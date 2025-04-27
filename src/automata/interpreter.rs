use crate::zones::constraint::{Clock, Limit, Relation};

use super::{
    expressions::{Binary, Comparison, Expression, Unary},
    literal::Literal,
    statements::Statement,
    tiots::State,
};

/// An stack-based interpreter for evaluating expressions and statements over a state with clock constraints.
///
/// The `Interpreter` maintains an internal evaluation stack for intermediate results in a stack
/// and provides methods for interpreting expressions, statements, and deriving tightened bounds
/// according to the expressions given the current state.
///
/// # Fields
///
/// - `stack`: A stack of `Literal` values used for intermediate evaluation during interpretation.
pub struct Interpreter {
    stack: Vec<Literal>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self { stack: Vec::new() }
    }

    /// Returns a reference to the top `Literal` on the stack, if any.
    pub fn peek(&self) -> Option<&Literal> {
        self.stack.last()
    }

    /// Removes and returns the top `Literal` from the stack, if any.
    pub fn pop(&mut self) -> Option<Literal> {
        self.stack.pop()
    }

    /// Assumes `Expression` is a boolean expression. This function evaluates an `Expression` in a
    /// given `State` and determines whether it is satisfied.
    ///
    /// This method uses the interpreter's internal stack to evaluate the expression,
    /// popping the final result from the stack and interpreting it as a boolean value.
    ///
    /// # Behavior
    /// - If the evaluation succeeds and yields a `Boolean` `Literal`, returns `Ok(true)` or `Ok(false)`.
    /// - If the evaluation fails or the final result is not a `Boolean`, returns `Err(())`.
    ///
    /// # Parameters
    /// - `state`: A reference to the current `State` in which to evaluate the expression.
    /// - `expression`: The `Expression` to evaluate for satisfaction.
    ///
    /// # Returns
    /// - `Ok(true)` if the expression is satisfied in the given state.
    /// - `Ok(false)` if the expression is not satisfied.
    /// - `Err(())` if the expression evaluation fails or the result is not a boolean.
    pub fn satisfies(&mut self, state: &State, expression: &Expression) -> Result<bool, ()> {
        self.expression(state, expression);
        match self.pop() {
            Some(literal) => {
                if let Literal::Boolean(satified) = literal {
                    Ok(satified)
                } else {
                    Err(())
                }
            }
            None => Err(()),
        }
    }

    /// Evaluates an expression within a given state.
    ///
    /// This method processes various forms of `Expression`,
    /// pushing results onto the interpreter's stack as necessary.
    ///
    /// # Parameters
    /// - `state`: A reference to the current `State`.
    /// - `expression`: The `Expression` to evaluate.
    pub fn expression(&mut self, state: &State, expression: &Expression) {
        match expression {
            Expression::Unary(unary, expression) => match unary {
                Unary::LogicalNegation => {
                    self.expression(state, expression);
                    let bool = self.stack.pop().unwrap().boolean().unwrap();
                    self.stack.push(Literal::Boolean(!bool));
                }
            },
            Expression::Binary(lhs, binary, rhs) => match binary {
                Binary::Conjunction => {
                    self.expression(state, lhs);
                    let lhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                    if lhs_bool {
                        self.expression(state, rhs);
                        let rhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                        self.stack.push(Literal::new_boolean(rhs_bool));
                    } else {
                        self.stack.push(Literal::new_false());
                    }
                }

                Binary::Disjunction => {
                    self.expression(state, lhs);
                    let lhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                    if lhs_bool {
                        self.stack.push(Literal::new_true());
                    } else {
                        self.expression(state, rhs);
                        let rhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                        self.stack.push(Literal::new_boolean(rhs_bool));
                    }
                }
            },
            Expression::Group(expression) => self.expression(state, expression),
            Expression::Literal(literal) => self.stack.push(literal.clone()),
            Expression::ClockConstraint(operand, comparison, limit) => {
                self.expression(state, &operand);
                let clock_symbol = self.stack.pop().unwrap().identifier().unwrap();
                let clock = state.environment().get_clock(clock_symbol).unwrap();

                self.expression(state, &limit);
                let limit_literal = self.stack.pop().unwrap().i16().unwrap() as Limit;

                let satisfied =
                    self.satisfies_clock_constraint(state, clock, *comparison, limit_literal);
                self.stack.push(Literal::Boolean(satisfied));
            }
            Expression::DiagonalClockConstraint(minuend, subtrahend, comparison, limit) => {
                self.expression(state, &minuend);
                let minuend_clock_symbol = self.stack.pop().unwrap().identifier().unwrap();
                let minuend_clock = state.environment().get_clock(minuend_clock_symbol).unwrap();

                self.expression(state, &subtrahend);
                let subtrahend_clock_symbol = self.stack.pop().unwrap().identifier().unwrap();
                let subtrahend_clock = state
                    .environment()
                    .get_clock(subtrahend_clock_symbol)
                    .unwrap();

                self.expression(state, &limit);
                let limit_literal = self.stack.pop().unwrap().i16().unwrap() as Limit;

                let satisfied = self.satisfies_diagonal_clock_constraint(
                    state,
                    minuend_clock,
                    subtrahend_clock,
                    *comparison,
                    limit_literal,
                );
                self.stack.push(Literal::Boolean(satisfied));
            }
        }
    }

    /// Checks whether a given clock constraint is satisfied in the current `State`.
    ///
    /// A clock constraint relates a single clock to a limit using a comparison operator
    /// (`<`, `<=`, `=`, `>=`, `>`).
    ///
    /// # Parameters
    /// - `state`: The current `State` containing the clock valuations.
    /// - `clock`: The `Clock` whose value is being checked.
    /// - `comparison`: The `Comparison` operator to apply.
    /// - `limit`: The `Limit` value against which the clock is compared.
    ///
    /// # Returns
    /// - `true` if the clock constraint is satisfied under the given state.
    /// - `false` otherwise.
    pub fn satisfies_clock_constraint(
        &self,
        state: &State,
        clock: Clock,
        comparison: Comparison,
        limit: Limit,
    ) -> bool {
        match comparison {
            Comparison::LessThanOrEqual => state.satisfies_upper(clock, Relation::weak(limit)),
            Comparison::LessThan => state.satisfies_upper(clock, Relation::strict(limit)),
            Comparison::Equal => state.satisfies_limit(clock, limit),
            Comparison::GreaterThanOrEqual => state.satisfies_lower(clock, Relation::weak(limit)),
            Comparison::GreaterThan => state.satisfies_lower(clock, Relation::strict(limit)),
        }
    }

    /// Checks whether a diagonal clock constraint is satisfied in the current `State`.
    ///
    /// A diagonal clock constraint relates the difference between two clocks
    /// (`minuend_clock - subtrahend_clock`) to a limit using a comparison operator
    /// (`<`, `<=`, `=`, `>=`, `>`).
    ///
    /// # Parameters
    /// - `state`: The current `State` containing the clock valuations.
    /// - `minuend_clock`: The `Clock` appearing first (being subtracted from).
    /// - `subtrahend_clock`: The `Clock` being subtracted.
    /// - `comparison`: The `Comparison` operator to apply to the difference.
    /// - `limit`: The `Limit` value against which the difference is compared.
    ///
    /// # Returns
    /// - `true` if the diagonal constraint is satisfied under the given state.
    /// - `false` otherwise.
    pub fn satisfies_diagonal_clock_constraint(
        &self,
        state: &State,
        minuend_clock: Clock,
        subtrahend_clock: Clock,
        comparison: Comparison,
        limit: Limit,
    ) -> bool {
        match comparison {
            Comparison::LessThanOrEqual => {
                state.satisfies(minuend_clock, subtrahend_clock, Relation::weak(limit))
            }
            Comparison::LessThan => {
                state.satisfies(minuend_clock, subtrahend_clock, Relation::strict(limit))
            }
            Comparison::Equal => {
                state.satisfies_difference_limit(minuend_clock, subtrahend_clock, limit)
            }
            Comparison::GreaterThanOrEqual => {
                state.satisfies(minuend_clock, subtrahend_clock, Relation::weak(limit))
            }
            Comparison::GreaterThan => {
                state.satisfies(minuend_clock, subtrahend_clock, Relation::strict(limit))
            }
        }
    }

    /// Executes a statement within a given state and returns the resulting state.
    ///
    /// Supports sequential execution (`Sequence`), branching (`Branch`), expressions,
    /// clock resets, and no-operation (`NOP`) statements.
    ///
    /// # Parameters
    /// - `state`: The `State` before executing the statement.
    /// - `statement`: The `Statement` to execute.
    ///
    /// # Returns
    /// The new `State` after executing the statement.
    pub fn statement(&mut self, mut state: State, statement: &Statement) -> Result<State, ()> {
        match statement {
            Statement::Sequence(statements) => {
                for statement in statements.into_iter() {
                    state = match self.statement(state, statement) {
                        Ok(state) => state,
                        Err(_) => return Err(()),
                    }
                }
                Ok(state)
            }
            Statement::Branch(branches) => {
                // TODO: This can be parallelised with rayon.
                for branch in branches.into_iter() {
                    state = match self.statement(state, branch) {
                        Ok(state) => state,
                        Err(_) => return Err(()),
                    }
                }
                Ok(state)
            }
            Statement::Expression(expression) => {
                self.expression(&state, expression);
                Ok(state)
            }
            Statement::Reset(clock, limit) => {
                let clock = state.environment().get_clock(*clock).unwrap();
                state.reset(clock, *limit);
                Ok(state)
            }
            Statement::NOP => Ok(state),
        }
    }

    /// Tightens the symbolic zone of the state to satisfy, if possible, the expression.
    ///
    /// This method recursively traverses the expression tree, evaluating and tightening bounds
    /// according to logical operations (`Unary`, `Binary`) and clock constraints
    /// (both simple and diagonal constraints).
    ///
    /// Intermediate evaluation results are pushed onto the internal stack.
    ///
    /// # Parameters
    /// - `bounds`: The initial `Bounds` to be tightened.
    /// - `state`: A reference to the current `State`.
    /// - `expression`: The `Expression` whose constraints must be respected.
    ///
    /// # Returns
    /// The new, tightened `Bounds` reflecting the constraints of the evaluated expression.
    pub fn constrain(&mut self, mut state: State, expression: &Expression) -> Result<State, ()> {
        match expression {
            Expression::Unary(..) => Err(()),
            Expression::Binary(lhs, binary, rhs) => match binary {
                Binary::Conjunction => {
                    state = match self.constrain(state, lhs) {
                        Ok(state) => state,
                        Err(_) => return Err(()),
                    };
                    let lhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                    if lhs_bool {
                        state = match self.constrain(state, rhs) {
                            Ok(state) => state,
                            Err(_) => return Err(()),
                        };
                        let rhs_bool = self.stack.pop().unwrap().boolean().unwrap();
                        self.stack.push(Literal::new_boolean(lhs_bool && rhs_bool));
                    }

                    self.stack.push(Literal::new_false());
                    Ok(state)
                }
                Binary::Disjunction => Err(()),
            },
            Expression::Group(expression) => self.constrain(state, expression),
            Expression::Literal(literal) => {
                self.stack.push(literal.clone());
                Ok(state)
            }
            Expression::ClockConstraint(operand, comparison, limit) => {
                state = self.constrain(state, &operand)?;
                let clock_symbol = self.stack.pop().unwrap().identifier().unwrap();
                let clock = state.environment().get_clock(clock_symbol).unwrap();

                state = self.constrain(state, &limit)?;
                let limit_literal = self.stack.pop().unwrap().i16().unwrap() as Limit;

                let satisfied =
                    self.satisfies_clock_constraint(&state, clock, *comparison, limit_literal);
                self.stack.push(Literal::Boolean(satisfied));

                if !satisfied {
                    return Ok(state);
                }

                match comparison {
                    Comparison::LessThanOrEqual => {
                        state.tighten_upper(clock, Relation::weak(limit_literal))
                    }
                    Comparison::LessThan => {
                        state.tighten_upper(clock, Relation::strict(limit_literal))
                    }
                    Comparison::Equal => state.set_limit(clock, limit_literal),
                    Comparison::GreaterThanOrEqual => {
                        state.tighten_lower(clock, Relation::weak(-limit_literal))
                    }
                    Comparison::GreaterThan => {
                        state.tighten_lower(clock, Relation::strict(-limit_literal))
                    }
                }
            }
            Expression::DiagonalClockConstraint(minuend, subtrahend, comparison, limit) => {
                state = self.constrain(state, &minuend)?;
                let minuend_clock_symbol = self.stack.pop().unwrap().identifier().unwrap();
                let minuend_clock = state.environment().get_clock(minuend_clock_symbol).unwrap();

                state = self.constrain(state, &subtrahend)?;
                let subtrahend_clock_symbol = self.stack.pop().unwrap().identifier().unwrap();
                let subtrahend_clock = state
                    .environment()
                    .get_clock(subtrahend_clock_symbol)
                    .unwrap();

                state = self.constrain(state, &limit)?;
                let limit_literal = self.stack.pop().unwrap().i16().unwrap();

                let satisfied = self.satisfies_diagonal_clock_constraint(
                    &state,
                    minuend_clock,
                    subtrahend_clock,
                    *comparison,
                    limit_literal,
                );
                self.stack.push(Literal::Boolean(satisfied));

                if !satisfied {
                    return Ok(state);
                }

                match comparison {
                    Comparison::LessThanOrEqual => state.tighten(
                        minuend_clock,
                        subtrahend_clock,
                        Relation::weak(limit_literal),
                    ),
                    Comparison::LessThan => state.tighten(
                        minuend_clock,
                        subtrahend_clock,
                        Relation::strict(limit_literal),
                    ),
                    Comparison::Equal => {
                        state.set_difference_limit(minuend_clock, subtrahend_clock, limit_literal)
                    }
                    Comparison::GreaterThanOrEqual => state.tighten(
                        minuend_clock,
                        subtrahend_clock,
                        Relation::weak(-limit_literal),
                    ),
                    Comparison::GreaterThan => state.tighten(
                        minuend_clock,
                        subtrahend_clock,
                        Relation::strict(-limit_literal),
                    ),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        automata::{
            environment::Environment, interpreter::Interpreter,
            partitioned_symbol_table::PartitionedSymbolTable, statements::Statement,
            tioa::LocationTree, tiots::State,
        },
        zones::dbm::DBM,
    };

    #[test]
    fn reset() {
        let symbols = PartitionedSymbolTable::new();
        let x_symbol = symbols.intern(0, "x");
        let y_symbol = symbols.intern(1, "y");

        let mut environment = Environment::new();
        let x = environment.insert_clock(x_symbol);
        let y = environment.insert_clock(y_symbol);

        let mut labels: Vec<&str> = vec!["", ""];
        labels[(x - 1) as usize] = "x";
        labels[(y - 1) as usize] = "y";

        let mut before = DBM::zero(2);
        before.up();
        assert_eq!(
            "-x ≤ 0 ∧ x - y ≤ 0 ∧ -y ≤ 0 ∧ y - x ≤ 0",
            before.fmt_conjunctions(&labels)
        );

        let reset_x = Statement::reset(x_symbol, 0);

        let mut interpreter = Interpreter::new();
        let state = State::new(LocationTree::Leaf(0.into()), before, environment);

        let after = interpreter
            .statement(state, &reset_x)
            .ok()
            .unwrap()
            .zone()
            .clone();

        assert_eq!(
            "-x ≤ 0 ∧ x ≤ 0 ∧ x - y ≤ 0 ∧ -y ≤ 0",
            after.fmt_conjunctions(&labels)
        );
    }
}
