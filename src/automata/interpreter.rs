use super::{expressions::Expression, literal::Literal, statements::Statement, tiots::State};

pub struct Interpreter {
    stack: Vec<Literal>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self { stack: Vec::new() }
    }

    pub fn expression(&mut self, state: &State, expression: &Expression) {}

    pub fn statement(&mut self, mut state: State, statement: &Statement) -> State {
        match statement {
            Statement::Sequence(statements) => {
                for statement in statements.into_iter() {
                    state = self.statement(state, statement)
                }
                state
            }
            Statement::Branch(branches) => {
                // TODO: This can be parallelised with rayon.
                for branch in branches.into_iter() {
                    state = self.statement(state, branch)
                }
                state
            }
            Statement::Expression(expression) => {
                todo!()
            }
            Statement::Reset(clock, limit) => {
                let clock = state.ref_environemnt().get_clock(*clock).unwrap();
                state.mut_zone().reset(clock, *limit);
                state
            }
            Statement::NOP => state,
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

        let after = interpreter.statement(state, &reset_x).ref_zone().clone();

        assert_eq!(
            "-x ≤ 0 ∧ x ≤ 0 ∧ x - y ≤ 0 ∧ -y ≤ 0",
            after.fmt_conjunctions(&labels)
        );
    }
}
