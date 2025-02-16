use crate::{
    automata::expressions::Comparison,
    zones::{bounds::Bounds, constraint::Relation},
};

use super::{
    expressions::{Binary, Expression},
    literal::Literal,
    tiots::State,
};

/// The range of clocks can in theory be unbounded, meaning that a clock can run
/// indefinitely, taking any real value. This means that one can stay at a location for
/// an indefinite time. Extrapolation, in contrast to Uppaal is significantly
/// different because it is not required for locations to have upper bounds on clocks.
/// One direct example of this are implementation's locations. Which requires either
/// output urgency or independent progress. Where independent progress in an implementation
/// is an indefinite delay. However, in many cases there are upper and lower bounds on clock
/// valuations. These we can utilise to restrict zones when delaying in locations.
///
/// OBS: The restrictions on the Automaton ensures that all exploration results in a convex zone.
/// Therefore all location invariants max bounds are a minimum representation of the over-approximated
/// zone's minimum representation.
///
/// More in-depth the restrictions states that essentially all location invariants only describe upper-bounds
/// and diagonal constraints. Edges are always convex meaning that no possible disjunction restricts the
/// clocal valuations in such a way that more than one zone is required to describe the exact zone for the guard.
///
/// The way the TIOTS works is that delays happen in the locations. Where we delay restricted
/// by the invariant's bounds. Meaning that each location essentially have a zone assocaited with
/// it, which describes an over-approximated zone reachable in the location. Then when an edge is
/// traversed the extrapolated zone is further restricted (and still convex).
pub struct Extrapolator {
    stack: Vec<Literal>,
}

impl Extrapolator {
    pub fn new() -> Self {
        Self { stack: Vec::new() }
    }

    pub fn bounds(&mut self, bounds: Bounds, state: &State, expression: &Expression) -> Bounds {
        match expression {
            Expression::Unary(unary, expression) => {
                let bounds = self.bounds(bounds, state, expression);
                let value = self.stack.pop().unwrap();

                match unary {
                    super::expressions::Unary::LogicalNegation => {
                        let negation = Literal::Boolean(!value.boolean().unwrap());
                        self.stack.push(negation);
                        return bounds.negation();
                    }
                }
            }
            Expression::Binary(lhs, binary, rhs) => match binary {
                Binary::Conjunction => {
                    let lhs_bounds = self.bounds(bounds.clone(), state, lhs);
                    let lhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                    if !lhs_bool {
                        self.stack.push(Literal::new_false());
                        return Bounds::new();
                    }

                    let rhs_bounds = self.bounds(bounds, state, rhs);
                    let rhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                    if !rhs_bool {
                        self.stack.push(Literal::new_false());
                        return Bounds::new();
                    }

                    self.stack.push(Literal::new_true());
                    lhs_bounds.tighten_all(rhs_bounds.into_iter())
                }
                Binary::Disjunction => {
                    let lhs_bounds = self.bounds(bounds.clone(), state, lhs);
                    let lhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                    let rhs_bounds = self.bounds(bounds.clone(), state, rhs);
                    let rhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                    self.stack.push(Literal::new_boolean(lhs_bool || rhs_bool));

                    return if lhs_bool && rhs_bool {
                        lhs_bounds.loosen_all(rhs_bounds.into_iter())
                    } else if lhs_bool {
                        lhs_bounds
                    } else if rhs_bool {
                        rhs_bounds
                    } else {
                        Bounds::new()
                    };
                }
            },
            Expression::Group(expression) => self.bounds(bounds, state, expression),
            Expression::Literal(literal) => {
                self.stack.push(literal.clone());
                bounds
            }
            Expression::ClockConstraint(operand, comparison, limit) => {
                self.bounds(bounds.clone(), state, &operand);
                let clock_symbol = self.stack.pop().unwrap().identifier().unwrap();
                let clock = state.ref_environemnt().get_clock(clock_symbol).unwrap();

                self.bounds(bounds.clone(), state, &limit);
                let limit_literal = self.stack.pop().unwrap().i16().unwrap();

                match comparison {
                    Comparison::LessThanOrEqual => {
                        bounds.tighten_upper(clock, Relation::weak(limit_literal))
                    }
                    Comparison::LessThan => {
                        bounds.tighten_upper(clock, Relation::strict(limit_literal))
                    }
                    Comparison::Equal => bounds.set_limit(clock, limit_literal),
                    Comparison::GreaterThanOrEqual => {
                        bounds.tighten_lower(clock, Relation::weak(-limit_literal))
                    }
                    Comparison::GreaterThan => {
                        bounds.tighten_lower(clock, Relation::strict(-limit_literal))
                    }
                }
            }
            Expression::DiagonalClockConstraint(minuend, subtrahend, comparison, limit) => {
                self.bounds(bounds.clone(), state, &minuend);
                let minuend_clock_symbol = self.stack.pop().unwrap().identifier().unwrap();
                let minuend_clock = state
                    .ref_environemnt()
                    .get_clock(minuend_clock_symbol)
                    .unwrap();

                self.bounds(bounds.clone(), state, &subtrahend);
                let subtrahend_clock_symbol = self.stack.pop().unwrap().identifier().unwrap();
                let subtrahend_clock = state
                    .ref_environemnt()
                    .get_clock(subtrahend_clock_symbol)
                    .unwrap();

                self.bounds(bounds.clone(), state, &limit);
                let limit_literal = self.stack.pop().unwrap().i16().unwrap();

                match comparison {
                    Comparison::LessThanOrEqual => bounds.tighten(
                        minuend_clock,
                        subtrahend_clock,
                        Relation::weak(limit_literal),
                    ),
                    Comparison::LessThan => bounds.tighten(
                        minuend_clock,
                        subtrahend_clock,
                        Relation::strict(limit_literal),
                    ),
                    Comparison::Equal => {
                        bounds.set_difference_limit(minuend_clock, subtrahend_clock, limit_literal)
                    }
                    Comparison::GreaterThanOrEqual => bounds.tighten(
                        minuend_clock,
                        subtrahend_clock,
                        Relation::weak(-limit_literal),
                    ),
                    Comparison::GreaterThan => bounds.tighten(
                        minuend_clock,
                        subtrahend_clock,
                        Relation::strict(-limit_literal),
                    ),
                }
            }
        }
    }
}
