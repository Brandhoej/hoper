use symbol_table::Symbol;

use super::{expressions::Expression, statements::Statement};

#[derive(Clone)]
pub enum Location {
    Leaf {
        name: Symbol,
        invariant: Expression,
        update: Statement,
    },
    Branch(Vec<Location>),
}

impl Location {
    pub const fn new(name: Symbol, invariant: Expression, update: Statement) -> Self {
        Self::Leaf {
            name,
            invariant,
            update,
        }
    }

    pub fn combine(locations: impl Iterator<Item = Self>) -> Self {
        todo!()
    }

    pub const fn with_name(name: Symbol) -> Self {
        Self::new(name, Expression::new_true(), Statement::empty())
    }

    pub const fn name(&self) -> Option<&Symbol> {
        match self {
            Location::Leaf { name, .. } => Some(name),
            Location::Branch(locations) => None,
        }
    }

    pub fn invariant(&self) -> Expression {
        match self {
            Location::Leaf { invariant, .. } => invariant.clone(),
            Location::Branch(locations) => Expression::conjunction(
                locations
                    .iter()
                    .map(|location| location.invariant().clone())
                    .collect(),
            ),
        }
    }

    pub fn update(&self) -> Statement {
        match self {
            Location::Leaf { update, .. } => update.clone(),
            Location::Branch(locations) => Statement::sequence(
                locations
                    .iter()
                    .map(|location| location.update().clone())
                    .collect(),
            ),
        }
    }
}
