use itertools::Itertools;
use rayon::iter::{ParallelBridge, ParallelIterator};

use super::{automaton::Automaton, conversion::Conversion, specification::Specification};

pub trait InputEnabled
where
    Self: Sized,
{
    fn is_input_enabled(self) -> Conversion<Self, Box<Specification>, ()>;
}

impl InputEnabled for Automaton {
    /// Returns true if all inputs at all locations can always be enabled.
    /// For now, this algorithm is very naive and over-approximates the required
    /// edges, by assuming that any edge can get the zero valuations to the location.
    /// Essentially, this means that lower bounds on clocks are ignored and we assume
    /// a potentially much larger zone.
    fn is_input_enabled(self) -> Conversion<Self, Box<Specification>, ()> {
        // Each of the states q ∈ Q is input-enabled:
        // ∀i? ∈ Actᵢ : ∃q' ∈ Q s.t. q -i?-> q'

        // This can easily be done do to location invariants cannot have lower-bounds on clocks.
        // Because of this the zero valuations of clocks will always satisfy the invariant. Therfore,
        // Computing the required zone for which the input should be enabled in is trivial. As it
        // is simply the zero valuations which is relaxed and the constrained by the invariant.

        let inputs: Vec<_> = self.inputs().cloned().collect();

        let has_disabled_inputs =
            Itertools::cartesian_product(self.node_iter(), inputs.into_iter())
                .par_bridge()
                .all(|(node, input)| {
                    /*self.locally_disabled(node, input)
                    .peekable()
                    .peek()
                    .is_some()*/
                    todo!()
                });

        if has_disabled_inputs {
            return Err((self, ()));
        }

        Conversion::Ok(Box::new(Specification::new(self)))
    }
}
