use crate::zones::{
    bounds::Bounds,
    dbm::{Canonical, Unsafe, DBM},
};

use super::expressions::Expression;

/// An `Extrapolation` describes the maximum reachable bounds.
/// These can be found using different strategies depending on performance
/// requirements. Maybe diagonal constraints are ignored and just
/// lower/upper bounds are taken into consideration.
///
/// TODO: Consider storing bounds on zones and reusing them for a following extrapolation.
pub enum Extrapolation {
    /// Takes diagonal constraints into account but does zone extrapolation
    /// on the fly. Meaning that no information regarding minimum zones are
    /// stored to make the proceeding extrapolations more effecient.
    DifferenceOnTheFly,
}

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
    extrapolation: Extrapolation,
}

impl Extrapolator {
    pub fn expression(
        &mut self,
        mut dbm: DBM<Canonical>,
        expression: &Expression,
    ) -> Result<DBM<Canonical>, DBM<Unsafe>> {
        let bounds = Bounds::empty();
        dbm.extrapolate(bounds)
    }
}
