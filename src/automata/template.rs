/// Represents a TIOA under construction. This means that it can be built into a TIOA but
/// meanwhile it is being incrementally built it is not required to adhere to the requried
/// rules of a TIOA. Additionally it keeps track of its symbols can be used for look-ups.
/// This allows an extremely ergonomic structure for e.g. completion where demonic completion
/// requries a new universal location to be constructed and angelic requires self looping edges.
pub struct Template {
    // TODO: Fields like TIOA and symbol_table.
}
