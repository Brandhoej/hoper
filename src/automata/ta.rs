use crate::zones::constraint::Clock;

pub trait TA {
    // FIXME: This is not how clocks are represented in TAs historically.
    // Conventionally this appraoch only makes sense because we are working with DBMs
    // which does not care for the set of clocks but rather their indices.
    // Returns the number of clocks.
    fn clocks(&self) -> Clock;
}
