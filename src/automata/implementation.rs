use super::specification::Specification;

/// An implementation is a specification which has both output urgency and independent progress.
/// Output urgency states that if an output can be produced then it is produced without any delay.
/// Independent progress states that either the implementation can delay indefinitely or delay until an action is possible.pub type Specification = dyn TIOA;
pub struct Implementation(Specification);

impl From<Box<Specification>> for Box<Implementation> {
    fn from(value: Box<Specification>) -> Self {
        todo!()
    }
}
