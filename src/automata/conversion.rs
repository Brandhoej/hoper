/// Represents a `Result` which essentially is a conversion where
/// if it fails it returns the original value. If, however, it does not
/// then the converted value is returned. By also returning the original
/// value when the conversion fails allows for us to not consume the value
/// when it failed its conversion. However, this type does not guarantee
/// that any alterations has happend on the original value. However,
/// altering it and returning it disguished as the original values in this
/// type is _highly_ discouraged. This type is not ment to represent such action.
pub type Conversion<O, R, E> = Result<R, (O, E)>;
