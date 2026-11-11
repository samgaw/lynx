//! Rustler facade for the workspace verification fixture.

/// Replaces the first byte through two ordinary workspace crates.
#[cfg(feature = "collections")]
#[rustler::nif]
fn replace_first(input: Vec<u8>, value: u8) -> (bool, Vec<u8>) {
    experiment_analysis::replace_first(input, value)
}

/// Restores a boolean through two calls in the first-party dependency graph.
#[rustler::nif(name = "restore", schedule = "DirtyCpu")]
fn native_restore(value: bool) -> bool {
    experiment_analysis::restore(value)
}

/// Negates the verified workspace result on the normal scheduler.
#[rustler::nif]
fn negate(value: bool) -> bool {
    !experiment_analysis::restore(value)
}

/// Evaluates the integer algorithm through the first-party dependency graph.
#[rustler::nif]
fn calculate(value: i64) -> i64 {
    experiment_analysis::twice_plus_one(value)
}

/// Exercises Rustler's i8 decoding and encoding.
#[rustler::nif]
fn echo_i8(value: i8) -> i8 {
    value
}

/// Exercises Rustler's i16 decoding and encoding.
#[rustler::nif]
fn echo_i16(value: i16) -> i16 {
    value
}

/// Exercises Rustler's i32 decoding and encoding.
#[rustler::nif]
fn echo_i32(value: i32) -> i32 {
    value
}

/// Exercises Rustler's u8 decoding and encoding.
#[rustler::nif]
fn echo_u8(value: u8) -> u8 {
    value
}

/// Exercises Rustler's u16 decoding and encoding.
#[rustler::nif]
fn echo_u16(value: u16) -> u16 {
    value
}

/// Exercises Rustler's u32 decoding and encoding.
#[rustler::nif]
fn echo_u32(value: u32) -> u32 {
    value
}

/// Exercises Rustler's u64 decoding and encoding.
#[rustler::nif]
fn echo_u64(value: u64) -> u64 {
    value
}

/// A compiled export deliberately outside the supported verification subset.
#[cfg(feature = "unsupported-float")]
#[rustler::nif]
fn echo_float(value: f64) -> f64 {
    value
}

#[cfg(not(any(feature = "composite", feature = "binary")))]
rustler::init!("Elixir.LynxRustFixture.Native");
#[cfg(all(feature = "composite", not(feature = "binary")))]
rustler::init!("Elixir.LynxRustFixture.CompositeNative");
#[cfg(feature = "binary")]
rustler::init!("Elixir.LynxRustFixture.BinaryNative");

/// Exposes an extracted tuple computation across first-party crates.
#[cfg(feature = "composite")]
#[rustler::nif]
fn transform_pair(value: (bool, i64)) -> (bool, i64) {
    experiment_analysis::transform_pair(value)
}

/// Exposes a result computed through shared first-party structs and enums.
#[cfg(feature = "composite")]
#[rustler::nif]
fn classify(value: (bool, i64)) -> Result<i64, u8> {
    experiment_analysis::classify(value)
}

/// Exercises tagged result decoding as well as result encoding.
#[cfg(feature = "composite")]
#[rustler::nif]
fn reverse_result(value: Result<i64, u8>) -> Result<u8, i64> {
    match value {
        Ok(value) => Err(value),
        Err(code) => Ok(code),
    }
}

/// Exercises nested tuples, singleton tuples and the empty tuple.
#[cfg(feature = "composite")]
#[rustler::nif]
fn echo_nested(value: ((bool,), (u8, i64, ()))) -> ((bool,), (u8, i64, ())) {
    value
}

/// Exercises Rustler's largest supported tuple arity.
#[cfg(feature = "composite")]
#[rustler::nif]
fn echo_seven(value: (u8, u8, u8, u8, u8, u8, u8)) -> (u8, u8, u8, u8, u8, u8, u8) {
    value
}

/// Preserves binary bytes through ordinary generic first-party implementations.
#[cfg(feature = "binary")]
#[rustler::nif]
fn echo_binary(value: rustler::Binary<'_>) -> rustler::Binary<'_> {
    experiment_analysis::preserve(value)
}

/// Computes binary length through two first-party workspace crates.
#[cfg(feature = "binary")]
#[rustler::nif]
fn binary_length(value: rustler::Binary<'_>) -> u64 {
    experiment_analysis::byte_length(value.as_slice())
}

/// Parses a versioned, length-prefixed UTF-8 frame across workspace crates.
#[cfg(feature = "protocol")]
#[rustler::nif]
fn parse_frame(value: rustler::Binary<'_>) -> Result<u64, u8> {
    experiment_analysis::parse_frame(value.as_slice())
}

/// Returns exact UTF-8 error positions through the verified binary adapter.
#[cfg(feature = "protocol")]
#[rustler::nif]
fn utf8_status(value: rustler::Binary<'_>) -> Result<u64, (u64, u8)> {
    experiment_analysis::utf8_status(value.as_slice())
}

/// An unmodelled owned conversion must not silently become verified.
#[cfg(feature = "unsupported-binary-method")]
#[rustler::nif]
fn binary_owned_length(value: rustler::Binary<'_>) -> u64 {
    value.to_owned().as_slice().len() as u64
}

#[cfg(feature = "custom-encoder")]
mod custom_encoding {
    use rustler::{Encoder, Env, Term};

    rustler::atoms! {
        invalid,
        missing,
    }

    #[derive(Debug)]
    enum Error {
        Invalid(String),
        Missing,
    }

    impl Encoder for Error {
        fn encode<'a>(&self, env: Env<'a>) -> Term<'a> {
            match self {
                Self::Invalid(message) => (invalid(), message).encode(env),
                Self::Missing => missing().encode(env),
            }
        }
    }

    /// Exercises a custom error encoder after an ordinary cross-crate call.
    #[rustler::nif]
    fn custom_validate(value: u8) -> Result<(), Error> {
        if experiment_analysis::restore(value > 1) {
            Ok(())
        } else if value == 0 {
            Err(Error::Missing)
        } else {
            Err(Error::Invalid("custom error".to_string()))
        }
    }
}

/// Applies the workspace policy to an optional boolean field.
#[cfg(feature = "optional")]
#[rustler::nif]
fn optional_flag(value: Option<bool>) -> bool {
    experiment_analysis::optional_flag(value)
}

/// Observes Rustler's inner-first decoding of nested options.
#[cfg(feature = "optional")]
#[rustler::nif]
fn nested_missing(value: Option<Option<bool>>) -> bool {
    matches!(value, Some(None))
}

/// Retains the structure of an optional composite value.
#[cfg(feature = "optional")]
#[rustler::nif]
fn optional_pair(value: Option<(bool, Result<u8, i64>)>) -> Option<(bool, Result<u8, i64>)> {
    value
}

/// Preserves list decoder panics and verification bounds inside Option.
#[cfg(feature = "optional")]
#[rustler::nif]
fn optional_bytes(value: Option<Vec<u8>>) -> Option<Vec<u8>> {
    value
}

/// Updates a signed field batch through two ordinary workspace crates.
#[cfg(feature = "scalar-vec")]
#[rustler::nif]
fn replace_first_i64(input: Vec<i64>, value: i64) -> (bool, Vec<i64>) {
    experiment_analysis::replace_first_i64(input, value)
}

/// Returns a batch of boolean fields using Rustler's ordinary list codec.
#[cfg(feature = "scalar-vec")]
#[rustler::nif]
fn echo_flags(input: Vec<bool>) -> Vec<bool> {
    input
}

/// Exercises Rustler's signed narrowing in a list element.
#[cfg(feature = "scalar-vec")]
#[rustler::nif]
fn echo_signed_bytes(input: Vec<i8>) -> Vec<i8> {
    input
}

/// A protocol tuple encoded by the actual Rustler derive implementation.
#[cfg(feature = "derived-tuple")]
#[derive(Debug, rustler::NifTuple)]
struct OrderedFields {
    low: u64,
    high: u64,
}

/// Returns ordered workspace fields through a derived Encoder.
#[cfg(feature = "derived-tuple")]
#[rustler::nif]
fn derived_pair(left: u64, right: u64) -> OrderedFields {
    let (low, high) = experiment_analysis::order_pair(left, right);
    OrderedFields { low, high }
}

/// Ordered protocol fields encoded by the actual Rustler map derive.
#[cfg(feature = "derived-map")]
#[derive(Debug, rustler::NifMap)]
struct OrderedMap {
    low: u64,
    high: u64,
}

/// Encodes the first-party ordering result as a map.
#[cfg(feature = "derived-map")]
#[rustler::nif]
fn derived_map(left: u64, right: u64) -> OrderedMap {
    let (low, high) = experiment_analysis::order_pair(left, right);
    OrderedMap { low, high }
}

/// Ordered protocol fields with an Elixir struct tag from the actual derive.
#[cfg(feature = "derived-struct")]
#[derive(Debug, rustler::NifStruct)]
#[module = "LynxOrderedFixture"]
struct OrderedStruct {
    low: u64,
    high: u64,
}

/// Encodes the first-party ordering result with the compiled struct tag.
#[cfg(feature = "derived-struct")]
#[rustler::nif]
fn derived_struct(left: u64, right: u64) -> OrderedStruct {
    let (low, high) = experiment_analysis::order_pair(left, right);
    OrderedStruct { low, high }
}

/// A derived tuple containing an encoded list.
#[cfg(feature = "derived-list")]
#[derive(Debug, rustler::NifTuple)]
struct OrderedList {
    values: Vec<u64>,
}

/// Constructs a nested list using the actual workspace ordering algorithm.
#[cfg(feature = "derived-list")]
#[rustler::nif]
#[expect(
    clippy::vec_init_then_push,
    reason = "Exercise the bounded Vec::push verification model"
)]
fn derived_list(left: u64, right: u64) -> OrderedList {
    let (low, high) = experiment_analysis::order_pair(left, right);
    let mut values = Vec::new();
    values.push(low);
    values.push(high);
    OrderedList { values }
}

/// A derived protocol response with atom and tuple representations.
#[cfg(feature = "derived-tagged")]
#[derive(rustler::NifTaggedEnum)]
enum OrderedReply {
    Empty,
    Equal(u64),
    Ordered(u64, u64),
}

/// Classifies and orders fields through the ordinary workspace crates.
#[cfg(feature = "derived-tagged")]
#[rustler::nif(name = "tagged_reply", schedule = "DirtyCpu")]
fn tagged_order(left: u64, right: u64) -> OrderedReply {
    if left == 0 && right == 0 {
        OrderedReply::Empty
    } else if left == right {
        OrderedReply::Equal(left)
    } else {
        let (low, high) = experiment_analysis::order_pair(left, right);
        OrderedReply::Ordered(low, high)
    }
}

/// Propagates checked arithmetic failure through the workspace's Option path.
#[cfg(feature = "checked-option")]
#[rustler::nif]
fn checked_analyse(value: i64) -> Option<i64> {
    experiment_analysis::analyse(value)
}

/// Internal tuple extraction proof root; this is not a NIF export.
#[cfg(feature = "custom-decoder")]
pub fn tuple_fields(input: rustler::Term<'_>) -> rustler::NifResult<Vec<rustler::Term<'_>>> {
    rustler::types::tuple::get_tuple(input)
}

/// Observes tuple arity and destroys only the temporary vector of copyable handles.
#[cfg(feature = "custom-decoder")]
pub fn tuple_size(input: rustler::Term<'_>) -> rustler::NifResult<usize> {
    match rustler::types::tuple::get_tuple(input) {
        Ok(fields) => Ok(fields.len()),
        Err(error) => Err(error),
    }
}

/// A protocol flag decoded by an actual first-party Decoder implementation.
#[cfg(feature = "custom-decoder")]
pub struct ProtocolFlag {
    enabled: bool,
}

/// Calls a statically selected Decoder without assuming its implementation.
#[cfg(feature = "custom-decoder")]
fn decode_via<'a, T: rustler::Decoder<'a>>(input: rustler::Term<'a>) -> rustler::NifResult<T> {
    T::decode(input)
}

/// Internal first-party dictionary composition; not a NIF export.
#[cfg(feature = "custom-decoder")]
pub fn decode_flag_via(input: rustler::Term<'_>) -> rustler::NifResult<ProtocolFlag> {
    decode_via::<ProtocolFlag>(input)
}

#[cfg(feature = "custom-decoder")]
impl<'a> rustler::Decoder<'a> for ProtocolFlag {
    fn decode(term: rustler::Term<'a>) -> rustler::NifResult<Self> {
        match decode_via::<u64>(term) {
            Ok(value) => Ok(Self {
                enabled: value != 0,
            }),
            Err(error) => Err(error),
        }
    }
}

/// Restores the decoded flag through both ordinary workspace library crates.
///
/// # Panics
/// Panics when the explicit failure flag is set, after argument decoding.
#[cfg(feature = "custom-decoder")]
#[rustler::nif]
fn decoded_flag(input: ProtocolFlag, should_panic: bool) -> bool {
    if should_panic {
        panic!();
    }
    experiment_analysis::restore(input.enabled)
}

/// Decodes a dynamic input before computing through the workspace dependencies.
#[cfg(feature = "nif-result")]
fn decode_result_impl(input: rustler::Term<'_>, should_panic: bool) -> rustler::NifResult<bool> {
    match <u64 as rustler::Decoder<'_>>::decode(input) {
        Ok(value) => {
            if should_panic {
                panic!();
            }
            Ok(experiment_analysis::restore(value != 0))
        }
        Err(error) => Err(error),
    }
}

/// Returns a decoded result without adding an Erlang result tag.
#[cfg(feature = "nif-result")]
#[rustler::nif]
fn forwarded_result(input: rustler::Term<'_>, should_panic: bool) -> rustler::NifResult<bool> {
    decode_result_impl(input, should_panic)
}

/// Exercises the same NifReturnable specialization with explicit Result spelling.
#[cfg(feature = "nif-result")]
#[rustler::nif(name = "explicit_result", schedule = "DirtyCpu")]
fn spelled_result(input: rustler::Term<'_>, should_panic: bool) -> Result<bool, rustler::Error> {
    decode_result_impl(input, should_panic)
}

/// Preserves an arbitrary Erlang term through Rustler's stateless Term boundary.
#[cfg(feature = "nif-result")]
#[rustler::nif]
fn echo_term(input: rustler::Term<'_>) -> rustler::Term<'_> {
    input
}

/// Rejects zero after decoding; malformed inputs retain their original error.
#[cfg(feature = "validated-decoder")]
fn validate_nonzero(input: rustler::Term<'_>) -> rustler::NifResult<bool> {
    match <u64 as rustler::Decoder<'_>>::decode(input) {
        Ok(value) => {
            if value == 0 {
                {
                    #[cfg(feature = "atom-errors")]
                    {
                        Err(rustler::Error::Atom("zero"))
                    }
                    #[cfg(not(feature = "atom-errors"))]
                    {
                        Err(rustler::Error::BadArg)
                    }
                }
            } else {
                Ok(experiment_analysis::restore(value != 0))
            }
        }
        Err(error) => Err(error),
    }
}

#[cfg(feature = "validated-decoder")]
struct ValidatedFlag {
    enabled: bool,
}

#[cfg(feature = "validated-decoder")]
impl<'a> rustler::Decoder<'a> for ValidatedFlag {
    fn decode(input: rustler::Term<'a>) -> rustler::NifResult<Self> {
        match validate_nonzero(input) {
            Ok(enabled) => Ok(Self { enabled }),
            Err(error) => Err(error),
        }
    }
}

/// Exercises the actual custom Decoder before entering the native body.
#[cfg(feature = "validated-decoder")]
#[rustler::nif]
fn validated_flag(input: ValidatedFlag) -> bool {
    experiment_analysis::restore(input.enabled)
}

/// Exercises the same validation through Rustler's NifResult return conversion.
#[cfg(feature = "validated-decoder")]
#[rustler::nif]
fn validated_result(input: rustler::Term<'_>) -> rustler::NifResult<bool> {
    #[cfg(feature = "atom-errors")]
    {
        raise_nonzero(input)
    }
    #[cfg(not(feature = "atom-errors"))]
    {
        validate_nonzero(input)
    }
}

/// Raises a literal atom only when the facade returns this constructed error.
#[cfg(feature = "atom-errors")]
fn raise_nonzero(input: rustler::Term<'_>) -> rustler::NifResult<bool> {
    match <u64 as rustler::Decoder<'_>>::decode(input) {
        Ok(value) => {
            if value == 0 {
                Err(rustler::Error::RaiseAtom("zero"))
            } else {
                Ok(experiment_analysis::restore(value != 0))
            }
        }
        Err(error) => Err(error),
    }
}

/// A deferred error payload with an actual first-party Encoder.
#[cfg(feature = "boxed-errors")]
struct BoxedErrorPayload {
    value: u64,
    should_panic: bool,
}

#[cfg(feature = "boxed-errors")]
impl rustler::Encoder for BoxedErrorPayload {
    fn encode<'a>(&self, env: rustler::Env<'a>) -> rustler::Term<'a> {
        if experiment_analysis::restore(self.should_panic) {
            panic!();
        }
        <u64 as rustler::Encoder>::encode(&self.value, env)
    }
}

/// Constructs an error without invoking its payload Encoder.
#[cfg(feature = "boxed-errors")]
#[rustler::nif]
fn boxed_error(value: u64, should_panic: bool) -> rustler::NifResult<bool> {
    Err(rustler::Error::RaiseTerm(Box::new(BoxedErrorPayload {
        value,
        should_panic,
    })))
}

/// Returns the deferred payload inside an ordinary error tuple.
#[cfg(feature = "boxed-errors")]
#[rustler::nif(name = "boxed_term", schedule = "DirtyCpu")]
fn boxed_returned(value: u64, should_panic: bool) -> rustler::NifResult<bool> {
    Err(rustler::Error::Term(Box::new(BoxedErrorPayload {
        value,
        should_panic,
    })))
}

/// Formats a message after preserving the value through both library crates.
#[cfg(feature = "string-errors")]
fn error_text(value: u64) -> String {
    let value = experiment_analysis::preserve(value);
    format!("λvalue={value}")
}

/// Raises a boxed UTF-8 String using the standard Rustler Encoder dictionary.
#[cfg(feature = "string-errors")]
#[rustler::nif]
fn string_error(value: u64) -> rustler::NifResult<bool> {
    Err(rustler::Error::RaiseTerm(Box::new(error_text(value))))
}

/// Returns the same owned message inside an error tuple on a dirty scheduler.
#[cfg(feature = "string-errors")]
#[rustler::nif(name = "string_term", schedule = "DirtyCpu")]
fn string_returned(value: u64) -> rustler::NifResult<bool> {
    Err(rustler::Error::Term(Box::new(error_text(value))))
}

#[cfg(test)]
mod tests {
    use std::ffi::CStr;

    #[test]
    fn compiled_rustler_exports_match_the_fixture() {
        let exports: Vec<_> = rustler::codegen_runtime::inventory::iter::<rustler::Nif>
            .into_iter()
            .collect();
        assert_eq!(
            exports.len(),
            10 + usize::from(cfg!(feature = "unsupported-float"))
                + if cfg!(feature = "composite") { 5 } else { 0 }
                + 2 * usize::from(cfg!(feature = "binary"))
                + 2 * usize::from(cfg!(feature = "protocol"))
                + usize::from(cfg!(feature = "unsupported-binary-method"))
                + usize::from(cfg!(feature = "custom-encoder"))
                + usize::from(cfg!(feature = "custom-decoder"))
                + 3 * usize::from(cfg!(feature = "nif-result"))
                + 2 * usize::from(cfg!(feature = "validated-decoder"))
                + 2 * usize::from(cfg!(feature = "boxed-errors"))
                + 2 * usize::from(cfg!(feature = "string-errors"))
                + usize::from(cfg!(feature = "collections"))
                + 4 * usize::from(cfg!(feature = "optional"))
                + 3 * usize::from(cfg!(feature = "scalar-vec"))
                + usize::from(cfg!(feature = "derived-tuple"))
                + usize::from(cfg!(feature = "derived-map"))
                + usize::from(cfg!(feature = "derived-struct"))
                + usize::from(cfg!(feature = "derived-list"))
                + usize::from(cfg!(feature = "derived-tagged"))
                + usize::from(cfg!(feature = "checked-option"))
        );
        let mut metadata: Vec<_> = exports
            .into_iter()
            .map(|export| {
                let export = export.get_def();
                // Rustler's macro emits a static NUL-terminated export name.
                let name = unsafe { CStr::from_ptr(export.name) };
                (
                    name.to_str().expect("ASCII export name").to_owned(),
                    export.arity,
                    export.flags,
                )
            })
            .collect();
        metadata.sort();
        let mut expected: Vec<_> = [
            "calculate",
            "echo_i8",
            "echo_i16",
            "echo_i32",
            "echo_u8",
            "echo_u16",
            "echo_u32",
            "echo_u64",
            "negate",
        ]
        .into_iter()
        .map(|name| (name.to_owned(), 1, rustler::SchedulerFlags::Normal as u32))
        .collect();
        expected.push((
            "restore".to_owned(),
            1,
            rustler::SchedulerFlags::DirtyCpu as u32,
        ));
        if cfg!(feature = "unsupported-float") {
            expected.push((
                "echo_float".to_owned(),
                1,
                rustler::SchedulerFlags::Normal as u32,
            ));
        }
        if cfg!(feature = "composite") {
            expected.extend(
                [
                    "transform_pair",
                    "classify",
                    "reverse_result",
                    "echo_nested",
                    "echo_seven",
                ]
                .into_iter()
                .map(|name| (name.to_owned(), 1, rustler::SchedulerFlags::Normal as u32)),
            );
        }
        for (enabled, name) in [
            (cfg!(feature = "custom-encoder"), "custom_validate"),
            (cfg!(feature = "binary"), "echo_binary"),
            (cfg!(feature = "binary"), "binary_length"),
            (cfg!(feature = "protocol"), "parse_frame"),
            (cfg!(feature = "protocol"), "utf8_status"),
            (
                cfg!(feature = "unsupported-binary-method"),
                "binary_owned_length",
            ),
        ] {
            if enabled {
                expected.push((name.to_owned(), 1, rustler::SchedulerFlags::Normal as u32));
            }
        }
        if cfg!(feature = "optional") {
            for name in [
                "optional_flag",
                "nested_missing",
                "optional_pair",
                "optional_bytes",
            ] {
                expected.push((name.to_owned(), 1, rustler::SchedulerFlags::Normal as u32));
            }
        }
        if cfg!(feature = "scalar-vec") {
            expected.push((
                "replace_first_i64".to_owned(),
                2,
                rustler::SchedulerFlags::Normal as u32,
            ));
            for name in ["echo_flags", "echo_signed_bytes"] {
                expected.push((name.to_owned(), 1, rustler::SchedulerFlags::Normal as u32));
            }
        }
        if cfg!(feature = "checked-option") {
            expected.push((
                "checked_analyse".to_owned(),
                1,
                rustler::SchedulerFlags::Normal as u32,
            ));
        }
        if cfg!(feature = "derived-list") {
            expected.push((
                "derived_list".to_owned(),
                2,
                rustler::SchedulerFlags::Normal as u32,
            ));
        }
        if cfg!(feature = "validated-decoder") {
            expected.extend([
                (
                    "validated_flag".to_owned(),
                    1,
                    rustler::SchedulerFlags::Normal as u32,
                ),
                (
                    "validated_result".to_owned(),
                    1,
                    rustler::SchedulerFlags::Normal as u32,
                ),
            ]);
        }
        if cfg!(feature = "string-errors") {
            expected.extend([
                (
                    "string_error".to_owned(),
                    1,
                    rustler::SchedulerFlags::Normal as u32,
                ),
                (
                    "string_term".to_owned(),
                    1,
                    rustler::SchedulerFlags::DirtyCpu as u32,
                ),
            ]);
        }
        if cfg!(feature = "boxed-errors") {
            expected.extend([
                (
                    "boxed_error".to_owned(),
                    2,
                    rustler::SchedulerFlags::Normal as u32,
                ),
                (
                    "boxed_term".to_owned(),
                    2,
                    rustler::SchedulerFlags::DirtyCpu as u32,
                ),
            ]);
        }
        if cfg!(feature = "nif-result") {
            expected.extend([
                (
                    "forwarded_result".to_owned(),
                    2,
                    rustler::SchedulerFlags::Normal as u32,
                ),
                (
                    "explicit_result".to_owned(),
                    2,
                    rustler::SchedulerFlags::DirtyCpu as u32,
                ),
                (
                    "echo_term".to_owned(),
                    1,
                    rustler::SchedulerFlags::Normal as u32,
                ),
            ]);
        }
        if cfg!(feature = "custom-decoder") {
            expected.push((
                "decoded_flag".to_owned(),
                2,
                rustler::SchedulerFlags::Normal as u32,
            ));
        }
        if cfg!(feature = "derived-tagged") {
            expected.push((
                "tagged_reply".to_owned(),
                2,
                rustler::SchedulerFlags::DirtyCpu as u32,
            ));
        }
        for (enabled, name) in [
            (cfg!(feature = "derived-map"), "derived_map"),
            (cfg!(feature = "derived-struct"), "derived_struct"),
        ] {
            if enabled {
                expected.push((name.to_owned(), 2, rustler::SchedulerFlags::Normal as u32));
            }
        }
        if cfg!(feature = "derived-tuple") {
            expected.push((
                "derived_pair".to_owned(),
                2,
                rustler::SchedulerFlags::Normal as u32,
            ));
        }
        if cfg!(feature = "collections") {
            expected.push((
                "replace_first".to_owned(),
                2,
                rustler::SchedulerFlags::Normal as u32,
            ));
        }
        expected.sort();
        assert_eq!(metadata, expected);
    }
}
