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
                + usize::from(cfg!(feature = "collections"))
                + 4 * usize::from(cfg!(feature = "optional"))
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
