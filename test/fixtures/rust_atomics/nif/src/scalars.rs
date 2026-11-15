//! Derived scalar codecs, including the SDK's integer narrowing behavior.
use crate::Counter;
use rustler::ResourceArc;

macro_rules! scalar_nif {
    ($record:ident, $function:ident, $scalar:ty) => {
        #[derive(rustler::NifTuple)]
        struct $record {
            value: $scalar,
        }
        #[rustler::nif]
        #[lynx::scalars]
        fn $function(input: $record) -> $scalar {
            input.value
        }
    };
}

scalar_nif!(BoolValue, scalar_bool, bool);
scalar_nif!(I8Value, scalar_i8, i8);
scalar_nif!(I16Value, scalar_i16, i16);
scalar_nif!(I32Value, scalar_i32, i32);
scalar_nif!(I64Value, scalar_i64, i64);
scalar_nif!(U8Value, scalar_u8, u8);
scalar_nif!(U16Value, scalar_u16, u16);
scalar_nif!(U32Value, scalar_u32, u32);
scalar_nif!(U64Value, scalar_u64, u64);

/// A mixed-width request controlling an actual cross-crate update.
#[derive(rustler::NifTuple)]
pub struct Request {
    enabled: bool,
    signed: i8,
    unsigned: u16,
}

/// A negative narrowed value suppresses the update; unsigned narrowing sets it.
pub fn counter_scalar(resource: ResourceArc<Counter>, request: Request) -> (i8, u16, bool, u64) {
    let (matched, previous) = if request.enabled && request.signed >= 0 {
        atomic_analysis::try_set(&resource.state, 0, u64::from(request.unsigned))
    } else {
        (false, atomic_core::current(&resource.state))
    };
    (request.signed, request.unsigned, matched, previous)
}

#[rustler::nif(name = "atomic_scalar", schedule = "DirtyCpu")]
#[lynx::scalars]
fn mixed(resource: ResourceArc<Counter>, request: Request) -> (i8, u16, bool, u64) {
    counter_scalar(resource, request)
}
