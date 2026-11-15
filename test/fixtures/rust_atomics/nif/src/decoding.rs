//! First-party decoding composed with shared atomic resource operations.
use crate::Counter;
use rustler::{Decoder, Error, NifResult, ResourceArc, Term};

/// A scalar protocol request with an extracted custom decoder.
pub struct Request {
    value: u64,
}

fn decode_via<'a, T: Decoder<'a>>(term: Term<'a>) -> NifResult<T> {
    T::decode(term)
}

/// Internal dictionary composition, independent of NIF exposure.
#[lynx::decoded]
pub fn decode_request(term: Term<'_>) -> NifResult<Request> {
    decode_via::<Request>(term)
}

impl<'a> Decoder<'a> for Request {
    fn decode(term: Term<'a>) -> NifResult<Self> {
        match decode_via::<u64>(term) {
            Ok(value) => match value {
                2 => panic!("decoder rejected request"),
                3 => Err(Error::RaiseAtom("rust_panicked")),
                4 => Err(Error::Atom("decoder_rejected")),
                5 => Err(Error::BadArg),
                _ => Ok(Self { value }),
            },
            Err(error) => Err(error),
        }
    }
}

/// A decoded request selects a real cross-crate update or a read.
pub fn counter_decoded(resource: ResourceArc<Counter>, request: Request, enabled: bool) -> u64 {
    if request.value != 0 && enabled {
        atomic_analysis::claim_two(&resource.state).0
    } else {
        atomic_core::current(&resource.state)
    }
}

#[rustler::nif(name = "atomic_decoded", schedule = "DirtyCpu")]
#[lynx::decoded]
fn decoded(resource: ResourceArc<Counter>, request: Request, enabled: bool) -> u64 {
    counter_decoded(resource, request, enabled)
}

#[rustler::nif(name = "atomic_decoded_first")]
#[lynx::decoded]
fn decoded_first(request: Request, resource: ResourceArc<Counter>) -> u64 {
    counter_decoded(resource, request, true)
}
