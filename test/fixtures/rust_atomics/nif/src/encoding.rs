//! Extracted return encoders composed with shared native state.
use crate::Counter;
use rustler::{Encoder, Env, Error, NifResult, ResourceArc, Term};

/// Previous and resulting values, encoded in declaration order.
#[derive(rustler::NifTuple)]
pub struct Reply {
    previous: u64,
    current: u64,
}

/// Internal update and response construction through both library crates.
pub fn counter_reply(resource: ResourceArc<Counter>, expected: u64, replacement: u64) -> Reply {
    let (matched, previous) = atomic_analysis::try_set(&resource.state, expected, replacement);
    Reply {
        previous,
        current: if matched { replacement } else { previous },
    }
}

/// A scalar response whose actual encoder rejects zero.
pub struct CheckedReply {
    value: u64,
}

impl Encoder for CheckedReply {
    /// # Panics
    /// Panics if the response value is zero.
    fn encode<'a>(&self, env: Env<'a>) -> Term<'a> {
        assert!(self.value != 0, "cannot encode a zero response");
        self.value.encode(env)
    }
}

#[rustler::nif(name = "atomic_reply", schedule = "DirtyCpu")]
#[lynx::encoded]
fn reply(resource: ResourceArc<Counter>, expected: u64, replacement: u64) -> Reply {
    counter_reply(resource, expected, replacement)
}

#[rustler::nif(name = "atomic_reply_option")]
#[lynx::encoded]
fn optional(
    resource: ResourceArc<Counter>,
    expected: u64,
    replacement: u64,
) -> Option<CheckedReply> {
    let response = counter_reply(resource, expected, replacement);
    if response.current == 0 {
        None
    } else {
        Some(CheckedReply {
            value: response.current,
        })
    }
}

#[rustler::nif(name = "atomic_reply_result")]
#[lynx::encoded]
fn result(resource: ResourceArc<Counter>, expected: u64, replacement: u64) -> Result<Reply, u64> {
    let response = counter_reply(resource, expected, replacement);
    if response.previous == expected {
        Ok(response)
    } else {
        Err(response.previous)
    }
}

#[rustler::nif(name = "atomic_reply_tuple")]
#[lynx::encoded]
fn tuple(resource: ResourceArc<Counter>, expected: u64, replacement: u64) -> (Reply, u64) {
    let response = counter_reply(resource, expected, replacement);
    let current = response.current;
    (response, current)
}

#[rustler::nif(name = "atomic_reply_checked")]
#[lynx::encoded]
fn checked(resource: ResourceArc<Counter>, expected: u64, replacement: u64) -> CheckedReply {
    let response = counter_reply(resource, expected, replacement);
    CheckedReply {
        value: response.current,
    }
}

#[rustler::nif(name = "atomic_reply_nif_result")]
#[lynx::encoded]
fn returned(resource: ResourceArc<Counter>, expected: u64, replacement: u64) -> NifResult<Reply> {
    if expected == u64::MAX {
        Err(Error::RaiseAtom("rust_panicked"))
    } else {
        Ok(counter_reply(resource, expected, replacement))
    }
}
