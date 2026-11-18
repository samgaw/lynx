//! Installed into Charon's test suite for the combined runtime profile.

use charon_lib::llbc_ast::{
    BodyVisitable, DropKind, FieldId, LocalId, PlaceKind, ProjectionElem, Statement, StatementKind,
};

mod util;

#[test]
fn owning_payload_retains_panic_cleanup_and_compiler_destructor() -> anyhow::Result<()> {
    let data = util::translate_rust_text(
        r#"//@ charon-args=--lift-associated-types=* --treat-box-as-builtin --ops-to-function-calls --index-to-function-calls --reconstruct-fallible-operations --reconstruct-panic-calls --reconstruct-matches --hide-marker-traits --hide-allocator --remove-unused-self-clauses --remove-adt-clauses --unbind-item-vars --deallocate-all-locals --no-gen-tuple-structs --owned-drops --mir=optimized --sysroot=default --opaque=core --opaque=std --opaque=alloc --start-from=crate::checked
pub struct Payload { pub bytes: Vec<u8> }
pub fn checked(payload: Payload, accepted: bool) -> usize {
    assert!(accepted);
    payload.bytes.len()
}
fn main() {}
"#,
    )?;
    let find = |name: &str| {
        data.fun_decls
            .iter()
            .find(|decl| decl.item_meta.name.debug_repr(&data) == name)
            .unwrap_or_else(|| panic!("missing extracted implementation: {name}"))
    };
    let checked = find("test_crate::checked");
    let body = &checked.body.as_structured().expect("checked body").body;
    let mut panics = 0;
    body.dyn_visit_in_body(|statement: &Statement| {
        assert!(!matches!(statement.kind, StatementKind::Assert { .. }));
        if let StatementKind::Panic { on_unwind, .. } = &statement.kind {
            panics += 1;
            let mut drops = 0;
            on_unwind.dyn_visit_in_body(|cleanup: &Statement| {
                if let StatementKind::Drop { kind, place, .. } = &cleanup.kind {
                    assert!(matches!(kind, DropKind::Precise));
                    assert_eq!(place.kind, PlaceKind::Local(LocalId::new(1)));
                    drops += 1;
                }
            });
            assert_eq!(drops, 1, "panic must destroy the still-owned payload");
        }
    });
    assert_eq!(panics, 1, "the source assertion must retain its panic edge");

    let destructor = find("test_crate::Payload::drop_owned");
    assert!(destructor.item_meta.started_from);
    assert!(!destructor.signature.is_unsafe);
    assert_eq!(destructor.signature.inputs, checked.signature.inputs[..1]);
    let body = &destructor
        .body
        .as_structured()
        .expect("compiler drop body")
        .body;
    assert!(body.statements.iter().any(|statement| matches!(
        &statement.kind, StatementKind::Drop { kind: DropKind::Precise, place, .. }
            if matches!(&place.kind, PlaceKind::Projection(base, ProjectionElem::Field(None, field))
                if base.kind == PlaceKind::Local(LocalId::new(1)) && *field == FieldId::new(0))
    )), "the actual compiler destructor must destroy the owned vector field");
    Ok(())
}
