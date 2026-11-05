//! Recognizes Rustler's generated constant atom cache without accepting arbitrary statics.

use serde_json::{json, Value};
use syn::{Expr, Item, ItemFn, Lit, Member, Pat, PathArguments, ReturnType, Stmt, Type};

fn path_is(path: &syn::Path, expected: &[&str]) -> bool {
    path.segments.len() == expected.len()
        && path.segments.iter().zip(expected).all(|(segment, name)| {
            segment.ident == *name && matches!(segment.arguments, PathArguments::None)
        })
}

fn expression_path_is(expression: &Expr, expected: &[&str]) -> bool {
    matches!(expression, Expr::Path(value) if value.qself.is_none() && path_is(&value.path, expected))
}

fn type_path_is(ty: &Type, expected: &[&str]) -> bool {
    matches!(ty, Type::Path(value) if value.qself.is_none() && path_is(&value.path, expected))
}

fn atom_type(ty: &Type) -> bool {
    type_path_is(ty, &["rustler", "types", "atom", "Atom"])
}

fn call<'a>(expression: &'a Expr, expected: &[&str], arity: usize) -> Option<&'a syn::ExprCall> {
    match expression {
        Expr::Call(value)
            if expression_path_is(&value.func, expected) && value.args.len() == arity =>
        {
            Some(value)
        }
        _ => None,
    }
}

fn closure(expression: &Expr) -> Option<&syn::ExprClosure> {
    match expression {
        Expr::Closure(value)
            if value.constness.is_none()
                && value.asyncness.is_none()
                && value.capture.is_none()
                && value.lifetimes.is_none()
                && matches!(value.output, ReturnType::Default) =>
        {
            Some(value)
        }
        _ => None,
    }
}

fn literal(expression: &Expr) -> Option<String> {
    match expression {
        Expr::Lit(value) => match &value.lit {
            Lit::Str(text) => Some(text.value()),
            _ => None,
        },
        _ => None,
    }
}

fn tail(block: &syn::Block) -> Option<&Expr> {
    match block.stmts.as_slice() {
        [Stmt::Expr(expression, None)] => Some(expression),
        _ => None,
    }
}

fn plain_signature(signature: &syn::Signature) -> bool {
    signature.constness.is_none()
        && signature.asyncness.is_none()
        && matches!(signature.safety, syn::Safety::Default)
        && signature.abi.is_none()
        && signature.variadic.is_none()
        && signature.generics.params.is_empty()
        && signature.generics.where_clause.is_none()
        && signature.inputs.is_empty()
}

fn getter(function: &ItemFn, field: &syn::Ident) -> bool {
    if function.sig.ident != *field
        || !plain_signature(&function.sig)
        || !matches!(&function.sig.output, ReturnType::Type(_, ty) if atom_type(ty))
    {
        return false;
    }
    matches!(tail(&function.block), Some(Expr::Field(value))
        if value.member == Member::Named(field.clone()) && call(&value.base, &["RustlerAtoms", "get"], 0).is_some())
}

fn initializer(block: &syn::Block) -> Option<&syn::ExprStruct> {
    let [Stmt::Item(Item::Use(import)), Stmt::Item(Item::Static(cache)), Stmt::Expr(Expr::MethodCall(get), None)] =
        block.stmts.as_slice()
    else {
        return None;
    };
    let syn::UseTree::Path(std) = &import.tree else {
        return None;
    };
    let syn::UseTree::Path(sync) = &*std.tree else {
        return None;
    };
    if std.ident != "std"
        || sync.ident != "sync"
        || !matches!(&*sync.tree, syn::UseTree::Name(name) if name.ident == "OnceLock")
        || cache.ident != "RUSTLER_ATOMS"
        || !matches!(cache.mutability, syn::StaticMutability::None)
        || call(&cache.expr, &["OnceLock", "new"], 0).is_none()
        || get.method != "get_or_init"
        || get.turbofish.is_some()
        || get.args.len() != 1
        || !expression_path_is(&get.receiver, &["RUSTLER_ATOMS"])
    {
        return None;
    }
    let Type::Path(cache_type) = &*cache.ty else {
        return None;
    };
    if cache_type.qself.is_some() || cache_type.path.segments.len() != 1 {
        return None;
    }
    let segment = cache_type.path.segments.first()?;
    let PathArguments::AngleBracketed(args) = &segment.arguments else {
        return None;
    };
    if segment.ident != "OnceLock"
        || args.args.len() != 1
        || !matches!(args.args.first(), Some(syn::GenericArgument::Type(ty)) if type_path_is(ty, &["RustlerAtoms"]))
    {
        return None;
    }
    let initialize = closure(get.args.first()?)?;
    if !initialize.inputs.is_empty() {
        return None;
    }
    let Expr::MethodCall(run) = &*initialize.body else {
        return None;
    };
    if run.method != "run"
        || run.turbofish.is_some()
        || run.args.len() != 1
        || call(&run.receiver, &["rustler", "env", "OwnedEnv", "new"], 0).is_none()
    {
        return None;
    }
    let run_body = closure(run.args.first()?)?;
    if !matches!(run_body.inputs.iter().collect::<Vec<_>>().as_slice(), [Pat::Ident(name)]
        if name.ident == "env" && name.by_ref.is_none() && name.mutability.is_none() && name.subpat.is_none())
    {
        return None;
    }
    let Expr::Block(body) = &*run_body.body else {
        return None;
    };
    match tail(&body.block)? {
        Expr::Struct(value)
            if value.qself.is_none()
                && path_is(&value.path, &["RustlerAtoms"])
                && value.rest.is_none() =>
        {
            Some(value)
        }
        _ => None,
    }
}

fn cache(items: &[Item]) -> Result<Value, String> {
    let structure = items
        .iter()
        .find_map(|item| match item {
            Item::Struct(value) if value.ident == "RustlerAtoms" => Some(value),
            _ => None,
        })
        .ok_or("missing RustlerAtoms declaration")?;
    if !structure.generics.params.is_empty() || structure.generics.where_clause.is_some() {
        return Err("generic RustlerAtoms cache is unsupported".into());
    }
    let syn::Fields::Named(fields) = &structure.fields else {
        return Err("RustlerAtoms cache must have named fields".into());
    };
    let implementations: Vec<_> = items
        .iter()
        .filter_map(|item| match item {
            Item::Impl(value) if type_path_is(&value.self_ty, &["RustlerAtoms"]) => Some(value),
            _ => None,
        })
        .collect();
    let [implementation] = implementations.as_slice() else {
        return Err("expected exactly one RustlerAtoms implementation".into());
    };
    if implementation.trait_.is_some()
        || implementation.unsafety.is_some()
        || !implementation.generics.params.is_empty()
        || implementation.generics.where_clause.is_some()
    {
        return Err("unsupported RustlerAtoms implementation".into());
    }
    let [syn::ImplItem::Fn(get)] = implementation.items.as_slice() else {
        return Err("RustlerAtoms implementation must contain only get".into());
    };
    if get.sig.ident != "get"
        || !plain_signature(&get.sig)
        || !matches!(&get.sig.output, ReturnType::Type(_, ty) if matches!(&**ty, Type::Reference(reference)
            if reference.mutability.is_none() && reference.lifetime.as_ref().is_some_and(|l| l.ident == "static")
                && type_path_is(&reference.elem, &["Self"])))
    {
        return Err("unsupported RustlerAtoms::get signature".into());
    }
    let initialized =
        initializer(&get.block).ok_or("unsupported RustlerAtoms cache initialization")?;
    if initialized.fields.len() != fields.named.len() || fields.named.is_empty() {
        return Err("inconsistent RustlerAtoms initializer fields".into());
    }
    let mut atoms = Vec::new();
    for (field, value) in fields.named.iter().zip(&initialized.fields) {
        let name = field.ident.as_ref().ok_or("unnamed RustlerAtoms field")?;
        if !atom_type(&field.ty)
            || value.member != Member::Named(name.clone())
            || value.colon_token.is_none()
        {
            return Err("inconsistent RustlerAtoms field identity or type".into());
        }
        let Expr::MethodCall(expect) = &value.expr else {
            return Err("missing atom expect".into());
        };
        if expect.method != "expect"
            || expect.turbofish.is_some()
            || expect.args.len() != 1
            || literal(expect.args.first().ok_or("missing expect argument")?).as_deref()
                != Some("rustler::atoms!: bad atom string")
        {
            return Err("unsupported atom failure conversion".into());
        }
        let from_str = call(
            &expect.receiver,
            &["rustler", "types", "atom", "Atom", "from_str"],
            2,
        )
        .ok_or("unsupported atom constructor")?;
        if !expression_path_is(&from_str.args[0], &["env"]) {
            return Err("inconsistent atom environment".into());
        }
        let text = literal(&from_str.args[1]).ok_or("atom name must be a literal")?;
        if !text.is_ascii() || text.len() > 255 || text.contains('\0') {
            return Err("only ASCII atom names up to 255 bytes without NUL are supported".into());
        }
        let getters: Vec<_> = items
            .iter()
            .filter_map(|item| match item {
                Item::Fn(function) if function.sig.ident == *name => Some(function),
                _ => None,
            })
            .collect();
        if !matches!(getters.as_slice(), [function] if getter(function, name)) {
            return Err(format!("missing or altered Rustler atom getter {name}"));
        }
        atoms.push(json!({"field": name.to_string(), "atom": text}));
    }
    Ok(json!({"structure": "RustlerAtoms", "fields": atoms}))
}

pub(super) fn discover(file: &syn::File, selected: &[Vec<String>]) -> Result<Vec<Value>, String> {
    fn walk(
        items: &[Item],
        path: &mut Vec<String>,
        selected: &[Vec<String>],
        result: &mut Vec<Value>,
    ) -> Result<(), String> {
        if selected.contains(path)
            && items
                .iter()
                .any(|item| matches!(item, Item::Struct(value) if value.ident == "RustlerAtoms"))
        {
            let mut entry = cache(items)
                .map_err(|error| format!("Rustler atom cache in {}: {error}", path.join("::")))?;
            entry["modules"] = json!(path);
            result.push(entry);
        }
        for item in items {
            if let Item::Mod(module) = item {
                if let Some((_, items)) = &module.content {
                    path.push(module.ident.to_string());
                    walk(items, path, selected, result)?;
                    path.pop();
                }
            }
        }
        Ok(())
    }
    let mut result = Vec::new();
    walk(&file.items, &mut Vec::new(), selected, &mut result)?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    const SOURCE: &str = r#"
      mod native {
        struct RustlerAtoms { invalid: ::rustler::types::atom::Atom }
        impl RustlerAtoms {
          fn get() -> &'static Self {
            use std::sync::OnceLock;
            static RUSTLER_ATOMS: OnceLock<RustlerAtoms> = OnceLock::new();
            RUSTLER_ATOMS.get_or_init(|| ::rustler::env::OwnedEnv::new().run(|env| {
              RustlerAtoms {
                invalid: ::rustler::types::atom::Atom::from_str(env, "renamed")
                  .expect("rustler::atoms!: bad atom string"),
              }
            }))
          }
        }
        pub fn invalid() -> ::rustler::types::atom::Atom { RustlerAtoms::get().invalid }
      }
    "#;

    fn parse(source: &str) -> Result<Vec<Value>, String> {
        discover(
            &syn::parse_file(source).expect("valid Rust fixture syntax"),
            &[vec!["native".into()]],
        )
    }

    #[test]
    fn discovers_actual_literal_instead_of_inventing_a_getter_name_mapping() {
        assert_eq!(
            parse(SOURCE).expect("supported generated cache"),
            vec![json!({
                "modules": ["native"], "structure": "RustlerAtoms",
                "fields": [{"field": "invalid", "atom": "renamed"}]
            })]
        );
    }

    #[test]
    fn rejects_changes_to_initialization_and_getter_behavior() {
        for (from, to) in [
            ("static RUSTLER_ATOMS:", "static mut RUSTLER_ATOMS:"),
            ("OnceLock<RustlerAtoms>", "OnceLock<Other>"),
            ("OnceLock::new()", "OnceLock::other()"),
            ("get_or_init(||", "get_or_init(move ||"),
            ("OwnedEnv::new()", "OwnedEnv::other()"),
            (".run(|env|", ".run(|other|"),
            ("from_str(env,", "from_str(other,"),
            ("from_str(env, \"renamed\")", "from_str(env, dynamic())"),
            (
                "{ RustlerAtoms::get().invalid }",
                "{ side_effect(); RustlerAtoms::get().invalid }",
            ),
            ("RustlerAtoms::get().invalid", "RustlerAtoms::get().other"),
            ("fn get()", "unsafe fn get()"),
            ("&'static Self", "&'static mut Self"),
            ("bad atom string", "different panic"),
        ] {
            assert!(
                SOURCE.contains(from),
                "mutation must change the fixture: {from}"
            );
            assert!(
                parse(&SOURCE.replace(from, to)).is_err(),
                "must reject {from} => {to}"
            );
        }
    }

    #[test]
    fn rejects_unbounded_names_and_ignores_unselected_modules() {
        for text in ["é".into(), "a".repeat(256), r"a\0".into()] {
            assert!(
                parse(&SOURCE.replace("renamed", &text)).is_err(),
                "unsupported atom {text:?}"
            );
        }
        let file = syn::parse_file(&SOURCE.replace("from_str", "other")).expect("valid fixture");
        assert_eq!(
            discover(&file, &[vec!["elsewhere".into()]]).expect("unselected cache"),
            Vec::<Value>::new()
        );
    }
}
