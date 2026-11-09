//! Reads Rustler's expanded inventory records without translating Rust bodies.
#[path = "../atom_cache.rs"]
mod atom_cache;
#[path = "../resource_registration.rs"]
mod resource_registration;
use serde_json::{json, Value};
use std::io::{self, Read};
use syn::visit::{self, Visit};
use syn::{Expr, FnArg, ItemFn, Lit, Member, ReturnType, Type};

// syn does not yet parse rustc's expanded `super let` temporary scopes. Their
// lifetime semantics are irrelevant to inventory/signature discovery. Adapt
// tokens only here; extraction still consumes the unchanged actual Rust code,
// and the discovered export table is checked against the compiled library.
fn metadata_tokens(tokens: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    use proc_macro2::{Group, TokenTree};
    let mut input = tokens.into_iter().peekable();
    let mut output = proc_macro2::TokenStream::new();
    while let Some(token) = input.next() {
        if matches!(&token, TokenTree::Ident(id) if id == "super")
            && matches!(input.peek(), Some(TokenTree::Ident(id)) if id == "let")
        {
            continue;
        }
        let token = match token {
            TokenTree::Group(group) => {
                let mut adapted = Group::new(group.delimiter(), metadata_tokens(group.stream()));
                adapted.set_span(group.span());
                TokenTree::Group(adapted)
            }
            token => token,
        };
        output.extend([token]);
    }
    output
}

fn parse_expanded(source: &str) -> Result<syn::File, String> {
    let tokens = source
        .parse()
        .map_err(|e| format!("cannot tokenize expanded Rust: {e}"))?;
    syn::parse2(metadata_tokens(tokens)).map_err(|e| format!("cannot parse expanded Rust: {e}"))
}

#[derive(Default)]
struct Bindings {
    selected: Option<Vec<(String, u32)>>,
    modules: Vec<String>,
    entries: Vec<Value>,
    errors: Vec<String>,
}

#[derive(Default)]
struct Functions {
    stack: Vec<String>,
    originals: Vec<ItemFn>,
}

impl<'ast> Visit<'ast> for Functions {
    fn visit_item_fn(&mut self, item: &'ast ItemFn) {
        if self.stack == ["nif_func", "wrapper"] {
            self.originals.push(item.clone());
            return;
        }
        self.stack.push(item.sig.ident.to_string());
        visit::visit_item_fn(self, item);
        self.stack.pop();
    }
}

#[derive(Default)]
struct Literals(Vec<Lit>);
impl<'ast> Visit<'ast> for Literals {
    fn visit_lit(&mut self, literal: &'ast Lit) {
        self.0.push(literal.clone());
    }
}

fn single_literal(expression: &Expr) -> Result<Lit, String> {
    let mut visitor = Literals::default();
    visitor.visit_expr(expression);
    match visitor.0.as_slice() {
        [literal] => Ok(literal.clone()),
        _ => Err("expected one literal in Rustler inventory field".into()),
    }
}

fn supported_type(ty: &Type, output: bool) -> Result<Value, String> {
    if let Type::Tuple(tuple) = ty {
        if tuple.elems.len() <= 7 {
            let fields: Result<Vec<_>, _> = tuple
                .elems
                .iter()
                .map(|ty| supported_type(ty, output))
                .collect();
            return Ok(json!({"tuple": fields?}));
        }
    }
    if let Type::Path(path) = ty {
        let names: Vec<_> = path
            .path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect();
        if path.qself.is_none()
            && (names == ["ResourceArc"]
                || names == ["rustler", "ResourceArc"]
                || names == ["rustler", "resource", "ResourceArc"]
                || names == ["rustler", "resource", "arc", "ResourceArc"])
        {
            let segment = path
                .path
                .segments
                .last()
                .ok_or("missing ResourceArc segment")?;
            if let syn::PathArguments::AngleBracketed(arguments) = &segment.arguments {
                if arguments.args.len() == 1 {
                    if let Some(syn::GenericArgument::Type(Type::Path(payload))) =
                        arguments.args.first()
                    {
                        if payload.qself.is_none()
                            && payload
                                .path
                                .segments
                                .iter()
                                .all(|s| matches!(s.arguments, syn::PathArguments::None))
                        {
                            let name: Vec<_> = payload
                                .path
                                .segments
                                .iter()
                                .map(|s| s.ident.to_string())
                                .collect();
                            return Ok(json!({"resource": name}));
                        }
                    }
                }
            }
            return Err("Rustler ResourceArc requires a monomorphic payload path".into());
        }
        if path.qself.is_none()
            && (names == ["Vec"]
                || names == ["std", "vec", "Vec"]
                || names == ["alloc", "vec", "Vec"])
        {
            let segment = path.path.segments.last().ok_or("missing Vec segment")?;
            if let syn::PathArguments::AngleBracketed(arguments) = &segment.arguments {
                if arguments.args.len() == 1 {
                    if let Some(syn::GenericArgument::Type(element)) = arguments.args.first() {
                        if supported_type(element, output)? == json!("u8") {
                            return Ok(json!({"vec": "u8"}));
                        }
                    }
                }
            }
            return Err("Rustler Vec currently requires exactly one u8 element type".into());
        }
        if path.qself.is_none()
            && (names == ["Binary"]
                || names == ["rustler", "Binary"]
                || names == ["rustler", "types", "binary", "Binary"])
        {
            let segment = path.path.segments.last().ok_or("missing Binary segment")?;
            match &segment.arguments {
                syn::PathArguments::None => return Ok(json!("binary")),
                syn::PathArguments::AngleBracketed(arguments) if arguments.args.len() == 1 => {
                    if matches!(arguments.args.first(), Some(syn::GenericArgument::Lifetime(lifetime)) if lifetime.ident == "_")
                    {
                        return Ok(json!("binary"));
                    }
                }
                _ => {}
            }
            return Err("Rustler Binary requires an elided lifetime".into());
        }
        if path.qself.is_none()
            && (names == ["Option"]
                || names == ["core", "option", "Option"]
                || names == ["std", "option", "Option"])
        {
            let segment = path.path.segments.last().ok_or("missing Option segment")?;
            if let syn::PathArguments::AngleBracketed(arguments) = &segment.arguments {
                if let [syn::GenericArgument::Type(inner)] =
                    arguments.args.iter().collect::<Vec<_>>().as_slice()
                {
                    return Ok(json!({"option": supported_type(inner, output)?}));
                }
            }
            return Err("Rustler Option requires one supported value type".into());
        }
        if path.qself.is_none()
            && (names == ["Result"]
                || names == ["core", "result", "Result"]
                || names == ["std", "result", "Result"])
        {
            let segment = path.path.segments.last().ok_or("missing Result segment")?;
            if let syn::PathArguments::AngleBracketed(arguments) = &segment.arguments {
                if arguments.args.len() == 2 {
                    let fields: Result<Vec<_>, _> = arguments
                        .args
                        .iter()
                        .map(|argument| match argument {
                            syn::GenericArgument::Type(ty) => supported_type(ty, output),
                            _ => Err("unsupported Rustler Result argument".into()),
                        })
                        .collect();
                    return Ok(json!({"result": fields?}));
                }
            }
            return Err("Rustler Result requires two supported value types".into());
        }
        if path.qself.is_none() && path.path.segments.len() == 1 {
            let segment = &path.path.segments[0];
            let name = segment.ident.to_string();
            if matches!(segment.arguments, syn::PathArguments::None)
                && ["bool", "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64"]
                    .contains(&name.as_str())
            {
                return Ok(json!(name));
            }
        }
        // This is a discovery hint, not an approved codec. The backend must
        // resolve the compiled return type and extract its actual Encoder.
        if output
            && path.qself.is_none()
            && !names.is_empty()
            && !["f32", "f64", "i128", "u128", "isize", "usize", "str"]
                .contains(&names.last().expect("nonempty path").as_str())
            && path
                .path
                .segments
                .iter()
                .all(|segment| matches!(segment.arguments, syn::PathArguments::None))
        {
            return Ok(json!({"native": names}));
        }
    }
    Err("unsupported Rustler parameter or return type".into())
}

impl Bindings {
    fn entry(&self, item: &syn::ExprStruct) -> Result<Value, String> {
        let field = |name: &str| -> Result<&Expr, String> {
            item.fields
                .iter()
                .find_map(|field| match &field.member {
                    Member::Named(ident) if ident == name => Some(&field.expr),
                    _ => None,
                })
                .ok_or_else(|| format!("Rustler inventory field missing: {name}"))
        };
        let Lit::Str(name) = single_literal(field("name")?)? else {
            return Err("Rustler export name is not a string literal".into());
        };
        let name = name.value();
        let name = name
            .strip_suffix('\0')
            .ok_or("Rustler export is not NUL terminated")?;
        if name.contains('\0') {
            return Err("Rustler export contains an embedded NUL".into());
        }
        let Lit::Int(arity) = single_literal(field("arity")?)? else {
            return Err("Rustler arity is not an integer literal".into());
        };
        let arity: u32 = arity
            .base10_parse()
            .map_err(|e| format!("invalid arity: {e}"))?;
        let Expr::Cast(flags) = field("flags")? else {
            return Err("unsupported Rustler scheduler expression".into());
        };
        let Expr::Path(flags) = &*flags.expr else {
            return Err("unsupported Rustler scheduler flag".into());
        };
        let flag_path: Vec<_> = flags
            .path
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect();
        if flag_path.len() != 3 || flag_path[0] != "rustler" || flag_path[1] != "SchedulerFlags" {
            return Err("unsupported Rustler scheduler path".into());
        }
        let flags = match flag_path.last().map(String::as_str) {
            Some("Normal") => 0,
            Some("DirtyCpu") => 1,
            Some("DirtyIo") => 2,
            _ => return Err("unknown Rustler scheduler flag".into()),
        };
        // Every export's metadata is checked against the compiled table, even
        // when its computation is outside this verification request.
        if self
            .selected
            .as_ref()
            .is_some_and(|selected| !selected.iter().any(|(n, a)| n == name && *a == arity))
        {
            return Ok(json!({"name": name, "arity": arity, "flags": flags}));
        }
        let mut functions = Functions::default();
        functions.visit_expr(field("raw_func")?);
        let [function] = functions.originals.as_slice() else {
            return Err("cannot identify the original function in Rustler's wrapper".into());
        };
        if !matches!(function.sig.safety, syn::Safety::Default)
            || function.sig.asyncness.is_some()
            || !function.sig.generics.params.is_empty()
            || function.sig.variadic.is_some()
            || function.sig.abi.is_some()
        {
            return Err(format!(
                "unsupported Rustler signature: {}",
                function.sig.ident
            ));
        }
        let arguments: Result<Vec<_>, _> = function
            .sig
            .inputs
            .iter()
            .map(|arg| match arg {
                FnArg::Typed(typed) => supported_type(&typed.ty, false),
                _ => Err("Rustler receiver parameters are unsupported".into()),
            })
            .collect();
        let arguments = arguments?;
        if arguments.len() != arity as usize {
            return Err("Rustler export arity differs from its computation signature".into());
        }
        let result = match &function.sig.output {
            ReturnType::Type(_, result) => supported_type(result, true)?,
            ReturnType::Default => json!({"tuple": []}),
        };
        Ok(json!({"name": name, "arity": arity, "flags": flags,
            "rust_name": function.sig.ident.to_string(), "modules": self.modules,
            "arguments": arguments, "result": result}))
    }
}

impl<'ast> Visit<'ast> for Bindings {
    fn visit_item_mod(&mut self, module: &'ast syn::ItemMod) {
        self.modules.push(module.ident.to_string());
        visit::visit_item_mod(self, module);
        self.modules.pop();
    }
    fn visit_expr_struct(&mut self, item: &'ast syn::ExprStruct) {
        let path: Vec<_> = item
            .path
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect();
        if path == ["rustler", "Nif"] {
            match self.entry(item) {
                Ok(entry) => self.entries.push(entry),
                Err(error) => self.errors.push(error),
            }
            return;
        }
        visit::visit_expr_struct(self, item);
    }
}

fn run() -> Result<(), String> {
    let mut source = String::new();
    if let Some(path) = std::env::args_os().nth(1) {
        source = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    } else {
        io::stdin()
            .read_to_string(&mut source)
            .map_err(|e| e.to_string())?;
    }
    let file = parse_expanded(&source)?;
    if std::env::args().nth(2).as_deref() == Some("--resources") {
        let selection: Value = serde_json::from_str(
            &std::env::args()
                .nth(3)
                .ok_or("missing resource selection")?,
        )
        .map_err(|e| e.to_string())?;
        let crate_name = selection["crate"]
            .as_str()
            .ok_or("missing resource crate")?;
        let module = selection["module"]
            .as_str()
            .ok_or("missing resource module")?;
        println!(
            "{}",
            resource_registration::discover(&file, crate_name, module)?
        );
        return Ok(());
    }
    if std::env::args().nth(2).as_deref() == Some("--atoms") {
        let selected: Vec<Vec<String>> = serde_json::from_str(
            &std::env::args()
                .nth(3)
                .ok_or("--atoms requires a module selection")?,
        )
        .map_err(|e| e.to_string())?;
        println!("{}", json!(atom_cache::discover(&file, &selected)?));
        return Ok(());
    }
    let selected = std::env::args()
        .nth(2)
        .map(|argument| serde_json::from_str(&argument).map_err(|e| e.to_string()))
        .transpose()?;
    let mut visitor = Bindings {
        selected,
        ..Bindings::default()
    };
    visitor.visit_file(&file);
    if !visitor.errors.is_empty() {
        return Err(visitor.errors.join("\n"));
    }
    if visitor.entries.is_empty() {
        return Err("no Rustler inventory records found in expanded crate".into());
    }
    println!("{}", json!(visitor.entries));
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn discover(signature: &str, arity: u32) -> Bindings {
        discover_selected(signature, arity, None)
    }

    fn discover_selected(
        signature: &str,
        arity: u32,
        selected: Option<Vec<(String, u32)>>,
    ) -> Bindings {
        let source = r#"
          mod nested {
            const _: () = { rustler::Nif {
              name: "renamed\0".as_ptr() as *const i8,
              arity: $ARITY,
              flags: rustler::SchedulerFlags::DirtyIo as u32,
              raw_func: {
                unsafe extern "C" fn nif_func() {
                  fn wrapper() {
                    let _ = move || { $SIGNATURE };
                  }
                }
                nif_func
              }
            }; };
          }
        "#
        .replace("$SIGNATURE", signature)
        .replace("$ARITY", &arity.to_string());
        let file = parse_expanded(&source).expect("valid expanded Rust syntax");
        let mut visitor = Bindings {
            selected,
            ..Bindings::default()
        };
        visitor.visit_file(&file);
        visitor
    }

    #[test]
    fn discovers_exports_with_expanded_pin_temporary_scopes() {
        let bindings = discover(
            "fn native(a: bool) -> bool { { super let mut pinned = a; pinned } }",
            1,
        );
        assert!(bindings.errors.is_empty(), "{:?}", bindings.errors);
        assert_eq!(bindings.entries[0]["arguments"], json!(["bool"]));
        assert_eq!(bindings.entries[0]["result"], json!("bool"));
        let file =
            parse_expanded("fn f() { let text = \"super let\"; super::f(); /* super let */ }")
                .expect("literal and parent module paths remain valid");
        let mut literals = Literals::default();
        literals.visit_file(&file);
        assert!(matches!(&literals.0[..], [Lit::Str(s)] if s.value() == "super let"));
        assert!(parse_expanded("fn f() { super other } ").is_err());
    }

    #[test]
    fn finds_renamed_export_scheduler_and_original_signature() {
        let bindings = discover("fn native(a: bool, b: i64) -> bool { a }", 2);
        assert!(bindings.errors.is_empty(), "{:?}", bindings.errors);
        assert_eq!(
            bindings.entries,
            vec![json!({"name":"renamed", "arity":2,
          "flags":2, "rust_name":"native", "modules":["nested"],
          "arguments":["bool", "i64"], "result":"bool"})]
        );
    }

    #[test]
    fn discovers_resource_hints_and_rejects_nonconcrete_payloads() {
        let bindings = discover("fn native(a: rustler::ResourceArc<State>) -> rustler::ResourceArc<types::State> { todo!() }", 1);
        assert!(bindings.errors.is_empty(), "{:?}", bindings.errors);
        assert_eq!(
            bindings.entries[0]["arguments"],
            json!([{"resource": ["State"]}])
        );
        assert_eq!(
            bindings.entries[0]["result"],
            json!({"resource": ["types", "State"]})
        );
        for signature in [
            "fn native(a: rustler::ResourceArc<State<u64>>) -> bool { true }",
            "fn native(a: rustler::ResourceArc<&State>) -> bool { true }",
            "fn native(a: rustler::ResourceArc<State, Other>) -> bool { true }",
        ] {
            assert_eq!(discover(signature, 1).errors.len(), 1, "{signature}");
        }
    }

    #[test]
    fn rejects_unsupported_signatures_and_arity_mismatch() {
        for (signature, arity) in [
            ("fn native(a: bool) -> bool { a }", 2),
            ("fn native(a: String) -> bool { true }", 1),
            ("unsafe fn native(a: bool) -> bool { a }", 1),
            ("fn native<T>(a: bool) -> bool { a }", 1),
            ("fn native(a: (bool, f64)) -> bool { true }", 1),
            ("fn native(a: Result<bool, String>) -> bool { true }", 1),
            (
                "fn native(a: (bool,bool,bool,bool,bool,bool,bool,bool)) -> bool { true }",
                1,
            ),
        ] {
            let bindings = discover(signature, arity);
            assert!(bindings.entries.is_empty(), "{signature}");
            assert_eq!(bindings.errors.len(), 1, "{signature}");
        }
    }

    #[test]
    fn discovers_nested_options_and_rejects_invalid_parameters() {
        let bindings = discover("fn native(a: Option<Option<bool>>) -> core::option::Option<(bool, Result<u8, i64>)> { todo!() }", 1);
        assert!(bindings.errors.is_empty(), "{:?}", bindings.errors);
        assert_eq!(
            bindings.entries[0]["arguments"],
            json!([{"option":{"option":"bool"}}])
        );
        assert_eq!(
            bindings.entries[0]["result"],
            json!({"option":{"tuple":["bool", {"result":["u8","i64"]}]}})
        );
        for signature in [
            "fn native(a: Option<bool, u8>) -> bool { true }",
            "fn native(a: other::Option<bool>) -> bool { true }",
            "fn native(a: Option<String>) -> bool { true }",
        ] {
            let invalid = discover(signature, 1);
            assert!(invalid.entries.is_empty(), "{signature}");
            assert_eq!(invalid.errors.len(), 1, "{signature}");
        }
    }

    #[test]
    fn discovers_recursive_composite_types_and_unit_returns() {
        let bindings = discover("fn native(a: ((bool,), (i64, ()))) -> std::result::Result<u8, (bool, i64)> { todo!() }", 1);
        assert!(bindings.errors.is_empty(), "{:?}", bindings.errors);
        assert_eq!(
            bindings.entries[0]["arguments"],
            json!([
                {"tuple":[{"tuple":["bool"]}, {"tuple":["i64", {"tuple":[]}]}]}
            ])
        );
        assert_eq!(
            bindings.entries[0]["result"],
            json!({"result":["u8", {"tuple":["bool","i64"]}]})
        );
        let unit = discover("fn native() {}", 0);
        assert!(unit.errors.is_empty(), "{:?}", unit.errors);
        assert_eq!(unit.entries[0]["result"], json!({"tuple":[]}));
    }

    #[test]
    fn discovers_nominal_return_hints_without_accepting_custom_arguments() {
        let bindings = discover(
            "fn native(a: u64) -> Result<(), errors::BridgeError> { todo!() }",
            1,
        );
        assert!(bindings.errors.is_empty(), "{:?}", bindings.errors);
        assert_eq!(
            bindings.entries[0]["result"],
            json!({"result": [{"tuple": []}, {"native": ["errors", "BridgeError"]}]})
        );
        for signature in [
            "fn native(a: BridgeError) -> bool { true }",
            "fn native() -> f64 { 0.0 }",
            "fn native() -> Error<u64> { todo!() }",
        ] {
            assert_eq!(
                discover(signature, u32::from(signature.contains("a:")))
                    .errors
                    .len(),
                1
            );
        }
    }

    #[test]
    fn discovers_binary_values_but_rejects_explicit_lifetime_contracts() {
        let bindings = discover(
            "fn native(value: rustler::Binary<'_>) -> Binary<'_> { value }",
            1,
        );
        assert!(bindings.errors.is_empty(), "{:?}", bindings.errors);
        assert_eq!(bindings.entries[0]["arguments"], json!(["binary"]));
        assert_eq!(bindings.entries[0]["result"], json!("binary"));
        let unsupported = discover(
            "fn native(value: rustler::Binary<'static>) -> bool { true }",
            1,
        );
        assert_eq!(unsupported.errors.len(), 1);
    }

    #[test]
    fn discovers_byte_vectors_without_approving_other_elements_or_allocators() {
        let bindings = discover(
            "fn native(value: Vec<u8>) -> (bool, std::vec::Vec<u8>) { todo!() }",
            1,
        );
        assert!(bindings.errors.is_empty(), "{:?}", bindings.errors);
        assert_eq!(bindings.entries[0]["arguments"], json!([{"vec": "u8"}]));
        assert_eq!(
            bindings.entries[0]["result"],
            json!({"tuple": ["bool", {"vec": "u8"}]})
        );
        for source in [
            "fn native(value: Vec<bool>) -> bool { true }",
            "fn native(value: Vec<u8, CustomAllocator>) -> bool { true }",
            "fn native(value: other::Vec<u8>) -> bool { true }",
        ] {
            assert_eq!(discover(source, 1).errors.len(), 1);
        }
    }

    #[test]
    fn retains_export_metadata_without_claiming_an_unselected_signature() {
        let bindings = discover_selected(
            "fn native(a: f64) -> f64 { a }",
            1,
            Some(vec![("another".into(), 1)]),
        );
        assert!(bindings.errors.is_empty(), "{:?}", bindings.errors);
        assert_eq!(
            bindings.entries,
            vec![json!({"name":"renamed", "arity":1, "flags":2})]
        );
        let selected = discover_selected(
            "fn native(a: f64) -> f64 { a }",
            1,
            Some(vec![("renamed".into(), 1)]),
        );
        assert_eq!(selected.errors.len(), 1);
        assert!(selected.entries.is_empty());
    }
}
