//! Recognizes the generated Rustler 0.39 loader and resource inventory configuration.
use serde_json::{json, Value};
use syn::visit::{self, Visit};
use syn::{Expr, GenericArgument, Item, ItemConst, ItemFn, Lit, PathArguments, Type};

fn path_is(path: &syn::Path, names: &[&str]) -> bool {
    path.segments.len() == names.len()
        && path
            .segments
            .iter()
            .zip(names)
            .all(|(part, name)| part.ident == *name)
}

fn constructor(expr: &Expr) -> Option<(String, Option<String>)> {
    let (expr, name) = if let Expr::MethodCall(call) = expr {
        if call.method != "with_name" || call.turbofish.is_some() || call.args.len() != 1 {
            return None;
        }
        let Expr::Lit(literal) = call.args.first()? else {
            return None;
        };
        let Lit::Str(name) = &literal.lit else {
            return None;
        };
        let name = name.value();
        if name.is_empty()
            || !name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b"_:.-".contains(&b))
        {
            return None;
        }
        (&*call.receiver, Some(name))
    } else {
        (expr, None)
    };
    let Expr::Call(call) = expr else { return None };
    let Expr::Path(path) = &*call.func else {
        return None;
    };
    if path.qself.is_some()
        || !call.args.is_empty()
        || !path_is(
            &path.path,
            &["rustler", "codegen_runtime", "ResourceRegistration", "new"],
        )
    {
        return None;
    }
    let PathArguments::AngleBracketed(args) = &path.path.segments.last()?.arguments else {
        return None;
    };
    if args.args.len() != 1 {
        return None;
    }
    let GenericArgument::Type(Type::Path(ty)) = args.args.first()? else {
        return None;
    };
    if ty.qself.is_some()
        || ty
            .path
            .segments
            .iter()
            .any(|p| !matches!(p.arguments, PathArguments::None))
    {
        return None;
    }
    let prefix = if ty.path.leading_colon.is_some() {
        "::"
    } else {
        ""
    };
    Some((
        format!(
            "{prefix}{}",
            ty.path
                .segments
                .iter()
                .map(|p| p.ident.to_string())
                .collect::<Vec<_>>()
                .join("::")
        ),
        name,
    ))
}

#[derive(Default)]
struct RegistrationCalls(bool);
impl<'ast> Visit<'ast> for RegistrationCalls {
    fn visit_expr_path(&mut self, expr: &'ast syn::ExprPath) {
        if path_is(
            &expr.path,
            &["rustler", "codegen_runtime", "ResourceRegistration", "new"],
        ) {
            self.0 = true;
        }
        visit::visit_expr_path(self, expr);
    }
}

fn registration(item: &ItemConst) -> Result<Option<Value>, String> {
    let mut calls = RegistrationCalls::default();
    calls.visit_item_const(item);
    if !calls.0 {
        return Ok(None);
    }
    let Expr::Block(block) = &*item.expr else {
        return Err("unsupported resource inventory block".into());
    };
    let [syn::Stmt::Item(Item::Static(node)), syn::Stmt::Item(Item::Fn(_)), syn::Stmt::Item(Item::Static(ctor))] =
        block.block.stmts.as_slice()
    else {
        return Err("unsupported resource inventory/constructor configuration".into());
    };
    let Expr::Struct(node_value) = &*node.expr else {
        return Err("missing resource inventory node".into());
    };
    let Some(value) = node_value
        .fields
        .iter()
        .find(|f| matches!(&f.member, syn::Member::Named(n) if n == "value"))
    else {
        return Err("missing resource inventory value".into());
    };
    let Expr::Reference(reference) = &value.expr else {
        return Err("unsupported resource inventory reference".into());
    };
    let Expr::Block(value) = &*reference.expr else {
        return Err("unsupported resource constructor block".into());
    };
    let [syn::Stmt::Expr(expression, None)] = value.block.stmts.as_slice() else {
        return Err("unsupported resource constructor statements".into());
    };
    let (ty, name) =
        constructor(expression).ok_or("unsupported resource registration constructor")?;
    let section = ctor
        .attrs
        .iter()
        .find_map(|a| {
            if !a.path().is_ident("link_section") {
                return None;
            }
            let syn::Meta::NameValue(v) = &a.meta else {
                return None;
            };
            let Expr::Lit(v) = &v.value else { return None };
            let Lit::Str(v) = &v.lit else { return None };
            Some(v.value())
        })
        .ok_or("resource constructor is missing its linker section")?;
    if ![".init_array", "__DATA,__mod_init_func,mod_init_funcs"].contains(&section.as_str()) {
        return Err("unsupported resource constructor linker section".into());
    }
    let constructor = format!(
        "rustler::codegen_runtime::ResourceRegistration::new::<{ty}>(){}",
        name.as_ref()
            .map(|n| format!(".with_name({n:?})"))
            .unwrap_or_default()
    );
    let expected: ItemConst = syn::parse_str(&format!(
        r#"
      #[allow(non_upper_case_globals)] const _: () = {{
        static __INVENTORY: ::inventory::Node = ::inventory::Node {{
          value: &{{ {constructor} }},
          next: ::inventory::__private::UnsafeCell::new(::inventory::__private::Option::None),
        }};
        unsafe extern "C" fn __ctor() {{ unsafe {{
          ::inventory::ErasedNode::submit(__INVENTORY.value, &__INVENTORY)
        }} }}
        #[used] #[link_section = {section:?}]
        static __CTOR: unsafe extern "C" fn() = __ctor;
      }};
    "#
    ))
    .map_err(|e| e.to_string())?;
    let mut actual = item.clone();
    let mut expected = expected;
    NormalizeStrings.visit_item_const_mut(&mut actual);
    NormalizeStrings.visit_item_const_mut(&mut expected);
    if actual != expected {
        return Err("resource inventory differs from the supported generated constructor".into());
    }
    Ok(Some(json!({"type_hint": ty, "name": name})))
}

struct NormalizeStrings;
impl syn::visit_mut::VisitMut for NormalizeStrings {
    fn visit_lit_str_mut(&mut self, literal: &mut syn::LitStr) {
        *literal = syn::LitStr::new(&literal.value(), literal.span());
    }
}
use syn::visit_mut::VisitMut;
fn same_function(left: &ItemFn, right: &ItemFn) -> bool {
    let mut left = left.clone();
    let mut right = right.clone();
    NormalizeStrings.visit_item_fn_mut(&mut left);
    NormalizeStrings.visit_item_fn_mut(&mut right);
    left == right
}

fn loader(crate_name: &str, module: &str) -> Result<ItemFn, String> {
    syn::parse_str(&format!(r#"
      #[no_mangle]
      extern "C" fn {crate_name}_nif_init() -> *const ::rustler::codegen_runtime::ErlNifEntry {{
        unsafe {{ ::rustler::codegen_runtime::internal_write_symbols() }}
        static mut NIF_ENTRY: Option<rustler::codegen_runtime::ErlNifEntry> = None;
        let nif_funcs: Box<[_]> = rustler::codegen_runtime::inventory::iter::<rustler::Nif>()
          .map(rustler::Nif::get_def).collect();
        let load = {{
          extern "C" fn nif_load(env: *mut rustler::sys::ErlNifEnv,
            _priv_data: *mut *mut rustler::codegen_runtime::c_void,
            load_info: rustler::sys::ErlNifTerm) -> rustler::codegen_runtime::c_int {{
            unsafe {{
              let mut env = rustler::Env::new_init_env(&env, env);
              let load_info = rustler::Term::new(env, load_info);
              if !rustler::codegen_runtime::ResourceRegistration::register_all_collected(env).is_ok() {{ return 1; }}
              None.map_or(0, |inner| {{ rustler::codegen_runtime::handle_nif_init_call(inner, env, load_info) }})
            }}
          }};
          nif_load
        }};
        let entry = rustler::codegen_runtime::ErlNifEntry::new(unsafe {{
          ::core::ffi::CStr::from_bytes_with_nul_unchecked({module:?}.as_bytes())
        }}, &nif_funcs, load);
        unsafe {{ std::mem::forget(nif_funcs); NIF_ENTRY = Some(entry); NIF_ENTRY.as_ref().unwrap() }}
      }}
    "#, module = format!("{module}\0"))).map_err(|e| e.to_string())
}

#[derive(Default)]
struct Registrations {
    modules: Vec<String>,
    functions: Vec<Vec<String>>,
    entries: Vec<Value>,
    errors: Vec<String>,
    anonymous: std::collections::BTreeMap<Vec<String>, usize>,
}
impl<'ast> Visit<'ast> for Registrations {
    fn visit_item_mod(&mut self, module: &'ast syn::ItemMod) {
        self.modules.push(module.ident.to_string());
        visit::visit_item_mod(self, module);
        self.modules.pop();
    }
    // Module-level anonymous constants have compiler disambiguators independent
    // of function/impl bodies. Resource inventories are module items.
    fn visit_item_fn(&mut self, item: &'ast ItemFn) {
        let mut path = self.modules.clone();
        path.push(item.sig.ident.to_string());
        self.functions.push(path);
    }
    fn visit_item_impl(&mut self, _item: &'ast syn::ItemImpl) {}
    fn visit_item_const(&mut self, item: &'ast ItemConst) {
        let ordinal = self.anonymous.entry(self.modules.clone()).or_default();
        let index = *ordinal;
        if item.ident == "_" {
            *ordinal += 1;
        }
        match registration(item) {
            Ok(Some(mut entry)) => {
                entry["modules"] = json!(self.modules);
                entry["anonymous_index"] = json!(index);
                self.entries.push(entry);
            }
            Ok(None) => {}
            Err(e) => self.errors.push(e),
        }
    }
}

/// Validate the generated loader and inventory before resolving compiler identities.
pub(super) fn discover(file: &syn::File, crate_name: &str, module: &str) -> Result<Value, String> {
    let expected = loader(crate_name, module)?;
    let functions: Vec<_> = file
        .items
        .iter()
        .filter_map(|i| if let Item::Fn(f) = i { Some(f) } else { None })
        .collect();
    if functions
        .iter()
        .filter(|f| f.sig.ident == expected.sig.ident)
        .count()
        != 1
        || !functions.iter().any(|f| same_function(f, &expected))
    {
        return Err("resource support requires the generated Rustler 0.39 loader without a custom load callback".into());
    }
    let shim: ItemFn = syn::parse_str(&format!(r#"#[no_mangle] fn nif_init() -> *const ::rustler::codegen_runtime::ErlNifEntry {{ {crate_name}_nif_init() }}"#)).map_err(|e| e.to_string())?;
    if !functions.iter().any(|f| same_function(f, &shim)) {
        return Err("unsupported primary NIF initialization shim".into());
    }
    let mut visitor = Registrations::default();
    visitor.visit_file(file);
    if !visitor.errors.is_empty() {
        return Err(visitor.errors.join("\n"));
    }
    // A container selector can also match ordinary module functions. Their
    // signatures may contain unsupported coroutine types; they are irrelevant
    // to registration discovery. Never exclude the validated loader or functions
    // nested inside the inventory constants whose actual bodies are audited.
    let loader = format!("{crate_name}_nif_init");
    let excluded_functions: Vec<_> = visitor
        .functions
        .into_iter()
        .filter(|path| path.as_slice() != [loader.as_str()])
        .map(|path| format!("{crate_name}::{}", path.join("::")))
        .collect();
    Ok(json!({"registrations": visitor.entries, "loader": loader,
        "excluded_functions": excluded_functions}))
}

#[cfg(test)]
mod tests {
    use super::*;

    const INVENTORY: &str = r#"
      #[allow(non_upper_case_globals)] const _: () = {
        static __INVENTORY: ::inventory::Node = ::inventory::Node {
          value: &{ rustler::codegen_runtime::ResourceRegistration::new::<crate::State>() },
          next: ::inventory::__private::UnsafeCell::new(::inventory::__private::Option::None),
        };
        unsafe extern "C" fn __ctor() { unsafe {
          ::inventory::ErasedNode::submit(__INVENTORY.value, &__INVENTORY)
        } }
        #[used] #[link_section = ".init_array"]
        static __CTOR: unsafe extern "C" fn() = __ctor;
      };
    "#;

    #[test]
    fn requires_linked_constructor_and_exact_inventory_submission() {
        let item: ItemConst = syn::parse_str(INVENTORY).expect("fixture must parse");
        let entry = registration(&item)
            .expect("generated inventory")
            .expect("resource");
        assert_eq!(entry["type_hint"], "crate::State");
        for invalid in [
            INVENTORY.replace("#[used]", ""),
            INVENTORY.replace(".init_array", ".data"),
            INVENTORY.replace(
                "__INVENTORY.value, &__INVENTORY",
                "__INVENTORY.value, &OTHER",
            ),
            INVENTORY.replace("::submit", "::other"),
            INVENTORY.replace(
                "new::<crate::State>()",
                "new::<crate::State>(); side_effect()",
            ),
        ] {
            let item: ItemConst = syn::parse_str(&invalid).expect("mutation must parse");
            assert!(
                registration(&item).is_err(),
                "accepted altered inventory: {invalid}"
            );
        }
    }

    #[test]
    fn tracks_module_inventory_disambiguators_without_function_constants() {
        let file = syn::parse_file(&format!(
            "const _: u8 = 0; fn unrelated() {{ const _: u8 = 1; }} {INVENTORY} const _: u8 = 2;"
        ))
        .expect("fixture");
        let mut registrations = Registrations::default();
        registrations.visit_file(&file);
        assert!(registrations.errors.is_empty());
        assert_eq!(registrations.entries.len(), 1);
        assert_eq!(registrations.entries[0]["anonymous_index"], 1);
        assert_eq!(registrations.functions, vec![vec!["unrelated"]]);
    }

    #[test]
    fn separates_module_functions_from_required_nested_registration_bodies() {
        let file = syn::parse_file(&format!(
            "async fn unrelated() {{}} mod nested {{ async fn another() {{}} {INVENTORY} }}"
        ))
        .expect("fixture");
        let mut registrations = Registrations::default();
        registrations.visit_file(&file);
        assert!(registrations.errors.is_empty());
        assert_eq!(
            registrations.functions,
            vec![vec!["unrelated"], vec!["nested", "another"]]
        );
        assert_eq!(registrations.entries.len(), 1);
        assert_eq!(registrations.entries[0]["modules"], json!(["nested"]));
    }

    #[test]
    fn ignores_unrelated_constants_but_rejects_hidden_resource_initializers() {
        let unrelated: ItemConst = syn::parse_str("const VALUE: u64 = 7;").expect("fixture");
        assert_eq!(registration(&unrelated).expect("constant"), None);
        let hidden: ItemConst = syn::parse_str(
            "const _: () = { fn hidden() { rustler::codegen_runtime::ResourceRegistration::new::<State>(); } };"
        ).expect("fixture");
        assert!(registration(&hidden).is_err());
    }

    #[test]
    fn literal_normalization_preserves_values_and_rejects_changed_loader_bodies() {
        let generated = loader("fixture", "Elixir.Native").expect("loader");
        let mut changed = generated.clone();
        changed
            .block
            .stmts
            .push(syn::parse_str("side_effect();").expect("statement"));
        assert!(!same_function(&generated, &changed));
        let escaped: ItemFn = syn::parse_str(r#"fn value() { "x\u{0}"; }"#).expect("function");
        let plain: ItemFn = syn::parse_str(r#"fn value() { "x\0"; }"#).expect("function");
        assert!(same_function(&escaped, &plain));
        let different: ItemFn = syn::parse_str(r#"fn value() { "y\0"; }"#).expect("function");
        assert!(!same_function(&escaped, &different));
    }
}
