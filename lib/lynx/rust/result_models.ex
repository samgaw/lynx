defmodule Lynx.Rust.ResultModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, FileModels, FormatModels}

  # A shared variant observation does not decode, move or destroy its payloads.
  # Reuse upstream Aeneas's observer while checking the actual Rust interface.
  def resolve(
        %{
          "body" => "Opaque",
          "src" => "Normal",
          "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["core", 0]},
              %{"Ident" => ["result", 0]},
              %{
                "Impl" => %{
                  "Ty" => %{
                    "kind" => "InherentImplBlock",
                    "skip_binder" => parent,
                    "params" => parent_params
                  }
                }
              },
              %{"Ident" => ["is_ok", 0]}
            ]
          },
          "generics" => params
        },
        translated,
        refs
      ) do
    expand = &CallModels.expand(&1, refs)
    t = variable(0)
    e = variable(1)

    with [%{"Ref" => [%{"Var" => %{"Free" => 0}}, self, "Shared"]}] <- expand.(sig["inputs"]),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <- self,
         true <- LLBC.result_type?(id, %{translated: translated, references: refs}),
         true <- args == arguments([t, e]),
         true <- free_parent(expand.(parent)) == self,
         true <- parameters?(parent_params, 2),
         [%{"index" => 0}] <- params["regions"],
         true <- parameters?(params |> Map.put("regions", []) |> Map.put("outlives", []), 2),
         true <-
           expand.(params["outlives"]) ==
             Enum.map([t, e], fn type ->
               %{
                 "regions" => [],
                 "outlives" => [],
                 "skip_binder" => [%{"Lub" => type}, %{"Var" => %{"Free" => 0}}]
               }
             end),
         true <- expand.(sig["output"]) == %{"Scalar" => "Bool"} do
      %{
        rust_name: "core::result::{core::result::Result<@T, @E>}::is_ok",
        lean: "Aeneas.Std.core.result.Result.is_ok",
        builtin: true,
        can_fail: true,
        lift: false,
        label:
          "Aeneas shared Result::is_ok variant observer; payloads are borrowed and not destroyed; Rust core implementation unverified"
      }
    else
      _ -> nil
    end
  end

  # Aeneas's map_err model invokes the actual FnOnce implementation, but does
  # not drop an unused callback on Ok. Admit only capture-free compiler closures
  # with NoopDestruct; captured state and user-written FnOnce implementations
  # require an explicit destructor model instead.
  def resolve(
        %{
          "body" => "Opaque",
          "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["core", 0]},
              %{"Ident" => ["result", 0]},
              %{"Impl" => %{"Ty" => %{"skip_binder" => parent, "params" => parent_params}}},
              %{"Ident" => ["map_err", 0]}
            ]
          },
          "generics" => generics
        },
        translated,
        refs
      ) do
    expand = &CallModels.expand(&1, refs)

    with [input, callback] <- Enum.map(sig["inputs"], expand),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <- input,
         true <- LLBC.result_type?(id, %{translated: translated, references: refs}),
         true <- args == arguments([variable(0), variable(1)]),
         true <- expand.(parent) |> free_parent() == input,
         true <- parameters?(parent_params, 2),
         true <- callback == variable(3),
         true <-
           expand.(sig["output"]) ==
             put_in(input, ["Adt", "generics"], arguments([variable(0), variable(2)])),
         %{"trait_clauses" => [fn_once, destruct]} <- generics,
         true <- parameters?(%{generics | "trait_clauses" => []}, 4),
         {0, fn_once_id, [functor, tuple, output]} <- clause(fn_once, refs),
         true <- functor == variable(3) and output == variable(2),
         true <- tuple?(tuple, [variable(1)]),
         true <- trait?(translated, fn_once_id, ~w(core ops function FnOnce), 3),
         {1, destruct_id, [destruct_type]} <- clause(destruct, refs),
         true <- destruct_type == variable(3),
         true <- trait?(translated, destruct_id, ~w(core marker Destruct), 1) do
      %{
        rust_name: "core::result::{core::result::Result<@T, @E>}::map_err",
        lean: "Aeneas.Std.core.result.Result.map_err",
        builtin: true,
        can_fail: true,
        lift: false,
        callback: :capture_free,
        fn_once_trait: fn_once_id,
        destruct_trait: destruct_id,
        label:
          "Aeneas Result::map_err with an extracted capture-free FnOnce callback and validated NoopDestruct; Rust core implementation not verified"
      }
    else
      _ -> nil
    end
  end

  # The standard combinator is modeled, while its compiler-generated callback
  # must have an actual extracted body and no observable skipped destructor.
  def resolve(
        %{
          "body" => "Opaque",
          "src" => "Normal",
          "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["core", 0]},
              %{"Ident" => ["option", 0]},
              %{
                "Impl" => %{
                  "Ty" => %{
                    "kind" => "InherentImplBlock",
                    "skip_binder" => parent,
                    "params" => parent_params
                  }
                }
              },
              %{"Ident" => ["and_then", 0]}
            ]
          },
          "generics" => generics
        },
        translated,
        refs
      ) do
    expand = &CallModels.expand(&1, refs)

    with [input, callback] <- expand.(sig["inputs"]),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <- input,
         true <- args == arguments([variable(0)]),
         type when not is_nil(type) <- declaration(translated["type_decls"], id),
         true <- Lynx.Rust.OptionModels.option_type?(type, refs),
         true <- expand.(parent) |> free_parent() == input,
         true <- parameters?(parent_params, 1),
         true <- callback == variable(2),
         output = put_in(input, ["Adt", "generics"], arguments([variable(1)])),
         true <- expand.(sig["output"]) == output,
         %{"trait_clauses" => [fn_once, destruct]} <- generics,
         true <- parameters?(%{generics | "trait_clauses" => []}, 3),
         {0, fn_once_id, [functor, tuple, result]} <- clause(fn_once, refs),
         true <- functor == variable(2) and result == output,
         true <- tuple?(tuple, [variable(0)]),
         true <- trait?(translated, fn_once_id, ~w(core ops function FnOnce), 3),
         {1, destruct_id, [destruct_type]} <- clause(destruct, refs),
         true <- destruct_type == variable(2),
         true <- trait?(translated, destruct_id, ~w(core marker Destruct), 1) do
      %{
        rust_name: "core::option::{core::option::Option<@T>}::and_then",
        backend_rust_name: "core::option::_::and_then",
        lean: "Lynx.Rust.Option.andThen",
        builtin: false,
        can_fail: true,
        lift: false,
        callback: :capture_free,
        fn_once_trait: fn_once_id,
        destruct_trait: destruct_id,
        option_callback_type: id,
        model_hash: Lynx.Rust.OptionModels.fingerprint(),
        label:
          "Option::and_then model with actual extracted capture-free compiler FnOnce and validated NoopDestruct; Rust core implementation not verified"
      }
    else
      _ -> nil
    end
  end

  def resolve(_, _, _), do: nil

  # Encoder construction must prove Ok. Err formatting, panic hooks and error
  # destruction are not modeled as successful or catchable computation.
  def resolve_encoder_unwrap(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["core", 0]},
               %{"Ident" => ["result", 0]},
               %{
                 "Impl" => %{
                   "Ty" => %{
                     "kind" => "InherentImplBlock",
                     "skip_binder" => parent,
                     "params" => parent_params
                   }
                 }
               },
               %{"Ident" => ["unwrap", 0]}
             ]
           },
           "generics" => %{"regions" => [], "trait_clauses" => [debug]} = params
         } <- function,
         [input] <- CallModels.expand(sig["inputs"], refs),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <- input,
         true <- LLBC.result_type?(id, %{translated: translated, references: refs}),
         true <- args == arguments([variable(0), variable(1)]),
         true <- free_parent(CallModels.expand(parent, refs)) == input,
         true <- parameters?(parent_params, 2),
         true <- parameters?(%{params | "trait_clauses" => []}, 2),
         true <- CallModels.expand(sig["output"], refs) == variable(0),
         {0, debug_id, [error]} <- clause(debug, refs),
         true <- error == variable(1) and trait?(translated, debug_id, ~w(core fmt Debug), 1) do
      %{
        rust_name: "core::result::{core::result::Result<@T, @E>}::unwrap",
        lean: "Lynx.Rustler.Encoding.unwrapOk",
        backend_rust_name: "lynx_rustler::result_unwrap_ok",
        encoder_unwrap_ok: true,
        builtin: false,
        can_fail: true,
        lift: false,
        keep_trait_clauses: [false],
        native_cutoff_only: true,
        label:
          "Result::unwrap successful-Ok model: transfers the actual payload; Err formatting, hooks, error destruction and unwind exhaust verification; no panic or Rust core implementation correctness claim"
      }
    else
      _ -> nil
    end
  end

  # A successful expect does not call Debug or drop an error. The Err path is
  # deliberately exhausted: formatting, destructors and unwind are not erased
  # into an apparently verified panic. This adapter is runtime-only.
  def resolve_native_expect(
        %{
          "body" => "Opaque",
          "src" => "Normal",
          "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["core", 0]},
              %{"Ident" => ["result", 0]},
              %{
                "Impl" => %{
                  "Ty" => %{
                    "kind" => "InherentImplBlock",
                    "skip_binder" => parent,
                    "params" => parent_params
                  }
                }
              },
              %{"Ident" => ["expect", 0]}
            ]
          },
          "generics" => %{"regions" => [%{"index" => 0}], "trait_clauses" => [debug]} = params
        },
        translated,
        refs
      ) do
    expand = &CallModels.expand(&1, refs)

    with [
           input,
           %{
             "Ref" => [
               %{"Var" => %{"Free" => 0}},
               %{"Adt" => %{"builtin" => "Str", "generics" => str_args}},
               "Shared"
             ]
           }
         ] <- expand.(sig["inputs"]),
         true <- str_args == arguments([]),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <- input,
         true <- LLBC.result_type?(id, %{translated: translated, references: refs}),
         true <- args == arguments([variable(0), variable(1)]),
         true <- free_parent(expand.(parent)) == input and parameters?(parent_params, 2),
         true <- parameters?(%{params | "regions" => [], "trait_clauses" => []}, 2),
         true <- expand.(sig["output"]) == variable(0),
         {0, debug_id, [error]} <- clause(debug, refs),
         true <- error == variable(1) and trait?(translated, debug_id, ~w(core fmt Debug), 1) do
      %{
        rust_name: "core::result::{core::result::Result<@T, @E>}::expect",
        lean: "Lynx.NativeM.expectOk",
        backend_rust_name: "lynx_native::result_expect_ok",
        native_expect_ok: true,
        builtin: false,
        can_fail: true,
        lift: true,
        keep_trait_clauses: [false],
        native_transfer: true,
        native_cutoff_only: true,
        label:
          "Native Result::expect successful-Ok model with exact Result, signature and Debug-bound validation; Debug is unused on Ok; Err formatting, destruction and unwind exhaust verification; Rust core implementation not verified"
      }
    else
      _ -> nil
    end
  end

  def resolve_native_expect(_, _, _), do: nil

  # The erased Debug dictionary may still be emitted by Aeneas. Give its exact
  # standard I/O-error method a nonreturning definition for elaboration only.
  # LLBC excludes these entries from callable models: no Rust implementation may
  # rely on this unsupported formatter, directly or through an indirect call.
  def resolve_unused_io_debug(function, translated, refs) do
    resolve_unused_error_debug(
      function,
      translated,
      refs,
      FileModels.error_declaration(translated),
      ~w(core io error),
      "core::io::error::{core::fmt::Debug<core::io::error::Error>}::fmt",
      "Lynx.NativeIoError.debugUnavailable"
    )
  end

  def resolve_unused_encoder_debug(function, translated, refs) do
    error = named(translated["type_decls"], ~w(rustler error Error))

    if match?(%{"kind" => "Opaque"}, error) do
      resolve_unused_error_debug(
        function,
        translated,
        refs,
        error,
        ~w(rustler error),
        "rustler::error::{core::fmt::Debug<rustler::error::Error>}::fmt",
        "Lynx.Rustler.Encoding.debugUnavailable"
      )
    end
  end

  defp resolve_unused_error_debug(function, translated, refs, declaration, scope, rust_name, lean) do
    with %{
           "body" => "Opaque",
           "src" => %{"TraitImpl" => source},
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "generics" => params
         } <- function,
         %{"def_id" => error} <- declaration,
         %{"def_id" => formatter} <- named(translated["type_decls"], ~w(core fmt Formatter)),
         %{"def_id" => fmt_error} <- named(translated["type_decls"], ~w(core fmt Error)),
         %{"def_id" => debug} <- named(translated["trait_decls"], ~w(core fmt Debug)),
         true <- trait?(translated, debug, ~w(core fmt Debug), 1),
         impl when not is_nil(impl) <-
           declaration(translated["trait_impls"], source["impl_ref"]["id"]),
         true <-
           impl["src"] == "Normal" and impl["is_unsafe"] == false and impl["is_negative"] == false,
         true <- parameters?(impl["generics"], 0),
         true <-
           Enum.take(impl["item_meta"]["name"], length(scope)) ==
             Enum.map(scope, &%{"Ident" => [&1, 0]}),
         true <-
           function["item_meta"]["name"] ==
             impl["item_meta"]["name"] ++ [%{"Ident" => ["fmt", 0]}],
         true <-
           CallModels.expand(impl["impl_trait"], refs) == %{
             "id" => debug,
             "generics" => arguments([adt(error)])
           },
         true <-
           FormatModels.method_identity?(function, impl, debug, %{
             translated: translated,
             refs: refs
           }),
         regions when is_list(regions) <- params["regions"],
         true <- Enum.map(regions, & &1["index"]) == [0, 1, 2],
         true <- parameters?(%{params | "regions" => [], "outlives" => []}, 0),
         true <-
           params["outlives"] == [
             %{"regions" => [], "outlives" => [], "skip_binder" => [region(2), region(1)]}
           ],
         true <-
           CallModels.expand(sig["inputs"], refs) == [
             %{"Ref" => [region(0), adt(error), "Shared"]},
             %{
               "Ref" => [
                 region(1),
                 put_in(adt(formatter), ["Adt", "generics", "regions"], [region(2)]),
                 "Mut"
               ]
             }
           ],
         %{"Adt" => %{"id" => result, "builtin" => nil, "generics" => args}} <-
           CallModels.expand(sig["output"], refs),
         true <- LLBC.result_type?(result, %{translated: translated, references: refs}),
         true <-
           match?([_, _], args["types"]),
         [unit, result_error] <- args["types"],
         true <-
           tuple?(unit, []) and result_error == adt(fmt_error) and
             args == arguments([unit, result_error]) do
      %{
        rust_name: rust_name,
        lean: lean,
        builtin: false,
        can_fail: true,
        lift: false,
        elaboration_only: true,
        formatting_unavailable: true,
        native_cutoff_only: true,
        label:
          "Unused standard error Debug dictionary elaboration only; formatter calls are unsupported and rejected; no formatting behavior verified"
      }
    else
      _ -> nil
    end
  end

  defp named(values, path),
    do:
      Enum.find(
        values || [],
        &(&1 && &1["item_meta"]["name"] == Enum.map(path, fn part -> %{"Ident" => [part, 0]} end))
      )

  defp region(index), do: %{"Var" => %{"Free" => index}}
  defp adt(id), do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => arguments([])}}

  # Aeneas already reserves the standard expect pattern. Alias only the opaque
  # declaration admitted above, after auditing the original compiler document.
  # Calls retain their definition IDs, signatures, arguments and source spans;
  # reports retain the original Rust name. No first-party body is replaced.
  def lower_native_names!(document, models) do
    selected =
      Map.filter(models, fn {_, model} ->
        model[:native_expect_ok] == true or model[:native_expect_some] == true or
          model[:encoder_unwrap_ok] == true or model[:rustler_result_conversion] != nil
      end)

    {functions, found} =
      Enum.map_reduce(document["translated"]["fun_decls"], [], fn function, found ->
        case function && selected[function["def_id"]] do
          nil ->
            {function, found}

          model ->
            unless function["body"] == "Opaque" and function["src"] == "Normal" and
                     function["item_meta"]["name"] == model.function["item_meta"]["name"],
                   do:
                     raise(
                       ArgumentError,
                       "native expect alias requires its original audited opaque declaration"
                     )

            parts = String.split(model.backend_rust_name, "::")

            collision =
              Enum.any?(document["translated"]["fun_decls"], fn other ->
                other && other["def_id"] != function["def_id"] &&
                  Enum.map(other["item_meta"]["name"], fn
                    %{"Ident" => [name, _]} -> name
                    _ -> :complex
                  end) == parts
              end)

            if collision,
              do: raise(ArgumentError, "native expect alias collides with another declaration")

            name = Enum.map(parts, &%{"Ident" => [&1, 0]})
            {put_in(function, ["item_meta", "name"], name), [function["def_id"] | found]}
        end
      end)

    unless Enum.sort(found) == Enum.sort(Map.keys(selected)),
      do: raise(ArgumentError, "missing audited native expect declaration")

    {put_in(document, ["translated", "fun_decls"], functions), Enum.sort(found)}
  end

  def audit(functions, models, translated, refs) do
    context = %{
      models: models,
      translated: translated,
      refs: refs,
      traits: trait_references(translated, %{}),
      functions: Map.new(functions, &{&1["def_id"], &1})
    }

    Enum.reduce_while(functions, {:ok, %{}}, fn function, {:ok, dependencies} ->
      try do
        ids = callbacks(function["body"], context) |> Enum.uniq() |> Enum.sort()
        {:cont, {:ok, Map.put(dependencies, function["def_id"], ids)}}
      rescue
        error in ArgumentError -> {:halt, {:error, function, Exception.message(error)}}
      end
    end)
  end

  defp callbacks(
         %{
           "Call" => %{
             "call" => %{
               "func" => %{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => args}}
             }
           }
         } = node,
         context
       ) do
    direct =
      case context.models[id] do
        %{callback: :capture_free} = model -> [callback!(args, model, context)]
        _ -> []
      end

    direct ++ Enum.flat_map(Map.values(node), &callbacks(&1, context))
  end

  defp callbacks(node, context) when is_map(node),
    do: Enum.flat_map(Map.values(node), &callbacks(&1, context))

  defp callbacks(nodes, context) when is_list(nodes),
    do: Enum.flat_map(nodes, &callbacks(&1, context))

  defp callbacks(_, _), do: []

  defp callback!(args, model, ctx) do
    expand = &CallModels.expand(&1, ctx.refs)

    args = callback_arguments(args, model)

    with %{
           "regions" => [],
           "const_generics" => [],
           "types" => [_, error, output, closure],
           "trait_refs" => [fn_ref, drop_ref]
         } <- args,
         %{"Adt" => %{"id" => type_id, "builtin" => nil, "generics" => type_args}} = closure_type <-
           expand.(closure),
         %{
           "kind" => %{"Struct" => []},
           "generics" => params,
           "item_meta" => %{"opacity" => "Transparent"},
           "src" => %{"Closure" => %{"info" => info}}
         } <- declaration(ctx.translated["type_decls"], type_id),
         true <- lifetime_parameters?(params, type_args),
         identity = identity_arguments(params),
         instantiate = &CallModels.instantiate(expand.(&1), type_args),
         %{
           "kind" => "FnOnce",
           "closure_body" => %{"id" => body_id, "generics" => body_args},
           "fn_once_impl" => %{
             "regions" => [],
             "outlives" => [],
             "skip_binder" => %{"id" => impl_id, "generics" => impl_args}
           }
         } <- info,
         true <- body_args == identity and impl_args == identity,
         %{
           "kind" => %{"TraitImpl" => %{"id" => ^impl_id, "generics" => ref_args}},
           "trait_decl_ref" => fn_decl
         } <- reference(fn_ref, ctx.traits),
         true <- ref_args == type_args,
         true <- fn_decl["id"] == model.fn_once_trait,
         [dict_closure, dict_tuple, dict_output] <- expand.(fn_decl["generics"])["types"],
         true <- dict_closure == closure_type and dict_output == expand.(output),
         true <- tuple?(dict_tuple, [expand.(error)]),
         %{
           "kind" => %{
             "BuiltinOrAuto" => %{
               "builtin_data" => "NoopDestruct",
               "parent_trait_refs" => [],
               "types" => [],
               "vtable" => nil
             }
           },
           "trait_decl_ref" => drop_decl
         } <- reference(drop_ref, ctx.traits),
         true <- drop_decl["id"] == model.destruct_trait,
         true <- expand.(drop_decl["generics"]) == arguments([closure_type]),
         %{
           "signature" => %{
             "is_unsafe" => false,
             "abi" => %{"Other" => "rust-call"},
             "is_variadic" => false,
             "inputs" => inputs,
             "output" => result
           },
           "src" => %{
             "TraitImpl" => %{
               "impl_ref" => %{"id" => ^impl_id, "generics" => body_impl_args},
               "trait_ref" => trait_ref,
               "item_id" => 0,
               "reuses_default" => false
             }
           }
         } <- ctx.functions[body_id],
         true <- callback_body_parameters?(get_in(ctx.functions, [body_id, "generics"]), identity),
         true <- body_impl_args == identity,
         true <- Enum.map(inputs, instantiate) == [closure_type, dict_tuple],
         true <- instantiate.(result) == expand.(output),
         true <- trait_ref["id"] == model.fn_once_trait,
         true <-
           instantiate.(trait_ref["generics"]) ==
             arguments([closure_type, dict_tuple, expand.(output)]),
         %{
           "src" => %{"Closure" => %{"kind" => "FnOnce"}},
           "is_negative" => false,
           "is_unsafe" => false,
           "generics" => impl_params,
           "impl_trait" => impl_trait,
           "methods" => [method]
         } <- declaration(ctx.translated["trait_impls"], impl_id),
         true <- callback_body_parameters?(impl_params, identity),
         true <-
           impl_params["outlives"] == get_in(ctx.functions, [body_id, "generics", "outlives"]),
         true <- impl_trait["id"] == model.fn_once_trait,
         true <-
           instantiate.(impl_trait["generics"]) ==
             arguments([closure_type, dict_tuple, expand.(output)]),
         %{
           "params" => method_params,
           "skip_binder" => %{"id" => ^body_id, "generics" => method_args},
           "kind" => %{"TraitMethod" => [trait_id, 0]}
         } <- method,
         true <-
           trait_id == model.fn_once_trait and parameters?(method_params, 0) and
             method_args == identity do
      body_id
    else
      _ ->
        raise ArgumentError,
              "Rust combinator requires an extracted capture-free compiler FnOnce callback with matching signature, implementation identity and NoopDestruct"
    end
  end

  defp callback_arguments(
         %{"types" => [input, output, closure]} = args,
         %{option_callback_type: id}
       ) do
    result = %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => arguments([output])}}
    %{args | "types" => [input, input, result, closure]}
  end

  defp callback_arguments(args, _), do: args

  # Compiler-generated borrowed callback arguments can carry region-to-region
  # outlives bounds. They add no executable behavior; retain all body/signature
  # identity checks and accept only references to this binder's own lifetimes.
  defp callback_body_parameters?(%{"outlives" => outlives} = params, args) do
    lifetime_parameters?(%{params | "outlives" => []}, args) and
      Enum.all?(outlives, fn
        %{
          "regions" => [],
          "outlives" => [],
          "skip_binder" => [
            %{"Var" => %{"Free" => left}},
            %{"Var" => %{"Free" => right}}
          ]
        } ->
          Enum.all?(
            [left, right],
            &(is_integer(&1) and &1 >= 0 and &1 < length(params["regions"]))
          )

        _ ->
          false
      end)
  end

  defp callback_body_parameters?(_, _), do: false

  defp lifetime_parameters?(params, args) when is_map(params) do
    regions = params["regions"]

    is_list(regions) and parameters?(%{params | "regions" => []}, 0) and
      Enum.all?(Enum.with_index(regions), fn {region, i} -> region["index"] == i end) and
      match?(%{"types" => [], "const_generics" => [], "trait_refs" => []}, args) and
      is_list(args["regions"]) and length(args["regions"]) == length(regions)
  end

  defp lifetime_parameters?(_, _), do: false

  defp identity_arguments(params),
    do: %{
      "regions" => Enum.map(params["regions"], fn r -> %{"Var" => %{"Free" => r["index"]}} end),
      "types" => [],
      "const_generics" => [],
      "trait_refs" => []
    }

  defp reference(%{"regions" => [], "outlives" => [], "skip_binder" => value}, refs) do
    case value do
      %{"Value" => [_, value]} -> value
      %{"Deduplicated" => id} -> Map.get(refs, id)
      _ -> nil
    end
  end

  defp reference(_, _), do: nil

  # Trait-reference and type hash-cons IDs occupy different namespaces.
  defp trait_references(%{"Value" => [id, %{"kind" => _, "trait_decl_ref" => _} = ref]}, refs) do
    if Map.has_key?(refs, id) and refs[id] != ref,
      do: raise(ArgumentError, "inconsistent LLBC shared trait identity")

    trait_references(ref, Map.put(refs, id, ref))
  end

  defp trait_references(value, refs) when is_map(value),
    do: Enum.reduce(Map.values(value), refs, &trait_references/2)

  defp trait_references(values, refs) when is_list(values),
    do: Enum.reduce(values, refs, &trait_references/2)

  defp trait_references(_, refs), do: refs

  defp clause(
         %{
           "clause_id" => index,
           "trait_" => %{
             "regions" => [],
             "outlives" => [],
             "skip_binder" => %{"id" => id, "generics" => args}
           }
         },
         refs
       ) do
    case CallModels.expand(args, refs) do
      %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []} ->
        {index, id, types}

      _ ->
        nil
    end
  end

  defp clause(_, _), do: nil

  defp trait?(translated, id, path, count) do
    case declaration(translated["trait_decls"], id) do
      %{"item_meta" => %{"name" => name}, "generics" => params} ->
        name == Enum.map(path, &%{"Ident" => [&1, 0]}) and parameters?(params, count)

      _ ->
        false
    end
  end

  defp parameters?(
         %{
           "regions" => [],
           "types" => types,
           "const_generics" => [],
           "trait_clauses" => [],
           "outlives" => [],
           "trait_type_constraints" => []
         },
         count
       ) do
    expected = if count == 0, do: [], else: Enum.to_list(0..(count - 1))
    Enum.map(types, & &1["index"]) == expected
  end

  defp parameters?(_, _), do: false

  defp tuple?(%{"Adt" => %{"builtin" => "Tuple", "generics" => args}}, types),
    do: args == arguments(types)

  defp tuple?(_, _), do: false
  defp variable(index), do: %{"TypeVar" => %{"Free" => index}}

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp declaration(values, id), do: Enum.find(values || [], &(&1 && &1["def_id"] == id))
  defp free_parent(%{"Bound" => [0, index]}), do: %{"Free" => index}

  defp free_parent(value) when is_map(value),
    do: Map.new(value, fn {k, v} -> {k, free_parent(v)} end)

  defp free_parent(value) when is_list(value), do: Enum.map(value, &free_parent/1)
  defp free_parent(value), do: value
end
