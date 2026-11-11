defmodule Lynx.Rust.LibraryHelpers do
  @moduledoc false

  # Only these narrowly selected helpers are retained from dependency metadata.
  # Inclusion is not a specification or an approval of its behavior: its actual
  # body goes through the same call audit, extraction and kernel checking as a
  # workspace function. Other dependency functions remain outside this scope.
  def includes(context \\ %{}) do
    [
      "thiserror::display",
      "core::hint::must_use",
      "rustler::term::_::decode"
    ] ++ if(context[:sysroot], do: ["core::slice::_::starts_with"], else: [])
  end

  def selected?(
        %{
          "body" => %{"Structured" => _},
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["core", 0]},
              %{"Ident" => ["slice", 0]},
              %{"Impl" => %{"Ty" => _}},
              %{"Ident" => ["starts_with", 0]}
            ]
          }
        } = function,
        translated
      ) do
    Lynx.Rust.ComparisonModels.prefix_helper?(function, translated)
  end

  # Retain the actual SDK forwarding body. Decoder dictionaries are closed by
  # the existing dispatch audit; no replacement implementation is supplied.
  def selected?(
        %{
          "src" => "Normal",
          "body" => %{"Structured" => _},
          "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"},
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["rustler", 0]},
              %{"Ident" => ["term", 0]},
              %{"Impl" => %{"Ty" => %{"kind" => "InherentImplBlock", "skip_binder" => parent}}},
              %{"Ident" => ["decode", 0]}
            ]
          }
        } = function,
        translated
      ) do
    refs = Lynx.Rust.LLBC.type_references!(translated)

    case Lynx.Rust.CallModels.expand(parent, refs) do
      %{"Adt" => %{"id" => id, "builtin" => nil}} ->
        Enum.any?(
          translated["type_decls"],
          &(&1 && &1["def_id"] == id &&
              &1["item_meta"]["name"] ==
                Enum.map(~w(rustler term Term), fn part -> %{"Ident" => [part, 0]} end))
        ) &&
          function["generics"]["const_generics"] == []

      _ ->
        false
    end
  end

  def selected?(
        %{
          "src" => "Normal",
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["core", 0]},
              %{"Ident" => ["hint", 0]},
              %{"Ident" => ["must_use", 0]}
            ]
          }
        },
        _
      ),
      do: true

  def selected?(
        %{
          "def_id" => function_id,
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["thiserror", disambiguator]},
              %{"Ident" => ["display", 0]},
              %{"Impl" => %{"Trait" => impl_id}},
              %{"Ident" => ["as_display", 0]}
            ]
          },
          "src" => %{
            "TraitImpl" => %{
              "impl_ref" => %{"id" => impl_id},
              "trait_ref" => %{"id" => trait_id},
              "item_id" => 0,
              "reuses_default" => false
            }
          }
        },
        translated
      )
      when is_integer(disambiguator) and disambiguator >= 0 do
    case Enum.find(translated["trait_impls"] || [], &(&1 && &1["def_id"] == impl_id)) do
      %{
        "src" => "Normal",
        "is_negative" => false,
        "is_unsafe" => false,
        "impl_trait" => %{"id" => ^trait_id},
        "methods" => [
          %{
            "kind" => %{"TraitMethod" => [^trait_id, 0]},
            "skip_binder" => %{"id" => ^function_id}
          }
        ]
      } ->
        case Enum.find(translated["trait_decls"] || [], &(&1 && &1["def_id"] == trait_id)) do
          %{
            "item_meta" => %{
              "name" => [
                %{"Ident" => ["thiserror", ^disambiguator]},
                %{"Ident" => ["display", 0]},
                %{"Ident" => ["AsDisplay", 0]}
              ]
            }
          } ->
            true

          _ ->
            false
        end

      _ ->
        false
    end
  end

  def selected?(
        %{
          "src" => "Normal",
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["core", 0]},
              %{"Ident" => ["pin", 0]},
              %{"Impl" => %{"Ty" => %{"kind" => "InherentImplBlock"}}},
              %{"Ident" => ["get_mut", 0]}
            ]
          },
          "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
          "generics" => params,
          "body" => %{
            "Structured" => %{
              "locals" => %{"arg_count" => 1, "locals" => [_, _]},
              "body" => %{"statements" => statements}
            }
          }
        },
        translated
      ) do
    refs = Lynx.Rust.LLBC.type_references!(translated)
    variable = %{"TypeVar" => %{"Free" => 0}}
    region = %{"Var" => %{"Free" => 0}}

    args = %{
      "regions" => [region],
      "types" => [variable],
      "const_generics" => [],
      "trait_refs" => []
    }

    with [%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => ^args}}] <-
           Lynx.Rust.CallModels.expand(sig["inputs"], refs),
         %{"Ref" => [^region, ^variable, "Mut"]} <-
           Lynx.Rust.CallModels.expand(sig["output"], refs),
         %{
           "src" => "Normal",
           "item_meta" => %{"name" => name},
           "kind" => %{"Struct" => [%{"name" => "pointer", "ty" => field}]}
         } <-
           Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id)),
         [
           %{"Ident" => ["core", 0]},
           %{"Ident" => ["pin", 0]},
           %{"Ident" => ["Pin", 0]},
           %{"Instantiated" => _}
         ] <- name,
         %{"Ref" => [^region, ^variable, "Mut"]} <- Lynx.Rust.CallModels.expand(field, refs),
         true <- pin_unpin_bound?(params, variable, translated, refs) do
      case Enum.reject(statements, &pin_storage?/1) do
        [
          %{
            "kind" => %{
              "Assign" => [
                %{"kind" => %{"Local" => 0}},
                %{
                  "Use" => [
                    %{
                      "Move" => %{
                        "kind" => %{
                          "Projection" => [
                            %{"kind" => %{"Local" => 1}},
                            %{"Field" => [nil, 0]}
                          ]
                        }
                      }
                    },
                    "No"
                  ]
                }
              ]
            }
          },
          %{"kind" => "Return"}
        ] ->
          true

        _ ->
          false
      end
    else
      _ -> false
    end
  end

  def selected?(
        %{
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["core", 0]},
              %{"Ident" => ["future", 0]},
              %{"Ident" => ["into_future", 0]},
              %{"Impl" => %{"Trait" => impl}},
              %{"Ident" => ["into_future", 0]}
            ]
          },
          "src" => %{"TraitImpl" => %{"impl_ref" => %{"id" => impl}, "reuses_default" => false}},
          "signature" =>
            %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = signature,
          "body" => %{
            "Structured" => %{
              "locals" => %{"arg_count" => 1, "locals" => [_, _]},
              "body" => %{"statements" => statements}
            }
          }
        },
        translated
      ) do
    refs = Lynx.Rust.LLBC.type_references!(translated)
    input = %{"TypeVar" => %{"Free" => 0}}

    Lynx.Rust.CallModels.expand(signature["inputs"], refs) == [input] and
      Lynx.Rust.CallModels.expand(signature["output"], refs) == input and
      match?(
        [
          %{
            "kind" => %{
              "Assign" => [
                %{"kind" => %{"Local" => 0}},
                %{"Use" => [%{"Move" => %{"kind" => %{"Local" => 1}}}, retag]}
              ]
            }
          },
          %{"kind" => "Return"}
        ]
        when retag in ["No", "Yes"],
        Enum.reject(statements, &pin_storage?/1)
      )
  end

  def selected?(_, _), do: false

  defp pin_storage?(%{"kind" => %{"StorageLive" => id}}) when id in [0, 1], do: true
  defp pin_storage?(%{"kind" => %{"StorageDead" => id}}) when id in [0, 1], do: true
  defp pin_storage?(_), do: false

  defp pin_unpin_bound?(
         %{
           "types" => [_],
           "regions" => [_],
           "const_generics" => [],
           "trait_type_constraints" => [],
           "trait_clauses" => [%{"trait_" => trait}]
         },
         variable,
         translated,
         refs
       ) do
    with %{
           "regions" => [],
           "outlives" => [],
           "skip_binder" => %{
             "id" => id,
             "generics" => %{
               "regions" => [],
               "types" => [^variable],
               "const_generics" => [],
               "trait_refs" => []
             }
           }
         } <- Lynx.Rust.CallModels.expand(trait, refs),
         %{
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["core", 0]},
               %{"Ident" => ["marker", 0]},
               %{"Ident" => ["Unpin", 0]}
             ]
           }
         } <-
           Enum.find(translated["trait_decls"], &(&1 && &1["def_id"] == id)) do
      true
    else
      _ -> false
    end
  end

  defp pin_unpin_bound?(_, _, _, _), do: false
end
