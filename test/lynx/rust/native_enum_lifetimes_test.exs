defmodule Lynx.Rust.NativeEnumLifetimesTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.NativeLifetimes

  test "repeated enum tests retain selected tags without resurrecting consumed payloads" do
    args = fn types ->
      %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}
    end

    params = %{
      "regions" => [],
      "types" => [%{"index" => 0}],
      "const_generics" => [],
      "trait_clauses" => [],
      "trait_type_constraints" => [],
      "outlives" => []
    }

    scalar = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}
    mutex = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => args.([scalar])}}
    choice = %{"Adt" => %{"id" => 2, "builtin" => nil, "generics" => args.([])}}
    unit = %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => args.([])}}

    place = fn id ->
      %{
        "kind" => %{"Local" => id},
        "ty" =>
          case id do
            1 -> choice
            2 -> mutex
            _ -> unit
          end
      }
    end

    field = %{"kind" => %{"Projection" => [place.(1), %{"Field" => [1, 0]}]}, "ty" => mutex}
    statement = &%{"kind" => &1}
    block = fn kinds -> %{"statements" => Enum.map(kinds, statement)} end

    label = fn tag ->
      %{
        "Value" => [
          10 + tag,
          [
            %{"Discriminant" => [choice["Adt"], tag]},
            %{"Scalar" => %{"Integer" => %{"Signed" => "Isize"}}}
          ]
        ]
      }
    end

    switch = fn empty, owned ->
      %{
        "Switch" => %{
          "data" => %{
            "scrutinee" => %{"Discriminant" => place.(1)},
            "branches" => [[label.(0), 0], [label.(1), 1]],
            "fallback" => nil
          },
          "branches" => [block.(empty), block.(owned)]
        }
      }
    end

    call = fn id, inputs, dest ->
      %{
        "Call" => %{
          "call" => %{
            "func" => %{"Regular" => %{"kind" => %{"Fun" => id}}},
            "args" => inputs
          },
          "dest" => place.(dest)
        }
      }
    end

    consume = [
      %{"Assign" => [place.(2), %{"Use" => [%{"Move" => field}, mutex]}]},
      call.(100, [%{"Move" => place.(2)}], 0)
    ]

    function = fn kinds ->
      %{
        "def_id" => 1,
        "item_meta" => %{"name" => [%{"Ident" => ["consume_choice", 0]}]},
        "signature" => %{"inputs" => [choice]},
        "body" => %{
          "Structured" => %{
            "locals" => %{
              "arg_count" => 1,
              "locals" => for(id <- 0..2, do: %{"index" => id, "ty" => place.(id)["ty"]})
            },
            "body" => block.(kinds)
          }
        }
      }
    end

    mutex_decl = %{
      "def_id" => 1,
      "generics" => params,
      "kind" => "Opaque",
      "item_meta" => %{
        "name" => Enum.map(~w(std sync poison mutex Mutex), &%{"Ident" => [&1, 0]})
      }
    }

    choice_decl = %{
      "def_id" => 2,
      "generics" => %{params | "types" => []},
      "item_meta" => %{"name" => [%{"Ident" => ["Choice", 0]}]},
      "kind" => %{
        "Enum" => [%{"id" => 0, "fields" => []}, %{"id" => 1, "fields" => [%{"ty" => mutex}]}]
      }
    }

    models = %{100 => %{can_fail: false, native_dispose: true}, 111 => %{can_fail: false}}

    audit = fn f ->
      NativeLifetimes.audit!(
        [f],
        models,
        %{"files" => [], "type_decls" => [mutex_decl, choice_decl], "fun_decls" => [f]},
        %{}
      )
    end

    panic = %{"Panic" => %{"on_unwind" => %{"statements" => []}}}
    audit.(function.([switch.([switch.(["Return"], [panic])], consume ++ ["Return"])]))

    # Replacing a previously empty value must invalidate its selected tag.
    replacement = [
      call.(111, [], 2),
      %{
        "Assign" => [
          place.(1),
          %{"Aggregate" => [%{"Adt" => choice["Adt"]}, [%{"Move" => place.(2)}]]}
        ]
      },
      switch.(["Return"], [panic])
    ]

    assert_raise CompileError, ~r/native owner lifetime/, fn ->
      audit.(function.([switch.(replacement, consume ++ ["Return"])]))
    end

    assert_raise CompileError, ~r/native owner lifetime/, fn ->
      audit.(
        function.([switch.(["Return"], consume ++ [switch.(["Return"], consume ++ ["Return"])])])
      )
    end

    wrapper = %{"Adt" => %{"id" => 3, "builtin" => nil, "generics" => args.([])}}
    wrapper_place = %{"kind" => %{"Local" => 1}, "ty" => wrapper}

    nested = %{
      "kind" => %{"Projection" => [wrapper_place, %{"Field" => [nil, 0]}]},
      "ty" => choice
    }

    replace = fn recurse, value ->
      cond do
        value == place.(1) -> nested
        is_map(value) -> Map.new(value, fn {k, v} -> {k, recurse.(recurse, v)} end)
        is_list(value) -> Enum.map(value, &recurse.(recurse, &1))
        true -> value
      end
    end

    wrapped = fn kinds ->
      f = function.(kinds)
      f = put_in(f, ["signature", "inputs"], [wrapper])
      f = update_in(f, ["body", "Structured", "body"], &replace.(replace, &1))

      update_in(f, ["body", "Structured", "locals", "locals"], fn locals ->
        Enum.map(locals, fn
          %{"index" => 1} = local -> %{local | "ty" => wrapper}
          local -> local
        end)
      end)
    end

    wrapper_decl = %{
      "def_id" => 3,
      "generics" => %{params | "types" => []},
      "item_meta" => %{"name" => [%{"Ident" => ["Wrapper", 0]}]},
      "kind" => %{"Struct" => [%{"ty" => choice}]}
    }

    nested_audit = fn f, declaration ->
      NativeLifetimes.audit!(
        [f],
        models,
        %{
          "files" => [],
          "type_decls" => [mutex_decl, choice_decl, declaration],
          "fun_decls" => [f]
        },
        %{}
      )
    end

    # An empty nested alternative discharges the one possible owner. Its tags
    # must remain distinct from any tags on the enclosing value.
    nested_audit.(
      wrapped.([switch.([switch.(["Return"], [panic])], consume ++ ["Return"])]),
      wrapper_decl
    )

    # Inspecting the tag after moving the payload does not recreate ownership.
    nested_audit.(
      wrapped.([switch.(["Return"], consume ++ [switch.([panic], ["Return"])])]),
      wrapper_decl
    )

    # An empty selected field cannot discharge a different field's owner.
    two_owners = put_in(wrapper_decl, ["kind", "Struct"], [%{"ty" => choice}, %{"ty" => mutex}])

    assert_raise CompileError, ~r/native owner lifetime/, fn ->
      nested_audit.(wrapped.([switch.(["Return"], consume ++ ["Return"])]), two_owners)
    end

    assert_raise CompileError, ~r/native owner lifetime/, fn ->
      nested_audit.(
        wrapped.([switch.(["Return"], consume ++ [switch.(["Return"], consume ++ ["Return"])])]),
        wrapper_decl
      )
    end
  end
end
