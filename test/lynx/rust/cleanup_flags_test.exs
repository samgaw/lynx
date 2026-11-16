defmodule Lynx.Rust.CleanupFlagsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.CleanupFlags

  test "removes only the unreachable cleanup selected by a known false flag" do
    {document, records} = lower([assign(false), call()])

    assert Enum.any?(
             records,
             &match?(%{kind: :constant_cleanup_branch, value: false, selected_branch: 1}, &1)
           )

    assert Enum.any?(records, &(&1.kind == :terminal_cleanup_tail))
    assert [%{"kind" => "UnwindResume"}] = cleanup(document)
  end

  test "preserves a live owner's drop on a known true branch" do
    {document, [_]} = lower([assign(true), call()])
    assert [%{"kind" => %{"Drop" => %{}}}, %{"kind" => "UnwindResume"}] = cleanup(document)
  end

  test "does not infer flags from inputs, unknown assignments or borrowed locals" do
    borrowed = %{"kind" => %{"Assign" => [place(2), %{"Ref" => %{"place" => place(1)}}]}}
    raw = %{"kind" => %{"Assign" => [place(2), %{"RawPtr" => %{"place" => place(1)}}]}}
    unknown = %{"kind" => %{"Assign" => [place(1), %{"BinaryOp" => []}]}}

    for statements <- [
          [call()],
          [assign(false), unknown, call()],
          [assign(false), borrowed, call()],
          [assign(false), raw, call()]
        ] do
      {document, []} = lower(statements)

      assert [
               %{"kind" => %{"Switch" => _}},
               %{"kind" => %{"Drop" => %{}}},
               %{"kind" => "UnwindResume"}
             ] = cleanup(document)
    end
  end

  test "keeps facts out of branch joins and unknown control flow" do
    switch = %{
      "kind" => %{
        "Switch" => %{
          "data" => %{
            "scrutinee" => %{"Value" => %{"Copy" => place(2)}},
            "branches" => [],
            "fallback" => 0
          },
          "branches" => [%{"statements" => [assign(false)]}, %{"statements" => [assign(true)]}]
        }
      }
    }

    for statements <- [[switch, call()], [assign(false), %{"kind" => %{"Loop" => %{}}}, call()]] do
      {document, []} = lower(statements)
      assert [%{"kind" => %{"Switch" => _}} | _] = cleanup(document)
    end
  end

  test "a call destination invalidates the old value and branch labels must be known" do
    overwrite = put_in(call(), ["kind", "Call", "dest"], place(1))
    {document, records} = lower([assign(false), overwrite, call()])
    assert records != []
    assert [%{"kind" => %{"Switch" => _}} | _] = cleanup(document)

    altered =
      put_in(
        call(),
        [
          "kind",
          "Call",
          "on_unwind",
          "statements",
          Access.at(0),
          "kind",
          "Switch",
          "data",
          "branches"
        ],
        [[%{"Deduplicated" => 999}, 0]]
      )

    {document, []} = lower([assign(false), altered])
    assert [%{"kind" => %{"Switch" => _}} | _] = cleanup(document)
  end

  test "panic cleanup uses only known unborrowed flags and forgets call destinations" do
    panic = %{
      "kind" => %{"Panic" => %{"on_unwind" => get_in(call(), ["kind", "Call", "on_unwind"])}}
    }

    for value <- [false, true] do
      {document, records} = lower([assign(value), panic])
      assert Enum.any?(records, &match?(%{kind: :constant_cleanup_branch, value: ^value}, &1))

      statements =
        get_in(
          hd(document["translated"]["fun_decls"]),
          ["body", "Structured", "body", "statements"]
        )

      cleanup = get_in(List.last(statements), ["kind", "Panic", "on_unwind", "statements"])

      if value do
        assert [%{"kind" => %{"Drop" => %{}}}, %{"kind" => "UnwindResume"}] = cleanup
      else
        assert [%{"kind" => "UnwindResume"}] = cleanup
      end
    end

    overwrite = put_in(call(), ["kind", "Call", "dest"], place(1))
    {document, _} = lower([assign(false), overwrite, panic])

    statements =
      get_in(
        hd(document["translated"]["fun_decls"]),
        ["body", "Structured", "body", "statements"]
      )

    assert [%{"kind" => %{"Switch" => _}} | _] =
             get_in(List.last(statements), ["kind", "Panic", "on_unwind", "statements"])
  end

  test "a shared enum discriminant selects only its matching unwind cleanup" do
    {document, records} = lower_enum([])
    assert Enum.any?(records, &match?(%{kind: :known_variant_cleanup_branch, variant: 1}, &1))
    assert [%{"kind" => "UnwindResume"}] = enum_cleanup(document)
  end

  test "enum cleanup facts expire after moves, overwrites and loop backedges" do
    move = %{
      "kind" => %{"Assign" => [enum_place(2), %{"Use" => [%{"Move" => enum_place(1)}, "Yes"]}]}
    }

    overwrite = %{
      "kind" => %{"Assign" => [enum_place(1), %{"Use" => [%{"Copy" => enum_place(2)}, "Yes"]}]}
    }

    loop = %{"kind" => %{"Loop" => %{"statements" => []}}}

    for prefix <- [[move], [overwrite], [loop]] do
      {document, records} = lower_enum(prefix)
      refute Enum.any?(records, &(&1.kind == :known_variant_cleanup_branch))
      assert [%{"kind" => %{"Switch" => _}}] = enum_cleanup(document)
    end
  end

  test "mutable references and raw pointers prevent enum tag inference" do
    for kind <- ["Mut", "RawPtr"] do
      borrow =
        if kind == "RawPtr",
          do: %{"RawPtr" => %{"place" => enum_place(1)}},
          else: %{"Ref" => %{"place" => enum_place(1), "kind" => kind}}

      {document, records} = lower_enum([%{"kind" => %{"Assign" => [place(3), borrow]}}])
      refute Enum.any?(records, &(&1.kind == :known_variant_cleanup_branch))
      assert [%{"kind" => %{"Switch" => _}}] = enum_cleanup(document)
    end
  end

  defp enum_type,
    do: %{
      "Adt" => %{"id" => 0, "builtin" => nil, "generics" => Lynx.Rust.ResourceModels.args([])}
    }

  defp enum_place(index), do: %{"kind" => %{"Local" => index}, "ty" => enum_type()}

  defp enum_switch(branches) do
    %{
      "id" => 20,
      "kind" => %{
        "Switch" => %{
          "data" => %{
            "scrutinee" => %{"Discriminant" => enum_place(1)},
            "branches" => [
              [
                %{
                  "Value" => [
                    50,
                    [%{"Discriminant" => [enum_type()["Adt"], 0]}, %{"Scalar" => "Usize"}]
                  ]
                },
                0
              ]
            ],
            "fallback" => 1
          },
          "branches" => Enum.map(branches, &%{"statements" => &1})
        }
      }
    }
  end

  defp lower_enum(prefix) do
    # The live Err arm borrows the value immutably before a potentially panicking call.
    shared = %{
      "kind" => %{
        "Assign" => [place(3), %{"Ref" => %{"place" => enum_place(1), "kind" => "Shared"}}]
      }
    }

    unwind = enum_switch([[%{"kind" => %{"Drop" => %{}}}], [%{"kind" => "UnwindResume"}]])
    call = put_in(call(), ["kind", "Call", "on_unwind"], %{"statements" => [unwind]})
    outer = enum_switch([[%{"kind" => "Return"}], [shared] ++ prefix ++ [call]])
    document = document([outer])

    document =
      put_in(document, ["translated", "type_decls"], [
        %{"def_id" => 0, "kind" => %{"Enum" => [%{"id" => 0}, %{"id" => 1}]}}
      ])

    document =
      update_in(
        document,
        ["translated", "fun_decls", Access.at(0), "body", "Structured", "locals", "locals"],
        fn locals ->
          Enum.map(locals, fn local ->
            if local["index"] in [1, 2], do: Map.put(local, "ty", enum_type()), else: local
          end)
        end
      )

    CleanupFlags.lower!(document, ["facade"])
  end

  defp enum_cleanup(document) do
    document["translated"]["fun_decls"]
    |> hd()
    |> get_in([
      "body",
      "Structured",
      "body",
      "statements",
      Access.at(0),
      "kind",
      "Switch",
      "branches",
      Access.at(1),
      "statements"
    ])
    |> List.last()
    |> get_in(["kind", "Call", "on_unwind", "statements"])
  end

  defp place(index), do: %{"kind" => %{"Local" => index}, "ty" => %{"Scalar" => "Bool"}}

  defp literal(value),
    do: %{"Value" => [if(value, do: 10, else: 11), [%{"Bool" => value}, %{"Scalar" => "Bool"}]]}

  defp assign(value),
    do: %{"kind" => %{"Assign" => [place(1), %{"Use" => [%{"Const" => literal(value)}, "Yes"]}]}}

  defp call do
    %{
      "kind" => %{
        "Call" => %{
          "call" => %{"args" => []},
          "dest" => place(3),
          "on_unwind" => %{
            "statements" => [
              %{
                "id" => 5,
                "kind" => %{
                  "Switch" => %{
                    "data" => %{
                      "scrutinee" => %{"Value" => %{"Copy" => place(1)}},
                      "branches" => [[literal(true), 0]],
                      "fallback" => 1
                    },
                    "branches" => [
                      %{"statements" => []},
                      %{"statements" => [%{"kind" => "UnwindResume"}]}
                    ]
                  }
                }
              },
              %{"kind" => %{"Drop" => %{}}},
              %{"kind" => "UnwindResume"}
            ]
          }
        }
      }
    }
  end

  defp lower(statements), do: CleanupFlags.lower!(document(statements), ["facade"])

  defp document(statements) do
    %{
      "translated" => %{
        "fun_decls" => [
          %{
            "def_id" => 0,
            "item_meta" => %{"name" => [%{"Ident" => ["facade", 0]}]},
            "body" => %{
              "Structured" => %{
                "locals" => %{
                  "locals" => Enum.map(1..3, &%{"index" => &1, "ty" => %{"Scalar" => "Bool"}})
                },
                "body" => %{"statements" => statements}
              }
            }
          }
        ]
      }
    }
  end

  defp cleanup(document) do
    document["translated"]["fun_decls"]
    |> hd()
    |> get_in(["body", "Structured", "body", "statements"])
    |> List.last()
    |> get_in(["kind", "Call", "on_unwind", "statements"])
  end
end
