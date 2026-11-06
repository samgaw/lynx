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
    overwrite = put_in(call(), ["kind", "Call", "call", "dest"], place(1))
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

  defp place(index), do: %{"kind" => %{"Local" => index}, "ty" => %{"Scalar" => "Bool"}}

  defp literal(value),
    do: %{"Value" => [if(value, do: 10, else: 11), [%{"Bool" => value}, %{"Scalar" => "Bool"}]]}

  defp assign(value),
    do: %{"kind" => %{"Assign" => [place(1), %{"Use" => [%{"Const" => literal(value)}, "Yes"]}]}}

  defp call do
    %{
      "kind" => %{
        "Call" => %{
          "call" => %{"dest" => place(3)},
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

  defp lower(statements) do
    document = %{
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

    CleanupFlags.lower!(document, ["facade"])
  end

  defp cleanup(document) do
    document["translated"]["fun_decls"]
    |> hd()
    |> get_in(["body", "Structured", "body", "statements"])
    |> List.last()
    |> get_in(["kind", "Call", "on_unwind", "statements"])
  end
end
