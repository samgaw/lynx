defmodule Lynx.Rust.NativeLifetimesTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.NativeLifetimes

  test "loop exits retain transferred owners and backedges cannot retain them" do
    for {body, tail, accepted} <- [
          {[create(0), edge("Break", 0)], [returned()], true},
          {[create(1), dispose(1), edge("Continue", 0)], [], true},
          {[create(0), edge("Continue", 0)], [returned()], false},
          {[create(1), edge("Continue", 0)], [returned()], false},
          {[create(1), edge("Break", 0)], [returned()], false},
          {[create(0), edge("Break", 0)], [panic()], false},
          {[loop([create(0), edge("Break", 1)])], [returned()], true},
          {[loop([create(1), edge("Break", 1)])], [dispose(1), returned()], true},
          {[loop([edge("Continue", 1)])], [], true},
          {[loop([create(1), edge("Continue", 1)])], [returned()], false},
          {[edge("Break", 1)], [returned()], false}
        ] do
      audit([loop(body) | tail], accepted)
    end
  end

  test "an owner already live at a loop header is not silently treated as an invariant" do
    error = audit([create(1), loop([edge("Break", 0)]), dispose(1), returned()], false)
    assert error.description =~ "loop header or backedge"
  end

  test "a boolean known before the loop cannot hide an unsafe later iteration" do
    initial = %{
      "kind" => %{
        "Assign" => [
          place(3),
          %{"Use" => [%{"Const" => %{"Value" => [nil, [%{"Bool" => false}, nil]]}}, nil]}
        ]
      }
    }

    branch = %{
      "kind" => %{
        "Switch" => %{
          "data" => %{
            "scrutinee" => %{"Value" => %{"Copy" => place(3)}},
            "branches" => [[%{"Value" => [nil, [%{"Bool" => false}, nil]]}, 0]],
            "fallback" => 1
          },
          "branches" => [
            %{"statements" => [edge("Break", 0)]},
            %{"statements" => [create(1), edge("Continue", 0)]}
          ]
        }
      }
    }

    ordinary =
      put_in(branch, ["kind", "Switch", "branches"], [
        %{"statements" => [returned()]},
        %{"statements" => [create(1), returned()]}
      ])

    audit([initial, ordinary], true)
    audit([initial, loop([branch]), returned()], false)
  end

  test "pure drop erasure needs its structural audit and never erases a native owner" do
    drop = fn local ->
      %{
        "kind" => %{
          "Drop" => %{
            "kind" => "Precise",
            "fn_ptr" => %{"kind" => %{"Fun" => 102}},
            "place" => place(local)
          }
        }
      }
    end

    audit([create(0), drop.(3), returned()], false)
    audit([create(0), drop.(3), returned()], true, %{sites: %{1 => [102]}})
    audit([create(0), drop.(0), returned()], false, %{sites: %{1 => [102]}})
  end

  defp args(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp owner, do: %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => args([scalar()])}}
  defp scalar, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}

  defp place(local),
    do: %{"kind" => %{"Local" => local}, "ty" => if(local == 3, do: scalar(), else: owner())}

  defp returned, do: %{"kind" => "Return"}
  defp panic, do: %{"kind" => %{"Panic" => %{"on_unwind" => %{"statements" => []}}}}
  defp edge(kind, target), do: %{"kind" => %{kind => target}}
  defp loop(statements), do: %{"kind" => %{"Loop" => %{"statements" => statements}}}
  defp create(local), do: call(100, [], local)
  defp dispose(local), do: call(101, [%{"Move" => place(local)}], 3)

  defp call(id, arguments, local) do
    %{
      "kind" => %{
        "Call" => %{
          "call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => id}}}, "args" => arguments},
          "dest" => place(local)
        }
      }
    }
  end

  defp audit(statements, accepted, drops \\ nil) do
    params =
      Map.merge(args([%{"index" => 0}]), %{
        "trait_clauses" => [],
        "trait_type_constraints" => [],
        "outlives" => []
      })

    type = %{
      "def_id" => 1,
      "kind" => "Opaque",
      "generics" => params,
      "item_meta" => %{
        "name" => Enum.map(~w(std sync poison mutex Mutex), &%{"Ident" => [&1, 0]})
      }
    }

    function = %{
      "def_id" => 1,
      "item_meta" => %{"name" => [%{"Ident" => ["owner_loop", 0]}]},
      "signature" => %{"inputs" => []},
      "body" => %{
        "Structured" => %{
          "locals" => %{
            "arg_count" => 0,
            "locals" => for(i <- 0..3, do: %{"index" => i, "ty" => place(i)["ty"]})
          },
          "body" => %{"statements" => statements}
        }
      }
    }

    translated = %{"files" => [], "type_decls" => [type], "fun_decls" => [function]}

    run = fn ->
      NativeLifetimes.audit!(
        [function],
        %{100 => %{can_fail: false}, 101 => %{can_fail: false, native_dispose: true}},
        translated,
        %{},
        drops
      )
    end

    if accepted, do: run.(), else: assert_raise(CompileError, ~r/native owner lifetime/, run)
  end
end
