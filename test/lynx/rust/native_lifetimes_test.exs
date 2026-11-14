defmodule Lynx.Rust.NativeLifetimesTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.NativeLifetimes

  test "primitive comparisons preserve live owners without admitting arithmetic panics" do
    for op <- ~w(BitAnd BitOr BitXor Eq Ne Lt Le Gt Ge Add Sub Mul Div Rem Shl Shr) do
      operation = %{
        "kind" => %{
          "Assign" => [
            place(3),
            %{"BinaryOp" => [op, %{"Copy" => place(3)}, %{"Copy" => place(3)}]}
          ]
        }
      }

      audit(
        [create(1), operation, dispose(1), create(0), returned()],
        op in ~w(BitAnd BitOr BitXor Eq Ne Lt Le Gt Ge)
      )

      audit([create(1), operation, create(0), returned()], false)
    end
  end

  test "primitive negation preserves the obligation to consume a live owner" do
    operation = %{
      "kind" => %{"Assign" => [place(3), %{"UnaryOp" => ["Not", %{"Copy" => place(3)}]}]}
    }

    audit([create(1), operation, dispose(1), create(0), returned()], true)
    audit([create(1), operation, create(0), returned()], false)
  end

  test "typed integer casts retain live-owner disposal obligations" do
    for source <- [scalar()],
        target <- [%{"Unsigned" => "U8"}, %{"Unsigned" => "Usize"}, %{"Signed" => "I32"}] do
      operation = %{
        "kind" => %{
          "Assign" => [
            %{"kind" => %{"Local" => 4}, "ty" => %{"Scalar" => %{"Integer" => target}}},
            %{
              "UnaryOp" => [
                %{"Cast" => %{"Scalar" => %{"Integer" => target}}},
                %{"Copy" => %{place(3) | "ty" => source}}
              ]
            }
          ]
        }
      }

      audit([create(1), operation, dispose(1), create(0), returned()], true, nil, %{}, %{
        4 => %{"Scalar" => %{"Integer" => target}}
      })

      audit([create(1), operation, create(0), returned()], false, nil, %{}, %{
        4 => %{"Scalar" => %{"Integer" => target}}
      })
    end
  end

  test "integer cast admission excludes native owners and noninteger casts" do
    for {source, target} <- [
          {owner(), %{"Integer" => %{"Unsigned" => "U64"}}},
          {scalar(), %{"Float" => "F64"}},
          {%{"Scalar" => "Bool"}, %{"Integer" => %{"Unsigned" => "U32"}}},
          {scalar(), %{"Integer" => %{"Unsigned" => "Unknown"}}}
        ] do
      operation = %{
        "kind" => %{
          "Assign" => [
            place(3),
            %{
              "UnaryOp" => [
                %{"Cast" => %{"Scalar" => target}},
                %{"Copy" => %{place(3) | "ty" => source}}
              ]
            }
          ]
        }
      }

      audit([create(1), operation, dispose(1), create(0), returned()], false)
    end
  end

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

  test "nonpanicking transfers retain unrelated owners and track the returned owner" do
    transferred = call(102, [%{"Move" => place(1)}], 1)
    complete = [create(1), create(2), transferred, dispose(1), dispose(2), create(0), returned()]
    model = %{can_fail: false, native_transfer: true}
    audit(complete, true, nil, %{102 => model})
    audit(complete, false, nil, %{102 => %{model | can_fail: true}})
    audit(complete, false, nil, %{102 => Map.delete(model, :native_transfer)})

    audit(
      [create(1), create(2), transferred, dispose(2), create(0), returned()],
      false,
      nil,
      %{102 => model}
    )
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

  test "moving one saved field retains every other frame owner's obligation" do
    frame_audit([frame_dispose(1), frame_dispose(2), returned()], true)
    frame_audit([frame_dispose(1), returned()], false)
    frame_audit([frame_dispose(2), returned()], false)
    frame_audit([frame_dispose(1), panic()], false)
  end

  test "saved fields cannot be consumed twice or resurrected by another state test" do
    frame_audit([frame_dispose(1), frame_dispose(1), frame_dispose(2), returned()], false)

    frame_audit(
      [frame_dispose(1), frame_switch([frame_dispose(1), frame_dispose(2), returned()])],
      false
    )
  end

  test "borrowed multi-owner frames retain obligations at joins and loop backedges" do
    branch = %{
      "kind" => %{
        "Switch" => %{
          "data" => %{
            "scrutinee" => %{
              "Value" => %{"Copy" => %{"kind" => %{"Local" => 2}, "ty" => %{"Scalar" => "Bool"}}}
            },
            "branches" => [[%{"Value" => [300, [%{"Bool" => true}, nil]]}, 0]],
            "fallback" => 1
          },
          "branches" => [%{"statements" => [frame_dispose(1)]}, %{"statements" => []}]
        }
      }
    }

    frame_audit([branch, returned()], false, true)
    frame_audit([loop([frame_dispose(1), edge("Continue", 0)]), returned()], false, true)
    frame_audit([loop([edge("Continue", 0)]), returned()], true, true)
    frame_audit([frame_dispose(1), panic()], false, true)
  end

  defp frame_type, do: %{"Adt" => %{"id" => 2, "builtin" => nil, "generics" => args([])}}
  defp u32, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "U32"}}}

  defp frame_place(field) do
    %{
      "kind" => %{
        "Projection" => [
          %{"kind" => %{"Local" => 1}, "ty" => frame_type()},
          %{"Field" => [nil, field]}
        ]
      },
      "ty" => if(field == 0, do: u32(), else: owner())
    }
  end

  defp frame_dispose(field) do
    %{
      "kind" => %{
        "Call" => %{
          "call" => %{
            "func" => %{"Regular" => %{"kind" => %{"Fun" => 101}}},
            "args" => [%{"Move" => frame_place(field)}]
          },
          "dest" => %{"kind" => %{"Local" => 0}, "ty" => scalar()}
        }
      }
    }
  end

  defp frame_switch(statements) do
    tag = fn n ->
      %{"Value" => [200 + n, [%{"Integer" => %{"Unsigned" => ["U32", to_string(n)]}}, nil]]}
    end

    %{
      "kind" => %{
        "Switch" => %{
          "data" => %{
            "scrutinee" => %{"Value" => %{"Copy" => frame_place(0)}},
            "branches" => [[tag.(3), 0], [tag.(0), 1], [tag.(1), 1], [tag.(2), 1]],
            "fallback" => 2
          },
          "branches" => [
            %{"statements" => statements},
            %{"statements" => [returned()]},
            %{"statements" => [%{"kind" => "UndefinedBehavior"}]}
          ]
        }
      }
    }
  end

  defp frame_audit(statements, accepted, borrowed \\ false) do
    params =
      Map.merge(args([]), %{
        "trait_clauses" => [],
        "trait_type_constraints" => [],
        "outlives" => []
      })

    mutex = %{
      "def_id" => 1,
      "kind" => "Opaque",
      "generics" => %{params | "types" => [%{"index" => 0}]},
      "item_meta" => %{
        "name" => Enum.map(~w(std sync poison mutex Mutex), &%{"Ident" => [&1, 0]})
      }
    }

    frame = %{
      "def_id" => 2,
      "src" => "Normal",
      "generics" => params,
      "kind" => %{"Struct" => [%{"ty" => u32()}, %{"ty" => owner()}, %{"ty" => owner()}]},
      "item_meta" => %{
        "name" => [%{"Ident" => ["owner_frame", 0]}, %{"Builtin" => ["Closure", 0]}],
        "attr_info" => %{
          "attributes" => [
            %{
              "Unknown" => %{
                "path" => "lynx::coroutine_storage_v1",
                "args" => JSON.encode!(%{state: 0, states: [[], [], [], [1, 2]]})
              }
            }
          ]
        }
      }
    }

    input = if borrowed, do: %{"Ref" => ["Erased", frame_type(), "Mut"]}, else: frame_type()

    name =
      if borrowed,
        do: [
          %{"Ident" => ["owner_frame", 0]},
          %{"Builtin" => ["Closure", 0]},
          %{"Ident" => ["poll", 0]}
        ],
        else: [%{"Ident" => ["consume_frame", 0]}]

    function = %{
      "def_id" => 1,
      "item_meta" => %{"name" => name},
      "signature" => %{"inputs" => [input, %{"Scalar" => "Bool"}]},
      "body" => %{
        "Structured" => %{
          "locals" => %{
            "arg_count" => 2,
            "locals" => [
              %{"index" => 0, "ty" => scalar()},
              %{"index" => 1, "ty" => input},
              %{"index" => 2, "ty" => %{"Scalar" => "Bool"}}
            ]
          },
          "body" => %{"statements" => [frame_switch(statements)]}
        }
      }
    }

    function =
      if borrowed do
        update_in(function, ["body", "Structured", "body"], &borrow_frame_places(&1, input))
      else
        function
      end

    translated = %{
      "files" => [],
      "type_decls" => [mutex, frame],
      "fun_decls" => [function],
      "options" => %{"cancelling_futures" => true}
    }

    run = fn ->
      NativeLifetimes.audit!(
        [function],
        %{101 => %{can_fail: false, native_dispose: true}},
        translated,
        %{}
      )
    end

    if accepted, do: run.(), else: assert_raise(CompileError, ~r/native owner lifetime/, run)
  end

  defp borrow_frame_places(%{"kind" => %{"Local" => 1}}, type),
    do: %{
      "kind" => %{"Projection" => [%{"kind" => %{"Local" => 1}, "ty" => type}, "Deref"]},
      "ty" => frame_type()
    }

  defp borrow_frame_places(map, type) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, borrow_frame_places(value, type)} end)

  defp borrow_frame_places(list, type) when is_list(list),
    do: Enum.map(list, &borrow_frame_places(&1, type))

  defp borrow_frame_places(value, _), do: value

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

  defp audit(statements, accepted, drops \\ nil, models \\ %{}, local_types \\ %{}) do
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
            "locals" =>
              for(i <- 0..4, do: %{"index" => i, "ty" => Map.get(local_types, i, place(i)["ty"])})
          },
          "body" => %{"statements" => statements}
        }
      }
    }

    translated = %{"files" => [], "type_decls" => [type], "fun_decls" => [function]}

    run = fn ->
      NativeLifetimes.audit!(
        [function],
        Map.merge(
          %{100 => %{can_fail: false}, 101 => %{can_fail: false, native_dispose: true}},
          models
        ),
        translated,
        %{},
        drops
      )
    end

    if accepted, do: run.(), else: assert_raise(CompileError, ~r/native owner lifetime/, run)
  end
end
