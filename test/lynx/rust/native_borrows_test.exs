defmodule Lynx.Rust.NativeBorrowsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{NativeBorrows, NativeLifetimes}

  test "frame discovery terminates on recursive reference wrappers without native ownership" do
    args = %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}
    cycle = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => args}}
    borrowed = %{"Ref" => ["Static", cycle, "Mut"]}

    type = %{
      "def_id" => 1,
      "src" => "Normal",
      "generics" => Map.merge(args, %{"trait_clauses" => []}),
      "item_meta" => %{
        "name" => [%{"Ident" => ["Cycle", 0]}],
        "attr_info" => %{"attributes" => []}
      },
      "kind" => %{"Struct" => [%{"ty" => borrowed}]}
    }

    function = %{
      "def_id" => 1,
      "item_meta" => %{"name" => [%{"Ident" => ["read_cycle", 0]}]},
      "signature" => %{"inputs" => [borrowed]},
      "body" => %{
        "Structured" => %{
          "locals" => %{"arg_count" => 1, "locals" => [%{"index" => 1, "ty" => borrowed}]},
          "body" => %{"statements" => [%{"kind" => "Return"}]}
        }
      }
    }

    NativeLifetimes.audit!(
      [function],
      %{},
      %{"type_decls" => [type], "fun_decls" => [function]},
      %{}
    )
  end

  test "classifies primitive bitwise and comparison operators without erasing arithmetic failures" do
    for op <- ~w(BitAnd BitOr BitXor Eq Ne Lt Le Gt Ge Add Sub Mul Div Rem Shl Shr) do
      function = %{
        "def_id" => 1,
        "body" => %{
          "Structured" => %{
            "body" => %{
              "statements" => [
                %{
                  "kind" => %{
                    "Assign" => [%{"kind" => %{"Local" => 0}}, %{"BinaryOp" => [op, %{}, %{}]}]
                  }
                },
                %{"kind" => "Return"}
              ]
            }
          }
        }
      }

      result = NativeBorrows.nonpanicking_calls([function], %{})
      assert MapSet.member?(result, 1) == op in ~w(BitAnd BitOr BitXor Eq Ne Lt Le Gt Ge)
    end
  end

  test "primitive not is nonpanicking but negation is not assumed safe" do
    for op <- ["Not", "Neg"] do
      function = %{
        "def_id" => 1,
        "body" => %{
          "Structured" => %{
            "body" => %{
              "statements" => [
                %{"kind" => %{"Assign" => [%{}, %{"UnaryOp" => [op, %{}]}]}},
                %{"kind" => "Return"}
              ]
            }
          }
        }
      }

      assert MapSet.member?(NativeBorrows.nonpanicking_calls([function], %{}), 1) == (op == "Not")
    end
  end

  test "integer casts are nonpanicking without admitting pointer or floating casts" do
    integer = fn sign, width -> %{"Scalar" => %{"Integer" => %{sign => width}}} end
    u64 = integer.("Unsigned", "U64")

    for {source, target, expected} <- [
          {integer.("Unsigned", "Usize"), u64, true},
          {integer.("Signed", "I128"), integer.("Unsigned", "U8"), true},
          {integer.("Unsigned", "U64"), integer.("Signed", "I8"), true},
          {%{"Scalar" => "Bool"}, u64, false},
          {%{"Scalar" => %{"Float" => "F64"}}, u64, false},
          {%{"Ref" => ["Static", u64, "Shared"]}, u64, false},
          {%{"Deduplicated" => 91}, u64, false},
          {u64, %{"Scalar" => "Bool"}, false}
        ] do
      %{"Scalar" => target} = target

      function = %{
        "def_id" => 1,
        "body" => %{
          "Structured" => %{
            "body" => %{
              "statements" => [
                %{
                  "kind" => %{
                    "Assign" => [
                      %{},
                      %{
                        "UnaryOp" => [
                          %{"Cast" => %{"Scalar" => target}},
                          %{"Move" => %{"ty" => source}}
                        ]
                      }
                    ]
                  }
                },
                %{"kind" => "Return"}
              ]
            }
          }
        }
      }

      assert MapSet.member?(NativeBorrows.nonpanicking_calls([function], %{}), 1) == expected
    end
  end

  test "checks loop safety without assuming termination or accepting invalid exits" do
    statement = &%{"kind" => &1}
    loop = fn kinds -> %{"Loop" => %{"statements" => Enum.map(kinds, statement)}} end
    panic = %{"Panic" => %{}}
    call = %{"Call" => %{"call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => 2}}}}}}

    function = fn id, kinds ->
      %{
        "def_id" => id,
        "body" => %{"Structured" => %{"body" => %{"statements" => Enum.map(kinds, statement)}}}
      }
    end

    for {kinds, expected} <- [
          {[loop.([%{"Continue" => 0}])], true},
          {[loop.([%{"Break" => 0}]), "Return"], true},
          {[loop.([loop.([%{"Break" => 1}])]), "Return"], true},
          {[loop.([%{"Break" => 1}])], false},
          {[loop.([%{"Continue" => -1}])], false},
          {[%{"Break" => 0}], false},
          {[loop.([panic])], false},
          {[loop.([%{"Continue" => 0}]), panic], false},
          {[loop.([%{"Drop" => %{}}])], false},
          {[loop.([call])], false}
        ] do
      # A callee cannot inherit permission to break out of its caller's loop.
      functions = [function.(1, kinds), function.(2, [%{"Break" => 0}])]
      assert MapSet.member?(NativeBorrows.nonpanicking_calls(functions, %{}), 1) == expected
    end
  end

  test "ignores only unreachable tails after returns on every structured branch" do
    returned = %{"statements" => [%{"kind" => "Return"}]}
    fallthrough = %{"statements" => [%{"kind" => %{"StorageDead" => 0}}]}
    unsafe = %{"kind" => "UndefinedBehavior"}
    branch = fn blocks -> %{"kind" => %{"Switch" => %{"branches" => blocks}}} end

    for {statements, expected} <- [
          {[%{"kind" => "Return"}, unsafe], true},
          {[branch.([returned, returned]), unsafe], true},
          {[branch.([returned, %{"statements" => [branch.([returned, returned])]}]), unsafe],
           true},
          {[branch.([returned, fallthrough]), unsafe], false},
          {[branch.([]), unsafe], false},
          {[unsafe, %{"kind" => "Return"}], false},
          {[%{"kind" => %{"Panic" => %{}}}, %{"kind" => "Return"}], false},
          {[branch.([returned, %{"statements" => [unsafe, %{"kind" => "Return"}]}]), unsafe],
           false}
        ] do
      function = %{
        "def_id" => 1,
        "body" => %{"Structured" => %{"body" => %{"statements" => statements}}}
      }

      assert MapSet.member?(NativeBorrows.nonpanicking_calls([function], %{}), 1) == expected
    end
  end

  test "retains other owners only across a nonpanicking consuming implementation" do
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

    declaration = %{
      "def_id" => 1,
      "kind" => "Opaque",
      "generics" => params,
      "item_meta" => %{
        "name" => Enum.map(~w(std sync poison mutex Mutex), &%{"Ident" => [&1, 0]})
      }
    }

    scalar = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}
    owner = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => args.([scalar])}}
    unit = %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => args.([])}}

    place = fn local ->
      %{"kind" => %{"Local" => local}, "ty" => if(local == 0, do: unit, else: owner)}
    end

    call = fn id, local ->
      %{
        "kind" => %{
          "Call" => %{
            "call" => %{
              "func" => %{"Regular" => %{"kind" => %{"Fun" => id}}},
              "args" => [%{"Move" => place.(local)}]
            },
            "dest" => place.(0)
          }
        }
      }
    end

    function = fn id, count, statements ->
      %{
        "def_id" => id,
        "signature" => %{"inputs" => List.duplicate(owner, count)},
        "item_meta" => %{"name" => [%{"Ident" => ["consume#{id}", 0]}]},
        "body" => %{
          "Structured" => %{
            "locals" => %{
              "arg_count" => count,
              "locals" => for(i <- 0..count, do: %{"index" => i, "ty" => place.(i)["ty"]})
            },
            "body" => %{"statements" => statements}
          }
        }
      }
    end

    caller = function.(1, 2, [call.(2, 1), call.(100, 2), %{"kind" => "Return"}])
    callee = function.(2, 1, [call.(100, 1), %{"kind" => "Return"}])
    translated = %{"files" => [], "type_decls" => [declaration], "fun_decls" => [caller, callee]}
    models = %{100 => %{can_fail: false, native_dispose: true}}
    NativeLifetimes.audit!([caller, callee], models, translated, %{})

    panicking =
      function.(2, 1, [
        call.(100, 1),
        %{"kind" => %{"Panic" => %{"on_unwind" => %{"statements" => []}}}}
      ])

    assert_raise CompileError, ~r/native owner lifetime/, fn ->
      NativeLifetimes.audit!(
        [caller, panicking],
        models,
        Map.put(translated, "fun_decls", [caller, panicking]),
        %{}
      )
    end
  end

  test "implicit destruction becomes nonpanicking only after validated lowering" do
    function = fn id, statements ->
      %{
        "def_id" => id,
        "body" => %{
          "Structured" => %{"body" => %{"statements" => statements ++ [%{"kind" => "Return"}]}}
        }
      }
    end

    call = fn id ->
      %{
        "kind" => %{
          "Call" => %{"call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => id}}}}}
        }
      }
    end

    caller = function.(2, [call.(1)])
    raw = function.(1, [%{"kind" => %{"Drop" => %{}}}])
    refute MapSet.member?(NativeBorrows.nonpanicking_calls([caller, raw], %{}), 2)
    lowered = function.(1, [call.(9)])

    for {model, expected} <- [
          {%{can_fail: true, native_cutoff_only: true}, true},
          {%{can_fail: false}, true},
          {%{can_fail: true}, false}
        ] do
      safe = NativeBorrows.nonpanicking_calls([caller, lowered], %{9 => model})
      assert MapSet.member?(safe, 2) == expected
    end

    panicking = function.(1, [call.(9), %{"kind" => %{"Panic" => %{}}}])

    refute MapSet.member?(
             NativeBorrows.nonpanicking_calls(
               [caller, panicking],
               %{9 => %{can_fail: true, native_cutoff_only: true}}
             ),
             2
           )

    refute MapSet.member?(NativeBorrows.nonpanicking_calls([caller, lowered], %{}), 2)
  end
end
