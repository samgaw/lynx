defmodule Lynx.Rust.BranchingTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.Branching

  test "invalid branch modes fail before native preparation" do
    assert Branching.validate!([]) == :join

    for mode <- [nil, true, :auto, "duplicate"] do
      assert_raise ArgumentError, ~r/branching must be/, fn ->
        Lynx.Rust.verify!("/unused", "unused", roots: ["unused::function"], branching: mode)
      end

      assert_raise ArgumentError, ~r/branching must be/, fn ->
        Lynx.Rustler.prepare!("/unused", "unused", branching: mode)
      end
    end
  end

  @tag :tmp_dir
  test "duplication requires an explicit backend capability", %{tmp_dir: tools} do
    assert Branching.backend_arguments!([], tools) == []
    File.write!(Path.join(tools, "lynx-toolchain"), "profile=runtime\n")

    assert_raise ArgumentError, ~r/requires the branch-duplication backend/, fn ->
      Branching.backend_arguments!([branching: :duplicate], tools)
    end

    File.write!(
      Path.join(tools, "lynx-toolchain"),
      "profile=runtime\naeneas_branching=duplicate-v1\n"
    )

    assert Branching.backend_arguments!([branching: :duplicate], tools) == ["-duplicate-branches"]
  end

  test "backend metadata must confirm the selected mode" do
    assert :ok = Branching.validate_metadata!(%{}, [])
    assert :ok = Branching.validate_metadata!(%{"branch_joins" => true}, [])
    assert :ok = Branching.validate_metadata!(%{"branch_joins" => false}, branching: :duplicate)

    for {metadata, options} <- [
          {%{}, [branching: :duplicate]},
          {%{"branch_joins" => true}, [branching: :duplicate]},
          {%{"branch_joins" => false}, []},
          {%{"branch_joins" => "false"}, [branching: :duplicate]}
        ] do
      assert_raise ArgumentError, ~r/branch mode does not match/, fn ->
        Branching.validate_metadata!(metadata, options)
      end
    end
  end
end
