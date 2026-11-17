defmodule Lynx.Rust.RuntimeLoopTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.Runtime

  @tag :tmp_dir
  test "binds the emitted fixed point only in runtime loop wrappers", %{tmp_dir: tmp} do
    directory = Path.join(tmp, "Example")
    File.mkdir!(directory)
    path = Path.join(directory, "Funs.lean")

    source = """
    def caller (x : Bool) := do
      monadLift (loop x)

    @[rust_loop_body]
    def caller_loop.body (x : Bool) := do
      monadLift (loop x)

    @[rust_loop]
    def caller_loop (x : Bool) := do
      monadLift (loop caller_loop.body x)

    @[rust_loop, rust_fun
      "dependency::Container<[u64; 2]>::read", trait_default]
    def dependency.read_loop
      (x : Bool) :
      Lynx.NativeM
        Bool
      := do
      monadLift (loop dependency.read_loop.body x)
    """

    File.write!(path, source)
    wrapper = %{"loop" => %{"is_body" => false}}
    metadata = %{"functions" => [wrapper, wrapper]}
    Runtime.bind_loop_operator!("RustM", tmp, "Example", metadata)
    assert File.read!(path) == source

    Runtime.bind_loop_operator!("Lynx.NativeM", tmp, "Example", metadata)

    expected =
      source
      |> String.replace("(loop caller_loop.body x)", "(Lynx.NativeM.loop caller_loop.body x)")
      |> String.replace(
        "(loop dependency.read_loop.body x)",
        "(Lynx.NativeM.loop dependency.read_loop.body x)"
      )

    assert File.read!(path) == expected

    Runtime.bind_loop_operator!("Lynx.NativeM", tmp, "Example", metadata)
    assert File.read!(path) == expected

    assert_raise ArgumentError, ~r/native loop wrappers do not match/, fn ->
      Runtime.bind_loop_operator!("Lynx.NativeM", tmp, "Example", %{"functions" => []})
    end

    assert File.read!(path) == expected
  end
end
