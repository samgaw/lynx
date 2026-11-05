defmodule Lynx.RustWorkspaceExampleTest do
  use ExUnit.Case

  @moduletag timeout: 900_000
  if is_nil(System.get_env("LYNX_AENEAS_DIR")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for the self-contained Rustler example")

  test "the self-contained example proves its native workspace and Elixir laws" do
    {output, status} =
      System.cmd("mix", ["run", "examples/rust_workspace/run.exs"],
        cd: Path.expand("../..", __DIR__),
        env: [{"MIX_ENV", "dev"}, {"LYNX_CACHE", "0"}],
        stderr_to_stdout: true
      )

    assert status == 0, output
    assert output =~ "Result: 2 passed (1 laws, 1 test)"
    refute output =~ "skipped"
  end
end
