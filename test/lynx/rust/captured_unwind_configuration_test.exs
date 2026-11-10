defmodule Lynx.Rust.CapturedUnwindConfigurationTest do
  use ExUnit.Case, async: true

  @tag :tmp_dir
  test "does not accept missing or different cleanup-preservation revisions", %{tmp_dir: tmp} do
    for marker <- [
          "profile=unpatched",
          "charon_cleanup_edges=preserved-v10",
          "charon_cleanup_edges=preserved-v1-unchecked"
        ] do
      File.write!(Path.join(tmp, "lynx-toolchain"), marker <> "\n")

      assert_raise ArgumentError, ~r/cleanup-preserving Charon/, fn ->
        Lynx.Rust.NativeUnwind.backend_arguments!(:captured, tmp)
      end
    end
  end
end
