defmodule LynxRustFixture.CaseLaws do
  use ExUnit.Case, register: false
  use Lynx.Case

  laws "native workspace through the standard ExUnit workflow",
    native:
      {Lynx.Rustler,
       workspace: Path.expand("..", __DIR__),
       package: "experiment-nif",
       lean_project: Path.expand("../proofs", __DIR__),
       module_prefix: "RustWorkspace.Facade",
       proof_modules: ["RustWorkspace.Native", "RustWorkspace.BridgeTests"]} do
    law restores_true,
      expects: LynxRustFixture.Native.restore(true) == true,
      proof: ~LEAN"""
      simp [«restores_true:ensures/0», Elixir.LynxRustFixture.Native.«restore/1»,
        Elixir.LynxRustFixture.Native.«restore:execution/1», RustWorkspace.Native.facade_spec,
        Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
      """
  end
end
