defmodule Lynx.Rustler.TermDecoderHelperTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.LibraryHelpers

  test "retains actual SDK forwarding instead of an assumed wrapper" do
    doc =
      JSON.decode!(File.read!(Path.expand("../../fixtures/rustler/atom_decoder.json", __DIR__)))

    translated = doc["translated"]

    helper =
      Enum.find(
        translated["fun_decls"],
        &(&1 &&
            match?(
              [
                %{"Ident" => ["rustler", 0]},
                %{"Ident" => ["term", 0]},
                _,
                %{"Ident" => ["decode", 0]}
              ],
              &1["item_meta"]["name"]
            ))
      )

    assert LibraryHelpers.selected?(helper, translated)
    assert "rustler::term::_::decode" in LibraryHelpers.includes()

    for changed <- [
          Map.put(helper, "body", "Opaque"),
          put_in(helper, ["signature", "abi"], "C"),
          put_in(helper, ["signature", "is_unsafe"], true)
        ],
        do: refute(LibraryHelpers.selected?(changed, translated))
  end
end
