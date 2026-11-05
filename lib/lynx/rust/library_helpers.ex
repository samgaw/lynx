defmodule Lynx.Rust.LibraryHelpers do
  @moduledoc false

  # Only this small helper is retained from third-party dependency metadata.
  # Inclusion is not a specification or an approval of its behavior: its actual
  # body goes through the same call audit, extraction and kernel checking as a
  # workspace function. Other dependency functions remain outside this scope.
  def includes, do: ["thiserror::display"]

  def selected?(
        %{
          "def_id" => function_id,
          "item_meta" => %{
            "name" => [
              %{"Ident" => ["thiserror", disambiguator]},
              %{"Ident" => ["display", 0]},
              %{"Impl" => %{"Trait" => impl_id}},
              %{"Ident" => ["as_display", 0]}
            ]
          },
          "src" => %{
            "TraitImpl" => %{
              "impl_ref" => %{"id" => impl_id},
              "trait_ref" => %{"id" => trait_id},
              "item_id" => 0,
              "reuses_default" => false
            }
          }
        },
        translated
      )
      when is_integer(disambiguator) and disambiguator >= 0 do
    case Enum.find(translated["trait_impls"] || [], &(&1 && &1["def_id"] == impl_id)) do
      %{
        "src" => "Normal",
        "is_negative" => false,
        "is_unsafe" => false,
        "impl_trait" => %{"id" => ^trait_id},
        "methods" => [
          %{
            "kind" => %{"TraitMethod" => [^trait_id, 0]},
            "skip_binder" => %{"id" => ^function_id}
          }
        ]
      } ->
        case Enum.find(translated["trait_decls"] || [], &(&1 && &1["def_id"] == trait_id)) do
          %{
            "item_meta" => %{
              "name" => [
                %{"Ident" => ["thiserror", ^disambiguator]},
                %{"Ident" => ["display", 0]},
                %{"Ident" => ["AsDisplay", 0]}
              ]
            }
          } ->
            true

          _ ->
            false
        end

      _ ->
        false
    end
  end

  def selected?(_, _), do: false
end
