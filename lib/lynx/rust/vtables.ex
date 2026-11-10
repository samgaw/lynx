defmodule Lynx.Rust.VTables do
  @moduledoc false
  alias Lynx.Rust.{CallModels, DropModels, FormatModels}
  @args %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}
  @label "Compiler vtable metadata validated against actual extracted trait implementation; logical dictionary construction uses actual extracted methods; native vtable ABI, allocation and deallocation unverified"

  # Aeneas constructs Dyn with the actual impl dictionary and omits the physical
  # vtable/shims. Admit only checked metadata; arbitrary function pointers and
  # first-party destructor effects must not disappear with those shims.
  def audit!(globals, functions, translated, refs) do
    if length(globals) != MapSet.size(MapSet.new(globals, & &1["def_id"])),
      do: raise(ArgumentError, "duplicate LLBC constant identity")

    tables = Enum.filter(globals, &(&1["global_kind"] == "VTable"))

    checked =
      Map.new(tables, fn global -> {global["def_id"], table!(global, translated, refs)} end)

    shims = checked |> Map.values() |> Enum.flat_map(& &1["lynx_vtable"].shims) |> MapSet.new()
    ordinary = Enum.reject(functions, &MapSet.member?(shims, &1["def_id"]))

    dependencies =
      Map.new(ordinary, fn function ->
        ids = globals(function["body"]) |> Enum.uniq()

        {function["def_id"],
         ids
         |> Enum.flat_map(fn id ->
           if checked[id], do: checked[id]["lynx_vtable"].methods, else: []
         end)
         |> Enum.uniq()}
      end)

    {checked, ordinary, dependencies}
  end

  # Only this catalogued foreign dictionary may be admitted. Its method remains
  # an explicitly reported Rustler FFI model, never a first-party implementation.
  def foreign_globals(translated) do
    Enum.filter(translated["global_decls"], fn global ->
      global && global["global_kind"] == "VTable" &&
        match?(
          [
            %{"Ident" => ["rustler", 0]},
            %{"Ident" => ["types", 0]},
            %{"Ident" => ["string", 0]},
            %{"Impl" => %{"Trait" => _}},
            %{"Builtin" => ["VTable", 0]}
          ],
          global["item_meta"]["name"]
        )
    end)
  end

  def merge_drops(tables, audit) do
    Enum.reduce(Map.values(tables), audit, fn global, audit ->
      case global["lynx_vtable"][:drops] do
        nil ->
          audit

        drops ->
          Map.new(audit, fn {key, entries} ->
            {key,
             Map.merge(entries, drops[key], fn _id, left, right ->
               unless left == right,
                 do: raise(ArgumentError, "inconsistent vtable destruction dependency")

               left
             end)}
          end)
      end
    end)
  end

  defp table!(global, translated, refs) do
    ctx = %{translated: translated, refs: refs, traits: %{}}

    try do
      %{
        "VTableInstance" => %{
          "self_ty" => self,
          "impl_ref" => %{"id" => impl_id, "generics" => @args}
        }
      } = global["src"]

      impl = one!(translated["trait_impls"], impl_id)
      %{"id" => trait_id, "generics" => %{"types" => [impl_self]} = args} = impl["impl_trait"]
      trait = one!(translated["trait_decls"], trait_id)
      self = CallModels.expand(self, refs)
      true = self == CallModels.expand(impl_self, refs)
      true = args == %{@args | "types" => [impl_self]}
      true = impl["src"] == "Normal" && impl["is_negative"] == false && impl["is_unsafe"] == false

      true =
        plain?(impl["generics"]) && impl["consts"] == [] && impl["types"] == [] &&
          impl["implied_trait_refs"] == []

      true =
        trait["src"] == "Normal" && trait["is_unsafe"] == false && trait["consts"] == [] &&
          trait["types"] == [] && trait["implied_clauses"] == []

      true =
        global["item_meta"]["has_errors"] == false &&
          global["item_meta"]["opacity"] == "Transparent" && plain?(global["generics"])

      true = impl["item_meta"]["has_errors"] == false && trait["item_meta"]["has_errors"] == false
      true = length(trait["methods"]) == 1
      [%{"index" => 0}] = trait["generics"]["types"]
      true = plain?(%{trait["generics"] | "types" => []})
      true = impl["vtable"] == %{"VTable" => %{"id" => global["def_id"], "generics" => @args}}

      true =
        global["item_meta"]["name"] ==
          impl["item_meta"]["name"] ++ [%{"Builtin" => ["VTable", 0]}]

      %{"Adt" => %{"id" => self_id, "builtin" => nil, "generics" => @args}} = self
      payload = one!(translated["type_decls"], self_id)
      true = plain?(payload["generics"]) && payload["item_meta"]["has_errors"] == false
      [%{"skip_binder" => %{"id" => method_id}}] = impl["methods"]
      method = one!(translated["fun_decls"], method_id)
      true = method["item_meta"]["has_errors"] == false
      true = FormatModels.method_identity?(method, impl, trait_id, ctx)

      standard =
        payload["kind"] == "Opaque" &&
          payload["item_meta"]["name"] ==
            Enum.map(~w(alloc string String), &%{"Ident" => [&1, 0]})

      model = if standard, do: Lynx.Rustler.EncoderModels.resolve(method, translated, refs)

      if standard do
        %{lean: "Lynx.Rustler.Encoding.string", encoder_standard: true} = model
      else
        %{"Struct" => fields} = payload["kind"]
        true = Enum.all?(fields, &DropModels.primitive_scalar?(CallModels.expand(&1["ty"], refs)))
        true = is_map(method["body"])
      end

      profile = method_profile!(method, self, translated, refs)

      %{"Adt" => %{"id" => table_id, "builtin" => nil, "generics" => @args}} =
        CallModels.expand(global["ty"], refs)

      true = trait["vtable"] == %{"id" => table_id, "builtin" => nil, "generics" => @args}
      table = one!(translated["type_decls"], table_id)
      true = dyn_trait!(table["src"]["VTable"]["dyn_predicate"]) == trait_id

      %{
        "VTable" => %{
          "field_map" => ["Size", "Align", "Drop", %{"Method" => [0, []]}],
          "supertrait_map" => []
        }
      } = table["src"]

      [%{"Adt" => [nil, [size, align, drop, slot]]}, value_type] =
        CallModels.expand(global["value"], refs)

      true = value_type == CallModels.expand(global["ty"], refs)
      usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
      [%{"SizeOf" => ^self}, ^usize] = size
      [%{"AlignOf" => ^self}, ^usize] = align
      drop_id = pointer!(drop, 1)
      slot_id = pointer!(slot, length(profile.regions))
      drop_fn = one!(translated["fun_decls"], drop_id)
      slot_fn = one!(translated["fun_decls"], slot_id)

      true =
        drop_fn["item_meta"]["name"] ==
          impl["item_meta"]["name"] ++ [%{"Builtin" => ["VTableDropShim", 0]}]

      true =
        slot_fn["item_meta"]["name"] ==
          method["item_meta"]["name"] ++ [%{"Builtin" => ["VTableMethod", 0]}]

      drop_profile =
        if standard,
          do: %{region: 0, target: 2, extra: [], output: nil, regions: [0], string: true}

      shim!(drop_fn, nil, self, trait_id, drop_profile, refs)
      shim!(slot_fn, method_id, self, trait_id, profile, refs)

      drops =
        if standard do
          {:ok, drops} = DropModels.audit([drop_fn], [], translated, refs, [])
          true = map_size(drops.erasures) == 1
          drops
        end

      Map.put(global, "lynx_vtable", %{
        impl: impl_id,
        trait: trait_id,
        model_method: if(standard, do: model.lean),
        drops: drops,
        external_trait: if(Map.get(profile, :encoder, false), do: "rustler::types::Encoder"),
        methods: [method_id],
        shims: [drop_id, slot_id]
      })
    rescue
      error in [MatchError, KeyError, ArgumentError] ->
        reraise ArgumentError,
                [
                  message:
                    "missing or unsupported compiler vtable metadata #{inspect(global["def_id"])}; requires a monomorphic scalar-field payload, one extracted shared scalar method or validated Rustler Encoder, and a callback-free destructor: #{Exception.message(error)}"
                ],
                __STACKTRACE__
    end
  end

  defp method_profile!(method, self, translated, refs) do
    signature = CallModels.expand(method["signature"], refs)

    if Lynx.Rustler.EncoderModels.implementation_method?(method, self, translated, refs) do
      [_receiver, env] = signature["inputs"]

      %{
        region: 1,
        target: 3,
        extra: [env],
        output: signature["output"],
        regions: [0, 1],
        encoder: true
      }
    else
      %{
        "is_unsafe" => false,
        "abi" => "Rust",
        "is_variadic" => false,
        "inputs" => [%{"Ref" => [%{"Var" => %{"Free" => 0}}, ^self, "Shared"]}],
        "output" => output
      } = signature

      true = DropModels.primitive_scalar?(output)
      %{region: 0, target: 2, extra: [], output: output, regions: [0]}
    end
  end

  defp shim!(function, method, self, trait, profile, refs) do
    profile = profile || %{region: 0, target: 2, extra: [], output: nil, regions: [0]}
    true = function["src"] == "VTableShim" && function["item_meta"]["has_errors"] == false

    %{
      "is_unsafe" => unsafe,
      "abi" => "Rust",
      "is_variadic" => false,
      "inputs" => [%{"Ref" => [region, %{"DynTrait" => predicate}, kind]} | extra],
      "output" => output
    } = CallModels.expand(function["signature"], refs)

    true = region == %{"Var" => %{"Free" => profile.region}} && extra == profile.extra
    true = unsafe == (method == nil) && dyn_trait!(predicate) == trait
    true = kind == if(method == nil, do: "Mut", else: "Shared")

    kinds =
      function["body"]["Structured"]["body"]["statements"]
      |> Enum.map(& &1["kind"])
      |> Enum.reject(&storage?/1)

    if method == nil do
      kinds =
        if Map.get(profile, :string, false) do
          [initial, cast, %{"Drop" => drop}, "Return"] = kinds

          expected = %{
            "kind" => %{
              "Projection" => [
                %{
                  "kind" => %{"Local" => 2},
                  "ty" => %{"Ref" => [%{"Var" => %{"Free" => 0}}, self, "Mut"]}
                },
                "Deref"
              ]
            },
            "ty" => self
          }

          true = CallModels.expand(drop["place"], refs) == expected
          [initial, cast, "Return"]
        else
          kinds
        end

      [
        %{
          "Assign" => [
            %{"kind" => %{"Local" => 0}},
            %{
              "Aggregate" => [
                %{"Adt" => [%{"builtin" => "Tuple", "generics" => @args}, nil, nil]},
                []
              ]
            }
          ]
        },
        cast,
        "Return"
      ] = kinds

      cast!(cast, self, "Mut", profile, refs)
    else
      true = output == profile.output
      [cast, %{"Call" => call}, "Return"] = kinds
      cast!(cast, self, "Shared", profile, refs)

      %{
        "func" => %{"Regular" => %{"kind" => %{"Fun" => ^method}, "generics" => args}},
        "args" => actual,
        "safety" => "Inherit"
      } = call["call"]

      true =
        args == %{@args | "regions" => Enum.map(profile.regions, &%{"Var" => %{"Free" => &1}})}

      receiver = %{
        "Move" => %{
          "kind" => %{"Local" => profile.target},
          "ty" => %{"Ref" => [region, self, "Shared"]}
        }
      }

      expected = [
        receiver
        | Enum.with_index(profile.extra, 2)
          |> Enum.map(fn {type, index} ->
            %{"Move" => %{"kind" => %{"Local" => index}, "ty" => type}}
          end)
      ]

      true = CallModels.expand(actual, refs) == expected
      %{"kind" => %{"Local" => 0}} = call["dest"]

      ["UnwindResume"] =
        call["on_unwind"]["statements"] |> Enum.map(& &1["kind"]) |> Enum.reject(&storage?/1)
    end
  end

  defp dyn_trait!(%{
         "binder" => %{
           "params" => %{
             "trait_clauses" => [clause],
             "trait_type_constraints" => [],
             "const_generics" => []
           }
         }
       }) do
    %{"origin" => "Dyn", "trait_" => %{"skip_binder" => %{"id" => trait}}} = clause
    trait
  end

  defp cast!(
         %{
           "Assign" => [
             %{"kind" => %{"Local" => local}, "ty" => dest},
             %{
               "UnaryOp" => [
                 %{"Cast" => %{"Concretize" => [target, []]}},
                 %{"Move" => %{"kind" => %{"Local" => 1}}}
               ]
             }
           ]
         },
         self,
         kind,
         profile,
         refs
       ) do
    true = local == profile.target
    expected = %{"Ref" => [%{"Var" => %{"Free" => profile.region}}, self, kind]}

    true =
      CallModels.expand(dest, refs) == expected && CallModels.expand(target, refs) == expected
  end

  defp pointer!([%{"FnPtr" => %{"kind" => %{"Fun" => id}, "generics" => args}}, _], regions) do
    true = args == %{@args | "regions" => List.duplicate("Erased", regions)}
    id
  end

  defp storage?(%{"StorageLive" => _}), do: true
  defp storage?(%{"StorageDead" => _}), do: true
  defp storage?(_), do: false
  defp plain?(params), do: is_map(params) && Enum.all?(Map.values(params), &(&1 == []))

  defp one!(items, id) do
    [item] = Enum.filter(items, &(&1 && &1["def_id"] == id))
    item
  end

  defp globals(%{"Global" => %{"id" => id}}), do: [id]
  defp globals(map) when is_map(map), do: Enum.flat_map(Map.values(map), &globals/1)
  defp globals(list) when is_list(list), do: Enum.flat_map(list, &globals/1)
  defp globals(_), do: []

  def link!(global, translation) do
    info = global["lynx_vtable"]

    [impl] =
      Enum.filter(
        translation["trait_impls"],
        &(&1["def_id"] == info.impl && &1["impl_trait_def_id"] == info.trait)
      )

    traits = Enum.filter(translation["trait_decls"], &(&1["def_id"] == info.trait))

    case {traits, Map.get(info, :external_trait)} do
      {[_], nil} ->
        :ok

      {[], "rustler::types::Encoder"} ->
        true =
          impl["impl_trait_is_builtin"] == true &&
            impl["impl_trait_rust_name"] == "rustler::types::Encoder"

      _ ->
        raise ArgumentError, "missing or inconsistent extracted vtable trait identity"
    end

    true =
      Enum.all?(info.methods, fn id ->
        case info[:model_method] do
          "Lynx.Rustler.Encoding.string" ->
            Enum.all?(translation["functions"], &(&1["def_id"] != id))

          nil ->
            Enum.count(
              translation["functions"],
              &(&1["def_id"] == id && &1["is_opaque"] == false)
            ) == 1

          _ ->
            false
        end
      end)

    %{
      "def_id" => global["def_id"],
      "rust_name" => impl["rust_name"] <> "::{vtable}",
      "lean_name" => impl["lean_name"],
      "declaration" => global,
      "inlined" => true,
      "modelled" => true,
      "label" =>
        if(info[:model_method],
          do:
            "Rustler String Encoder vtable and shims validated against the compiled interface; dictionary invokes the approved String encoding model; logical String deallocation model; native vtable ABI, encoding FFI, allocation and reclamation unverified",
          else: @label
        )
    }
  rescue
    _ in [MatchError, KeyError] ->
      raise ArgumentError,
            "missing or inconsistent extracted Rust vtable dictionary #{inspect(global["def_id"])}"
  end
end
