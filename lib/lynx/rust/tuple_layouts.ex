defmodule Lynx.Rust.TupleLayouts do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Cargo, Fingerprint, LLBC}
  @wrapper "LynxTupleLayout"

  # Builtin tuples have no TypeDecl layout in LLBC. Ask the same compiler for
  # a repr(C) wrapper containing precisely that builtin type. Its total size is
  # a conservative bound on the field; no application definition is replaced.
  def prepare!(context, tools, document, output, module, first_party) do
    t = document["translated"]
    refs = LLBC.type_references!(t)

    pushes =
      for f <- t["fun_decls"],
          f,
          model = Lynx.Rust.CollectionModels.resolve(f, t, refs),
          model && model[:vec_owned_method] == "push",
          into: MapSet.new(),
          do: f["def_id"]

    types =
      for f <- t["fun_decls"],
          f,
          [%{"Ident" => [crate, _]} | _] = f["item_meta"]["name"],
          crate in first_party,
          type <- candidates(f["body"], pushes, refs),
          render(type) != nil,
          uniq: true,
          do: type

    queries =
      types
      |> Enum.sort_by(&:erlang.term_to_binary/1)
      |> Enum.with_index()
      |> Enum.map(fn {type, index} ->
        dir = Path.join(output, "#{String.replace(module, ".", "_")}.tuple-layout-#{index}")
        File.mkdir_p!(dir)
        source = source(render(type))
        path = Path.join(dir, "probe.rs")
        llbc = Path.join(dir, "probe.llbc")
        File.write!(path, source)
        args = arguments!(context, path, dir)

        {diagnostics, status} =
          System.cmd(
            Path.join(tools, "charon"),
            [
              "rustc",
              "--sysroot",
              if(context[:sysroot], do: context.sysroot.path, else: "default"),
              "--preset=aeneas",
              "--start-from",
              "crate::lynx_tuple_layout",
              "--dest-file",
              llbc,
              "--"
            ] ++ args,
            cd: context.record["directory"],
            env: Cargo.environment(context),
            stderr_to_stdout: true
          )

        unless status == 0, do: raise("tuple layout compiler query failed:\n#{diagnostics}")
        probe = llbc |> File.read!() |> JSON.decode!()
        bytes = validate!(probe, document, type)

        %{
          type: type,
          bytes: bytes,
          source_sha256: Fingerprint.digest(source),
          llbc_sha256: Fingerprint.file!(llbc)
        }
      end)

    %{
      queries: queries,
      targets: t["target_information"],
      fingerprint: Fingerprint.digest(:erlang.term_to_binary(queries, [:deterministic]))
    }
  end

  def allowed?(type, %{queries: queries, targets: targets}, selected) when targets == selected do
    Enum.any?(
      queries,
      &(&1.type == type and is_integer(&1.bytes) and &1.bytes >= 0 and &1.bytes <= 4095)
    )
  end

  def allowed?(_, _, _), do: false

  def validate!(probe, original, type) do
    t = probe["translated"]
    refs = LLBC.type_references!(t)

    wrappers =
      Enum.filter(t["type_decls"], fn d ->
        d && d["item_meta"]["is_local"] == true &&
          d["item_meta"]["name"] ==
            [%{"Ident" => [t["crate_name"], 0]}, %{"Ident" => [@wrapper, 0]}]
      end)

    with true <- probe["has_errors"] == false,
         true <- probe["charon_version"] == original["charon_version"],
         true <- t["crate_name"] == original["translated"]["crate_name"],
         true <- t["target_information"] == original["translated"]["target_information"],
         [
           %{
             "src" => "Normal",
             "generics" => generics,
             "kind" => %{"Struct" => [field]},
             "layout" => [layout]
           }
         ] <- wrappers,
         true <-
           Enum.all?(
             ~w(regions types const_generics trait_clauses outlives trait_type_constraints),
             &(generics[&1] == [])
           ),
         true <- render(type) != nil and CallModels.expand(field["ty"], refs) == type,
         [%{"key" => target, "value" => %{"target_pointer_size" => pointer}}] <-
           t["target_information"],
         true <- pointer in [4, 8],
         %{
           "key" => ^target,
           "value" => %{
             "size" => %{"chosen" => chosen},
             "repr" => %{"repr_algo" => "C", "align_modif" => nil, "transparent" => false},
             "variant_layouts" => [%{"field_offsets" => [%{"chosen" => 0}]}]
           }
         } <- layout,
         %{
           "Value" => [
             _,
             %{
               "Constant" => %{
                 "Value" => [_, [%{"Integer" => %{"Unsigned" => ["Usize", text]}}, size_type]]
               }
             }
           ]
         } <- chosen,
         true <- is_binary(text),
         true <-
           CallModels.expand(size_type, refs) == %{
             "Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}
           },
         {bytes, ""} when bytes >= 0 <- Integer.parse(text) do
      bytes
    else
      _ -> raise ArgumentError, "inconsistent compiler tuple layout evidence"
    end
  end

  defp candidates(
         %{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => g}} = node,
         pushes,
         refs
       ) do
    own =
      if MapSet.member?(pushes, id) do
        case CallModels.expand(g["types"], refs) do
          [%{"Adt" => %{"builtin" => "Tuple"}} = type | _] -> [type]
          _ -> []
        end
      else
        []
      end

    own ++ candidates(Map.values(node), pushes, refs)
  end

  defp candidates(node, pushes, refs) when is_map(node),
    do: candidates(Map.values(node), pushes, refs)

  defp candidates(nodes, pushes, refs) when is_list(nodes),
    do: Enum.flat_map(nodes, &candidates(&1, pushes, refs))

  defp candidates(_, _, _), do: []

  # Only closed builtin scalar tuples are rendered. Named, generic, reference,
  # floating-point and borrowed types cannot acquire layout evidence this way.
  defp render(%{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => g}}), do: tuple(g, 0)
  defp render(_), do: nil

  defp tuple(
         %{"regions" => [], "const_generics" => [], "trait_refs" => [], "types" => types},
         depth
       )
       when depth < 8 and length(types) in 1..32 do
    fields = Enum.map(types, &field(&1, depth + 1))
    if Enum.all?(fields, &is_binary/1), do: "(" <> Enum.join(fields, ",") <> ",)"
  end

  defp tuple(_, _), do: nil
  defp field(%{"Scalar" => "Bool"}, _), do: "bool"

  defp field(%{"Scalar" => %{"Integer" => %{"Unsigned" => width}}}, _)
       when width in ~w(U8 U16 U32 U64 U128 Usize), do: String.downcase(width)

  defp field(%{"Scalar" => %{"Integer" => %{"Signed" => width}}}, _)
       when width in ~w(I8 I16 I32 I64 I128 Isize), do: String.downcase(width)

  defp field(%{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => g}}, depth),
    do: tuple(g, depth)

  defp field(_, _), do: nil

  defp source(type),
    do: """
    //! Compiler-only layout query for a closed builtin tuple.
    #[repr(C)]
    /// A containing bound on the tuple's storage size.
    pub struct #{@wrapper} {
        /// The exact builtin type from the application call site.
        pub value: #{type},
    }
    /// Retains the concrete wrapper for compiler layout extraction.
    pub fn lynx_tuple_layout(value: #{@wrapper}) -> #{@wrapper} { value }
    """

  defp arguments!(context, path, dir) do
    source = Path.expand(context.artifact["target"]["src_path"])
    args = Cargo.extraction_arguments(context, dir)
    matches = Enum.count(args, &(Path.expand(&1, context.record["directory"]) == source))

    unless matches == 1,
      do: raise(ArgumentError, "tuple layout query cannot identify the Cargo source argument")

    Enum.map(args, fn arg ->
      if Path.expand(arg, context.record["directory"]) == source, do: path, else: arg
    end)
  end
end
