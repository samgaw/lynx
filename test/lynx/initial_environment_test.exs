defmodule Lynx.InitialEnvironmentTest do
  use ExUnit.Case, async: true
  import Lynx.Lean, only: [sigil_LEAN: 2]

  @prelude ~LEAN"""
  module
  public import Lynx
  public section
  namespace InitialModel
  @[expose] def seven : Lynx.Environment :=
    ({} : Lynx.Environment).setPdict [(.atom "seed",.integer 7)]
  @[expose] def eight : Lynx.Environment :=
    ({} : Lynx.Environment).setPdict [(.atom "seed",.integer 8)]
  def wrongType : Nat := 7
  end InitialModel
  """

  setup_all do
    {:module, _, beam, _} =
      defmodule Reader do
        @compile :debug_info
        use Lynx.Laws

        law seeded,
          expects: :erlang.get(:seed) == 7,
          proof: ~LEAN"""
          simp [Lynx.sequentialFrom_eq_run,Lynx.apply_eq,«seeded:ensures/0»,
            Erlang.erlang.«get/1»,Erlang.erlang.«==/2»,InitialModel.seven,
          Lynx.Result.monadGet_eq,Lynx.Environment.pdict,Lynx.Environment.setPdict]
          """
      end

    {:module, _, plain_beam, _} =
      defmodule Plain do
        @compile :debug_info
        use Lynx.Laws

        law truth, expects: true, proof: ~LEAN"rfl"
      end

    %{beam: beam, plain_beam: plain_beam}
  end

  @tag :tmp_dir
  test "laws use and report an explicit model state and cache it separately", %{
    tmp_dir: tmp,
    beam: beam
  } do
    opts = [
      preludes: [@prelude],
      initial_environment: "InitialModel.seven",
      debug_dir: tmp,
      debug: :lean
    ]

    reports = Lynx.Laws.verify([beam], opts)
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)

    assert %{initial_environments: ["InitialModel.seven"], trusted_boundary: [boundary]} =
             List.last(reports)

    assert boundary =~ "correspondence to a live external system is unverified"
    assert Enum.all?(Lynx.Laws.verify([beam], opts), &(&1.status == :ok and &1.cached))

    changed =
      Lynx.Laws.verify([beam], Keyword.put(opts, :initial_environment, "InitialModel.eight"))

    assert %{status: :ok, cached: true} = hd(changed)

    assert %{status: :error, cached: false, initial_environments: ["InitialModel.eight"]} =
             List.last(changed)

    export = Path.join(tmp, "initial.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam], Keyword.put(opts, :export, export)),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    project = Path.expand("../../Lean", __DIR__)
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end

  test "unknown, malformed and incorrectly typed model definitions fail", %{beam: beam} do
    for name <- ["InitialModel.missing", "InitialModel.wrongType", "(by sorry)"] do
      assert_raise RuntimeError, ~r/initial_environment|invalid identifier/, fn ->
        Lynx.Laws.verify([beam], preludes: [@prelude], initial_environment: name)
      end
    end

    for invalid <- [false, 1, ""] do
      assert_raise ArgumentError, ~r/initial_environment/, fn ->
        Lynx.Laws.verify([beam], initial_environment: invalid)
      end
    end
  end

  test "the model module is audited even when its extra declarations are private and unused", %{
    beam: beam
  } do
    for extra <- [
          "private axiom hiddenModelTrust : False",
          "private theorem unfinishedModel : True := by sorry"
        ] do
      prelude = %{@prelude | source: @prelude.source <> "\n" <> extra <> "\n"}

      reports =
        Lynx.Laws.verify([beam], preludes: [prelude], initial_environment: "InitialModel.seven")

      assert Enum.any?(reports, &(&1.status == :error)), inspect(reports, limit: :infinity)
      assert List.last(reports).status == :skipped
    end
  end

  test "private unused prelude declarations are audited without an initial environment", %{
    plain_beam: beam
  } do
    assert Enum.all?(Lynx.Laws.verify([beam], preludes: [@prelude]), &(&1.status == :ok))

    for extra <- [
          "private axiom hiddenPreludeTrust : False",
          "private theorem unfinishedPrelude : True := by sorry"
        ] do
      prelude = %{@prelude | source: @prelude.source <> "\n" <> extra <> "\n"}
      reports = Lynx.Laws.verify([beam], preludes: [prelude])

      assert Enum.any?(reports, &(&1.module == "Erlang.prelude" and &1.status == :error)),
             inspect(reports, limit: :infinity)

      assert List.last(reports).status == :skipped
    end
  end

  @tag :tmp_dir
  test "composes complete proof files with their own imports and caches the audited module", %{
    tmp_dir: tmp,
    plain_beam: beam
  } do
    second = ~LEAN"""
    module
    public import Lynx.Modules.Erlang.erlang
    public section
    namespace SecondProofFile
    theorem equal : Erlang.erlang.«==/2» (.integer 7) (.integer 7) = .ok Lynx.Term.true := by
      simp [Erlang.erlang.«==/2»]
    end SecondProofFile
    """

    opts = [preludes: [@prelude, second], debug_dir: tmp, debug: :lean]
    reports = Lynx.Laws.verify([beam], opts)
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    assert Enum.all?(Lynx.Laws.verify([beam], opts), &(&1.status == :ok and &1.cached))

    source = Path.join(tmp, "Erlang/prelude.lean")
    assert File.read!(source) =~ "public import Lynx.Modules.Erlang.erlang"
    {status, output} = Lynx.Commands.lake(Path.expand("Lean"), ["env", "lean", source])
    assert status == 0, output

    for extra <- [
          "private axiom hiddenSecondFile : False",
          "private theorem unfinishedSecondFile : True := by sorry"
        ] do
      wrong = %{second | source: second.source <> "\n" <> extra <> "\n"}
      reports = Lynx.Laws.verify([beam], preludes: [@prelude, wrong])
      assert Enum.any?(reports, &(&1.module == "Erlang.prelude" and &1.status == :error))
      assert List.last(reports).status == :skipped
    end
  end

  test "later declaration fragments still extend the first proof file", %{plain_beam: beam} do
    fragment = ~LEAN"""
    namespace InitialModel
    theorem seeded : seven.pdict = [(.atom "seed", .integer 7)] := by
      simp [seven, Lynx.Environment.pdict, Lynx.Environment.setPdict]
    end InitialModel
    """

    reports = Lynx.Laws.verify([beam], preludes: [@prelude, fragment])
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
  end
end
