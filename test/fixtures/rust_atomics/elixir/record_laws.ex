defmodule LynxRecordFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law map_matched,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          LynxRecordFixture.Native.atomic_map(resource, %{expected: 7, replacement: 11}) ==
            {true, 7}

        returned and LynxRecordFixture.Native.atomic_read(resource) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.map_success [(.atom "replacement", .integer 11), (.atom "expected", .integer 7)] 7#u64 11#u64 (by rfl) (by rfl)
    simp only [Lynx.apply, «map_matched:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_map/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law map_mismatch,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          LynxRecordFixture.Native.atomic_map(resource, %{expected: 8, replacement: 11}) ==
            {false, 7}

        returned and LynxRecordFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.map_success [(.atom "replacement", .integer 11), (.atom "expected", .integer 8)] 8#u64 11#u64 (by rfl) (by rfl)
    simp only [Lynx.apply, «map_mismatch:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_map/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law map_extra,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          LynxRecordFixture.Native.atomic_map(resource, %{
            expected: 7,
            extra: true,
            replacement: 11
          }) == {true, 7}

        returned and LynxRecordFixture.Native.atomic_read(resource) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.map_success [(.atom "replacement", .integer 11), (.atom "expected", .integer 7), (.atom "extra", .atom "true")] 7#u64 11#u64 (by rfl) (by rfl)
    simp only [Lynx.apply, «map_extra:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_map/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law map_nonmap,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          try do
            LynxRecordFixture.Native.atomic_map(resource, 7)
            false
          catch
            :error, :badarg -> true
          end

        returned and LynxRecordFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.map_nonmap 7
    simp only [Lynx.apply, «map_nonmap:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_map/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law map_missing_first,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          try do
            LynxRecordFixture.Native.atomic_map(resource, %{replacement: 11})
            false
          catch
            :error, :badarg -> true
          end

        returned and LynxRecordFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.map_missing_first [(.atom "replacement", .integer 11)] (by rfl)
    simp only [Lynx.apply, «map_missing_first:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_map/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law map_missing_second,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          try do
            LynxRecordFixture.Native.atomic_map(resource, %{expected: 7})
            false
          catch
            :error, :badarg -> true
          end

        returned and LynxRecordFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.map_missing_second [(.atom "expected", .integer 7)] 7#u64 (by rfl) (by rfl)
    simp only [Lynx.apply, «map_missing_second:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_map/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law map_bad_first,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          try do
            LynxRecordFixture.Native.atomic_map(resource, %{expected: false, replacement: 11})
            false
          catch
            :error, reason -> reason == "Could not decode field :expected on %{}"
          end

        returned and LynxRecordFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.map_expected_encoded [(.atom "replacement", .integer 11), (.atom "expected", .atom "false")] (.atom "false") (by rfl) (by rfl)
    simp only [Lynx.apply, «map_bad_first:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_map/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law map_bad_second,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          try do
            LynxRecordFixture.Native.atomic_map(resource, %{expected: 7, replacement: -1})
            false
          catch
            :error, reason -> reason == "Could not decode field :replacement on %{}"
          end

        returned and LynxRecordFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.map_replacement_encoded [(.atom "replacement", .integer (-1)), (.atom "expected", .integer 7)] (.integer (-1)) 7#u64 (by rfl) (by rfl) (by rfl)
    simp only [Lynx.apply, «map_bad_second:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_map/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law struct_matched,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          LynxRecordFixture.Native.atomic_struct(resource, %{
            __struct__: LynxRecordFixture.Request,
            expected: 7,
            replacement: 11
          }) == {true, 7}

        returned and LynxRecordFixture.Native.atomic_read(resource) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.struct_success [(.atom "replacement", .integer 11), (.atom "expected", .integer 7), (.atom "__struct__", .atom "Elixir.LynxRecordFixture.Request")] 7#u64 11#u64 (by rfl) (by rfl) (by rfl)
    simp only [Lynx.apply, «struct_matched:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_struct/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law struct_missing_tag,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          try do
            LynxRecordFixture.Native.atomic_struct(resource, %{expected: 7, replacement: 11})
            false
          catch
            :error, :badarg -> true
          end

        returned and LynxRecordFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.struct_missing_tag [(.atom "replacement", .integer 11), (.atom "expected", .integer 7)] (by rfl)
    simp only [Lynx.apply, «struct_missing_tag:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_struct/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law struct_nonatom_tag,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          try do
            LynxRecordFixture.Native.atomic_struct(resource, %{
              __struct__: 7,
              expected: 7,
              replacement: 11
            })

            false
          catch
            :error, :badarg -> true
          end

        returned and LynxRecordFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.struct_nonatom_tag [(.atom "replacement", .integer 11), (.atom "expected", .integer 7), (.atom "__struct__", .integer 7)] 7 (by rfl)
    simp only [Lynx.apply, «struct_nonatom_tag:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_struct/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law struct_wrong_tag,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          try do
            LynxRecordFixture.Native.atomic_struct(resource, %{
              __struct__: :wrong,
              expected: false,
              replacement: false
            })

            false
          catch
            :error, :invalid_struct -> true
          end

        returned and LynxRecordFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.struct_wrong_tag [(.atom "replacement", .atom "false"), (.atom "expected", .atom "false"), (.atom "__struct__", .atom "wrong")] "wrong" (by decide +kernel) (by rfl)
    simp only [Lynx.apply, «struct_wrong_tag:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_struct/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law struct_bad_first,
    expects:
      (
        resource = LynxRecordFixture.Native.atomic_new(7)

        returned =
          try do
            LynxRecordFixture.Native.atomic_struct(resource, %{
              __struct__: LynxRecordFixture.Request,
              expected: false,
              replacement: 11
            })

            false
          catch
            :error, reason -> reason == "Could not decode field :expected on %StructRequest{}"
          end

        returned and LynxRecordFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Records.Properties.struct_expected_encoded [(.atom "replacement", .integer 11), (.atom "expected", .atom "false"), (.atom "__struct__", .atom "Elixir.LynxRecordFixture.Request")] (.atom "false") (by rfl) (by rfl) (by rfl)
    simp only [Lynx.apply, «struct_bad_first:ensures/0»,
      Elixir.LynxRecordFixture.Native.«atomic_struct/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """
end
