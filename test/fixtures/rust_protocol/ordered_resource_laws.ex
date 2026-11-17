defmodule LynxRegistryFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  @proof ~LEAN"""
      set_option maxHeartbeats 24000000 in
      set_option maxRecDepth 8192 in
      refine ⟨0, ?_⟩
      intro depth enough elapsed events last outcome run terminal
      apply terminal.outcome_eq.symm.trans
      apply Lynx.Outcome.eq_of_isTrue
      apply Lynx.Concurrent.checkPost_sound (depth := 1024)
        (accept := fun config => config.outcome.isTrue) ?_ run terminal
      clear enough events last outcome run terminal
      cbv
  """

  law empty,
    expects:
      LynxRegistryFixture.Native.registry_take(LynxRegistryFixture.Native.registry_new(), 7) ==
        nil,
    proof: @proof

  law updates,
    expects:
      (
        registry = LynxRegistryFixture.Native.registry_new()
        first = LynxRegistryFixture.Native.registry_replace(registry, 7, 11)
        previous = LynxRegistryFixture.Native.registry_replace(registry, 7, 42)
        taken = LynxRegistryFixture.Native.registry_take(registry, 7)
        missing = LynxRegistryFixture.Native.registry_take(registry, 7)
        first == nil and previous == 11 and taken == 42 and missing == nil
      ),
    proof: @proof

  law independent_fields,
    expects:
      (
        registry = LynxRegistryFixture.Native.registry_new()
        LynxRegistryFixture.Native.registry_replace(registry, 7, 42)
        first = LynxRegistryFixture.Native.registry_claim(registry, 7)
        second = LynxRegistryFixture.Native.registry_claim(registry, 7)
        first and not second and LynxRegistryFixture.Native.registry_take(registry, 7) == 42
      ),
    proof: @proof

  law alias_observes,
    expects:
      (
        registry = LynxRegistryFixture.Native.registry_new()
        alias_handle = registry
        LynxRegistryFixture.Native.registry_replace(alias_handle, 7, 9)
        LynxRegistryFixture.Native.registry_take(registry, 7) == 9
      ),
    proof: @proof

  law rejected_input_preserves,
    expects:
      (
        registry = LynxRegistryFixture.Native.registry_new()
        LynxRegistryFixture.Native.registry_replace(registry, 7, 11)

        rejected =
          try do
            LynxRegistryFixture.Native.registry_replace(registry, 18_446_744_073_709_551_616, 42)
            false
          rescue
            ArgumentError -> true
          end

        rejected and LynxRegistryFixture.Native.registry_take(registry, 7) == 11
      ),
    proof: @proof

  law invalid_handle,
    expects:
      (try do
         LynxRegistryFixture.Native.registry_take(0, 7)
         false
       rescue
         ArgumentError -> true
       end),
    proof: @proof

  law concurrent_claims,
    expects:
      (
        registry = LynxRegistryFixture.Native.registry_new()
        parent = self()
        spawn(fn -> send(parent, LynxRegistryFixture.Native.registry_claim(registry, 7)) end)
        mine = LynxRegistryFixture.Native.registry_claim(registry, 7)

        theirs =
          receive do
            value -> value
          end

        mine != theirs
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
    set_option maxRecDepth 8192 in
    set_option cbv.maxSteps 2000000 in
    refine ⟨2, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le' enough
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.check_sound (depth := 1024)
      (accept := fun outcome => outcome.isTrue) ?_ run terminal
    clear events last outcome run terminal
    cbv
    """

  law first_key_empty,
    expects:
      LynxRegistryFixture.Native.registry_first_key(LynxRegistryFixture.Native.registry_new()) ==
        nil,
    proof: @proof

  law first_key_order,
    expects:
      (
        registry = LynxRegistryFixture.Native.registry_new()
        LynxRegistryFixture.Native.registry_replace(registry, 20, 1)
        LynxRegistryFixture.Native.registry_replace(registry, 3, 99)
        first = LynxRegistryFixture.Native.registry_first_key(registry)
        again = LynxRegistryFixture.Native.registry_first_key(registry)
        first == 3 and again == 3 and LynxRegistryFixture.Native.registry_take(registry, 3) == 99
      ),
    proof: @proof

  law first_key_after_remove,
    expects:
      (
        registry = LynxRegistryFixture.Native.registry_new()
        LynxRegistryFixture.Native.registry_replace(registry, 20, 1)
        LynxRegistryFixture.Native.registry_replace(registry, 3, 99)
        LynxRegistryFixture.Native.registry_take(registry, 3)
        LynxRegistryFixture.Native.registry_first_key(registry) == 20
      ),
    proof: @proof
end
