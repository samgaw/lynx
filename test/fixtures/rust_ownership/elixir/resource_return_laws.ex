defmodule LynxResourceReturnFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law returns_true,
    expects:
      LynxResourceReturnFixture.Native.resource_checked(
        LynxResourceReturnFixture.Native.resource_allocate(true, true),
        true
      ) == true,
    proof: ~LEAN"""
    set_option maxHeartbeats 1000000 in
    simp [Lynx.concurrent_eq_run, «returns_true:ensures/0»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate:execution/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked:execution/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.Rustler.executeNative, Lynx.NativeM.resumeCaptured, Lynx.NativeM.capturePanic,
      Returned.Properties.facade_return, Returned.Properties.facade_checked,
      Returned.Properties.allocate, Returned.Properties.allocations_distinct,
      Lynx.NativeResourceArc.vmCells, Lynx.NativeResourceArc.newCaptured,
      Lynx.NativeResourceArc.new, Lynx.NativeResourceArc.deref, Lynx.NativeResourceArc.release,
      Lynx.NativeResourceArc.takeOwner, Lynx.NativeResourceArc.ownerState,
      Lynx.NativeResourceArc.retiredState, Lynx.NativeResourceArc.ownership,
      Lynx.NativeResourceArc.handleType, Lynx.NativeResourceArc.typeName,
      Lynx.NativeResourceArc.termType, Lynx.NativeResourceArc.referenceLimit,
      Lynx.NativeResourceArc.clone, Lynx.NativeResourceArc.encode_eq,
      Lynx.NativeResourceArc.decode_eq, Lynx.NativeCodec.roundtrip,
      Lynx.NativeM.allocate, Lynx.NativeM.ok, Lynx.NativeM.fail, Lynx.Result.handle,
      Lynx.Result.tryWith, Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason,
      List.filter, List.map, List.eraseDups_cons, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law returns_false,
    expects:
      LynxResourceReturnFixture.Native.resource_checked(
        LynxResourceReturnFixture.Native.resource_allocate(false, true),
        true
      ) == false,
    proof: ~LEAN"""
    set_option maxHeartbeats 1000000 in
    simp [Lynx.concurrent_eq_run, «returns_false:ensures/0»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate:execution/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked:execution/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.Rustler.executeNative, Lynx.NativeM.resumeCaptured, Lynx.NativeM.capturePanic,
      Returned.Properties.facade_return, Returned.Properties.facade_checked,
      Returned.Properties.allocate, Returned.Properties.allocations_distinct,
      Lynx.NativeResourceArc.vmCells, Lynx.NativeResourceArc.newCaptured,
      Lynx.NativeResourceArc.new, Lynx.NativeResourceArc.deref, Lynx.NativeResourceArc.release,
      Lynx.NativeResourceArc.takeOwner, Lynx.NativeResourceArc.ownerState,
      Lynx.NativeResourceArc.retiredState, Lynx.NativeResourceArc.ownership,
      Lynx.NativeResourceArc.handleType, Lynx.NativeResourceArc.typeName,
      Lynx.NativeResourceArc.termType, Lynx.NativeResourceArc.referenceLimit,
      Lynx.NativeResourceArc.clone, Lynx.NativeResourceArc.encode_eq,
      Lynx.NativeResourceArc.decode_eq, Lynx.NativeCodec.roundtrip,
      Lynx.NativeM.allocate, Lynx.NativeM.ok, Lynx.NativeM.fail, Lynx.Result.handle,
      Lynx.Result.tryWith, Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason,
      List.filter, List.map, List.eraseDups_cons, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law rejects_after_creation,
    expects:
      (try do
         LynxResourceReturnFixture.Native.resource_allocate(true, false)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 1000000 in
    simp [Lynx.concurrent_eq_run, «rejects_after_creation:ensures/0»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate:execution/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked:execution/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.Rustler.executeNative, Lynx.NativeM.resumeCaptured, Lynx.NativeM.capturePanic,
      Returned.Properties.facade_return, Returned.Properties.facade_checked,
      Returned.Properties.allocate, Returned.Properties.allocations_distinct,
      Lynx.NativeResourceArc.vmCells, Lynx.NativeResourceArc.newCaptured,
      Lynx.NativeResourceArc.new, Lynx.NativeResourceArc.deref, Lynx.NativeResourceArc.release,
      Lynx.NativeResourceArc.takeOwner, Lynx.NativeResourceArc.ownerState,
      Lynx.NativeResourceArc.retiredState, Lynx.NativeResourceArc.ownership,
      Lynx.NativeResourceArc.handleType, Lynx.NativeResourceArc.typeName,
      Lynx.NativeResourceArc.termType, Lynx.NativeResourceArc.referenceLimit,
      Lynx.NativeResourceArc.clone, Lynx.NativeResourceArc.encode_eq,
      Lynx.NativeResourceArc.decode_eq, Lynx.NativeCodec.roundtrip,
      Lynx.NativeM.allocate, Lynx.NativeM.ok, Lynx.NativeM.fail, Lynx.Result.handle,
      Lynx.Result.tryWith, Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason,
      List.filter, List.map, List.eraseDups_cons, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law rejects_first_argument,
    expects:
      (try do
         LynxResourceReturnFixture.Native.resource_allocate(7, true)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 1000000 in
    simp [Lynx.concurrent_eq_run, «rejects_first_argument:ensures/0»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate:execution/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked:execution/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.Rustler.executeNative, Lynx.NativeM.resumeCaptured, Lynx.NativeM.capturePanic,
      Returned.Properties.facade_return, Returned.Properties.facade_checked,
      Returned.Properties.allocate, Returned.Properties.allocations_distinct,
      Lynx.NativeResourceArc.vmCells, Lynx.NativeResourceArc.newCaptured,
      Lynx.NativeResourceArc.new, Lynx.NativeResourceArc.deref, Lynx.NativeResourceArc.release,
      Lynx.NativeResourceArc.takeOwner, Lynx.NativeResourceArc.ownerState,
      Lynx.NativeResourceArc.retiredState, Lynx.NativeResourceArc.ownership,
      Lynx.NativeResourceArc.handleType, Lynx.NativeResourceArc.typeName,
      Lynx.NativeResourceArc.termType, Lynx.NativeResourceArc.referenceLimit,
      Lynx.NativeResourceArc.clone, Lynx.NativeResourceArc.encode_eq,
      Lynx.NativeResourceArc.decode_eq, Lynx.NativeCodec.roundtrip,
      Lynx.NativeM.allocate, Lynx.NativeM.ok, Lynx.NativeM.fail, Lynx.Result.handle,
      Lynx.Result.tryWith, Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason,
      List.filter, List.map, List.eraseDups_cons, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law rejects_second_argument,
    expects:
      (try do
         LynxResourceReturnFixture.Native.resource_allocate(true, 7)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 1000000 in
    simp [Lynx.concurrent_eq_run, «rejects_second_argument:ensures/0»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate:execution/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked:execution/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.Rustler.executeNative, Lynx.NativeM.resumeCaptured, Lynx.NativeM.capturePanic,
      Returned.Properties.facade_return, Returned.Properties.facade_checked,
      Returned.Properties.allocate, Returned.Properties.allocations_distinct,
      Lynx.NativeResourceArc.vmCells, Lynx.NativeResourceArc.newCaptured,
      Lynx.NativeResourceArc.new, Lynx.NativeResourceArc.deref, Lynx.NativeResourceArc.release,
      Lynx.NativeResourceArc.takeOwner, Lynx.NativeResourceArc.ownerState,
      Lynx.NativeResourceArc.retiredState, Lynx.NativeResourceArc.ownership,
      Lynx.NativeResourceArc.handleType, Lynx.NativeResourceArc.typeName,
      Lynx.NativeResourceArc.termType, Lynx.NativeResourceArc.referenceLimit,
      Lynx.NativeResourceArc.clone, Lynx.NativeResourceArc.encode_eq,
      Lynx.NativeResourceArc.decode_eq, Lynx.NativeCodec.roundtrip,
      Lynx.NativeM.allocate, Lynx.NativeM.ok, Lynx.NativeM.fail, Lynx.Result.handle,
      Lynx.Result.tryWith, Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason,
      List.filter, List.map, List.eraseDups_cons, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law rejects_later_decoding,
    expects:
      (try do
         LynxResourceReturnFixture.Native.resource_checked(
           LynxResourceReturnFixture.Native.resource_allocate(true, true),
           7
         )

         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 1000000 in
    simp [Lynx.concurrent_eq_run, «rejects_later_decoding:ensures/0»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate:execution/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked:execution/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.Rustler.executeNative, Lynx.NativeM.resumeCaptured, Lynx.NativeM.capturePanic,
      Returned.Properties.facade_return, Returned.Properties.facade_checked,
      Returned.Properties.allocate, Returned.Properties.allocations_distinct,
      Lynx.NativeResourceArc.vmCells, Lynx.NativeResourceArc.newCaptured,
      Lynx.NativeResourceArc.new, Lynx.NativeResourceArc.deref, Lynx.NativeResourceArc.release,
      Lynx.NativeResourceArc.takeOwner, Lynx.NativeResourceArc.ownerState,
      Lynx.NativeResourceArc.retiredState, Lynx.NativeResourceArc.ownership,
      Lynx.NativeResourceArc.handleType, Lynx.NativeResourceArc.typeName,
      Lynx.NativeResourceArc.termType, Lynx.NativeResourceArc.referenceLimit,
      Lynx.NativeResourceArc.clone, Lynx.NativeResourceArc.encode_eq,
      Lynx.NativeResourceArc.decode_eq, Lynx.NativeCodec.roundtrip,
      Lynx.NativeM.allocate, Lynx.NativeM.ok, Lynx.NativeM.fail, Lynx.Result.handle,
      Lynx.Result.tryWith, Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason,
      List.filter, List.map, List.eraseDups_cons, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law retains_handle,
    expects:
      (
        resource = LynxResourceReturnFixture.Native.resource_allocate(true, true)

        LynxResourceReturnFixture.Native.resource_checked(resource, true) == true and
          LynxResourceReturnFixture.Native.resource_checked(resource, true) == true
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 1000000 in
    simp [Lynx.concurrent_eq_run, «retains_handle:ensures/0»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate:execution/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked:execution/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.Rustler.executeNative, Lynx.NativeM.resumeCaptured, Lynx.NativeM.capturePanic,
      Returned.Properties.facade_return, Returned.Properties.facade_checked,
      Returned.Properties.allocate, Returned.Properties.allocations_distinct,
      Lynx.NativeResourceArc.vmCells, Lynx.NativeResourceArc.newCaptured,
      Lynx.NativeResourceArc.new, Lynx.NativeResourceArc.deref, Lynx.NativeResourceArc.release,
      Lynx.NativeResourceArc.takeOwner, Lynx.NativeResourceArc.ownerState,
      Lynx.NativeResourceArc.retiredState, Lynx.NativeResourceArc.ownership,
      Lynx.NativeResourceArc.handleType, Lynx.NativeResourceArc.typeName,
      Lynx.NativeResourceArc.termType, Lynx.NativeResourceArc.referenceLimit,
      Lynx.NativeResourceArc.clone, Lynx.NativeResourceArc.encode_eq,
      Lynx.NativeResourceArc.decode_eq, Lynx.NativeCodec.roundtrip,
      Lynx.NativeM.allocate, Lynx.NativeM.ok, Lynx.NativeM.fail, Lynx.Result.handle,
      Lynx.Result.tryWith, Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason,
      List.filter, List.map, List.eraseDups_cons, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law independent_handles,
    expects:
      (
        first = LynxResourceReturnFixture.Native.resource_allocate(true, true)
        second = LynxResourceReturnFixture.Native.resource_allocate(false, true)

        LynxResourceReturnFixture.Native.resource_checked(first, true) == true and
          LynxResourceReturnFixture.Native.resource_checked(second, true) == false
      ),
    proof: ~LEAN"""
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «independent_handles:ensures/0»]
    rw [Elixir.LynxResourceReturnFixture.Native.«resource_allocate/2»]
    simp only [Lynx.Rustler.withResourceTypes, Lynx.Result.nativeModify_bind,
      Lynx.Result.nativeModify_run, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.Result.ok_bind, List.nil_append, List.eraseDups_cons, List.eraseDups_nil]
    rw [Elixir.LynxResourceReturnFixture.Native.«resource_allocate:execution/2»]
    change (Lynx.Result.run _ Returned.Properties.initial schedule).1 = _
    rw [Returned.Properties.encoded_next]
    simp only [Bool.true_eq, ite_true]
    simp [Returned.Properties.pinned, Returned.Properties.initial, Lynx.concurrent_eq_run, «independent_handles:ensures/0»,
        Elixir.LynxResourceReturnFixture.Native.«resource_allocate/2»,
        Elixir.LynxResourceReturnFixture.Native.«resource_allocate:execution/2»,
        Elixir.LynxResourceReturnFixture.Native.«resource_checked/2»,
        Elixir.LynxResourceReturnFixture.Native.«resource_checked:execution/2»,
        Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
        Lynx.Rustler.executeNative, Lynx.NativeM.resumeCaptured, Lynx.NativeM.capturePanic,
        Returned.Properties.facade_return, Returned.Properties.facade_checked,
        Returned.Properties.allocate, Returned.Properties.allocations_distinct, Returned.Properties.resource_reference_eq,
        Lynx.NativeResourceArc.vmCells, Lynx.NativeResourceArc.newCaptured,
        Lynx.NativeResourceArc.new, Lynx.NativeResourceArc.deref, Lynx.NativeResourceArc.release,
        Lynx.NativeResourceArc.takeOwner, Lynx.NativeResourceArc.ownerState,
        Lynx.NativeResourceArc.retiredState, Lynx.NativeResourceArc.ownership,
        Lynx.NativeResourceArc.handleType, Lynx.NativeResourceArc.typeName,
        Lynx.NativeResourceArc.termType, Lynx.NativeResourceArc.referenceLimit,
        Lynx.NativeResourceArc.clone, Lynx.NativeResourceArc.encode_eq,
        Lynx.NativeResourceArc.decode_eq, Lynx.NativeCodec.roundtrip,
        Lynx.NativeM.allocate, Lynx.NativeM.ok, Lynx.NativeM.fail, Lynx.Result.handle,
         Lynx.Exception.classTerm, Lynx.Exception.reason,
        List.filter, List.map, List.eraseDups_cons, Lynx.Rustler.encodeBool,
        Erlang.erlang.«==/2»]
    """

  law preserves_prior_handle,
    expects:
      (
        first = LynxResourceReturnFixture.Native.resource_allocate(true, true)

        try do
          LynxResourceReturnFixture.Native.resource_allocate(false, false)
          false
        catch
          :error, :nif_panicked ->
            LynxResourceReturnFixture.Native.resource_checked(first, true) == true
        end
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 1000000 in
    simp [Lynx.concurrent_eq_run, «preserves_prior_handle:ensures/0»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_allocate:execution/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked/2»,
      Elixir.LynxResourceReturnFixture.Native.«resource_checked:execution/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.Rustler.executeNative, Lynx.NativeM.resumeCaptured, Lynx.NativeM.capturePanic,
      Returned.Properties.facade_return, Returned.Properties.facade_checked,
      Returned.Properties.allocate, Returned.Properties.allocations_distinct, Returned.Properties.resource_reference_eq,
      Lynx.NativeResourceArc.vmCells, Lynx.NativeResourceArc.newCaptured,
      Lynx.NativeResourceArc.new, Lynx.NativeResourceArc.deref, Lynx.NativeResourceArc.release,
      Lynx.NativeResourceArc.takeOwner, Lynx.NativeResourceArc.ownerState,
      Lynx.NativeResourceArc.retiredState, Lynx.NativeResourceArc.ownership,
      Lynx.NativeResourceArc.handleType, Lynx.NativeResourceArc.typeName,
      Lynx.NativeResourceArc.termType, Lynx.NativeResourceArc.referenceLimit,
      Lynx.NativeResourceArc.clone, Lynx.NativeResourceArc.encode_eq,
      Lynx.NativeResourceArc.decode_eq, Lynx.NativeCodec.roundtrip,
      Lynx.NativeM.allocate, Lynx.NativeM.ok, Lynx.NativeM.fail, Lynx.Result.handle,
      Lynx.Result.tryWith, Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason,
      List.filter, List.map, List.eraseDups_cons, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """
end
