module
public import Record.TornSyncFailure

public section

open Lynx

namespace Record.MixedRepairScripts
open NativeFile
open Record.FallibleReopen (openScript)
open Record.TornSyncFailure (choose zeros boot)

@[expose] def closeScript (mask : ByteArray) (closeSucceeds : Bool) : Term :=
  choose "close" closeSucceeds (if closeSucceeds then 0 else 5) mask .nil

@[expose] def syncScript (error : Nat) (syncMask closeMask : ByteArray) (closeSucceeds : Bool) : Term :=
  choose "sync_all" false error syncMask (closeScript closeMask closeSucceeds)

@[expose] def resizeScript (error : Nat) (resizeMask syncMask closeMask : ByteArray)
    (closeSucceeds : Bool) : Term :=
  choose "set_len" true 0 resizeMask (syncScript error syncMask closeMask closeSucceeds)

@[expose] def start (counter : Nat) (left : Bool) (tail : List UInt8)
    (resizeMask syncMask closeMask : ByteArray) (closeSucceeds : Bool) : Environment :=
  let count := 8 + tail.length
  let beforeResize := resizeScript (counter + 1) resizeMask syncMask closeMask closeSucceeds
  let eof := choose "read" true 0 (zeros count) beforeResize
  let steps := choose "seek" true 0 (zeros count)
    ((List.range count).foldr (fun _ => choose "read" true 1 (zeros count)) eof)
  replaceNamespaceScript (openScript true 0 steps .nil) (boot counter left tail 0 0 false)

end Record.MixedRepairScripts
