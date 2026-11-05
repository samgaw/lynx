module
public import RustWorkspace.RustlerBridge
public import RustWorkspace.Facade.Funs
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std
namespace RustWorkspace.BridgeTests

-- Rustler 0.39 narrows after decoding through its 32-bit NIF API.
theorem signed8_truncates : (Lynx.Rustler.decodeSigned .I8 32 (.integer 128)).map Lynx.Rustler.encodeSigned =
    .ok (.integer (-128)) := by rfl
theorem signed16_truncates : (Lynx.Rustler.decodeSigned .I16 32 (.integer 32768)).map Lynx.Rustler.encodeSigned =
    .ok (.integer (-32768)) := by rfl
theorem unsigned8_truncates : (Lynx.Rustler.decodeUnsigned .U8 32 (.integer 256)).map Lynx.Rustler.encodeUnsigned =
    .ok (.integer 0) := by rfl
theorem unsigned16_truncates : (Lynx.Rustler.decodeUnsigned .U16 32 (.integer 65536)).map Lynx.Rustler.encodeUnsigned =
    .ok (.integer 0) := by rfl

theorem signed64_upper_rejected : Lynx.Rustler.decodeSigned .I64 64 (.integer 9223372036854775808) =
    .error (.error (.atom "badarg")) := by rfl
theorem signed64_lower_rejected : Lynx.Rustler.decodeSigned .I64 64 (.integer (-9223372036854775809)) =
    .error (.error (.atom "badarg")) := by rfl
theorem unsigned64_upper_rejected : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 18446744073709551616) =
    .error (.error (.atom "badarg")) := by rfl
theorem unsigned64_negative_rejected : Lynx.Rustler.decodeUnsigned .U64 64 (.integer (-1)) =
    .error (.error (.atom "badarg")) := by rfl
theorem noninteger_rejected : Lynx.Rustler.decodeSigned .I32 32 (.atom "true") =
    .error (.error (.atom "badarg")) := by rfl

-- An actual Rust arithmetic overflow, rather than a substituted Lean function.
theorem overflow_is_panic : Lynx.Rustler.execute
    (experiment_nif.__2.__INVENTORY.nif_func.wrapper.closure.calculate 4611686018427387904#i64)
    Lynx.Rustler.encodeSigned = .error (.error (.atom "nif_panicked")) := by
  have overflow : (4611686018427387904#i64 * 2#i64 : RustM I64) = RustM.fail .panic := by
    change IScalar.mul _ _ = _
    simp [IScalar.mul, IScalar.tryMk, IScalar.tryMkOpt, IScalar.check_bounds]
  simp [experiment_nif.__2.__INVENTORY.nif_func.wrapper.closure.calculate,
    experiment_nif.experiment_analysis.twice_plus_one, experiment_nif.experiment_core.double,
    overflow, bind_fail]

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.RustlerBridge
  LynxTest.ProofAudit.checkModule `RustWorkspace.BridgeTests
end RustWorkspace.BridgeTests
