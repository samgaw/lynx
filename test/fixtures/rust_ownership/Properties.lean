module
public import Ownership.Funs
public section
open Aeneas Aeneas.Std ownership_app
namespace Ownership.Properties

theorem consume_contract {T : Type} (dict : LynxCompilerOwnership.Destruct T) (value : T)
    (finishes : ∃ result, dict.drop_glue value = RustM.ok result) :
    ownership_base.consume dict value = RustM.ok () := by
  obtain ⟨result, finishes⟩ := finishes
  simp [ownership_base.consume, finishes]

theorem run_panics : run (7#u64) = RustM.fail .panic := by
  simp [run, ownership_base.consume, ownership_base.Audit.Insts.LynxCompilerOwnershipDestruct,
    ownership_base.Audit.Insts.LynxCompilerOwnershipDestruct.drop_glue,
    ownership_base.Audit.Insts.LynxCompilerOwnershipDrop.drop]

theorem run_returns (code : U64) (valid : code ≠ 7#u64) : run code = RustM.ok () := by
  unfold run
  apply consume_contract
  refine ⟨{ code := code }, ?_⟩
  simp [ownership_base.Audit.Insts.LynxCompilerOwnershipDestruct,
    ownership_base.Audit.Insts.LynxCompilerOwnershipDestruct.drop_glue,
    ownership_base.Audit.Insts.LynxCompilerOwnershipDrop.drop, valid]
theorem scalar_finishes (code : U64) : run_scalar code = RustM.ok () := by
  simp [run_scalar, ownership_base.consume, U64.Insts.LynxCompilerOwnershipDestruct,
    LynxCompilerOwnership.noop]
end Ownership.Properties
