module

meta import LynxTest.ProofAudit
import LynxTest.EmptyModule
-- These imports intentionally include private proof dependencies for the audit.
import all Lynx.Term.NativeTrace
import all Lynx.Term.NativeSchedule

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeTrace
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeSchedule

-- Empty imported modules have no declarations, while unknown modules still fail.
run_cmd do
  let names ← LynxTest.ProofAudit.moduleDeclarations `LynxTest.EmptyModule
  unless names.isEmpty do throwError "expected an empty test module"
  LynxTest.ProofAudit.checkModule `LynxTest.EmptyModule

/-- error: unknown audit module: LynxTest.MissingAuditModule -/
#guard_msgs in
run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.MissingAuditModule
