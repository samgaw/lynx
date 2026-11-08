module

meta import LynxTest.ProofAudit
-- These imports intentionally include private proof dependencies for the audit.
import all Lynx.Term.NativeTrace
import all Lynx.Term.NativeSchedule

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeTrace
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeSchedule
