import Khachiyan

/-!
Compare the two final theorem types in the full environment, aligning the
order of the implicit matrix and `NeZero` binders. This file is only a statement
audit; the separate independence audit imports Resolvent alone.
-/

run_cmd Lean.Elab.Command.liftTermElabM do
  let first ← Lean.getConstInfo `Khachiyan.RankOne.trace_increment_lower_bound
  Lean.Meta.forallTelescope first.type fun args conclusion => do
    let reordered := #[args[0]!, args[3]!, args[1]!, args[2]!] ++ args.extract 4 args.size
    let proof := Lean.mkAppN (Lean.mkConst `Khachiyan.Resolvent.trace_increment_lower_bound) reordered
    Lean.Meta.check proof
    let secondType ← Lean.Meta.inferType proof
    unless ← Lean.Meta.isDefEq conclusion secondType do
      throwError "The primary M04 and independent M04R hypotheses or conclusions differ."
  Lean.logInfo "PASS: primary M04 and independent M04R have identical hypotheses and conclusions after aligning implicit binders."

#check @Khachiyan.RankOne.trace_increment_lower_bound
#check @Khachiyan.Resolvent.trace_increment_lower_bound
#print axioms Khachiyan.Resolvent.trace_increment_lower_bound
