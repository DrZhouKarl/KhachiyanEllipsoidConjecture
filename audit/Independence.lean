import Khachiyan.Resolvent

/-!
Standalone complete D01/A01/M04R audit. Inspect the actual loaded module environment, rather
than relying on the root's common foundational-axiom list for independence.
Only M01/M02, ResolventScalar, and Resolvent may be project imports.
-/

run_cmd do
  let env ← Lean.getEnv
  let allowed : List Lean.Name :=
    [`Khachiyan.Basic, `Khachiyan.MatrixBridge, `Khachiyan.MatrixPowers,
      `Khachiyan.PowerIntegral, `Khachiyan.ResolventScalar, `Khachiyan.Resolvent]
  for mod in env.header.moduleNames do
    if (`Khachiyan).isPrefixOf mod then
      unless allowed.contains mod do
        throwError "Unexpected project dependency: {mod}"
      Lean.logInfo m!"Allowed project import: {mod}"
  Lean.logInfo "PASS: the actual import closure excludes the M03/M04 route."

-- Traverse types and proof terms, including opaque theorem values.
run_cmd do
  let env ← Lean.getEnv
  let mut pending :=
    [`Khachiyan.ResolventScalar.logDiff,
      `Khachiyan.ResolventScalar.log_sub_log_le,
      `Khachiyan.ResolventScalar.abs_log_sub_log_le,
      `Khachiyan.ResolventScalar.abs_logDiff_le,
      `Khachiyan.ResolventScalar.powerKernel,
      `Khachiyan.ResolventScalar.powerKernel_eq,
      `Khachiyan.ResolventScalar.integrable_powerKernel,
      `Khachiyan.ResolventScalar.power_eq_integral_powerKernel,
      `Khachiyan.ResolventScalar.integrable_weighted_inv,
      `Khachiyan.ResolventScalar.integrable_weighted_logDiff,
      `Khachiyan.ResolventScalar.boundary_zero,
      `Khachiyan.ResolventScalar.abs_logDiff_le_div,
      `Khachiyan.ResolventScalar.boundary_infty,
      `Khachiyan.ResolventScalar.hasDerivAt_logDiff,
      `Khachiyan.ResolventScalar.weighted_logDiff_derivative,
      `Khachiyan.ResolventScalar.integrable_weighted_logDiff_derivative,
      `Khachiyan.ResolventScalar.integral_logDiff,
      `Khachiyan.ResolventScalar.rpow_sub_eq_integral_logDiff,
      `Khachiyan.ResolventScalar.logDiff_add,
      `Khachiyan.ResolventScalar.integrable_weighted_log_one_add_div,
      `Khachiyan.ResolventScalar.rpow_add_sub_eq_integral_log,
      `Khachiyan.Resolvent.det_add_smul_outer,
      `Khachiyan.Resolvent.one_add_mul_inv_quadratic_pos,
      `Khachiyan.Resolvent.log_det_add_smul_outer,
      `Khachiyan.Resolvent.posDef_add_smul_one,
      `Khachiyan.Resolvent.inner_action_left,
      `Khachiyan.Resolvent.inverse_scaled_sq_quadratic,
      `Khachiyan.Resolvent.cfc_shift,
      `Khachiyan.Resolvent.log_det_shift_eq_sum,
      `Khachiyan.Resolvent.logDetDiff,
      `Khachiyan.Resolvent.logDetDiff_eq_sum,
      `Khachiyan.Resolvent.integrable_weighted_logDetDiff,
      `Khachiyan.Resolvent.trace_rpow_sub_eq_integral_logDetDiff,
      `Khachiyan.Resolvent.trace_inv_shift_eq_sum,
      `Khachiyan.Resolvent.hasDerivAt_logDetDiff,
      `Khachiyan.Resolvent.logDetDiff_boundary_zero,
      `Khachiyan.Resolvent.logDetDiff_boundary_infty,
      `Khachiyan.Resolvent.posDef_add_smul_outer,
      `Khachiyan.Resolvent.logDetDiff_rank_one,
      `Khachiyan.Resolvent.integrable_rank_one_log_kernel,
      `Khachiyan.Resolvent.trace_rpow_rank_one_eq_integral_log,
      `Khachiyan.Resolvent.resolvent_quadratic_lower_bound,
      `Khachiyan.Resolvent.trace_increment_lower_bound]
  let mut visited : Lean.NameSet := {}
  let mut projectDeps : Lean.NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail
    if visited.contains name then
      continue
    visited := visited.insert name
    let some info := env.find? name
      | throwError "Missing declaration in dependency traversal: {name}"
    if (`Khachiyan).isPrefixOf name then
      projectDeps := projectDeps.insert name
      let some idx := env.getModuleIdxFor? name
        | throwError "Missing module for project declaration: {name}"
      let mod := env.header.moduleNames[idx]!
      unless ([`Khachiyan.Basic, `Khachiyan.MatrixBridge, `Khachiyan.MatrixPowers,
        `Khachiyan.PowerIntegral, `Khachiyan.ResolventScalar, `Khachiyan.Resolvent] : List Lean.Name).contains mod do
        throwError "Unexpected project proof dependency: {name} in {mod}"
    for dep in info.getUsedConstantsAsSet.toArray do
      pending := dep :: pending
  for name in projectDeps.toArray do
    Lean.logInfo m!"Project declaration in proof closure: {name}"
  Lean.logInfo "PASS: all transitive project proof dependencies belong to M01/M02 or the independent resolvent modules."

#check @Khachiyan.ResolventScalar.abs_logDiff_le
#check @Khachiyan.ResolventScalar.integrable_weighted_logDiff
#check @Khachiyan.ResolventScalar.rpow_add_sub_eq_integral_log
#check @Khachiyan.Resolvent.hasDerivAt_logDetDiff
#check @Khachiyan.Resolvent.logDetDiff_boundary_zero
#check @Khachiyan.Resolvent.logDetDiff_boundary_infty
#check @Khachiyan.Resolvent.resolvent_quadratic_lower_bound
#check @Khachiyan.Resolvent.integrable_rank_one_log_kernel
#check @Khachiyan.Resolvent.trace_rpow_rank_one_eq_integral_log
#check @Khachiyan.Resolvent.trace_increment_lower_bound

#print axioms Khachiyan.ResolventScalar.logDiff
#print axioms Khachiyan.ResolventScalar.log_sub_log_le
#print axioms Khachiyan.ResolventScalar.abs_log_sub_log_le
#print axioms Khachiyan.ResolventScalar.abs_logDiff_le
#print axioms Khachiyan.ResolventScalar.powerKernel
#print axioms Khachiyan.ResolventScalar.powerKernel_eq
#print axioms Khachiyan.ResolventScalar.integrable_powerKernel
#print axioms Khachiyan.ResolventScalar.power_eq_integral_powerKernel
#print axioms Khachiyan.ResolventScalar.integrable_weighted_inv
#print axioms Khachiyan.ResolventScalar.integrable_weighted_logDiff
#print axioms Khachiyan.ResolventScalar.boundary_zero
#print axioms Khachiyan.ResolventScalar.abs_logDiff_le_div
#print axioms Khachiyan.ResolventScalar.boundary_infty
#print axioms Khachiyan.ResolventScalar.hasDerivAt_logDiff
#print axioms Khachiyan.ResolventScalar.weighted_logDiff_derivative
#print axioms Khachiyan.ResolventScalar.integrable_weighted_logDiff_derivative
#print axioms Khachiyan.ResolventScalar.integral_logDiff
#print axioms Khachiyan.ResolventScalar.rpow_sub_eq_integral_logDiff
#print axioms Khachiyan.ResolventScalar.logDiff_add
#print axioms Khachiyan.ResolventScalar.integrable_weighted_log_one_add_div
#print axioms Khachiyan.ResolventScalar.rpow_add_sub_eq_integral_log
#print axioms Khachiyan.Resolvent.det_add_smul_outer
#print axioms Khachiyan.Resolvent.one_add_mul_inv_quadratic_pos
#print axioms Khachiyan.Resolvent.log_det_add_smul_outer
#print axioms Khachiyan.Resolvent.posDef_add_smul_one
#print axioms Khachiyan.Resolvent.inner_action_left
#print axioms Khachiyan.Resolvent.inverse_scaled_sq_quadratic
#print axioms Khachiyan.Resolvent.cfc_shift
#print axioms Khachiyan.Resolvent.log_det_shift_eq_sum
#print axioms Khachiyan.Resolvent.logDetDiff
#print axioms Khachiyan.Resolvent.logDetDiff_eq_sum
#print axioms Khachiyan.Resolvent.integrable_weighted_logDetDiff
#print axioms Khachiyan.Resolvent.trace_rpow_sub_eq_integral_logDetDiff
#print axioms Khachiyan.Resolvent.trace_inv_shift_eq_sum
#print axioms Khachiyan.Resolvent.hasDerivAt_logDetDiff
#print axioms Khachiyan.Resolvent.logDetDiff_boundary_zero
#print axioms Khachiyan.Resolvent.logDetDiff_boundary_infty
#print axioms Khachiyan.Resolvent.posDef_add_smul_outer
#print axioms Khachiyan.Resolvent.logDetDiff_rank_one
#print axioms Khachiyan.Resolvent.integrable_rank_one_log_kernel
#print axioms Khachiyan.Resolvent.trace_rpow_rank_one_eq_integral_log
#print axioms Khachiyan.Resolvent.resolvent_quadratic_lower_bound
#print axioms Khachiyan.Resolvent.trace_increment_lower_bound
