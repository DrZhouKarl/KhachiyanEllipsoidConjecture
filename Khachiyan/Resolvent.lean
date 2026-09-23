import Khachiyan.MatrixPowers
import Khachiyan.PowerIntegral
import Khachiyan.ResolventScalar
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Independent resolvent proof of the rank-one trace estimate

This module completes D01/A01/M04R of `formalization_plan.md`, corresponding to
the alternative proof of M04 in Section 8 of `proof.md`. The scalar integration
by parts in `ResolventScalar` is lifted through two fixed spectral decompositions.
Both endpoint limits, the log-resolvent integral, and the resolvent quadratic
lower bound are proved. Only M01/M02 and mathlib are used; the project M03 trace
derivative and its M04 rank-one trace estimate are not dependencies.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix MeasureTheory Set Filter
open scoped Topology

namespace Khachiyan.Resolvent

variable {n : ℕ}

/-- The rank-one determinant identity from Section 8 of `proof.md`.
The base matrix need only be invertible, and the scalar may have either sign. -/
theorem det_add_smul_outer {Q : MatR n} (hQ : IsUnit Q.det) (b : V n) (t : ℝ) :
    (Q + t • outer b).det =
      Q.det * (1 + t * ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ b⟫) := by
  rw [outer_eq_vecMulVec, ← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq Unit,
    Matrix.det_add_replicateCol_mul_replicateRow hQ,
    Matrix.mul_assoc, ← Matrix.replicateCol_mulVec]
  simp [Matrix.det_unique, inner_matrix_action, Matrix.mulVec_smul, smul_eq_mul]

/-- The logarithm argument in the rank-one identity is strictly positive,
including a zero vector or a zero perturbation parameter. -/
theorem one_add_mul_inv_quadratic_pos {Q : MatR n} (hQ : Q.PosDef)
    (b : V n) {t : ℝ} (ht : 0 ≤ t) :
    0 < 1 + t * ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ b⟫ := by
  have hquad : 0 ≤ ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ b⟫ := by
    rw [inner_matrix_action]
    simpa only [star_trivial] using hQ.inv.posSemidef.dotProduct_mulVec_nonneg b.ofLp
  exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ht hquad)

/-- The logarithmic rank-one determinant identity from Section 8 of `proof.md`.
Positive definiteness and a nonnegative parameter ensure positive determinants
and a positive logarithm argument; neither is assumed as an extra hypothesis. -/
theorem log_det_add_smul_outer {Q : MatR n} (hQ : Q.PosDef)
    (b : V n) {t : ℝ} (ht : 0 ≤ t) :
    Real.log (Q + t • outer b).det - Real.log Q.det =
      Real.log (1 + t * ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ b⟫) := by
  rw [det_add_smul_outer (isUnit_iff_ne_zero.mpr hQ.det_pos.ne') b t,
    Real.log_mul hQ.det_pos.ne' (one_add_mul_inv_quadratic_pos hQ b ht).ne']
  ring

/-- Positive shifts preserve positive definiteness, including the zero shift. -/
theorem posDef_add_smul_one {Q : MatR n} (hQ : Q.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    (Q + s • (1 : MatR n)).PosDef :=
  hQ.add_posSemidef (Matrix.PosSemidef.one.smul hs)

/-- Move a real symmetric matrix across the Euclidean inner product. -/
theorem inner_action_left {A : MatR n} (hA : A.IsHermitian) (u v : V n) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A u, v⟫ =
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) A v⟫ := by
  rw [inner_eq_dotProduct, matrix_action_ofLp, inner_matrix_action]
  have hAt : Aᵀ = A := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, hAt]

/-- Exact cancellation of a scaled squared shape in a quadratic form. -/
theorem inverse_scaled_sq_quadratic {A : MatR n} (hA : A.PosDef)
    {c : ℝ} (hc : c ≠ 0) (u : V n) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A u,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (c • A ^ 2)⁻¹
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)⟫ = c⁻¹ * ‖u‖ ^ 2 := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hi : (c • A ^ 2)⁻¹ = c⁻¹ • (A⁻¹ * A⁻¹) := by
    apply Matrix.inv_eq_right_inv
    simp [pow_two, smul_smul, mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left A _ hu, Matrix.mul_nonsing_inv A hu, hc]
  have he : A * (c⁻¹ • (A⁻¹ * A⁻¹)) * A = c⁻¹ • (1 : MatR n) := by
    simp [mul_assoc,
      Matrix.mul_nonsing_inv A hu, Matrix.nonsing_inv_mul A hu]
  rw [inner_action_left hA.isHermitian, inner_matrix_action,
    matrix_action_ofLp, matrix_action_ofLp, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hi, he]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    ← inner_eq_dotProduct, real_inner_self_eq_norm_sq]
  rfl

/-- A shifted matrix is a scalar function of the fixed base matrix. -/
theorem cfc_shift {Q : MatR n} (hQ : Q.IsHermitian) (s : ℝ) :
    cfc (fun x : ℝ => s + x) Q = Q + s • (1 : MatR n) := by
  rw [cfc_const_add s (fun x : ℝ => x) Q (by fun_prop) hQ.isSelfAdjoint,
    cfc_id' ℝ Q hQ.isSelfAdjoint, Algebra.algebraMap_eq_smul_one, add_comm]

/-- Shifted log determinants in a fixed eigenbasis. -/
theorem log_det_shift_eq_sum {Q : MatR n} (hQ : Q.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    Real.log (Q + s • (1 : MatR n)).det =
      ∑ i, Real.log (s + hQ.isHermitian.eigenvalues i) := by
  rw [← cfc_shift hQ.isHermitian s, Spectral.det_cfc hQ.isHermitian]
  exact Real.log_prod (fun i _ => (add_pos_of_nonneg_of_pos hs (hQ.eigenvalues_pos i)).ne')

/-- The logarithmic determinant difference used in Section 8. -/
def logDetDiff (N M : MatR n) (s : ℝ) : ℝ :=
  Real.log (N + s • (1 : MatR n)).det - Real.log (M + s • (1 : MatR n)).det

theorem logDetDiff_eq_sum {N M : MatR n} (hN : N.PosDef) (hM : M.PosDef)
    {s : ℝ} (hs : 0 ≤ s) :
    logDetDiff N M s = ∑ i, ResolventScalar.logDiff
      (hN.isHermitian.eigenvalues i) (hM.isHermitian.eigenvalues i) s := by
  simp only [logDetDiff, log_det_shift_eq_sum hN hs, log_det_shift_eq_sum hM hs,
    ResolventScalar.logDiff, Finset.sum_sub_distrib]

/-- Absolute integrability of the weighted log determinant difference. -/
theorem integrable_weighted_logDetDiff {N M : MatR n} (hN : N.PosDef) (hM : M.PosDef)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun s => s ^ (p - 1) * logDetDiff N M s) (Ioi 0) := by
  have h : IntegrableOn (fun s => ∑ i, s ^ (p - 1) * ResolventScalar.logDiff
      (hN.isHermitian.eigenvalues i) (hM.isHermitian.eigenvalues i) s) (Ioi 0) :=
    integrable_finsetSum Finset.univ (fun i _ =>
      ResolventScalar.integrable_weighted_logDiff hp (hN.eigenvalues_pos i) (hM.eigenvalues_pos i))
  apply h.congr_fun _ measurableSet_Ioi
  intro s hs
  dsimp only
  rw [logDetDiff_eq_sum hN hM hs.le, Finset.mul_sum]

/-- The independent logarithmic trace representation, obtained by integration
by parts in the two fixed eigenbases. There is no varying spectral basis. -/
theorem trace_rpow_sub_eq_integral_logDetDiff {N M : MatR n}
    (hN : N.PosDef) (hM : M.PosDef) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    (CFC.rpow N p).trace - (CFC.rpow M p).trace =
      p * PowerIntegral.powerNormalization p *
        ∫ s in Ioi 0, s ^ (p - 1) * logDetDiff N M s := by
  have hi : (∫ s in Ioi 0, s ^ (p - 1) * logDetDiff N M s) =
      ∑ i, ∫ s in Ioi 0, s ^ (p - 1) * ResolventScalar.logDiff
        (hN.isHermitian.eigenvalues i) (hM.isHermitian.eigenvalues i) s := by
    calc
      _ = ∫ s in Ioi 0, ∑ i, s ^ (p - 1) * ResolventScalar.logDiff
          (hN.isHermitian.eigenvalues i) (hM.isHermitian.eigenvalues i) s := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro s hs
        dsimp only
        rw [logDetDiff_eq_sum hN hM hs.le, Finset.mul_sum]
      _ = _ := integral_finsetSum Finset.univ (fun i _ =>
        ResolventScalar.integrable_weighted_logDiff hp (hN.eigenvalues_pos i) (hM.eigenvalues_pos i))
  rw [hi, Finset.mul_sum, Spectral.trace_rpow hN p, Spectral.trace_rpow hM p,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact ResolventScalar.rpow_sub_eq_integral_logDiff hp (hN.eigenvalues_pos i) (hM.eigenvalues_pos i)

/-- The trace of the shifted inverse in the fixed eigenbasis. -/
theorem trace_inv_shift_eq_sum {Q : MatR n} (hQ : Q.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    (Q + s • (1 : MatR n))⁻¹.trace = ∑ i, (s + hQ.isHermitian.eigenvalues i)⁻¹ := by
  have hnz : ∀ x ∈ spectrum ℝ Q, s + x ≠ 0 := by
    intro x hx
    rw [hQ.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (add_pos_of_nonneg_of_pos hs (hQ.eigenvalues_pos i)).ne'
  have hi := cfc_inv (fun x : ℝ => s + x) Q hnz (by fun_prop) hQ.isHermitian.isSelfAdjoint
  rw [cfc_shift hQ.isHermitian s, ← Matrix.nonsing_inv_eq_ringInverse] at hi
  rw [← hi, Spectral.trace_cfc hQ.isHermitian]

/-- Differentiate the shifted log determinants in their two fixed eigenbases. -/
theorem hasDerivAt_logDetDiff {N M : MatR n} (hN : N.PosDef) (hM : M.PosDef)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (logDetDiff N M)
      ((N + s • (1 : MatR n))⁻¹.trace - (M + s • (1 : MatR n))⁻¹.trace) s := by
  rw [trace_inv_shift_eq_sum hN hs.le, trace_inv_shift_eq_sum hM hs.le,
    ← Finset.sum_sub_distrib]
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    ResolventScalar.hasDerivAt_logDiff (hN.eigenvalues_pos i) (hM.eigenvalues_pos i) hs.le)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with z hz
  simpa only [Finset.sum_apply] using logDetDiff_eq_sum hN hM hz.le

/-- The matrix boundary term at zero follows from the finite scalar boundary terms. -/
theorem logDetDiff_boundary_zero {N M : MatR n} (hN : N.PosDef) (hM : M.PosDef)
    {p : ℝ} (hp : 0 < p) :
    Tendsto (fun s => s ^ p * logDetDiff N M s) (𝓝[>] 0) (𝓝 0) := by
  have ht := tendsto_finsetSum Finset.univ (fun i _ =>
    ResolventScalar.boundary_zero hp (hN.eigenvalues_pos i) (hM.eigenvalues_pos i))
  simp only [Finset.sum_const_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [logDetDiff_eq_sum hN hM hs.le, Finset.mul_sum]

/-- The matrix boundary term at infinity follows from the finite inverse-linear bounds. -/
theorem logDetDiff_boundary_infty {N M : MatR n} (hN : N.PosDef) (hM : M.PosDef)
    {p : ℝ} (hp : p < 1) :
    Tendsto (fun s => s ^ p * logDetDiff N M s) atTop (𝓝 0) := by
  have ht := tendsto_finsetSum Finset.univ (fun i _ =>
    ResolventScalar.boundary_infty hp (hN.eigenvalues_pos i) (hM.eigenvalues_pos i))
  simp only [Finset.sum_const_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [logDetDiff_eq_sum hN hM hs.le, Finset.mul_sum]

/-- Nonnegative rank-one perturbations preserve positive definiteness. -/
theorem posDef_add_smul_outer {M : MatR n} (hM : M.PosDef) (b : V n)
    {t : ℝ} (ht : 0 ≤ t) : (M + t • outer b).PosDef :=
  hM.add_posSemidef ((outer_posSemidef b).smul ht)

/-- The shifted rank-one logarithmic identity, in the notation of A01. -/
theorem logDetDiff_rank_one {M : MatR n} (hM : M.PosDef) (b : V n)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    logDetDiff (M + t • outer b) M s =
      Real.log (1 + t * ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) (M + s • (1 : MatR n))⁻¹ b⟫) := by
  unfold logDetDiff
  rw [show M + t • outer b + s • (1 : MatR n) =
    (M + s • (1 : MatR n)) + t • outer b by abel]
  exact log_det_add_smul_outer (posDef_add_smul_one hM hs) b ht

/-- Absolute integrability of the actual rank-one log-resolvent kernel. -/
theorem integrable_rank_one_log_kernel {M : MatR n} (hM : M.PosDef) (b : V n)
    {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    IntegrableOn (fun s => s ^ (p - 1) *
      Real.log (1 + t * ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) (M + s • (1 : MatR n))⁻¹ b⟫))
      (Ioi 0) := by
  apply (integrable_weighted_logDetDiff (posDef_add_smul_outer hM b ht) hM hp).congr_fun
    _ measurableSet_Ioi
  intro s hs
  dsimp only
  rw [logDetDiff_rank_one hM b ht hs.le]

/-- A01: the independent rank-one log-resolvent integral identity, with the
exact reciprocal normalization integral from M02.1. -/
theorem trace_rpow_rank_one_eq_integral_log {M : MatR n} (hM : M.PosDef) (b : V n)
    {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    (CFC.rpow (M + t • outer b) p).trace - (CFC.rpow M p).trace =
      p * PowerIntegral.powerNormalization p *
        ∫ s in Ioi 0, s ^ (p - 1) *
          Real.log (1 + t * ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) (M + s • (1 : MatR n))⁻¹ b⟫) := by
  rw [trace_rpow_sub_eq_integral_logDetDiff (posDef_add_smul_outer hM b ht) hM hp]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only
  rw [logDetDiff_rank_one hM b ht hs.le]

section PositiveDimension

variable [NeZero n]

/-- The resolvent quadratic lower bound in Section 8 of `proof.md`.
The direction is arbitrary and no commutativity between `A` and `M` is needed. -/
theorem resolvent_quadratic_lower_bound {A M : MatR n} (hA : A.PosDef)
    (hM : M.PosDef) {m : ℝ} (hm : 0 < m)
    (hMA : M ≤ (m / Spectral.minEigenvalue hA.isHermitian ^ 2) • A ^ 2)
    (u : V n) (hu : ‖u‖ = 1) {s : ℝ} (hs : 0 < s) :
    Spectral.minEigenvalue hA.isHermitian ^ 2 / (m + s) ≤
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A u,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (M + s • (1 : MatR n))⁻¹
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)⟫ := by
  let α := Spectral.minEigenvalue hA.isHermitian
  have ha : 0 < α := Spectral.minEigenvalue_pos hA
  have ha2 : 0 < α ^ 2 := sq_pos_of_pos ha
  have hsq : α ^ 2 • (1 : MatR n) ≤ A ^ 2 := by
    have h := Spectral.minEigenvalue_rpow_smul_one_le hA (p := (2 : ℕ)) (by norm_num)
    rw [show CFC.rpow A (2 : ℕ) = A ^ 2 from CFC.rpow_natCast A 2 hA.posSemidef.nonneg,
      Real.rpow_natCast] at h
    exact h
  have hsbound : s • (1 : MatR n) ≤ (s / α ^ 2) • A ^ 2 := by
    calc
      _ = (s / α ^ 2) • (α ^ 2 • (1 : MatR n)) := by
        rw [smul_smul, div_mul_cancel₀ _ ha2.ne']
      _ ≤ _ := smul_le_smul_of_nonneg_left hsq (div_nonneg hs.le ha2.le)
  have hbound : M + s • (1 : MatR n) ≤ ((m + s) / α ^ 2) • A ^ 2 := by
    calc
      _ ≤ (m / α ^ 2) • A ^ 2 + (s / α ^ 2) • A ^ 2 := add_le_add hMA hsbound
      _ = _ := by rw [← add_smul, ← add_div]
  have hq := Spectral.quadratic_mono
    (MatrixPowers.inv_antitone (posDef_add_smul_one hM hs.le) hbound)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)
  rw [inverse_scaled_sq_quadratic hA (div_pos (add_pos hm hs) ha2).ne' u] at hq
  simpa only [hu, one_pow, mul_one, inv_div] using hq

/-- M04R: an independent second proof of the full rank-one trace lower bound.
This proof uses the log-resolvent integral, not the M03 trace derivative or the
existing M04 theorem. It includes all real exponents in `(0,1)`, all `t ≥ 0`,
all unit directions, and general noncommuting positive definite matrices. -/
theorem trace_increment_lower_bound {A M : MatR n} (hA : A.PosDef) (hM : M.PosDef)
    (u : V n) (hu : ‖u‖ = 1) {m p t : ℝ} (hm : 0 < m)
    (hMA : M ≤ (m / Spectral.minEigenvalue hA.isHermitian ^ 2) • A ^ 2)
    (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    (m + t * Spectral.minEigenvalue hA.isHermitian ^ 2) ^ p - m ^ p ≤
      (CFC.rpow (M + t • outer (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)) p).trace -
        (CFC.rpow M p).trace := by
  have hd : 0 ≤ t * Spectral.minEigenvalue hA.isHermitian ^ 2 := mul_nonneg ht (sq_nonneg _)
  rw [ResolventScalar.rpow_add_sub_eq_integral_log hp hm hd,
    trace_rpow_rank_one_eq_integral_log hM _ hp ht]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg hp.1.le (PowerIntegral.powerNormalization_pos hp).le)
  apply setIntegral_mono_on
    (ResolventScalar.integrable_weighted_log_one_add_div hp hm hd)
    (integrable_rank_one_log_kernel hM _ hp ht) measurableSet_Ioi
  intro s hs
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hs.le _)
  apply Real.log_le_log
    (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hd (add_pos hm hs).le))
  have hq := mul_le_mul_of_nonneg_left
    (resolvent_quadratic_lower_bound hA hM hm hMA u hu hs) ht
  rw [← mul_div_assoc] at hq
  linarith

end PositiveDimension

end Khachiyan.Resolvent
