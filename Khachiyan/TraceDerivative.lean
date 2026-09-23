import Khachiyan.MatrixPowers
import Khachiyan.PowerIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Trace differentiation along self-adjoint directions

This module develops M03 of `proof.md` and `formalization_plan.md`. Differentiation
is along a real parameter with a self-adjoint direction. It does not assert a
derivative of the total CFC expression in arbitrary matrix directions.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator Topology
open Matrix MeasureTheory Set Filter

namespace Khachiyan.TraceDerivative

variable {n : ℕ} {X H A : MatR n}

def line (X H : MatR n) (t : ℝ) : MatR n := X + t • H

def kernelDeriv (p s : ℝ) (Y H : MatR n) : MatR n :=
  s ^ p • ((Y + s • (1 : MatR n))⁻¹ * H * (Y + s • (1 : MatR n))⁻¹)

theorem hermitian_lower_of_norm_le (hH : H.IsHermitian) {c : ℝ} (hc : ‖H‖ ≤ c) :
    (-c) • (1 : MatR n) ≤ H := by
  have hb : ∀ x ∈ spectrum ℝ H, -c ≤ x := by
    intro x hx
    have hn := IsometricContinuousFunctionalCalculus.norm_spectrum_le H hx hH.isSelfAdjoint
    exact (abs_le.mp (hn.trans hc)).1
  have h := (algebraMap_le_iff_le_spectrum (R := ℝ) (a := H) hH.isSelfAdjoint).mpr hb
  simpa only [Algebra.algebraMap_eq_smul_one] using h

theorem norm_inv_le (hA : A.PosDef) {d : ℝ} (hd : 0 < d) (hlo : d • (1 : MatR n) ≤ A) :
    ‖A⁻¹‖ ≤ d⁻¹ := by
  have hl : ∀ x ∈ spectrum ℝ A, d ≤ x := by
    apply (algebraMap_le_iff_le_spectrum (R := ℝ) (a := A) hA.isHermitian.isSelfAdjoint).mp
    simpa only [Algebra.algebraMap_eq_smul_one] using hlo
  rw [MatrixPowers.inv_eq_rpow_neg_one hA, Spectral.rpow_eq_cfc hA (-1 : ℝ)]
  apply norm_cfc_le (by positivity)
  intro x hx
  have hxpos := hd.trans_le (hl x hx)
  rw [Real.rpow_neg_one, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
  simpa only [one_div] using one_div_le_one_div_of_le hd (hl x hx)

theorem line_isHermitian (hX : X.IsHermitian) (hH : H.IsHermitian) (t : ℝ) :
    (line X H t).IsHermitian := by
  change star (X + t • H) = X + t • H
  simp [show star X = X from hX, show star H = H from hH]

theorem exists_uniform_lower [NeZero n] (hX : X.PosDef) (hH : H.IsHermitian) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ t : ℝ in 𝓝 0,
      (line X H t).PosDef ∧ d • (1 : MatR n) ≤ line X H t := by
  let d := Spectral.minEigenvalue hX.isHermitian / 2
  have hd : 0 < d := div_pos (Spectral.minEigenvalue_pos hX) (by norm_num)
  refine ⟨d, hd, ?_⟩
  have hcont : ContinuousAt (fun t : ℝ => ‖t • H‖) 0 := by fun_prop
  have ht : ∀ᶠ t : ℝ in 𝓝 0, ‖t • H‖ < d :=
    hcont.eventually (Iio_mem_nhds (by simpa using hd))
  filter_upwards [ht] with t ht
  have hH' : (t • H).IsHermitian := by
    change star (t • H) = t • H
    simp [show star H = H from hH]
  have hlow := add_le_add (Spectral.minEigenvalue_smul_one_le hX.isHermitian)
    (hermitian_lower_of_norm_le hH' ht.le)
  rw [← add_smul] at hlow
  have heq : Spectral.minEigenvalue hX.isHermitian + -d = d := by dsimp [d]; ring
  rw [heq] at hlow
  exact ⟨MatrixPowers.posDef_of_le (Matrix.PosDef.one.smul hd) hlow, hlow⟩

theorem posDef_add_smul_one (hA : A.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    (A + s • (1 : MatR n)).PosDef :=
  hA.add_posSemidef (Matrix.PosSemidef.one.smul hs)

theorem norm_resolvent_le (hA : A.PosDef) {d s : ℝ} (hd : 0 < d)
    (hlo : d • (1 : MatR n) ≤ A) (hs : 0 < s) :
    ‖(A + s • (1 : MatR n))⁻¹‖ ≤ (d + s)⁻¹ := by
  apply norm_inv_le (posDef_add_smul_one hA hs.le) (add_pos hd hs)
  simpa only [add_smul] using add_le_add hlo (le_refl (s • (1 : MatR n)))

theorem hasDerivAt_line (X H : MatR n) (t : ℝ) : HasDerivAt (line X H) H t := by
  have h := (hasDerivAt_const t X).add ((hasDerivAt_id t).smul_const H)
  change HasDerivAt (fun u : ℝ => X + u • H) H t
  simpa only [Pi.add_def, id_eq, one_smul, zero_add] using h

theorem hasDerivAt_matrix_inv {f : ℝ → MatR n} {f' : MatR n} {t : ℝ}
    (hf : HasDerivAt f f' t) (hu : IsUnit (f t)) :
    HasDerivAt (fun u => (f u)⁻¹) (-((f t)⁻¹ * f' * (f t)⁻¹)) t := by
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  simp only [← Ring.inverse_unit, hu.unit_spec] at hi
  have h := hi.comp_hasDerivAt t hf
  change HasDerivAt (fun u => Ring.inverse (f u))
    (-(Ring.inverse (f t) * f' * Ring.inverse (f t))) t at h
  simpa only [← Matrix.nonsing_inv_eq_ringInverse] using h

theorem mul_resolvent (hA : A.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    A * (A + s • (1 : MatR n))⁻¹ = 1 - s • (A + s • (1 : MatR n))⁻¹ := by
  have hZ := posDef_add_smul_one hA hs
  have h := Matrix.mul_nonsing_inv (A + s • (1 : MatR n))
    (isUnit_iff_ne_zero.mpr hZ.det_pos.ne')
  rw [add_mul, smul_mul, one_mul] at h
  exact eq_sub_iff_add_eq.mpr h

theorem kernel_deriv_algebra (Y H R : MatR n) (s c : ℝ)
    (hYR : Y * R = 1 - s • R) :
    c • (H * R + Y * (-(R * H * R))) = (c * s) • (R * H * R) := by
  have he : Y * (-(R * H * R)) + H * R = s • (R * H * R) := by
    rw [mul_neg, ← mul_assoc, ← mul_assoc, hYR]
    simp only [sub_mul, one_mul, smul_mul]
    abel
  rw [add_comm (H * R), he, smul_smul]

theorem hasDerivAt_resolventKernel (X H : MatR n) (p s t : ℝ)
    (hs : 0 < s) (hY : (line X H t).PosDef) :
    HasDerivAt (fun u => PowerIntegral.resolventKernel p s (line X H u))
      (kernelDeriv p s (line X H t) H) t := by
  have hl := hasDerivAt_line X H t
  have hi := hasDerivAt_matrix_inv (hl.add_const (s • (1 : MatR n)))
    (posDef_add_smul_one hY hs.le).isUnit
  have h := (hl.mul hi).const_smul (s ^ (p - 1))
  have hp : s ^ (p - 1) * s = s ^ p := by
    rw [Real.rpow_sub_one hs.ne' p]
    field_simp
  convert h using 1
  · rfl
  · dsimp [kernelDeriv]
    rw [kernel_deriv_algebra _ _ _ _ _ (mul_resolvent hY hs.le), hp]

def derivBound (H : MatR n) (d p s : ℝ) : ℝ :=
  (‖H‖ / d) * Real.rpowIntegrand₀₁ p s d

theorem integrable_derivBound (H : MatR n) {d p : ℝ} (hd : 0 < d)
    (hp : p ∈ Ioo (0 : ℝ) 1) : IntegrableOn (derivBound H d p) (Ioi 0) := by
  unfold derivBound IntegrableOn
  exact (Real.integrableOn_rpowIntegrand₀₁_Ioi hp hd.le).const_mul _

theorem norm_kernelDeriv_le (hA : A.PosDef) {d p s : ℝ} (hd : 0 < d)
    (hlo : d • (1 : MatR n) ≤ A) (hp : p ∈ Ioo (0 : ℝ) 1) (hs : 0 < s)
    (H : MatR n) : ‖kernelDeriv p s A H‖ ≤ derivBound H d p s := by
  let R := (A + s • (1 : MatR n))⁻¹
  have hR : ‖R‖ ≤ (d + s)⁻¹ := norm_resolvent_le hA hd hlo hs
  have hprod : ‖R * H * R‖ ≤ (d + s)⁻¹ * ‖H‖ * (d + s)⁻¹ := calc
    _ ≤ (‖R‖ * ‖H‖) * ‖R‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hR (norm_nonneg H)) hR
      (norm_nonneg R) (mul_nonneg (by positivity) (norm_nonneg H))
  have hpw : s ^ p = s ^ (p - 1) * s := by
    rw [Real.rpow_sub_one hs.ne' p]
    field_simp
  have heq : s ^ p * ((d + s)⁻¹ * ‖H‖ * (d + s)⁻¹) =
      (s / (s + d)) * derivBound H d p s := by
    rw [derivBound, Real.rpowIntegrand₀₁_eq_pow_div hp hs.le hd.le, hpw]
    field_simp [hd.ne', (add_pos hd hs).ne', (add_pos hs hd).ne']
    ring
  have hb : 0 ≤ derivBound H d p s :=
    mul_nonneg (div_nonneg (norm_nonneg H) hd.le)
      (Real.rpowIntegrand₀₁_nonneg hp.1 hs.le hd.le)
  have hfrac : s / (s + d) ≤ 1 := (div_le_one (add_pos hs hd)).mpr (by linarith)
  calc
    _ = s ^ p * ‖R * H * R‖ := by
      rw [kernelDeriv, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hs p)]
    _ ≤ s ^ p * ((d + s)⁻¹ * ‖H‖ * (d + s)⁻¹) :=
      mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hs.le p)
    _ = (s / (s + d)) * derivBound H d p s := heq
    _ ≤ 1 * derivBound H d p s := mul_le_mul_of_nonneg_right hfrac hb
    _ = _ := one_mul _

theorem continuousOn_resolvent (hX : X.PosDef) :
    ContinuousOn (fun s : ℝ => (X + s • (1 : MatR n))⁻¹) (Ioi 0) := by
  intro s hs
  have hi := hasDerivAt_matrix_inv (hasDerivAt_line X (1 : MatR n) s)
    (posDef_add_smul_one hX hs.le).isUnit
  exact hi.continuousAt.continuousWithinAt

theorem continuousOn_kernelDeriv (hX : X.PosDef) (H : MatR n) (p : ℝ) :
    ContinuousOn (fun s => kernelDeriv p s X H) (Ioi 0) := by
  have hpow : ContinuousOn (fun s : ℝ => s ^ p) (Ioi 0) :=
    continuousOn_id.rpow_const (fun s hs => Or.inl hs.ne')
  have hR := continuousOn_resolvent hX
  exact hpow.smul ((hR.mul continuousOn_const).mul hR)

/-- Differentiation of the full matrix integral along a self-adjoint direction. -/
theorem hasDerivAt_rpow_integral [NeZero n] (hX : X.PosDef) (hH : H.IsHermitian)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun s => kernelDeriv p s X H) (Ioi 0) ∧
      HasDerivAt (fun t => CFC.rpow (line X H t) p)
        (PowerIntegral.powerNormalization p • ∫ s in Ioi (0 : ℝ), kernelDeriv p s X H) 0 := by
  obtain ⟨d, hd, hU⟩ := exists_uniform_lower hX hH
  let S := {t : ℝ | (line X H t).PosDef ∧ d • (1 : MatR n) ≤ line X H t}
  have hS : S ∈ 𝓝 (0 : ℝ) := hU
  have hm : ∀ᶠ t : ℝ in 𝓝 0, AEStronglyMeasurable
      (fun s => PowerIntegral.resolventKernel p s (line X H t)) (volume.restrict (Ioi 0)) := by
    filter_upwards [hU] with t ht
    exact (PowerIntegral.integrable_resolvent_kernel ht.1 hp).aestronglyMeasurable
  have h0 : Integrable (fun s => PowerIntegral.resolventKernel p s (line X H 0))
      (volume.restrict (Ioi 0)) := by
    simpa only [IntegrableOn, line, zero_smul, add_zero] using PowerIntegral.integrable_resolvent_kernel hX hp
  have hm' : AEStronglyMeasurable (fun s => kernelDeriv p s (line X H 0) H)
      (volume.restrict (Ioi 0)) := by
    simpa only [line, zero_smul, add_zero] using
      (continuousOn_kernelDeriv hX H p).aestronglyMeasurable (μ := volume) measurableSet_Ioi
  have hb : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi 0)), ∀ t ∈ S,
      ‖kernelDeriv p s (line X H t) H‖ ≤ derivBound H d p s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro t ht
    exact norm_kernelDeriv_le ht.1 hd ht.2 hp hs H
  have hdiff : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi 0)), ∀ t ∈ S,
      HasDerivAt (fun u => PowerIntegral.resolventKernel p s (line X H u))
        (kernelDeriv p s (line X H t) H) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro t ht
    exact hasDerivAt_resolventKernel X H p s t hs ht.1
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t s => PowerIntegral.resolventKernel p s (line X H t))
    (F' := fun t s => kernelDeriv p s (line X H t) H)
    (bound := derivBound H d p) hS hm h0 hm' hb (integrable_derivBound H hd hp) hdiff
  refine ⟨by simpa only [IntegrableOn, line, zero_smul, add_zero] using hD.1, ?_⟩
  have heq : (fun t => CFC.rpow (line X H t) p) =ᶠ[𝓝 0]
      (fun t => PowerIntegral.powerNormalization p •
        ∫ s in Ioi (0 : ℝ), PowerIntegral.resolventKernel p s (line X H t)) := by
    filter_upwards [hU] with t ht
    exact PowerIntegral.rpow_eq_integral ht.1 hp
  have hscaled := (hD.2.const_smul (PowerIntegral.powerNormalization p)).congr_of_eventuallyEq heq
  simpa only [line, zero_smul, add_zero] using hscaled

theorem rpow_line_one (hX : X.PosDef) (p t : ℝ)
    (ht : ∀ i, 0 < t + hX.isHermitian.eigenvalues i) :
    CFC.rpow (line X 1 t) p = PowerIntegral.spectralCLM hX.isHermitian
      (fun i => (t + hX.isHermitian.eigenvalues i) ^ p) := by
  have hshift : cfc (fun x : ℝ => t + x) X = line X 1 t := by
    rw [cfc_const_add t (fun x : ℝ => x) X (by fun_prop) hX.isHermitian.isSelfAdjoint,
      cfc_id' ℝ X hX.isHermitian.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
    exact add_comm _ _
  have hpos : ∀ x ∈ spectrum ℝ X, 0 < t + x := by
    intro x hx
    rw [hX.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ht i
  have hpow : CFC.rpow (cfc (fun x : ℝ => t + x) X) p =
      cfc (fun x : ℝ => (t + x) ^ p) X :=
    CFC.cfc_rpow hpos (by fun_prop) hX.isHermitian.isSelfAdjoint
  rw [← hshift, hpow, ← PowerIntegral.spectralCLM_cfc hX.isHermitian]

/-- Along the identity direction, a fixed eigenbasis gives the derivative directly. -/
theorem hasDerivAt_rpow_shift (hX : X.PosDef) (p : ℝ) :
    HasDerivAt (fun t => CFC.rpow (line X 1 t) p) (p • CFC.rpow X (p - 1)) 0 := by
  have hdv : HasDerivAt (fun t : ℝ => fun i => (t + hX.isHermitian.eigenvalues i) ^ p)
      (p • fun i => (hX.isHermitian.eigenvalues i) ^ (p - 1)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := ((hasDerivAt_id (0 : ℝ)).add_const (hX.isHermitian.eigenvalues i)).rpow_const
      (p := p) (Or.inl (by simpa using (hX.eigenvalues_pos i).ne'))
    simpa only [id_eq, zero_add, one_mul, Pi.smul_apply, smul_eq_mul] using h
  have hmap := (PowerIntegral.spectralCLM hX.isHermitian).hasFDerivAt.comp_hasDerivAt 0 hdv
  rw [map_smul, PowerIntegral.spectralCLM_cfc hX.isHermitian (fun x : ℝ => x ^ (p - 1)),
    ← Spectral.rpow_eq_cfc hX (p - 1)] at hmap
  have ht : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < t + hX.isHermitian.eigenvalues i := by
    rw [eventually_all]
    intro i
    have hc : ContinuousAt (fun t : ℝ => t + hX.isHermitian.eigenvalues i) 0 := by fun_prop
    exact hc.eventually (Ioi_mem_nhds (by simpa using hX.eigenvalues_pos i))
  have heq : (fun t => CFC.rpow (line X 1 t) p) =ᶠ[𝓝 0]
      (fun t => PowerIntegral.spectralCLM hX.isHermitian
        (fun i => (t + hX.isHermitian.eigenvalues i) ^ p)) :=
    ht.mono (fun t ht => rpow_line_one hX p t ht)
  exact hmap.congr_of_eventuallyEq heq

theorem normalization_smul_integral_kernel_one [NeZero n] (hX : X.PosDef)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    PowerIntegral.powerNormalization p • ∫ s in Ioi (0 : ℝ), kernelDeriv p s X 1 =
      p • CFC.rpow X (p - 1) :=
  (hasDerivAt_rpow_integral hX (Matrix.PosDef.one : (1 : MatR n).PosDef).isHermitian hp).2.unique
    (hasDerivAt_rpow_shift hX p)

def traceCLM : MatR n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (n := Fin n) (R := ℝ) (α := ℝ))

@[simp] theorem traceCLM_apply (A : MatR n) : traceCLM A = A.trace := rfl

def traceMulCLM (H : MatR n) : MatR n →L[ℝ] ℝ :=
  traceCLM.comp ((ContinuousLinearMap.mul ℝ (MatR n)).flip H)

@[simp] theorem traceMulCLM_apply (H A : MatR n) : traceMulCLM H A = (A * H).trace := rfl

theorem trace_kernel_cyclic (X H : MatR n) (p s : ℝ) :
    (kernelDeriv p s X H).trace = (kernelDeriv p s X 1 * H).trace := by
  simp only [kernelDeriv, smul_mul, Matrix.trace_smul, mul_one]
  congr 1
  exact Matrix.trace_mul_cycle _ _ _

theorem trace_integral_kernel (X H : MatR n) (p c : ℝ)
    (hH : IntegrableOn (fun s => kernelDeriv p s X H) (Ioi 0))
    (hI : IntegrableOn (fun s => kernelDeriv p s X 1) (Ioi 0)) :
    (c • ∫ s in Ioi (0 : ℝ), kernelDeriv p s X H).trace =
      ((c • ∫ s in Ioi (0 : ℝ), kernelDeriv p s X 1) * H).trace := by
  rw [smul_mul, Matrix.trace_smul, Matrix.trace_smul]
  congr 1
  calc
    _ = ∫ s in Ioi (0 : ℝ), (kernelDeriv p s X H).trace :=
      ((traceCLM (n := n)).integral_comp_comm hH).symm
    _ = ∫ s in Ioi (0 : ℝ), (kernelDeriv p s X 1 * H).trace :=
      setIntegral_congr_fun measurableSet_Ioi (fun s _ => trace_kernel_cyclic X H p s)
    _ = _ := (traceMulCLM H).integral_comp_comm hI

/-- M03: the trace derivative in any self-adjoint direction, without a commutativity assumption. -/
theorem hasDerivAt_trace_rpow [NeZero n] (hX : X.PosDef) (hH : H.IsHermitian)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => (CFC.rpow (X + t • H) p).trace)
      (p * (CFC.rpow X (p - 1) * H).trace) 0 := by
  have hD := hasDerivAt_rpow_integral hX hH hp
  have hI := hasDerivAt_rpow_integral hX (Matrix.PosDef.one : (1 : MatR n).PosDef).isHermitian hp
  have hcoef : traceCLM (PowerIntegral.powerNormalization p •
      ∫ s in Ioi (0 : ℝ), kernelDeriv p s X H) = p * (CFC.rpow X (p - 1) * H).trace := by
    rw [traceCLM_apply, trace_integral_kernel X H p _ hD.1 hI.1,
      normalization_smul_integral_kernel_one hX hp, smul_mul, Matrix.trace_smul]
    rfl
  have hT := (traceCLM (n := n)).hasFDerivAt.comp_hasDerivAt 0 hD.2
  rw [hcoef] at hT
  simpa only [Function.comp_def, traceCLM_apply, line] using hT

end Khachiyan.TraceDerivative
