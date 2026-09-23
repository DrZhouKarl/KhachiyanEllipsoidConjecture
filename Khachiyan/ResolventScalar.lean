import Khachiyan.PowerIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Scalar logarithmic integral for the independent resolvent proof

This module supplies the scalar integration-by-parts and endpoint arguments for
A01/M04R, Section 8 of `proof.md`. All integrals use Lebesgue measure on `(0,∞)`.
No project trace derivative or rank-one trace inequality is imported.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Khachiyan.ResolventScalar

/-- The difference of two shifted scalar log determinants. -/
def logDiff (x y s : ℝ) : ℝ := Real.log (s + x) - Real.log (s + y)

theorem log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a - Real.log b ≤ (a - b) / b := by
  rw [← Real.log_div ha.ne' hb.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  convert h using 1
  field_simp

/-- A denominator bounded away from zero gives a uniform logarithm bound. -/
theorem abs_log_sub_log_le {a b d : ℝ} (hd : 0 < d) (hda : d ≤ a) (hdb : d ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / d := by
  have ha := hd.trans_le hda
  have hb := hd.trans_le hdb
  apply abs_le.mpr
  constructor
  · have h := (log_sub_log_le hb ha).trans
      ((div_le_div_of_nonneg_right (le_abs_self (b - a)) ha.le).trans
        (div_le_div_of_nonneg_left (abs_nonneg (b - a)) hd hda))
    rw [abs_sub_comm b a] at h
    linarith
  · exact (log_sub_log_le ha hb).trans
      ((div_le_div_of_nonneg_right (le_abs_self (a - b)) hb.le).trans
        (div_le_div_of_nonneg_left (abs_nonneg (a - b)) hd hdb))

theorem abs_logDiff_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) :
    |logDiff x y s| ≤ |x - y| / (s + min x y) := by
  simpa only [logDiff, add_sub_add_left_eq_sub] using
    abs_log_sub_log_le (add_pos_of_nonneg_of_pos hs (lt_min hx hy))
      (by linarith [min_le_left x y] : s + min x y ≤ s + x)
      (by linarith [min_le_right x y] : s + min x y ≤ s + y)

/-- The scalar resolvent kernel in M02.1. -/
def powerKernel (p x s : ℝ) : ℝ := s ^ (p - 1) * x / (s + x)

theorem powerKernel_eq {p x s : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hx : 0 < x) (hs : 0 < s) :
    powerKernel p x s = Real.rpowIntegrand₀₁ p s x := by
  exact (Real.rpowIntegrand₀₁_eq_pow_div hp hs.le hx.le).symm

theorem integrable_powerKernel {p x : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    IntegrableOn (powerKernel p x) (Ioi 0) := by
  exact (Real.integrableOn_rpowIntegrand₀₁_Ioi hp hx.le).congr_fun
    (fun s hs => (powerKernel_eq hp hx hs).symm) measurableSet_Ioi

theorem power_eq_integral_powerKernel {p x : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hx : 0 < x) :
    x ^ p = PowerIntegral.powerNormalization p * ∫ s in Ioi 0, powerKernel p x s := by
  rw [PowerIntegral.normalization_eq_inverse_integral hp]
  convert Real.rpow_eq_const_mul_integral hp hx.le using 1
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun s hs => powerKernel_eq hp hx hs)

theorem integrable_weighted_inv {p x : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => s ^ (p - 1) / (s + x)) (Ioi 0) := by
  have h : IntegrableOn (fun s => powerKernel p x s / x) (Ioi 0) :=
    (integrable_powerKernel hp hx).div_const x
  apply h.congr_fun _ measurableSet_Ioi
  intro s hs
  dsimp [powerKernel]
  field_simp

theorem integrable_weighted_logDiff {p x y : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun s => s ^ (p - 1) * logDiff x y s) (Ioi 0) := by
  apply ((integrable_weighted_inv hp (lt_min hx hy)).const_mul |x - y|).mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro s hs
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · exact Real.continuousAt_rpow_const _ _ (Or.inl hs.ne')
    · exact ((continuousAt_id.add continuousAt_const).log (add_pos hs hx).ne').sub
        ((continuousAt_id.add continuousAt_const).log (add_pos hs hy).ne')
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs _)]
    calc
      _ ≤ s ^ (p - 1) * (|x - y| / (s + min x y)) :=
        mul_le_mul_of_nonneg_left (abs_logDiff_le hx hy hs.le) (Real.rpow_nonneg hs.le _)
      _ = _ := by ring

/-- The boundary term vanishes at the finite endpoint, where the log difference
has a finite limit. -/
theorem boundary_zero {p x y : ℝ} (hp : 0 < p) (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun s => s ^ p * logDiff x y s) (𝓝[>] 0) (𝓝 0) := by
  have hf : ContinuousAt (fun s => s ^ p * logDiff x y s) 0 := by
    apply ContinuousAt.mul
    · exact Real.continuousAt_rpow_const _ _ (Or.inr hp.le)
    · exact ((continuousAt_id.add continuousAt_const).log (by simpa using hx.ne')).sub
        ((continuousAt_id.add continuousAt_const).log (by simpa using hy.ne'))
  simpa only [Real.zero_rpow hp.ne', zero_mul] using hf.tendsto.mono_left nhdsWithin_le_nhds

/-- The explicit inverse-linear bound needed at infinity. -/
theorem abs_logDiff_le_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {s : ℝ} (hs : 0 < s) :
    |logDiff x y s| ≤ |x - y| / s := by
  exact (abs_logDiff_le hx hy hs.le).trans
    (div_le_div_of_nonneg_left (abs_nonneg _) hs (by linarith [lt_min hx hy]))

/-- The boundary term vanishes at infinity by the inverse-linear log bound
and the strict upper bound on the exponent. -/
theorem boundary_infty {p x y : ℝ} (hp : p < 1) (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun s => s ^ p * logDiff x y s) atTop (𝓝 0) := by
  have hpow : Tendsto (fun s : ℝ => s ^ (p - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hp)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa using hpow.const_mul |x - y|)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs _)]
  calc
    _ ≤ s ^ p * (|x - y| / s) :=
      mul_le_mul_of_nonneg_left (abs_logDiff_le_div hx hy hs) (Real.rpow_nonneg hs.le _)
    _ = |x - y| * s ^ (p - 1) := by rw [Real.rpow_sub_one hs.ne']; ring

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_logDiff {x y s : ℝ} (hx : 0 < x) (hy : 0 < y) (hs : 0 ≤ s) :
    HasDerivAt (logDiff x y) ((s + x)⁻¹ - (s + y)⁻¹) s := by
  convert!
    (((hasDerivAt_id s).add_const x).log (add_pos_of_nonneg_of_pos hs hx).ne').sub
      (((hasDerivAt_id s).add_const y).log (add_pos_of_nonneg_of_pos hs hy).ne') using 1
  simp [one_div]

/-- Multiplication of the log derivative by `s^p` gives a difference of the
already integrable M02 kernels. -/
theorem weighted_logDiff_derivative {p x y s : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hs : 0 < s) :
    s ^ p * ((s + x)⁻¹ - (s + y)⁻¹) = powerKernel p y s - powerKernel p x s := by
  dsimp [powerKernel]
  rw [Real.rpow_sub_one hs.ne']
  field_simp
  ring

theorem integrable_weighted_logDiff_derivative {p x y : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun s => s ^ p * ((s + x)⁻¹ - (s + y)⁻¹)) (Ioi 0) := by
  have h : IntegrableOn (fun s => powerKernel p y s - powerKernel p x s) (Ioi 0) :=
    (integrable_powerKernel hp hy).sub (integrable_powerKernel hp hx)
  exact h.congr_fun (fun s hs => (weighted_logDiff_derivative hx hy hs).symm) measurableSet_Ioi

set_option backward.isDefEq.respectTransparency false in
/-- Scalar integration by parts, with integrability and both endpoint limits
proved above rather than assumed. -/
theorem integral_logDiff {p x y : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hx : 0 < x) (hy : 0 < y) :
    p * (∫ s in Ioi 0, s ^ (p - 1) * logDiff x y s) =
      (∫ s in Ioi 0, powerKernel p x s) - (∫ s in Ioi 0, powerKernel p y s) := by
  have huv : IntegrableOn (fun s => p * s ^ (p - 1) * logDiff x y s) (Ioi 0) := by
    simpa only [IntegrableOn, mul_assoc] using (integrable_weighted_logDiff hp hx hy).const_mul p
  have hi := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := fun s : ℝ => s ^ p) (v := logDiff x y)
    (u' := fun s => p * s ^ (p - 1)) (v' := fun s => (s + x)⁻¹ - (s + y)⁻¹)
    (fun s hs => Real.hasDerivAt_rpow_const (Or.inl hs.ne'))
    (fun s hs => hasDerivAt_logDiff hx hy hs.le)
    (integrable_weighted_logDiff_derivative hp hx hy) huv
    (boundary_zero hp.1 hx hy) (boundary_infty hp.2 hx hy)
  have he : (∫ s in Ioi 0, s ^ p * ((s + x)⁻¹ - (s + y)⁻¹)) =
      (∫ s in Ioi 0, powerKernel p y s) - (∫ s in Ioi 0, powerKernel p x s) := by
    rw [← integral_sub (integrable_powerKernel hp hy) (integrable_powerKernel hp hx)]
    exact setIntegral_congr_fun measurableSet_Ioi (fun s hs => weighted_logDiff_derivative hx hy hs)
  rw [he] at hi
  simp only [zero_sub, sub_zero, mul_assoc, integral_const_mul] at hi
  linarith

/-- The scalar logarithmic representation used for the final M04R comparison. -/
theorem rpow_sub_eq_integral_logDiff {p x y : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hx : 0 < x) (hy : 0 < y) :
    x ^ p - y ^ p = p * PowerIntegral.powerNormalization p *
      ∫ s in Ioi 0, s ^ (p - 1) * logDiff x y s := by
  rw [power_eq_integral_powerKernel hp hx, power_eq_integral_powerKernel hp hy]
  rw [mul_assoc p, mul_left_comm p, ← mul_sub, integral_logDiff hp hx hy]

/-- The scalar determinant ratio in the form used in the resolvent comparison. -/
theorem logDiff_add {m d s : ℝ} (hm : 0 < m) (hd : 0 ≤ d) (hs : 0 ≤ s) :
    logDiff (m + d) m s = Real.log (1 + d / (m + s)) := by
  dsimp [logDiff]
  rw [← Real.log_div (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

theorem integrable_weighted_log_one_add_div {p m d : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hm : 0 < m) (hd : 0 ≤ d) :
    IntegrableOn (fun s => s ^ (p - 1) * Real.log (1 + d / (m + s))) (Ioi 0) := by
  apply (integrable_weighted_logDiff hp (add_pos_of_pos_of_nonneg hm hd) hm).congr_fun
    _ measurableSet_Ioi
  intro s hs
  dsimp only
  rw [logDiff_add hm hd hs.le]

/-- Exact evaluation of the scalar integral on the lower side of M04R. -/
theorem rpow_add_sub_eq_integral_log {p m d : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hm : 0 < m) (hd : 0 ≤ d) :
    (m + d) ^ p - m ^ p = p * PowerIntegral.powerNormalization p *
      ∫ s in Ioi 0, s ^ (p - 1) * Real.log (1 + d / (m + s)) := by
  rw [rpow_sub_eq_integral_logDiff hp (add_pos_of_pos_of_nonneg hm hd) hm]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only
  rw [logDiff_add hm hd hs.le]

end Khachiyan.ResolventScalar
