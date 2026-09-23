import Khachiyan.ConeGeometry
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# C03: actual cone-volume ratios and their limit

This module implements C03 of `proof.md`. The explicit feasible ellipsoid
supplies an actual Lebesgue-volume ratio lower bound tending to `sqrt e / 2`.
T01 also bounds the full maximal-volume ratio from above, giving its limit.
-/

noncomputable section
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace BigOperators
open Matrix Set MeasureTheory Filter Topology

namespace Khachiyan.Cone

variable {m : ℕ}

def lowerBound (m : ℕ) : ℝ := (1 / 2 : ℝ) * Real.sqrt ((1 + 1 / (m : ℝ)) ^ m)

def volumeRatio (m : ℕ) : ℝ :=
  (maxEllipsoidVolume (cut m)).toReal / (maxEllipsoidVolume (body m)).toReal

theorem candidateShape_det_eq_lowerBound (hm : 1 ≤ m) :
    (candidateShape m).det = lowerBound m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hbase : ((m : ℝ) + 1) / m = 1 + 1 / (m : ℝ) := by field_simp
  have hpow : (transverseScale m ^ m) ^ 2 = (1 + 1 / (m : ℝ)) ^ m := by
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul, transverseScale_sq hm, hbase]
  have hsqrt : (Real.sqrt ((1 + 1 / (m : ℝ)) ^ m)) ^ 2 =
      (1 + 1 / (m : ℝ)) ^ m := Real.sq_sqrt (by positivity)
  have heq : transverseScale m ^ m = Real.sqrt ((1 + 1 / (m : ℝ)) ^ m) := by
    nlinarith [pow_nonneg (transverseScale_pos hm).le m,
      Real.sqrt_nonneg ((1 + 1 / (m : ℝ)) ^ m)]
  rw [candidateShape_det, heq]
  rfl

theorem candidate_volume_ratio (hm : 1 ≤ m) :
    (volume (ellipsoid (candidateCenter m) (candidateShape m))).toReal /
        (maxEllipsoidVolume (body m)).toReal = lowerBound m := by
  rw [volume_ellipsoid_real_ratio (isJohnNormalized_body hm) (candidateShape_posDef hm),
    Matrix.det_one, div_one, candidateShape_det_eq_lowerBound hm]

theorem lowerBound_le_volumeRatio (hm : 1 ≤ m) : lowerBound m ≤ volumeRatio m := by
  have hvolume := volume_le_maxEllipsoidVolume (candidate_feasible hm)
  have hreal := (ENNReal.toReal_le_toReal
    (volume_ellipsoid_lt_top (candidateCenter m) (candidateShape m)).ne
    (isConvexBody_cut hm).maxEllipsoidVolume_lt_top.ne).mpr hvolume
  unfold volumeRatio
  rw [← candidate_volume_ratio hm]
  exact (div_le_div_iff_of_pos_right
    (isJohnNormalized_body hm).maxEllipsoidVolume_toReal_pos).mpr hreal

theorem volumeRatio_pos (hm : 1 ≤ m) : 0 < volumeRatio m := by
  have hc := isConvexBody_cut hm
  exact div_pos (ENNReal.toReal_pos_iff.mpr
    ⟨hc.maxEllipsoidVolume_pos, hc.maxEllipsoidVolume_lt_top⟩)
    (isJohnNormalized_body hm).maxEllipsoidVolume_toReal_pos

theorem volumeRatio_le_rStar (hm : 1 ≤ m) : volumeRatio m ≤ rStar := by
  rw [volumeRatio, cut_eq_canonical_cut hm]
  exact john_center_cut_volume_ratio_le (isConvexBody_body hm) (cutNormal_ne_zero m)

/-- C03: the explicit feasible-volume lower bounds tend to the claimed optimal constant. -/
theorem tendsto_lowerBound : Tendsto lowerBound atTop (𝓝 rStar) := by
  have h : Tendsto (fun m : ℕ => (1 / 2 : ℝ) *
    Real.sqrt ((1 + 1 / (m : ℝ)) ^ m)) atTop
      (𝓝 ((1 / 2 : ℝ) * Real.sqrt (Real.exp 1))) :=
    tendsto_const_nhds.mul (Real.tendsto_one_add_div_pow_exp (1 : ℝ)).sqrt
  have he : (1 / 2 : ℝ) * Real.sqrt (Real.exp 1) = rStar := by
    rw [Scalar.rStar_eq_sqrt_exp_one]
    ring
  rw [he] at h
  exact h

/-- Combining C03 with T01 also gives the limit of the actual maximal-volume ratios. -/
theorem tendsto_volumeRatio : Tendsto volumeRatio atTop (𝓝 rStar) := by
  apply tendsto_lowerBound.squeeze' tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact lowerBound_le_volumeRatio hm
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact volumeRatio_le_rStar hm

theorem exists_volumeRatio_gt {r : ℝ} (hr : r < rStar) :
    ∃ m : ℕ, 1 ≤ m ∧ r < volumeRatio m := by
  obtain ⟨m, hm, hrm⟩ := ((eventually_ge_atTop 1).and
    (tendsto_lowerBound.eventually_const_lt hr)).exists
  exact ⟨m, hm, hrm.trans_le (lowerBound_le_volumeRatio hm)⟩

end Khachiyan.Cone
