import Khachiyan.ConeLimit

/-!
# T02: uniform optimality of the geometric cutting constant

This module extracts the geometric counterexamples from C01--C03 of `proof.md`.
Every smaller real constant fails in some dimension at least two, for actual
Lebesgue maximal-ellipsoid volumes and the canonical cutting center.
-/

noncomputable section
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set MeasureTheory

namespace Khachiyan

/-- T02, including every real `r < rStar`, without a nonnegativity restriction on `r`. -/
theorem sharp_constant {r : ℝ} (hr : r < rStar) :
    ∃ (n : ℕ) (hn : 2 ≤ n),
      letI : NeZero n := ⟨by omega⟩
      ∃ (K : Set (V n)) (p : V n),
        IsConvexBody K ∧ p ≠ 0 ∧
          r * (maxEllipsoidVolume K).toReal <
            (maxEllipsoidVolume (K ∩ centralHalfspace (johnCenter K) p)).toReal := by
  obtain ⟨m, hm, hratio⟩ := Cone.exists_volumeRatio_gt hr
  refine ⟨m + 1, by omega, Cone.body m, Cone.cutNormal m,
    Cone.isConvexBody_body hm, Cone.cutNormal_ne_zero m, ?_⟩
  have hden := (Cone.isJohnNormalized_body hm).maxEllipsoidVolume_toReal_pos
  have hvolume := (lt_div_iff₀ hden).mp hratio
  rw [← Cone.cut_eq_canonical_cut hm]
  exact hvolume

end Khachiyan
