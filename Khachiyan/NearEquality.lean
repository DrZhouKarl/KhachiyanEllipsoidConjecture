import Khachiyan.GeometricBound

/-!
# T04: the smallest normalized semiaxis near equality

This module implements T04 of `proof.md`. The logarithmic deficit bounds and
the exponential semiaxis bounds follow from actual normalized containment and
maximality, through R02 and the two exact scalar tangents in S01.
-/

noncomputable section
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set MeasureTheory

namespace Khachiyan

theorem log_rStar : Real.log rStar = Scalar.logConstant := by
  rw [← Scalar.exp_logConstant, Real.log_exp]

variable {n : ℕ} [NeZero n]

theorem t04_log_det_tangents {K : Set (V n)} (hK : IsJohnNormalized K)
    (hconv : Convex ℝ K) (hclosed : IsClosed K) {a : V n} {A : MatR n}
    (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    (hrho : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖) :
    Real.log A.det ≤ Scalar.logConstant +
        (Real.log (Spectral.minEigenvalue hA.isHermitian) - Scalar.crossing) / 6 ∧
      Real.log A.det ≤ Scalar.logConstant -
        (Real.log (Spectral.minEigenvalue hA.isHermitian) - Scalar.crossing) / 42 := by
  have hα := Spectral.minEigenvalue_pos hA
  have h1 := Real.log_le_log hA.det_pos (r02_log_bound_one hK hconv hclosed hA hell hrho rfl)
  have h2 := Real.log_le_log hA.det_pos (r02_log_bound_two hK hconv hclosed hA hell hrho rfl)
  rw [Scalar.log_R1 hα] at h1
  rw [Scalar.log_R2 hα] at h2
  exact ⟨h1.trans (Scalar.F1_le_tangent _), h2.trans (Scalar.F2_le_tangent _)⟩

/-- Both tangent deficits are valid globally; the piecewise statement chooses the useful side. -/
theorem t04_log_deficit_bounds {K : Set (V n)} (hK : IsJohnNormalized K)
    (hconv : Convex ℝ K) (hclosed : IsClosed K) {a : V n} {A : MatR n}
    (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    (hrho : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖) :
    (1 / 6 : ℝ) * Real.log (1 / (2 * Spectral.minEigenvalue hA.isHermitian)) ≤
        Real.log (rStar / A.det) ∧
      (1 / 42 : ℝ) * Real.log (2 * Spectral.minEigenvalue hA.isHermitian) ≤
        Real.log (rStar / A.det) := by
  have ht := t04_log_det_tangents hK hconv hclosed hA hell hrho
  have hα := Spectral.minEigenvalue_pos hA
  have hprod : Real.log (2 * Spectral.minEigenvalue hA.isHermitian) =
      Real.log 2 + Real.log (Spectral.minEigenvalue hA.isHermitian) :=
    Real.log_mul (by norm_num) hα.ne'
  have hinv : Real.log (1 / (2 * Spectral.minEigenvalue hA.isHermitian)) =
      -(Real.log 2 + Real.log (Spectral.minEigenvalue hA.isHermitian)) := by
    rw [one_div, Real.log_inv, hprod]
  rw [Real.log_div rStar_pos.ne' hA.det_pos.ne', log_rStar, hinv, hprod]
  dsimp [Scalar.crossing] at ht
  constructor <;> linarith [ht.1, ht.2]

/-- The exact piecewise logarithmic statement in T04. -/
theorem t04_log_deficit {K : Set (V n)} (hK : IsJohnNormalized K)
    (hconv : Convex ℝ K) (hclosed : IsClosed K) {a : V n} {A : MatR n}
    (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    (hrho : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖) :
    let α := Spectral.minEigenvalue hA.isHermitian
    (if α ≤ (1 / 2 : ℝ) then (1 / 6 : ℝ) * Real.log (1 / (2 * α))
      else (1 / 42 : ℝ) * Real.log (2 * α)) ≤ Real.log (rStar / A.det) := by
  have h := t04_log_deficit_bounds hK hconv hclosed hA hell hrho
  dsimp
  split_ifs
  · exact h.1
  · exact h.2

/-- T04: near equality forces the smallest normalized semiaxis into an explicit interval. -/
theorem t04 {K : Set (V n)} (hK : IsJohnNormalized K)
    (hconv : Convex ℝ K) (hclosed : IsClosed K) {a : V n} {A : MatR n}
    (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    (hrho : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖)
    {ε : ℝ} (_hε : 0 ≤ ε) (hnear : rStar * Real.exp (-ε) ≤ A.det) :
    (1 / 2 : ℝ) * Real.exp (-6 * ε) ≤ Spectral.minEigenvalue hA.isHermitian ∧
      Spectral.minEigenvalue hA.isHermitian ≤ (1 / 2 : ℝ) * Real.exp (42 * ε) := by
  have ht := t04_log_det_tangents hK hconv hclosed hA hell hrho
  have hn := Real.log_le_log (mul_pos rStar_pos (Real.exp_pos (-ε))) hnear
  rw [Real.log_mul rStar_pos.ne' (Real.exp_pos (-ε)).ne', log_rStar, Real.log_exp] at hn
  have hlo : Scalar.crossing + (-6 * ε) ≤ Real.log (Spectral.minEigenvalue hA.isHermitian) := by
    linarith [ht.1]
  have hhi : Real.log (Spectral.minEigenvalue hA.isHermitian) ≤ Scalar.crossing + 42 * ε := by
    linarith [ht.2]
  have hel := Real.exp_le_exp.mpr hlo
  have heh := Real.exp_le_exp.mpr hhi
  rw [Real.exp_add, Scalar.exp_crossing, Real.exp_log (Spectral.minEigenvalue_pos hA)] at hel
  rw [Real.exp_add, Scalar.exp_crossing, Real.exp_log (Spectral.minEigenvalue_pos hA)] at heh
  exact ⟨hel, heh⟩

/-- T04 in original coordinates, with near equality stated using actual Lebesgue volume. -/
theorem t04_of_central_cut {K : Set (V n)} (hK : IsConvexBody K)
    {c p : V n} {S : MatR n} (hmax : IsMaxDet K c S) (hp : p ≠ 0)
    {a : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace c p) a A)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hnear : rStar * Real.exp (-ε) ≤
      (volume (ellipsoid a A)).toReal / (maxEllipsoidVolume K).toReal) :
    let α := Spectral.minEigenvalue (normalized_shape_posDef hmax.posDef hA.1).isHermitian
    (1 / 2 : ℝ) * Real.exp (-6 * ε) ≤ α ∧ α ≤ (1 / 2 : ℝ) * Real.exp (42 * ε) := by
  have hb := hK.normalizedBody c hmax.posDef
  have hf := hA.normalize c hmax.posDef
  have hs := hf.2
  rw [normalizedBody_cut hmax.posDef] at hs
  have hrho := norm_inv_center_ge_one_of_halfspace hf.1
    (normalized_normal_ne_zero hmax.posDef hp) (hs.trans inter_subset_right)
  apply t04 hmax.isJohnNormalized hb.2.1 hb.1.isClosed hf.1
    (hs.trans inter_subset_left) hrho hε
  rw [normalized_shape_det hmax.posDef hA.1,
    ← volume_ellipsoid_real_ratio (a := a) hmax hA.1]
  exact hnear

theorem t04_of_john_center_cut {K : Set (V n)} (hK : IsConvexBody K)
    {p : V n} (hp : p ≠ 0) {a : V n} {A : MatR n}
    (hA : IsFeasible (K ∩ centralHalfspace (johnCenter K) p) a A)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hnear : rStar * Real.exp (-ε) ≤
      (volume (ellipsoid a A)).toReal / (maxEllipsoidVolume K).toReal) :
    let α := Spectral.minEigenvalue (normalized_shape_posDef (johnShape_posDef hK) hA.1).isHermitian
    (1 / 2 : ℝ) * Real.exp (-6 * ε) ≤ α ∧ α ≤ (1 / 2 : ℝ) * Real.exp (42 * ε) :=
  t04_of_central_cut hK (john_isMaxDet hK) hp hA hε hnear

end Khachiyan
