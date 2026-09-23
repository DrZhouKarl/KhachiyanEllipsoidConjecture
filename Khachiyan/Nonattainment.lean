import Khachiyan.GeometricBound

/-!
# T03: nonattainment of the uniform constant in finite dimension

This module implements the finite-dimensional strict determinant and geometric
volume bounds of T03 in `proof.md`.
The positive slack at the scalar crossing yields strictness even when the
remaining eigenvalue sum is empty, so the determinant argument includes dimension one.
The exact one-dimensional ratio is proved separately in `OneDimensional.lean`.
-/

noncomputable section
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace BigOperators
open Matrix Set MeasureTheory

namespace Khachiyan

theorem sum_log_lt_of_sum_le {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 < z i) {δ : ℝ} (hδ : 0 < δ)
    (hsum : ∑ i ∈ s, z i ≤ (s.card : ℝ) + δ) :
    ∑ i ∈ s, Real.log (z i) < δ := by
  classical
  by_cases hall : ∀ i ∈ s, z i = 1
  · have he : ∑ i ∈ s, Real.log (z i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hall i hi, Real.log_one]
    rwa [he]
  · push Not at hall
    obtain ⟨i, hi, hne⟩ := hall
    have hlt := Finset.sum_lt_sum (fun j hj => Real.log_le_sub_one_of_pos (hz j hj))
      ⟨i, hi, Real.log_lt_sub_one_of_pos (hz i hi) hne⟩
    have he : ∑ j ∈ s, (z j - 1) = (∑ j ∈ s, z j) - (s.card : ℝ) := by
      simp [Finset.sum_sub_distrib]
    rw [he] at hlt
    linarith

variable {n : ℕ} [NeZero n]

theorem det_lt_rStar_at_half {A : MatR n} (hA : A.PosDef)
    (hhalf : Spectral.minEigenvalue hA.isHermitian = (1 / 2 : ℝ))
    (hsum : (3 / 4 : ℝ) + ∑ i ∈ Finset.univ.erase (Spectral.minIndex hA.isHermitian),
      (hA.isHermitian.eigenvalues i) ^ (1 / 2 : ℝ) ≤ (n : ℝ)) : A.det < rStar := by
  let s := Finset.univ.erase (Spectral.minIndex hA.isHermitian)
  let e := hA.isHermitian.eigenvalues
  have hcard : (s.card : ℝ) = (n : ℝ) - 1 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    norm_num [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))]
  have hepos (i : Fin n) : 0 < e i := hA.eigenvalues_pos i
  have hlogsum : ∑ i ∈ s, Real.log (e i ^ (1 / 2 : ℝ)) < (1 / 4 : ℝ) := by
    apply sum_log_lt_of_sum_le s _ (fun i _ => Real.rpow_pos_of_pos (hepos i) _)
      (by norm_num)
    change (3 / 4 : ℝ) + ∑ i ∈ s, e i ^ (1 / 2 : ℝ) ≤ n at hsum
    rw [hcard]
    linarith
  have hlogscale : ∑ i ∈ s, Real.log (e i) =
      2 * ∑ i ∈ s, Real.log (e i ^ (1 / 2 : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.log_rpow (hepos i)]
    ring
  have hdet : A.det = (1 / 2 : ℝ) * ∏ i ∈ s, e i := by
    rw [Spectral.det_eq_min_mul_prod_erase hA.isHermitian, hhalf]
  have hlogdet : Real.log A.det < Real.log (1 / 2 : ℝ) + 1 / 2 := by
    rw [hdet, Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => (hepos i).ne')),
      Real.log_prod (fun i _ => (hepos i).ne'), hlogscale]
    linarith
  have h := Real.exp_lt_exp.mpr hlogdet
  rw [Real.exp_log hA.det_pos, Real.exp_add, Real.exp_log (by norm_num)] at h
  simpa only [rStar, div_eq_mul_inv, one_mul, mul_comm] using h

/-- The uniform normalized determinant bound is strict in every finite positive dimension. -/
theorem normalized_det_lt_rStar {K : Set (V n)} (hK : IsJohnNormalized K)
    (hconv : Convex ℝ K) (hclosed : IsClosed K) {a : V n} {A : MatR n}
    (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    (hrho : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖) : A.det < rStar := by
  by_cases hhalf : Spectral.minEigenvalue hA.isHermitian = (1 / 2 : ℝ)
  · apply det_lt_rStar_at_half hA hhalf
    have h := r01_constraint_one hK hconv hclosed hA hell hrho rfl
    change Scalar.f1 (Spectral.minEigenvalue hA.isHermitian) + _ ≤ (n : ℝ) at h
    rwa [hhalf, Scalar.f1_half] at h
  · exact (r02_exp_bounds hK hconv hclosed hA hell hrho rfl).trans_lt
      (Scalar.joint_lt_of_ne_half (Spectral.minEigenvalue_pos hA) hhalf)

theorem normalized_cut_det_lt {K : Set (V n)} (hK : IsConvexBody K)
    {c p : V n} {S : MatR n} (hmax : IsMaxDet K c S) (hp : p ≠ 0)
    {a : V n} {A : MatR n}
    (hA : IsFeasible (normalizedBody (K ∩ centralHalfspace c p) c S) a A) :
    A.det < rStar := by
  have hb := hK.normalizedBody c hmax.posDef
  have hs := hA.2
  rw [normalizedBody_cut hmax.posDef] at hs
  exact normalized_det_lt_rStar hmax.isJohnNormalized hb.2.1 hb.1.isClosed hA.1
    (hs.trans inter_subset_left) (norm_inv_center_ge_one_of_halfspace hA.1
      (normalized_normal_ne_zero hmax.posDef hp) (hs.trans inter_subset_right))

theorem central_cut_candidate_volume_ratio_lt {K : Set (V n)} (hK : IsConvexBody K)
    {c p : V n} {S : MatR n} (hmax : IsMaxDet K c S) (hp : p ≠ 0)
    {a : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace c p) a A) :
    (volume (ellipsoid a A)).toReal / (maxEllipsoidVolume K).toReal < rStar := by
  have h := normalized_cut_det_lt hK hmax hp (hA.normalize c hmax.posDef)
  rw [normalized_shape_det hmax.posDef hA.1] at h
  rwa [volume_ellipsoid_real_ratio hmax hA.1]

/-- The geometric finite-dimensional bound is strict for any exact maximizing center. -/
theorem center_cut_volume_lt {K : Set (V n)} (hK : IsConvexBody K)
    {c p : V n} {S : MatR n} (hmax : IsMaxDet K c S) (hp : p ≠ 0) :
    (maxEllipsoidVolume (K ∩ centralHalfspace c p)).toReal <
      rStar * (maxEllipsoidVolume K).toReal := by
  have hcut := hK.centralCut hmax.center_mem_interior hp
  obtain ⟨a, A, hcutmax⟩ := exists_isMaxDet hcut
  rw [hcutmax.maxEllipsoidVolume_eq]
  exact (div_lt_iff₀ hmax.maxEllipsoidVolume_toReal_pos).mp
    (central_cut_candidate_volume_ratio_lt hK hmax hp hcutmax.feasible)

/-- T03: no finite positive dimension attains the uniform central-cut constant. -/
theorem t03 {K : Set (V n)} (hK : IsConvexBody K) {p : V n} (hp : p ≠ 0) :
    (maxEllipsoidVolume (K ∩ centralHalfspace (johnCenter K) p)).toReal <
      rStar * (maxEllipsoidVolume K).toReal :=
  center_cut_volume_lt hK (john_isMaxDet hK) hp

theorem john_center_cut_volume_ratio_lt {K : Set (V n)} (hK : IsConvexBody K)
    {p : V n} (hp : p ≠ 0) :
    (maxEllipsoidVolume (K ∩ centralHalfspace (johnCenter K) p)).toReal /
      (maxEllipsoidVolume K).toReal < rStar :=
  (div_lt_iff₀ (john_isMaxDet hK).maxEllipsoidVolume_toReal_pos).mpr (t03 hK hp)

end Khachiyan
