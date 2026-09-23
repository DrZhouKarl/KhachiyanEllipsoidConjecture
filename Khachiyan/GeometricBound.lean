import Khachiyan.Normalization

/-!
# T01: the geometric central-cut volume bound

This module implements T01 in Sections 1 and 5 of `proof.md`.
The bound applies in every positive dimension to actual Lebesgue volumes of
maximal inscribed ellipsoids. G04 normalizes an arbitrary feasible candidate,
and N01 supplies the determinant bound without extra spectral assumptions.
-/

noncomputable section

open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set MeasureTheory

namespace Khachiyan

variable {n : ℕ} [NeZero n]

/-- The normalized determinant estimate transported to an arbitrary central cut. -/
theorem central_cut_candidate_det_le {K : Set (V n)} (hK : IsConvexBody K)
    {c p : V n} {S : MatR n} (hmax : IsMaxDet K c S) (hp : p ≠ 0)
    {a : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace c p) a A) :
    A.det ≤ rStar * S.det := by
  have hd := normalized_cut_det_bound hK hmax hp (hA.normalize c hmax.posDef)
  rw [normalized_shape_det hmax.posDef hA.1] at hd
  exact (div_le_iff₀ hmax.posDef.det_pos).mp hd

/-- Every nondegenerate ellipsoid in the retained side satisfies the actual volume bound. -/
theorem central_cut_candidate_volume_le {K : Set (V n)} (hK : IsConvexBody K)
    {c p : V n} {S : MatR n} (hmax : IsMaxDet K c S) (hp : p ≠ 0)
    {a : V n} {A : MatR n} (hA : IsFeasible (K ∩ centralHalfspace c p) a A) :
    volume (ellipsoid a A) ≤ ENNReal.ofReal rStar * maxEllipsoidVolume K := by
  calc
    volume (ellipsoid a A) = ENNReal.ofReal A.det * volume (unitBall n) :=
      volume_ellipsoid_eq_det hA.1 a
    _ ≤ ENNReal.ofReal (rStar * S.det) * volume (unitBall n) := by
      gcongr
      exact central_cut_candidate_det_le hK hmax hp hA
    _ = ENNReal.ofReal rStar * maxEllipsoidVolume K := by
      rw [ENNReal.ofReal_mul rStar_pos.le, hmax.maxEllipsoidVolume_eq_det, mul_assoc]

/-- T01 for a specified exact maximal inscribed ellipsoid. -/
theorem center_cut_volume_le {K : Set (V n)} (hK : IsConvexBody K)
    {c p : V n} {S : MatR n} (hmax : IsMaxDet K c S) (hp : p ≠ 0) :
    maxEllipsoidVolume (K ∩ centralHalfspace c p) ≤
      ENNReal.ofReal rStar * maxEllipsoidVolume K := by
  have hcut := hK.centralCut hmax.center_mem_interior hp
  obtain ⟨a, A, hcutmax⟩ := exists_isMaxDet hcut
  rw [hcutmax.maxEllipsoidVolume_eq]
  exact central_cut_candidate_volume_le hK hmax hp hcutmax.feasible

/-- The unique maximizing parameter pair for a convex body.
The default outside the convex-body domain is irrelevant to the theorems below. -/
def johnParameters (K : Set (V n)) : V n × MatR n := by
  classical
  exact if hK : IsConvexBody K then (existsUnique_isMaxDet hK).exists.choose else (0, 1)

/-- The center of the maximum-volume inscribed ellipsoid. -/
def johnCenter (K : Set (V n)) : V n := (johnParameters K).1

/-- The positive-definite shape of the maximum-volume inscribed ellipsoid. -/
def johnShape (K : Set (V n)) : MatR n := (johnParameters K).2

/-- The canonical maximum-volume inscribed ellipsoid of a convex body. -/
def johnEllipsoid (K : Set (V n)) : Set (V n) :=
  ellipsoid (johnCenter K) (johnShape K)

theorem john_isMaxDet {K : Set (V n)} (hK : IsConvexBody K) :
    IsMaxDet K (johnCenter K) (johnShape K) := by
  classical
  change IsMaxDet K (johnParameters K).1 (johnParameters K).2
  simpa only [johnParameters, dite_eq_left hK] using (existsUnique_isMaxDet hK).exists.choose_spec

theorem johnCenter_eq_of_isMaxDet {K : Set (V n)} (hK : IsConvexBody K)
    {c : V n} {S : MatR n} (hmax : IsMaxDet K c S) : johnCenter K = c :=
  (isMaxDet_unique hK.2.1 hK.1.isClosed (john_isMaxDet hK) hmax).1

theorem johnShape_eq_of_isMaxDet {K : Set (V n)} (hK : IsConvexBody K)
    {c : V n} {S : MatR n} (hmax : IsMaxDet K c S) : johnShape K = S :=
  (isMaxDet_unique hK.2.1 hK.1.isClosed (john_isMaxDet hK) hmax).2

theorem johnShape_posDef {K : Set (V n)} (hK : IsConvexBody K) :
    (johnShape K).PosDef := (john_isMaxDet hK).posDef

theorem johnEllipsoid_subset {K : Set (V n)} (hK : IsConvexBody K) :
    johnEllipsoid K ⊆ K := (john_isMaxDet hK).subset

theorem volume_johnEllipsoid {K : Set (V n)} (hK : IsConvexBody K) :
    volume (johnEllipsoid K) = maxEllipsoidVolume K :=
  (john_isMaxDet hK).maxEllipsoidVolume_eq.symm

theorem johnCenter_mem_interior {K : Set (V n)} (hK : IsConvexBody K) :
    johnCenter K ∈ interior K := (john_isMaxDet hK).center_mem_interior

/-- Feasible parameters maximize the determinant exactly when they attain actual maximal volume. -/
theorem isMaxDet_iff_attains_volume {K : Set (V n)} {c : V n} {S : MatR n}
    (hS : IsFeasible K c S) :
    IsMaxDet K c S ↔ volume (ellipsoid c S) = maxEllipsoidVolume K := by
  constructor
  · intro h
    exact h.maxEllipsoidVolume_eq.symm
  · intro hv
    refine ⟨hS, fun a A hA => ?_⟩
    have hle : volume (ellipsoid a A) ≤ volume (ellipsoid c S) := by
      rw [hv]
      exact volume_le_maxEllipsoidVolume hA
    have hratio : volume (ellipsoid a A) / volume (unitBall n) ≤
        volume (ellipsoid c S) / volume (unitBall n) := by
      gcongr
    rw [volume_ellipsoid_div_unitBall hA.1, volume_ellipsoid_div_unitBall hS.1] at hratio
    exact (ENNReal.ofReal_le_ofReal_iff hS.1.det_pos.le).mp hratio

/-- Uniqueness also holds when maximality is expressed solely using Lebesgue volume. -/
theorem john_eq_of_volume_maximal {K : Set (V n)} (hK : IsConvexBody K)
    {a : V n} {A : MatR n} (hA : IsFeasible K a A)
    (hv : volume (ellipsoid a A) = maxEllipsoidVolume K) :
    johnCenter K = a ∧ johnShape K = A :=
  isMaxDet_unique hK.2.1 hK.1.isClosed (john_isMaxDet hK)
    ((isMaxDet_iff_attains_volume hA).mpr hv)

theorem john_center_cut_isConvexBody {K : Set (V n)} (hK : IsConvexBody K)
    {p : V n} (hp : p ≠ 0) :
    IsConvexBody (K ∩ centralHalfspace (johnCenter K) p) :=
  hK.centralCut (johnCenter_mem_interior hK) hp

/-- The central-cut inequality at the canonical maximum-volume ellipsoid center. -/
theorem john_center_cut_volume_le {K : Set (V n)} (hK : IsConvexBody K)
    {p : V n} (hp : p ≠ 0) :
    maxEllipsoidVolume (K ∩ centralHalfspace (johnCenter K) p) ≤
      ENNReal.ofReal rStar * maxEllipsoidVolume K :=
  center_cut_volume_le hK (john_isMaxDet hK) hp

/-- T01: in every positive dimension the retained side is a convex body and
its maximal inscribed-ellipsoid volume is at most `exp (1/2) / 2` times the original. -/
theorem t01 {K : Set (V n)} (hK : IsConvexBody K) {p : V n} (hp : p ≠ 0) :
    IsConvexBody (K ∩ centralHalfspace (johnCenter K) p) ∧
      maxEllipsoidVolume (K ∩ centralHalfspace (johnCenter K) p) ≤
        ENNReal.ofReal rStar * maxEllipsoidVolume K :=
  ⟨john_center_cut_isConvexBody hK hp, john_center_cut_volume_le hK hp⟩

/-- The actual-volume inequality as a real inequality; both volumes are finite. -/
theorem john_center_cut_volume_le_real {K : Set (V n)} (hK : IsConvexBody K)
    {p : V n} (hp : p ≠ 0) :
    (maxEllipsoidVolume (K ∩ centralHalfspace (johnCenter K) p)).toReal ≤
      rStar * (maxEllipsoidVolume K).toReal := by
  have hleft : maxEllipsoidVolume (K ∩ centralHalfspace (johnCenter K) p) < ∞ :=
    (john_center_cut_isConvexBody hK hp).maxEllipsoidVolume_lt_top
  have hright : ENNReal.ofReal rStar * maxEllipsoidVolume K < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.maxEllipsoidVolume_lt_top
  have h := (ENNReal.toReal_le_toReal hleft.ne hright.ne).mpr
    (john_center_cut_volume_le hK hp)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal rStar_pos.le] using h

/-- The dimension-independent ratio bound, with a proved positive finite denominator. -/
theorem john_center_cut_volume_ratio_le {K : Set (V n)} (hK : IsConvexBody K)
    {p : V n} (hp : p ≠ 0) :
    (maxEllipsoidVolume (K ∩ centralHalfspace (johnCenter K) p)).toReal /
        (maxEllipsoidVolume K).toReal ≤ rStar :=
  (div_le_iff₀ (john_isMaxDet hK).maxEllipsoidVolume_toReal_pos).mpr
    (john_center_cut_volume_le_real hK hp)

end Khachiyan
