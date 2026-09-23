import Khachiyan.GeometricBound
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.Compact

/-!
# T03: the exact one-dimensional cutting ratio

This module proves the one-dimensional assertion of T03 in `proof.md`.
The Euclidean line is identified with the real line by an explicit homeomorphism;
all volumes remain the project's actual Lebesgue volumes.
-/

noncomputable section
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set MeasureTheory

namespace Khachiyan.OneDimensional

def point (t : ℝ) : V 1 := WithLp.toLp 2 (fun _ => t)

@[simp] theorem point_apply (t : ℝ) (i : Fin 1) : point t i = t := rfl

@[simp] theorem point_coordinate (x : V 1) : point (x 0) = x := by
  ext i
  rw [Subsingleton.elim i 0]
  rfl

theorem norm_point (t : ℝ) : ‖point t‖ = |t| := by
  simp [EuclideanSpace.norm_eq, point, Real.sqrt_sq_eq_abs]

theorem norm_eq_abs_coordinate (x : V 1) : ‖x‖ = |x 0| := by
  calc
    ‖x‖ = ‖point (x 0)‖ := congrArg norm (point_coordinate x).symm
    _ = |x 0| := norm_point _

theorem inner_eq_coordinate (x y : V 1) : ⟪x, y⟫ = x 0 * y 0 := by
  simp [inner_eq_dotProduct, dotProduct]

def lineHomeomorph : ℝ ≃ₜ V 1 where
  toFun := point
  invFun := fun x => x 0
  left_inv := fun _ => rfl
  right_inv := point_coordinate
  continuous_toFun := by unfold point; fun_prop
  continuous_invFun := by fun_prop

theorem scalar_shape_action (s : ℝ) (y : V 1) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (s • (1 : MatR 1)) y = s • y := by simp

theorem mem_scalar_ellipsoid {a x : V 1} {s : ℝ} (hs : 0 < s) :
    x ∈ ellipsoid a (s • (1 : MatR 1)) ↔ a 0 - s ≤ x 0 ∧ x 0 ≤ a 0 + s := by
  rw [mem_ellipsoid]
  constructor
  · rintro ⟨y, hy, he⟩
    have he0 := congrArg (fun z : V 1 => z 0) he
    simp only [scalar_shape_action, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at he0
    rw [norm_eq_abs_coordinate, abs_le] at hy
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hy.1 hs.le,
      mul_le_mul_of_nonneg_left hy.2 hs.le]
  · rintro ⟨hl, hu⟩
    refine ⟨point ((x 0 - a 0) / s), ?_, ?_⟩
    · rw [norm_point, abs_le]
      constructor
      · apply (le_div_iff₀ hs).mpr
        linarith
      · apply (div_le_iff₀ hs).mpr
        linarith
    · rw [scalar_shape_action]
      ext i
      rw [Subsingleton.elim i 0]
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, point_apply]
      field_simp
      ring

theorem exists_interval {K : Set (V 1)} (hK : IsConvexBody K) :
    ∃ l u : ℝ, l < u ∧ K = {x | l ≤ x 0 ∧ x 0 ≤ u} := by
  let e := lineHomeomorph.symm
  let S : Set ℝ := e '' K
  have hcompact : IsCompact S := hK.1.image e.continuous
  have hconv : Convex ℝ S := by
    rintro x ⟨v, hv, rfl⟩ y ⟨w, hw, rfl⟩ a b ha hb hab
    exact ⟨a • v + b • w, hK.2.1 hv hw ha hb hab, rfl⟩
  have hne : S.Nonempty := (hK.2.2.mono interior_subset).image e
  have hset : S = Icc (sInf S) (sSup S) :=
    eq_Icc_of_connected_compact (hconv.isConnected hne) hcompact
  have hInt : (interior S).Nonempty := by
    change (interior (e '' K)).Nonempty
    rw [← e.image_interior]
    exact hK.2.2.image e
  have hlt : sInf S < sSup S := by
    rw [hset, interior_Icc] at hInt
    exact nonempty_Ioo.mp hInt
  refine ⟨sInf S, sSup S, hlt, ?_⟩
  ext x
  have hm : x ∈ K ↔ e x ∈ S := e.injective.mem_set_image.symm
  rw [hm]
  conv_lhs => rw [hset]
  rfl

theorem exists_eq_scalar_ellipsoid {K : Set (V 1)} (hK : IsConvexBody K) :
    ∃ c : V 1, ∃ s : ℝ, 0 < s ∧ K = ellipsoid c (s • (1 : MatR 1)) := by
  obtain ⟨l, u, hlu, hKset⟩ := exists_interval hK
  have hs : 0 < (u - l) / 2 := by linarith
  refine ⟨point ((l + u) / 2), (u - l) / 2, hs, ?_⟩
  rw [hKset]
  ext x
  rw [mem_scalar_ellipsoid hs]
  simp only [mem_ofPred_eq, point_apply]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith

theorem scalar_ellipsoid_isMaxDet (c : V 1) {s : ℝ} (hs : 0 < s) :
    IsMaxDet (ellipsoid c (s • (1 : MatR 1))) c (s • 1) := by
  have hf : IsFeasible (ellipsoid c (s • (1 : MatR 1))) c (s • 1) :=
    ⟨Matrix.PosDef.one.smul hs, Subset.rfl⟩
  apply (isMaxDet_iff_attains_volume hf).mpr
  exact le_antisymm (volume_le_maxEllipsoidVolume hf) (maxEllipsoidVolume_le_volume _)

theorem johnEllipsoid_eq {K : Set (V 1)} (hK : IsConvexBody K) : johnEllipsoid K = K := by
  obtain ⟨c, s, hs, hKeq⟩ := exists_eq_scalar_ellipsoid hK
  have hmax : IsMaxDet K c (s • (1 : MatR 1)) := by
    rw [hKeq]
    exact scalar_ellipsoid_isMaxDet c hs
  rw [johnEllipsoid, johnCenter_eq_of_isMaxDet hK hmax,
    johnShape_eq_of_isMaxDet hK hmax, ← hKeq]

theorem maxEllipsoidVolume_eq_volume {K : Set (V 1)} (hK : IsConvexBody K) :
    maxEllipsoidVolume K = volume K := by
  rw [← volume_johnEllipsoid hK, johnEllipsoid_eq hK]

theorem scalar_cut_of_pos (c p : V 1) {s : ℝ} (hs : 0 < s) (hp : 0 < p 0) :
    ellipsoid c (s • (1 : MatR 1)) ∩ centralHalfspace c p =
      ellipsoid (c + point (s / 2)) ((s / 2) • (1 : MatR 1)) := by
  ext x
  simp only [mem_inter_iff, mem_scalar_ellipsoid hs, mem_scalar_ellipsoid (half_pos hs),
    centralHalfspace, mem_ofPred_eq, inner_eq_coordinate, PiLp.sub_apply, PiLp.add_apply,
    point_apply, mul_nonneg_iff_of_pos_left hp]
  constructor
  · rintro ⟨⟨hl, hu⟩, hp⟩
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

theorem scalar_cut_of_neg (c p : V 1) {s : ℝ} (hs : 0 < s) (hp : p 0 < 0) :
    ellipsoid c (s • (1 : MatR 1)) ∩ centralHalfspace c p =
      ellipsoid (c - point (s / 2)) ((s / 2) • (1 : MatR 1)) := by
  ext x
  simp only [mem_inter_iff, mem_scalar_ellipsoid hs, mem_scalar_ellipsoid (half_pos hs),
    centralHalfspace, mem_ofPred_eq, inner_eq_coordinate, PiLp.sub_apply, point_apply]
  rw [show p 0 * (x 0 - c 0) = (-p 0) * (c 0 - x 0) by ring,
    mul_nonneg_iff_of_pos_left (neg_pos.mpr hp)]
  constructor
  · rintro ⟨⟨hl, hu⟩, hp⟩
    constructor <;> linarith
  · rintro ⟨hl, hu⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

theorem coordinate_ne_zero {p : V 1} (hp : p ≠ 0) : p 0 ≠ 0 := by
  intro h
  apply hp
  calc
    p = point (p 0) := (point_coordinate p).symm
    _ = point 0 := by rw [h]
    _ = 0 := rfl

theorem scalar_cut_eq_half_ellipsoid (c p : V 1) {s : ℝ} (hs : 0 < s) (hp : p ≠ 0) :
    ∃ d : V 1, ellipsoid c (s • (1 : MatR 1)) ∩ centralHalfspace c p =
      ellipsoid d ((s / 2) • (1 : MatR 1)) := by
  rcases (coordinate_ne_zero hp).lt_or_gt with hneg | hpos
  · exact ⟨_, scalar_cut_of_neg c p hs hneg⟩
  · exact ⟨_, scalar_cut_of_pos c p hs hpos⟩

theorem scalar_cut_volume_eq_half (c p : V 1) {s : ℝ} (hs : 0 < s) (hp : p ≠ 0) :
    maxEllipsoidVolume (ellipsoid c (s • (1 : MatR 1)) ∩ centralHalfspace c p) =
      ENNReal.ofReal (1 / 2 : ℝ) * maxEllipsoidVolume (ellipsoid c (s • (1 : MatR 1))) := by
  obtain ⟨d, hcut⟩ := scalar_cut_eq_half_ellipsoid c p hs hp
  rw [hcut, (scalar_ellipsoid_isMaxDet d (half_pos hs)).maxEllipsoidVolume_eq_det,
    (scalar_ellipsoid_isMaxDet c hs).maxEllipsoidVolume_eq_det]
  simp only [Matrix.det_smul, Fintype.card_fin, pow_one, Matrix.det_one, mul_one]
  rw [show s / 2 = (1 / 2 : ℝ) * s by ring, ENNReal.ofReal_mul (by norm_num), mul_assoc]

/-- T03 in dimension one: every central cut halves the actual maximal-ellipsoid volume. -/
theorem center_cut_volume_eq_half {K : Set (V 1)} (hK : IsConvexBody K)
    {p : V 1} (hp : p ≠ 0) :
    maxEllipsoidVolume (K ∩ centralHalfspace (johnCenter K) p) =
      ENNReal.ofReal (1 / 2 : ℝ) * maxEllipsoidVolume K := by
  obtain ⟨c, s, hs, hKeq⟩ := exists_eq_scalar_ellipsoid hK
  have hmax : IsMaxDet K c (s • (1 : MatR 1)) := by
    rw [hKeq]
    exact scalar_ellipsoid_isMaxDet c hs
  rw [johnCenter_eq_of_isMaxDet hK hmax, hKeq]
  exact scalar_cut_volume_eq_half c p hs hp

theorem center_cut_volume_ratio_eq_half {K : Set (V 1)} (hK : IsConvexBody K)
    {p : V 1} (hp : p ≠ 0) :
    (maxEllipsoidVolume (K ∩ centralHalfspace (johnCenter K) p)).toReal /
        (maxEllipsoidVolume K).toReal = (1 / 2 : ℝ) := by
  have hden : 0 < (maxEllipsoidVolume K).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hK.maxEllipsoidVolume_pos, hK.maxEllipsoidVolume_lt_top⟩
  have hcutfin := (john_center_cut_isConvexBody hK hp).maxEllipsoidVolume_lt_top
  have hrightfin : ENNReal.ofReal (1 / 2 : ℝ) * maxEllipsoidVolume K < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.maxEllipsoidVolume_lt_top
  have heq : (maxEllipsoidVolume (K ∩ centralHalfspace (johnCenter K) p)).toReal =
      (ENNReal.ofReal (1 / 2 : ℝ) * maxEllipsoidVolume K).toReal := by
    apply le_antisymm
    · exact (ENNReal.toReal_le_toReal hcutfin.ne hrightfin.ne).mpr
        (center_cut_volume_eq_half hK hp).le
    · exact (ENNReal.toReal_le_toReal hrightfin.ne hcutfin.ne).mpr
        (center_cut_volume_eq_half hK hp).ge
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] at heq
  rw [heq]
  field_simp

theorem sharp_half {r : ℝ} (hr : r < (1 / 2 : ℝ)) :
    ∃ (K : Set (V 1)) (p : V 1), IsConvexBody K ∧ p ≠ 0 ∧
      r * (maxEllipsoidVolume K).toReal <
        (maxEllipsoidVolume (K ∩ centralHalfspace (johnCenter K) p)).toReal := by
  have hK : IsConvexBody (unitBall 1) := by
    refine ⟨isCompact_closedBall _ _, convex_closedBall _ _, ⟨0, ?_⟩⟩
    rw [unitBall, interior_closedBall (0 : V 1) one_ne_zero]
    simp
  have hp : point 1 ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : V 1 => x 0) h
    norm_num at h0
  refine ⟨unitBall 1, point 1, hK, hp, ?_⟩
  apply (lt_div_iff₀ (john_isMaxDet hK).maxEllipsoidVolume_toReal_pos).mp
  rwa [center_cut_volume_ratio_eq_half hK hp]

end Khachiyan.OneDimensional
