import Khachiyan.JohnUniqueness
import Khachiyan.NormalizedBound

/-!
# G04: affine normalization and center exclusion

This module implements G04 of `proof.md` and `formalization_plan.md`.
All affine transports act on Euclidean space. General linear images of shape
matrices are converted to positive-definite shapes with `affineShape`.
-/

noncomputable section

open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set MeasureTheory

namespace Khachiyan

variable {n : ℕ}

private theorem action_mul (A B : MatR n) (x : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (A * B) x =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A
        (Matrix.toEuclideanCLM (𝕜 := ℝ) B x) :=
  congrArg (fun f => f x) ((Matrix.toEuclideanCLM (𝕜 := ℝ)).map_mul A B)

private theorem action_inv_action {A : MatR n} (hA : A.PosDef) (x : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A x) = x := by
  rw [← action_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')]
  simp

private theorem action_action_inv {A : MatR n} (hA : A.PosDef) (x : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) A
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ x) = x := by
  rw [← action_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')]
  simp

/-- The forward map sending the specified ellipsoid to the unit ball. -/
def normalizePoint (c : V n) (S : MatR n) (x : V n) : V n :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ (x - c)

/-- The inverse affine map from normalized coordinates. -/
def denormalizePoint (c : V n) (S : MatR n) (y : V n) : V n :=
  c + Matrix.toEuclideanCLM (𝕜 := ℝ) S y

@[simp] theorem normalize_denormalize {S : MatR n} (hS : S.PosDef)
    (c y : V n) : normalizePoint c S (denormalizePoint c S y) = y := by
  simp only [normalizePoint, denormalizePoint, add_sub_cancel_left]
  exact action_inv_action hS y

@[simp] theorem denormalize_normalize {S : MatR n} (hS : S.PosDef)
    (c x : V n) : denormalizePoint c S (normalizePoint c S x) = x := by
  rw [denormalizePoint, normalizePoint, action_action_inv hS]
  abel

/-- Normalization as a genuine homeomorphism, including its explicit inverse. -/
def normalizationHomeomorph (c : V n) {S : MatR n} (hS : S.PosDef) : V n ≃ₜ V n where
  toFun := normalizePoint c S
  invFun := denormalizePoint c S
  left_inv := denormalize_normalize hS c
  right_inv := normalize_denormalize hS c
  continuous_toFun := (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹).continuous.comp
    (continuous_id.sub continuous_const)
  continuous_invFun := continuous_const.add (Matrix.toEuclideanCLM (𝕜 := ℝ) S).continuous

theorem normalize_ellipsoid_self {S : MatR n} (hS : S.PosDef) (c : V n) :
    normalizePoint c S '' ellipsoid c S = unitBall n := by
  change normalizePoint c S '' (denormalizePoint c S '' unitBall n) = unitBall n
  simp only [image_image, normalize_denormalize hS, image_id']

theorem mem_interior_ellipsoid_iff {a : V n} {A : MatR n} (hA : A.PosDef) :
    0 ∈ interior (ellipsoid a A) ↔
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖ < 1 := by
  let e := normalizationHomeomorph a hA
  have hi := e.image_interior (ellipsoid a A)
  have he : e '' ellipsoid a A = unitBall n := normalize_ellipsoid_self hA a
  rw [he, unitBall, interior_closedBall (0 : V n) one_ne_zero] at hi
  have hm : (0 : V n) ∈ interior (ellipsoid a A) ↔
      e 0 ∈ e '' interior (ellipsoid a A) := e.injective.mem_set_image.symm
  rw [hm, hi]
  change normalizePoint a A 0 ∈ Metric.ball 0 1 ↔ _
  simp [normalizePoint, Metric.mem_ball]

theorem center_exclusion_iff {a : V n} {A : MatR n} (hA : A.PosDef) :
    0 ∉ interior (ellipsoid a A) ↔
      1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖ := by
  rw [mem_interior_ellipsoid_iff hA, not_lt]

/-- The pointwise form also proves that an ellipsoid contains its center in its interior. -/
theorem mem_interior_ellipsoid_iff_norm {a x : V n} {A : MatR n} (hA : A.PosDef) :
    x ∈ interior (ellipsoid a A) ↔ ‖normalizePoint a A x‖ < 1 := by
  let e := normalizationHomeomorph a hA
  have hi := e.image_interior (ellipsoid a A)
  have he : e '' ellipsoid a A = unitBall n := normalize_ellipsoid_self hA a
  rw [he, unitBall, interior_closedBall (0 : V n) one_ne_zero] at hi
  have hm : x ∈ interior (ellipsoid a A) ↔
      e x ∈ e '' interior (ellipsoid a A) := e.injective.mem_set_image.symm
  rw [hm, hi]
  change normalizePoint a A x ∈ Metric.ball 0 1 ↔ _
  simp [Metric.mem_ball]

theorem center_mem_interior_ellipsoid {A : MatR n} (hA : A.PosDef) (a : V n) :
    a ∈ interior (ellipsoid a A) := by
  rw [mem_interior_ellipsoid_iff_norm hA]
  simp [normalizePoint]

theorem IsMaxDet.center_mem_interior {K : Set (V n)} {c : V n} {S : MatR n}
    (h : IsMaxDet K c S) : c ∈ interior K :=
  interior_mono h.subset (center_mem_interior_ellipsoid h.posDef c)

/-- The minimum support value characterizes containment in a central halfspace. -/
theorem ellipsoid_subset_centralHalfspace_zero_iff {a p : V n} {A : MatR n}
    (hA : A.IsSymm) :
    ellipsoid a A ⊆ centralHalfspace 0 p ↔
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A p‖ ≤ ⟪p, a⟫ := by
  constructor
  · intro h
    obtain ⟨x, hx, heq⟩ := ellipsoid_support_attained (a := a) hA (-p)
    have hx' : 0 ≤ ⟪p, x⟫ := by simpa [centralHalfspace] using h hx
    simp only [inner_neg_left, map_neg, norm_neg] at heq
    linarith
  · intro h x hx
    have hu := ellipsoid_support_le hA (v := -p) hx
    simp only [inner_neg_left, map_neg, norm_neg] at hu
    change 0 ≤ ⟪p, x - 0⟫
    simp only [sub_zero]
    linarith

theorem norm_inv_center_ge_one_of_halfspace {a p : V n} {A : MatR n}
    (hA : A.PosDef) (hp : p ≠ 0)
    (hsub : ellipsoid a A ⊆ centralHalfspace 0 p) :
    1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖ := by
  have hsupport := (ellipsoid_subset_centralHalfspace_zero_iff hA.isHermitian.isSymm).mp hsub
  have hAp : Matrix.toEuclideanCLM (𝕜 := ℝ) A p ≠ 0 := by
    intro h
    have hh := action_inv_action hA p
    rw [h, map_zero] at hh
    exact hp hh.symm
  have hid : ⟪p, a⟫ = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A p,
      Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a⟫ := by
    rw [← inner_matrix_action_symm hA.isHermitian.isSymm, action_action_inv hA]
  rw [hid] at hsupport
  have hcs := real_inner_le_norm (Matrix.toEuclideanCLM (𝕜 := ℝ) A p)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a)
  have hpos := norm_pos_iff.mpr hAp
  nlinarith

/-- The explicit separating normal is the Euclidean action of `A⁻²` on the center. -/
theorem inverse_square_normal_separates {a : V n} {A : MatR n}
    (hA : A.PosDef) (hrho : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖) :
    let v := Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a)
    v ≠ 0 ∧ ellipsoid a A ⊆ centralHalfspace 0 v := by
  let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a
  let v := Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ b
  have hAv : Matrix.toEuclideanCLM (𝕜 := ℝ) A v = b := action_action_inv hA b
  have hv : v ≠ 0 := by
    intro h
    rw [h, map_zero] at hAv
    have hb : b = 0 := hAv.symm
    change 1 ≤ ‖b‖ at hrho
    norm_num [hb] at hrho
  refine ⟨hv, (ellipsoid_subset_centralHalfspace_zero_iff hA.isHermitian.isSymm).mpr ?_⟩
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖ ≤ ⟪v, a⟫
  have hi : ⟪v, a⟫ = ‖b‖ ^ 2 := by
    dsimp [v]
    rw [← inner_matrix_action_symm hA.inv.isHermitian.isSymm]
    exact real_inner_self_eq_norm_sq b
  rw [hAv, hi]
  change 1 ≤ ‖b‖ at hrho
  nlinarith

theorem center_exclusion_iff_exists_halfspace {a : V n} {A : MatR n}
    (hA : A.PosDef) :
    0 ∉ interior (ellipsoid a A) ↔
      ∃ p : V n, p ≠ 0 ∧ ellipsoid a A ⊆ centralHalfspace 0 p := by
  rw [center_exclusion_iff hA]
  constructor
  · intro h
    exact ⟨_, inverse_square_normal_separates hA h⟩
  · rintro ⟨p, hp, hsub⟩
    exact norm_inv_center_ge_one_of_halfspace hA hp hsub

/-- The full body in coordinates centered at the specified ellipsoid. -/
def normalizedBody (K : Set (V n)) (c : V n) (S : MatR n) : Set (V n) :=
  normalizePoint c S '' K

theorem normalizedBody_eq_preimage {S : MatR n} (hS : S.PosDef)
    (K : Set (V n)) (c : V n) :
    normalizedBody K c S = denormalizePoint c S ⁻¹' K := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_preimage, denormalize_normalize hS] using hx
  · intro hy
    exact ⟨denormalizePoint c S y, hy, normalize_denormalize hS c y⟩

theorem denormalize_normalizedBody {S : MatR n} (hS : S.PosDef)
    (K : Set (V n)) (c : V n) :
    denormalizePoint c S '' normalizedBody K c S = K := by
  simp only [normalizedBody, image_image, denormalize_normalize hS, image_id']

theorem normalizedBody_convex {K : Set (V n)} (hK : Convex ℝ K)
    (c : V n) {S : MatR n} (hS : S.PosDef) :
    Convex ℝ (normalizedBody K c S) := by
  rw [normalizedBody_eq_preimage hS]
  exact (hK.translate_preimage_right c).linear_preimage
    (Matrix.toEuclideanCLM (𝕜 := ℝ) S).toLinearMap

theorem IsConvexBody.normalizedBody {K : Set (V n)} (hK : IsConvexBody K)
    (c : V n) {S : MatR n} (hS : S.PosDef) :
    IsConvexBody (normalizedBody K c S) := by
  let e := normalizationHomeomorph c hS
  refine ⟨hK.1.image e.continuous, normalizedBody_convex hK.2.1 c hS, ?_⟩
  change (interior (e '' K)).Nonempty
  rw [← e.image_interior]
  exact hK.2.2.image e

/-- Restore a symmetric shape after a general, possibly noncommuting, affine image. -/
theorem denormalize_ellipsoid (c a : V n) (S A : MatR n) :
    denormalizePoint c S '' ellipsoid a A =
      ellipsoid (denormalizePoint c S a) (affineShape (S * A)) := by
  rw [← affine_image_unitBall_eq_ellipsoid, ellipsoid, image_image]
  congr 1
  funext y
  simp [denormalizePoint, map_add, add_assoc]

theorem normalize_ellipsoid (c a : V n) (S A : MatR n) :
    normalizePoint c S '' ellipsoid a A =
      ellipsoid (normalizePoint c S a) (affineShape (S⁻¹ * A)) := by
  rw [← affine_image_unitBall_eq_ellipsoid, ellipsoid, image_image]
  congr 1
  funext y
  simp only [normalizePoint, map_sub, map_add, action_mul]
  abel

private theorem product_det_isUnit {S A : MatR n} (hS : S.PosDef) (hA : A.PosDef) :
    IsUnit (S * A).det := by
  rw [Matrix.det_mul]
  exact isUnit_iff_ne_zero.mpr (mul_pos hS.det_pos hA.det_pos).ne'

theorem denormalized_shape_posDef {S A : MatR n} (hS : S.PosDef) (hA : A.PosDef) :
    (affineShape (S * A)).PosDef :=
  affineShape_posDef (product_det_isUnit hS hA)

theorem normalized_shape_posDef {S A : MatR n} (hS : S.PosDef) (hA : A.PosDef) :
    (affineShape (S⁻¹ * A)).PosDef :=
  denormalized_shape_posDef hS.inv hA

variable [NeZero n]

theorem denormalized_shape_det {S A : MatR n} (hS : S.PosDef) (hA : A.PosDef) :
    (affineShape (S * A)).det = S.det * A.det := by
  rw [affineShape_det (product_det_isUnit hS hA), Matrix.det_mul,
    abs_of_pos (mul_pos hS.det_pos hA.det_pos)]

theorem normalized_shape_det {S A : MatR n} (hS : S.PosDef) (hA : A.PosDef) :
    (affineShape (S⁻¹ * A)).det = A.det / S.det := by
  rw [denormalized_shape_det hS.inv hA, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  ring

omit [NeZero n] in
theorem IsFeasible.normalize {K : Set (V n)} {a : V n} {A S : MatR n}
    (h : IsFeasible K a A) (c : V n) (hS : S.PosDef) :
    IsFeasible (normalizedBody K c S) (normalizePoint c S a)
      (affineShape (S⁻¹ * A)) := by
  refine ⟨normalized_shape_posDef hS h.1, ?_⟩
  rw [← normalize_ellipsoid]
  exact Set.image_mono h.2

omit [NeZero n] in
theorem IsFeasible.denormalize {K : Set (V n)} {a c : V n} {A S : MatR n}
    (h : IsFeasible (normalizedBody K c S) a A) (hS : S.PosDef) :
    IsFeasible K (denormalizePoint c S a) (affineShape (S * A)) := by
  refine ⟨denormalized_shape_posDef hS h.1, ?_⟩
  rw [← denormalize_ellipsoid, ← denormalize_normalizedBody hS K c]
  exact Set.image_mono h.2

theorem IsMaxDet.isJohnNormalized {K : Set (V n)} {c : V n} {S : MatR n}
    (h : IsMaxDet K c S) : IsJohnNormalized (normalizedBody K c S) := by
  refine ⟨⟨Matrix.PosDef.one, ?_⟩, ?_⟩
  · rw [ellipsoid_zero_one, ← normalize_ellipsoid_self h.posDef c]
    exact Set.image_mono h.subset
  · intro a A hA
    have hd := h.det_le _ _ (hA.denormalize h.posDef)
    rw [denormalized_shape_det h.posDef hA.1] at hd
    simp only [Matrix.det_one]
    nlinarith [h.posDef.det_pos]

omit [NeZero n] in
/-- Determinant maximality attains the supremum of actual Lebesgue volumes. -/
theorem IsMaxDet.maxEllipsoidVolume_eq {K : Set (V n)} {c : V n} {S : MatR n}
    (h : IsMaxDet K c S) : maxEllipsoidVolume K = volume (ellipsoid c S) := by
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun A => iSup_le fun hA => ?_
    rw [volume_ellipsoid_eq_det hA.1 a, volume_ellipsoid_eq_det h.posDef c]
    gcongr
    exact h.det_le a A hA
  · exact volume_le_maxEllipsoidVolume h.feasible

omit [NeZero n] in
theorem IsMaxDet.maxEllipsoidVolume_eq_det {K : Set (V n)} {c : V n} {S : MatR n}
    (h : IsMaxDet K c S) :
    maxEllipsoidVolume K = ENNReal.ofReal S.det * volume (unitBall n) := by
  rw [h.maxEllipsoidVolume_eq, volume_ellipsoid_eq_det h.posDef]

theorem IsConvexBody.exists_maxEllipsoidVolume {K : Set (V n)} (hK : IsConvexBody K) :
    ∃ c S, IsMaxDet K c S ∧ maxEllipsoidVolume K = volume (ellipsoid c S) := by
  obtain ⟨c, S, h⟩ := exists_isMaxDet hK
  exact ⟨c, S, h, h.maxEllipsoidVolume_eq⟩

theorem IsConvexBody.maxEllipsoidVolume_pos {K : Set (V n)} (hK : IsConvexBody K) :
    0 < maxEllipsoidVolume K := by
  obtain ⟨c, S, h, heq⟩ := hK.exists_maxEllipsoidVolume
  rw [heq]
  exact volume_ellipsoid_pos h.posDef

omit [NeZero n] in
theorem volume_denormalizePoint {S : MatR n} (hS : S.PosDef) (c : V n)
    (s : Set (V n)) :
    volume (denormalizePoint c S '' s) = ENNReal.ofReal S.det * volume s := by
  have he : denormalizePoint c S '' s =
      (fun x : V n => c + x) '' (Matrix.toEuclideanCLM (𝕜 := ℝ) S '' s) := by
    rw [image_image]
    rfl
  rw [he, volume_translate, volume_linear_image, abs_of_pos hS.det_pos]

omit [NeZero n] in
theorem volume_normalizePoint {S : MatR n} (hS : S.PosDef) (c : V n)
    (s : Set (V n)) :
    volume (normalizePoint c S '' s) = ENNReal.ofReal S.det⁻¹ * volume s := by
  have he : normalizePoint c S '' s = Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ ''
      ((fun x : V n => -c + x) '' s) := by
    rw [image_image]
    congr 1
    funext x
    simp only [normalizePoint, sub_eq_neg_add]
  rw [he, volume_linear_image, volume_translate, abs_of_pos hS.inv.det_pos,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv]

omit [NeZero n] in
/-- The common volume scale is positive and finite, so it cancels even for arbitrary sets. -/
theorem volume_normalize_ratio {S : MatR n} (hS : S.PosDef) (c : V n)
    (s t : Set (V n)) :
    volume (normalizePoint c S '' s) / volume (normalizePoint c S '' t) =
      volume s / volume t := by
  rw [volume_normalizePoint hS, volume_normalizePoint hS]
  exact ENNReal.mul_div_mul_left _ _
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hS.det_pos)).ne' ENNReal.ofReal_ne_top

theorem volume_ellipsoid_div_unitBall {A : MatR n} (hA : A.PosDef) (a : V n) :
    volume (ellipsoid a A) / volume (unitBall n) = ENNReal.ofReal A.det := by
  rw [volume_ellipsoid_eq_det hA]
  exact ENNReal.mul_div_cancel_right unitBall_volume_pos.ne'
    (isCompact_closedBall (0 : V n) 1).measure_lt_top.ne

omit [NeZero n] in
theorem volume_normalized_ellipsoid_ratio {S A : MatR n}
    (hS : S.PosDef) (c a : V n) :
    volume (ellipsoid (normalizePoint c S a) (affineShape (S⁻¹ * A))) /
        volume (unitBall n) =
      volume (ellipsoid a A) / volume (ellipsoid c S) := by
  rw [← normalize_ellipsoid, ← normalize_ellipsoid_self hS c]
  exact volume_normalize_ratio hS c _ _

theorem IsMaxDet.normalized_maxEllipsoidVolume {K : Set (V n)}
    {c : V n} {S : MatR n} (h : IsMaxDet K c S) :
    maxEllipsoidVolume (normalizedBody K c S) = volume (unitBall n) := by
  rw [h.isJohnNormalized.maxEllipsoidVolume_eq_det]
  simp

theorem IsMaxDet.maxEllipsoidVolume_normalize {K : Set (V n)}
    {c : V n} {S : MatR n} (h : IsMaxDet K c S) :
    maxEllipsoidVolume (normalizedBody K c S) =
      ENNReal.ofReal S.det⁻¹ * maxEllipsoidVolume K := by
  rw [h.normalized_maxEllipsoidVolume, h.maxEllipsoidVolume_eq]
  rw [← volume_normalizePoint h.posDef, normalize_ellipsoid_self h.posDef]

omit [NeZero n] in
theorem denormalize_centralHalfspace (c p : V n) (S : MatR n) :
    denormalizePoint c S ⁻¹' centralHalfspace c p =
      centralHalfspace 0 (Matrix.toEuclideanCLM (𝕜 := ℝ) Sᵀ p) := by
  ext y
  simp only [mem_preimage, centralHalfspace, mem_ofPred_eq, denormalizePoint,
    add_sub_cancel_left, sub_zero, inner_transpose_action]

omit [NeZero n] in
theorem normalize_centralHalfspace {S : MatR n} (hS : S.PosDef) (c p : V n) :
    normalizePoint c S '' centralHalfspace c p =
      centralHalfspace 0 (Matrix.toEuclideanCLM (𝕜 := ℝ) S p) := by
  change normalizedBody (centralHalfspace c p) c S = _
  rw [normalizedBody_eq_preimage hS, denormalize_centralHalfspace,
    hS.isHermitian.isSymm.eq]

omit [NeZero n] in
theorem normalized_normal_ne_zero {S : MatR n} (hS : S.PosDef)
    {p : V n} (hp : p ≠ 0) : Matrix.toEuclideanCLM (𝕜 := ℝ) S p ≠ 0 := by
  intro h
  have hi := action_inv_action hS p
  rw [h, map_zero] at hi
  exact hp hi.symm

omit [NeZero n] in
theorem normalizedBody_cut {S : MatR n} (hS : S.PosDef)
    (K : Set (V n)) (c p : V n) :
    normalizedBody (K ∩ centralHalfspace c p) c S =
      normalizedBody K c S ∩ centralHalfspace 0 (Matrix.toEuclideanCLM (𝕜 := ℝ) S p) := by
  change normalizePoint c S '' (K ∩ centralHalfspace c p) = _
  have hinj : Function.Injective (normalizePoint c S) :=
    (normalizationHomeomorph c hS).injective
  rw [Set.image_inter hinj,
    normalize_centralHalfspace hS]
  rfl

/-- G04 supplies every center-exclusion hypothesis required by N01 for the retained side. -/
theorem normalized_cut_det_bound {K : Set (V n)} (hK : IsConvexBody K)
    {c p : V n} {S : MatR n} (hmax : IsMaxDet K c S) (hp : p ≠ 0)
    {a : V n} {A : MatR n}
    (hA : IsFeasible (normalizedBody (K ∩ centralHalfspace c p) c S) a A) :
    A.det ≤ rStar := by
  have hb := hK.normalizedBody c hmax.posDef
  have hs := hA.2
  rw [normalizedBody_cut hmax.posDef] at hs
  exact n01_normalized_det_bound hmax.isJohnNormalized hb.2.1 hb.1.isClosed hA.1
    (hs.trans inter_subset_left)
    (norm_inv_center_ge_one_of_halfspace hA.1
      (normalized_normal_ne_zero hmax.posDef hp) (hs.trans inter_subset_right)) rfl

omit [NeZero n] in
theorem isClosed_centralHalfspace (c p : V n) : IsClosed (centralHalfspace c p) :=
  isClosed_le continuous_const (by fun_prop)

omit [NeZero n] in
theorem convex_centralHalfspace (c p : V n) : Convex ℝ (centralHalfspace c p) := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ ⟪p, a • x + b • y - c⟫
  have hc : a • c + b • c = c := by rw [← add_smul, hab, one_smul]
  have he : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    calc
      a • x + b • y - c = a • x + b • y - (a • c + b • c) := by rw [hc]
      _ = a • (x - c) + b • (y - c) := by module
  rw [he, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

omit [NeZero n] in
/-- A central halfspace retains an open piece near any interior cutting center. -/
theorem interior_cut_nonempty {K : Set (V n)} {c p : V n}
    (hc : c ∈ interior K) (hp : p ≠ 0) :
    (interior (K ∩ centralHalfspace c p)).Nonempty := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hc)
  let t : ℝ := r / (2 * ‖p‖)
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have ht : 0 < t := div_pos hr (mul_pos (by norm_num) hpn)
  have hnorm : ‖t • p‖ = r / 2 := by
    rw [norm_smul, Real.norm_of_nonneg ht.le]
    dsimp [t]
    field_simp
  let x := c + t • p
  have hxb : x ∈ Metric.ball c r := by
    simpa only [x, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm]
      using (half_lt_self hr)
  have hxp : 0 < ⟪p, x - c⟫ := by
    simp only [x, add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_pos ht (sq_pos_of_pos hpn)
  have hopen : IsOpen {y : V n | 0 < ⟪p, y - c⟫} :=
    isOpen_lt continuous_const (by fun_prop)
  refine ⟨x, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply Filter.mem_of_superset ((Metric.isOpen_ball.inter hopen).mem_nhds ⟨hxb, hxp⟩)
  intro y hy
  refine ⟨hball hy.1, ?_⟩
  change 0 ≤ ⟪p, y - c⟫
  exact le_of_lt hy.2

omit [NeZero n] in
theorem IsConvexBody.centralCut {K : Set (V n)} (hK : IsConvexBody K)
    {c p : V n} (hc : c ∈ interior K) (hp : p ≠ 0) :
    IsConvexBody (K ∩ centralHalfspace c p) :=
  ⟨hK.1.inter_right (isClosed_centralHalfspace c p),
    hK.2.1.inter (convex_centralHalfspace c p), interior_cut_nonempty hc hp⟩

omit [NeZero n] in
/-- The volume supremum scales correctly for every set, including the retained side. -/
theorem maxEllipsoidVolume_normalizedBody {S : MatR n} (hS : S.PosDef)
    (c : V n) (K : Set (V n)) :
    maxEllipsoidVolume (normalizedBody K c S) =
      ENNReal.ofReal S.det⁻¹ * maxEllipsoidVolume K := by
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun A => iSup_le fun hA => ?_
    have himage : normalizePoint c S '' (denormalizePoint c S '' ellipsoid a A) =
        ellipsoid a A := by
      simp only [image_image, normalize_denormalize hS, image_id']
    have hv := volume_normalizePoint hS c (denormalizePoint c S '' ellipsoid a A)
    rw [himage, denormalize_ellipsoid] at hv
    rw [hv]
    gcongr
    exact volume_le_maxEllipsoidVolume (hA.denormalize hS)
  · rw [maxEllipsoidVolume]
    simp only [ENNReal.mul_iSup]
    refine iSup_le fun a => iSup_le fun A => iSup_le fun hA => ?_
    rw [← volume_normalizePoint hS c, normalize_ellipsoid]
    exact volume_le_maxEllipsoidVolume (hA.normalize c hS)

omit [NeZero n] in
theorem maxEllipsoidVolume_normalize_ratio {S : MatR n} (hS : S.PosDef)
    (c : V n) (K L : Set (V n)) :
    maxEllipsoidVolume (normalizedBody K c S) /
        maxEllipsoidVolume (normalizedBody L c S) =
      maxEllipsoidVolume K / maxEllipsoidVolume L := by
  rw [maxEllipsoidVolume_normalizedBody hS, maxEllipsoidVolume_normalizedBody hS]
  exact ENNReal.mul_div_mul_left _ _
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hS.det_pos)).ne' ENNReal.ofReal_ne_top

theorem volume_ellipsoid_div_maxEllipsoidVolume {K : Set (V n)}
    {c a : V n} {S A : MatR n} (hmax : IsMaxDet K c S) (hA : A.PosDef) :
    volume (ellipsoid a A) / maxEllipsoidVolume K = ENNReal.ofReal (A.det / S.det) := by
  rw [volume_ellipsoid_eq_det hA, hmax.maxEllipsoidVolume_eq_det]
  rw [ENNReal.mul_div_mul_right _ _ unitBall_volume_pos.ne'
    (isCompact_closedBall (0 : V n) 1).measure_lt_top.ne]
  exact (ENNReal.ofReal_div_of_pos hmax.posDef.det_pos).symm

/-- Positivity and finiteness justify the real-volume denominator used in ratio statements. -/
theorem IsMaxDet.maxEllipsoidVolume_toReal_pos {K : Set (V n)}
    {c : V n} {S : MatR n} (h : IsMaxDet K c S) :
    0 < (maxEllipsoidVolume K).toReal := by
  rw [h.maxEllipsoidVolume_eq]
  exact ENNReal.toReal_pos_iff.mpr ⟨volume_ellipsoid_pos h.posDef,
    volume_ellipsoid_lt_top c S⟩

theorem volume_ellipsoid_real_ratio {K : Set (V n)}
    {c a : V n} {S A : MatR n} (hmax : IsMaxDet K c S) (hA : A.PosDef) :
    (volume (ellipsoid a A)).toReal / (maxEllipsoidVolume K).toReal = A.det / S.det := by
  have hfin := volume_ellipsoid_lt_top a A
  have hmaxfin : maxEllipsoidVolume K < ∞ := by
    rw [hmax.maxEllipsoidVolume_eq]
    exact volume_ellipsoid_lt_top c S
  have hden := hmax.maxEllipsoidVolume_toReal_pos
  have heq := volume_ellipsoid_div_maxEllipsoidVolume (a := a) hmax hA
  apply (ENNReal.ofReal_eq_ofReal_iff
    (div_nonneg ENNReal.toReal_nonneg hden.le)
    (div_pos hA.det_pos hmax.posDef.det_pos).le).mp
  rw [ENNReal.ofReal_div_of_pos hden, ENNReal.ofReal_toReal hfin.ne,
    ENNReal.ofReal_toReal hmaxfin.ne]
  exact heq

end Khachiyan
