import Khachiyan.ContactCertificate
import Khachiyan.GeometricBound

/-!
# C02: explicit cones and their inscribed ellipsoids

This module implements C02 of `proof.md`. The parameter `m` is the transverse
dimension, so the ambient dimension is `m + 1`, with `m ≥ 1` for the cone family.
Coordinates and norms always belong to genuine Euclidean spaces.
-/

noncomputable section
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace BigOperators
open Matrix Set MeasureTheory

namespace Khachiyan.Cone

variable {m : ℕ}

/-- Euclidean axial/transverse coordinates, without using the product norm. -/
def join (t : ℝ) (y : V m) : V (m + 1) := WithLp.toLp 2 (Fin.cons t y.ofLp)

def tail (x : V (m + 1)) : V m := WithLp.toLp 2 (fun i => x i.succ)

@[simp] theorem join_zero (t : ℝ) (y : V m) : join t y 0 = t := rfl
@[simp] theorem join_succ (t : ℝ) (y : V m) (i : Fin m) : join t y i.succ = y i := rfl
@[simp] theorem tail_apply (x : V (m + 1)) (i : Fin m) : tail x i = x i.succ := rfl
@[simp] theorem tail_join (t : ℝ) (y : V m) : tail (join t y) = y := by ext i; rfl

theorem norm_sq_split (x : V (m + 1)) : ‖x‖ ^ 2 = (x 0) ^ 2 + ‖tail x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, EuclideanSpace.real_norm_sq_eq]
  rfl

theorem norm_join_sq (t : ℝ) (y : V m) : ‖join t y‖ ^ 2 = t ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_sq_split, join_zero, tail_join]

theorem inner_join (t s : ℝ) (y z : V m) :
    ⟪join t y, join s z⟫ = t * s + ⟪y, z⟫ := by
  simp only [inner_eq_dotProduct, dotProduct, Fin.sum_univ_succ, join_zero, join_succ]

@[simp] theorem tail_add (x y : V (m + 1)) : tail (x + y) = tail x + tail y := by
  ext i; rfl

@[simp] theorem tail_smul (a : ℝ) (x : V (m + 1)) : tail (a • x) = a • tail x := by
  ext i; rfl

theorem continuous_tail : Continuous (tail : V (m + 1) → V m) := by
  unfold tail
  fun_prop

/-- The two-dimensional Cauchy--Schwarz calculation used for the cone inequalities. -/
theorem axial_support_le {t q a b r : ℝ} (hx : t ^ 2 + q ^ 2 ≤ 1)
    (hab : a ^ 2 + b ^ 2 = r ^ 2) (hr : 0 ≤ r) : a * t + b * q ≤ r := by
  have hid : (a * t + b * q) ^ 2 + (a * q - b * t) ^ 2 =
      (a ^ 2 + b ^ 2) * (t ^ 2 + q ^ 2) := by ring
  rw [hab] at hid
  have hmul := mul_le_mul_of_nonneg_left hx (sq_nonneg r)
  nlinarith [sq_nonneg (a * q - b * t)]

/-- The cone's transverse slope in ambient dimension `m + 1`. -/
def slope (m : ℕ) : ℝ := Real.sqrt (((m : ℝ) + 1) ^ 2 - 1)

def body (m : ℕ) : Set (V (m + 1)) :=
  {x | -1 ≤ x 0 ∧ x 0 + slope m * ‖tail x‖ ≤ (m : ℝ) + 1}

theorem slope_nonneg (m : ℕ) : 0 ≤ slope m := Real.sqrt_nonneg _

theorem slope_sq (m : ℕ) : slope m ^ 2 = ((m : ℝ) + 1) ^ 2 - 1 := by
  exact Real.sq_sqrt (by have := Nat.cast_nonneg (α := ℝ) m; nlinarith)

theorem slope_pos (hm : 1 ≤ m) : 0 < slope m := by
  apply Real.sqrt_pos.mpr
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

theorem unitBall_subset_body (m : ℕ) : unitBall (m + 1) ⊆ body m := by
  intro x hx
  have hn := (mem_unitBall x).mp hx
  have hs : (x 0) ^ 2 + ‖tail x‖ ^ 2 ≤ 1 := by
    rw [← norm_sq_split]
    nlinarith [norm_nonneg x]
  refine ⟨?_, ?_⟩
  · nlinarith [sq_nonneg ‖tail x‖]
  · have h := axial_support_le (a := 1) (b := slope m) (r := (m : ℝ) + 1)
      hs (by rw [slope_sq]; ring) (by positivity)
    simpa only [one_mul] using h

theorem isClosed_body (m : ℕ) : IsClosed (body m) := by
  change IsClosed ({x : V (m + 1) | -1 ≤ x 0} ∩
    {x | x 0 + slope m * ‖tail x‖ ≤ (m : ℝ) + 1})
  apply IsClosed.inter (isClosed_le continuous_const (by fun_prop))
  apply isClosed_le _ continuous_const
  exact (by fun_prop : Continuous (fun x : V (m + 1) => x 0)).add
    (continuous_const.mul continuous_tail.norm)

theorem convex_body (m : ℕ) : Convex ℝ (body m) := by
  intro x hx y hy a b ha hb hab
  change -1 ≤ a * x 0 + b * y 0 ∧
    a * x 0 + b * y 0 + slope m * ‖tail (a • x + b • y)‖ ≤ (m : ℝ) + 1
  have hx0 := hx.1
  have hy0 := hy.1
  have hx1 := hx.2
  have hy1 := hy.2
  have hn : ‖tail (a • x + b • y)‖ ≤ a * ‖tail x‖ + b * ‖tail y‖ := by
    rw [tail_add, tail_smul, tail_smul]
    calc
      ‖a • tail x + b • tail y‖ ≤ ‖a • tail x‖ + ‖b • tail y‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have hscaled := mul_le_mul_of_nonneg_left hn (slope_nonneg m)
  constructor
  · nlinarith [mul_nonneg ha (by linarith : 0 ≤ x 0 + 1),
      mul_nonneg hb (by linarith : 0 ≤ y 0 + 1)]
  · have hax := mul_le_mul_of_nonneg_left hx1 ha
    have hby := mul_le_mul_of_nonneg_left hy1 hb
    nlinarith

theorem body_coordinate_bounds (hm : 1 ≤ m) {x : V (m + 1)} (hx : x ∈ body m) :
    |x 0| ≤ (m : ℝ) + 1 ∧ ‖tail x‖ ≤ ((m : ℝ) + 2) / slope m := by
  have hx0 := hx.1
  have hx1 := hx.2
  have hm0 := Nat.cast_nonneg (α := ℝ) m
  have hk := slope_pos hm
  have hup : x 0 ≤ (m : ℝ) + 1 := by
    nlinarith [mul_nonneg hk.le (norm_nonneg (tail x))]
  refine ⟨abs_le.mpr ⟨by linarith, hup⟩, ?_⟩
  apply (le_div_iff₀ hk).mpr
  nlinarith

theorem isBounded_body (hm : 1 ≤ m) : Bornology.IsBounded (body m) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨((m : ℝ) + 1) + ((m : ℝ) + 2) / slope m, fun x hx => ?_⟩
  obtain ⟨hhead, htail⟩ := body_coordinate_bounds hm hx
  have hd : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have hs : (x 0) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x 0)) hd).mpr hhead
  have hnorm : ‖x‖ ≤ (m : ℝ) + 1 + ‖tail x‖ := by
    nlinarith [norm_sq_split x, norm_nonneg (tail x), norm_nonneg x,
      mul_nonneg hd (norm_nonneg (tail x))]
  linarith

theorem isConvexBody_body (hm : 1 ≤ m) : IsConvexBody (body m) := by
  refine ⟨Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_body m, isBounded_body hm⟩,
    convex_body m, ?_⟩
  refine ⟨0, interior_mono (unitBall_subset_body m) ?_⟩
  rw [unitBall, interior_closedBall (0 : V (m + 1)) one_ne_zero]
  simp

theorem inner_join_left (t : ℝ) (y : V m) (x : V (m + 1)) :
    ⟪join t y, x⟫ = t * x 0 + ⟪y, tail x⟫ := by
  simp only [inner_eq_dotProduct, dotProduct, Fin.sum_univ_succ, join_zero, join_succ, tail_apply]

abbrev ContactIndex (m : ℕ) := Unit ⊕ (Fin m × Bool)

def sideNormal (m : ℕ) (i : Fin m) (b : Bool) : V (m + 1) :=
  join (1 / ((m : ℝ) + 1))
    (EuclideanSpace.single i (if b then slope m / ((m : ℝ) + 1) else
      -(slope m / ((m : ℝ) + 1))))

def contactNormal (m : ℕ) : ContactIndex m → V (m + 1)
  | .inl _ => join (-1) 0
  | .inr (i, b) => sideNormal m i b

def baseWeight (m : ℕ) : ℝ := ((m : ℝ) + 1) / ((m : ℝ) + 2)
def sideWeight (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) ^ 2 / (2 * (((m : ℝ) + 1) ^ 2 - 1))

def contactWeight (m : ℕ) : ContactIndex m → ℝ
  | .inl _ => baseWeight m
  | .inr _ => sideWeight m

theorem side_scales_sq (m : ℕ) :
    (1 / ((m : ℝ) + 1)) ^ 2 + (slope m / ((m : ℝ) + 1)) ^ 2 = 1 := by
  rw [div_pow, div_pow, slope_sq]
  field_simp
  ring

/-- The implemented side coefficient is exactly the coefficient in `proof.md`. -/
theorem side_scale_eq_sqrt (m : ℕ) :
    slope m / ((m : ℝ) + 1) = Real.sqrt (1 - 1 / ((m : ℝ) + 1) ^ 2) := by
  have hs := side_scales_sq m
  rw [div_pow, one_pow] at hs
  have heq : 1 - 1 / ((m : ℝ) + 1) ^ 2 = (slope m / ((m : ℝ) + 1)) ^ 2 := by
    linarith
  rw [heq, Real.sqrt_sq (div_nonneg (slope_nonneg m) (by positivity))]

theorem sideNormal_norm (m : ℕ) (i : Fin m) (b : Bool) : ‖sideNormal m i b‖ = 1 := by
  have hlen : ‖EuclideanSpace.single i (if b then slope m / ((m : ℝ) + 1) else
      -(slope m / ((m : ℝ) + 1)))‖ ^ 2 = (slope m / ((m : ℝ) + 1)) ^ 2 := by
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, EuclideanSpace.single,
      PiLp.norm_single, norm_neg, Real.norm_eq_abs, sq_abs]
  have hs : ‖sideNormal m i b‖ ^ 2 = 1 := by
    rw [sideNormal, norm_join_sq, hlen]
    exact side_scales_sq m
  nlinarith [norm_nonneg (sideNormal m i b)]

theorem contactNormal_norm (m : ℕ) (i : ContactIndex m) : ‖contactNormal m i‖ = 1 := by
  rcases i with u | ⟨i, b⟩
  · have hs : ‖join (-1) (0 : V m)‖ ^ 2 = 1 := by
      simpa using norm_join_sq (-1 : ℝ) (0 : V m)
    change ‖join (-1) (0 : V m)‖ = 1
    nlinarith [norm_nonneg (join (-1) (0 : V m))]
  · exact sideNormal_norm m i b

theorem contactWeight_pos (hm : 1 ≤ m) (i : ContactIndex m) : 0 < contactWeight m i := by
  rcases i with u | ⟨i, b⟩
  · change 0 < baseWeight m
    unfold baseWeight
    positivity
  · change 0 < sideWeight m
    unfold sideWeight
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    apply div_pos (by positivity)
    nlinarith

theorem sideNormal_support (m : ℕ) (i : Fin m) (b : Bool)
    {x : V (m + 1)} (hx : x ∈ body m) : ⟪sideNormal m i b, x⟫ ≤ 1 := by
  have hd : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlen : ‖EuclideanSpace.single i (if b then slope m / ((m : ℝ) + 1) else
      -(slope m / ((m : ℝ) + 1)))‖ = slope m / ((m : ℝ) + 1) := by
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, EuclideanSpace.single,
      PiLp.norm_single, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (slope_nonneg m) hd.le)]
  have hcs := real_inner_le_norm
    (EuclideanSpace.single i (if b then slope m / ((m : ℝ) + 1) else
      -(slope m / ((m : ℝ) + 1)))) (tail x)
  rw [hlen] at hcs
  have hdiv : (x 0 + slope m * ‖tail x‖) / ((m : ℝ) + 1) ≤ 1 :=
    (div_le_iff₀ hd).mpr (by simpa using hx.2)
  rw [sideNormal, inner_join_left]
  calc
    _ ≤ 1 / ((m : ℝ) + 1) * x 0 +
        (slope m / ((m : ℝ) + 1)) * ‖tail x‖ := by linarith
    _ = (x 0 + slope m * ‖tail x‖) / ((m : ℝ) + 1) := by ring
    _ ≤ 1 := hdiv

theorem contactNormal_support (m : ℕ) (i : ContactIndex m)
    {x : V (m + 1)} (hx : x ∈ body m) : ⟪contactNormal m i, x⟫ ≤ 1 := by
  rcases i with u | ⟨i, b⟩
  · change ⟪join (-1) (0 : V m), x⟫ ≤ 1
    rw [inner_join_left]
    have h := hx.1
    simp only [inner_zero_left, add_zero, neg_one_mul]
    linarith
  · exact sideNormal_support m i b hx

theorem contact_first_moment (hm : 1 ≤ m) :
    ∑ i : ContactIndex m, contactWeight m i • contactNormal m i = 0 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : (m : ℝ) + 1 ≠ 0 := by positivity
  have hd2 : ((m : ℝ) + 1) ^ 2 - 1 ≠ 0 := by nlinarith
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Fintype.sum_sum_type, Fintype.sum_prod_type,
      contactWeight, contactNormal, sideNormal, baseWeight, sideWeight]
    field_simp
    ring
  · simp [Fintype.sum_sum_type, Fintype.sum_prod_type,
      contactWeight, contactNormal, sideNormal, EuclideanSpace.single, PiLp.single_apply]
    apply Finset.sum_eq_zero
    intro i hi
    split_ifs <;> ring

theorem contact_second_moment (hm : 1 ≤ m) :
    ∑ i : ContactIndex m, contactWeight m i • outer (contactNormal m i) = 1 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : (m : ℝ) + 1 ≠ 0 := by positivity
  have hd2 : ((m : ℝ) + 1) ^ 2 - 1 ≠ 0 := by nlinarith
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, outer_apply, smul_eq_mul, Matrix.one_apply]
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Fintype.sum_sum_type, contactWeight, contactNormal,
        sideNormal, baseWeight, sideWeight]
      field_simp
      ring
    · simp [Fintype.sum_sum_type, Fintype.sum_prod_type, contactWeight, contactNormal,
        sideNormal, EuclideanSpace.single, PiLp.single_apply]
      exact (Fin.succ_ne_zero j).symm
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Fintype.sum_sum_type, Fintype.sum_prod_type, contactWeight, contactNormal,
        sideNormal, EuclideanSpace.single, PiLp.single_apply]
    · by_cases hij : i = j
      · subst j
        simp [Fintype.sum_sum_type, Fintype.sum_prod_type, contactWeight, contactNormal,
          sideNormal, EuclideanSpace.single, PiLp.single_apply]
        rw [← sq, div_pow, slope_sq]
        unfold sideWeight
        field_simp
        ring
      · simp [Fintype.sum_sum_type, Fintype.sum_prod_type, contactWeight, contactNormal,
          sideNormal, EuclideanSpace.single, PiLp.single_apply, hij]

/-- The actual cone has the unit ball as its globally maximal inscribed ellipsoid. -/
theorem isJohnNormalized_body (hm : 1 ≤ m) : IsJohnNormalized (body m) :=
  isJohnNormalized_of_contacts (unitBall_subset_body m) (contactNormal m) (contactWeight m)
    (contactNormal_norm m) (contactWeight_pos hm)
    (fun i _ hx => contactNormal_support m i hx)
    (contact_first_moment hm) (contact_second_moment hm)

theorem johnCenter_body (hm : 1 ≤ m) : johnCenter (body m) = 0 :=
  johnCenter_eq_of_isMaxDet (isConvexBody_body hm) (isJohnNormalized_body hm)

theorem maxEllipsoidVolume_body (hm : 1 ≤ m) :
    maxEllipsoidVolume (body m) = volume (unitBall (m + 1)) := by
  rw [(isJohnNormalized_body hm).maxEllipsoidVolume_eq_det]
  simp

def cutNormal (m : ℕ) : V (m + 1) := join (-1) 0

def cut (m : ℕ) : Set (V (m + 1)) := body m ∩ {x | x 0 ≤ 0}

theorem cutNormal_ne_zero (m : ℕ) : cutNormal m ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : V (m + 1) => x 0) h
  norm_num [cutNormal] at h0

theorem centralHalfspace_cutNormal (m : ℕ) :
    centralHalfspace 0 (cutNormal m) = {x : V (m + 1) | x 0 ≤ 0} := by
  ext x
  change 0 ≤ ⟪join (-1) (0 : V m), x - 0⟫ ↔ x 0 ≤ 0
  rw [sub_zero, inner_join_left]
  simp

theorem cut_eq_canonical_cut (hm : 1 ≤ m) :
    cut m = body m ∩ centralHalfspace (johnCenter (body m)) (cutNormal m) := by
  rw [johnCenter_body hm, centralHalfspace_cutNormal]
  rfl

theorem isConvexBody_cut (hm : 1 ≤ m) : IsConvexBody (cut m) := by
  rw [cut_eq_canonical_cut hm]
  exact john_center_cut_isConvexBody (isConvexBody_body hm) (cutNormal_ne_zero m)

def transverseScale (m : ℕ) : ℝ := Real.sqrt (((m : ℝ) + 1) / m)

def candidateCenter (m : ℕ) : V (m + 1) := join (-(1 / 2 : ℝ)) 0

def candidateShape (m : ℕ) : MatR (m + 1) :=
  Matrix.diagonal (Fin.cons (1 / 2 : ℝ) (fun _ : Fin m => transverseScale m))

theorem transverseScale_pos (hm : 1 ≤ m) : 0 < transverseScale m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  exact Real.sqrt_pos.mpr (div_pos (by positivity) hm')

theorem transverseScale_sq (hm : 1 ≤ m) :
    transverseScale m ^ 2 = ((m : ℝ) + 1) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  exact Real.sq_sqrt (div_nonneg (by positivity) hm'.le)

theorem slope_scale_sq (hm : 1 ≤ m) :
    (slope m * transverseScale m) ^ 2 = ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [mul_pow, slope_sq, transverseScale_sq hm]
  field_simp
  ring

theorem candidateShape_posDef (hm : 1 ≤ m) : (candidateShape m).PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  refine Fin.cases (by norm_num) (fun _ => transverseScale_pos hm) i

theorem candidateShape_action (m : ℕ) (x : V (m + 1)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (candidateShape m) x =
      join (x 0 / 2) (transverseScale m • tail x) := by
  ext i
  change (candidateShape m *ᵥ x.ofLp) i = _
  rw [candidateShape, Matrix.mulVec_diagonal]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
    ring
  · rfl

/-- Containment is checked for every point of the ellipsoid, including all transverse directions. -/
theorem candidate_subset_cut (hm : 1 ≤ m) :
    ellipsoid (candidateCenter m) (candidateShape m) ⊆ cut m := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_ellipsoid _ _ _).mp hx
  have hysq : (y 0) ^ 2 + ‖tail y‖ ^ 2 ≤ 1 := by
    rw [← norm_sq_split]
    nlinarith [norm_nonneg y]
  have hylo : -1 ≤ y 0 := by nlinarith [sq_nonneg ‖tail y‖]
  have hyhi : y 0 ≤ 1 := by nlinarith [sq_nonneg ‖tail y‖]
  have hsupport := axial_support_le (a := (1 / 2 : ℝ))
    (b := slope m * transverseScale m) (r := (m : ℝ) + 3 / 2) hysq
    (by rw [slope_scale_sq hm]; ring) (by positivity)
  simp only [cut, body, mem_inter_iff, mem_ofPred_eq, candidateShape_action, candidateCenter,
    PiLp.add_apply, join_zero, tail_add, tail_join, zero_add, norm_smul,
    Real.norm_of_nonneg (transverseScale_pos hm).le]
  exact ⟨⟨by linarith, by nlinarith⟩, by linarith⟩

theorem candidate_feasible (hm : 1 ≤ m) :
    IsFeasible (cut m) (candidateCenter m) (candidateShape m) :=
  ⟨candidateShape_posDef hm, candidate_subset_cut hm⟩

theorem candidateShape_det (m : ℕ) :
    (candidateShape m).det = (1 / 2 : ℝ) * transverseScale m ^ m := by
  rw [candidateShape, Matrix.det_diagonal, Fin.prod_univ_succ]
  simp

end Khachiyan.Cone
