import Khachiyan.JohnExistence
import Khachiyan.IntermediateEllipsoid
import Khachiyan.MatrixPowers

noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set
namespace Khachiyan
variable {n : ℕ} [NeZero n]

def relativeShape (A₀ A₁ : MatR n) : MatR n :=
  (CFC.sqrt A₀)⁻¹ * A₁ * (CFC.sqrt A₀)⁻¹

lemma sqrt_posDef {A : MatR n} (hA : A.PosDef) : (CFC.sqrt A).PosDef := by
  rw [CFC.sqrt_eq_rpow]
  exact Spectral.rpow_posDef hA (1 / 2 : ℝ)

lemma relativeShape_posDef {A₀ A₁ : MatR n} (h₀ : A₀.PosDef) (h₁ : A₁.PosDef) :
    (relativeShape A₀ A₁).PosDef := by
  let B : MatR n := (CFC.sqrt A₀)⁻¹
  have hB : B.PosDef := (sqrt_posDef h₀).inv
  have h := h₁.conjTranspose_mul_mul_same hB.mulVec_injective
  have hstar : Bᴴ = B := hB.isHermitian
  rw [hstar] at h
  exact h

lemma sqrt_mul_self {A : MatR n} (hA : A.PosDef) :
    CFC.sqrt A * CFC.sqrt A = A := by
  simpa [pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg

lemma relativeShape_reconstruct {A₀ A₁ : MatR n} (h₀ : A₀.PosDef) :
    CFC.sqrt A₀ * relativeShape A₀ A₁ * CFC.sqrt A₀ = A₁ := by
  let S : MatR n := CFC.sqrt A₀
  have hS : S.PosDef := sqrt_posDef h₀
  have hunit : IsUnit S.det := Matrix.isUnit_iff_isUnit_det S |>.mp hS.isUnit
  change S * (S⁻¹ * A₁ * S⁻¹) * S = A₁
  calc
    S * (S⁻¹ * A₁ * S⁻¹) * S = (S * S⁻¹) * A₁ * (S⁻¹ * S) := by noncomm_ring
    _ = A₁ := by rw [Matrix.mul_nonsing_inv _ hunit,
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul, Matrix.mul_one]

lemma relativeShape_eq_one_iff {A₀ A₁ : MatR n} (h₀ : A₀.PosDef) :
    relativeShape A₀ A₁ = 1 ↔ A₁ = A₀ := by
  constructor
  · intro h
    have hr := relativeShape_reconstruct (A₁ := A₁) h₀
    rw [h, Matrix.mul_one, sqrt_mul_self h₀] at hr
    exact hr.symm
  · intro h
    subst A₁
    let S : MatR n := CFC.sqrt A₀
    have hS : S.PosDef := sqrt_posDef h₀
    have hunit : IsUnit S.det := Matrix.isUnit_iff_isUnit_det S |>.mp hS.isUnit
    change S⁻¹ * A₀ * S⁻¹ = 1
    rw [← sqrt_mul_self h₀]
    calc
      S⁻¹ * (S * S) * S⁻¹ = (S⁻¹ * S) * (S * S⁻¹) := by noncomm_ring
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ hunit,
        Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]

lemma relativeShape_exists_eigenvalue_ne_one {A₀ A₁ : MatR n}
    (h₀ : A₀.PosDef) (h₁ : A₁.PosDef) (hne : A₀ ≠ A₁) :
    ∃ i, (relativeShape_posDef h₀ h₁).isHermitian.eigenvalues i ≠ 1 := by
  let C := relativeShape A₀ A₁
  let hC : C.PosDef := relativeShape_posDef h₀ h₁
  by_contra hall
  push Not at hall
  have hCI : C = 1 := by
    have hs := Spectral.rpow_spectral hC 1
    have hone : CFC.rpow C (1 : ℝ) = C := by
      change C ^ (1 : ℝ) = C
      exact CFC.rpow_one C hC.posSemidef.nonneg
    rw [hone] at hs
    rw [hs]
    have hdiag : diagonal (fun i => hC.isHermitian.eigenvalues i ^ (1 : ℝ)) =
        (1 : MatR n) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [hall]
      · simp [hij]
    rw [hdiag, Matrix.mul_one]
    exact Unitary.coe_mul_star_self hC.isHermitian.eigenvectorUnitary
  have := (relativeShape_eq_one_iff h₀).mp hCI
  exact hne this.symm

lemma relativeShape_det {A₀ A₁ : MatR n} (h₀ : A₀.PosDef) :
    (relativeShape A₀ A₁).det = A₁.det / A₀.det := by
  let S : MatR n := CFC.sqrt A₀
  have hS : S.PosDef := sqrt_posDef h₀
  have hSdet : S.det = Real.sqrt A₀.det := by
    simpa [S] using Spectral.det_sqrt h₀
  rw [relativeShape, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
    hSdet]
  have hsqrt : (Real.sqrt A₀.det) ^ 2 = A₀.det := Real.sq_sqrt h₀.det_pos.le
  have hsqrt0 : Real.sqrt A₀.det ≠ 0 := (Real.sqrt_pos.2 h₀.det_pos).ne'
  rw [div_eq_mul_inv]
  have hinv : (Real.sqrt A₀.det)⁻¹ * (Real.sqrt A₀.det)⁻¹ = A₀.det⁻¹ := by
    rw [← mul_inv, ← sq]
    rw [hsqrt]
  rw [Ring.inverse_eq_inv]
  calc
    (Real.sqrt A₀.det)⁻¹ * A₁.det * (Real.sqrt A₀.det)⁻¹ =
        A₁.det * ((Real.sqrt A₀.det)⁻¹ * (Real.sqrt A₀.det)⁻¹) := by ring
    _ = A₁.det * A₀.det⁻¹ := by rw [hinv]

lemma midpoint_det_factor {A₀ A₁ : MatR n} (h₀ : A₀.PosDef) :
    (((1 / 2 : ℝ) • A₀ + (1 / 2 : ℝ) • A₁).det) =
      A₀.det *
        (((1 / 2 : ℝ) • (1 : MatR n) +
          (1 / 2 : ℝ) • relativeShape A₀ A₁).det) := by
  let S : MatR n := CFC.sqrt A₀
  have hfac :
      (1 / 2 : ℝ) • A₀ + (1 / 2 : ℝ) • A₁ =
        S * ((1 / 2 : ℝ) • (1 : MatR n) +
          (1 / 2 : ℝ) • relativeShape A₀ A₁) * S := by
    have hrec := relativeShape_reconstruct (A₁ := A₁) h₀
    have hsq := sqrt_mul_self h₀
    dsimp [S]
    calc
      _ = (1 / 2 : ℝ) • (CFC.sqrt A₀ * CFC.sqrt A₀) +
          (1 / 2 : ℝ) •
            (CFC.sqrt A₀ * relativeShape A₀ A₁ * CFC.sqrt A₀) := by
        rw [hsq, hrec]
      _ = _ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hfac, Matrix.det_mul, Matrix.det_mul]
  rw [show (CFC.sqrt A₀).det *
        (((1 / 2 : ℝ) • (1 : MatR n) +
          (1 / 2 : ℝ) • relativeShape A₀ A₁).det) *
        (CFC.sqrt A₀).det =
      ((CFC.sqrt A₀).det ^ 2) *
        (((1 / 2 : ℝ) • (1 : MatR n) +
          (1 / 2 : ℝ) • relativeShape A₀ A₁).det) by ring]
  rw [Spectral.det_sqrt h₀, Real.sq_sqrt h₀.det_pos.le]

lemma det_eq_of_isMaxDet {K : Set (V n)} {c₀ c₁ : V n} {A₀ A₁ : MatR n}
    (h₀ : IsMaxDet K c₀ A₀) (h₁ : IsMaxDet K c₁ A₁) :
    A₀.det = A₁.det := by
  exact le_antisymm (h₁.det_le _ _ h₀.feasible) (h₀.det_le _ _ h₁.feasible)

theorem strict_midpoint_det {A₀ A₁ : MatR n}
    (h₀ : A₀.PosDef) (h₁ : A₁.PosDef) (hd : A₀.det = A₁.det)
    (hne : A₀ ≠ A₁) :
    A₀.det < ((1 / 2 : ℝ) • A₀ + (1 / 2 : ℝ) • A₁).det := by
  let C := relativeShape A₀ A₁
  let hC : C.PosDef := relativeShape_posDef h₀ h₁
  have heig := relativeShape_exists_eigenvalue_ne_one h₀ h₁ hne
  have haff := strict_affine_det_of_eigenvalues hC heig
  have hCdet : C.det = 1 := by
    rw [relativeShape_det h₀, hd]
    exact div_self h₁.det_pos.ne'
  have hsqrt : Real.sqrt C.det = 1 := by rw [hCdet, Real.sqrt_one]
  have hfac := midpoint_det_factor (A₁ := A₁) h₀
  rw [hfac]
  rw [hsqrt] at haff
  simpa [C] using mul_lt_mul_of_pos_left haff h₀.det_pos

theorem maxDet_shape_unique {K : Set (V n)}
    (hKconv : Convex ℝ K) {c₀ c₁ : V n} {A₀ A₁ : MatR n}
    (h₀ : IsMaxDet K c₀ A₀) (h₁ : IsMaxDet K c₁ A₁) : A₀ = A₁ := by
  apply maxDet_same_shape_of_isMaxDet hKconv h₀ h₁
  exact strict_midpoint_det h₀.feasible.1 h₁.feasible.1
    (det_eq_of_isMaxDet h₀ h₁)

lemma affineShape_det {C : MatR n} (hC : IsUnit C.det) :
    (affineShape C).det = |C.det| := by
  have hCC : (C * Cᵀ).PosSemidef := by
    simpa using (Matrix.posSemidef_self_mul_conjTranspose C)
  rw [affineShape, Matrix.PosSemidef.det_sqrt hCC]
  rw [RCLike.sqrt_of_nonneg hCC.det_nonneg]
  rw [Matrix.det_mul, Matrix.det_transpose]
  change Real.sqrt (C.det * C.det) = |C.det|
  rw [show C.det * C.det = C.det ^ 2 by ring, Real.sqrt_sq_eq_abs]

lemma ellipsoid_affine_preimage {a c : V n} {A : MatR n} (hA : A.PosDef) :
    (fun x : V n => Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (x - c)) ''
        ellipsoid a A =
      ellipsoid (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (a - c)) (1 : MatR n) := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_ellipsoid a A x).mp hx
    apply (mem_ellipsoid _ _ _).2
    refine ⟨y, hy, ?_⟩
    have hunit : IsUnit A.det := Matrix.isUnit_iff_isUnit_det A |>.mp hA.isUnit
    have hone : Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : MatR n) y = y := by simp
    rw [hone]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (a - c) + y =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (a + Matrix.toEuclideanCLM (𝕜 := ℝ) A y - c)
    have hadd := map_add (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹) a
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A y)
    have hsub := map_sub (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹)
      (a + Matrix.toEuclideanCLM (𝕜 := ℝ) A y) c
    rw [hsub, hadd, show Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A y) = y by
      have hm := (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_mul A⁻¹ A
      rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A y) =
          Matrix.toEuclideanCLM (𝕜 := ℝ) (A⁻¹ * A) y by
        exact congrArg (fun f => f y) hm.symm]
      rw [Matrix.nonsing_inv_mul A hunit]
      simp]
    have hsub0 := map_sub (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹) a c
    rw [hsub0]
    abel
  · rintro z ⟨y, hy, rfl⟩
    refine ⟨a + Matrix.toEuclideanCLM (𝕜 := ℝ) A y,
      (mem_ellipsoid a A _).2 ⟨y, (mem_unitBall y).mp hy, rfl⟩, ?_⟩
    have hunit : IsUnit A.det := Matrix.isUnit_iff_isUnit_det A |>.mp hA.isUnit
    have hone : Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : MatR n) y = y := by simp
    change Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹
      (a + Matrix.toEuclideanCLM (𝕜 := ℝ) A y - c) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (a - c) +
        Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : MatR n) y
    rw [hone]
    have hadd := map_add (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹) a
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A y)
    have hsub₁ := map_sub (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹)
      (a + Matrix.toEuclideanCLM (𝕜 := ℝ) A y) c
    have hsub₀ := map_sub (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹) a c
    rw [hsub₁, hsub₀, hadd, show Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A y) = y by
      have hm := (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_mul A⁻¹ A
      rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A y) =
          Matrix.toEuclideanCLM (𝕜 := ℝ) (A⁻¹ * A) y by
        exact congrArg (fun f => f y) hm.symm]
      rw [Matrix.nonsing_inv_mul A hunit]
      simp]
    abel

lemma image_subset_image {f : V n → V n} {S T : Set (V n)} (h : S ⊆ T) :
    f '' S ⊆ f '' T := Set.image_mono h

theorem maxDet_center_unique_same_shape {K : Set (V n)}
    (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    {c₀ c₁ : V n} {A : MatR n}
    (h₀ : IsMaxDet K c₀ A) (h₁ : IsMaxDet K c₁ A) : c₀ = c₁ := by
  by_contra hcenters
  let f : V n → V n := fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (x - c₀)
  let g : V n → V n := fun z => c₀ + Matrix.toEuclideanCLM (𝕜 := ℝ) A z
  let K' : Set (V n) := f '' K
  let b : V n := Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (c₁ - c₀)
  have hA : A.PosDef := h₀.feasible.1
  have hb : b ≠ 0 := by
    intro hb0
    have hmul := congrArg (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) A x) hb0
    have hunit : IsUnit A.det := Matrix.isUnit_iff_isUnit_det A |>.mp hA.isUnit
    dsimp [b] at hmul
    rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) A
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (c₁ - c₀)) = c₁ - c₀ by
      have hm := (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_mul A A⁻¹
      rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) A
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (c₁ - c₀)) =
          Matrix.toEuclideanCLM (𝕜 := ℝ) (A * A⁻¹) (c₁ - c₀) by
        exact congrArg (fun q => q (c₁ - c₀)) hm.symm]
      rw [Matrix.mul_nonsing_inv A hunit]
      simp] at hmul
    simp at hmul
    exact hcenters (sub_eq_zero.mp hmul).symm
  have hKconv' : Convex ℝ K' := by
    intro z₀ hz₀ z₁ hz₁ a b ha hb hab
    obtain ⟨x, hx, hxz⟩ := hz₀
    obtain ⟨y, hy, hyz⟩ := hz₁
    subst z₀
    subst z₁
    refine ⟨a • x + b • y, hKconv hx hy ha hb hab, ?_⟩
    dsimp [f]
    rw [map_sub, map_add, map_smul, map_smul]
    have hxsub := map_sub (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹) x c₀
    have hysub := map_sub (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹) y c₀
    rw [hxsub, hysub]
    have hc : a • Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ c₀ +
        b • Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ c₀ =
        Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ c₀ := by
      rw [← add_smul, hab, one_smul]
    nth_rewrite 1 [← hc]
    module
  have hfg (z : V n) : f (g z) = z := by
    have hunit : IsUnit A.det := Matrix.isUnit_iff_isUnit_det A |>.mp hA.isUnit
    dsimp [f, g]
    rw [show c₀ + Matrix.toEuclideanCLM (𝕜 := ℝ) A z - c₀ =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A z by abel]
    have hm := (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_mul A⁻¹ A
    rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A z) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (A⁻¹ * A) z by
      exact congrArg (fun q => q z) hm.symm]
    rw [Matrix.nonsing_inv_mul A hunit]
    simp
  have hgf (x : V n) : g (f x) = x := by
    have hunit : IsUnit A.det := Matrix.isUnit_iff_isUnit_det A |>.mp hA.isUnit
    dsimp [f, g]
    have hm := (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_mul A A⁻¹
    rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) A
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (x - c₀)) = x - c₀ by
      rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) A
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (x - c₀)) =
          Matrix.toEuclideanCLM (𝕜 := ℝ) (A * A⁻¹) (x - c₀) by
        exact congrArg (fun q => q (x - c₀)) hm.symm]
      rw [Matrix.mul_nonsing_inv A hunit]
      simp]
    abel
  have hset : K' = g ⁻¹' K := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [hgf] using hx
    · intro hz
      exact ⟨g z, hz, hfg z⟩
  have hKclosed' : IsClosed K' := by
    rw [hset]
    exact hKclosed.preimage (by fun_prop)
  have hunit : unitBall n ⊆ K' := by
    rw [← ellipsoid_zero_one]
    have he : Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (c₀ - c₀) = 0 := by simp
    rw [← he, ← ellipsoid_affine_preimage (a := c₀) (c := c₀) hA]
    exact image_subset_image h₀.feasible.2
  have hbsub : ellipsoid b (1 : MatR n) ⊆ K' := by
    dsimp [b]
    rw [← ellipsoid_affine_preimage (a := c₁) (c := c₀) hA]
    exact image_subset_image h₁.feasible.2
  have hinter := intermediate_ellipsoid_subset hKconv' hKclosed' hunit hbsub
    (Matrix.PosDef.one : (1 : MatR n).PosDef)
  let T := intermediateShape b (1 : MatR n)
  have hT : T.PosDef := intermediateShape_posDef Matrix.PosDef.one
  have hTdet : 1 < T.det := by
    dsimp [T, intermediateShape]
    rw [Spectral.det_sqrt (Matrix.PosDef.one.add_posSemidef
      ((outer_posSemidef b).smul (by norm_num)))]
    have hrank : (1 + (1 / 4 : ℝ) • outer b : MatR n).det =
        1 + ‖b‖ ^ 2 / 4 := by
      rw [outer_eq_vecMulVec, Matrix.vecMulVec_eq Unit]
      have hscale : (1 / 4 : ℝ) •
          (Matrix.replicateCol Unit b.ofLp * Matrix.replicateRow Unit b.ofLp) =
          Matrix.replicateCol Unit ((1 / 4 : ℝ) • b.ofLp) *
            Matrix.replicateRow Unit b.ofLp := by
        ext i j
        simp [Matrix.mul_apply, smul_eq_mul]
        ring
      rw [hscale, Matrix.det_one_add_replicateCol_mul_replicateRow]
      congr 1
      calc
        ∑ i, b.ofLp i * ((1 / 4 : ℝ) • b.ofLp) i =
            (1 / 4 : ℝ) * ∑ i, b.ofLp i * b.ofLp i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          simp [smul_eq_mul]
          ring
        _ = (1 / 4 : ℝ) * ‖b‖ ^ 2 := by
          congr 1
          change b.ofLp ⬝ᵥ b.ofLp = ‖b‖ ^ 2
          rw [← inner_eq_dotProduct, real_inner_self_eq_norm_sq]
        _ = ‖b‖ ^ 2 / 4 := by ring
    rw [hrank]
    have hbpos : 0 < ‖b‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hb)
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + ‖b‖ ^ 2 / 4 by positivity),
      Real.sqrt_nonneg (1 + ‖b‖ ^ 2 / 4)]
  let C : MatR n := A * T
  let B : MatR n := affineShape C
  have hCunit : IsUnit C.det := by
    dsimp [C]
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_iff_isUnit_det A |>.mp hA.isUnit).mul
      (Matrix.isUnit_iff_isUnit_det T |>.mp hT.isUnit)
  have hB : B.PosDef := affineShape_posDef hCunit
  have hBdet : A.det < B.det := by
    dsimp [B]
    rw [affineShape_det hCunit]
    dsimp [C]
    rw [Matrix.det_mul]
    rw [abs_of_pos (mul_pos hA.det_pos hT.det_pos)]
    nlinarith [mul_lt_mul_of_pos_left hTdet hA.det_pos]
  let d : V n := (1 / 2 : ℝ) • b
  let center : V n := c₀ + Matrix.toEuclideanCLM (𝕜 := ℝ) A d
  have himage : ellipsoid center B = g '' ellipsoid d T := by
    rw [show ellipsoid center B =
        (fun y : V n => center + Matrix.toEuclideanCLM (𝕜 := ℝ) C y) '' unitBall n by
      symm
      exact affine_image_unitBall_eq_ellipsoid center C]
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      let z : V n := d + Matrix.toEuclideanCLM (𝕜 := ℝ) T y
      refine ⟨z, (mem_ellipsoid d T z).2 ⟨y, (mem_unitBall y).mp hy, rfl⟩, ?_⟩
      dsimp [g, center, C, z]
      have hm := (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_mul A T
      rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) (A * T) y =
          Matrix.toEuclideanCLM (𝕜 := ℝ) A
            (Matrix.toEuclideanCLM (𝕜 := ℝ) T y) by
        exact congrArg (fun q => q y) hm]
      rw [map_add]
      abel
    · rintro x ⟨z, hz, rfl⟩
      obtain ⟨y, hy, rfl⟩ := (mem_ellipsoid d T z).mp hz
      refine ⟨y, (mem_unitBall y).mpr hy, ?_⟩
      dsimp [g, center, C]
      have hm := (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_mul A T
      rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) (A * T) y =
          Matrix.toEuclideanCLM (𝕜 := ℝ) A
            (Matrix.toEuclideanCLM (𝕜 := ℝ) T y) by
        exact congrArg (fun q => q y) hm]
      rw [map_add]
      abel
  have hBsub : ellipsoid center B ⊆ K := by
    rw [himage]
    rintro x ⟨z, hz, rfl⟩
    have hzK' : z ∈ K' := hinter hz
    rw [hset] at hzK'
    exact hzK'
  have hle := h₀.det_le center B ⟨hB, hBsub⟩
  exact (not_lt_of_ge hle) hBdet

theorem isMaxDet_unique {K : Set (V n)}
    (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    {c₀ c₁ : V n} {A₀ A₁ : MatR n}
    (h₀ : IsMaxDet K c₀ A₀) (h₁ : IsMaxDet K c₁ A₁) :
    c₀ = c₁ ∧ A₀ = A₁ := by
  have hshape : A₀ = A₁ := maxDet_shape_unique hKconv h₀ h₁
  subst A₁
  exact ⟨maxDet_center_unique_same_shape hKconv hKclosed h₀ h₁, rfl⟩

theorem existsUnique_isMaxDet {K : Set (V n)} (hK : IsConvexBody K) :
    ∃! p : V n × MatR n, IsMaxDet K p.1 p.2 := by
  obtain ⟨c, A, hmax⟩ := exists_isMaxDet hK
  refine ⟨(c, A), hmax, ?_⟩
  intro q hq
  have hu := isMaxDet_unique hK.2.1 hK.1.isClosed hq hmax
  exact Prod.ext hu.1 hu.2

end Khachiyan
