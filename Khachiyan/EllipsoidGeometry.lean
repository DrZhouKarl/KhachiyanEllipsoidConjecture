import Khachiyan.Basic
import Khachiyan.MatrixBridge
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Support and affine geometry of ellipsoids

This module starts G01S of `formalization_plan.md`.  It records the support
calculation for symmetric shapes, the closed-convex half-space interface, and
the conversion of arbitrary invertible linear images to symmetric positive
definite shapes.  Volume transformation and maximal-ellipsoid results are
deliberately kept in later modules.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set

namespace Khachiyan

variable {n : ℕ}

/-! ## The support calculation -/

theorem inner_matrix_action_symm {A : MatR n} (hA : A.IsSymm) (x y : V n) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A y⟫ =
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A x, y⟫ := by
  calc
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A y⟫ =
        x.ofLp ⬝ᵥ A *ᵥ y.ofLp := inner_matrix_action A x y
    _ = y.ofLp ⬝ᵥ A *ᵥ x.ofLp := hA.dotProduct_mulVec_comm
    _ = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A x, y⟫ :=
      by rw [real_inner_comm]; exact (inner_matrix_action A y x).symm

theorem ellipsoid_support_le {a : V n} {A : MatR n} (hA : A.IsSymm)
    {v x : V n} (hx : x ∈ ellipsoid a A) :
    ⟪v, x⟫ ≤ ⟪v, a⟫ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖ := by
  obtain ⟨y, hy, rfl⟩ := (mem_ellipsoid a A x).mp hx
  rw [inner_add_right, inner_matrix_action_symm hA]
  have hcs := real_inner_le_norm
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) y
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖ * ‖y‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖ := by
    nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) A v)]
  linarith

theorem ellipsoid_support_attained {a : V n} {A : MatR n} (hA : A.IsSymm)
    (v : V n) :
    ∃ x ∈ ellipsoid a A,
      ⟪v, x⟫ = ⟪v, a⟫ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖ := by
  by_cases hv : Matrix.toEuclideanCLM (𝕜 := ℝ) A v = 0
  · refine ⟨a, center_mem_ellipsoid a A, ?_⟩
    simp [hv]
  · let y : V n := (‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖)⁻¹ •
      Matrix.toEuclideanCLM (𝕜 := ℝ) A v
    refine ⟨a + Matrix.toEuclideanCLM (𝕜 := ℝ) A y, ?_, ?_⟩
    · apply (mem_ellipsoid a A _).2
      refine ⟨y, ?_, rfl⟩
      dsimp [y]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (norm_pos_iff.mpr hv)]
      field_simp
      exact le_rfl
    · rw [inner_add_right, inner_matrix_action_symm hA]
      dsimp [y]
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖ ≠ 0 :=
        ne_of_gt (norm_pos_iff.mpr hv)
      field_simp

/-! ## Closed-convex support separation -/

theorem mem_of_forall_strongDual_support {K : Set (V n)}
    (hKconv : Convex ℝ K) (hKclosed : IsClosed K) {x : V n}
    (h : ∀ l : StrongDual ℝ (V n), ∃ y ∈ K, l x ≤ l y) :
    x ∈ K := by
  have hx : x ∈ ⋂ l : StrongDual ℝ (V n), {z | ∃ y ∈ K, l z ≤ l y} := by
    simp only [mem_iInter]
    intro l
    exact h l
  rw [iInter_halfSpaces_eq hKconv hKclosed] at hx
  exact hx

/-! ## Symmetric shape associated with an invertible linear image -/

def affineShape (C : MatR n) : MatR n := CFC.sqrt (C * Cᵀ)

theorem affineShape_isSymm (C : MatR n) : (affineShape C).IsSymm := by
  have hs : (affineShape C).PosSemidef := by
    simpa [affineShape] using (Matrix.le_iff.mp (CFC.sqrt_nonneg (C * Cᵀ)))
  exact hs.isHermitian.isSymm

theorem affineShape_posDef {C : MatR n} (hC : IsUnit C.det) :
    (affineShape C).PosDef := by
  have hs : (affineShape C).PosSemidef := by
    simpa [affineShape] using (Matrix.le_iff.mp (CFC.sqrt_nonneg (C * Cᵀ)))
  apply hs.posDef_iff_det_ne_zero.mpr
  change (CFC.sqrt (C * Cᵀ)).det ≠ 0
  have hCC : (C * Cᵀ).PosSemidef := by
    simpa using (Matrix.posSemidef_self_mul_conjTranspose C)
  rw [Matrix.PosSemidef.det_sqrt hCC]
  rw [RCLike.sqrt_of_nonneg hCC.det_nonneg]
  apply Real.sqrt_ne_zero'.mpr
  rw [Matrix.det_mul, Matrix.det_transpose]
  exact mul_self_pos.mpr (isUnit_iff_ne_zero.mp hC)

theorem inner_transpose_action (C : MatR n) (x y : V n) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ x, y⟫ =
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) C y⟫ := by
  rw [real_inner_comm, inner_matrix_action, inner_matrix_action]
  rw [dotProduct_comm]
  simp [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem affineShape_action_norm (C : MatR n) (v : V n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C) v‖ := by
  have hCC : (C * Cᵀ).PosSemidef := by
    simpa using (Matrix.posSemidef_self_mul_conjTranspose C)
  have hs : (affineShape C) ^ 2 = C * Cᵀ := by
    simpa [affineShape] using CFC.sq_sqrt (C * Cᵀ) hCC.nonneg
  have hsq : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v‖ ^ 2 =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C) v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    calc
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v,
          Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v⟫ =
          ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) C
            (Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v)⟫ :=
        inner_transpose_action C v
          (Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v)
      _ = ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (C * Cᵀ) v⟫ := by
        have hm := (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_mul C Cᵀ
        simpa using congrArg (fun f => f v) hm.symm
      _ = ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) ((affineShape C) ^ 2) v⟫ := by
        rw [hs]
      _ = ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C) v,
          Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C) v⟫ := by
        rw [pow_two]
        have hm := (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_mul
          (affineShape C) (affineShape C)
        rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C * affineShape C) v =
            ((Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C)) *
              (Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C))) v by
              simpa using congrArg (fun f => f v) hm]
        simp only [mul_apply_eq_comp]
        exact inner_matrix_action_symm (affineShape_isSymm C) v
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C) v)
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v),
    norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C) v)]

theorem linear_image_support_le (C : MatR n) {v x : V n}
    (hx : x ∈ Matrix.toEuclideanCLM (𝕜 := ℝ) C '' unitBall n) :
    ⟪v, x⟫ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v‖ := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← inner_transpose_action]
  have hcs := real_inner_le_norm
    (Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v) y
  have hy' : ‖y‖ ≤ 1 := (mem_unitBall y).mp hy
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v‖ * ‖y‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v‖ := by
    exact mul_le_of_le_one_right (norm_nonneg _) hy'
  linarith

theorem linear_image_support_attained (C : MatR n) (v : V n) :
    ∃ x ∈ Matrix.toEuclideanCLM (𝕜 := ℝ) C '' unitBall n,
      ⟪v, x⟫ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v‖ := by
  by_cases hv : Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v = 0
  · refine ⟨0, ⟨0, by simp, by simp⟩, ?_⟩
    simp [hv]
  · let y : V n := (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v‖)⁻¹ •
      Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v
    refine ⟨Matrix.toEuclideanCLM (𝕜 := ℝ) C y, ⟨y, ?_, rfl⟩, ?_⟩
    · apply (mem_unitBall y).2
      dsimp [y]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (norm_pos_iff.mpr hv)]
      field_simp
      exact le_rfl
    · rw [← inner_transpose_action]
      dsimp [y]
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ v‖ ≠ 0 :=
        ne_of_gt (norm_pos_iff.mpr hv)
      field_simp

theorem isCompact_linear_image_unitBall (C : MatR n) :
    IsCompact (Matrix.toEuclideanCLM (𝕜 := ℝ) C '' unitBall n) := by
  apply (isCompact_closedBall (0 : V n) 1).image
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) C).continuous

theorem convex_linear_image_unitBall (C : MatR n) :
    Convex ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) C '' unitBall n) := by
  exact (convex_closedBall (0 : V n) 1).linear_image
    (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap

theorem linear_image_unitBall_eq_affineShape (C : MatR n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) C '' unitBall n =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C) '' unitBall n := by
  apply Set.Subset.antisymm
  · intro x hx
    have hAt : (affineShape C)ᵀ = affineShape C := (affineShape_isSymm C).eq
    apply mem_of_forall_strongDual_support
      (convex_linear_image_unitBall (affineShape C))
      (isCompact_linear_image_unitBall (affineShape C)).isClosed
    intro l
    let u : V n := (InnerProductSpace.toDual ℝ (V n)).symm l
    obtain ⟨z, hz, hzs⟩ := linear_image_support_attained (affineShape C) u
    refine ⟨z, hz, ?_⟩
    have hlx : l x = ⟪u, x⟫ :=
      (InnerProductSpace.toDual_symm_apply (x := x) (y := l)).symm
    have hlz : l z = ⟪u, z⟫ :=
      (InnerProductSpace.toDual_symm_apply (x := z) (y := l)).symm
    rw [hlx, hlz, hzs, hAt]
    exact (linear_image_support_le C hx).trans_eq (affineShape_action_norm C u)
  · intro x hx
    have hAt : (affineShape C)ᵀ = affineShape C := (affineShape_isSymm C).eq
    apply mem_of_forall_strongDual_support
      (convex_linear_image_unitBall C)
      (isCompact_linear_image_unitBall C).isClosed
    intro l
    let u : V n := (InnerProductSpace.toDual ℝ (V n)).symm l
    obtain ⟨z, hz, hzs⟩ := linear_image_support_attained C u
    refine ⟨z, hz, ?_⟩
    have hlx : l x = ⟪u, x⟫ :=
      (InnerProductSpace.toDual_symm_apply (x := x) (y := l)).symm
    have hlz : l z = ⟪u, z⟫ :=
      (InnerProductSpace.toDual_symm_apply (x := z) (y := l)).symm
    rw [hlx, hlz, hzs]
    calc
      ⟪u, x⟫ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C)ᵀ u‖ :=
        linear_image_support_le (affineShape C) hx
      _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C) u‖ := by rw [hAt]
      _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Cᵀ u‖ :=
        (affineShape_action_norm C u).symm

theorem affine_image_unitBall_eq_ellipsoid (a : V n) (C : MatR n) :
    (fun y : V n => a + Matrix.toEuclideanCLM (𝕜 := ℝ) C y) '' unitBall n =
      ellipsoid a (affineShape C) := by
  change (fun y : V n => a + Matrix.toEuclideanCLM (𝕜 := ℝ) C y) '' unitBall n =
    (fun y : V n => a + Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C) y) '' unitBall n
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hCy : Matrix.toEuclideanCLM (𝕜 := ℝ) C y ∈
        Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C) '' unitBall n := by
      rw [← linear_image_unitBall_eq_affineShape C]
      exact ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzeq⟩ := hCy
    exact ⟨z, hz, by simp [hzeq]⟩
  · rintro x ⟨y, hy, rfl⟩
    have hAy : Matrix.toEuclideanCLM (𝕜 := ℝ) (affineShape C) y ∈
        Matrix.toEuclideanCLM (𝕜 := ℝ) C '' unitBall n := by
      rw [linear_image_unitBall_eq_affineShape C]
      exact ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzeq⟩ := hAy
    exact ⟨z, hz, by simp [hzeq]⟩

end Khachiyan
