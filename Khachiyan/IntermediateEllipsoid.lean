import Khachiyan.EllipsoidGeometry

/-!
# The intermediate ellipsoid

This module implements G02 of `proof.md` and `formalization_plan.md`.  The
proof uses the support and closed-convex separation interfaces from G01S.  In
particular, it does not introduce a support supremum or any maximality or trace
hypothesis: the two support witnesses supplied by the contained unit ball and
the contained ellipsoid are enough.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set

namespace Khachiyan

variable {n : ℕ}

/-- The shape in the intermediate-ellipsoid construction. -/
def intermediateShape (b : V n) (S : MatR n) : MatR n :=
  CFC.sqrt (S + (1 / 4 : ℝ) • outer b)

theorem intermediateShape_posDef {b : V n} {S : MatR n} (hS : S.PosDef) :
    (intermediateShape b S).PosDef := by
  have hQ : (S + (1 / 4 : ℝ) • outer b).PosDef := by
    exact hS.add_posSemidef ((outer_posSemidef b).smul (by norm_num))
  rw [intermediateShape, CFC.sqrt_eq_rpow]
  exact Spectral.rpow_posDef hQ (1 / 2 : ℝ)

theorem intermediateShape_isSymm {b : V n} {S : MatR n} (hS : S.PosDef) :
    (intermediateShape b S).IsSymm :=
  (intermediateShape_posDef hS).isHermitian.isSymm

theorem inner_outer_action (b u : V n) :
    ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (outer b) u⟫ = ⟪u, b⟫ ^ 2 := by
  rw [outer_action]
  rw [real_inner_smul_right, real_inner_comm]
  ring

theorem intermediateShape_norm_sq {b : V n} {S : MatR n} (hS : S.PosDef)
    (u : V n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (intermediateShape b S) u‖ ^ 2 =
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (S + (1 / 4 : ℝ) • outer b) u⟫ := by
  let T := intermediateShape b S
  have hQ : (S + (1 / 4 : ℝ) • outer b).PosDef := by
    exact hS.add_posSemidef ((outer_posSemidef b).smul (by norm_num))
  have hT : T.IsSymm := intermediateShape_isSymm hS
  have hsq : T ^ 2 = S + (1 / 4 : ℝ) • outer b := by
    dsimp [T, intermediateShape]
    exact CFC.sq_sqrt _ hQ.posSemidef.nonneg
  rw [← real_inner_self_eq_norm_sq]
  calc
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) T u,
        Matrix.toEuclideanCLM (𝕜 := ℝ) T u⟫ =
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) T
          (Matrix.toEuclideanCLM (𝕜 := ℝ) T u)⟫ :=
      (inner_matrix_action_symm hT u
        (Matrix.toEuclideanCLM (𝕜 := ℝ) T u)).symm
    _ = ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (T ^ 2) u⟫ := by
      have hm := (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_mul T T
      simpa [pow_two] using congrArg (fun f => ⟪u, f u⟫) hm.symm
    _ = ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ)
        (S + (1 / 4 : ℝ) • outer b) u⟫ := by rw [hsq]

theorem intermediate_support_bound {b : V n} {S : MatR n} (hS : S.PosDef)
    (u : V n) :
    ⟪u, (1 / 2 : ℝ) • b⟫ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (intermediateShape b S) u‖ ≤
      max ‖u‖ (⟪u, b⟫ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S u‖) := by
  let s : ℝ := ⟪u, b⟫
  let h : ℝ := max ‖u‖ (s + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S u‖)
  let T := intermediateShape b S
  have hSsymm : S.IsSymm := hS.isHermitian.isSymm
  have hu : 0 ≤ ‖u‖ := norm_nonneg u
  have hgeu : ‖u‖ ≤ h := by
    exact le_max_left _ _
  have hges : s + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S u‖ ≤ h := by
    exact le_max_right _ _
  have hs_le : s ≤ h := by
    dsimp [h] at hges ⊢
    linarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) S u)]
  have hS_le : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S u‖ ≤ h - s := by
    linarith [hges]
  have hnonneg_sub : 0 ≤ h - s := by linarith
  have hquad :
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) S u⟫ ≤ h * (h - s) := by
    have hcs := real_inner_le_norm
      (Matrix.toEuclideanCLM (𝕜 := ℝ) S u) u
    have hcs' :
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) S u⟫ ≤
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S u‖ * ‖u‖ := by
      rw [inner_matrix_action_symm hSsymm]
      exact hcs
    have hmul :
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S u‖ * ‖u‖ ≤
          (h - s) * h := by
      exact mul_le_mul hS_le hgeu (norm_nonneg _) hnonneg_sub
    linarith [hcs']
  have hq :
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ)
          (S + (1 / 4 : ℝ) • outer b) u⟫ ≤ (h - s / 2) ^ 2 := by
    have hadd := (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_add S
      ((1 / 4 : ℝ) • outer b)
    have hsmul := map_smul (Matrix.toEuclideanCLM (𝕜 := ℝ)) (1 / 4 : ℝ) (outer b)
    rw [show Matrix.toEuclideanCLM (𝕜 := ℝ)
          (S + (1 / 4 : ℝ) • outer b) u =
        Matrix.toEuclideanCLM (𝕜 := ℝ) S u +
          Matrix.toEuclideanCLM (𝕜 := ℝ) ((1 / 4 : ℝ) • outer b) u by
          simpa using congrArg (fun f => f u) hadd]
    rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) ((1 / 4 : ℝ) • outer b) u =
        (1 / 4 : ℝ) • Matrix.toEuclideanCLM (𝕜 := ℝ) (outer b) u by
          simpa using congrArg (fun f => f u) hsmul]
    rw [inner_add_right, inner_smul_right, inner_outer_action]
    dsimp [s]
    nlinarith [hquad]
  have hhalf_nonneg : 0 ≤ h - s / 2 := by
    nlinarith [hu, hs_le]
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) T u‖ ≤ h - s / 2 := by
    have hsq := intermediateShape_norm_sq (b := b) hS u
    dsimp [T] at hsq ⊢
    nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) T u), hq]
  have hinner : ⟪u, (1 / 2 : ℝ) • b⟫ = s / 2 := by
    simp [s, real_inner_smul_right]
    ring
  rw [hinner]
  dsimp [h, T, intermediateShape] at hnorm ⊢
  linarith

theorem intermediate_ellipsoid_subset {K : Set (V n)} {b : V n} {S : MatR n}
    (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hunit : unitBall n ⊆ K) (hell : ellipsoid b S ⊆ K) (hS : S.PosDef) :
    ellipsoid ((1 / 2 : ℝ) • b) (intermediateShape b S) ⊆ K := by
  intro x hx
  apply mem_of_forall_strongDual_support hKconv hKclosed (x := x)
  intro l
  let u : V n := (InnerProductSpace.toDual ℝ (V n)).symm l
  obtain ⟨z₁, hz₁, hs₁⟩ :=
    ellipsoid_support_attained (a := (0 : V n)) (A := (1 : MatR n)) (by simp) u
  obtain ⟨z₂, hz₂, hs₂⟩ :=
    ellipsoid_support_attained hS.isHermitian.isSymm u
  have hz₁' : z₁ ∈ K := by
    apply hunit
    simpa [ellipsoid_zero_one] using hz₁
  have hz₂' : z₂ ∈ K := hell hz₂
  have hlx : l x = ⟪u, x⟫ :=
    (InnerProductSpace.toDual_symm_apply (x := x) (y := l)).symm
  have hl₁ : l z₁ = ‖u‖ := by
    rw [(InnerProductSpace.toDual_symm_apply (x := z₁) (y := l)).symm, hs₁]
    simp
  have hl₂ : l z₂ = ⟪u, b⟫ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S u‖ := by
    rw [(InnerProductSpace.toDual_symm_apply (x := z₂) (y := l)).symm, hs₂]
  by_cases hh : ‖u‖ ≥ ⟪u, b⟫ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S u‖
  · refine ⟨z₁, hz₁', ?_⟩
    rw [hlx, hl₁]
    calc
      ⟪u, x⟫ ≤ ⟪u, (1 / 2 : ℝ) • b⟫ +
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (intermediateShape b S) u‖ := by
        exact ellipsoid_support_le (intermediateShape_isSymm hS) hx
      _ ≤ max ‖u‖ (⟪u, b⟫ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S u‖) :=
        intermediate_support_bound hS u
      _ = ‖u‖ := max_eq_left hh
  · refine ⟨z₂, hz₂', ?_⟩
    rw [hlx, hl₂]
    calc
      ⟪u, x⟫ ≤ ⟪u, (1 / 2 : ℝ) • b⟫ +
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (intermediateShape b S) u‖ := by
        exact ellipsoid_support_le (intermediateShape_isSymm hS) hx
      _ ≤ max ‖u‖ (⟪u, b⟫ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S u‖) :=
        intermediate_support_bound hS u
      _ = ⟪u, b⟫ + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S u‖ :=
        max_eq_right (le_of_not_ge hh)

end Khachiyan
