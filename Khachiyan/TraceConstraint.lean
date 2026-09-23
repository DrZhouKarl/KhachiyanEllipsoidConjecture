import Khachiyan.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The trace constraint from normalized maximality

This module implements G05 of `proof.md` and `formalization_plan.md`.  The
trace bound is derived from the actual `IsJohnNormalized` determinant
maximality certificate.  No trace inequality is included in the certificate
itself.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set Filter TopologicalSpace

namespace Khachiyan

variable {n : ℕ}

/-- The shape obtained by taking the convex combination of the unit shape and `S`. -/
def convexShape (t : ℝ) (S : MatR n) : MatR n :=
  (1 - t) • (1 : MatR n) + t • S

theorem convexShape_posDef {t : ℝ} {S : MatR n} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hS : S.PosDef) : (convexShape t S).PosDef := by
  by_cases ht0 : t = 0
  · subst t
    simpa [convexShape] using (Matrix.PosDef.one : (1 : MatR n).PosDef)
  by_cases ht1 : t = 1
  · subst t
    simpa [convexShape] using hS
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hsubpos : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)
  exact (Matrix.PosDef.smul (Matrix.PosDef.one : (1 : MatR n).PosDef) hsubpos).add
    (Matrix.PosDef.smul hS htpos)

theorem convexShape_action (t : ℝ) (S : MatR n) (y : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (convexShape t S) y =
      (1 - t) • y + t • Matrix.toEuclideanCLM (𝕜 := ℝ) S y := by
  dsimp [convexShape]
  have hadd := (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_add
    ((1 - t) • (1 : MatR n)) (t • S)
  have hsmul₁ := map_smul (Matrix.toEuclideanCLM (𝕜 := ℝ)) (1 - t) (1 : MatR n)
  have hsmul₂ := map_smul (Matrix.toEuclideanCLM (𝕜 := ℝ)) t S
  rw [show Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((1 - t) • (1 : MatR n) + t • S) y =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) ((1 - t) • (1 : MatR n))) y +
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (t • S)) y by
        simpa using congrArg (fun f => f y) hadd]
  rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) ((1 - t) • (1 : MatR n)) y =
      (1 - t) • y by simpa using congrArg (fun f => f y) hsmul₁]
  rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) (t • S) y =
      t • Matrix.toEuclideanCLM (𝕜 := ℝ) S y by
        simpa using congrArg (fun f => f y) hsmul₂]

theorem convex_combination_ellipsoid_subset {K : Set (V n)} {b : V n} {S : MatR n}
    (hKconv : Convex ℝ K) (hunit : unitBall n ⊆ K)
    (hell : ellipsoid b S ⊆ K) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ellipsoid (t • b) (convexShape t S) ⊆ K := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (mem_ellipsoid (t • b) (convexShape t S) x).mp hx
  have hy0 : y ∈ K := hunit ((mem_unitBall y).mpr hy)
  have hy1 : Matrix.toEuclideanCLM (𝕜 := ℝ) S y + b ∈ K := by
    apply hell
    apply (mem_ellipsoid b S _).2
    refine ⟨y, hy, ?_⟩
    rw [add_comm]
  have hcomb := hKconv hy0 hy1 (sub_nonneg.mpr ht.2) ht.1
      (by ring)
  have hrewrite :
      (1 - t) • y + t • (Matrix.toEuclideanCLM (𝕜 := ℝ) S y + b) = x := by
    rw [← hxy, convexShape_action]
    module
  rw [← hrewrite]
  exact hcomb

/-- The determinant path associated with a shape `S`. -/
def detPath (S : MatR n) (t : ℝ) : ℝ := (convexShape t S).det

def detRemainder (X : MatR n) : Polynomial ℝ :=
  (1 + (Polynomial.X : Polynomial ℝ) • X.map Polynomial.C).det.divX.divX

theorem convexShape_eq_one_add (t : ℝ) (S : MatR n) :
    convexShape t S = 1 + t • (S - 1) := by
  ext i j
  simp [convexShape]
  ring

theorem detPath_eq_expansion (S : MatR n) (t : ℝ) :
    detPath S t = 1 + (S - 1).trace * t + (detRemainder (S - 1)).eval t * t ^ 2 := by
  rw [detPath, convexShape_eq_one_add, Matrix.det_one_add_smul]
  rfl

theorem hasDerivAt_detPath_zero (S : MatR n) :
    HasDerivAt (detPath S) (S - 1).trace 0 := by
  let q : Polynomial ℝ := detRemainder (S - 1)
  have hq : HasDerivAt (fun t : ℝ => q.eval t) (q.derivative.eval 0) 0 :=
    q.hasDerivAt 0
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ))
  have hprod : HasDerivAt (fun t : ℝ => q.eval t * t ^ 2) 0 0 := by
    convert hq.mul hsq using 1 <;> simp
  have hlin : HasDerivAt (fun t : ℝ => (S - 1).trace * t) (S - 1).trace 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_mul (S - 1).trace
  have hsum : HasDerivAt
      (fun t : ℝ => 1 + (S - 1).trace * t + q.eval t * t ^ 2)
      (S - 1).trace 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hlin.add hprod) using 1
    · funext t
      simp
      rw [mul_comm]
      ring
    · ring
  rw [show detPath S =
      (fun t : ℝ => 1 + (S - 1).trace * t + q.eval t * t ^ 2) by
        funext t; exact detPath_eq_expansion S t]
  exact hsum

theorem detPath_le_one_of_isJohnNormalized {K : Set (V n)}
    (hK : IsJohnNormalized K) (hKconv : Convex ℝ K)
    {b : V n} {S : MatR n} (hS : S.PosDef) (hell : ellipsoid b S ⊆ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : detPath S t ≤ 1 := by
  have hunit : unitBall n ⊆ K := hK.unitBall_subset
  have hcontain : ellipsoid (t • b) (convexShape t S) ⊆ K :=
    convex_combination_ellipsoid_subset hKconv hunit hell ht
  have hfeas : IsFeasible K (t • b) (convexShape t S) :=
    ⟨convexShape_posDef ht hS, hcontain⟩
  have hdet := hK.det_le (t • b) (convexShape t S) hfeas
  simpa [detPath, IsJohnNormalized, convexShape] using hdet

theorem trace_le_of_isJohnNormalized {K : Set (V n)}
    (hK : IsJohnNormalized K) (hKconv : Convex ℝ K)
    {b : V n} {S : MatR n} (hS : S.PosDef) (hell : ellipsoid b S ⊆ K) :
    S.trace ≤ n := by
  let f : ℝ → ℝ := detPath S
  have hmax : IsMaxOn f (Set.Icc (0 : ℝ) 1) 0 := by
    intro t ht
    change f t ≤ f 0
    calc
      f t ≤ 1 := by
        simpa [f] using detPath_le_one_of_isJohnNormalized hK hKconv hS hell ht
      _ = f 0 := by simp [f, detPath, convexShape]
  have htan : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    have hs : segment ℝ (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      rw [segment_eq_Icc (by norm_num)]
    simpa using (sub_mem_posTangentConeAt_of_segment_subset hs)
  have hderiv := (hmax.isLocalMaxOn).hasFDerivWithinAt_nonpos
    (hasDerivAt_detPath_zero S).hasDerivWithinAt.hasFDerivWithinAt htan
  have htrace : (S - 1).trace ≤ 0 := by
    simpa using hderiv
  rw [Matrix.trace_sub] at htrace
  simpa using (sub_nonpos.mp htrace)

end Khachiyan
