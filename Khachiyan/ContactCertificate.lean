import Khachiyan.EllipsoidGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# C01: a sufficient contact-point certificate

This module implements C01 of `proof.md`. A finite family of unit supporting
normals with positive weights, zero first moment, and identity second moment
certifies actual global maximality of the inscribed unit ball.
-/

noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace BigOperators
open Matrix Set

namespace Khachiyan

variable {n : ℕ}

/-- The scalar logarithm bound gives the determinant consequence of `trace A ≤ n`. -/
theorem det_le_one_of_trace_le {A : MatR n} (hA : A.PosDef)
    (htrace : A.trace ≤ (n : ℝ)) : A.det ≤ 1 := by
  have hlog : Real.log A.det = ∑ i, Real.log (hA.isHermitian.eigenvalues i) := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues]
    exact Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
  rw [Finset.sum_sub_distrib, ← Spectral.trace_eq_sum hA.isHermitian] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hsum
  have hl : Real.log A.det ≤ 0 := by rw [hlog]; linarith
  calc
    A.det = Real.exp (Real.log A.det) := (Real.exp_log hA.det_pos).symm
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hl
    _ = 1 := Real.exp_zero

private theorem trace_action_outer (A : MatR n) (u : V n) :
    (A * outer u).trace = ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) A u⟫ := by
  rw [outer_eq_vecMulVec, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, inner_matrix_action]
  exact dotProduct_comm _ _

theorem contact_weights_sum {ι : Type*} [Fintype ι] (u : ι → V n) (c : ι → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) (hsecond : ∑ i, c i • outer (u i) = 1) :
    ∑ i, c i = (n : ℝ) := by
  have ht := congrArg Matrix.trace hsecond
  simpa only [Matrix.trace_sum, Matrix.trace_smul, trace_outer, hu,
    one_pow, smul_eq_mul, mul_one, Matrix.trace_one, Fintype.card_fin] using ht

theorem contact_trace_bound {ι : Type*} [Fintype ι]
    {K : Set (V n)} (u : ι → V n) (c : ι → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) (hc : ∀ i, 0 < c i)
    (hsupport : ∀ i, ∀ x ∈ K, ⟪u i, x⟫ ≤ 1)
    (hfirst : ∑ i, c i • u i = 0) (hsecond : ∑ i, c i • outer (u i) = 1)
    {a : V n} {A : MatR n} (hA : IsFeasible K a A) : A.trace ≤ (n : ℝ) := by
  have hweight := contact_weights_sum u c hu hsecond
  have hcenter : ∑ i, c i * ⟪u i, a⟫ = 0 := by
    have ht := congrArg (fun v : V n => ⟪v, a⟫) hfirst
    simpa only [sum_inner, real_inner_smul_left, inner_zero_left] using ht
  have htrace : ∑ i, c i * ⟪u i, Matrix.toEuclideanCLM (𝕜 := ℝ) A (u i)⟫ =
      A.trace := by
    have ht := congrArg (fun B : MatR n => (A * B).trace) hsecond
    simpa only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      trace_action_outer, smul_eq_mul, Matrix.mul_one] using ht
  have heach (i : ι) : ⟪u i, Matrix.toEuclideanCLM (𝕜 := ℝ) A (u i)⟫ ≤
      1 - ⟪u i, a⟫ := by
    obtain ⟨x, hx, hxeq⟩ := ellipsoid_support_attained hA.1.isHermitian.isSymm (u i)
    have hxle := hsupport i x (hA.2 hx)
    rw [hxeq] at hxle
    have hcs := real_inner_le_norm (u i) (Matrix.toEuclideanCLM (𝕜 := ℝ) A (u i))
    rw [hu i, one_mul] at hcs
    linarith
  calc
    A.trace = ∑ i, c i * ⟪u i, Matrix.toEuclideanCLM (𝕜 := ℝ) A (u i)⟫ := htrace.symm
    _ ≤ ∑ i, c i * (1 - ⟪u i, a⟫) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (heach i) (hc i).le
    _ = (n : ℝ) := by simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hweight,
        hcenter, sub_zero]

/-- C01: the finite contact conditions certify the unit ball as a global maximizer. -/
theorem isJohnNormalized_of_contacts {ι : Type*} [Fintype ι]
    {K : Set (V n)} (hball : unitBall n ⊆ K) (u : ι → V n) (c : ι → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) (hc : ∀ i, 0 < c i)
    (hsupport : ∀ i, ∀ x ∈ K, ⟪u i, x⟫ ≤ 1)
    (hfirst : ∑ i, c i • u i = 0) (hsecond : ∑ i, c i • outer (u i) = 1) :
    IsJohnNormalized K := by
  refine ⟨⟨Matrix.PosDef.one, by simpa using hball⟩, fun a A hA => ?_⟩
  rw [Matrix.det_one]
  exact det_le_one_of_trace_le hA.1
    (contact_trace_bound u c hu hc hsupport hfirst hsecond hA)

end Khachiyan
