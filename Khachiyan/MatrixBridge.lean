import Khachiyan.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Fintype.Lattice

/-!
# Spectral calculations for real matrices

This module formalizes M01 of `proof.md` and `formalization_plan.md`.
Fractional powers use the continuous functional calculus, geometry uses
`EuclideanSpace`, and matrix inequalities use Loewner order. Comparisons of
scalar functions below are applied to one fixed self-adjoint matrix; they do
not assert operator monotonicity between powers of different matrices.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix

namespace Khachiyan.Spectral

variable {n : ℕ} {A X Y : MatR n}

theorem eigenvalue_pos (hA : A.PosDef) (i : Fin n) :
    0 < hA.isHermitian.eigenvalues i :=
  hA.eigenvalues_pos i

theorem det_eq_prod (hA : A.IsHermitian) : A.det = ∏ i, hA.eigenvalues i :=
  hA.det_eq_prod_eigenvalues

theorem trace_eq_sum (hA : A.IsHermitian) : A.trace = ∑ i, hA.eigenvalues i :=
  hA.trace_eq_sum_eigenvalues

theorem trace_mono (hXY : X ≤ Y) : X.trace ≤ Y.trace := by
  have h := (Matrix.le_iff.mp hXY).trace_nonneg
  rw [Matrix.trace_sub] at h
  linarith

theorem rpow_eq_cfc (hA : A.PosDef) (p : ℝ) :
    CFC.rpow A p = cfc (fun t : ℝ => t ^ p) A :=
  CFC.rpow_eq_cfc_real hA.posSemidef.nonneg

/-- The real functional calculus is orthogonal conjugation of a spectral diagonal. -/
theorem cfc_spectral (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : MatR n) *
      diagonal (fun i => f (hA.eigenvalues i)) * star (hA.eigenvectorUnitary : MatR n) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

theorem trace_cfc (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [cfc_spectral hA f, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    one_mul, Matrix.trace_diagonal]

theorem det_cfc (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).det = ∏ i, f (hA.eigenvalues i) := by
  rw [cfc_spectral hA f, mul_assoc, Matrix.det_mul_comm, mul_assoc,
    Unitary.coe_star_mul_self, mul_one, Matrix.det_diagonal]

/-- The trace formula holds for every real exponent on a positive definite matrix. -/
theorem trace_rpow (hA : A.PosDef) (p : ℝ) :
    (CFC.rpow A p).trace = ∑ i, (hA.isHermitian.eigenvalues i) ^ p := by
  rw [rpow_eq_cfc hA p, trace_cfc hA.isHermitian]

theorem det_rpow_eq_prod (hA : A.PosDef) (p : ℝ) :
    (CFC.rpow A p).det = ∏ i, (hA.isHermitian.eigenvalues i) ^ p := by
  rw [rpow_eq_cfc hA p, det_cfc hA.isHermitian]

theorem rpow_spectral (hA : A.PosDef) (p : ℝ) :
    CFC.rpow A p = (hA.isHermitian.eigenvectorUnitary : MatR n) *
      diagonal (fun i => (hA.isHermitian.eigenvalues i) ^ p) *
      star (hA.isHermitian.eigenvectorUnitary : MatR n) := by
  rw [rpow_eq_cfc hA p, cfc_spectral hA.isHermitian]

theorem det_rpow (hA : A.PosDef) (p : ℝ) : (CFC.rpow A p).det = A.det ^ p := by
  rw [det_rpow_eq_prod hA p, det_eq_prod hA.isHermitian]
  exact Real.finsetProd_rpow Finset.univ hA.isHermitian.eigenvalues
    (fun i _ => (hA.eigenvalues_pos i).le) p

theorem trace_sqrt (hA : A.PosDef) :
    (CFC.sqrt A).trace = ∑ i, Real.sqrt (hA.isHermitian.eigenvalues i) := by
  have hs : CFC.sqrt A = CFC.rpow A (1 / 2 : ℝ) := CFC.sqrt_eq_rpow
  rw [hs, trace_rpow hA (1 / 2 : ℝ)]
  simp only [Real.sqrt_eq_rpow]

theorem det_sqrt (hA : A.PosDef) : (CFC.sqrt A).det = Real.sqrt A.det := by
  have hs : CFC.sqrt A = CFC.rpow A (1 / 2 : ℝ) := CFC.sqrt_eq_rpow
  rw [hs, det_rpow hA (1 / 2 : ℝ), Real.sqrt_eq_rpow]

theorem rpow_posDef (hA : A.PosDef) (p : ℝ) : (CFC.rpow A p).PosDef := by
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.rpow A p hA.isStrictlyPositive)

/-- Scalar comparison on the eigenvalues of one fixed real symmetric matrix. -/
theorem cfc_le_of_eigenvalues (hA : A.IsHermitian) (f g : ℝ → ℝ)
    (hfg : ∀ i, f (hA.eigenvalues i) ≤ g (hA.eigenvalues i)) : cfc f A ≤ cfc g A := by
  apply (cfc_le_iff f g A ((Matrix.finite_real_spectrum (A := A)).continuousOn f)
    ((Matrix.finite_real_spectrum (A := A)).continuousOn g) hA).mpr
  intro t ht
  rw [hA.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  exact hfg i

theorem quadratic_mono (hXY : X ≤ Y) (u : V n) :
    ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) X u⟫ ≤
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) Y u⟫ := by
  have h := (Matrix.le_iff.mp hXY).dotProduct_mulVec_nonneg u.ofLp
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at h
  rw [inner_matrix_action, inner_matrix_action]
  linarith

theorem scalar_lower_quadratic {r : ℝ} (h : r • (1 : MatR n) ≤ A) (u : V n) :
    r * ‖u‖ ^ 2 ≤ ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) A u⟫ := by
  have hq := quadratic_mono h u
  simpa [map_smul, inner_smul_right, real_inner_self_eq_norm_sq] using hq

section PositiveDimension

variable [NeZero n]

/-- A minimizing index, chosen without relying on the library's eigenvalue ordering. -/
def minIndex (hA : A.IsHermitian) : Fin n :=
  Classical.choose (Finite.exists_min hA.eigenvalues)

def minEigenvalue (hA : A.IsHermitian) : ℝ := hA.eigenvalues (minIndex hA)

theorem minEigenvalue_le (hA : A.IsHermitian) (i : Fin n) :
    minEigenvalue hA ≤ hA.eigenvalues i :=
  Classical.choose_spec (Finite.exists_min hA.eigenvalues) i

theorem minEigenvalue_pos (hA : A.PosDef) : 0 < minEigenvalue hA.isHermitian :=
  hA.eigenvalues_pos (minIndex hA.isHermitian)

theorem minEigenvalue_le_of_mem_spectrum (hA : A.IsHermitian) {t : ℝ}
    (ht : t ∈ spectrum ℝ A) : minEigenvalue hA ≤ t := by
  rw [hA.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  exact minEigenvalue_le hA i

theorem minEigenvalue_mem_spectrum (hA : A.IsHermitian) :
    minEigenvalue hA ∈ spectrum ℝ A :=
  hA.eigenvalues_mem_spectrum_real (minIndex hA)

theorem exists_unit_min_eigenvector (hA : A.IsHermitian) :
    ∃ u : V n, ‖u‖ = 1 ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) A u = minEigenvalue hA • u := by
  refine ⟨hA.eigenvectorBasis (minIndex hA), hA.eigenvectorBasis.orthonormal.1 _, ?_⟩
  have h := hA.mulVec_eigenvectorBasis (minIndex hA)
  ext i
  exact congrFun h i

theorem minEigenvalue_smul_one_le (hA : A.IsHermitian) :
    minEigenvalue hA • (1 : MatR n) ≤ A := by
  have h := (algebraMap_le_iff_le_spectrum (R := ℝ) (a := A) hA).mpr
    (fun t ht => minEigenvalue_le_of_mem_spectrum hA ht)
  simpa only [Algebra.algebraMap_eq_smul_one] using h

/-- The spectral inequality $A\preceq\alpha^{-1}A^2$ from M01. -/
theorem le_inv_minEigenvalue_smul_sq (hA : A.PosDef) :
    A ≤ (minEigenvalue hA.isHermitian)⁻¹ • A ^ 2 := by
  have ha := minEigenvalue_pos hA
  have h := cfc_le_of_eigenvalues hA.isHermitian id
    (fun t : ℝ => (minEigenvalue hA.isHermitian)⁻¹ * t ^ 2) (by
      intro i
      change hA.isHermitian.eigenvalues i ≤
        (minEigenvalue hA.isHermitian)⁻¹ * (hA.isHermitian.eigenvalues i) ^ 2
      rw [← div_eq_inv_mul]
      apply (le_div_iff₀ ha).mpr
      have hm := mul_le_mul_of_nonneg_right (minEigenvalue_le hA.isHermitian i)
        (hA.eigenvalues_pos i).le
      nlinarith)
  rw [cfc_id ℝ A hA.isHermitian.isSelfAdjoint, cfc_const_mul _ _ _ (by fun_prop),
    cfc_pow_id (R := ℝ) A 2 hA.isHermitian.isSelfAdjoint] at h
  exact h

/-- Lower spectral bounds persist under a nonnegative scalar exponent. -/
theorem minEigenvalue_rpow_smul_one_le (hA : A.PosDef) {p : ℝ} (hp : 0 ≤ p) :
    (minEigenvalue hA.isHermitian) ^ p • (1 : MatR n) ≤ CFC.rpow A p := by
  have h := cfc_le_of_eigenvalues hA.isHermitian
    (fun _ : ℝ => (minEigenvalue hA.isHermitian) ^ p) (fun t : ℝ => t ^ p)
    (fun i => Real.rpow_le_rpow (minEigenvalue_pos hA).le
      (minEigenvalue_le hA.isHermitian i) hp)
  rw [cfc_const _ A hA.isHermitian.isSelfAdjoint, ← rpow_eq_cfc hA p] at h
  simpa only [Algebra.algebraMap_eq_smul_one] using h

theorem minEigenvalue_rpow_le_quadratic (hA : A.PosDef) {p : ℝ} (hp : 0 ≤ p) (u : V n) :
    (minEigenvalue hA.isHermitian) ^ p * ‖u‖ ^ 2 ≤
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.rpow A p) u⟫ :=
  scalar_lower_quadratic (minEigenvalue_rpow_smul_one_le hA hp) u

/-- The unit-vector quadratic-form lower bound from M01, for every $p>0$. -/
theorem minEigenvalue_two_mul_rpow_le_quadratic (hA : A.PosDef) {p : ℝ} (hp : 0 < p)
    (u : V n) (hu : ‖u‖ = 1) :
    (minEigenvalue hA.isHermitian) ^ (2 * p) ≤
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.rpow A (2 * p)) u⟫ := by
  have h := minEigenvalue_rpow_le_quadratic hA (by positivity : 0 ≤ 2 * p) u
  simpa only [hu, one_pow, mul_one] using h

/-- Remove one occurrence of the minimum eigenvalue, preserving multiplicities. -/
theorem trace_rpow_eq_min_add_sum_erase (hA : A.PosDef) (p : ℝ) :
    (CFC.rpow A p).trace = (minEigenvalue hA.isHermitian) ^ p +
      ∑ i ∈ Finset.univ.erase (minIndex hA.isHermitian),
        (hA.isHermitian.eigenvalues i) ^ p := by
  rw [trace_rpow hA p]
  exact (Finset.add_sum_erase Finset.univ
    (fun i => (hA.isHermitian.eigenvalues i) ^ p)
    (Finset.mem_univ (minIndex hA.isHermitian))).symm

theorem det_eq_min_mul_prod_erase (hA : A.IsHermitian) :
    A.det = minEigenvalue hA *
      ∏ i ∈ Finset.univ.erase (minIndex hA), hA.eigenvalues i := by
  rw [det_eq_prod hA]
  exact (Finset.mul_prod_erase Finset.univ hA.eigenvalues
    (Finset.mem_univ (minIndex hA))).symm

end PositiveDimension

end Khachiyan.Spectral
