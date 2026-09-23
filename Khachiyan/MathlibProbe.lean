import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Concrete mathlib interface probes

These bootstrap probes implement the experiments in Section 6.1 of
`formalization_plan.md`, touching B01, M01, M02, and G01V. They check existing
mathlib interfaces on the intended types. They do not complete those nodes.
The real-matrix operator-monotonicity adapter was not part of Phase 0; it is now
proved separately in `Khachiyan/MatrixPowers.lean`.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix MeasureTheory

namespace Khachiyan.MathlibProbe

abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev MatR (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev MatC (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

#synth InnerProductSpace ℝ (V 3)
#synth NormedRing (MatR 3)
#synth PartialOrder (MatR 3)
#synth CStarAlgebra (MatC 3)
#synth MeasureSpace (V 3)
#synth Measure.IsAddHaarMeasure (volume : Measure (V 3))

#check Matrix.le_iff
#check Matrix.isStrictlyPositive_iff_posDef
#check Matrix.toEuclideanCLM
#check Matrix.inner_toEuclideanCLM
#check Matrix.ofLp_toEuclideanCLM
#check CFC.sqrt_eq_rpow
#check CFC.sq_sqrt
#check CFC.sqrt_sq
#check CFC.monotone_rpow
#check Matrix.IsHermitian.spectral_theorem
#check Matrix.PosDef.eigenvalues_pos
#check Matrix.IsHermitian.det_eq_prod_eigenvalues
#check Matrix.IsHermitian.trace_eq_sum_eigenvalues
#check Measure.addHaar_image_linearMap

variable {n : ℕ}

theorem loewner_iff (A B : MatR n) : A ≤ B ↔ (B - A).PosSemidef :=
  Matrix.le_iff

theorem strict_positive_iff (A : MatR n) : IsStrictlyPositive A ↔ A.PosDef :=
  Matrix.isStrictlyPositive_iff_posDef

theorem sqrt_squared (A : MatR n) (hA : A.PosSemidef) : (CFC.sqrt A) ^ 2 = A :=
  CFC.sq_sqrt A hA.nonneg

theorem sqrt_of_square (A : MatR n) (hA : A.PosSemidef) : CFC.sqrt (A ^ 2) = A :=
  CFC.sqrt_sq A hA.nonneg

theorem sqrt_eq_half_power (A : MatR n) : CFC.sqrt A = CFC.rpow A (1 / 2 : ℝ) :=
  CFC.sqrt_eq_rpow

theorem euclidean_action (A : MatR n) (x : V n) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A x).ofLp = A *ᵥ x.ofLp :=
  Matrix.ofLp_toEuclideanCLM A x

theorem euclidean_inner (A : MatR n) (x y : V n) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A y⟫ = x.ofLp ⬝ᵥ (A *ᵥ y.ofLp) :=
  Matrix.inner_toEuclideanCLM A x y

-- Operator monotonicity is tested on complex matrices, where the required
-- C*-algebra instance is valid. This is not a real-matrix adapter.
theorem complex_rpow_monotone (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (A B : MatC n) (hAB : A ≤ B) : CFC.rpow A p ≤ CFC.rpow B p :=
  CFC.monotone_rpow hp hAB

theorem eigenvalue_positive (A : MatR n) (hA : A.PosDef) (i : Fin n) :
    0 < hA.isHermitian.eigenvalues i :=
  hA.eigenvalues_pos i

theorem determinant_product (A : MatR n) (hA : A.PosDef) :
    A.det = ∏ i, hA.isHermitian.eigenvalues i :=
  hA.isHermitian.det_eq_prod_eigenvalues

theorem trace_sum (A : MatR n) (hA : A.PosDef) :
    A.trace = ∑ i, hA.isHermitian.eigenvalues i :=
  hA.isHermitian.trace_eq_sum_eigenvalues

theorem determinant_positive (A : MatR n) (hA : A.PosDef) : 0 < A.det :=
  hA.det_pos

-- This checks actual Lebesgue volume on EuclideanSpace. Converting the
-- linear-map determinant to Matrix.det and adding translations remain G01V work.
theorem volume_linear_image (f : V n →ₗ[ℝ] V n) (s : Set (V n)) :
    volume (f '' s) = ENNReal.ofReal |LinearMap.det f| * volume s :=
  Measure.addHaar_image_linearMap volume f s

end Khachiyan.MathlibProbe
