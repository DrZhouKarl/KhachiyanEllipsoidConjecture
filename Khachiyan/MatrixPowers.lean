import Khachiyan.MatrixBridge
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Order properties of real matrix powers

This module formalizes the order assertions in M02 of `proof.md` and the real
matrix adapter in Section 2.2 of `formalization_plan.md`. The adapter embeds real
matrices into complex matrices as a real star algebra homomorphism. Only the
complex matrix algebra uses the complex C*-algebra instance.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix

namespace Khachiyan.MatrixPowers

abbrev MatC (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

variable {n : ℕ}

/-- Entrywise complexification, as a homomorphism of real star algebras. -/
def complexify : MatR n →⋆ₐ[ℝ] MatC n :=
  { (Algebra.ofId ℝ ℂ).mapMatrix with
    map_star' A := by
      ext i j
      simp [AlgHom.mapMatrix_apply, Matrix.star_eq_conjTranspose] }

@[simp] theorem complexify_apply (A : MatR n) (i j : Fin n) :
    complexify A i j = (A i j : ℂ) := rfl

theorem complexify_injective : Function.Injective (complexify (n := n)) := by
  intro A B h
  ext i j
  exact Complex.ofReal_injective (congrFun (congrFun h i) j)

theorem continuous_complexify : Continuous (complexify (n := n)) :=
  complexify.toAlgHom.toLinearMap.continuous_of_finiteDimensional

theorem complexify_isHermitian {A : MatR n} (hA : A.IsHermitian) :
    (complexify A).IsHermitian := by
  change star (complexify A) = complexify A
  rw [← map_star, show star A = A from hA]

theorem complexify_posSemidef {A : MatR n} (hA : A.PosSemidef) :
    (complexify A).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp (map_nonneg complexify hA.nonneg)

theorem complexify_quadratic (A : MatR n) (x : Fin n → ℝ) :
    star (fun i => (x i : ℂ)) ⬝ᵥ (complexify A *ᵥ (fun i => (x i : ℂ))) =
      ((star x ⬝ᵥ (A *ᵥ x) : ℝ) : ℂ) := by
  simp [dotProduct, Matrix.mulVec]

theorem posSemidef_of_complexify {A : MatR n} (hA : (complexify A).PosSemidef) :
    A.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · change star A = A
    apply complexify_injective
    rw [map_star]
    exact hA.isHermitian
  · intro x
    have h := hA.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
    rw [complexify_quadratic] at h
    exact Complex.zero_le_real.mp h

theorem complexify_posSemidef_iff (A : MatR n) :
    (complexify A).PosSemidef ↔ A.PosSemidef :=
  ⟨posSemidef_of_complexify, complexify_posSemidef⟩

theorem complexify_le_iff (A B : MatR n) : complexify A ≤ complexify B ↔ A ≤ B := by
  rw [Matrix.le_iff, ← map_sub, complexify_posSemidef_iff, Matrix.le_iff]

theorem complexify_posDef {A : MatR n} (hA : A.PosDef) : (complexify A).PosDef := by
  have hu : IsUnit (complexify A) := hA.isUnit.map complexify.toMonoidHom
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (hu.isStrictlyPositive (complexify_posSemidef hA.posSemidef).nonneg)

theorem complexify_cfc {A : MatR n} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    complexify (cfc f A) = cfc f (complexify A) := by
  exact complexify.map_cfc f A ((Matrix.finite_real_spectrum (A := A)).continuousOn f)
    continuous_complexify hA.isSelfAdjoint (complexify_isHermitian hA).isSelfAdjoint

theorem complexify_rpow {A : MatR n} (hA : A.PosSemidef) (p : ℝ) :
    complexify (CFC.rpow A p) = CFC.rpow (complexify A) p := by
  have hr : CFC.rpow A p = cfc (fun t : ℝ => t ^ p) A :=
    CFC.rpow_eq_cfc_real hA.nonneg
  have hc : CFC.rpow (complexify A) p = cfc (fun t : ℝ => t ^ p) (complexify A) :=
    CFC.rpow_eq_cfc_real (complexify_posSemidef hA).nonneg
  rw [hr, hc, complexify_cfc hA.isHermitian]

/-- Real matrix fractional powers preserve Loewner order for exponents in `[0,1]`. -/
theorem rpow_mono {X Y : MatR n} {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hX : X.PosSemidef) (hXY : X ≤ Y) : CFC.rpow X p ≤ CFC.rpow Y p := by
  have hY : Y.PosSemidef := (hX.nonneg.trans hXY).posSemidef
  apply (complexify_le_iff _ _).mp
  rw [complexify_rpow hX, complexify_rpow hY]
  exact CFC.monotone_rpow (A := MatC n) hp ((complexify_le_iff X Y).mpr hXY)

theorem sqrt_mono {X Y : MatR n} (hX : X.PosSemidef) (hXY : X ≤ Y) :
    CFC.sqrt X ≤ CFC.sqrt Y := by
  have hx : CFC.sqrt X = CFC.rpow X (1 / 2 : ℝ) := CFC.sqrt_eq_rpow
  have hy : CFC.sqrt Y = CFC.rpow Y (1 / 2 : ℝ) := CFC.sqrt_eq_rpow
  rw [hx, hy]
  exact rpow_mono (by constructor <;> norm_num) hX hXY

theorem posDef_of_le {X Y : MatR n} (hX : X.PosDef) (hXY : X ≤ Y) : Y.PosDef := by
  convert hX.add_posSemidef (Matrix.le_iff.mp hXY) using 1
  abel

theorem inv_eq_rpow_neg_one {A : MatR n} (hA : A.PosDef) :
    A⁻¹ = CFC.rpow A (-1 : ℝ) := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact CFC.inverse_eq_rpow_neg_one hA.isStrictlyPositive

theorem complexify_inv {A : MatR n} (hA : A.PosDef) :
    complexify A⁻¹ = (complexify A)⁻¹ := by
  have hc : (complexify A)⁻¹ = CFC.rpow (complexify A) (-1 : ℝ) := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    exact CFC.inverse_eq_rpow_neg_one (complexify_posDef hA).isStrictlyPositive
  rw [inv_eq_rpow_neg_one hA, complexify_rpow hA.posSemidef, hc]

/-- Matrix inversion reverses Loewner order above a positive definite lower matrix. -/
theorem inv_antitone {X Y : MatR n} (hX : X.PosDef) (hXY : X ≤ Y) : Y⁻¹ ≤ X⁻¹ := by
  have hY := posDef_of_le hX hXY
  apply (complexify_le_iff _ _).mp
  rw [complexify_inv hY, complexify_inv hX, Matrix.nonsing_inv_eq_ringInverse,
    Matrix.nonsing_inv_eq_ringInverse]
  exact CStarAlgebra.ringInverse_le_ringInverse ((complexify_le_iff X Y).mpr hXY)
    (complexify_posDef hX).isStrictlyPositive

theorem inv_rpow {A : MatR n} (hA : A.PosDef) (p : ℝ) :
    (CFC.rpow A p)⁻¹ = CFC.rpow A (-p) := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  by_cases hp : p = 0
  · subst p
    have h0 : CFC.rpow A (0 : ℝ) = 1 := CFC.rpow_zero A hA.posSemidef.nonneg
    simp only [neg_zero, h0]
    simp
  · exact CFC.inverse_rpow A p hp hA.isStrictlyPositive

/-- Real matrix powers reverse order for every exponent in `[-1,0]`. -/
theorem rpow_antitone {X Y : MatR n} {p : ℝ} (hp : p ∈ Set.Icc (-1 : ℝ) 0)
    (hX : X.PosDef) (hXY : X ≤ Y) : CFC.rpow Y p ≤ CFC.rpow X p := by
  have hY := posDef_of_le hX hXY
  have hneg : -p ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hp.1, hp.2]
  have horder := rpow_mono hneg hX.posSemidef hXY
  have h := inv_antitone (Spectral.rpow_posDef hX (-p)) horder
  rwa [inv_rpow hY (-p), inv_rpow hX (-p), neg_neg] at h

/-- The negative exponent required by M03 and M04. -/
theorem rpow_sub_one_antitone {X Y : MatR n} {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hX : X.PosDef) (hXY : X ≤ Y) : CFC.rpow Y (p - 1) ≤ CFC.rpow X (p - 1) :=
  rpow_antitone (by constructor <;> linarith [hp.1, hp.2]) hX hXY

end Khachiyan.MatrixPowers
