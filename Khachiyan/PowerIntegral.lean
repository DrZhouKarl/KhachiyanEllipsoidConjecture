import Khachiyan.MatrixBridge
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The real matrix power integral

This module formalizes M02.1 of `proof.md`, including the positive normalization
constant and integrability. The finite spectral calculus commutes with integration
through a continuous linear map, without differentiating eigenvalues.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory Set

namespace Khachiyan.PowerIntegral

def powerNormalization (p : ℝ) : ℝ :=
  (∫ s in Ioi (0 : ℝ), s ^ (p - 1) / (1 + s))⁻¹

theorem scalar_kernel_one_eq {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {s : ℝ}
    (hs : s ∈ Ioi (0 : ℝ)) :
    Real.rpowIntegrand₀₁ p s 1 = s ^ (p - 1) / (1 + s) := by
  rw [Real.rpowIntegrand₀₁_eq_pow_div hp hs.le (by norm_num)]
  simp [add_comm]

theorem integrable_normalization_kernel {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun s : ℝ => s ^ (p - 1) / (1 + s)) (Ioi 0) := by
  exact (integrableOn_congr_fun (fun s hs => scalar_kernel_one_eq hp hs)
    measurableSet_Ioi).mp (Real.integrableOn_rpowIntegrand₀₁_Ioi hp (by norm_num))

theorem normalization_eq_inverse_integral {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    powerNormalization p = (∫ s in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p s 1)⁻¹ := by
  unfold powerNormalization
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  exact (scalar_kernel_one_eq hp hs).symm

theorem powerNormalization_pos {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < powerNormalization p := by
  rw [normalization_eq_inverse_integral hp]
  exact inv_pos.mpr (Real.integral_rpowIntegrand₀₁_one_pos hp)

variable {n : ℕ} {A : MatR n}

/-- A continuous linear map from spectral coefficients to a matrix in the fixed eigenbasis. -/
def spectralCLM (hA : A.IsHermitian) : (Fin n → ℝ) →L[ℝ] MatR n :=
  LinearMap.toContinuousLinearMap
    ((Unitary.conjStarAlgAut ℝ (MatR n) hA.eigenvectorUnitary).toStarAlgHom.toAlgHom.toLinearMap.comp
      (Matrix.diagonalLinearMap (n := Fin n) (α := ℝ) (R := ℝ)))

theorem spectralCLM_apply (hA : A.IsHermitian) (v : Fin n → ℝ) :
    spectralCLM hA v = (hA.eigenvectorUnitary : MatR n) * diagonal v *
      star (hA.eigenvectorUnitary : MatR n) := rfl

theorem spectralCLM_cfc (hA : A.IsHermitian) (f : ℝ → ℝ) :
    spectralCLM hA (fun i => f (hA.eigenvalues i)) = cfc f A := by
  rw [spectralCLM_apply, Spectral.cfc_spectral hA]

theorem integrable_cfc_spectrum (hA : A.IsHermitian) (f : ℝ → ℝ → ℝ)
    (hf : ∀ i, IntegrableOn (fun s => f s (hA.eigenvalues i)) (Ioi 0)) :
    IntegrableOn (fun s => cfc (f s) A) (Ioi 0) := by
  change Integrable (fun s => cfc (f s) A) (volume.restrict (Ioi 0))
  have hv : IntegrableOn (fun s i => f s (hA.eigenvalues i)) (Ioi 0) :=
    integrable_pi_iff.mpr hf
  simpa only [Function.comp_def, spectralCLM_cfc] using (spectralCLM hA).integrable_comp hv

theorem integral_cfc_spectrum (hA : A.IsHermitian) (f : ℝ → ℝ → ℝ)
    (hf : ∀ i, IntegrableOn (fun s => f s (hA.eigenvalues i)) (Ioi 0)) :
    (∫ s in Ioi (0 : ℝ), cfc (f s) A) = cfc (fun x => ∫ s in Ioi (0 : ℝ), f s x) A := by
  have hv : IntegrableOn (fun s i => f s (hA.eigenvalues i)) (Ioi 0) :=
    integrable_pi_iff.mpr hf
  calc
    _ = ∫ s in Ioi (0 : ℝ), spectralCLM hA (fun i => f s (hA.eigenvalues i)) := by
      simp only [spectralCLM_cfc]
    _ = spectralCLM hA (∫ s in Ioi (0 : ℝ), fun i => f s (hA.eigenvalues i)) :=
      (spectralCLM hA).integral_comp_comm hv
    _ = spectralCLM hA (fun i => ∫ s in Ioi (0 : ℝ), f s (hA.eigenvalues i)) := by
      congr 1
      funext i
      exact MeasureTheory.eval_integral hf i
    _ = _ := spectralCLM_cfc hA (fun x => ∫ s in Ioi (0 : ℝ), f s x)

theorem integrable_cfc_kernel (hA : A.PosDef) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun s => cfc (Real.rpowIntegrand₀₁ p s) A) (Ioi 0) :=
  integrable_cfc_spectrum hA.isHermitian (Real.rpowIntegrand₀₁ p)
    (fun i => Real.integrableOn_rpowIntegrand₀₁_Ioi hp (hA.eigenvalues_pos i).le)

theorem rpow_eq_normalization_smul_integral_cfc (hA : A.PosDef) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    CFC.rpow A p = powerNormalization p •
      ∫ s in Ioi (0 : ℝ), cfc (Real.rpowIntegrand₀₁ p s) A := by
  have hi := fun i => Real.integrableOn_rpowIntegrand₀₁_Ioi hp (hA.eigenvalues_pos i).le
  rw [integral_cfc_spectrum hA.isHermitian (Real.rpowIntegrand₀₁ p) hi,
    ← cfc_const_mul _ _ _ ((Matrix.finite_real_spectrum (A := A)).continuousOn _),
    Spectral.rpow_eq_cfc hA p]
  apply cfc_congr
  intro x hx
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [normalization_eq_inverse_integral hp]
  exact Real.rpow_eq_const_mul_integral hp (hA.eigenvalues_pos i).le

/-- The resolvent kernel in the precise formula M02.1. -/
def resolventKernel (p s : ℝ) (A : MatR n) : MatR n :=
  s ^ (p - 1) • (A * (A + s • (1 : MatR n))⁻¹)

theorem cfc_kernel_eq_resolvent (hA : A.PosDef) {p s : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) :
    cfc (Real.rpowIntegrand₀₁ p s) A = resolventKernel p s A := by
  have hspec : ∀ x ∈ spectrum ℝ A, 0 < x := by
    intro x hx
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hA.eigenvalues_pos i
  have hf : cfc (fun x : ℝ => s ^ (p - 1) * x) A = s ^ (p - 1) • A :=
    cfc_const_mul_id _ A hA.isHermitian.isSelfAdjoint
  have hg : cfc (fun x : ℝ => s + x) A = s • (1 : MatR n) + A := by
    rw [cfc_const_add s (fun x : ℝ => x) A (by fun_prop) hA.isHermitian.isSelfAdjoint,
      cfc_id' ℝ A hA.isHermitian.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  calc
    _ = cfc (fun x : ℝ => s ^ (p - 1) * x / (s + x)) A :=
      cfc_congr (fun x hx => Real.rpowIntegrand₀₁_eq_pow_div hp hs.le (hspec x hx).le)
    _ = _ := by
      rw [cfc_map_div (fun x : ℝ => s ^ (p - 1) * x) (fun x : ℝ => s + x) A
        (fun x hx => (add_pos hs (hspec x hx)).ne') (by fun_prop) (by fun_prop)
        hA.isHermitian.isSelfAdjoint, hf, hg, ← Matrix.nonsing_inv_eq_ringInverse]
      rw [add_comm (s • (1 : MatR n)) A, smul_mul]
      rfl

theorem integrable_resolvent_kernel (hA : A.PosDef) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun s => resolventKernel p s A) (Ioi 0) := by
  exact (integrableOn_congr_fun (fun s hs => cfc_kernel_eq_resolvent hA hp hs)
    measurableSet_Ioi).mp (integrable_cfc_kernel hA hp)

/-- M02.1 with actual Lebesgue integration and the specified positive constant. -/
theorem rpow_eq_integral (hA : A.PosDef) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    CFC.rpow A p = powerNormalization p •
      ∫ s in Ioi (0 : ℝ), s ^ (p - 1) • (A * (A + s • (1 : MatR n))⁻¹) := by
  rw [rpow_eq_normalization_smul_integral_cfc hA hp]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  exact cfc_kernel_eq_resolvent hA hp hs

end Khachiyan.PowerIntegral
