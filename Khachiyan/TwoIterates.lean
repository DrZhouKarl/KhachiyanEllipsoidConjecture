import Khachiyan.TraceConstraint
import Khachiyan.IntermediateEllipsoid
import Khachiyan.MatrixPowers
import Khachiyan.RankOne
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Two intermediate iterations and spectral constraints

This module starts R01 of `proof.md`.  It keeps the normalized hypotheses
explicit: the unit ball is a genuine feasible maximizer, while the candidate
ellipsoid is supplied only by its actual containment and positive-definite
shape.  The shortened displacement is derived from the inverse action of the
candidate shape, rather than assumed as an additional matrix constraint.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set

namespace Khachiyan

variable {n : ℕ} [NeZero n]

theorem inv_action_mul_action {A : MatR n} (hA : A.PosDef) (x : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) A
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ x) = x := by
  have hm := Matrix.mul_nonsing_inv A (Matrix.isUnit_iff_isUnit_det A |>.mp hA.isUnit)
  have hv := congrArg (fun M : MatR n => Matrix.toEuclideanCLM (𝕜 := ℝ) M x) hm
  simpa [mul_apply_eq_comp] using hv

theorem shortened_direction {A : MatR n} {a : V n} (hA : A.PosDef)
    {rho : ℝ} (hrho : 0 < rho)
    (hrho_def : rho = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖) :
    let u := rho⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a
    let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
    ‖u‖ = 1 ∧ b = rho⁻¹ • a := by
  dsimp
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖ = rho := hrho_def.symm
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hrho, hnorm]
    field_simp
  · rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) A
        (rho⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a) =
        rho⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) A
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a) by simp]
    rw [inv_action_mul_action hA]

def r01Shape₁ (a : V n) (A : MatR n) : MatR n :=
  intermediateShape a A

def r01Shape₂ (a : V n) (A : MatR n) : MatR n :=
  intermediateShape ((1 / 2 : ℝ) • a) (r01Shape₁ a A)

theorem r01Shape₁_posDef {a : V n} {A : MatR n} (hA : A.PosDef) :
    (r01Shape₁ a A).PosDef :=
  intermediateShape_posDef hA

theorem r01Shape₂_posDef {a : V n} {A : MatR n} (hA : A.PosDef) :
    (r01Shape₂ a A).PosDef := by
  apply intermediateShape_posDef
  exact r01Shape₁_posDef hA

theorem r01Shape₁_trace_le {K : Set (V n)}
    (hK : IsJohnNormalized K) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    {a : V n} {A : MatR n} (hA : A.PosDef) (hell : ellipsoid a A ⊆ K) :
    (r01Shape₁ a A).trace ≤ n := by
  have hsub := intermediate_ellipsoid_subset hKconv hKclosed hK.unitBall_subset hell hA
  exact trace_le_of_isJohnNormalized hK hKconv (r01Shape₁_posDef hA) hsub

theorem r01Shape₂_trace_le {K : Set (V n)}
    (hK : IsJohnNormalized K) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    {a : V n} {A : MatR n} (hA : A.PosDef) (hell : ellipsoid a A ⊆ K) :
    (r01Shape₂ a A).trace ≤ n := by
  have h1 := intermediate_ellipsoid_subset hKconv hKclosed hK.unitBall_subset hell hA
  have h2 := intermediate_ellipsoid_subset hKconv hKclosed hK.unitBall_subset h1
    (r01Shape₁_posDef hA)
  exact trace_le_of_isJohnNormalized hK hKconv (r01Shape₂_posDef hA) h2

theorem shortened_outer_le {A : MatR n} {a : V n} (hA : A.PosDef)
    {rho : ℝ} (hrho : 1 ≤ rho) :
    outer (rho⁻¹ • a) ≤ outer a := by
  have hrho0 : 0 < rho := lt_of_lt_of_le (by norm_num) hrho
  have hc : (rho⁻¹ : ℝ) ^ 2 ≤ 1 := by
    rw [inv_pow]
    simpa [pow_two] using
      (mul_self_le_mul_self (by positivity : 0 ≤ rho⁻¹)
        (inv_le_one_of_one_le₀ hrho))
  have ho := outer_posSemidef a
  have hscalar : (rho⁻¹ : ℝ) ^ 2 • outer a ≤ outer a := by
    apply Matrix.le_iff.mpr
    have hps : ((1 : ℝ) - (rho⁻¹ : ℝ) ^ 2) • outer a |>.PosSemidef :=
      ho.smul (sub_nonneg.mpr hc)
    have heq : outer a - (rho⁻¹ : ℝ) ^ 2 • outer a =
        ((1 : ℝ) - (rho⁻¹ : ℝ) ^ 2) • outer a := by module
    rw [heq]
    exact hps
  have hout : outer (rho⁻¹ • a) = (rho⁻¹ : ℝ) ^ 2 • outer a := by
    ext i j
    simp [outer, smul_eq_mul, pow_two, mul_assoc, mul_left_comm, mul_comm]
  rw [hout]
  exact hscalar

theorem shortened_shape_le {A : MatR n} {a : V n} (hA : A.PosDef)
    {rho : ℝ} (hrho : 1 ≤ rho) :
    intermediateShape (rho⁻¹ • a) A ≤ intermediateShape a A := by
  apply MatrixPowers.sqrt_mono
  exact hA.posSemidef.add ((outer_posSemidef (rho⁻¹ • a)).smul (by norm_num))
  apply Matrix.le_iff.mpr
  simpa only [smul_sub, add_sub_add_left_eq_sub] using
    (shortened_outer_le hA hrho).smul (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ))

theorem sqrt_smul_sq {A : MatR n} (hA : A.PosDef) {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (c • A ^ 2) = Real.sqrt c • A := by
  have hnonneg : 0 ≤ Real.sqrt c • A := by
    change (0 : MatR n) ≤ Real.sqrt c • A
    apply Matrix.le_iff.mpr
    simpa using (hA.posSemidef.smul (Real.sqrt_nonneg c))
  have heq : c • A ^ 2 = (Real.sqrt c • A) ^ 2 := by
    symm
    ext i j
    simp [pow_two, smul_eq_mul]
    calc
      Real.sqrt c * (Real.sqrt c * (A * A) i j) =
          (Real.sqrt c) ^ 2 * (A * A) i j := by ring
      _ = c * (A * A) i j := by rw [Real.sq_sqrt hc]
  rw [heq, CFC.sqrt_sq _ hnonneg]

theorem r01_m1_le_scaled_sq {A : MatR n} (hA : A.PosDef) (u : V n)
    (hu : ‖u‖ = 1) :
    let α := Spectral.minEigenvalue hA.isHermitian
    let f₁ := Real.sqrt (α + α ^ 2 / 4)
    let M₁ := intermediateShape (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) A
    M₁ ≤ (f₁ / α ^ 2) • A ^ 2 := by
  dsimp
  let α := Spectral.minEigenvalue hA.isHermitian
  let f₁ := Real.sqrt (α + α ^ 2 / 4)
  let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
  let Q := A + (1 / 4 : ℝ) • outer b
  let M₁ := intermediateShape b A
  have hα : 0 < α := Spectral.minEigenvalue_pos hA
  have hQ : Q.PosDef := by
    dsimp [Q]
    exact hA.add_posSemidef ((outer_posSemidef b).smul (by norm_num))
  have houter : outer b ≤ A ^ 2 := RankOne.outer_image_le_sq hA.isHermitian u hu
  have hAorder : A ≤ α⁻¹ • A ^ 2 := Spectral.le_inv_minEigenvalue_smul_sq hA
  have hQle : Q ≤ (α⁻¹ + (1 / 4 : ℝ)) • A ^ 2 := by
    dsimp [Q]
    have houter' : (1 / 4 : ℝ) • outer b ≤ (1 / 4 : ℝ) • A ^ 2 := by
      apply Matrix.le_iff.mpr
      have hp := (Matrix.le_iff.mp houter).smul (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have heq : (1 / 4 : ℝ) • A ^ 2 - (1 / 4 : ℝ) • outer b =
          (1 / 4 : ℝ) • (A ^ 2 - outer b) := by module
      rw [heq]
      exact hp
    have h := add_le_add hAorder houter'
    rw [← add_smul] at h
    simpa [Matrix.le_iff] using h
  have hsqrt := MatrixPowers.sqrt_mono hQ.posSemidef hQle
  have hshape : M₁ = CFC.sqrt Q := rfl
  have hc : 0 ≤ α⁻¹ + (1 / 4 : ℝ) := by positivity
  rw [sqrt_smul_sq hA hc] at hsqrt
  have hscalar : Real.sqrt (α⁻¹ + (1 / 4 : ℝ)) * α⁻¹ = f₁ / α ^ 2 := by
    have hleft : 0 ≤ Real.sqrt (α⁻¹ + (1 / 4 : ℝ)) * α⁻¹ := by positivity
    have hright : 0 ≤ f₁ / α ^ 2 := by positivity
    have hsquare :
        (Real.sqrt (α⁻¹ + (1 / 4 : ℝ)) * α⁻¹) ^ 2 =
          (f₁ / α ^ 2) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hc,
        Real.sq_sqrt (show 0 ≤ α + α ^ 2 / 4 by positivity)]
      field_simp [hα.ne']
    nlinarith
  have hscaled' :
      Real.sqrt (α⁻¹ + (1 / 4 : ℝ)) • A ≤
        (Real.sqrt (α⁻¹ + (1 / 4 : ℝ)) * α⁻¹) • A ^ 2 := by
    apply Matrix.le_iff.mpr
    have hp := (Matrix.le_iff.mp hAorder).smul
      (show 0 ≤ Real.sqrt (α⁻¹ + (1 / 4 : ℝ)) by positivity)
    have heq :
        (Real.sqrt (α⁻¹ + (1 / 4 : ℝ)) * α⁻¹) • A ^ 2 -
            Real.sqrt (α⁻¹ + (1 / 4 : ℝ)) • A =
          Real.sqrt (α⁻¹ + (1 / 4 : ℝ)) • (α⁻¹ • A ^ 2 - A) := by
      module
    rw [heq]
    exact hp
  rw [hscalar] at hscaled'
  have hsqrt' : M₁ ≤ Real.sqrt (α⁻¹ + (1 / 4 : ℝ)) • A := by
    simpa only [M₁, Q, intermediateShape] using hsqrt
  exact hsqrt'.trans hscaled'

theorem trace_rpow_sqrt_half {Q : MatR n} (hQ : Q.PosDef) :
    (CFC.rpow (CFC.sqrt Q) (1 / 2 : ℝ)).trace =
      (CFC.rpow Q (1 / 4 : ℝ)).trace := by
  rw [CFC.sqrt_eq_rpow]
  have hpow := CFC.rpow_rpow Q (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num)
    hQ.isStrictlyPositive
  change (CFC.rpow (CFC.rpow Q (1 / 2 : ℝ)) (1 / 2 : ℝ)).trace = _
  rw [show CFC.rpow (CFC.rpow Q (1 / 2 : ℝ)) (1 / 2 : ℝ) =
    CFC.rpow Q (1 / 2 * (1 / 2 : ℝ)) by exact hpow]
  congr 1
  norm_num

theorem r01_m2_le_original {A : MatR n} {a : V n} (hA : A.PosDef)
    {rho : ℝ} (hrho : 1 ≤ rho) :
    r01Shape₂ (rho⁻¹ • a) A ≤ r01Shape₂ a A := by
  let b : V n := rho⁻¹ • a
  let M₁ : MatR n := r01Shape₁ b A
  let T₁ : MatR n := r01Shape₁ a A
  have hM₁ : M₁ ≤ T₁ := by
    dsimp [M₁, T₁, b]
    exact shortened_shape_le hA hrho
  have hout : outer b ≤ outer a := by
    dsimp [b]
    exact shortened_outer_le hA hrho
  have hout' : (1 / 16 : ℝ) • outer b ≤ (1 / 16 : ℝ) • outer a := by
    apply Matrix.le_iff.mpr
    have hp := (Matrix.le_iff.mp hout).smul (by norm_num : (0 : ℝ) ≤ 1 / 16)
    have heq : (1 / 16 : ℝ) • outer a - (1 / 16 : ℝ) • outer b =
        (1 / 16 : ℝ) • (outer a - outer b) := by module
    rw [heq]
    exact hp
  have hbase : M₁ + (1 / 16 : ℝ) • outer b ≤
      T₁ + (1 / 16 : ℝ) • outer a := add_le_add hM₁ hout'
  have hpos : (M₁ + (1 / 16 : ℝ) • outer b).PosSemidef := by
    exact (r01Shape₁_posDef hA).posSemidef.add
      ((outer_posSemidef b).smul (by norm_num))
  have hs := MatrixPowers.sqrt_mono hpos hbase
  have hscale (x : V n) :
      (1 / 4 : ℝ) • outer ((1 / 2 : ℝ) • x) =
        (1 / 16 : ℝ) • outer x := by
    ext i j
    simp [outer, smul_eq_mul]
    ring
  dsimp [r01Shape₂, r01Shape₁, intermediateShape, b, M₁, T₁]
  rw [hscale a, hscale (rho⁻¹ • a)]
  exact hs

theorem r01_first_increment {A : MatR n} (hA : A.PosDef) (u : V n)
    (hu : ‖u‖ = 1) :
    let α := Spectral.minEigenvalue hA.isHermitian
    let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
    let M₁ := intermediateShape b A
    (α + (1 / 4 : ℝ) * α ^ 2) ^ (1 / 2 : ℝ) - α ^ (1 / 2 : ℝ) ≤
      M₁.trace -
        (CFC.rpow A (1 / 2 : ℝ)).trace := by
  dsimp
  let α := Spectral.minEigenvalue hA.isHermitian
  have hα : 0 < α := Spectral.minEigenvalue_pos hA
  have hMA : A ≤ (α / α ^ 2) • A ^ 2 := by
    have h := Spectral.le_inv_minEigenvalue_smul_sq hA
    have he : α / α ^ 2 = α⁻¹ := by field_simp [hα.ne']
    rw [he]
    simpa [α] using h
  have hinc := RankOne.trace_increment_lower_bound hA hA u hu
    hα hMA (by constructor <;> norm_num : (1 / 2 : ℝ) ∈ Set.Ioo 0 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hshape : intermediateShape (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) A =
      CFC.sqrt (A + (1 / 4 : ℝ) •
        outer (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)) := rfl
  simpa [hshape, CFC.sqrt_eq_rpow, Real.sqrt_eq_rpow, α] using hinc

theorem r01_second_increment {A : MatR n} (hA : A.PosDef) (u : V n)
    (hu : ‖u‖ = 1) :
    let α := Spectral.minEigenvalue hA.isHermitian
    let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
    let Q := A + (1 / 4 : ℝ) • outer b
    (α + (1 / 4 : ℝ) * α ^ 2) ^ (1 / 4 : ℝ) - α ^ (1 / 4 : ℝ) ≤
      (CFC.rpow Q (1 / 4 : ℝ)).trace -
        (CFC.rpow A (1 / 4 : ℝ)).trace := by
  dsimp
  let α := Spectral.minEigenvalue hA.isHermitian
  let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
  let Q := A + (1 / 4 : ℝ) • outer b
  have hα : 0 < α := Spectral.minEigenvalue_pos hA
  have hMA : A ≤ (α / α ^ 2) • A ^ 2 := by
    have h := Spectral.le_inv_minEigenvalue_smul_sq hA
    have he : α / α ^ 2 = α⁻¹ := by field_simp [hα.ne']
    rw [he]
    simpa [α] using h
  have hinc := RankOne.trace_increment_lower_bound hA hA u hu hα hMA
    (by constructor <;> norm_num : (1 / 4 : ℝ) ∈ Set.Ioo 0 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  simpa [Q, α] using hinc

theorem r01_third_increment {A : MatR n} (hA : A.PosDef) (u : V n)
    (hu : ‖u‖ = 1) :
    let α := Spectral.minEigenvalue hA.isHermitian
    let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
    let M₁ := intermediateShape b A
    let f₁ := Real.sqrt (α + α ^ 2 / 4)
    let M₂ := intermediateShape ((1 / 2 : ℝ) • b) M₁
    (f₁ + (1 / 16 : ℝ) * α ^ 2) ^ (1 / 2 : ℝ) - f₁ ^ (1 / 2 : ℝ) ≤
      M₂.trace - (CFC.rpow M₁ (1 / 2 : ℝ)).trace := by
  dsimp
  let α := Spectral.minEigenvalue hA.isHermitian
  let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
  let M₁ := intermediateShape b A
  let f₁ := Real.sqrt (α + α ^ 2 / 4)
  let M₂ := intermediateShape ((1 / 2 : ℝ) • b) M₁
  have hα : 0 < α := Spectral.minEigenvalue_pos hA
  have hf₁ : 0 < f₁ := by positivity
  have hM₁ : M₁.PosDef := intermediateShape_posDef hA
  have hMA : M₁ ≤ (f₁ / α ^ 2) • A ^ 2 := by
    simpa [M₁, f₁, α] using r01_m1_le_scaled_sq hA u hu
  have hinc := RankOne.trace_increment_lower_bound hA hM₁ u hu hf₁ hMA
    (by constructor <;> norm_num : (1 / 2 : ℝ) ∈ Set.Ioo 0 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have hshape : M₂ = CFC.sqrt (M₁ + (1 / 16 : ℝ) • outer b) := by
    dsimp [M₂, intermediateShape]
    have hscale : (1 / 4 : ℝ) • outer ((1 / 2 : ℝ) • b) =
        (1 / 16 : ℝ) • outer b := by
      ext i j
      simp [outer, smul_eq_mul]
      ring
    rw [hscale]
  have htrace :
      (CFC.rpow (M₁ + (1 / 16 : ℝ) • outer b) (1 / 2 : ℝ)).trace = M₂.trace := by
    simpa [hshape, CFC.sqrt_eq_rpow]
  rw [← htrace]
  simpa [f₁, α] using hinc

/-!
The second M04 increment is stated at exponent `1 / 4`, whereas the third
increment starts from the square-root trace of the first intermediate shape.
The following bridge is the exact place where `trace_rpow_sqrt_half` is used:
`M₁ = sqrt Q`, so `tr (Q ^ (1/4)) = tr (M₁ ^ (1/2))`.  Adding the second
and third inequalities then cancels this intermediate trace and yields the
second spectral constraint.
-/

theorem r01_second_third_combined {A : MatR n} (hA : A.PosDef) (u : V n)
    (hu : ‖u‖ = 1) :
    let α := Spectral.minEigenvalue hA.isHermitian
    let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
    let Q := A + (1 / 4 : ℝ) • outer b
    let M₁ := intermediateShape b A
    let f₁ := Real.sqrt (α + α ^ 2 / 4)
    let f₂ := Real.sqrt (f₁ + α ^ 2 / 16)
    let M₂ := intermediateShape ((1 / 2 : ℝ) • b) M₁
    f₂ - α ^ (1 / 4 : ℝ) ≤
      M₂.trace - (CFC.rpow A (1 / 4 : ℝ)).trace := by
  dsimp
  let α := Spectral.minEigenvalue hA.isHermitian
  let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
  let Q := A + (1 / 4 : ℝ) • outer b
  let M₁ := intermediateShape b A
  let f₁ := Real.sqrt (α + α ^ 2 / 4)
  let f₂ := Real.sqrt (f₁ + α ^ 2 / 16)
  let M₂ := intermediateShape ((1 / 2 : ℝ) • b) M₁
  have hQ : Q.PosDef := by
    dsimp [Q]
    exact hA.add_posSemidef ((outer_posSemidef b).smul (by norm_num))
  have hsecond := r01_second_increment hA u hu
  have hthird := r01_third_increment hA u hu
  have hbridge :
      (CFC.rpow Q (1 / 4 : ℝ)).trace =
        (CFC.rpow M₁ (1 / 2 : ℝ)).trace := by
    have hsqrt : M₁ = CFC.sqrt Q := rfl
    rw [hsqrt]
    exact (trace_rpow_sqrt_half hQ).symm
  have hpow : f₁ ^ (1 / 2 : ℝ) =
      (α + (1 / 4 : ℝ) * α ^ 2) ^ (1 / 4 : ℝ) := by
    change (Real.sqrt (α + α ^ 2 / 4)) ^ (1 / 2 : ℝ) = _
    have hα : 0 < α := by
      dsimp [α]
      exact Spectral.minEigenvalue_pos hA
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (by positivity : 0 ≤ α + α ^ 2 / 4)]
    congr 1
    · ring
    · norm_num
  have hsecond' :
      f₁ ^ (1 / 2 : ℝ) - α ^ (1 / 4 : ℝ) ≤
        (CFC.rpow Q (1 / 4 : ℝ)).trace -
          (CFC.rpow A (1 / 4 : ℝ)).trace := by
    rw [hpow]
    simpa [Q, b, α] using hsecond
  have hthird' :
      f₂ - f₁ ^ (1 / 2 : ℝ) ≤
        M₂.trace - (CFC.rpow M₁ (1 / 2 : ℝ)).trace := by
    dsimp [M₂, M₁, b, f₂, f₁, α]
    rw [Real.sqrt_eq_rpow]
    convert hthird using 1 <;> ring
  rw [hbridge] at hsecond'
  calc
    f₂ - α ^ (1 / 4 : ℝ) =
        (f₁ ^ (1 / 2 : ℝ) - α ^ (1 / 4 : ℝ)) +
          (f₂ - f₁ ^ (1 / 2 : ℝ)) := by ring
    _ ≤ ((CFC.rpow M₁ (1 / 2 : ℝ)).trace -
          (CFC.rpow A (1 / 4 : ℝ)).trace) +
          (M₂.trace - (CFC.rpow M₁ (1 / 2 : ℝ)).trace) :=
      add_le_add hsecond' hthird'
    _ = M₂.trace - (CFC.rpow A (1 / 4 : ℝ)).trace := by ring

/-!
The two inequalities below are the formal versions of (R01.1).  The first
uses the first M04 increment and the trace bound for the first intermediate
ellipsoid.  The second uses `r01_second_third_combined` and the trace bound for
the second intermediate ellipsoid.  The spectral sums remove exactly one
occurrence of the minimum eigenvalue, so multiplicities are preserved.
-/

theorem r01_constraint_one {K : Set (V n)}
    (hK : IsJohnNormalized K) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    {a : V n} {A : MatR n} (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    {rho : ℝ} (hrho : 1 ≤ rho)
    (hrho_def : rho = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖) :
    let α := Spectral.minEigenvalue hA.isHermitian
    let u := rho⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a
    let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
    let M₁ := intermediateShape b A
    let f₁ := Real.sqrt (α + α ^ 2 / 4)
    f₁ + ∑ i ∈ Finset.univ.erase (Spectral.minIndex hA.isHermitian),
        (hA.isHermitian.eigenvalues i) ^ (1 / 2 : ℝ) ≤ n := by
  dsimp
  let α := Spectral.minEigenvalue hA.isHermitian
  let u := rho⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a
  let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
  let M₁ := intermediateShape b A
  let f₁ := Real.sqrt (α + α ^ 2 / 4)
  have hrho0 : 0 < rho := lt_of_lt_of_le (by norm_num) hrho
  have hdir := shortened_direction hA hrho0 hrho_def
  have hu : ‖u‖ = 1 := by simpa [u] using hdir.1
  have hdir' : b = rho⁻¹ • a := by simpa [u, b] using hdir.2
  have htrace : M₁.trace ≤ n := by
    have hT : (r01Shape₁ a A).trace ≤ n :=
      r01Shape₁_trace_le hK hKconv hKclosed hA hell
    have hle : M₁ ≤ r01Shape₁ a A := by
      change intermediateShape b A ≤ intermediateShape a A
      rw [hdir']
      exact shortened_shape_le hA hrho
    exact (Spectral.trace_mono hle).trans hT
  have hinc := r01_first_increment hA u hu
  have hsum :
      (CFC.rpow A (1 / 2 : ℝ)).trace =
        α ^ (1 / 2 : ℝ) +
          ∑ i ∈ Finset.univ.erase (Spectral.minIndex hA.isHermitian),
            (hA.isHermitian.eigenvalues i) ^ (1 / 2 : ℝ) := by
    simpa [α] using Spectral.trace_rpow_eq_min_add_sum_erase hA (1 / 2 : ℝ)
  rw [hsum] at hinc
  have hf₁ : f₁ = (α + (1 / 4 : ℝ) * α ^ 2) ^ (1 / 2 : ℝ) := by
    change Real.sqrt (α + α ^ 2 / 4) = _
    rw [Real.sqrt_eq_rpow]
    congr 1
    ring
  have hinc' :
      f₁ - α ^ (1 / 2 : ℝ) ≤
        M₁.trace -
          (α ^ (1 / 2 : ℝ) +
            ∑ i ∈ Finset.univ.erase (Spectral.minIndex hA.isHermitian),
              (hA.isHermitian.eigenvalues i) ^ (1 / 2 : ℝ)) := by
    rw [hf₁]
    simpa [M₁, b, u, α] using hinc
  change f₁ + ∑ i ∈ Finset.univ.erase (Spectral.minIndex hA.isHermitian),
      (hA.isHermitian.eigenvalues i) ^ (1 / 2 : ℝ) ≤ n
  linarith

theorem r01_constraint_two {K : Set (V n)}
    (hK : IsJohnNormalized K) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    {a : V n} {A : MatR n} (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    {rho : ℝ} (hrho : 1 ≤ rho)
    (hrho_def : rho = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖) :
    let α := Spectral.minEigenvalue hA.isHermitian
    let u := rho⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a
    let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
    let M₁ := intermediateShape b A
    let f₁ := Real.sqrt (α + α ^ 2 / 4)
    let f₂ := Real.sqrt (f₁ + α ^ 2 / 16)
    let M₂ := intermediateShape ((1 / 2 : ℝ) • b) M₁
    f₂ + ∑ i ∈ Finset.univ.erase (Spectral.minIndex hA.isHermitian),
        (hA.isHermitian.eigenvalues i) ^ (1 / 4 : ℝ) ≤ n := by
  dsimp
  let α := Spectral.minEigenvalue hA.isHermitian
  let u := rho⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a
  let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
  let M₁ := intermediateShape b A
  let f₁ := Real.sqrt (α + α ^ 2 / 4)
  let f₂ := Real.sqrt (f₁ + α ^ 2 / 16)
  let M₂ := intermediateShape ((1 / 2 : ℝ) • b) M₁
  have hrho0 : 0 < rho := lt_of_lt_of_le (by norm_num) hrho
  have hdir := shortened_direction hA hrho0 hrho_def
  have hu : ‖u‖ = 1 := by simpa [u] using hdir.1
  have hdir' : b = rho⁻¹ • a := by simpa [u, b] using hdir.2
  have htrace : M₂.trace ≤ n := by
    have hT : (r01Shape₂ a A).trace ≤ n :=
      r01Shape₂_trace_le hK hKconv hKclosed hA hell
    have hle : M₂ ≤ r01Shape₂ a A := by
      change intermediateShape ((1 / 2 : ℝ) • b) (intermediateShape b A) ≤
        r01Shape₂ a A
      rw [hdir']
      exact r01_m2_le_original (a := a) hA hrho
    exact (Spectral.trace_mono hle).trans hT
  have hinc := r01_second_third_combined hA u hu
  have hsum :
      (CFC.rpow A (1 / 4 : ℝ)).trace =
        α ^ (1 / 4 : ℝ) +
          ∑ i ∈ Finset.univ.erase (Spectral.minIndex hA.isHermitian),
            (hA.isHermitian.eigenvalues i) ^ (1 / 4 : ℝ) := by
    simpa [α] using Spectral.trace_rpow_eq_min_add_sum_erase hA (1 / 4 : ℝ)
  rw [hsum] at hinc
  have hinc' :
      f₂ - α ^ (1 / 4 : ℝ) ≤
        M₂.trace -
          (α ^ (1 / 4 : ℝ) +
            ∑ i ∈ Finset.univ.erase (Spectral.minIndex hA.isHermitian),
              (hA.isHermitian.eigenvalues i) ^ (1 / 4 : ℝ)) := by
    simpa [M₂, M₁, f₂, f₁, b, u, α, Real.sqrt_eq_rpow] using hinc
  change f₂ + ∑ i ∈ Finset.univ.erase (Spectral.minIndex hA.isHermitian),
      (hA.isHermitian.eigenvalues i) ^ (1 / 4 : ℝ) ≤ n
  linarith

end Khachiyan
