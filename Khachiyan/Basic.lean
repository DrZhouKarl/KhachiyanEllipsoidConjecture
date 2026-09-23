import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Foundational definitions and type bridges

This module implements B01 of `formalization_plan.md`, corresponding to the
definitions in Section 0 of `proof.md`. Geometry uses the Euclidean norm, matrix
order is Loewner order, and volume is the canonical Lebesgue measure.

Definitions allow dimension zero and degenerate shape matrices where useful for
limits. Feasibility requires `Matrix.PosDef`; the eventual T01 theorem must
separately require positive dimension and a nonzero halfspace normal.
Existence of a maximal ellipsoid and the determinant-to-volume bridge are later
obligations, not assumptions built into the definition of a convex body.
-/

noncomputable section

open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix MeasureTheory

namespace Khachiyan

abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev MatR (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The dimension-independent constant in T01 and T02. -/
def rStar : ℝ := Real.exp (1 / 2 : ℝ) / 2

/-- The closed Euclidean unit ball. -/
def unitBall (n : ℕ) : Set (V n) := Metric.closedBall 0 1

/-- The affine image of the unit ball; the definition also allows singular shapes. -/
def ellipsoid {n : ℕ} (a : V n) (A : MatR n) : Set (V n) :=
  (fun y => a + Matrix.toEuclideanCLM (𝕜 := ℝ) A y) '' unitBall n

/-- The real symmetric outer product $bb^{\mathsf T}$. -/
def outer {n : ℕ} (b : V n) : MatR n := fun i j => b i * b j

/-- A compact convex set with nonempty interior, as in Section 0 of `proof.md`. -/
def IsConvexBody {n : ℕ} (K : Set (V n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- A nondegenerate ellipsoid contained in the given set. -/
def IsFeasible {n : ℕ} (K : Set (V n)) (a : V n) (A : MatR n) : Prop :=
  A.PosDef ∧ ellipsoid a A ⊆ K

/-- Supremum of actual Lebesgue volumes of all feasible ellipsoids.

Finiteness for convex bodies is proved below; positivity and attainment remain
later obligations. The definition applies to arbitrary sets without choosing a maximizer.
-/
def maxEllipsoidVolume {n : ℕ} (K : Set (V n)) : ℝ≥0∞ :=
  ⨆ (a : V n) (A : MatR n) (_ : IsFeasible K a A), volume (ellipsoid a A)

/-- Actual global maximality of the determinant among all feasible shapes.

G01V will connect this condition to maximal Lebesgue volume. No trace or
fractional-power inequality is included in this certificate.
-/
structure IsMaxDet {n : ℕ} (K : Set (V n)) (c : V n) (S : MatR n) : Prop where
  feasible : IsFeasible K c S
  det_le : ∀ (a : V n) (A : MatR n), IsFeasible K a A → A.det ≤ S.det

/-- The unit ball is a feasible ellipsoid with globally maximal determinant. -/
abbrev IsJohnNormalized {n : ℕ} (K : Set (V n)) : Prop := IsMaxDet K 0 1

/-- A closed halfspace through `c` when `v` is nonzero, oriented by `v`. -/
def centralHalfspace {n : ℕ} (c v : V n) : Set (V n) :=
  {x | 0 ≤ ⟪v, x - c⟫}

theorem rStar_pos : 0 < rStar :=
  div_pos (Real.exp_pos _) (by norm_num)

variable {n : ℕ}

@[simp] theorem mem_unitBall (x : V n) : x ∈ unitBall n ↔ ‖x‖ ≤ 1 := by
  simp [unitBall, Metric.mem_closedBall]

theorem matrix_le_iff (A B : MatR n) : A ≤ B ↔ (B - A).PosSemidef :=
  Matrix.le_iff

theorem matrix_strictlyPositive_iff (A : MatR n) : IsStrictlyPositive A ↔ A.PosDef :=
  Matrix.isStrictlyPositive_iff_posDef

theorem matrix_action_ofLp (A : MatR n) (x : V n) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A x).ofLp = A *ᵥ x.ofLp :=
  Matrix.ofLp_toEuclideanCLM A x

theorem inner_matrix_action (A : MatR n) (x y : V n) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A y⟫ = x.ofLp ⬝ᵥ (A *ᵥ y.ofLp) :=
  Matrix.inner_toEuclideanCLM A x y

theorem inner_eq_dotProduct (x y : V n) : ⟪x, y⟫ = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

@[simp] theorem outer_apply (b : V n) (i j : Fin n) : outer b i j = b i * b j := rfl

theorem outer_eq_vecMulVec (b : V n) : outer b = vecMulVec b.ofLp b.ofLp := rfl

theorem outer_posSemidef (b : V n) : (outer b).PosSemidef := by
  rw [outer_eq_vecMulVec]
  simpa using Matrix.posSemidef_vecMulVec_self_star b.ofLp

theorem outer_action (b x : V n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (outer b) x = ⟪b, x⟫ • b := by
  ext i
  change (outer b *ᵥ x.ofLp) i = ⟪b, x⟫ * b i
  simp [Matrix.mulVec, dotProduct, outer, inner_eq_dotProduct,
    Finset.mul_sum, mul_comm, mul_assoc]

theorem trace_outer (b : V n) : (outer b).trace = ‖b‖ ^ 2 := by
  rw [outer_eq_vecMulVec, Matrix.trace_vecMulVec, ← inner_eq_dotProduct,
    real_inner_self_eq_norm_sq]

theorem mem_ellipsoid (a : V n) (A : MatR n) (x : V n) :
    x ∈ ellipsoid a A ↔
      ∃ y : V n, ‖y‖ ≤ 1 ∧ a + Matrix.toEuclideanCLM (𝕜 := ℝ) A y = x := by
  simp [ellipsoid]

theorem center_mem_ellipsoid (a : V n) (A : MatR n) : a ∈ ellipsoid a A := by
  exact ⟨0, by simp, by simp⟩

@[simp] theorem ellipsoid_zero_one : ellipsoid (0 : V n) (1 : MatR n) = unitBall n := by
  simp [ellipsoid]

theorem isCompact_ellipsoid (a : V n) (A : MatR n) : IsCompact (ellipsoid a A) := by
  apply (isCompact_closedBall (0 : V n) 1).image
  exact continuous_const.add (Matrix.toEuclideanCLM (𝕜 := ℝ) A).continuous

theorem measurableSet_ellipsoid (a : V n) (A : MatR n) : MeasurableSet (ellipsoid a A) :=
  (isCompact_ellipsoid a A).measurableSet

theorem volume_ellipsoid_lt_top (a : V n) (A : MatR n) : volume (ellipsoid a A) < ∞ :=
  (isCompact_ellipsoid a A).measure_lt_top

theorem IsFeasible.center_mem {K : Set (V n)} {a : V n} {A : MatR n}
    (h : IsFeasible K a A) : a ∈ K :=
  h.2 (center_mem_ellipsoid a A)

theorem volume_le_maxEllipsoidVolume {K : Set (V n)} {a : V n} {A : MatR n}
    (h : IsFeasible K a A) : volume (ellipsoid a A) ≤ maxEllipsoidVolume K :=
  le_iSup_of_le a (le_iSup_of_le A (le_iSup_of_le h le_rfl))

theorem maxEllipsoidVolume_le_volume (K : Set (V n)) :
    maxEllipsoidVolume K ≤ volume K := by
  refine iSup_le fun a => iSup_le fun A => iSup_le fun h => ?_
  exact measure_mono h.2

theorem maxEllipsoidVolume_mono {K L : Set (V n)} (hKL : K ⊆ L) :
    maxEllipsoidVolume K ≤ maxEllipsoidVolume L := by
  refine iSup_le fun a => iSup_le fun A => iSup_le fun h => ?_
  exact volume_le_maxEllipsoidVolume ⟨h.1, h.2.trans hKL⟩

theorem IsConvexBody.maxEllipsoidVolume_lt_top {K : Set (V n)} (hK : IsConvexBody K) :
    maxEllipsoidVolume K < ∞ :=
  (maxEllipsoidVolume_le_volume K).trans_lt hK.1.measure_lt_top

theorem IsMaxDet.posDef {K : Set (V n)} {c : V n} {S : MatR n}
    (h : IsMaxDet K c S) : S.PosDef :=
  h.feasible.1

theorem IsMaxDet.subset {K : Set (V n)} {c : V n} {S : MatR n}
    (h : IsMaxDet K c S) : ellipsoid c S ⊆ K :=
  h.feasible.2

theorem IsJohnNormalized.unitBall_subset {K : Set (V n)} (hK : IsJohnNormalized K) :
    unitBall n ⊆ K := by
  simpa using hK.feasible.2

end Khachiyan
