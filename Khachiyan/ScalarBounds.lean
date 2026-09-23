import Khachiyan.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The joint scalar maximum

This module formalizes S01 of `proof.md` and `formalization_plan.md`.
The log-sum-exp convexity argument uses the convexity of the exponential after
normalizing each pair of summands. All variables and constants are real.
-/

noncomputable section

open Set

namespace Khachiyan.Scalar

def f1 (a : ℝ) : ℝ := Real.sqrt (a + a ^ 2 / 4)
def f2 (a : ℝ) : ℝ := Real.sqrt (f1 a + a ^ 2 / 16)
def R1 (a : ℝ) : ℝ := a * Real.exp (2 * (1 - f1 a))
def R2 (a : ℝ) : ℝ := a * Real.exp (4 * (1 - f2 a))
def F1 (x : ℝ) : ℝ := x + 2 * (1 - f1 (Real.exp x))
def F2 (x : ℝ) : ℝ := x + 4 * (1 - f2 (Real.exp x))
def crossing : ℝ := -Real.log 2
def logConstant : ℝ := 1 / 2 - Real.log 2
def weightedEnvelope (x : ℝ) : ℝ := F1 x / 8 + 7 * F2 x / 8

def logAddExp (s t : ℝ) : ℝ := Real.log (Real.exp s + Real.exp t)

theorem logAddExp_mono {s t u v : ℝ} (hs : s ≤ u) (ht : t ≤ v) :
    logAddExp s t ≤ logAddExp u v := by
  apply Real.log_le_log (by positivity)
  exact add_le_add (Real.exp_le_exp.mpr hs) (Real.exp_le_exp.mpr ht)

theorem exp_normalized_sum (s t : ℝ) :
    Real.exp (s - logAddExp s t) + Real.exp (t - logAddExp s t) = 1 := by
  rw [Real.exp_sub, Real.exp_sub, ← add_div, logAddExp,
    Real.exp_log (by positivity), div_self (by positivity)]

/-- Two-term log-sum-exp satisfies the convexity inequality in both arguments. -/
theorem logAddExp_weighted_le (s1 t1 s2 t2 a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    logAddExp (a * s1 + b * s2) (a * t1 + b * t2) ≤
      a * logAddExp s1 t1 + b * logAddExp s2 t2 := by
  let L := a * logAddExp s1 t1 + b * logAddExp s2 t2
  have hs := convexOn_exp.2 (mem_univ (s1 - logAddExp s1 t1))
    (mem_univ (s2 - logAddExp s2 t2)) ha hb hab
  have ht := convexOn_exp.2 (mem_univ (t1 - logAddExp s1 t1))
    (mem_univ (t2 - logAddExp s2 t2)) ha hb hab
  simp only [smul_eq_mul] at hs ht
  have hsum : Real.exp ((a * s1 + b * s2) - L) +
      Real.exp ((a * t1 + b * t2) - L) ≤ 1 := by
    calc
      _ = Real.exp (a * (s1 - logAddExp s1 t1) + b * (s2 - logAddExp s2 t2)) +
          Real.exp (a * (t1 - logAddExp s1 t1) + b * (t2 - logAddExp s2 t2)) := by
            congr 1 <;> congr 1 <;> dsimp [L] <;> ring
      _ ≤ (a * Real.exp (s1 - logAddExp s1 t1) + b * Real.exp (s2 - logAddExp s2 t2)) +
          (a * Real.exp (t1 - logAddExp s1 t1) + b * Real.exp (t2 - logAddExp s2 t2)) :=
        add_le_add hs ht
      _ = a * (Real.exp (s1 - logAddExp s1 t1) + Real.exp (t1 - logAddExp s1 t1)) +
          b * (Real.exp (s2 - logAddExp s2 t2) + Real.exp (t2 - logAddExp s2 t2)) := by ring
      _ = 1 := by rw [exp_normalized_sum, exp_normalized_sum]; linarith
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  rw [Real.exp_sub, Real.exp_sub, ← add_div] at hsum
  simpa [L] using (div_le_iff₀ (Real.exp_pos L)).mp hsum

theorem convexOn_logAddExp {f g : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) (hg : ConvexOn ℝ univ g) :
    ConvexOn ℝ univ (fun x => logAddExp (f x) (g x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  exact (logAddExp_mono (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)).trans
    (logAddExp_weighted_le (f x) (g x) (f y) (g y) a b ha hb hab)

theorem convexOn_exp_comp {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    ConvexOn ℝ univ (fun x => Real.exp (f x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  exact (Real.exp_le_exp.mpr (hf.2 hx hy ha hb hab)).trans
    (convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hab)

theorem f1_pos {a : ℝ} (ha : 0 < a) : 0 < f1 a := by
  unfold f1
  positivity

theorem f2_pos {a : ℝ} (ha : 0 < a) : 0 < f2 a := by
  have h := f1_pos ha
  unfold f2
  positivity

theorem f1_sq {a : ℝ} (ha : 0 < a) : (f1 a) ^ 2 = a + a ^ 2 / 4 := by
  exact Real.sq_sqrt (by positivity)

theorem f2_sq {a : ℝ} (ha : 0 < a) : (f2 a) ^ 2 = f1 a + a ^ 2 / 16 := by
  have h := f1_pos ha
  exact Real.sq_sqrt (by positivity)

theorem exp_double_sub_log (x c : ℝ) (hc : 0 < c) :
    Real.exp (2 * x - Real.log c) = Real.exp x ^ 2 / c := by
  rw [Real.exp_sub, Real.exp_log hc, two_mul, Real.exp_add, pow_two]

theorem log_f1_exp (x : ℝ) :
    Real.log (f1 (Real.exp x)) = logAddExp x (2 * x - Real.log 4) / 2 := by
  rw [f1, Real.log_sqrt (by positivity), logAddExp,
    exp_double_sub_log x 4 (by norm_num)]

theorem log_f2_exp (x : ℝ) :
    Real.log (f2 (Real.exp x)) =
      logAddExp (Real.log (f1 (Real.exp x))) (2 * x - Real.log 16) / 2 := by
  have h := f1_pos (Real.exp_pos x)
  rw [f2, Real.log_sqrt (by positivity), logAddExp, Real.exp_log h,
    exp_double_sub_log x 16 (by norm_num)]

theorem convexOn_double_sub (c : ℝ) : ConvexOn ℝ univ (fun x : ℝ => 2 * x - c) := by
  simpa only [smul_eq_mul, id_eq, sub_eq_add_neg, Pi.add_def] using
    ((convexOn_id (𝕜 := ℝ) (s := (univ : Set ℝ)) convex_univ).smul
      (by norm_num : 0 ≤ (2 : ℝ))).add_const (-c)

theorem convexOn_log_f1_exp : ConvexOn ℝ univ (fun x => Real.log (f1 (Real.exp x))) := by
  have h := (convexOn_logAddExp (convexOn_id (𝕜 := ℝ) convex_univ)
    (convexOn_double_sub (Real.log 4))).smul (by norm_num : 0 ≤ (1 / 2 : ℝ))
  convert h using 1
  ext x
  rw [log_f1_exp]
  simp only [smul_eq_mul, id_eq]
  ring

theorem convexOn_log_f2_exp : ConvexOn ℝ univ (fun x => Real.log (f2 (Real.exp x))) := by
  have h := (convexOn_logAddExp convexOn_log_f1_exp
    (convexOn_double_sub (Real.log 16))).smul (by norm_num : 0 ≤ (1 / 2 : ℝ))
  convert h using 1
  ext x
  rw [log_f2_exp]
  simp only [smul_eq_mul]
  ring

theorem convexOn_f1_exp : ConvexOn ℝ univ (fun x => f1 (Real.exp x)) := by
  convert convexOn_exp_comp convexOn_log_f1_exp using 1
  ext x
  exact (Real.exp_log (f1_pos (Real.exp_pos x))).symm

theorem convexOn_f2_exp : ConvexOn ℝ univ (fun x => f2 (Real.exp x)) := by
  convert convexOn_exp_comp convexOn_log_f2_exp using 1
  ext x
  exact (Real.exp_log (f2_pos (Real.exp_pos x))).symm

theorem concaveOn_F1 : ConcaveOn ℝ univ F1 := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := convexOn_f1_exp.2 hx hy ha hb hab
  simp only [F1, smul_eq_mul] at h ⊢
  nlinarith

theorem concaveOn_F2 : ConcaveOn ℝ univ F2 := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := convexOn_f2_exp.2 hx hy ha hb hab
  simp only [F2, smul_eq_mul] at h ⊢
  nlinarith

@[simp] theorem f1_half : f1 (1 / 2) = 3 / 4 := by
  unfold f1
  rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
  norm_num

@[simp] theorem f2_half : f2 (1 / 2) = 7 / 8 := by
  rw [f2, f1_half, Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
  norm_num

@[simp] theorem exp_crossing : Real.exp crossing = 1 / 2 := by
  rw [crossing, Real.exp_neg, Real.exp_log (by norm_num : 0 < (2 : ℝ))]
  norm_num

@[simp] theorem F1_crossing : F1 crossing = logConstant := by
  rw [F1, exp_crossing, f1_half]
  unfold crossing logConstant
  ring

@[simp] theorem F2_crossing : F2 crossing = logConstant := by
  rw [F2, exp_crossing, f2_half]
  unfold crossing logConstant
  ring

theorem hasDerivAt_f1 {a : ℝ} (ha : 0 < a) :
    HasDerivAt f1 ((1 + a / 2) / (2 * f1 a)) a := by
  have h := ((hasDerivAt_id a).add (((hasDerivAt_id a).pow 2).div_const 4)).sqrt
    (by positivity : a + a ^ 2 / 4 ≠ 0)
  convert h using 1
  · rfl
  · dsimp [f1]
    ring

theorem hasDerivAt_f2 {a : ℝ} (ha : 0 < a) :
    HasDerivAt f2 (((1 + a / 2) / (2 * f1 a) + a / 8) / (2 * f2 a)) a := by
  have hp := f1_pos ha
  have h := ((hasDerivAt_f1 ha).add (((hasDerivAt_id a).pow 2).div_const 16)).sqrt
    (by positivity : f1 a + a ^ 2 / 16 ≠ 0)
  convert h using 1
  · rfl
  · dsimp [f2]
    ring

theorem hasDerivAt_f1_half : HasDerivAt f1 (5 / 6) (1 / 2) := by
  convert hasDerivAt_f1 (by norm_num : 0 < (1 / 2 : ℝ)) using 1
  norm_num

theorem hasDerivAt_f2_half : HasDerivAt f2 (43 / 84) (1 / 2) := by
  convert hasDerivAt_f2 (by norm_num : 0 < (1 / 2 : ℝ)) using 1
  norm_num

theorem hasDerivAt_F1_crossing : HasDerivAt F1 (1 / 6) crossing := by
  have hf : HasDerivAt f1 (5 / 6) (Real.exp crossing) := by
    rw [exp_crossing]
    exact hasDerivAt_f1_half
  have h := (hasDerivAt_id crossing).add
    (((hasDerivAt_const crossing (1 : ℝ)).sub
      (hf.comp crossing (Real.hasDerivAt_exp crossing))).const_mul 2)
  convert h using 1
  · rfl
  · rw [exp_crossing]
    norm_num

theorem hasDerivAt_F2_crossing : HasDerivAt F2 (-1 / 42) crossing := by
  have hf : HasDerivAt f2 (43 / 84) (Real.exp crossing) := by
    rw [exp_crossing]
    exact hasDerivAt_f2_half
  have h := (hasDerivAt_id crossing).add
    (((hasDerivAt_const crossing (1 : ℝ)).sub
      (hf.comp crossing (Real.hasDerivAt_exp crossing))).const_mul 4)
  convert h using 1
  · rfl
  · rw [exp_crossing]
    norm_num

/-- A differentiable concave function on the real line lies below its tangent. -/
theorem concave_le_tangent {f : ℝ → ℝ} {d x0 : ℝ}
    (hc : ConcaveOn ℝ univ f) (hd : HasDerivAt f d x0) (x : ℝ) :
    f x ≤ f x0 + d * (x - x0) := by
  rcases lt_trichotomy x x0 with h | rfl | h
  · have hs := hc.le_slope_of_hasDerivAt (mem_univ x) (mem_univ x0) h hd
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith
  · simp
  · have hs := hc.slope_le_of_hasDerivAt (mem_univ x0) (mem_univ x) h hd
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    linarith

/-- The first global tangent inequality in S01.1. -/
theorem F1_le_tangent (x : ℝ) : F1 x ≤ logConstant + (x - crossing) / 6 := by
  have h := concave_le_tangent concaveOn_F1 hasDerivAt_F1_crossing x
  rw [F1_crossing] at h
  linarith

/-- The second global tangent inequality in S01.1. -/
theorem F2_le_tangent (x : ℝ) : F2 x ≤ logConstant - (x - crossing) / 42 := by
  have h := concave_le_tangent concaveOn_F2 hasDerivAt_F2_crossing x
  rw [F2_crossing] at h
  linarith

theorem joint_log_bound (x : ℝ) : min (F1 x) (F2 x) ≤ logConstant := by
  rcases le_total x crossing with h | h
  · have ht := F1_le_tangent x
    have hm := min_le_left (F1 x) (F2 x)
    linarith
  · have ht := F2_le_tangent x
    have hm := min_le_right (F1 x) (F2 x)
    linarith

theorem joint_log_eq_iff (x : ℝ) :
    min (F1 x) (F2 x) = logConstant ↔ x = crossing := by
  constructor
  · intro h
    have h1 := min_le_left (F1 x) (F2 x)
    have h2 := min_le_right (F1 x) (F2 x)
    rw [h] at h1 h2
    have ht1 := F1_le_tangent x
    have ht2 := F2_le_tangent x
    linarith
  · rintro rfl
    simp

theorem concaveOn_weightedEnvelope : ConcaveOn ℝ univ weightedEnvelope := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h1 := concaveOn_F1.2 hx hy ha hb hab
  have h2 := concaveOn_F2.2 hx hy ha hb hab
  simp only [weightedEnvelope, smul_eq_mul] at h1 h2 ⊢
  linarith

@[simp] theorem weightedEnvelope_crossing : weightedEnvelope crossing = logConstant := by
  rw [weightedEnvelope, F1_crossing, F2_crossing]
  ring

theorem hasDerivAt_weightedEnvelope_crossing : HasDerivAt weightedEnvelope 0 crossing := by
  have h := (hasDerivAt_F1_crossing.div_const 8).add
    ((hasDerivAt_F2_crossing.const_mul 7).div_const 8)
  convert h using 1
  · rfl
  · norm_num

theorem weightedEnvelope_le (x : ℝ) : weightedEnvelope x ≤ logConstant := by
  have h := concave_le_tangent concaveOn_weightedEnvelope
    hasDerivAt_weightedEnvelope_crossing x
  simpa using h

theorem min_le_weightedEnvelope (x : ℝ) : min (F1 x) (F2 x) ≤ weightedEnvelope x := by
  have h1 := min_le_left (F1 x) (F2 x)
  have h2 := min_le_right (F1 x) (F2 x)
  unfold weightedEnvelope
  linarith

theorem exp_logConstant : Real.exp logConstant = rStar := by
  rw [logConstant, Real.exp_sub, Real.exp_log (by norm_num : 0 < (2 : ℝ))]
  rfl

theorem rStar_eq_sqrt_exp_one : rStar = Real.sqrt (Real.exp 1) / 2 := by
  rw [rStar, Real.exp_half]

theorem exp_F1_log {a : ℝ} (ha : 0 < a) : Real.exp (F1 (Real.log a)) = R1 a := by
  rw [F1, Real.exp_log ha, Real.exp_add, Real.exp_log ha]
  rfl

theorem exp_F2_log {a : ℝ} (ha : 0 < a) : Real.exp (F2 (Real.log a)) = R2 a := by
  rw [F2, Real.exp_log ha, Real.exp_add, Real.exp_log ha]
  rfl

theorem log_R1 {a : ℝ} (ha : 0 < a) : Real.log (R1 a) = F1 (Real.log a) := by
  rw [← exp_F1_log ha, Real.log_exp]

theorem log_R2 {a : ℝ} (ha : 0 < a) : Real.log (R2 a) = F2 (Real.log a) := by
  rw [← exp_F2_log ha, Real.log_exp]

theorem log_R1_exp (x : ℝ) : Real.log (R1 (Real.exp x)) = F1 x := by
  rw [log_R1 (Real.exp_pos x), Real.log_exp]

theorem log_R2_exp (x : ℝ) : Real.log (R2 (Real.exp x)) = F2 x := by
  rw [log_R2 (Real.exp_pos x), Real.log_exp]

theorem exp_min (s t : ℝ) :
    Real.exp (min s t) = min (Real.exp s) (Real.exp t) := by
  rcases le_total s t with h | h
  · rw [min_eq_left h, min_eq_left (Real.exp_le_exp.mpr h)]
  · rw [min_eq_right h, min_eq_right (Real.exp_le_exp.mpr h)]

theorem log_eq_crossing_iff {a : ℝ} (ha : 0 < a) :
    Real.log a = crossing ↔ a = 1 / 2 := by
  constructor
  · intro h
    have he := congrArg Real.exp h
    rwa [Real.exp_log ha, exp_crossing] at he
  · intro h
    apply Real.exp_injective
    rw [Real.exp_log ha, exp_crossing, h]

@[simp] theorem R1_half : R1 (1 / 2) = rStar := by
  unfold R1
  rw [f1_half]
  norm_num [rStar]
  ring

@[simp] theorem R2_half : R2 (1 / 2) = rStar := by
  unfold R2
  rw [f2_half]
  norm_num [rStar]
  ring

/-- S01: the joint envelope is bounded by the exact dimension-independent constant. -/
theorem joint_bound {a : ℝ} (ha : 0 < a) : min (R1 a) (R2 a) ≤ rStar := by
  have h := Real.exp_le_exp.mpr (joint_log_bound (Real.log a))
  rwa [exp_min, exp_F1_log ha, exp_F2_log ha, exp_logConstant] at h

/-- The joint envelope reaches its bound only at the specified smallest semiaxis. -/
theorem joint_eq_iff {a : ℝ} (ha : 0 < a) :
    min (R1 a) (R2 a) = rStar ↔ a = 1 / 2 := by
  rw [← exp_F1_log ha, ← exp_F2_log ha, ← exp_min, ← exp_logConstant,
    Real.exp_eq_exp, joint_log_eq_iff, log_eq_crossing_iff ha]

theorem joint_lt_of_ne_half {a : ℝ} (ha : 0 < a) (hne : a ≠ 1 / 2) :
    min (R1 a) (R2 a) < rStar := by
  rcases lt_or_eq_of_le (joint_bound ha) with h | h
  · exact h
  · exact (hne ((joint_eq_iff ha).mp h)).elim

/-- The maximum over all positive real inputs exists and equals `rStar`. -/
theorem joint_isGreatest :
    IsGreatest ((fun a : ℝ => min (R1 a) (R2 a)) '' Ioi 0) rStar := by
  refine ⟨⟨1 / 2, by norm_num, ?_⟩, ?_⟩
  · change min (R1 (1 / 2)) (R2 (1 / 2)) = rStar
    rw [R1_half, R2_half, min_self]
  · rintro y ⟨a, ha, rfl⟩
    exact joint_bound ha

/-- The two scalar curves themselves intersect at exactly one positive input. -/
theorem R1_eq_R2_iff {a : ℝ} (ha : 0 < a) : R1 a = R2 a ↔ a = 1 / 2 := by
  constructor
  · intro h
    change a * Real.exp (2 * (1 - f1 a)) = a * Real.exp (4 * (1 - f2 a)) at h
    have he := Real.exp_injective (mul_left_cancel₀ ha.ne' h)
    have hl : 2 * f2 a = f1 a + 1 := by linarith
    have hs := congrArg (fun z : ℝ => z ^ 2) hl
    have hs1 := f1_sq ha
    have hs2 := f2_sq ha
    have hl1 : 2 * f1 a = a + 1 := by nlinarith
    have hs' := congrArg (fun z : ℝ => z ^ 2) hl1
    nlinarith
  · rintro rfl
    rw [R1_half, R2_half]

end Khachiyan.Scalar
