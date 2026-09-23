import Khachiyan.TraceDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Quantitative rank-one trace estimate

This module formalizes M04 of `proof.md` using the trace derivative from M03.
The matrices need not commute. All vectors and unit-vector conditions use the
Euclidean space specified in B01. The independent resolvent proof A01 is separate.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set

namespace Khachiyan.RankOne

variable {n : ℕ} {A M : MatR n}

def path (M : MatR n) (b : V n) (s : ℝ) : MatR n := M + s • outer b

theorem posSemidef_of_inner_nonneg (hA : A.IsHermitian)
    (h : ∀ x : V n, 0 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫) : A.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hA, ?_⟩
  intro x
  simpa only [inner_matrix_action, WithLp.ofLp_toLp, star_trivial] using h (WithLp.toLp 2 x)

theorem outer_le_one (u : V n) (hu : ‖u‖ = 1) : outer u ≤ (1 : MatR n) := by
  apply Matrix.le_iff.mpr
  apply posSemidef_of_inner_nonneg
    ((Matrix.PosSemidef.one : (1 : MatR n).PosSemidef).isHermitian.sub (outer_posSemidef u).isHermitian)
  intro x
  have h := real_inner_mul_inner_self_le x u
  simp only [real_inner_self_eq_norm_sq, hu, one_pow, mul_one] at h
  simp only [map_sub, map_one, _root_.sub_apply, one_apply_eq_self,
    outer_action, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [real_inner_comm u x] at h ⊢
  nlinarith

theorem outer_image (A : MatR n) (u : V n) :
    outer (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) = A * outer u * star A := by
  simp only [outer_eq_vecMulVec, Matrix.ofLp_toEuclideanCLM, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.vecMul_transpose]

theorem outer_image_le_sq (hA : A.IsHermitian) (u : V n) (hu : ‖u‖ = 1) :
    outer (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) ≤ A ^ 2 := by
  rw [outer_image, Matrix.le_iff]
  have h := (Matrix.le_iff.mp (outer_le_one u hu)).mul_mul_conjTranspose_same A
  simpa only [mul_sub, sub_mul, mul_one, ← Matrix.star_eq_conjTranspose,
    show star A = A from hA, pow_two] using h

theorem trace_mul_outer (T : MatR n) (b : V n) :
    (T * outer b).trace = ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) T b⟫ := by
  rw [outer_eq_vecMulVec, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, inner_matrix_action]
  exact dotProduct_comm _ _

theorem inner_sandwich (hA : A.IsHermitian) (T : MatR n) (u : V n) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A u,
      Matrix.toEuclideanCLM (𝕜 := ℝ) T (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)⟫ =
    ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (A * T * A) u⟫ := by
  have h := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) u
    (Matrix.toEuclideanCLM (𝕜 := ℝ) T (Matrix.toEuclideanCLM (𝕜 := ℝ) A u))
  simp only [map_mul, mul_apply_eq_comp]
  convert h using 1 <;> rfl

theorem path_posDef (hM : M.PosDef) (b : V n) {s : ℝ} (hs : 0 ≤ s) :
    (path M b s).PosDef :=
  hM.add_posSemidef ((outer_posSemidef b).smul hs)

theorem scalar_sandwich {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (p : ℝ) :
    x * (c * x ^ 2) ^ (p - 1) * x = c ^ (p - 1) * x ^ (2 * p) := by
  rw [Real.mul_rpow hc.le (sq_nonneg x)]
  calc
    _ = c ^ (p - 1) * ((x ^ 2) ^ (p - 1) * x ^ 2) := by ring
    _ = c ^ (p - 1) * (x ^ 2) ^ p := by
      rw [← Real.rpow_add_one (sq_pos_of_pos hx).ne' (p - 1), sub_add_cancel]
    _ = _ := by rw [Real.rpow_mul hx.le (2 : ℝ) p, Real.rpow_two]

theorem sandwich_scaled_sq_rpow (hA : A.PosDef) {c : ℝ} (hc : 0 < c) (p : ℝ) :
    A * CFC.rpow (c • A ^ 2) (p - 1) * A = c ^ (p - 1) • CFC.rpow A (2 * p) := by
  have hspec : ∀ x ∈ spectrum ℝ A, 0 < x := by
    intro x hx
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hA.eigenvalues_pos i
  have hpoly : cfc (fun x : ℝ => c * x ^ 2) A = c • A ^ 2 := by
    rw [cfc_const_mul _ _ _ (by fun_prop), cfc_pow_id (R := ℝ) A 2 hA.isHermitian.isSelfAdjoint]
  let f : ℝ → ℝ := fun x => (c * x ^ 2) ^ (p - 1)
  have hpow : CFC.rpow (c • A ^ 2) (p - 1) = cfc f A := by
    rw [← hpoly]
    exact CFC.cfc_rpow (fun x hx => mul_pos hc (sq_pos_of_pos (hspec x hx)))
      (by fun_prop) hA.isHermitian.isSelfAdjoint
  rw [hpow]
  calc
    _ = cfc (fun x : ℝ => x * f x * x) A := by
      symm
      rw [cfc_mul (fun x : ℝ => x * f x) (fun x : ℝ => x) A
        ((Matrix.finite_real_spectrum (A := A)).continuousOn _) (by fun_prop),
        cfc_mul (fun x : ℝ => x) f A (by fun_prop)
          ((Matrix.finite_real_spectrum (A := A)).continuousOn f),
        cfc_id' ℝ A hA.isHermitian.isSelfAdjoint]
    _ = cfc (fun x : ℝ => c ^ (p - 1) * x ^ (2 * p)) A :=
      cfc_congr (fun x hx => scalar_sandwich (hspec x hx) hc p)
    _ = _ := by
      rw [cfc_const_mul _ _ _ ((Matrix.finite_real_spectrum (A := A)).continuousOn _),
        ← Spectral.rpow_eq_cfc hA (2 * p)]

theorem scalar_scale_min {a k : ℝ} (ha : 0 < a) (hk : 0 < k) (p : ℝ) :
    (k / a ^ 2) ^ (p - 1) * a ^ (2 * p) = a ^ 2 * k ^ (p - 1) := by
  have he : (a ^ 2) ^ (p - 1) * a ^ 2 = a ^ (2 * p) := by
    rw [← Real.rpow_add_one (sq_pos_of_pos ha).ne' (p - 1), sub_add_cancel,
      Real.rpow_mul ha.le (2 : ℝ) p, Real.rpow_two]
  rw [Real.div_rpow hk.le (sq_nonneg a), ← he]
  field_simp [(Real.rpow_pos_of_pos (sq_pos_of_pos ha) (p - 1)).ne']

theorem scaled_sq_posDef (hA : A.PosDef) {c : ℝ} (hc : 0 < c) : (c • A ^ 2).PosDef := by
  have he : CFC.rpow A (2 : ℝ) = A ^ 2 := CFC.rpow_natCast A 2 hA.posSemidef.nonneg
  have h := Spectral.rpow_posDef hA (2 : ℝ)
  rw [he] at h
  exact h.smul hc

/-- Functional calculus acts on any eigenvector, including inside a repeated eigenspace. -/
theorem cfc_action_of_eigenvector (hA : A.IsHermitian) (u : V n) (k : ℝ)
    (hu : Matrix.toEuclideanCLM (𝕜 := ℝ) A u = k • u) (f : ℝ → ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (cfc f A) u = f k • u := by
  let g : ℝ → ℝ := fun x => (f x - f k) / (x - k)
  have hmat : cfc f A - f k • (1 : MatR n) = cfc g A * (A - k • (1 : MatR n)) := by
    calc
      _ = cfc (fun x : ℝ => f x - f k) A := by
        rw [cfc_sub f (fun _ : ℝ => f k) A
          ((Matrix.finite_real_spectrum (A := A)).continuousOn f) (by fun_prop),
          cfc_const (f k) A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
      _ = cfc (fun x : ℝ => g x * (x - k)) A := by
        apply cfc_congr
        intro x hx
        by_cases hk : x = k
        · simp [hk, g]
        · exact (div_mul_cancel₀ (f x - f k) (sub_ne_zero.mpr hk)).symm
      _ = _ := by
        rw [cfc_mul g (fun x : ℝ => x - k) A
          ((Matrix.finite_real_spectrum (A := A)).continuousOn g) (by fun_prop),
          cfc_sub (fun x : ℝ => x) (fun _ : ℝ => k) A (by fun_prop) (by fun_prop),
          cfc_id' ℝ A hA.isSelfAdjoint, cfc_const k A hA.isSelfAdjoint,
          Algebra.algebraMap_eq_smul_one]
  have h := congrArg (fun T : MatR n => Matrix.toEuclideanCLM (𝕜 := ℝ) T u) hmat
  simp only [map_sub, map_smul, map_one, map_mul, _root_.sub_apply, _root_.smul_apply,
    one_apply_eq_self, mul_apply_eq_comp, hu, sub_self, map_zero, sub_eq_zero] at h
  exact h

theorem rpow_action_of_eigenvector (hA : A.PosDef) (u : V n) (k : ℝ)
    (hu : Matrix.toEuclideanCLM (𝕜 := ℝ) A u = k • u) (q : ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.rpow A q) u = k ^ q • u := by
  rw [Spectral.rpow_eq_cfc hA q]
  exact cfc_action_of_eigenvector hA.isHermitian u k hu (fun x : ℝ => x ^ q)

theorem quadratic_rpow_eigen (hA : A.PosDef) (u : V n) (hu : ‖u‖ = 1) (k a q : ℝ)
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) A u = k • u) :
    ⟪a • u, Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.rpow A q) (a • u)⟫ = a ^ 2 * k ^ q := by
  have hpow := rpow_action_of_eigenvector hA u k heig q
  simp only [map_smul, hpow, real_inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, hu, one_pow]
  ring

theorem hasDerivAt_scalar_curve (m a p s : ℝ) (hs : 0 < m + s * a ^ 2) :
    HasDerivAt (fun r : ℝ => (m + r * a ^ 2) ^ p)
      (p * a ^ 2 * (m + s * a ^ 2) ^ (p - 1)) s := by
  have h := ((hasDerivAt_const s m).add ((hasDerivAt_id s).mul_const (a ^ 2))).rpow_const
    (p := p) (Or.inl hs.ne')
  convert h using 1
  · rfl
  · simp only [Pi.add_apply, id_eq, zero_add, one_mul]
    ring

theorem increment_le_of_derivative_le {f g f' g' : ℝ → ℝ}
    (hf : ∀ s, 0 ≤ s → HasDerivAt f (f' s) s)
    (hg : ∀ s, 0 ≤ s → HasDerivAt g (g' s) s)
    (hle : ∀ s, 0 ≤ s → f' s ≤ g' s) {t : ℝ} (ht : 0 ≤ t) :
    f t - f 0 ≤ g t - g 0 := by
  have hd := fun s hs => (hg s hs).sub (hf s hs)
  have hm : MonotoneOn (fun s => g s - f s) (Ici (0 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
      (f' := fun s => g' s - f' s)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt
    · exact fun s hs => sub_nonneg.mpr (hle s (interior_subset hs))
  have h := hm (by simp) (show t ∈ Ici (0 : ℝ) from ht) ht
  dsimp at h
  linarith

theorem increment_eq_of_derivative_eq {f g d : ℝ → ℝ}
    (hf : ∀ s, 0 ≤ s → HasDerivAt f (d s) s)
    (hg : ∀ s, 0 ≤ s → HasDerivAt g (d s) s) {t : ℝ} (ht : 0 ≤ t) :
    f t - f 0 = g t - g 0 := by
  apply le_antisymm
  · exact increment_le_of_derivative_le hf hg (fun _ _ => le_rfl) ht
  · exact increment_le_of_derivative_le hg hf (fun _ _ => le_rfl) ht

section PositiveDimension

variable [NeZero n]

theorem hasDerivAt_trace_path (M : MatR n) (b : V n) (p s : ℝ)
    (hp : p ∈ Ioo (0 : ℝ) 1) (hP : (path M b s).PosDef) :
    HasDerivAt (fun r : ℝ => (CFC.rpow (path M b r) p).trace)
      (p * ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.rpow (path M b s) (p - 1)) b⟫) s := by
  have h0 := TraceDerivative.hasDerivAt_trace_rpow hP (outer_posSemidef b).isHermitian hp
  have h0' : HasDerivAt (fun r : ℝ => (CFC.rpow (path M b s + r • outer b) p).trace)
      (p * (CFC.rpow (path M b s) (p - 1) * outer b).trace) (s - s) := by
    simpa only [sub_self] using h0
  have h := h0'.comp (h := fun r : ℝ => r - s) s ((hasDerivAt_id s).sub_const s)
  have heq (r : ℝ) : path M b s + (r - s) • outer b = path M b r := by
    unfold path
    rw [sub_smul]
    abel
  simpa only [Function.comp_def, heq, mul_one, trace_mul_outer] using h

theorem path_le_scaled_sq (hA : A.PosDef) (u : V n) (hu : ‖u‖ = 1) {m s : ℝ}
    (hMA : M ≤ (m / (Spectral.minEigenvalue hA.isHermitian) ^ 2) • A ^ 2) (hs : 0 ≤ s) :
    path M (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) s ≤
      ((m + s * (Spectral.minEigenvalue hA.isHermitian) ^ 2) /
        (Spectral.minEigenvalue hA.isHermitian) ^ 2) • A ^ 2 := by
  have ho := outer_image_le_sq hA.isHermitian u hu
  have hso : s • outer (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) ≤ s • A ^ 2 := by
    apply Matrix.le_iff.mpr
    simpa only [smul_sub] using (Matrix.le_iff.mp ho).smul hs
  have h := add_le_add hMA hso
  rw [← add_smul] at h
  have he : m / (Spectral.minEigenvalue hA.isHermitian) ^ 2 + s =
      (m + s * (Spectral.minEigenvalue hA.isHermitian) ^ 2) /
        (Spectral.minEigenvalue hA.isHermitian) ^ 2 := by
    field_simp [(Spectral.minEigenvalue_pos hA).ne']
  rwa [he] at h

theorem quadratic_path_lower (hA : A.PosDef) (hM : M.PosDef) (u : V n) (hu : ‖u‖ = 1)
    {m s p : ℝ} (hm : 0 < m)
    (hMA : M ≤ (m / (Spectral.minEigenvalue hA.isHermitian) ^ 2) • A ^ 2)
    (hp : p ∈ Ioo (0 : ℝ) 1) (hs : 0 ≤ s) :
    (Spectral.minEigenvalue hA.isHermitian) ^ 2 *
        (m + s * (Spectral.minEigenvalue hA.isHermitian) ^ 2) ^ (p - 1) ≤
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A u,
        Matrix.toEuclideanCLM (𝕜 := ℝ)
          (CFC.rpow (path M (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) s) (p - 1))
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)⟫ := by
  let a := Spectral.minEigenvalue hA.isHermitian
  let k := m + s * a ^ 2
  let c := k / a ^ 2
  let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
  have ha : 0 < a := Spectral.minEigenvalue_pos hA
  have hk : 0 < k := add_pos_of_pos_of_nonneg hm (mul_nonneg hs (sq_nonneg a))
  have hc : 0 < c := div_pos hk (sq_pos_of_pos ha)
  have hbound : path M b s ≤ c • A ^ 2 := path_le_scaled_sq hA u hu hMA hs
  have hneg := MatrixPowers.rpow_sub_one_antitone hp (path_posDef hM b hs) hbound
  have hq := Spectral.quadratic_mono hneg b
  have hspec := Spectral.minEigenvalue_two_mul_rpow_le_quadratic hA hp.1 u hu
  have hlow : a ^ 2 * k ^ (p - 1) ≤
      ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.rpow (c • A ^ 2) (p - 1)) b⟫ := by
    calc
      _ = c ^ (p - 1) * a ^ (2 * p) := (scalar_scale_min ha hk p).symm
      _ ≤ c ^ (p - 1) * ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.rpow A (2 * p)) u⟫ :=
        mul_le_mul_of_nonneg_left hspec (Real.rpow_pos_of_pos hc (p - 1)).le
      _ = _ := by
        dsimp only [b]
        rw [inner_sandwich hA.isHermitian, sandwich_scaled_sq_rpow hA hc p,
          map_smul, _root_.smul_apply, inner_smul_right]
  exact hlow.trans hq

/-- M04.1 for general positive definite matrices and every unit displacement direction. -/
theorem trace_increment_lower_bound (hA : A.PosDef) (hM : M.PosDef)
    (u : V n) (hu : ‖u‖ = 1) {m p t : ℝ} (hm : 0 < m)
    (hMA : M ≤ (m / (Spectral.minEigenvalue hA.isHermitian) ^ 2) • A ^ 2)
    (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    (m + t * (Spectral.minEigenvalue hA.isHermitian) ^ 2) ^ p - m ^ p ≤
      (CFC.rpow (M + t • outer (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)) p).trace -
        (CFC.rpow M p).trace := by
  let a := Spectral.minEigenvalue hA.isHermitian
  let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
  let f : ℝ → ℝ := fun s => (m + s * a ^ 2) ^ p
  let g : ℝ → ℝ := fun s => (CFC.rpow (path M b s) p).trace
  let df : ℝ → ℝ := fun s => p * a ^ 2 * (m + s * a ^ 2) ^ (p - 1)
  let dg : ℝ → ℝ := fun s =>
    p * ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.rpow (path M b s) (p - 1)) b⟫
  have hf : ∀ s, 0 ≤ s → HasDerivAt f (df s) s := by
    intro s hs
    exact hasDerivAt_scalar_curve m a p s (add_pos_of_pos_of_nonneg hm (mul_nonneg hs (sq_nonneg a)))
  have hg : ∀ s, 0 ≤ s → HasDerivAt g (dg s) s := by
    intro s hs
    exact hasDerivAt_trace_path M b p s hp (path_posDef hM b hs)
  have hle : ∀ s, 0 ≤ s → df s ≤ dg s := by
    intro s hs
    have hq : a ^ 2 * (m + s * a ^ 2) ^ (p - 1) ≤
        ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.rpow (path M b s) (p - 1)) b⟫ :=
      quadratic_path_lower hA hM u hu hm hMA hp hs
    dsimp only [df, dg]
    nlinarith [mul_le_mul_of_nonneg_left hq hp.1.le]
  have h := increment_le_of_derivative_le hf hg hle ht
  simpa only [f, g, path, zero_mul, zero_smul, add_zero, a, b] using h

/-- The base matrix in the equality example of M04. -/
def equalityBase (hA : A.PosDef) (m : ℝ) : MatR n :=
  (m / (Spectral.minEigenvalue hA.isHermitian) ^ 2) • A ^ 2

theorem equalityBase_posDef (hA : A.PosDef) {m : ℝ} (hm : 0 < m) :
    (equalityBase hA m).PosDef :=
  scaled_sq_posDef hA (div_pos hm (sq_pos_of_pos (Spectral.minEigenvalue_pos hA)))

theorem equality_path_eigen (hA : A.PosDef) (u : V n) (hu : ‖u‖ = 1)
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) A u = Spectral.minEigenvalue hA.isHermitian • u)
    (m s : ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ)
      (path (equalityBase hA m) (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) s) u =
        (m + s * (Spectral.minEigenvalue hA.isHermitian) ^ 2) • u := by
  let a := Spectral.minEigenvalue hA.isHermitian
  have ha : 0 < a := Spectral.minEigenvalue_pos hA
  have hAu : Matrix.toEuclideanCLM (𝕜 := ℝ) A u = a • u := heig
  have hA2 : Matrix.toEuclideanCLM (𝕜 := ℝ) (A ^ 2) u = a ^ 2 • u := by
    simp only [pow_two, map_mul, mul_apply_eq_comp, hAu, map_smul, smul_smul]
  have hM : Matrix.toEuclideanCLM (𝕜 := ℝ) (equalityBase hA m) u = m • u := by
    change Matrix.toEuclideanCLM (𝕜 := ℝ) ((m / a ^ 2) • A ^ 2) u = m • u
    rw [map_smul, _root_.smul_apply, hA2, smul_smul]
    congr 1
    field_simp [ha.ne']
  have hO : Matrix.toEuclideanCLM (𝕜 := ℝ) (outer (Matrix.toEuclideanCLM (𝕜 := ℝ) A u)) u =
      a ^ 2 • u := by
    rw [outer_action, hAu, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
    simp only [mul_one, smul_smul, pow_two]
  unfold path
  rw [map_add, _root_.add_apply, hM, map_smul, _root_.smul_apply, hO, smul_smul, ← add_smul]

/-- Equality in M04 for any unit eigenvector associated with the minimum eigenvalue. -/
theorem trace_increment_eq (hA : A.PosDef) (u : V n) (hu : ‖u‖ = 1)
    (heig : Matrix.toEuclideanCLM (𝕜 := ℝ) A u = Spectral.minEigenvalue hA.isHermitian • u)
    {m p t : ℝ} (hmpos : 0 < m) (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    (CFC.rpow (path (equalityBase hA m) (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) t) p).trace -
      (CFC.rpow (equalityBase hA m) p).trace =
        (m + t * (Spectral.minEigenvalue hA.isHermitian) ^ 2) ^ p - m ^ p := by
  let a := Spectral.minEigenvalue hA.isHermitian
  let b := Matrix.toEuclideanCLM (𝕜 := ℝ) A u
  let M0 := equalityBase hA m
  let f : ℝ → ℝ := fun s => (CFC.rpow (path M0 b s) p).trace
  let g : ℝ → ℝ := fun s => (m + s * a ^ 2) ^ p
  let d : ℝ → ℝ := fun s => p * a ^ 2 * (m + s * a ^ 2) ^ (p - 1)
  have hM : M0.PosDef := equalityBase_posDef hA hmpos
  have hb : b = a • u := heig
  have hf : ∀ s, 0 ≤ s → HasDerivAt f (d s) s := by
    intro s hs
    have hP := path_posDef hM b hs
    have hE : Matrix.toEuclideanCLM (𝕜 := ℝ) (path M0 b s) u = (m + s * a ^ 2) • u :=
      equality_path_eigen hA u hu heig m s
    have hq : ⟪b, Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.rpow (path M0 b s) (p - 1)) b⟫ =
        a ^ 2 * (m + s * a ^ 2) ^ (p - 1) := by
      simpa only [← hb] using quadratic_rpow_eigen hP u hu (m + s * a ^ 2) a (p - 1) hE
    have h := hasDerivAt_trace_path M0 b p s hp hP
    rw [hq] at h
    convert h using 1
    dsimp only [d]
    ring
  have hg : ∀ s, 0 ≤ s → HasDerivAt g (d s) s := by
    intro s hs
    exact hasDerivAt_scalar_curve m a p s
      (add_pos_of_pos_of_nonneg hmpos (mul_nonneg hs (sq_nonneg a)))
  have h := increment_eq_of_derivative_eq hf hg ht
  simpa only [f, g, path, zero_smul, zero_mul, add_zero, a, b, M0] using h

theorem exists_equality_direction (hA : A.PosDef) {m p t : ℝ}
    (hm : 0 < m) (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    ∃ u : V n, ‖u‖ = 1 ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) A u = Spectral.minEigenvalue hA.isHermitian • u ∧
      (CFC.rpow (path (equalityBase hA m) (Matrix.toEuclideanCLM (𝕜 := ℝ) A u) t) p).trace -
        (CFC.rpow (equalityBase hA m) p).trace =
          (m + t * (Spectral.minEigenvalue hA.isHermitian) ^ 2) ^ p - m ^ p := by
  obtain ⟨u, hu, heig⟩ := Spectral.exists_unit_min_eigenvector hA.isHermitian
  exact ⟨u, hu, heig, trace_increment_eq hA u hu heig hm hp ht⟩

end PositiveDimension

end Khachiyan.RankOne
