import Khachiyan.TwoIterates
import Khachiyan.ScalarBounds
import Khachiyan.Smoke
import Mathlib.Analysis.MeanInequalities

/-!
# R02: determinant bounds from the two spectral constraints

This module implements the two determinant estimates in Section 4 of
`proof.md`.  The logarithmic estimate is proved for an arbitrary positive
exponent `p` and reciprocal exponent `q`; the two R02 bounds are its
specializations `(p,q) = (1/2,2)` and `(1/4,4)`.  A separate AM--GM lemma
handles the nontrivial finite-dimensional case `n ≥ 2`.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace BigOperators
open Matrix Set

namespace Khachiyan

variable {n : ℕ} [NeZero n]

theorem r02_log_det_bound {A : MatR n} (hA : A.PosDef)
    {p q f : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : q * p = 1)
    (hconstraint :
      f + ∑ i ∈ Finset.univ.erase (Spectral.minIndex hA.isHermitian),
        (hA.isHermitian.eigenvalues i) ^ p ≤ n) :
    A.det ≤ Spectral.minEigenvalue hA.isHermitian * Real.exp (q * (1 - f)) := by
  let α := Spectral.minEigenvalue hA.isHermitian
  let e := hA.isHermitian.eigenvalues
  let s := Finset.univ.erase (Spectral.minIndex hA.isHermitian)
  have hα : 0 < α := Spectral.minEigenvalue_pos hA
  have hepos : ∀ i ∈ s, 0 < e i := by
    intro i hi
    exact hA.eigenvalues_pos i
  have hsum : ∑ i ∈ s, e i ^ p ≤ (n : ℝ) - f := by
    dsimp [s, e, α] at hconstraint ⊢
    linarith
  have hlog_each : ∀ i ∈ s, Real.log (e i ^ p) ≤ e i ^ p - 1 := by
    intro i hi
    exact Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (hepos i hi) p)
  have hlogsum :
      ∑ i ∈ s, Real.log (e i ^ p) ≤ (n : ℝ) - f - (s.card : ℝ) := by
    calc
      ∑ i ∈ s, Real.log (e i ^ p) ≤ ∑ i ∈ s, (e i ^ p - 1) :=
        Finset.sum_le_sum (fun i hi => hlog_each i hi)
      _ = (∑ i ∈ s, e i ^ p) - (s.card : ℝ) := by
        rw [Finset.sum_sub_distrib]
        simp
      _ ≤ (n : ℝ) - f - (s.card : ℝ) := by linarith
  have hcard : (s.card : ℝ) = (n : ℝ) - 1 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    norm_num [Fintype.card_fin, Nat.cast_sub hn]
  have hlogsum' :
      ∑ i ∈ s, Real.log (e i ^ p) ≤ 1 - f := by
    rw [hcard] at hlogsum
    linarith
  have hlogdet :
      Real.log A.det ≤ Real.log α + q * (1 - f) := by
    have hlogdet' :
        Real.log (α * ∏ i ∈ s, e i) ≤ Real.log α + q * (1 - f) := by
      rw [Real.log_mul hα.ne' (Finset.prod_ne_zero_iff.2 (fun i hi =>
        (hepos i hi).ne'))]
      rw [Real.log_prod (fun i hi => (hepos i hi).ne')]
      have hlogrpow : ∀ i ∈ s, Real.log (e i ^ p) = p * Real.log (e i) := by
        intro i hi
        rw [Real.log_rpow (hepos i hi)]
      have hsumlog : ∑ i ∈ s, Real.log (e i) =
          q * ∑ i ∈ s, Real.log (e i ^ p) := by
        calc
          ∑ i ∈ s, Real.log (e i) =
              ∑ i ∈ s, q * Real.log (e i ^ p) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hlogrpow i hi]
            calc
              Real.log (e i) = (q * p) * Real.log (e i) := by rw [hpq, one_mul]
              _ = q * (p * Real.log (e i)) := by ring
          _ = q * ∑ i ∈ s, Real.log (e i ^ p) := by rw [Finset.mul_sum]
      rw [hsumlog]
      nlinarith [mul_le_mul_of_nonneg_left hlogsum' hq.le]
    rw [Spectral.det_eq_min_mul_prod_erase hA.isHermitian]
    exact hlogdet'
  have hdetpos : 0 < A.det := hA.det_pos
  have hexp := Real.exp_le_exp.mpr hlogdet
  rw [Real.exp_log hdetpos, Real.exp_add, Real.exp_log hα] at hexp
  exact hexp

theorem r02_log_bound_one {K : Set (V n)}
    (hK : IsJohnNormalized K) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    {a : V n} {A : MatR n} (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    {rho : ℝ} (hrho : 1 ≤ rho)
    (hrho_def : rho = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖) :
    A.det ≤ Scalar.R1 (Spectral.minEigenvalue hA.isHermitian) := by
  have hconstraint := r01_constraint_one hK hKconv hKclosed hA hell hrho hrho_def
  have h := r02_log_det_bound hA (p := (1 / 2 : ℝ)) (q := 2)
    (f := Real.sqrt (Spectral.minEigenvalue hA.isHermitian +
      (Spectral.minEigenvalue hA.isHermitian) ^ 2 / 4))
    (by norm_num) (by norm_num) (by norm_num) hconstraint
  simpa [Scalar.R1, Scalar.f1] using h

theorem r02_log_bound_two {K : Set (V n)}
    (hK : IsJohnNormalized K) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    {a : V n} {A : MatR n} (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    {rho : ℝ} (hrho : 1 ≤ rho)
    (hrho_def : rho = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖) :
    A.det ≤ Scalar.R2 (Spectral.minEigenvalue hA.isHermitian) := by
  have hconstraint := r01_constraint_two hK hKconv hKclosed hA hell hrho hrho_def
  have h := r02_log_det_bound hA (p := (1 / 4 : ℝ)) (q := 4)
    (f := Real.sqrt (Real.sqrt (Spectral.minEigenvalue hA.isHermitian +
      (Spectral.minEigenvalue hA.isHermitian) ^ 2 / 4) +
      (Spectral.minEigenvalue hA.isHermitian) ^ 2 / 16))
    (by norm_num) (by norm_num) (by norm_num) hconstraint
  simpa [Scalar.R2, Scalar.f1, Scalar.f2] using h

theorem r02_exp_bounds {K : Set (V n)}
    (hK : IsJohnNormalized K) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    {a : V n} {A : MatR n} (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    {rho : ℝ} (hrho : 1 ≤ rho)
    (hrho_def : rho = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖) :
    A.det ≤ min (Scalar.R1 (Spectral.minEigenvalue hA.isHermitian))
      (Scalar.R2 (Spectral.minEigenvalue hA.isHermitian)) := by
  exact le_min (r02_log_bound_one hK hKconv hKclosed hA hell hrho hrho_def)
    (r02_log_bound_two hK hKconv hKclosed hA hell hrho hrho_def)

theorem r02_amgm_det_bound {A : MatR n} (hA : A.PosDef)
    {p q f : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : q * p = 1)
    (hn : 2 ≤ n)
    (hconstraint :
      f + ∑ i ∈ Finset.univ.erase (Spectral.minIndex hA.isHermitian),
        (hA.isHermitian.eigenvalues i) ^ p ≤ n) :
    A.det ≤ Spectral.minEigenvalue hA.isHermitian *
      (((n : ℝ) - f) / (n - 1 : ℝ)) ^ (q * (n - 1 : ℝ)) := by
  let α := Spectral.minEigenvalue hA.isHermitian
  let e := hA.isHermitian.eigenvalues
  let s := Finset.univ.erase (Spectral.minIndex hA.isHermitian)
  have hα : 0 < α := Spectral.minEigenvalue_pos hA
  have hepos : ∀ i ∈ s, 0 < e i := by
    intro i hi
    exact hA.eigenvalues_pos i
  have hs_nonempty : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs
    have hc : s.card = 0 := Finset.card_eq_zero.mpr hs
    have hcard : s.card = n - 1 := by
      dsimp [s]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      simp [Fintype.card_fin]
    rw [hcard] at hc
    omega
  have hsum : ∑ i ∈ s, e i ^ p ≤ (n : ℝ) - f := by
    dsimp [s, e, α] at hconstraint ⊢
    linarith
  have hcpos : 0 < (s.card : ℝ) := by exact_mod_cast hs_nonempty.card_pos
  have hgm := Real.geom_mean_le_arith_mean s (fun _ => (1 : ℝ))
      (fun i => e i ^ p) (fun _ _ => by norm_num)
      (by simpa using hcpos) (fun i hi => Real.rpow_nonneg (hepos i hi).le p)
  have hgm' :
      (∏ i ∈ s, (e i ^ p)) ^ (s.card : ℝ)⁻¹ ≤
        (∑ i ∈ s, e i ^ p) / (s.card : ℝ) := by
    simpa [Real.rpow_one, Finset.sum_const, nsmul_eq_mul, hcpos.ne'] using hgm
  have hprod_pow :
      ∏ i ∈ s, e i ^ p ≤
        ((∑ i ∈ s, e i ^ p) / (s.card : ℝ)) ^ (s.card : ℕ) := by
    have hprod : 0 < ∏ i ∈ s, e i ^ p :=
      Finset.prod_pos (fun i hi => Real.rpow_pos_of_pos (hepos i hi) p)
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hprod.le _)
      hgm' hcpos.le
    have hleft :
        ((∏ i ∈ s, e i ^ p) ^ (s.card : ℝ)⁻¹) ^ (s.card : ℝ) =
          ∏ i ∈ s, e i ^ p := by
      rw [← Real.rpow_mul hprod.le]
      congr 1
      field_simp
      simp
    rw [hleft] at hpow
    simpa only [Real.rpow_natCast, ← Finset.sum_div] using hpow
  have hprod : ∏ i ∈ s, e i ≤
      ((∑ i ∈ s, e i ^ p) / (s.card : ℝ)) ^ (q * (s.card : ℝ)) := by
    have hprod_nonneg : 0 ≤ ∏ i ∈ s, e i ^ p := by
      exact Finset.prod_nonneg (fun i hi => (Real.rpow_pos_of_pos (hepos i hi) p).le)
    have hpow := Real.rpow_le_rpow hprod_nonneg hprod_pow hq.le
    have hpq' : p * q = 1 := by nlinarith [hpq]
    have hleft :
        (∏ i ∈ s, e i ^ p) ^ q = ∏ i ∈ s, e i := by
      rw [Real.finsetProd_rpow s e (fun i hi => (hepos i hi).le) p]
      have heprod : 0 < ∏ i ∈ s, e i := Finset.prod_pos (fun i hi => hepos i hi)
      rw [← Real.rpow_mul heprod.le]
      simp [hpq']
    have hright :
        (((∑ i ∈ s, e i ^ p) / (s.card : ℝ)) ^ (s.card : ℕ)) ^ q =
          ((∑ i ∈ s, e i ^ p) / (s.card : ℝ)) ^ (q * (s.card : ℝ)) := by
      obtain ⟨i₀, hi₀⟩ := hs_nonempty
      have hsum_pos : 0 < ∑ i ∈ s, e i ^ p :=
        Finset.sum_pos' (fun i hi => (Real.rpow_pos_of_pos (hepos i hi) p).le)
          ⟨i₀, hi₀, Real.rpow_pos_of_pos (hepos i₀ hi₀) p⟩
      have hbasepos : 0 < (∑ i ∈ s, e i ^ p) / (s.card : ℝ) :=
        div_pos hsum_pos hcpos
      have hnat :
          ((∑ i ∈ s, e i ^ p) / (s.card : ℝ)) ^ (s.card : ℕ) =
            ((∑ i ∈ s, e i ^ p) / (s.card : ℝ)) ^ (s.card : ℝ) := by
        rw [Real.rpow_natCast]
      rw [hnat, ← Real.rpow_mul hbasepos.le]
      congr 1
      ring
    rw [hleft, hright] at hpow
    exact hpow
  have hbase :
      ((∑ i ∈ s, e i ^ p) / (s.card : ℝ)) ^ (q * (s.card : ℝ)) ≤
        (((n : ℝ) - f) / (n - 1 : ℝ)) ^ (q * (n - 1 : ℝ)) := by
    have hsum_nonneg : 0 ≤ ∑ i ∈ s, e i ^ p := by
      exact Finset.sum_nonneg (fun i hi => (Real.rpow_pos_of_pos (hepos i hi) p).le)
    have hleft : 0 ≤ (∑ i ∈ s, e i ^ p) / (s.card : ℝ) :=
      div_nonneg hsum_nonneg hcpos.le
    have hsum_le :
        (∑ i ∈ s, e i ^ p) / (s.card : ℝ) ≤
          ((n : ℝ) - f) / (n - 1 : ℝ) := by
      have hcard : (s.card : ℝ) = (n : ℝ) - 1 := by
        dsimp [s]
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
        have hn1 : 1 ≤ n := le_trans (by norm_num) hn
        norm_num [Fintype.card_fin, Nat.cast_sub hn1]
      rw [hcard]
      have hnpos : 0 < (n : ℝ) - 1 := by
        have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
        linarith
      exact (div_le_div_iff_of_pos_right hnpos).mpr hsum
    have hnonneg_exp : 0 ≤ q * (s.card : ℝ) := mul_nonneg hq.le hcpos.le
    have hcard : (s.card : ℝ) = (n : ℝ) - 1 := by
      dsimp [s]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      have hn1 : 1 ≤ n := le_trans (by norm_num) hn
      norm_num [Fintype.card_fin, Nat.cast_sub hn1]
    rw [hcard] at hleft hsum_le ⊢
    have hnonneg_exp' : 0 ≤ q * ((n : ℝ) - 1) := by
      have hnpos : 0 ≤ (n : ℝ) - 1 := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
        linarith
      exact mul_nonneg hq.le hnpos
    exact Real.rpow_le_rpow hleft hsum_le hnonneg_exp'
  rw [Spectral.det_eq_min_mul_prod_erase hA.isHermitian]
  have hprod_nonneg : 0 ≤ ∏ i ∈ s, e i := by
    exact Finset.prod_nonneg (fun i hi => (hepos i hi).le)
  have hdet := mul_le_mul_of_nonneg_left (hprod.trans hbase) hα.le
  simpa [α, e, s] using hdet

theorem r02_amgm_bound_one {K : Set (V n)}
    (hK : IsJohnNormalized K) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    {a : V n} {A : MatR n} (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    {rho : ℝ} (hrho : 1 ≤ rho)
    (hrho_def : rho = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖)
    (hn : 2 ≤ n) :
    A.det ≤ Spectral.minEigenvalue hA.isHermitian *
      (((n : ℝ) - Scalar.f1 (Spectral.minEigenvalue hA.isHermitian)) /
        (n - 1 : ℝ)) ^ (2 * (n - 1 : ℝ)) := by
  exact r02_amgm_det_bound hA (p := (1 / 2 : ℝ)) (q := 2)
    (f := Scalar.f1 (Spectral.minEigenvalue hA.isHermitian))
    (by norm_num) (by norm_num) (by norm_num) hn
    (r01_constraint_one hK hKconv hKclosed hA hell hrho hrho_def)

theorem r02_amgm_bound_two {K : Set (V n)}
    (hK : IsJohnNormalized K) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    {a : V n} {A : MatR n} (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    {rho : ℝ} (hrho : 1 ≤ rho)
    (hrho_def : rho = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖)
    (hn : 2 ≤ n) :
    A.det ≤ Spectral.minEigenvalue hA.isHermitian *
      (((n : ℝ) - Scalar.f2 (Spectral.minEigenvalue hA.isHermitian)) /
        (n - 1 : ℝ)) ^ (4 * (n - 1 : ℝ)) := by
  exact r02_amgm_det_bound hA (p := (1 / 4 : ℝ)) (q := 4)
    (f := Scalar.f2 (Spectral.minEigenvalue hA.isHermitian))
    (by norm_num) (by norm_num) (by norm_num) hn
    (r01_constraint_two hK hKconv hKclosed hA hell hrho hrho_def)

end Khachiyan
