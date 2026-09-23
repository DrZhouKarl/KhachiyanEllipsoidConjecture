import Khachiyan.VolumeBridge

/-!
# G03E: existence of a maximum-volume inscribed ellipsoid

This module proves G03E by the direct method.  A convex body contains a
positive-radius ball, hence it has a positive-definite feasible ellipsoid.
The PSD-feasible parameter set is shown closed and bounded, determinant
attains a maximum on it, and the positive witness forces the maximizer to be
positive definite.  The resulting `exists_isMaxDet` theorem is the actual
maximality certificate used by later modules.
-/

noncomputable section

open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set Metric Filter TopologicalSpace MeasureTheory

namespace Khachiyan

variable {n : ℕ} [NeZero n]

theorem exists_positive_ball_subset {K : Set (V n)} (hK : IsConvexBody K) :
    ∃ c : V n, ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ K := by
  rcases hK.2.2 with ⟨c, hc⟩
  have hnh : K ∈ nhds c := mem_interior_iff_mem_nhds.mp hc
  rcases Metric.mem_nhds_iff.mp hnh with ⟨r, hr, hball⟩
  refine ⟨c, r / 2, half_pos hr, ?_⟩
  intro x hx
  apply hball
  exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith))

theorem exists_positive_feasible_ellipsoid {K : Set (V n)}
    (hK : IsConvexBody K) :
    ∃ c : V n, ∃ A : MatR n, A.PosDef ∧ ellipsoid c A ⊆ K := by
  obtain ⟨c, r, hr, hball⟩ := exists_positive_ball_subset hK
  refine ⟨c, (r / 2) • (1 : MatR n), Matrix.PosDef.one.smul (half_pos hr), ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_ellipsoid c ((r / 2) • (1 : MatR n)) x).mp hx
  apply hball
  rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) ((r / 2) • (1 : MatR n)) y =
      (r / 2) • y by simp]
  apply mem_closedBall'.mpr
  have hdist : dist c (c + (r / 2) • y) = ‖(r / 2) • y‖ := by
    rw [dist_comm, dist_eq_norm]
    congr 1
    abel
  rw [hdist, norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  have h := mul_le_mul_of_nonneg_left hy (le_of_lt (half_pos hr))
  nlinarith [hr]

theorem feasible_volume_pos {K : Set (V n)} (hK : IsConvexBody K) :
    ∃ c : V n, ∃ A : MatR n, IsFeasible K c A ∧ 0 < volume (ellipsoid c A) := by
  obtain ⟨c, A, hA, hsub⟩ := exists_positive_feasible_ellipsoid hK
  exact ⟨c, A, ⟨hA, hsub⟩, volume_ellipsoid_pos hA⟩

theorem feasible_volume_lt_top {K : Set (V n)} {c : V n} {A : MatR n}
    (hfeas : IsFeasible K c A) : volume (ellipsoid c A) < ∞ :=
  volume_ellipsoid_lt_top c A

theorem feasible_center_mem {K : Set (V n)} {c : V n} {A : MatR n}
    (hfeas : IsFeasible K c A) : c ∈ K :=
  hfeas.2 (center_mem_ellipsoid c A)

theorem feasible_shape_opNorm_le {K : Set (V n)} {c : V n} {A : MatR n}
    (hK : IsConvexBody K) (hfeas : IsFeasible K c A) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A : V n →L[ℝ] V n)‖ ≤
      Metric.diam K / 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  by_cases hx : x = 0
  · simp [hx]
  let u : V n := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (norm_pos_iff.mpr hx)]
    field_simp
  have hplus : c + Matrix.toEuclideanCLM (𝕜 := ℝ) A u ∈ K := by
    apply hfeas.2
    exact (mem_ellipsoid c A _).2 ⟨u, hu.le, rfl⟩
  have hminus : c + Matrix.toEuclideanCLM (𝕜 := ℝ) A (-u) ∈ K := by
    apply hfeas.2
    exact (mem_ellipsoid c A _).2 ⟨-u, by simpa using hu.le, rfl⟩
  have hdist : dist (c + Matrix.toEuclideanCLM (𝕜 := ℝ) A u)
      (c + Matrix.toEuclideanCLM (𝕜 := ℝ) A (-u)) ≤ Metric.diam K :=
    Metric.dist_le_diam_of_mem hK.1.isBounded hplus hminus
  have hAu : 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A u‖ ≤ Metric.diam K := by
    rw [dist_eq_norm] at hdist
    have heq :
        c + Matrix.toEuclideanCLM (𝕜 := ℝ) A u -
            (c + Matrix.toEuclideanCLM (𝕜 := ℝ) A (-u)) =
          (2 : ℝ) • Matrix.toEuclideanCLM (𝕜 := ℝ) A u := by
      rw [map_neg]
      module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hdist
    simpa using hdist
  have hAu' : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A u‖ ≤ Metric.diam K / 2 := by
    linarith
  have hscale : Matrix.toEuclideanCLM (𝕜 := ℝ) A x =
      ‖x‖ • Matrix.toEuclideanCLM (𝕜 := ℝ) A u := by
    have hxrep : x = ‖x‖ • u := by
      dsimp [u]
      rw [smul_smul]
      field_simp [norm_pos_iff.mpr hx]
      simp
    rw [hxrep, map_smul]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), hu, mul_one]
  rw [hscale, norm_smul]
  simpa [norm_norm, mul_comm] using mul_le_mul_of_nonneg_left hAu' (norm_nonneg x)

theorem feasible_parameter_bounds {K : Set (V n)} {c : V n} {A : MatR n}
    (hK : IsConvexBody K) (hfeas : IsFeasible K c A) :
    ∃ R : ℝ, 0 ≤ R ∧ ‖c‖ ≤ R ∧
      ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A : V n →L[ℝ] V n)‖ ≤ R := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : V n)).mp hK.1.isBounded
  have hc : c ∈ K := feasible_center_mem hfeas
  have hcR : c ∈ Metric.closedBall (0 : V n) R := hR hc
  have hR0 : 0 ≤ R := by
    by_contra hR0
    have : R < 0 := lt_of_not_ge hR0
    have := mem_closedBall.mp hcR
    have hd : 0 ≤ dist c (0 : V n) := dist_nonneg
    linarith
  have hdiam : 0 ≤ Metric.diam K / 2 := by positivity
  refine ⟨max R (Metric.diam K / 2), le_max_of_le_right hdiam, ?_, ?_⟩
  · exact le_max_of_le_left (by simpa using mem_closedBall.mp hcR)
  · exact (feasible_shape_opNorm_le hK hfeas).trans (le_max_right _ _)

theorem psd_shape_opNorm_le {K : Set (V n)} {c : V n} {A : MatR n}
    (hK : IsConvexBody K) (hA : A.PosSemidef) (hsub : ellipsoid c A ⊆ K) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A : V n →L[ℝ] V n)‖ ≤
      Metric.diam K / 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  by_cases hx : x = 0
  · simp [hx]
  let u : V n := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (norm_pos_iff.mpr hx)]
    field_simp
  have hplus : c + Matrix.toEuclideanCLM (𝕜 := ℝ) A u ∈ K := by
    apply hsub
    exact (mem_ellipsoid c A _).2 ⟨u, hu.le, rfl⟩
  have hminus : c + Matrix.toEuclideanCLM (𝕜 := ℝ) A (-u) ∈ K := by
    apply hsub
    exact (mem_ellipsoid c A _).2 ⟨-u, by simpa using hu.le, rfl⟩
  have hdist := Metric.dist_le_diam_of_mem hK.1.isBounded hplus hminus
  rw [dist_eq_norm] at hdist
  have heq :
      c + Matrix.toEuclideanCLM (𝕜 := ℝ) A u -
          (c + Matrix.toEuclideanCLM (𝕜 := ℝ) A (-u)) =
        (2 : ℝ) • Matrix.toEuclideanCLM (𝕜 := ℝ) A u := by
    rw [map_neg]
    module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hdist
  have hAu : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A u‖ ≤ Metric.diam K / 2 := by
    linarith
  have hxrep : x = ‖x‖ • u := by
    dsimp [u]
    rw [smul_smul]
    field_simp [norm_pos_iff.mpr hx]
    simp
  calc
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A x‖ =
        ‖x‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A u‖ := by
      rw [hxrep, map_smul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg x)]
      have hnorm : ‖‖x‖ • u‖ = ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), hu, mul_one]
      rw [hnorm]
    _ ≤ ‖x‖ * (Metric.diam K / 2) :=
      mul_le_mul_of_nonneg_left hAu (norm_nonneg x)
    _ = Metric.diam K / 2 * ‖x‖ := by ring

def feasiblePSDParameters {n : ℕ} (K : Set (V n)) : Set (V n × MatR n) :=
  {p | p.2.PosSemidef ∧ ellipsoid p.1 p.2 ⊆ K}

theorem isClosed_posSemidef_set :
    IsClosed {A : MatR n | A.PosSemidef} := by
  have hHerm : IsClosed {A : MatR n | A.IsHermitian} := by
    change IsClosed {A : MatR n | Aᴴ = A}
    exact isClosed_eq (by fun_prop) continuous_id
  have hQ : IsClosed {A : MatR n |
      ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)} := by
    rw [show {A : MatR n | ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)} =
        ⋂ x : Fin n → ℝ, {A : MatR n | 0 ≤ x ⬝ᵥ (A *ᵥ x)} by
      ext A
      simp]
    apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const (by fun_prop)
  rw [show {A : MatR n | A.PosSemidef} =
      {A : MatR n | A.IsHermitian} ∩
        {A : MatR n | ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)} by
    ext A
    change A.PosSemidef ↔ A.IsHermitian ∧
      ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)
    exact Matrix.posSemidef_iff_dotProduct_mulVec]
  exact hHerm.inter hQ

theorem isClosed_feasiblePSDParameters {K : Set (V n)} (hKclosed : IsClosed K) :
    IsClosed (feasiblePSDParameters K) := by
  have hPSD : IsClosed {p : V n × MatR n | p.2.PosSemidef} :=
    isClosed_posSemidef_set.preimage continuous_snd
  have hcontain : IsClosed {p : V n × MatR n |
      ellipsoid p.1 p.2 ⊆ K} := by
    rw [show {p : V n × MatR n | ellipsoid p.1 p.2 ⊆ K} =
        ⋂ y : V n, ⋂ (_ : y ∈ unitBall n),
          {p : V n × MatR n |
            p.1 + Matrix.toEuclideanCLM (𝕜 := ℝ) p.2 y ∈ K} by
      ext p
      simp only [mem_setOf_eq, mem_iInter]
      constructor
      · intro hp y hy
        exact hp ((mem_ellipsoid p.1 p.2 _).2
          ⟨y, (mem_unitBall y).mp hy, rfl⟩)
      · intro hp x hx
        obtain ⟨y, hy, rfl⟩ := (mem_ellipsoid p.1 p.2 x).mp hx
        exact hp y ((mem_unitBall y).mpr hy)]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    exact hKclosed.preimage (by fun_prop)
  rw [show feasiblePSDParameters K =
      {p | p.2.PosSemidef} ∩ {p | ellipsoid p.1 p.2 ⊆ K} by rfl]
  exact hPSD.inter hcontain

theorem isBounded_feasiblePSDParameters {K : Set (V n)}
    (hK : IsConvexBody K) :
    Bornology.IsBounded (feasiblePSDParameters K) := by
  obtain ⟨R, hR, hRcenter, hRshape⟩ :
      ∃ R : ℝ, 0 ≤ R ∧
        (∀ {c : V n} {A : MatR n},
          c ∈ K → ‖c‖ ≤ R) ∧
        (∀ {c : V n} {A : MatR n},
          A.PosSemidef → ellipsoid c A ⊆ K → ‖A‖ ≤ R) := by
    have hKbound := hK.1.isBounded
    obtain ⟨R₀, hR₀⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : V n)).mp hKbound
    refine ⟨max R₀ (Metric.diam K / 2), ?_, ?_, ?_⟩
    · positivity
    · intro c A hc
      have hcR := hR₀ hc
      have hcn : ‖c‖ ≤ R₀ := by simpa using mem_closedBall.mp hcR
      exact hcn.trans (le_max_left _ _)
    · intro c A hA hsub
      simpa only [show ‖A‖ =
          ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A : V n →L[ℝ] V n)‖ by rfl] using
        (psd_shape_opNorm_le hK hA hsub).trans (le_max_right _ _)
  refine (Metric.isBounded_iff_subset_closedBall (0 : V n × MatR n)).2 ⟨R, ?_⟩
  intro p hp
  rw [mem_closedBall, dist_zero_right, Prod.norm_def]
  refine max_le ?_ ?_
  · exact hRcenter (A := p.2) (hp.2 (center_mem_ellipsoid (p.1) (p.2)))
  · exact hRshape hp.1 hp.2

theorem isCompact_feasiblePSDParameters {K : Set (V n)}
    (hK : IsConvexBody K) :
    IsCompact (feasiblePSDParameters K) :=
  Metric.isCompact_of_isClosed_isBounded
    (isClosed_feasiblePSDParameters hK.1.isClosed)
    (isBounded_feasiblePSDParameters hK)

theorem exists_max_det_feasiblePSDParameters {K : Set (V n)}
    (hK : IsConvexBody K) :
    ∃ p ∈ feasiblePSDParameters K,
      ∀ q ∈ feasiblePSDParameters K, q.2.det ≤ p.2.det := by
  have hcomp := isCompact_feasiblePSDParameters hK
  obtain ⟨c, A, hA, hsub⟩ := exists_positive_feasible_ellipsoid hK
  have hne : (feasiblePSDParameters K).Nonempty :=
    ⟨(c, A), hA.posSemidef, hsub⟩
  have hcont : ContinuousOn (fun p : V n × MatR n => p.2.det)
      (feasiblePSDParameters K) := by
    fun_prop
  obtain ⟨p, hp, hmax⟩ := hcomp.exists_isMaxOn hne hcont
  exact ⟨p, hp, hmax⟩

theorem exists_isMaxDet {K : Set (V n)} (hK : IsConvexBody K) :
    ∃ c : V n, ∃ A : MatR n, IsMaxDet K c A := by
  obtain ⟨p, hp, hmax⟩ := exists_max_det_feasiblePSDParameters hK
  have hpos : 0 < p.2.det := by
    obtain ⟨c₀, A₀, hA₀, hsub₀⟩ := exists_positive_feasible_ellipsoid hK
    have hle := hmax (c₀, A₀) ⟨hA₀.posSemidef, hsub₀⟩
    exact lt_of_lt_of_le hA₀.det_pos hle
  have hA : p.2.PosDef :=
    hp.1.posDef_iff_det_ne_zero.mpr hpos.ne'
  refine ⟨p.1, p.2, ⟨hA, hp.2⟩, ?_⟩
  intro c A hfeas
  exact hmax (c, A) ⟨hfeas.1.posSemidef, hfeas.2⟩

theorem midpoint_feasible_of_feasible {K : Set (V n)}
    (hKconv : Convex ℝ K) {c₀ c₁ : V n} {A₀ A₁ : MatR n}
    (h₀ : IsFeasible K c₀ A₀) (h₁ : IsFeasible K c₁ A₁) :
    IsFeasible K ((1 / 2 : ℝ) • c₀ + (1 / 2 : ℝ) • c₁)
      ((1 / 2 : ℝ) • A₀ + (1 / 2 : ℝ) • A₁) := by
  refine ⟨?_, ?_⟩
  · exact (h₀.1.smul (by norm_num)).add (h₁.1.smul (by norm_num))
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := (mem_ellipsoid _ _ x).mp hx
    rw [← hxy]
    have hz₀ : c₀ + Matrix.toEuclideanCLM (𝕜 := ℝ) A₀ y ∈ K := by
      apply h₀.2
      exact (mem_ellipsoid c₀ A₀ _).2 ⟨y, hy, rfl⟩
    have hz₁ : c₁ + Matrix.toEuclideanCLM (𝕜 := ℝ) A₁ y ∈ K := by
      apply h₁.2
      exact (mem_ellipsoid c₁ A₁ _).2 ⟨y, hy, rfl⟩
    have hc := hKconv hz₀ hz₁ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1)
    simpa [map_add, map_smul, add_smul, smul_add, add_assoc, add_left_comm,
      add_comm] using hc

theorem maxDet_midpoint_le_of_isMaxDet {K : Set (V n)}
    (hKconv : Convex ℝ K) {c₀ c₁ : V n} {A₀ A₁ : MatR n}
    (h₀ : IsMaxDet K c₀ A₀) (h₁ : IsMaxDet K c₁ A₁) :
    (((1 / 2 : ℝ) • A₀ + (1 / 2 : ℝ) • A₁).det) ≤ A₀.det := by
  have hm := midpoint_feasible_of_feasible hKconv h₀.feasible h₁.feasible
  exact h₀.det_le _ _ hm

theorem maxDet_same_shape_of_isMaxDet {K : Set (V n)}
    (hKconv : Convex ℝ K) {c₀ c₁ : V n} {A₀ A₁ : MatR n}
    (h₀ : IsMaxDet K c₀ A₀) (h₁ : IsMaxDet K c₁ A₁)
    (hstrict : A₀ ≠ A₁ →
      A₀.det < ((1 / 2 : ℝ) • A₀ + (1 / 2 : ℝ) • A₁).det) :
    A₀ = A₁ := by
  by_contra hne
  have hmid := maxDet_midpoint_le_of_isMaxDet hKconv h₀ h₁
  have hlt := hstrict hne
  exact (not_lt_of_ge hmid) hlt

theorem strict_scalar_midpoint_prod {ι : Type*} [Fintype ι]
    (vals : ι → ℝ) (hvals : ∀ i, 0 < vals i) (hne : ∃ i, vals i ≠ 1) :
    (∏ i, Real.sqrt (vals i)) < ∏ i, (1 + vals i) / 2 := by
  have hnonneg : ∀ i, 0 ≤ Real.sqrt (vals i) := fun i => Real.sqrt_nonneg _
  have hle : ∀ i, Real.sqrt (vals i) ≤ (1 + vals i) / 2 := by
    intro i
    have hs : (Real.sqrt (vals i)) ^ 2 = vals i := Real.sq_sqrt (hvals i).le
    have hsq : 0 ≤ (Real.sqrt (vals i) - 1) ^ 2 := sq_nonneg _
    nlinarith
  have hlt : ∃ i, Real.sqrt (vals i) < (1 + vals i) / 2 := by
    obtain ⟨i, hi⟩ := hne
    refine ⟨i, ?_⟩
    by_contra hnlt
    have heq : Real.sqrt (vals i) = (1 + vals i) / 2 := le_antisymm (hle i) (le_of_not_gt hnlt)
    have hs : (Real.sqrt (vals i)) ^ 2 = vals i := Real.sq_sqrt (hvals i).le
    have : vals i = 1 := by nlinarith
    exact hi this
  exact Finset.prod_lt_prod₀
    (fun i _ => Real.sqrt_pos.2 (hvals i))
    (fun i _ => hle i)
    (by obtain ⟨i, hi⟩ := hlt; exact ⟨i, Finset.mem_univ _, hi⟩)

theorem strict_affine_det_of_eigenvalues {C : MatR n} (hC : C.PosDef)
    (hne : ∃ i, hC.isHermitian.eigenvalues i ≠ 1) :
    Real.sqrt C.det <
      ((1 / 2 : ℝ) • (1 : MatR n) + (1 / 2 : ℝ) • C).det := by
  have hdet : ((1 / 2 : ℝ) • (1 : MatR n) + (1 / 2 : ℝ) • C).det =
      ∏ i, (1 + hC.isHermitian.eigenvalues i) / 2 := by
    have hcfc : cfc (fun x : ℝ => (1 + x) / 2) C =
        (1 / 2 : ℝ) • (1 : MatR n) + (1 / 2 : ℝ) • C := by
      have hfun : (fun x : ℝ => (1 + x) / 2) =
          (fun x : ℝ => 1 / 2 + x / 2) := by funext x; ring
      rw [hfun]
      rw [cfc_const_add (1 / 2 : ℝ) (fun x : ℝ => x / 2) C (by fun_prop)
        hC.isHermitian.isSelfAdjoint]
      have hdiv : (fun x : ℝ => x / 2) =
          (fun x : ℝ => (1 / 2) * x) := by funext x; ring
      rw [hdiv, cfc_const_mul _ _ _ (by fun_prop),
        cfc_id' ℝ C hC.isHermitian.isSelfAdjoint,
        Algebra.algebraMap_eq_smul_one]
    rw [← hcfc, Spectral.det_cfc hC.isHermitian]
  rw [hdet, Spectral.det_eq_prod hC.isHermitian]
  have hvals : ∀ i, 0 < hC.isHermitian.eigenvalues i :=
    fun i => hC.eigenvalues_pos i
  have hstrict := strict_scalar_midpoint_prod
    (fun i => hC.isHermitian.eigenvalues i) hvals hne
  calc
    Real.sqrt (∏ i, hC.isHermitian.eigenvalues i) =
        ∏ i, Real.sqrt (hC.isHermitian.eigenvalues i) := by
      simpa using (Real.sqrt_prod Finset.univ (fun i _ => (hvals i).le))
    _ < _ := hstrict

end Khachiyan
