import Khachiyan.RankOne
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# M05: diminishing trace increments

This module implements M05 of `proof.md`, including the positive-semidefinite
strong-subadditivity form. Matrix order is Loewner order; powers are CFC powers.
-/

noncomputable section
open scoped NNReal MatrixOrder Matrix.Norms.L2Operator
open Matrix Set Filter Topology

namespace Khachiyan.Diminishing

variable {n : ℕ}

theorem trace_mul_nonneg {A B : MatR n} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  let S := CFC.sqrt B
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have hs := hA.conjTranspose_mul_mul_same S
  rw [hS.isHermitian.eq] at hs
  have heq : (S * A * S).trace = (A * B).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm (S * S) A]
    rw [show S * S = B by exact CFC.sqrt_mul_sqrt_self B hB.nonneg]
  rw [← heq]
  exact hs.trace_nonneg

theorem trace_mul_mono {A B H : MatR n} (hAB : A ≤ B) (hH : H.PosSemidef) :
    (A * H).trace ≤ (B * H).trace := by
  have h := trace_mul_nonneg (Matrix.le_iff.mp hAB) hH
  rw [sub_mul, Matrix.trace_sub] at h
  linarith

variable [NeZero n]

theorem hasDerivAt_trace_line (X H : MatR n) (s : ℝ) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hH : H.IsHermitian) (hP : (X + s • H).PosDef) :
    HasDerivAt (fun t : ℝ => (CFC.rpow (X + t • H) p).trace)
      (p * (CFC.rpow (X + s • H) (p - 1) * H).trace) s := by
  have h0 := TraceDerivative.hasDerivAt_trace_rpow hP hH hp
  have h0' : HasDerivAt (fun t : ℝ => (CFC.rpow (X + s • H + t • H) p).trace)
      (p * (CFC.rpow (X + s • H) (p - 1) * H).trace) (s - s) := by
    simpa only [sub_self] using h0
  have h := h0'.comp (h := fun t : ℝ => t - s) s ((hasDerivAt_id s).sub_const s)
  have heq (t : ℝ) : X + s • H + (t - s) • H = X + t • H := by module
  simpa only [Function.comp_def, heq, mul_one] using h

/-- M05 for ordered positive-definite base matrices and any PSD increment. -/
theorem trace_increment_antitone {X Y H : MatR n} (hX : X.PosDef)
    (hXY : X ≤ Y) (hH : H.PosSemidef) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    (CFC.rpow (Y + H) p).trace - (CFC.rpow Y p).trace ≤
      (CFC.rpow (X + H) p).trace - (CFC.rpow X p).trace := by
  have hY := MatrixPowers.posDef_of_le hX hXY
  have hx (t : ℝ) (ht : 0 ≤ t) : (X + t • H).PosDef :=
    hX.add_posSemidef (hH.smul ht)
  have hy (t : ℝ) (ht : 0 ≤ t) : (Y + t • H).PosDef :=
    hY.add_posSemidef (hH.smul ht)
  have h := RankOne.increment_le_of_derivative_le
    (fun t ht => hasDerivAt_trace_line Y H t hp hH.isHermitian (hy t ht))
    (fun t ht => hasDerivAt_trace_line X H t hp hH.isHermitian (hx t ht))
    (fun t ht => ?_) (t := 1) (by norm_num)
  · simpa only [one_smul, zero_smul, add_zero] using h
  · apply mul_le_mul_of_nonneg_left _ hp.1.le
    apply trace_mul_mono _ hH
    exact MatrixPowers.rpow_sub_one_antitone hp (hx t ht) (by
      simpa only [Matrix.le_iff, add_sub_add_right_eq_sub] using hXY)

omit [NeZero n] in
/-- Positive fractional powers are continuous on the entire PSD cone, including its boundary. -/
theorem continuousOn_rpow_nonneg {p : ℝ} (hp : 0 < p) :
    ContinuousOn (fun A : MatR n => CFC.rpow A p) {A | 0 ≤ A} := by
  let q : ℝ≥0 := ⟨p, hp.le⟩
  have hq : 0 < q := hp
  have hc : ContinuousOn (fun A : MatR n => CFC.nnrpow A q) {A | 0 ≤ A} :=
    CFC.continuousOn_nnrpow q
  exact hc.congr (fun A _ => (CFC.nnrpow_eq_rpow hq).symm)

omit [NeZero n] in
theorem trace_regularized_tendsto {A : MatR n} (hA : A.PosSemidef)
    {p : ℝ} (hp : 0 < p) :
    Tendsto (fun ε : ℝ => (CFC.rpow (A + ε • 1) p).trace)
      (𝓝[Ioi 0] 0) (𝓝 (CFC.rpow A p).trace) := by
  have hf : Continuous (fun ε : ℝ => A + ε • (1 : MatR n)) := by fun_prop
  have hm : MapsTo (fun ε : ℝ => A + ε • (1 : MatR n)) (Ioi 0) {B | 0 ≤ B} := by
    intro ε hε
    exact (hA.add (Matrix.PosSemidef.one.smul hε.le)).nonneg
  have hc : ContinuousWithinAt (fun ε : ℝ => CFC.rpow (A + ε • 1) p) (Ioi 0) 0 :=
    (continuousOn_rpow_nonneg hp (A + (0 : ℝ) • 1)
      (by simpa using hA.nonneg)).comp (f := fun ε : ℝ => A + ε • 1)
        hf.continuousWithinAt hm
  have ht := (TraceDerivative.traceCLM (n := n)).continuous.continuousAt.comp_continuousWithinAt hc
  simpa only [Function.comp_def, zero_smul, add_zero, TraceDerivative.traceCLM_apply]
    using ht.tendsto

omit [NeZero n] in
theorem regularized_posDef {A : MatR n} (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (A + ε • 1).PosDef := by
  simpa only [add_comm] using
    ((Matrix.PosDef.one : (1 : MatR n).PosDef).smul hε).add_posSemidef hA

/-- M05 on the PSD boundary, obtained by positive regularization and continuity. -/
theorem trace_strong_subadditivity {U V W : MatR n}
    (hU : U.PosSemidef) (hV : V.PosSemidef) (hW : W.PosSemidef)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    (CFC.rpow (U + V + W) p).trace + (CFC.rpow W p).trace ≤
      (CFC.rpow (U + W) p).trace + (CFC.rpow (V + W) p).trace := by
  apply le_of_tendsto_of_tendsto
    ((trace_regularized_tendsto ((hU.add hV).add hW) hp.1).add
      (trace_regularized_tendsto hW hp.1))
    ((trace_regularized_tendsto (hU.add hW) hp.1).add
      (trace_regularized_tendsto (hV.add hW) hp.1))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hXY : W + ε • (1 : MatR n) ≤ V + W + ε • 1 := by
    rw [Matrix.le_iff]
    convert hV using 1
    abel
  have h := trace_increment_antitone (regularized_posDef hW hε) hXY hU hp
  have h1 : V + W + ε • (1 : MatR n) + U = U + V + W + ε • 1 := by abel
  have h2 : W + ε • (1 : MatR n) + U = U + W + ε • 1 := by abel
  rw [h1, h2] at h
  linarith

end Khachiyan.Diminishing
