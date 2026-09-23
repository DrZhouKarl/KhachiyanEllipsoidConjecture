import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Scalar environment check

This module checks the mathlib logarithm inequality used in R02 of `proof.md`.
It is a bootstrap example, not a proof of R02 or S01.
-/

namespace Khachiyan.Smoke

theorem log_le_sub_one (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1 := by
  exact Real.log_le_sub_one_of_pos hx

end Khachiyan.Smoke
