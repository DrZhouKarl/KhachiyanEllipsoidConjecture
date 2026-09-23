import Khachiyan.DeterminantBound

/-!
# N01: the normalized determinant bound

The R02 estimate is now combined with the exact scalar envelope from S01.
No spectral constraint is assumed here: both constraints enter through
`r02_exp_bounds`, which in turn derives them from the actual normalized
containment hypotheses via R01.
-/

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set

namespace Khachiyan

variable {n : ℕ} [NeZero n]

theorem n01_normalized_det_bound {K : Set (V n)}
    (hK : IsJohnNormalized K) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    {a : V n} {A : MatR n} (hA : A.PosDef) (hell : ellipsoid a A ⊆ K)
    {rho : ℝ} (hrho : 1 ≤ rho)
    (hrho_def : rho = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ a‖) :
    A.det ≤ rStar := by
  have hα : 0 < Spectral.minEigenvalue hA.isHermitian :=
    Spectral.minEigenvalue_pos hA
  have hR := r02_exp_bounds hK hKconv hKclosed hA hell hrho hrho_def
  exact hR.trans (Scalar.joint_bound hα)

end Khachiyan
