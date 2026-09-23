import Khachiyan.EllipsoidGeometry

/-!
# G01V: the ellipsoid volume bridge

This module connects the concrete affine-image definition of an ellipsoid to
actual Lebesgue measure on `EuclideanSpace`.  The determinant of the linear map
induced by a real matrix is identified with the matrix determinant using the
standard Euclidean orthonormal basis.  Positivity of the unit-ball volume and
finiteness of every ellipsoid volume are recorded before any later cancellation.
-/

noncomputable section

open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix Set MeasureTheory

namespace Khachiyan

variable {n : ℕ}

theorem unitBall_volume_pos [NeZero n] :
    0 < volume (unitBall n) := by
  simpa [unitBall] using
    (measure_closedBall_pos (volume : Measure (V n)) (0 : V n) (by norm_num))

theorem matrix_action_det_eq (A : MatR n) :
    LinearMap.det
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) A : V n →L[ℝ] V n) : V n →ₗ[ℝ] V n) =
      A.det := by
  let b : Module.Basis (Fin n) ℝ (V n) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hmat : LinearMap.toMatrix b b
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) A : V n →L[ℝ] V n) : V n →ₗ[ℝ] V n) = A := by
    ext i j
    simp [b, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply]
  rw [← LinearMap.det_toMatrix b, hmat]

theorem volume_translate (a : V n) (s : Set (V n)) :
    volume ((fun x : V n => a + x) '' s) = volume s := by
  rw [image_add_left, measure_preimage_add]

theorem volume_linear_image (A : MatR n) (s : Set (V n)) :
    volume (Matrix.toEuclideanCLM (𝕜 := ℝ) A '' s) =
      ENNReal.ofReal |A.det| * volume s := by
  rw [MeasureTheory.Measure.addHaar_image_continuousLinearMap,
    matrix_action_det_eq]

theorem volume_ellipsoid_eq (a : V n) (A : MatR n) :
    volume (ellipsoid a A) =
      ENNReal.ofReal |A.det| * volume (unitBall n) := by
  rw [show ellipsoid a A = (fun x : V n => a + x) ''
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A '' unitBall n) by
        simp [ellipsoid, image_image], volume_translate, volume_linear_image]

theorem volume_ellipsoid_eq_det (hA : A.PosDef) (a : V n) :
    volume (ellipsoid a A) = ENNReal.ofReal A.det * volume (unitBall n) := by
  rw [volume_ellipsoid_eq]
  rw [abs_of_pos hA.det_pos]

theorem volume_ellipsoid_pos [NeZero n] {a : V n} {A : MatR n}
    (hA : A.PosDef) : 0 < volume (ellipsoid a A) := by
  rw [volume_ellipsoid_eq_det hA a]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hA.det_pos).ne'
    unitBall_volume_pos.ne'

theorem volume_ellipsoid_ne_zero [NeZero n] {a : V n} {A : MatR n}
    (hA : A.PosDef) : volume (ellipsoid a A) ≠ 0 :=
  (volume_ellipsoid_pos hA).ne'

end Khachiyan
