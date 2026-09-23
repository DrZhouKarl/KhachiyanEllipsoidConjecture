import Khachiyan.Basic
import Khachiyan.MatrixBridge
import Khachiyan.MatrixPowers
import Khachiyan.PowerIntegral
import Khachiyan.Resolvent
import Khachiyan.TraceDerivative
import Khachiyan.RankOne
import Khachiyan.EllipsoidGeometry
import Khachiyan.IntermediateEllipsoid
import Khachiyan.TraceConstraint
import Khachiyan.TwoIterates
import Khachiyan.DeterminantBound
import Khachiyan.NormalizedBound
import Khachiyan.VolumeBridge
import Khachiyan.JohnExistence
import Khachiyan.JohnUniqueness
import Khachiyan.Normalization
import Khachiyan.GeometricBound
import Khachiyan.Main
import Khachiyan.DiminishingIncrements
import Khachiyan.Nonattainment
import Khachiyan.OneDimensional
import Khachiyan.NearEquality
import Khachiyan.CutIterations
import Khachiyan.ScalarBounds
import Khachiyan.Smoke
import Khachiyan.MathlibProbe

/-!
Current root: B01, S01, M01--M04, G01S, G02, G05, R01, and R02.  R01 includes
the three M04 applications, the exact intermediate-trace cancellation, and
the two spectral constraints.  R02 includes logarithmic determinant bounds and
the finite-dimensional AM--GM bounds.  N01 combines the R02 envelope with
the exact S01 scalar maximum.  G01V now supplies the actual Lebesgue-volume
bridge for ellipsoids, and G03E supplies positive feasible witnesses and the
finite/positive volume foundation for the direct method.  The maximal-ellipsoid
existence and uniqueness theorems are now both available. G04 supplies affine
normalization, center exclusion, halfspace transport, preservation of maximality,
actual volume ratios and supremum attainment, and the convex-body cut interface.
The normalized retained-side determinant bound is connected to N01. T01 now
proves the actual geometric volume bound in every positive dimension, including
the canonical maximum-volume ellipsoid center and the convex-body cut conclusion.
C01--C03 supply the finite contact certificate, the explicit cone family, and
the actual volume-ratio limit. T02 proves uniform optimality of the constant.
The main objective and the additional conclusions below are complete; the
alternative resolvent proof is also complete in `Resolvent` and
`ResolventScalar`, including the independent A01 integral, both endpoint
arguments, and the full M04R inequality.
M05 is also complete in both its positive-definite and positive-semidefinite
forms. T03 supplies the strict geometric volume bound in every finite positive
dimension and the exact one-dimensional optimal ratio of one half.
T04 proves the near-equality semiaxis constraints, and T05 the multiplicative
volume and logarithmic progress bounds for exact central-cut sequences.
-/
