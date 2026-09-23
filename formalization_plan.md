# Formal statements and module map

The mathematical specification is [proof.md](proof.md). Setup and verification
commands are in [lean_guide.md](lean_guide.md). The root `Khachiyan.lean` imports
the complete theorem chain and the independent resolvent proof.

## Representation and scope

- Geometry uses `EuclideanSpace ℝ (Fin n)` and its Euclidean norm.
- Real matrices use `Matrix (Fin n) (Fin n) ℝ`; `MatrixOrder` gives Loewner order.
- Positive definiteness is `Matrix.PosDef`. Fractional powers use `CFC.rpow`.
- Ellipsoid volume is actual Lebesgue volume. Positivity and finiteness are proved
  before converting extended-real measures or dividing by volume.
- The geometric result covers every positive dimension, compact convex bodies
  with nonempty interior, exact maximal ellipsoids, and proper central halfspaces.

## Completed modules

| Specification node | Module or modules |
|---|---|
| B01: definitions and bridges | `Basic` |
| S01: sharp scalar envelope and weighted certificate | `ScalarBounds` |
| M01: spectral formulas and minimum eigenvalue | `MatrixBridge` |
| M02: order, inverse, and fractional powers | `MatrixPowers`, `PowerIntegral` |
| M03: trace derivative along self-adjoint directions | `TraceDerivative` |
| M04: general rank-one estimate and equality case | `RankOne` |
| M05: diminishing increments and PSD strong subadditivity | `DiminishingIncrements` |
| G01S: support functions, separation, affine shapes | `EllipsoidGeometry` |
| G01V: determinant-to-Lebesgue-volume bridge | `VolumeBridge` |
| G02: intermediate ellipsoid | `IntermediateEllipsoid` |
| G03: maximal-ellipsoid existence and uniqueness | `JohnExistence`, `JohnUniqueness` |
| G04: normalization, center exclusion, central cuts | `Normalization` |
| G05: trace constraint from actual maximality | `TraceConstraint` |
| R01: two iterations and spectral constraints | `TwoIterates` |
| R02: determinant bounds | `DeterminantBound` |
| N01: normalized determinant bound | `NormalizedBound` |
| T01: actual geometric upper bound | `GeometricBound` |
| C01: finite contact certificate | `ContactCertificate` |
| C02: explicit cone family | `ConeGeometry` |
| C03 and T02: volume-ratio limit and uniform optimality | `ConeLimit`, `Sharpness` |
| T03: nonattainment and exact one-dimensional ratio | `Nonattainment`, `OneDimensional` |
| T04: near-equality semiaxis constraints | `NearEquality` |
| T05: exact central-cut iterations | `CutIterations` |
| D01, A01, M04R: independent resolvent proof | `ResolventScalar`, `Resolvent` |

`Main` imports the geometric bound, sharpness, and named additional conclusions.
`Smoke` and `MathlibProbe` supply elementary checks and concrete interfaces;
they remain part of the root and full audit.

## Independent rank-one proofs

The primary route combines M02 operator order with the M03 trace derivative.
The derivative is taken along self-adjoint directions and does not differentiate
an eigenbasis varying with the matrix. `RankOne` proves the general inequality,
its equality case, and an attaining direction.

The independent route imports `Basic`, `MatrixBridge`, `MatrixPowers`,
`PowerIntegral`, `ResolventScalar`, and `Resolvent` only among project modules.
For positive scalars it proves

$$
|\log(s+x)-\log(s+y)|\le\frac{|x-y|}{s+\min(x,y)}.
$$

This bound gives absolute integrability and the two endpoint limits. Scalar
integration by parts, followed by finite sums in two fixed eigenbases, gives
the matrix log-resolvent integral. The determinant lemma identifies its rank-one
integrand. Inverse antitonicity and

$$
\alpha^2 I\preceq A^2,\qquad M+sI\preceq\frac{m+s}{\alpha^2}A^2
$$

give the required resolvent quadratic lower bound. The evaluated scalar integral
and logarithm monotonicity yield M04R for arbitrary unit directions and
noncommuting matrices. The resulting hypotheses and conclusion agree with M04.

The independent audit checks actual imports and transitive theorem types and
proof terms, in addition to printing axioms. The existing equality-case theorem
is retained in `RankOne` as a separate result.

## Verification boundary

All named nodes above are formalized. Some calculations use equivalent
implementations: for example, S01 uses normalized exponential convexity in place
of a Hessian computation, and the resolvent integral is assembled from scalar
integration by parts in fixed eigenbases. No theorem is weakened by these choices.

Lean checks the stated propositions. The specification and module map make the
intended mathematical interpretation reviewable; the claim is coverage of the
named statements rather than a line-by-line transcription of every calculation.
