# Khachiyan's Ellipsoid Conjecture

This repository records a Lean 4 formalization of a spectral proof of Khachiyan’s conjecture about the sharp dimension-independent cutting constant $\sqrt e/2$, using mathlib and actual Lebesgue volume.

For every positive-dimensional convex body, a closed halfspace through the center of its maximum-volume inscribed ellipsoid retains at most $\sqrt e/2$ of the maximum inscribed-ellipsoid volume. The constant is optimal uniformly over dimensions.

Full arXiv report: [A Spectral Proof of Khachiyan's Ellipsoid Conjecture](https://arxiv.org/abs/2609.28447)

The formalization includes existence and uniqueness of the maximal ellipsoid, affine normalization, the determinant-to-volume bridge, explicit cones proving sharpness, finite-dimensional nonattainment, the exact one-dimensional ratio, near-equality constraints, and iteration bounds for central cuts. It also contains two independent proofs of the general rank-one matrix inequality.

## Main declarations

| Result | Lean declaration |
|---|---|
| Geometric upper bound | `Khachiyan.t01` |
| Uniform optimality | `Khachiyan.sharp_constant` |
| Primary rank-one estimate | `Khachiyan.RankOne.trace_increment_lower_bound` |
| Independent resolvent proof | `Khachiyan.Resolvent.trace_increment_lower_bound` |
| Finite-dimensional nonattainment | `Khachiyan.t03` |
| Near-equality constraints | `Khachiyan.t04` |
| Iterated central cuts | `Khachiyan.t05` |

## Documentation and verification

- [Mathematical specification and proof](proof.md).
- [Module and dependency map](formalization_plan.md).
- [Installation and verification guide](lean_guide.md).

The project pins Lean `v4.35.0-rc2` and mathlib commit `0a6c8e0355da0405d616f80b9f8232c4fab2cc5b`. The complete axiom audit covers 598 declarations. The independent resolvent audit covers 43 public declarations and checks both the actual import graph and transitive proof dependencies. The verification script reruns the build and audits, accepting only `propext`, `Classical.choice`, and `Quot.sound` as foundational axioms.

All named mathematical results in the specification are formalized. This does not assert a line-by-line formalization of every calculation in the written proof; equivalent implementation choices are described in the module map.
