import Khachiyan.GeometricBound
import Khachiyan.Sharpness
import Khachiyan.DiminishingIncrements
import Khachiyan.Nonattainment
import Khachiyan.OneDimensional
import Khachiyan.NearEquality
import Khachiyan.CutIterations

/-!
# Khachiyan's inscribed-ellipsoid cutting inequality and uniform optimality

The main objective in `proof.md` is provided by:
* `Khachiyan.t01`: the actual geometric volume bound in every positive dimension;
* `Khachiyan.sharp_constant`: every smaller real constant fails in some dimension
  at least two, for a convex body cut through its canonical maximal-ellipsoid center.

The cone construction also proves convergence of its actual maximal-volume ratios.
M05 is proved in `DiminishingIncrements`. T03 is proved in `Nonattainment`, and
its exact one-dimensional ratio in `OneDimensional`. T04 is proved in
`NearEquality`, and T05 in `CutIterations`. The completed independent resolvent
proof A01/M04R is in `Resolvent`, imported separately by the project root.
The geometric conclusions here use the original M03/M04 route.
-/
