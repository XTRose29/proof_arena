import Submission.Dbar.Wirtinger
import Submission.Dbar.CauchyKernel
import Submission.Dbar.SolveDisk
import Submission.Dbar.Form01
import Submission.Dbar.Operator
import Submission.Dbar.PlanarPoU
import Submission.Dbar.PlanarCousin
import Submission.Dbar.DiskAcyclic

/-!
# dbar-solvability: the `∂̄`-equation on Riemann surfaces (namespace `RS`)

API summary (see `docs/design/dbar-solvability.md`). Zero sorries throughout.

* **Planar core** (mathlib-only): `wirtingerD`/`wirtingerDbar` + the CR bridge
  (`Wirtinger.lean`); `cauchyKernel`/`cauchyTransform` and Forster 13.1
  (`exists_dbar_solution_of_hasCompactSupport`, `CauchyKernel.lean`); Forster 13.2 on disks
  (`exists_dbar_solution_ball`, `SolveDisk.lean`); finite smooth partitions of unity
  (`exists_smooth_partition_of_finite_cover`, `PlanarPoU.lean`); the planar Cousin atoms
  (`exists_smooth_splitting`/`exists_holo_splitting_ball`, `PlanarCousin.lean`).
* **Surface layer**: `Form01 X` (chart-coefficient `(0,1)`-forms, `Form01.lean`); `SmoothC X`,
  the intrinsic `dbar : SmoothC X →ₗ[ℂ] Form01 X`, `IsDbarAt`/`IsDbarOn`,
  `contMDiffOn_omega_of_isDbarOn_zero`, `contMDiffOn_omega_sub_of_isDbarOn`, and chart-disk
  solvability `exists_dbar_solution_chart_ball` (`Operator.lean`).
* **Disk acyclicity** (`DiskAcyclic.lean`): `subsingleton_h1Cover_zero_of_isChartDisk`, the
  `D = 0` case of Čech `H¹` vanishing on chart-disk covers — the general-divisor twist is NOT
  included (see the file's docstring and the build log for the honest scope note).
-/
