import Submission.HopfTransportNormalized

open scoped unitInterval

noncomputable section

namespace Submission.HopfLift

open Submission.Helpers
open Submission.HopfTransport

/-- The capped grid coefficient `min k n / n` in the unit interval. -/
def gridCoefficient (n k : ℕ) : I :=
  ⟨((min k n : ℕ) : ℝ) / (n : ℝ),
    unitInterval.div_mem (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_le.mpr (Nat.min_le_right k n))⟩

/-- Scale a time parameter by the `k`th coefficient in an `n`-step
subdivision.  The cap makes the resulting target sequence constant after
stage `n`. -/
def scaledTime (n k : ℕ) (t : I) : I :=
  gridCoefficient n k * t

lemma continuous_scaledTime (n k : ℕ) :
    Continuous (scaledTime n k) := by
  apply Continuous.subtype_mk
  change Continuous fun t : I => (gridCoefficient n k : ℝ) * (t : ℝ)
  fun_prop

@[simp]
lemma scaledTime_zero (n : ℕ) (t : I) :
    scaledTime n 0 t = 0 := by
  apply Subtype.ext
  simp [scaledTime, gridCoefficient]

@[simp]
lemma scaledTime_self {n : ℕ} (hn : 0 < n) (t : I) :
    scaledTime n n t = t := by
  apply Subtype.ext
  simp [scaledTime, gridCoefficient, Nat.cast_ne_zero.mpr hn.ne']

/-- Successive capped grid scalings move a time coordinate by at most
`1 / n`. -/
lemma dist_scaledTime_succ_le {n k : ℕ} (hn : 0 < n) (t : I) :
    dist (scaledTime n k t) (scaledTime n (k + 1) t) ≤
      (1 : ℝ) / n := by
  change
    dist ((scaledTime n k t : I) : ℝ)
        ((scaledTime n (k + 1) t : I) : ℝ) ≤
      (1 : ℝ) / n
  rw [Real.dist_eq]
  change
    |((min k n : ℕ) : ℝ) / n * (t : ℝ) -
        ((min (k + 1) n : ℕ) : ℝ) / n * (t : ℝ)| ≤
      (1 : ℝ) / n
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hk : k < n
  · have hmin : min k n = k := Nat.min_eq_left hk.le
    have hminSucc : min (k + 1) n = k + 1 :=
      Nat.min_eq_left (Nat.succ_le_iff.mpr hk)
    rw [hmin, hminSucc]
    have heq :
        (k : ℝ) / n * (t : ℝ) -
            ((k + 1 : ℕ) : ℝ) / n * (t : ℝ) =
          -((t : ℝ) / n) := by
      push_cast
      field_simp
      ring
    rw [heq, abs_neg, abs_of_nonneg (div_nonneg t.property.1 hnR.le)]
    exact div_le_div_of_nonneg_right t.property.2 hnR.le
  · have hnk : n ≤ k := Nat.le_of_not_gt hk
    rw [Nat.min_eq_right hnk,
      Nat.min_eq_right (hnk.trans (Nat.le_add_right k 1))]
    simp

/-- The `k`th target in the capped subdivision of a family of paths. -/
def gridTarget {P : Type*} (f : P × I → SphereTwo)
    (n k : ℕ) (p : P × I) : SphereTwo :=
  f (p.1, scaledTime n k p.2)

lemma continuous_gridTarget {P : Type*} [TopologicalSpace P]
    {f : P × I → SphereTwo} (hf : Continuous f) (n k : ℕ) :
    Continuous (gridTarget f n k) :=
  hf.comp
    (continuous_fst.prodMk
      ((continuous_scaledTime n k).comp continuous_snd))

@[simp]
lemma gridTarget_zero {P : Type*} (f : P × I → SphereTwo)
    (n : ℕ) (p : P × I) :
    gridTarget f n 0 p = f (p.1, 0) := by
  simp [gridTarget]

@[simp]
lemma gridTarget_self {P : Type*} (f : P × I → SphereTwo)
    {n : ℕ} (hn : 0 < n) (p : P × I) :
    gridTarget f n n p = f p := by
  simp [gridTarget, scaledTime_self hn]

/-- A positive subdivision count on which consecutive targets of a family
of paths lie in the short-transport domain. -/
structure TargetSubdivision {P : Type*} (f : P × I → SphereTwo) where
  steps : ℕ
  steps_pos : 0 < steps
  short : ∀ k p,
    dist (gridTarget f steps k p) (gridTarget f steps (k + 1) p) < 2

/-- Heine--Cantor supplies a single short-transport subdivision valid for
all paths in a compact parameter family. -/
theorem exists_targetSubdivision {P : Type*}
    [PseudoMetricSpace P] [CompactSpace P]
    (f : P × I → SphereTwo) (hf : Continuous f) :
    Nonempty (TargetSubdivision f) := by
  have huc : UniformContinuous f :=
    CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hfδ⟩ :=
    Metric.uniformContinuous_iff.mp huc 2 (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨{
    steps := n + 1
    steps_pos := Nat.succ_pos n
    short := ?_ }⟩
  intro k p
  apply hfδ
  rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)]
  exact
    (dist_scaledTime_succ_le (Nat.succ_pos n) p.2).trans_lt
      (by simpa [Nat.cast_add, Nat.cast_one] using hn)

/-- A continuously parametrized lift of the `k`th map in a sequence of
maps to the 2-sphere. -/
structure Stage {P : Type*} [TopologicalSpace P]
    (y : ℕ → P → SphereTwo) (k : ℕ) where
  toFun : P → SphereThree
  continuous_toFun : Continuous toFun
  hopfMap_toFun : ∀ p, hopfMap (toFun p) = y k p

/-- Repeated short transport lifts a sequence of continuously varying
targets, provided consecutive targets stay less than distance two apart. -/
def stage {P : Type*} [TopologicalSpace P]
    (y : ℕ → P → SphereTwo)
    (z : P → SphereThree)
    (hz : Continuous z)
    (hzero : ∀ p, hopfMap (z p) = y 0 p)
    (hy : ∀ k, Continuous (y k))
    (hshort : ∀ k p, dist (y k p) (y (k + 1) p) < 2) :
    (k : ℕ) → Stage y k
  | 0 =>
      { toFun := z
        continuous_toFun := hz
        hopfMap_toFun := hzero }
  | k + 1 =>
      let previous := stage y z hz hzero hy hshort k
      let hadmissible :
          ∀ p, dist (hopfMap (previous.toFun p)) (y (k + 1) p) < 2 :=
        fun p => by
          rw [previous.hopfMap_toFun]
          exact hshort k p
      { toFun :=
          transportOf previous.toFun (y (k + 1)) hadmissible
        continuous_toFun :=
          continuous_transportOf hadmissible previous.continuous_toFun
            (hy (k + 1))
        hopfMap_toFun :=
          hopfMap_transportOf previous.toFun (y (k + 1)) hadmissible }

@[simp]
lemma stage_zero_toFun {P : Type*} [TopologicalSpace P]
    (y : ℕ → P → SphereTwo)
    (z : P → SphereThree)
    (hz : Continuous z)
    (hzero : ∀ p, hopfMap (z p) = y 0 p)
    (hy : ∀ k, Continuous (y k))
    (hshort : ∀ k p, dist (y k p) (y (k + 1) p) < 2) :
    (stage y z hz hzero hy hshort 0).toFun = z :=
  rfl

/-- If every target in the sequence agrees at a parameter, repeated short
transport leaves the initial lift unchanged at that parameter. -/
lemma stage_toFun_eq_of_targets_eq {P : Type*} [TopologicalSpace P]
    (y : ℕ → P → SphereTwo)
    (z : P → SphereThree)
    (hz : Continuous z)
    (hzero : ∀ p, hopfMap (z p) = y 0 p)
    (hy : ∀ k, Continuous (y k))
    (hshort : ∀ k p, dist (y k p) (y (k + 1) p) < 2)
    (p : P) (htarget : ∀ k, y k p = y 0 p) :
    ∀ k, (stage y z hz hzero hy hshort k).toFun p = z p := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      calc
        transportOf
              (stage y z hz hzero hy hshort k).toFun
              (y (k + 1)) _ p =
            (stage y z hz hzero hy hshort k).toFun p := by
          apply transportOf_eq_self
          rw [(stage y z hz hzero hy hshort k).hopfMap_toFun]
          exact (htarget (k + 1)).trans (htarget k).symm
        _ = z p := ih

/-- A chosen uniformly short subdivision of a compact family of paths. -/
def targetSubdivision {P : Type*}
    [PseudoMetricSpace P] [CompactSpace P]
    (f : P × I → SphereTwo) (hf : Continuous f) :
    TargetSubdivision f :=
  Classical.choice (exists_targetSubdivision f hf)

/-- The final recursive stage lifting a compact family of paths. -/
def pathFamilyStage {P : Type*}
    [PseudoMetricSpace P] [CompactSpace P]
    (f : P × I → SphereTwo) (hf : Continuous f)
    (z : P → SphereThree) (hz : Continuous z)
    (hzero : ∀ a, hopfMap (z a) = f (a, 0)) :
    Stage
      (fun k => gridTarget f (targetSubdivision f hf).steps k)
      (targetSubdivision f hf).steps :=
  stage
    (fun k => gridTarget f (targetSubdivision f hf).steps k)
    (fun p => z p.1)
    (hz.comp continuous_fst)
    (fun p => by simpa using hzero p.1)
    (fun k => continuous_gridTarget hf _ k)
    (targetSubdivision f hf).short
    (targetSubdivision f hf).steps

/-- A simultaneous lift of a compact family of paths through the concrete
Hopf map. -/
def pathFamilyLift {P : Type*}
    [PseudoMetricSpace P] [CompactSpace P]
    (f : P × I → SphereTwo) (hf : Continuous f)
    (z : P → SphereThree) (hz : Continuous z)
    (hzero : ∀ a, hopfMap (z a) = f (a, 0)) :
    P × I → SphereThree :=
  (pathFamilyStage f hf z hz hzero).toFun

lemma continuous_pathFamilyLift {P : Type*}
    [PseudoMetricSpace P] [CompactSpace P]
    (f : P × I → SphereTwo) (hf : Continuous f)
    (z : P → SphereThree) (hz : Continuous z)
    (hzero : ∀ a, hopfMap (z a) = f (a, 0)) :
    Continuous (pathFamilyLift f hf z hz hzero) :=
  (pathFamilyStage f hf z hz hzero).continuous_toFun

@[simp]
lemma hopfMap_pathFamilyLift {P : Type*}
    [PseudoMetricSpace P] [CompactSpace P]
    (f : P × I → SphereTwo) (hf : Continuous f)
    (z : P → SphereThree) (hz : Continuous z)
    (hzero : ∀ a, hopfMap (z a) = f (a, 0))
    (p : P × I) :
    hopfMap (pathFamilyLift f hf z hz hzero p) = f p := by
  have hp :=
    (pathFamilyStage f hf z hz hzero).hopfMap_toFun p
  exact hp.trans
    (gridTarget_self f (targetSubdivision f hf).steps_pos p)

@[simp]
lemma pathFamilyLift_zero {P : Type*}
    [PseudoMetricSpace P] [CompactSpace P]
    (f : P × I → SphereTwo) (hf : Continuous f)
    (z : P → SphereThree) (hz : Continuous z)
    (hzero : ∀ a, hopfMap (z a) = f (a, 0))
    (a : P) :
    pathFamilyLift f hf z hz hzero (a, 0) = z a := by
  let d := targetSubdivision f hf
  have hfixed :=
    stage_toFun_eq_of_targets_eq
      (fun k => gridTarget f d.steps k)
      (fun p : P × I => z p.1)
      (hz.comp continuous_fst)
      (fun p => by simpa using hzero p.1)
      (fun k => continuous_gridTarget hf _ k)
      d.short
      (a, 0)
      (fun k => by simp [gridTarget, scaledTime])
      d.steps
  simpa [pathFamilyLift, pathFamilyStage, d] using hfixed

/-- A lifted path whose base path is constant is the prescribed initial
lift at every time. -/
lemma pathFamilyLift_eq_of_path_eq {P : Type*}
    [PseudoMetricSpace P] [CompactSpace P]
    (f : P × I → SphereTwo) (hf : Continuous f)
    (z : P → SphereThree) (hz : Continuous z)
    (hzero : ∀ a, hopfMap (z a) = f (a, 0))
    (a : P) (t : I) (hpath : ∀ s, f (a, s) = f (a, 0)) :
    pathFamilyLift f hf z hz hzero (a, t) = z a := by
  let d := targetSubdivision f hf
  have hfixed :=
    stage_toFun_eq_of_targets_eq
      (fun k => gridTarget f d.steps k)
      (fun p : P × I => z p.1)
      (hz.comp continuous_fst)
      (fun p => by simpa using hzero p.1)
      (fun k => continuous_gridTarget hf _ k)
      d.short
      (a, t)
      (fun k => by
        calc
          gridTarget f d.steps k (a, t) = f (a, 0) := by
            exact hpath (scaledTime d.steps k t)
          _ = gridTarget f d.steps 0 (a, t) := by
            symm
            exact gridTarget_zero f d.steps (a, t))
      d.steps
  simpa [pathFamilyLift, pathFamilyStage, d] using hfixed

end Submission.HopfLift
