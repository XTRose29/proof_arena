import Submission.QuaternionSpaceForm

/-!
# Coordinate paths for the quaternion space form

The paths in this file run along coordinate great circles.  Consequently each
product path uses at most three of the four quaternion coordinates.  This is
the geometric input needed to keep multiplication homotopies away from the
chosen puncture orbit.
-/

open Metric
open scoped Quaternion

namespace Submission.QuaternionPaths

open QuaternionObstruction
open QuaternionSpaceForm

noncomputable section

/-- One of the four real coordinates of a quaternion. -/
def coordinate (k : Fin 4) (q : ℍ) : ℝ :=
  ![q.re, q.imI, q.imJ, q.imK] k

/--
The imaginary coordinate used by the preferred path to a quaternion unit.
The paths to `1` and `-1` both use the `i`-circle.
-/
def pathAxis : Q8 → Fin 4
  | QuaternionGroup.a _ => 1
  | QuaternionGroup.xa k =>
      if k = 0 ∨ k = 2 then 2 else 3

private noncomputable def iPoint (θ : ℝ) : SphereThree :=
  ⟨⟨Real.cos θ, Real.sin θ, 0, 0⟩, by
    rw [mem_sphere_zero_iff_norm, norm_eq_sqrt_real_inner,
      Quaternion.inner_self]
    rw [show
      Quaternion.normSq (⟨Real.cos θ, Real.sin θ, 0, 0⟩ : ℍ) = 1 by
        simp only [Quaternion.normSq_def']
        nlinarith [Real.sin_sq_add_cos_sq θ]]
    norm_num⟩

private noncomputable def jPoint (θ : ℝ) : SphereThree :=
  ⟨⟨Real.cos θ, 0, Real.sin θ, 0⟩, by
    rw [mem_sphere_zero_iff_norm, norm_eq_sqrt_real_inner,
      Quaternion.inner_self]
    rw [show
      Quaternion.normSq (⟨Real.cos θ, 0, Real.sin θ, 0⟩ : ℍ) = 1 by
        simp only [Quaternion.normSq_def']
        nlinarith [Real.sin_sq_add_cos_sq θ]]
    norm_num⟩

private noncomputable def kPoint (θ : ℝ) : SphereThree :=
  ⟨⟨Real.cos θ, 0, 0, Real.sin θ⟩, by
    rw [mem_sphere_zero_iff_norm, norm_eq_sqrt_real_inner,
      Quaternion.inner_self]
    rw [show
      Quaternion.normSq (⟨Real.cos θ, 0, 0, Real.sin θ⟩ : ℍ) = 1 by
        simp only [Quaternion.normSq_def']
        nlinarith [Real.sin_sq_add_cos_sq θ]]
    norm_num⟩

private theorem cos_neg_pi_div_two :
    Real.cos (-Real.pi / 2) = 0 := by
  rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
    Real.cos_neg]
  simp

private theorem sin_neg_pi_div_two :
    Real.sin (-Real.pi / 2) = -1 := by
  rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
    Real.sin_neg]
  simp

private noncomputable def iArc (θ : ℝ) :
    Path (1 : SphereThree) (iPoint θ) where
  toFun t := iPoint (t.1 * θ)
  continuous_toFun := by
    apply Continuous.subtype_mk
    have h :
        Continuous fun t : unitInterval =>
          Quaternion.linearIsometryEquivTuple.symm
            (!₂[Real.cos (t.1 * θ), Real.sin (t.1 * θ), 0, 0] :
              EuclideanSpace ℝ (Fin 4)) := by
      fun_prop
    simpa [Quaternion.linearIsometryEquivTuple_symm_apply] using h
  source' := by
    apply Subtype.ext
    apply Quaternion.ext <;> simp [iPoint]
  target' := by
    apply Subtype.ext
    apply Quaternion.ext <;> simp [iPoint]

private noncomputable def jArc (θ : ℝ) :
    Path (1 : SphereThree) (jPoint θ) where
  toFun t := jPoint (t.1 * θ)
  continuous_toFun := by
    apply Continuous.subtype_mk
    have h :
        Continuous fun t : unitInterval =>
          Quaternion.linearIsometryEquivTuple.symm
            (!₂[Real.cos (t.1 * θ), 0, Real.sin (t.1 * θ), 0] :
              EuclideanSpace ℝ (Fin 4)) := by
      fun_prop
    simpa [Quaternion.linearIsometryEquivTuple_symm_apply] using h
  source' := by
    apply Subtype.ext
    apply Quaternion.ext <;> simp [jPoint]
  target' := by
    apply Subtype.ext
    apply Quaternion.ext <;> simp [jPoint]

private noncomputable def kArc (θ : ℝ) :
    Path (1 : SphereThree) (kPoint θ) where
  toFun t := kPoint (t.1 * θ)
  continuous_toFun := by
    apply Continuous.subtype_mk
    have h :
        Continuous fun t : unitInterval =>
          Quaternion.linearIsometryEquivTuple.symm
            (!₂[Real.cos (t.1 * θ), 0, 0, Real.sin (t.1 * θ)] :
              EuclideanSpace ℝ (Fin 4)) := by
      fun_prop
    simpa [Quaternion.linearIsometryEquivTuple_symm_apply] using h
  source' := by
    apply Subtype.ext
    apply Quaternion.ext <;> simp [kPoint]
  target' := by
    apply Subtype.ext
    apply Quaternion.ext <;> simp [kPoint]

private theorem smul_one_eq_q8ToSphere (q : Q8) :
    q • (1 : SphereThree) = q8ToSphere q := by
  simp [MulAction.compHom_smul_def]

/-- A path uses only its real coordinate and its designated imaginary axis. -/
def Supported (q : Q8) (p : Path (1 : SphereThree) (q • 1)) : Prop :=
  ∀ t k, k ≠ 0 → k ≠ pathAxis q →
    coordinate k (p t).1 = 0

private theorem exists_supportedPath (q : Q8) :
    ∃ p : Path (1 : SphereThree) (q • 1), Supported q p := by
  rcases q with k | k
  · fin_cases k
    · have htarget :
          (QuaternionGroup.a 0 : Q8) • (1 : SphereThree) =
            (1 : SphereThree) := by
        rw [smul_one_eq_q8ToSphere]
        apply Subtype.ext
        rw [q8ToSphere_coe]
        apply Quaternion.ext <;>
          simp [q8RealValue, q8IntValue, intQuaternionCast]
      refine ⟨(Path.refl _).cast rfl htarget, ?_⟩
      intro t n hn0 hnaxis
      change coordinate n (1 : ℍ) = 0
      fin_cases n <;> simp_all [coordinate]
    · have htarget :
          (QuaternionGroup.a 1 : Q8) • (1 : SphereThree) =
            iPoint (Real.pi / 2) := by
        rw [smul_one_eq_q8ToSphere]
        apply Subtype.ext
        rw [q8ToSphere_coe]
        apply Quaternion.ext <;>
          simp [q8RealValue, q8IntValue, intQuaternionCast, iPoint]
      refine ⟨(iArc (Real.pi / 2)).cast rfl htarget, ?_⟩
      intro t n hn0 hnaxis
      change coordinate n
        (iPoint (t.1 * (Real.pi / 2))).1 = 0
      fin_cases n <;>
        simp_all +decide [coordinate, iPoint]
    · have htarget :
          (QuaternionGroup.a 2 : Q8) • (1 : SphereThree) =
            iPoint Real.pi := by
        rw [smul_one_eq_q8ToSphere]
        apply Subtype.ext
        rw [q8ToSphere_coe]
        apply Quaternion.ext <;>
          simp [q8RealValue, q8IntValue, intQuaternionCast, iPoint]
      refine ⟨(iArc Real.pi).cast rfl htarget, ?_⟩
      intro t n hn0 hnaxis
      change coordinate n (iPoint (t.1 * Real.pi)).1 = 0
      fin_cases n <;>
        simp_all +decide [coordinate, iPoint]
    · have htarget :
          (QuaternionGroup.a 3 : Q8) • (1 : SphereThree) =
            iPoint (-Real.pi / 2) := by
        rw [smul_one_eq_q8ToSphere]
        apply Subtype.ext
        rw [q8ToSphere_coe]
        apply Quaternion.ext <;>
          simp [q8RealValue, q8IntValue, intQuaternionCast,
            iPoint, cos_neg_pi_div_two,
            sin_neg_pi_div_two]
      refine ⟨(iArc (-Real.pi / 2)).cast rfl htarget, ?_⟩
      intro t n hn0 hnaxis
      change coordinate n
        (iPoint (t.1 * (-Real.pi / 2))).1 = 0
      fin_cases n <;>
        simp_all +decide [coordinate, iPoint]
  · fin_cases k
    · have htarget :
          (QuaternionGroup.xa 0 : Q8) • (1 : SphereThree) =
            jPoint (Real.pi / 2) := by
        rw [smul_one_eq_q8ToSphere]
        apply Subtype.ext
        rw [q8ToSphere_coe]
        apply Quaternion.ext <;>
          simp [q8RealValue, q8IntValue, intQuaternionCast, jPoint]
      refine ⟨(jArc (Real.pi / 2)).cast rfl htarget, ?_⟩
      intro t n hn0 hnaxis
      change coordinate n
        (jPoint (t.1 * (Real.pi / 2))).1 = 0
      fin_cases n <;>
        simp_all +decide [coordinate, jPoint]
    · have htarget :
          (QuaternionGroup.xa 1 : Q8) • (1 : SphereThree) =
            kPoint (-Real.pi / 2) := by
        rw [smul_one_eq_q8ToSphere]
        apply Subtype.ext
        rw [q8ToSphere_coe]
        apply Quaternion.ext <;>
          simp [q8RealValue, q8IntValue, intQuaternionCast,
            kPoint, cos_neg_pi_div_two,
            sin_neg_pi_div_two]
      refine ⟨(kArc (-Real.pi / 2)).cast rfl htarget, ?_⟩
      intro t n hn0 hnaxis
      change coordinate n
        (kPoint (t.1 * (-Real.pi / 2))).1 = 0
      fin_cases n <;>
        simp_all +decide [coordinate, kPoint]
    · have htarget :
          (QuaternionGroup.xa 2 : Q8) • (1 : SphereThree) =
            jPoint (-Real.pi / 2) := by
        rw [smul_one_eq_q8ToSphere]
        apply Subtype.ext
        rw [q8ToSphere_coe]
        apply Quaternion.ext <;>
          simp [q8RealValue, q8IntValue, intQuaternionCast,
            jPoint, cos_neg_pi_div_two,
            sin_neg_pi_div_two]
      refine ⟨(jArc (-Real.pi / 2)).cast rfl htarget, ?_⟩
      intro t n hn0 hnaxis
      change coordinate n
        (jPoint (t.1 * (-Real.pi / 2))).1 = 0
      fin_cases n <;>
        simp_all +decide [coordinate, jPoint]
    · have htarget :
          (QuaternionGroup.xa 3 : Q8) • (1 : SphereThree) =
            kPoint (Real.pi / 2) := by
        rw [smul_one_eq_q8ToSphere]
        apply Subtype.ext
        rw [q8ToSphere_coe]
        apply Quaternion.ext <;>
          simp [q8RealValue, q8IntValue, intQuaternionCast, kPoint]
      refine ⟨(kArc (Real.pi / 2)).cast rfl htarget, ?_⟩
      intro t n hn0 hnaxis
      change coordinate n
        (kPoint (t.1 * (Real.pi / 2))).1 = 0
      fin_cases n <;>
        simp_all +decide [coordinate, kPoint]

/-- The preferred coordinate-circle path to a quaternion deck translate. -/
noncomputable def supportedPath (q : Q8) :
    Path (1 : SphereThree) (q • 1) :=
  (exists_supportedPath q).choose

theorem supportedPath_supported (q : Q8) :
    Supported q (supportedPath q) :=
  (exists_supportedPath q).choose_spec

/-- The coordinate axis occupied by a quaternion unit, ignoring its sign. -/
def unitAxis : Q8 → Fin 4
  | QuaternionGroup.a k =>
      if k = 0 ∨ k = 2 then 0 else 1
  | QuaternionGroup.xa k =>
      if k = 0 ∨ k = 2 then 2 else 3

/--
Left multiplication by `q` sends output coordinate `k` to this input
coordinate, up to sign.
-/
def leftPerm (q : Q8) (k : Fin 4) : Fin 4 :=
  if unitAxis q = 0 then k
  else if unitAxis q = 1 then ![1, 0, 3, 2] k
  else if unitAxis q = 2 then ![2, 3, 0, 1] k
  else ![3, 2, 1, 0] k

set_option maxHeartbeats 1000000 in
theorem coordinate_smul_eq_zero
    (q : Q8) (x : SphereThree) (k : Fin 4)
    (h : coordinate (leftPerm q k) x.1 = 0) :
    coordinate k (q • x).1 = 0 := by
  rcases q with q | q <;> fin_cases q <;> fin_cases k
  all_goals
    simp only [MulAction.compHom_smul_def]
    change coordinate _ ((q8ToSphere _).1 * x.1) = 0
    rw [q8ToSphere_coe]
    simp_all +decide [coordinate, leftPerm, q8RealValue,
      q8IntValue, intQuaternionCast,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]

/--
A coordinate omitted simultaneously by a preferred path, its translated
successor, and the preferred path to the product.
-/
def GoodCoordinate (q r : Q8) (k : Fin 4) : Prop :=
  k ≠ 0 ∧ k ≠ pathAxis q ∧
    leftPerm q k ≠ 0 ∧ leftPerm q k ≠ pathAxis r ∧
      k ≠ pathAxis (q * r)

private instance goodCoordinateDecidable (q r : Q8) (k : Fin 4) :
    Decidable (GoodCoordinate q r k) := by
  unfold GoodCoordinate
  infer_instance

private theorem exists_goodCoordinate_all :
    ∀ q r : Q8, ∃ k : Fin 4, GoodCoordinate q r k := by
  decide

private theorem exists_goodCoordinate (q r : Q8) :
    ∃ k : Fin 4, GoodCoordinate q r k :=
  exists_goodCoordinate_all q r

noncomputable def commonZeroCoordinate (q r : Q8) : Fin 4 :=
  (exists_goodCoordinate q r).choose

theorem commonZeroCoordinate_good (q r : Q8) :
    GoodCoordinate q r (commonZeroCoordinate q r) :=
  (exists_goodCoordinate q r).choose_spec

/-- A unit point with exactly coordinate `k` equal to zero. -/
noncomputable def hyperplanePoint (k : Fin 4) : SphereThree := by
  let q : ℍ :=
    if k = 0 then ⟨0, 1 / 3, 2 / 3, 2 / 3⟩
    else if k = 1 then ⟨1 / 3, 0, 2 / 3, 2 / 3⟩
    else if k = 2 then ⟨1 / 3, 2 / 3, 0, 2 / 3⟩
    else ⟨1 / 3, 2 / 3, 2 / 3, 0⟩
  refine ⟨q, ?_⟩
  rw [mem_sphere_zero_iff_norm, norm_eq_sqrt_real_inner,
    Quaternion.inner_self]
  fin_cases k <;>
    simp +decide [q, Quaternion.normSq_def'] <;>
    norm_num

theorem coordinate_hyperplanePoint_self (k : Fin 4) :
    coordinate k (hyperplanePoint k).1 = 0 := by
  fin_cases k <;>
    simp +decide [coordinate, hyperplanePoint]

theorem coordinate_hyperplanePoint_ne_zero
    {j k : Fin 4} (hjk : j ≠ k) :
    coordinate j (hyperplanePoint k).1 ≠ 0 := by
  fin_cases j <;> fin_cases k <;>
    simp_all +decide [coordinate, hyperplanePoint]

/-- The lift of a product of two preferred quotient loops. -/
noncomputable def supportedProductPath (q r : Q8) :
    Path (1 : SphereThree) ((q * r) • 1) :=
  (supportedPath q).trans <|
    (translatePath q (supportedPath r)).cast rfl
      (mul_smul q r (1 : SphereThree))

theorem supportedProductPath_commonZero (q r : Q8) (t) :
    coordinate (commonZeroCoordinate q r)
      (supportedProductPath q r t).1 = 0 := by
  have hg := commonZeroCoordinate_good q r
  rw [supportedProductPath, Path.trans_apply]
  split_ifs
  · exact supportedPath_supported q _ _
      hg.1 hg.2.1
  · apply coordinate_smul_eq_zero
    exact supportedPath_supported r _ _
      hg.2.2.1 hg.2.2.2.1

theorem supportedPath_product_commonZero (q r : Q8) (t) :
    coordinate (commonZeroCoordinate q r)
      (supportedPath (q * r) t).1 = 0 := by
  have hg := commonZeroCoordinate_good q r
  exact supportedPath_supported (q * r) _ _
    hg.1 hg.2.2.2.2

private theorem exists_extra_supported_all :
    ∀ (q : Q8) (k : Fin 4),
      k ≠ 0 → k ≠ pathAxis q →
        ∃ j : Fin 4, j ≠ k ∧ j ≠ 0 ∧ j ≠ pathAxis q := by
  decide

private theorem exists_extra_supported
    (q : Q8) (k : Fin 4)
    (hk0 : k ≠ 0) (hka : k ≠ pathAxis q) :
    ∃ j : Fin 4, j ≠ k ∧ j ≠ 0 ∧ j ≠ pathAxis q :=
  exists_extra_supported_all q k hk0 hka

private theorem exists_extra_translated_all :
    ∀ (q r : Q8) (k : Fin 4),
      leftPerm q k ≠ 0 →
      leftPerm q k ≠ pathAxis r →
        ∃ j : Fin 4,
          j ≠ k ∧ leftPerm q j ≠ 0 ∧
            leftPerm q j ≠ pathAxis r := by
  decide

private theorem exists_extra_translated
    (q r : Q8) (k : Fin 4)
    (hk0 : leftPerm q k ≠ 0)
    (hka : leftPerm q k ≠ pathAxis r) :
    ∃ j : Fin 4,
      j ≠ k ∧ leftPerm q j ≠ 0 ∧
        leftPerm q j ≠ pathAxis r :=
  exists_extra_translated_all q r k hk0 hka

private theorem supportedPath_ne_hyperplanePoint
    (q : Q8) (k : Fin 4)
    (hk0 : k ≠ 0) (hka : k ≠ pathAxis q) (t) :
    supportedPath q t ≠ hyperplanePoint k := by
  obtain ⟨j, hjk, hj0, hja⟩ :=
    exists_extra_supported q k hk0 hka
  intro h
  apply coordinate_hyperplanePoint_ne_zero hjk
  rw [← h]
  exact supportedPath_supported q t j hj0 hja

private theorem translated_supportedPath_ne_hyperplanePoint
    (q r : Q8) (k : Fin 4)
    (hk0 : leftPerm q k ≠ 0)
    (hka : leftPerm q k ≠ pathAxis r) (t) :
    translatePath q (supportedPath r) t ≠ hyperplanePoint k := by
  obtain ⟨j, hjk, hj0, hja⟩ :=
    exists_extra_translated q r k hk0 hka
  intro h
  apply coordinate_hyperplanePoint_ne_zero hjk
  rw [← h]
  apply coordinate_smul_eq_zero
  exact supportedPath_supported r t _ hj0 hja

theorem supportedProductPath_ne_hyperplanePoint
    (q r : Q8) (t) :
    supportedProductPath q r t ≠
      hyperplanePoint (commonZeroCoordinate q r) := by
  have hg := commonZeroCoordinate_good q r
  intro h
  have hm :
      supportedProductPath q r t ∈
        Set.range (supportedProductPath q r) :=
    Set.mem_range_self t
  rw [supportedProductPath, Path.trans_range] at hm
  rcases hm with ⟨u, hu⟩ | ⟨u, hu⟩
  · exact supportedPath_ne_hyperplanePoint q _
      hg.1 hg.2.1 u (hu.trans h)
  · exact translated_supportedPath_ne_hyperplanePoint q r _
      hg.2.2.1 hg.2.2.2.1 u (by simpa using hu.trans h)

theorem supportedPath_product_ne_hyperplanePoint
    (q r : Q8) (t) :
    supportedPath (q * r) t ≠
      hyperplanePoint (commonZeroCoordinate q r) := by
  have hg := commonZeroCoordinate_good q r
  exact supportedPath_ne_hyperplanePoint (q * r) _
    hg.1 hg.2.2.2.2 t

end
end Submission.QuaternionPaths
