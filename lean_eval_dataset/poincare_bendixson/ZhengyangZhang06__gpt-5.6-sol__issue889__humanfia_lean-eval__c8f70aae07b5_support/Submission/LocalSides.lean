import Submission.JordanBoundary
import Submission.OrbitArc

open Function Metric Set Topology
open scoped Convex

open LeanEval.Dynamics

namespace Submission.LocalSides

noncomputable section

/-- A small offset from the open part of a transverse segment.  The offset
vanishes at the endpoints and is always shorter than the distance to `O`.
This gives a canonical corridor on either side of a closing segment. -/
def sideCorridor (O : Set Plane) (v base : Plane)
    (a b sign u : ℝ) : Plane :=
  let f := (u - a) * (b - u)
  let d := infDist (Transversal.sectionPoint v base u) O
  Transversal.sectionPoint v base u +
    (sign * d * f /
      (2 * (1 + |f|) * (‖v‖ + 1))) • v

theorem continuous_sideCorridor (O : Set Plane) (v base : Plane)
    (a b sign : ℝ) :
    Continuous (sideCorridor O v base a b sign) := by
  have hs : Continuous (Transversal.sectionPoint v base) :=
    Transversal.continuous_sectionPoint v base
  have hf : Continuous (fun u : ℝ => (u - a) * (b - u)) := by
    fun_prop
  have hd : Continuous (fun u : ℝ =>
      infDist (Transversal.sectionPoint v base u) O) :=
    (continuous_infDist_pt O).comp hs
  have hnum : Continuous (fun u : ℝ =>
      sign * infDist (Transversal.sectionPoint v base u) O *
        ((u - a) * (b - u))) :=
    (continuous_const.mul hd).mul hf
  have hden : Continuous (fun u : ℝ =>
      2 * (1 + |(u - a) * (b - u)|) * (‖v‖ + 1)) :=
    (continuous_const.mul (continuous_const.add hf.abs)).mul
      continuous_const
  have hcoef : Continuous (fun u : ℝ =>
      sign * infDist (Transversal.sectionPoint v base u) O *
          ((u - a) * (b - u)) /
        (2 * (1 + |(u - a) * (b - u)|) * (‖v‖ + 1))) :=
    hnum.div hden (fun _ ↦ by positivity)
  change Continuous (fun u : ℝ =>
    Transversal.sectionPoint v base u +
      (sign * infDist (Transversal.sectionPoint v base u) O *
          ((u - a) * (b - u)) /
        (2 * (1 + |(u - a) * (b - u)|) *
          (‖v‖ + 1))) • v)
  exact
    hs.add
      (hcoef.smul
        (continuous_const : Continuous (fun _ : ℝ ↦ v)))

@[simp]
theorem sideCorridor_left (O : Set Plane) (v base : Plane)
    (a b sign : ℝ) :
    sideCorridor O v base a b sign a =
      Transversal.sectionPoint v base a := by
  simp [sideCorridor]

@[simp]
theorem sideCorridor_right (O : Set Plane) (v base : Plane)
    (a b sign : ℝ) :
    sideCorridor O v base a b sign b =
      Transversal.sectionPoint v base b := by
  simp [sideCorridor]

theorem transverseValue_sideCorridor
    (O : Set Plane) {v base : Plane} (hv : v ≠ 0)
    (a b sign u : ℝ) :
    Transversal.transverseValue v base
        (sideCorridor O v base a b sign u) =
      sign * infDist (Transversal.sectionPoint v base u) O *
          ((u - a) * (b - u)) /
        (2 * (1 + |(u - a) * (b - u)|) * (‖v‖ + 1)) := by
  exact Transversal.transverseValue_offset_sectionPoint hv _ _

theorem sideCorridor_ne_section_of_mem_Ioo
    (O : Set Plane) {v base : Plane} (hv : v ≠ 0)
    {a b sign u : ℝ} (hsign : sign ≠ 0) (hu : u ∈ Ioo a b)
    (huO : Transversal.sectionPoint v base u ∉ O)
    (hOclosed : IsClosed O) (hOne : O.Nonempty) :
    sideCorridor O v base a b sign u ≠
      Transversal.sectionPoint v base u := by
  intro heq
  have hd :
      0 < infDist (Transversal.sectionPoint v base u) O :=
    (hOclosed.notMem_iff_infDist_pos hOne).mp huO
  have hvalue :=
    congrArg (Transversal.transverseValue v base) heq
  rw [transverseValue_sideCorridor O hv,
    Transversal.transverseValue_sectionPoint hv] at hvalue
  have hf : 0 < (u - a) * (b - u) :=
    mul_pos (sub_pos.mpr hu.1) (sub_pos.mpr hu.2)
  have hden :
      0 <
        2 * (1 + |(u - a) * (b - u)|) * (‖v‖ + 1) := by
    positivity
  exact
    (div_ne_zero
      (mul_ne_zero (mul_ne_zero hsign hd.ne') hf.ne')
      hden.ne') hvalue

theorem sideCorridor_not_mem_of_mem_Ioo
    (O : Set Plane) {v base : Plane} (hv : v ≠ 0)
    {a b sign u : ℝ} (hsign : |sign| ≤ 1)
    (hu : u ∈ Ioo a b)
    (huO : Transversal.sectionPoint v base u ∉ O)
    (hOclosed : IsClosed O) (hOne : O.Nonempty) :
    sideCorridor O v base a b sign u ∉ O := by
  let p := Transversal.sectionPoint v base u
  let f := (u - a) * (b - u)
  let d := infDist p O
  let c :=
    sign * d * f /
      (2 * (1 + |f|) * (‖v‖ + 1))
  have hd : 0 < d :=
    (hOclosed.notMem_iff_infDist_pos hOne).mp huO
  have hf : 0 < f := by
    dsimp [f]
    exact mul_pos (sub_pos.mpr hu.1) (sub_pos.mpr hu.2)
  have hnorm : 0 ≤ ‖v‖ := norm_nonneg _
  have hcabs :
      |c| =
        |sign| * d * f /
          (2 * (1 + f) * (‖v‖ + 1)) := by
    dsimp [c]
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hd, abs_of_pos hf]
    rw [abs_of_pos (by positivity :
      0 < 2 * (1 + f) * (‖v‖ + 1))]
  have hfrac :
      |sign| * d * f * ‖v‖ <
        d * (2 * (1 + f) * (‖v‖ + 1)) := by
    have hleft :
        |sign| * d * f * ‖v‖ ≤ d * f * ‖v‖ := by
      calc
        |sign| * d * f * ‖v‖ =
            |sign| * (d * f * ‖v‖) := by ring
        _ ≤ 1 * (d * f * ‖v‖) :=
          mul_le_mul_of_nonneg_right hsign (by positivity)
        _ = d * f * ‖v‖ := by ring
    have hright :
        d * f * ‖v‖ <
          d * (2 * (1 + f) * (‖v‖ + 1)) := by
      have hpos : 0 < d * (2 + 2 * f + 2 * ‖v‖ + f * ‖v‖) := by
        positivity
      nlinarith
    exact hleft.trans_lt hright
  have hden :
      0 < 2 * (1 + f) * (‖v‖ + 1) := by positivity
  have hdist : dist p (sideCorridor O v base a b sign u) < d := by
    rw [dist_comm]
    rw [show sideCorridor O v base a b sign u = p + c • v by rfl]
    rw [Transversal.dist_offset_sectionPoint]
    rw [hcabs]
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ hden).2 hfrac
  intro hmem
  exact (not_le_of_gt hdist) (infDist_le_dist_of_mem hmem)

/-- At an interior point of a transverse closing segment, a ball which
avoids the other compact arc sees exactly the affine transverse line. -/
theorem exists_ball_union_segment_iff_transverseValue_eq_zero
    {v base : Plane} (hv : v ≠ 0) {a m b : ℝ}
    (ham : a < m) (hmb : m < b)
    {O : Set Plane} (hOclosed : IsClosed O)
    (hmO : Transversal.sectionPoint v base m ∉ O) :
    ∃ R : ℝ, 0 < R ∧
      ∀ z ∈ ball (Transversal.sectionPoint v base m) R,
        (z ∈ O ∪
            [Transversal.sectionPoint v base a -[ℝ]
              Transversal.sectionPoint v base b] ↔
          Transversal.transverseValue v base z = 0) := by
  let pm := Transversal.sectionPoint v base m
  have hOcompl : Oᶜ ∈ 𝓝 pm :=
    hOclosed.isOpen_compl.mem_nhds hmO
  obtain ⟨r₀, hr₀, hr₀sub⟩ :=
    Metric.mem_nhds_iff.mp hOcompl
  let d : ℝ := min (m - a) (b - m)
  have hd : 0 < d := lt_min (sub_pos.mpr ham) (sub_pos.mpr hmb)
  let r₁ : ℝ := ‖v‖ * d
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hr₁ : 0 < r₁ := mul_pos hvnorm hd
  let R : ℝ := min r₀ r₁
  have hR : 0 < R := lt_min hr₀ hr₁
  refine ⟨R, hR, ?_⟩
  intro z hzBall
  constructor
  · intro hz
    rcases hz with hzO | hzSegment
    · have hzSmall : z ∈ ball pm r₀ := by
        change dist z pm < r₀
        change dist z pm < R at hzBall
        exact hzBall.trans_le (min_le_left _ _)
      exact (hr₀sub hzSmall) hzO |>.elim
    · exact
        OrbitArc.transverseValue_segment_eq_zero
          (Transversal.transverseValue_sectionPoint hv a)
          (Transversal.transverseValue_sectionPoint hv b)
          hzSegment
  · intro hzZero
    apply Or.inr
    let u := Transversal.sectionValue v base z
    have hzu :
        Transversal.sectionPoint v base u = z :=
      Transversal.sectionPoint_sectionValue hv hzZero
    have hdist :
        ‖v‖ * |u - m| < ‖v‖ * d := by
      calc
        ‖v‖ * |u - m| =
            dist (Transversal.sectionPoint v base u) pm := by
          rw [Transversal.dist_sectionPoint]
        _ = dist z pm := by rw [hzu]
        _ < R := hzBall
        _ ≤ r₁ := min_le_right _ _
        _ = ‖v‖ * d := rfl
    have habs : |u - m| < d :=
      lt_of_mul_lt_mul_left hdist hvnorm.le
    have hleft : |u - m| < m - a :=
      habs.trans_le (min_le_left _ _)
    have hright : |u - m| < b - m :=
      habs.trans_le (min_le_right _ _)
    have hu : u ∈ Icc a b := by
      constructor
      · linarith [neg_lt_of_abs_lt hleft]
      · linarith [lt_of_abs_lt hright]
    rw [← hzu]
    exact Transversal.sectionPoint_mem_segment (ham.trans hmb) hu

/-- A planar Jordan curve has points in two distinct complementary
components. -/
theorem exists_points_distinct_components
    (r : C(Circle, Plane)) (hinj : Injective r) :
    ∃ x ∈ (range r)ᶜ, ∃ y ∈ (range r)ᶜ,
      connectedComponentIn (range r)ᶜ x ≠
        connectedComponentIn (range r)ᶜ y := by
  let C := ConnectedComponents ((range r)ᶜ : Set Plane)
  have hcard : Nat.card C = 2 := by
    let rs :
        Metric.sphere (0 : Plane) 1 → Plane :=
      r ∘ Transport.sphereEquiv
    have hrange : range rs = range r :=
      Transport.sphereEquiv.surjective.range_comp r
    have h :=
      JordanCurve.jordan_curve rs
        (r.continuous.comp Transport.sphereEquiv.continuous)
        (hinj.comp Transport.sphereEquiv.injective)
    rw [hrange] at h
    exact h
  letI : Finite C :=
    Finite.of_not_infinite (by
      intro hInfinite
      letI : Infinite C := hInfinite
      have hzero : Nat.card C = 0 :=
        Nat.card_eq_zero_of_infinite
      omega)
  letI : Nontrivial C :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨c, d, hcd⟩ := exists_pair_ne C
  obtain ⟨x, hxc⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨y, hyd⟩ := ConnectedComponents.surjective_coe d
  have hcomponent (u v : ((range r)ᶜ : Set Plane)) :
      (u : ConnectedComponents ((range r)ᶜ : Set Plane)) = v ↔
        connectedComponentIn (range r)ᶜ u =
          connectedComponentIn (range r)ᶜ v := by
    rw [ConnectedComponents.coe_eq_coe,
      connectedComponentIn_eq_image u.2,
      connectedComponentIn_eq_image v.2]
    constructor
    · exact fun h ↦ congrArg (fun t ↦ Subtype.val '' t) h
    · intro h
      exact Set.image_injective.mpr Subtype.val_injective h
  refine ⟨x, x.2, y, y.2, ?_⟩
  intro hxy
  apply hcd
  have hxy' :
      (x : ConnectedComponents ((range r)ᶜ : Set Plane)) = y :=
    (hcomponent x y).2 hxy
  exact hxc.symm.trans (hxy'.trans hyd)

/-- Two points in a ball on the same side of a locally straight Jordan
curve belong to the same complementary component. -/
theorem component_eq_of_same_side
    (r : C(Circle, Plane)) (q : Plane →L[ℝ] ℝ)
    {p : Plane} {R : ℝ}
    (hlocal : ∀ z ∈ ball p R,
      (z ∈ range r ↔ q (z - p) = 0))
    {x y : Plane}
    (_hx : x ∈ (range r)ᶜ) (_hy : y ∈ (range r)ᶜ)
    (hxBall : x ∈ ball p R) (hyBall : y ∈ ball p R)
    (hsign :
      (0 < q (x - p) ∧ 0 < q (y - p)) ∨
        (q (x - p) < 0 ∧ q (y - p) < 0)) :
    connectedComponentIn (range r)ᶜ x =
      connectedComponentIn (range r)ᶜ y := by
  have hqLinear : IsLinearMap ℝ (q : Plane → ℝ) :=
    ⟨q.map_add, q.map_smul⟩
  rcases hsign with hpos | hneg
  · let S : Set Plane := ball p R ∩ {z | q p < q z}
    have hSconvex : Convex ℝ S :=
      (convex_ball p R).inter
        (convex_halfSpace_gt hqLinear (q p))
    have hSsub : S ⊆ (range r)ᶜ := by
      intro z hz hzRange
      have hzero := (hlocal z hz.1).1 hzRange
      have hzPos : q p < q z := hz.2
      exact hzPos.ne (sub_eq_zero.mp (by simpa only [map_sub] using hzero)).symm
    have hxS : x ∈ S := by
      refine ⟨hxBall, ?_⟩
      change q p < q x
      simpa only [map_sub, sub_pos] using hpos.1
    have hyS : y ∈ S := by
      refine ⟨hyBall, ?_⟩
      change q p < q y
      simpa only [map_sub, sub_pos] using hpos.2
    apply connectedComponentIn_eq
    exact
      hSconvex.isPreconnected
        |>.subset_connectedComponentIn hxS hSsub hyS

  · let S : Set Plane := ball p R ∩ {z | q z < q p}
    have hSconvex : Convex ℝ S :=
      (convex_ball p R).inter
        (convex_halfSpace_lt hqLinear (q p))
    have hSsub : S ⊆ (range r)ᶜ := by
      intro z hz hzRange
      have hzero := (hlocal z hz.1).1 hzRange
      have hzNeg : q z < q p := hz.2
      exact hzNeg.ne (sub_eq_zero.mp (by simpa only [map_sub] using hzero))
    have hxS : x ∈ S := by
      refine ⟨hxBall, ?_⟩
      change q x < q p
      simpa only [map_sub, sub_neg] using hneg.1
    have hyS : y ∈ S := by
      refine ⟨hyBall, ?_⟩
      change q y < q p
      simpa only [map_sub, sub_neg] using hneg.2
    apply connectedComponentIn_eq
    exact
      hSconvex.isPreconnected
        |>.subset_connectedComponentIn hxS hSsub hyS

/-- Distinct complementary components approaching a locally straight point
approach it from opposite sides of the local line. -/
theorem exists_opposite_side_points
    (r : C(Circle, Plane)) (hinj : Injective r)
    (q : Plane →L[ℝ] ℝ) {p : Plane} {R : ℝ} (hR : 0 < R)
    (hlocal : ∀ z ∈ ball p R,
      (z ∈ range r ↔ q (z - p) = 0))
    {x y : Plane}
    (hx : x ∈ (range r)ᶜ) (hy : y ∈ (range r)ᶜ)
    (hcomponents :
      connectedComponentIn (range r)ᶜ x ≠
        connectedComponentIn (range r)ᶜ y) :
    ∃ u ∈ connectedComponentIn (range r)ᶜ x,
      u ∈ ball p R ∧
      ∃ v ∈ connectedComponentIn (range r)ᶜ y,
        v ∈ ball p R ∧
        ((q (u - p) < 0 ∧ 0 < q (v - p)) ∨
          (0 < q (u - p) ∧ q (v - p) < 0)) := by
  have hpRange : p ∈ range r := by
    apply (hlocal p (mem_ball_self hR)).2
    simp
  have hpFrontX :
      p ∈ frontier (connectedComponentIn (range r)ᶜ x) := by
    rw [JordanBoundary.frontier_component_eq_range_plane r hinj hx]
    exact hpRange
  have hpFrontY :
      p ∈ frontier (connectedComponentIn (range r)ᶜ y) := by
    rw [JordanBoundary.frontier_component_eq_range_plane r hinj hy]
    exact hpRange
  obtain ⟨u, huBall, huComp⟩ :=
    mem_closure_iff.mp hpFrontX.1
      (ball p R) isOpen_ball (mem_ball_self hR)
  obtain ⟨v, hvBall, hvComp⟩ :=
    mem_closure_iff.mp hpFrontY.1
      (ball p R) isOpen_ball (mem_ball_self hR)
  have huCompl :
      u ∈ (range r)ᶜ :=
    connectedComponentIn_subset (range r)ᶜ x huComp
  have hvCompl :
      v ∈ (range r)ᶜ :=
    connectedComponentIn_subset (range r)ᶜ y hvComp
  have huNe : q (u - p) ≠ 0 :=
    fun huZero ↦ huCompl ((hlocal u huBall).2 huZero)
  have hvNe : q (v - p) ≠ 0 :=
    fun hvZero ↦ hvCompl ((hlocal v hvBall).2 hvZero)
  refine ⟨u, huComp, huBall, v, hvComp, hvBall, ?_⟩
  rcases lt_or_gt_of_ne huNe with huNeg | huPos
  · rcases lt_or_gt_of_ne hvNe with hvNeg | hvPos
    · have huv :=
        component_eq_of_same_side r q hlocal
          huCompl hvCompl huBall hvBall
            (Or.inr ⟨huNeg, hvNeg⟩)
      exact
        (hcomponents
          ((connectedComponentIn_eq huComp).trans
            (huv.trans (connectedComponentIn_eq hvComp).symm))).elim
    · exact Or.inl ⟨huNeg, hvPos⟩
  · rcases lt_or_gt_of_ne hvNe with hvNeg | hvPos
    · exact Or.inr ⟨huPos, hvNeg⟩
    · have huv :=
        component_eq_of_same_side r q hlocal
          huCompl hvCompl huBall hvBall
            (Or.inl ⟨huPos, hvPos⟩)
      exact
        (hcomponents
          ((connectedComponentIn_eq huComp).trans
            (huv.trans (connectedComponentIn_eq hvComp).symm))).elim

/-- Points on opposite sides of a locally straight Jordan curve belong to
distinct complementary components. -/
theorem components_ne_of_opposite_side
    (r : C(Circle, Plane)) (hinj : Injective r)
    (q : Plane →L[ℝ] ℝ) {p : Plane} {R : ℝ} (hR : 0 < R)
    (hlocal : ∀ z ∈ ball p R,
      (z ∈ range r ↔ q (z - p) = 0))
    {u v : Plane}
    (hu : u ∈ (range r)ᶜ) (hv : v ∈ (range r)ᶜ)
    (huBall : u ∈ ball p R) (hvBall : v ∈ ball p R)
    (huPos : 0 < q (u - p)) (hvNeg : q (v - p) < 0) :
    connectedComponentIn (range r)ᶜ u ≠
      connectedComponentIn (range r)ᶜ v := by
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    exists_points_distinct_components r hinj
  obtain ⟨xSide, hxSide, hxSideBall, ySide, hySide, hySideBall,
      hsides⟩ :=
    exists_opposite_side_points r hinj q hR hlocal hx hy hxy
  have hxSideCompl :
      xSide ∈ (range r)ᶜ :=
    connectedComponentIn_subset (range r)ᶜ x hxSide
  have hySideCompl :
      ySide ∈ (range r)ᶜ :=
    connectedComponentIn_subset (range r)ᶜ y hySide
  intro huv
  rcases hsides with hxnyn | hxpyp
  · have huY :
        connectedComponentIn (range r)ᶜ u =
          connectedComponentIn (range r)ᶜ ySide :=
      component_eq_of_same_side r q hlocal
        hu hySideCompl huBall hySideBall
          (Or.inl ⟨huPos, hxnyn.2⟩)
    have hvX :
        connectedComponentIn (range r)ᶜ v =
          connectedComponentIn (range r)ᶜ xSide :=
      component_eq_of_same_side r q hlocal
        hv hxSideCompl hvBall hxSideBall
          (Or.inr ⟨hvNeg, hxnyn.1⟩)
    apply hxy
    exact
      (connectedComponentIn_eq hxSide).trans
        (hvX.symm.trans (huv.symm.trans
          (huY.trans (connectedComponentIn_eq hySide).symm)))
  · have huX :
        connectedComponentIn (range r)ᶜ u =
          connectedComponentIn (range r)ᶜ xSide :=
      component_eq_of_same_side r q hlocal
        hu hxSideCompl huBall hxSideBall
          (Or.inl ⟨huPos, hxpyp.1⟩)
    have hvY :
        connectedComponentIn (range r)ᶜ v =
          connectedComponentIn (range r)ᶜ ySide :=
      component_eq_of_same_side r q hlocal
        hv hySideCompl hvBall hySideBall
          (Or.inr ⟨hvNeg, hxpyp.2⟩)
    apply hxy
    exact
      (connectedComponentIn_eq hxSide).trans
      (huX.symm.trans (huv.trans
          (hvY.trans (connectedComponentIn_eq hySide).symm)))

/-- Along an open straight part of a Jordan curve, the choice of
complementary component made by a side of the affine line is independent of
the point on that part. -/
theorem component_eq_of_same_side_along_segment
    (r : C(Circle, Plane)) (O : Set Plane)
    {v base : Plane} (hv : v ≠ 0)
    {a b sign : ℝ} (hab : a < b)
    (hsign : sign = 1 ∨ sign = -1)
    (hOclosed : IsClosed O) (hOne : O.Nonempty)
    (hOdisj : ∀ u ∈ Ioo a b,
      Transversal.sectionPoint v base u ∉ O)
    (hrange : range r ⊆
      O ∪ {z |
        Transversal.transverseValue v base z = 0})
    {Ra Rb : ℝ} (hRa : 0 < Ra) (hRb : 0 < Rb)
    (hlocalA : ∀ z ∈ ball (Transversal.sectionPoint v base a) Ra,
      (z ∈ range r ↔
        Transversal.transverseFunctional v
          (z - Transversal.sectionPoint v base a) = 0))
    (hlocalB : ∀ z ∈ ball (Transversal.sectionPoint v base b) Rb,
      (z ∈ range r ↔
        Transversal.transverseFunctional v
          (z - Transversal.sectionPoint v base b) = 0))
    {x y : Plane}
    (hx : x ∈ (range r)ᶜ) (hy : y ∈ (range r)ᶜ)
    (hxBall : x ∈ ball (Transversal.sectionPoint v base a) Ra)
    (hyBall : y ∈ ball (Transversal.sectionPoint v base b) Rb)
    (hxSign : 0 <
      sign * Transversal.transverseFunctional v
        (x - Transversal.sectionPoint v base a))
    (hySign : 0 <
      sign * Transversal.transverseFunctional v
        (y - Transversal.sectionPoint v base b)) :
    connectedComponentIn (range r)ᶜ x =
      connectedComponentIn (range r)ᶜ y := by
  let c : ℝ → Plane :=
    sideCorridor O v base a b sign
  let S : Set Plane := c '' Ioo a b
  have hccont : Continuous c :=
    continuous_sideCorridor O v base a b sign
  have hsignAbs : |sign| ≤ 1 := by
    rcases hsign with rfl | rfl <;> norm_num
  have hsignNe : sign ≠ 0 := by
    rcases hsign with rfl | rfl <;> norm_num
  have hSsub : S ⊆ (range r)ᶜ := by
    rintro z ⟨u, hu, rfl⟩ hzRange
    rcases hrange hzRange with hzO | hzLine
    · exact
        sideCorridor_not_mem_of_mem_Ioo O hv hsignAbs hu
          (hOdisj u hu) hOclosed hOne hzO
    · have hzNe :
          Transversal.transverseValue v base
              (sideCorridor O v base a b sign u) ≠ 0 := by
        rw [transverseValue_sideCorridor O hv]
        have hd :
            0 < infDist (Transversal.sectionPoint v base u) O :=
          (hOclosed.notMem_iff_infDist_pos hOne).mp
            (hOdisj u hu)
        have hf : 0 < (u - a) * (b - u) :=
          mul_pos (sub_pos.mpr hu.1) (sub_pos.mpr hu.2)
        exact
          div_ne_zero
            (mul_ne_zero (mul_ne_zero hsignNe hd.ne') hf.ne')
            (by positivity)
      exact hzNe hzLine
  have hSpre : IsPreconnected S := by
    exact
      isPreconnected_Ioo.image c
        (hccont.continuousOn)
  have haClosure : Transversal.sectionPoint v base a ∈ closure S := by
    have ha : a ∈ closure (Ioo a b) := by
      rw [closure_Ioo hab.ne]
      exact ⟨le_rfl, hab.le⟩
    have hmap :
        c a ∈ closure S :=
      map_mem_closure hccont ha
        (fun u hu ↦ ⟨u, hu, rfl⟩)
    simpa only [c, sideCorridor_left] using hmap
  have hbClosure : Transversal.sectionPoint v base b ∈ closure S := by
    have hb : b ∈ closure (Ioo a b) := by
      rw [closure_Ioo hab.ne]
      exact ⟨hab.le, le_rfl⟩
    have hmap :
        c b ∈ closure S :=
      map_mem_closure hccont hb
        (fun u hu ↦ ⟨u, hu, rfl⟩)
    simpa only [c, sideCorridor_right] using hmap
  obtain ⟨xa, hxaBall, hxaS⟩ :=
    mem_closure_iff.mp haClosure
      (ball (Transversal.sectionPoint v base a) Ra)
      isOpen_ball (mem_ball_self hRa)
  obtain ⟨yb, hybBall, hybS⟩ :=
    mem_closure_iff.mp hbClosure
      (ball (Transversal.sectionPoint v base b) Rb)
      isOpen_ball (mem_ball_self hRb)
  have hxaSmem : xa ∈ S := hxaS
  have hybSmem : yb ∈ S := hybS
  obtain ⟨ua, hua, hxa⟩ := hxaS
  obtain ⟨ub, hub, hyb⟩ := hybS
  have hxaCompl : xa ∈ (range r)ᶜ := hSsub hxaSmem
  have hybCompl : yb ∈ (range r)ᶜ := hSsub hybSmem
  have hside (u : ℝ) (hu : u ∈ Ioo a b) :
      0 <
        sign *
          Transversal.transverseValue v base
            (sideCorridor O v base a b sign u) := by
    rw [transverseValue_sideCorridor O hv]
    have hd :
        0 < infDist (Transversal.sectionPoint v base u) O :=
      (hOclosed.notMem_iff_infDist_pos hOne).mp
        (hOdisj u hu)
    have hf : 0 < (u - a) * (b - u) :=
      mul_pos (sub_pos.mpr hu.1) (sub_pos.mpr hu.2)
    rcases hsign with rfl | rfl
    · positivity
    · have hden :
          0 <
            2 * (1 + |(u - a) * (b - u)|) *
              (‖v‖ + 1) := by
          positivity
      have hnum :
          (-1 : ℝ) *
              infDist (Transversal.sectionPoint v base u) O *
              ((u - a) * (b - u)) < 0 :=
        mul_neg_of_neg_of_pos
          (mul_neg_of_neg_of_pos (by norm_num) hd) hf
      have hquot :
          (-1 : ℝ) *
                infDist (Transversal.sectionPoint v base u) O *
                ((u - a) * (b - u)) /
              (2 * (1 + |(u - a) * (b - u)|) *
                (‖v‖ + 1)) < 0 :=
        div_neg_of_neg_of_pos hnum hden
      exact mul_pos_of_neg_of_neg (by norm_num) hquot
  have hxaSign :
      0 <
        sign * Transversal.transverseFunctional v
          (xa - Transversal.sectionPoint v base a) := by
    rw [Transversal.transverseValue_recenter_sectionPoint hv]
    rw [← hxa]
    exact hside ua hua
  have hybSign :
      0 <
        sign * Transversal.transverseFunctional v
          (yb - Transversal.sectionPoint v base b) := by
    rw [Transversal.transverseValue_recenter_sectionPoint hv]
    rw [← hyb]
    exact hside ub hub
  have hxXa :
      connectedComponentIn (range r)ᶜ x =
        connectedComponentIn (range r)ᶜ xa := by
    rcases hsign with rfl | rfl
    · apply component_eq_of_same_side r (Transversal.transverseFunctional v)
        hlocalA hx hxaCompl hxBall hxaBall
      exact Or.inl ⟨by simpa using hxSign, by simpa using hxaSign⟩
    · apply component_eq_of_same_side r (Transversal.transverseFunctional v)
        hlocalA hx hxaCompl hxBall hxaBall
      exact Or.inr ⟨by linarith, by linarith⟩
  have hxaYb :
      connectedComponentIn (range r)ᶜ xa =
        connectedComponentIn (range r)ᶜ yb := by
    apply connectedComponentIn_eq
    exact
      hSpre.subset_connectedComponentIn hxaSmem hSsub hybSmem
  have hybY :
      connectedComponentIn (range r)ᶜ yb =
        connectedComponentIn (range r)ᶜ y := by
    rcases hsign with rfl | rfl
    · apply component_eq_of_same_side r (Transversal.transverseFunctional v)
        hlocalB hybCompl hy hybBall hyBall
      exact Or.inl ⟨by simpa using hybSign, by simpa using hySign⟩
    · apply component_eq_of_same_side r (Transversal.transverseFunctional v)
        hlocalB hybCompl hy hybBall hyBall
      exact Or.inr ⟨by linarith, by linarith⟩
  exact hxXa.trans (hxaYb.trans hybY)

theorem components_ne_of_opposite_side_along_segment
    (r : C(Circle, Plane)) (hinj : Injective r)
    (O : Set Plane) {v base : Plane} (hv : v ≠ 0)
    {a b : ℝ} (hab : a < b)
    (hOclosed : IsClosed O) (hOne : O.Nonempty)
    (hOdisj : ∀ u ∈ Ioo a b,
      Transversal.sectionPoint v base u ∉ O)
    (hrange : range r ⊆
      O ∪ {z |
        Transversal.transverseValue v base z = 0})
    {Ra Rb : ℝ} (hRa : 0 < Ra) (hRb : 0 < Rb)
    (hlocalA : ∀ z ∈ ball (Transversal.sectionPoint v base a) Ra,
      (z ∈ range r ↔
        Transversal.transverseFunctional v
          (z - Transversal.sectionPoint v base a) = 0))
    (hlocalB : ∀ z ∈ ball (Transversal.sectionPoint v base b) Rb,
      (z ∈ range r ↔
        Transversal.transverseFunctional v
          (z - Transversal.sectionPoint v base b) = 0))
    {x y : Plane}
    (hx : x ∈ (range r)ᶜ) (hy : y ∈ (range r)ᶜ)
    (hxBall : x ∈ ball (Transversal.sectionPoint v base a) Ra)
    (hyBall : y ∈ ball (Transversal.sectionPoint v base b) Rb)
    (hxPos : 0 <
      Transversal.transverseFunctional v
        (x - Transversal.sectionPoint v base a))
    (hyNeg :
      Transversal.transverseFunctional v
        (y - Transversal.sectionPoint v base b) < 0) :
    connectedComponentIn (range r)ᶜ x ≠
      connectedComponentIn (range r)ᶜ y := by
  let ε : ℝ := Rb / (2 * (‖v‖ + 1))
  let z :=
    Transversal.sectionPoint v base b + ε • v
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hzBall :
      z ∈ ball (Transversal.sectionPoint v base b) Rb := by
    rw [mem_ball]
    rw [show z =
      Transversal.sectionPoint v base b + ε • v by rfl]
    rw [Transversal.dist_offset_sectionPoint]
    have hnorm : 0 ≤ ‖v‖ := norm_nonneg _
    dsimp [ε]
    rw [abs_of_pos (by positivity :
      0 < Rb / (2 * (‖v‖ + 1)))]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity :
      0 < 2 * (‖v‖ + 1))).2
    exact mul_lt_mul_of_pos_left
      (by nlinarith [norm_nonneg v]) hRb
  have hzPos :
      0 <
        Transversal.transverseFunctional v
          (z - Transversal.sectionPoint v base b) := by
    rw [Transversal.transverseValue_recenter_sectionPoint hv]
    change 0 <
      Transversal.transverseValue v base
        (Transversal.sectionPoint v base b + ε • v)
    rw [Transversal.transverseValue_offset_sectionPoint hv]
    exact hε
  have hz : z ∈ (range r)ᶜ := by
    intro hzRange
    exact hzPos.ne'
      ((hlocalB z hzBall).mp hzRange)
  have hxz :
      connectedComponentIn (range r)ᶜ x =
        connectedComponentIn (range r)ᶜ z := by
    apply component_eq_of_same_side_along_segment
      r O hv hab (Or.inl rfl) hOclosed hOne hOdisj hrange
      hRa hRb hlocalA hlocalB hx hz hxBall hzBall
    · simpa using hxPos
    · simpa using hzPos
  intro hxy
  apply
    components_ne_of_opposite_side r hinj
      (Transversal.transverseFunctional v) hRb hlocalB
      hz hy hzBall hyBall hzPos hyNeg
  exact hxz.symm.trans hxy

theorem components_ne_of_opposite_side_along_segment_rev
    (r : C(Circle, Plane)) (hinj : Injective r)
    (O : Set Plane) {v base : Plane} (hv : v ≠ 0)
    {a b : ℝ} (hab : a < b)
    (hOclosed : IsClosed O) (hOne : O.Nonempty)
    (hOdisj : ∀ u ∈ Ioo a b,
      Transversal.sectionPoint v base u ∉ O)
    (hrange : range r ⊆
      O ∪ {z |
        Transversal.transverseValue v base z = 0})
    {Ra Rb : ℝ} (hRa : 0 < Ra) (hRb : 0 < Rb)
    (hlocalA : ∀ z ∈ ball (Transversal.sectionPoint v base a) Ra,
      (z ∈ range r ↔
        Transversal.transverseFunctional v
          (z - Transversal.sectionPoint v base a) = 0))
    (hlocalB : ∀ z ∈ ball (Transversal.sectionPoint v base b) Rb,
      (z ∈ range r ↔
        Transversal.transverseFunctional v
          (z - Transversal.sectionPoint v base b) = 0))
    {x y : Plane}
    (hx : x ∈ (range r)ᶜ) (hy : y ∈ (range r)ᶜ)
    (hxBall : x ∈ ball (Transversal.sectionPoint v base a) Ra)
    (hyBall : y ∈ ball (Transversal.sectionPoint v base b) Rb)
    (hxNeg :
      Transversal.transverseFunctional v
        (x - Transversal.sectionPoint v base a) < 0)
    (hyPos : 0 <
      Transversal.transverseFunctional v
        (y - Transversal.sectionPoint v base b)) :
    connectedComponentIn (range r)ᶜ x ≠
      connectedComponentIn (range r)ᶜ y := by
  let ε : ℝ := Ra / (2 * (‖v‖ + 1))
  let z :=
    Transversal.sectionPoint v base a + ε • v
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hzBall :
      z ∈ ball (Transversal.sectionPoint v base a) Ra := by
    rw [mem_ball]
    rw [show z =
      Transversal.sectionPoint v base a + ε • v by rfl]
    rw [Transversal.dist_offset_sectionPoint]
    have hnorm : 0 ≤ ‖v‖ := norm_nonneg _
    dsimp [ε]
    rw [abs_of_pos (by positivity :
      0 < Ra / (2 * (‖v‖ + 1)))]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity :
      0 < 2 * (‖v‖ + 1))).2
    exact mul_lt_mul_of_pos_left
      (by nlinarith [norm_nonneg v]) hRa
  have hzPos :
      0 <
        Transversal.transverseFunctional v
          (z - Transversal.sectionPoint v base a) := by
    rw [Transversal.transverseValue_recenter_sectionPoint hv]
    change 0 <
      Transversal.transverseValue v base
        (Transversal.sectionPoint v base a + ε • v)
    rw [Transversal.transverseValue_offset_sectionPoint hv]
    exact hε
  have hz : z ∈ (range r)ᶜ := by
    intro hzRange
    exact hzPos.ne'
      ((hlocalA z hzBall).mp hzRange)
  have hzy :
      connectedComponentIn (range r)ᶜ z =
        connectedComponentIn (range r)ᶜ y := by
    apply component_eq_of_same_side_along_segment
      r O hv hab (Or.inl rfl) hOclosed hOne hOdisj hrange
      hRa hRb hlocalA hlocalB hz hy hzBall hyBall
    · simpa using hzPos
    · simpa using hyPos
  intro hxy
  apply
    components_ne_of_opposite_side r hinj
      (Transversal.transverseFunctional v) hRa hlocalA
      hz hx hzBall hxBall hzPos hxNeg
  exact hzy.trans hxy.symm

/-- A preconnected subset of the curve complement cannot join the two local
sides. -/
theorem no_preconnected_set_crosses
    (r : C(Circle, Plane)) (hinj : Injective r)
    (q : Plane →L[ℝ] ℝ) {p : Plane} {R : ℝ} (hR : 0 < R)
    (hlocal : ∀ z ∈ ball p R,
      (z ∈ range r ↔ q (z - p) = 0))
    {u v : Plane}
    (hu : u ∈ (range r)ᶜ) (hv : v ∈ (range r)ᶜ)
    (huBall : u ∈ ball p R) (hvBall : v ∈ ball p R)
    (huPos : 0 < q (u - p)) (hvNeg : q (v - p) < 0)
    {S : Set Plane} (hS : IsPreconnected S)
    (huS : u ∈ S) (hvS : v ∈ S) (hSsub : S ⊆ (range r)ᶜ) :
    False := by
  apply
    components_ne_of_opposite_side r hinj q hR hlocal
      hu hv huBall hvBall huPos hvNeg
  apply connectedComponentIn_eq
  exact hS.subset_connectedComponentIn huS hSsub hvS

end

end Submission.LocalSides
