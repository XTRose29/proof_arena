import Submission.ReturnCrossing

open Function Metric Set Topology
open scoped Convex

open LeanEval.Dynamics

namespace Submission.EndpointBridge

noncomputable section

/-- Recentring the affine section translates its scalar coordinate. -/
theorem sectionPoint_recenter
    (v base : Plane) (a u : ℝ) :
    Transversal.sectionPoint v
        (Transversal.sectionPoint v base a) u =
      Transversal.sectionPoint v base (a + u) := by
  apply Transport.planeEquiv.injective
  simp only [Transversal.sectionPoint,
    Transport.planeEquiv.apply_symm_apply, map_add]
  push_cast
  ring

/-- Two points in a ball disjoint from a set lie in the same complementary
component. -/
theorem component_eq_of_mem_ball_disjoint
    {S : Set Plane} {p x y : Plane} {R : ℝ}
    (hsub : ball p R ⊆ Sᶜ)
    (hx : x ∈ ball p R) (hy : y ∈ ball p R) :
    connectedComponentIn Sᶜ x =
      connectedComponentIn Sᶜ y := by
  apply connectedComponentIn_eq
  exact
    (convex_ball p R).isPreconnected
      |>.subset_connectedComponentIn hx hsub hy

theorem sectionPoint_not_mem_segment_of_outside
    {v base : Plane} (hv : v ≠ 0) {A B u : ℝ}
    (hAB : A < B) (hu : u < A ∨ B < u) :
    Transversal.sectionPoint v base u ∉
      [Transversal.sectionPoint v base A -[ℝ]
        Transversal.sectionPoint v base B] := by
  intro hmem
  obtain ⟨w, hw, huw⟩ :=
    Transversal.exists_eq_sectionPoint_of_mem_segment hAB hmem
  have : u = w :=
    Transversal.sectionPoint_injective hv huw
  rcases hu with hu | hu <;> linarith [hw.1, hw.2]

theorem sectionPoint_mem_compl_of_outside
    (r : C(Circle, Plane)) (O : Set Plane)
    {v base : Plane} (hv : v ≠ 0) {A B u : ℝ}
    (hAB : A < B) (hu : u < A ∨ B < u)
    (huO : Transversal.sectionPoint v base u ∉ O)
    (hrange :
      range r =
        O ∪
          [Transversal.sectionPoint v base A -[ℝ]
            Transversal.sectionPoint v base B]) :
    Transversal.sectionPoint v base u ∈ (range r)ᶜ := by
  rw [hrange]
  rintro (huO' | huSegment)
  · exact huO huO'
  · exact
      sectionPoint_not_mem_segment_of_outside hv hAB hu huSegment

/-- A short longitudinal segment which points away from the orbit side at a
corner of a closing loop remains in one complementary component. -/
theorem component_eq_corner_vertical
    (r : C(Circle, Plane)) (O : Set Plane)
    {v base p : Plane} (hv : v ≠ 0)
    {u c sign R : ℝ} (hc : 0 < c)
    (hsign : sign = 1 ∨ sign = -1)
    (hball : ∀ d ∈ Icc (0 : ℝ) c,
      Transversal.sectionPoint v base u + (-sign * d) • v ∈
        ball p R)
    (hOside : ∀ z ∈ O, z ∈ ball p R →
      0 ≤ sign * Transversal.transverseValue v base z)
    (hrange :
      range r ⊆
        O ∪ {z | Transversal.transverseValue v base z = 0})
    (hline :
      Transversal.sectionPoint v base u ∈ (range r)ᶜ) :
    connectedComponentIn (range r)ᶜ
        (Transversal.sectionPoint v base u) =
      connectedComponentIn (range r)ᶜ
        (Transversal.sectionPoint v base u + (-sign * c) • v) := by
  let vertical : ℝ → Plane := fun d ↦
    Transversal.sectionPoint v base u + (-sign * d) • v
  let S : Set Plane := vertical '' Icc (0 : ℝ) c
  have hvertical : Continuous vertical := by
    fun_prop
  have hSpre : IsPreconnected S :=
    isPreconnected_Icc.image vertical hvertical.continuousOn
  have hSsub : S ⊆ (range r)ᶜ := by
    rintro z ⟨d, hd, rfl⟩ hzRange
    by_cases hd0 : d = 0
    · subst d
      apply hline
      simpa only [vertical, mul_zero, zero_smul, add_zero] using
        hzRange
    have hdpos : 0 < d := lt_of_le_of_ne hd.1 (Ne.symm hd0)
    rcases hrange hzRange with hzO | hzLine
    · have hwrong :=
        hOside (vertical d) hzO (hball d hd)
      dsimp only [vertical] at hwrong
      rw [Transversal.transverseValue_offset_sectionPoint hv] at hwrong
      rcases hsign with rfl | rfl <;> norm_num at hwrong <;> linarith
    · dsimp only [vertical] at hzLine
      change
        Transversal.transverseValue v base
          (Transversal.sectionPoint v base u + (-sign * d) • v) = 0
        at hzLine
      rw [Transversal.transverseValue_offset_sectionPoint hv] at hzLine
      rcases hsign with rfl | rfl <;> norm_num at hzLine <;> linarith
  apply connectedComponentIn_eq
  exact
    hSpre.subset_connectedComponentIn
      ⟨0, left_mem_Icc.mpr hc.le, by simp [vertical]⟩ hSsub
      ⟨c, right_mem_Icc.mpr hc.le, rfl⟩

/-- Uniformly small section and longitudinal offsets stay in a prescribed
corner ball. -/
theorem exists_offset_rectangle_in_ball
    {v base : Plane} {a R sign : ℝ} (hR : 0 < R)
    (hsign : sign = 1 ∨ sign = -1) :
    ∃ η : ℝ, 0 < η ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ u ∈ Icc (a - η) (a + η),
          Transversal.sectionPoint v base u + (-sign * c) • v ∈
            ball (Transversal.sectionPoint v base a) R := by
  let d : ℝ := R / (4 * (‖v‖ + 1))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  refine ⟨d, hd, d, hd, ?_⟩
  intro u hu
  have huAbs : |u - a| ≤ d := by
    rw [abs_le]
    constructor <;> linarith [hu.1, hu.2]
  have hsignAbs : |-sign| = 1 := by
    rcases hsign with rfl | rfl <;> norm_num
  rw [mem_ball]
  calc
    dist
        (Transversal.sectionPoint v base u + (-sign * d) • v)
        (Transversal.sectionPoint v base a) ≤
        dist
            (Transversal.sectionPoint v base u + (-sign * d) • v)
            (Transversal.sectionPoint v base u) +
          dist (Transversal.sectionPoint v base u)
            (Transversal.sectionPoint v base a) :=
      dist_triangle _ _ _
    _ = d * ‖v‖ + ‖v‖ * |u - a| := by
      rw [Transversal.dist_offset_sectionPoint,
        Transversal.dist_sectionPoint, abs_mul, hsignAbs,
        one_mul, abs_of_pos hd]
    _ ≤ d * ‖v‖ + ‖v‖ * d := by
      gcongr
    _ < R := by
      dsimp [d]
      have hv : 0 ≤ ‖v‖ := norm_nonneg v
      have hden : 0 < 4 * (‖v‖ + 1) := by positivity
      rw [show
        R / (4 * (‖v‖ + 1)) * ‖v‖ +
            ‖v‖ * (R / (4 * (‖v‖ + 1))) =
          (2 * R * ‖v‖) / (4 * (‖v‖ + 1)) by ring]
      apply (div_lt_iff₀ hden).2
      nlinarith

/-- A short constant longitudinal offset crosses a corner coordinate without
crossing a Jordan loop, provided the orbit part of the loop lies on the other
closed longitudinal side in the corner ball. -/
theorem component_eq_across_endpoint_offset
    (r : C(Circle, Plane)) (O : Set Plane)
    {v base : Plane} (hv : v ≠ 0)
    {left a right c sign R : ℝ}
    (hleft : left < a) (hright : a < right) (hc : 0 < c)
    (hsign : sign = 1 ∨ sign = -1)
    (hball :
      ∀ u ∈ Icc left right,
        Transversal.sectionPoint v base u + (-sign * c) • v ∈
          ball (Transversal.sectionPoint v base a) R)
    (hOside :
      ∀ z ∈ O,
        z ∈ ball (Transversal.sectionPoint v base a) R →
          0 ≤ sign * Transversal.transverseValue v base z)
    (hrange :
      range r ⊆
        O ∪ {z | Transversal.transverseValue v base z = 0}) :
    connectedComponentIn (range r)ᶜ
        (Transversal.sectionPoint v base left +
          (-sign * c) • v) =
      connectedComponentIn (range r)ᶜ
        (Transversal.sectionPoint v base right +
          (-sign * c) • v) := by
  let bridge : ℝ → Plane := fun u ↦
    Transversal.sectionPoint v base u + (-sign * c) • v
  let S : Set Plane := bridge '' Icc left right
  have hbridge : Continuous bridge := by
    exact
      (Transversal.continuous_sectionPoint v base).add
        continuous_const
  have hSpre : IsPreconnected S :=
    isPreconnected_Icc.image bridge hbridge.continuousOn
  have hSsub : S ⊆ (range r)ᶜ := by
    rintro z ⟨u, hu, rfl⟩ hzRange
    rcases hrange hzRange with hzO | hzLine
    · have hwrong :=
        hOside (bridge u) hzO (hball u hu)
      dsimp only [bridge] at hwrong
      rw [Transversal.transverseValue_offset_sectionPoint hv] at hwrong
      rcases hsign with rfl | rfl <;> norm_num at hwrong <;> linarith
    · dsimp only [bridge] at hzLine
      change
        Transversal.transverseValue v base
          (Transversal.sectionPoint v base u + (-sign * c) • v) = 0
        at hzLine
      rw [Transversal.transverseValue_offset_sectionPoint hv] at hzLine
      rcases hsign with rfl | rfl <;> norm_num at hzLine <;> linarith
  have hleftMem : bridge left ∈ S :=
    ⟨left, ⟨le_rfl, (hleft.trans hright).le⟩, rfl⟩
  have hrightMem : bridge right ∈ S :=
    ⟨right, ⟨(hleft.trans hright).le, le_rfl⟩, rfl⟩
  apply connectedComponentIn_eq
  simpa only [bridge] using
    hSpre.subset_connectedComponentIn hleftMem hSsub hrightMem

/-- If an interval of the affine section is disjoint from the orbit part of a
Jordan loop and its endpoints are outside the loop, then those endpoints lie
in the same complementary component.  A side corridor supplies the connecting
set without touching the affine line itself. -/
theorem component_eq_sectionPoints_of_interval_disjoint
    (r : C(Circle, Plane)) (O : Set Plane)
    {v base : Plane} (hv : v ≠ 0)
    {a b sign : ℝ} (hab : a < b)
    (hsign : sign = 1 ∨ sign = -1)
    (hOclosed : IsClosed O) (hOne : O.Nonempty)
    (hOdisj : ∀ u ∈ Ioo a b,
      Transversal.sectionPoint v base u ∉ O)
    (hrange :
      range r ⊆
        O ∪ {z | Transversal.transverseValue v base z = 0})
    (haCompl : Transversal.sectionPoint v base a ∈ (range r)ᶜ)
    (hbCompl : Transversal.sectionPoint v base b ∈ (range r)ᶜ) :
    connectedComponentIn (range r)ᶜ
        (Transversal.sectionPoint v base a) =
      connectedComponentIn (range r)ᶜ
        (Transversal.sectionPoint v base b) := by
  let corridor : ℝ → Plane :=
    LocalSides.sideCorridor O v base a b sign
  let S : Set Plane := corridor '' Ioo a b
  have hcorridor : Continuous corridor :=
    LocalSides.continuous_sideCorridor O v base a b sign
  have hsignAbs : |sign| ≤ 1 := by
    rcases hsign with rfl | rfl <;> norm_num
  have hsignNe : sign ≠ 0 := by
    rcases hsign with rfl | rfl <;> norm_num
  have hSsub : S ⊆ (range r)ᶜ := by
    rintro z ⟨u, hu, rfl⟩ hzRange
    rcases hrange hzRange with hzO | hzLine
    · exact
        LocalSides.sideCorridor_not_mem_of_mem_Ioo
          O hv hsignAbs hu (hOdisj u hu) hOclosed hOne hzO
    · have hne :
          Transversal.transverseValue v base
              (LocalSides.sideCorridor O v base a b sign u) ≠ 0 := by
        rw [LocalSides.transverseValue_sideCorridor O hv]
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
      exact hne hzLine
  have hSpre : IsPreconnected S :=
    isPreconnected_Ioo.image corridor hcorridor.continuousOn
  have haClosure :
      Transversal.sectionPoint v base a ∈ closure S := by
    have ha : a ∈ closure (Ioo a b) := by
      rw [closure_Ioo hab.ne]
      exact ⟨le_rfl, hab.le⟩
    have hmap :=
      map_mem_closure hcorridor ha
        (fun u hu ↦ mem_image_of_mem corridor hu)
    simpa only [corridor, LocalSides.sideCorridor_left] using hmap
  have hbClosure :
      Transversal.sectionPoint v base b ∈ closure S := by
    have hb : b ∈ closure (Ioo a b) := by
      rw [closure_Ioo hab.ne]
      exact ⟨hab.le, le_rfl⟩
    have hmap :=
      map_mem_closure hcorridor hb
        (fun u hu ↦ mem_image_of_mem corridor hu)
    simpa only [corridor, LocalSides.sideCorridor_right] using hmap
  have hopen : IsOpen (range r)ᶜ :=
    (isCompact_range r.continuous).isClosed.isOpen_compl
  obtain ⟨Ra, hRa, hRaSub⟩ :=
    Metric.mem_nhds_iff.mp (hopen.mem_nhds haCompl)
  obtain ⟨Rb, hRb, hRbSub⟩ :=
    Metric.mem_nhds_iff.mp (hopen.mem_nhds hbCompl)
  obtain ⟨xa, hxaBall, hxaS⟩ :=
    mem_closure_iff.mp haClosure
      (ball (Transversal.sectionPoint v base a) Ra)
      isOpen_ball (mem_ball_self hRa)
  obtain ⟨yb, hybBall, hybS⟩ :=
    mem_closure_iff.mp hbClosure
      (ball (Transversal.sectionPoint v base b) Rb)
      isOpen_ball (mem_ball_self hRb)
  have hax :
      connectedComponentIn (range r)ᶜ
          (Transversal.sectionPoint v base a) =
        connectedComponentIn (range r)ᶜ xa :=
    component_eq_of_mem_ball_disjoint hRaSub
      (mem_ball_self hRa) hxaBall
  have hxy :
      connectedComponentIn (range r)ᶜ xa =
        connectedComponentIn (range r)ᶜ yb := by
    apply connectedComponentIn_eq
    exact
      hSpre.subset_connectedComponentIn
        hxaS hSsub hybS
  have hyb :
      connectedComponentIn (range r)ᶜ yb =
        connectedComponentIn (range r)ᶜ
          (Transversal.sectionPoint v base b) :=
    component_eq_of_mem_ball_disjoint hRbSub
      hybBall (mem_ball_self hRb)
  exact hax.trans (hxy.trans hyb)

/-- Near the initial endpoint of an injective orbit arc, the whole arc is on
the nonnegative longitudinal side of its transverse line. -/
theorem exists_start_ball_orbitArc_nonneg
    (β : ℝ → Plane) (hβcont : Continuous β)
    {v base : Plane} {B : ℝ} (hB : 0 < B)
    (hβinj : InjOn β (Icc (0 : ℝ) B))
    (hβ0 : Transversal.transverseValue v base (β 0) = 0)
    (hderiv :
      0 <
        deriv (fun t ↦
          Transversal.transverseValue v base (β t)) 0) :
    ∃ R : ℝ, 0 < R ∧
      ∀ z ∈ β '' Icc (0 : ℝ) B,
        z ∈ ball (β 0) R →
          0 ≤ Transversal.transverseValue v base z ∧
            (z ≠ β 0 →
              0 < Transversal.transverseValue v base z) := by
  let f : ℝ → ℝ :=
    fun t ↦ Transversal.transverseValue v base (β t)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f t := by
    have hsign :=
      eventually_nhdsWithin_sign_eq_of_deriv_pos hderiv hβ0
    filter_upwards
      [hsign.filter_mono inf_le_left, self_mem_nhdsWithin]
      with t htSign ht
    apply sign_eq_one_iff.mp
    exact htSign.trans (sign_pos (sub_pos.mpr ht))
  obtain ⟨η, hη, hηsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hpos
  let ε : ℝ := min (η / 2) (B / 2)
  have hε : 0 < ε :=
    lt_min (half_pos hη) (half_pos hB)
  have hεη : ε < η :=
    (min_le_left _ _).trans_lt (half_lt_self hη)
  have hεB : ε < B :=
    (min_le_right _ _).trans_lt (half_lt_self hB)
  let rest : Set Plane := β '' Icc ε B
  have hrestCompact : IsCompact rest :=
    isCompact_Icc.image hβcont
  have hβ0rest : β 0 ∉ rest := by
    rintro ⟨t, ht, ht0⟩
    have htFull : t ∈ Icc (0 : ℝ) B :=
      ⟨hε.le.trans ht.1, ht.2⟩
    have : t = 0 :=
      hβinj htFull (left_mem_Icc.mpr hB.le) ht0
    linarith [ht.1, hε]
  have hrestCompl : restᶜ ∈ 𝓝 (β 0) :=
    hrestCompact.isClosed.isOpen_compl.mem_nhds hβ0rest
  obtain ⟨R, hR, hRsub⟩ :=
    Metric.mem_nhds_iff.mp hrestCompl
  refine ⟨R, hR, ?_⟩
  rintro z ⟨t, ht, rfl⟩ htBall
  by_cases ht0 : t = 0
  · subst t
    exact ⟨hβ0.ge, fun h ↦ (h rfl).elim⟩
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  by_cases htε : t < ε
  · have hstrict := hηsub ⟨htpos, htε.trans hεη⟩
    exact ⟨hstrict.le, fun _ ↦ hstrict⟩
  · exfalso
    exact
      (hRsub htBall)
        ⟨t, ⟨le_of_not_gt htε, ht.2⟩, rfl⟩

/-- Near the terminal endpoint of an injective orbit arc, the whole arc is on
the nonpositive longitudinal side of its transverse line. -/
theorem exists_end_ball_orbitArc_nonpos
    (β : ℝ → Plane) (hβcont : Continuous β)
    {v base : Plane} {B : ℝ} (hB : 0 < B)
    (hβinj : InjOn β (Icc (0 : ℝ) B))
    (hβB : Transversal.transverseValue v base (β B) = 0)
    (hderiv :
      0 <
        deriv (fun t ↦
          Transversal.transverseValue v base (β t)) B) :
    ∃ R : ℝ, 0 < R ∧
      ∀ z ∈ β '' Icc (0 : ℝ) B,
        z ∈ ball (β B) R →
          Transversal.transverseValue v base z ≤ 0 ∧
            (z ≠ β B →
              Transversal.transverseValue v base z < 0) := by
  let f : ℝ → ℝ :=
    fun t ↦ Transversal.transverseValue v base (β t)
  have hneg : ∀ᶠ t in 𝓝[<] B, f t < 0 := by
    have hsign :=
      eventually_nhdsWithin_sign_eq_of_deriv_pos hderiv hβB
    filter_upwards
      [hsign.filter_mono inf_le_left, self_mem_nhdsWithin]
      with t htSign ht
    apply sign_eq_neg_one_iff.mp
    exact htSign.trans (sign_neg (sub_neg.mpr ht))
  obtain ⟨η, hη, hηsub⟩ :=
    mem_nhdsLT_iff_exists_Ioo_subset.mp hneg
  let ε : ℝ := min ((B - η) / 2) (B / 2)
  have hBη : 0 < B - η := sub_pos.mpr hη
  have hε : 0 < ε :=
    lt_min (half_pos hBη) (half_pos hB)
  have hηBε : η < B - ε := by
    have hε' : ε < B - η :=
      (min_le_left _ _).trans_lt (half_lt_self hBη)
    linarith
  let rest : Set Plane := β '' Icc (0 : ℝ) (B - ε)
  have hrestCompact : IsCompact rest :=
    isCompact_Icc.image hβcont
  have hβBrest : β B ∉ rest := by
    rintro ⟨t, ht, htB⟩
    have htFull : t ∈ Icc (0 : ℝ) B :=
      ⟨ht.1, ht.2.trans (sub_le_self B hε.le)⟩
    have : t = B :=
      hβinj htFull (right_mem_Icc.mpr hB.le) htB
    linarith [ht.2, hε]
  have hrestCompl : restᶜ ∈ 𝓝 (β B) :=
    hrestCompact.isClosed.isOpen_compl.mem_nhds hβBrest
  obtain ⟨R, hR, hRsub⟩ :=
    Metric.mem_nhds_iff.mp hrestCompl
  refine ⟨R, hR, ?_⟩
  rintro z ⟨t, ht, rfl⟩ htBall
  by_cases htB : t = B
  · subst t
    exact ⟨hβB.le, fun h ↦ (h rfl).elim⟩
  have htlt : t < B := ht.2.lt_of_ne htB
  by_cases hcut : B - ε < t
  · have hstrict := hηsub ⟨hηBε.trans hcut, htlt⟩
    exact ⟨hstrict.le, fun _ ↦ hstrict⟩
  · exfalso
    exact
      (hRsub htBall)
        ⟨t, ⟨ht.1, le_of_not_gt hcut⟩, rfl⟩

/-- Three future points cannot alternate between the two complementary
components of a transverse closing loop.  The two intervening arcs would
provide two positive crossings of the closing segment. -/
theorem no_alternating_complement_components
    {G : Plane → Plane} (β : ℝ → Plane)
    (hβ : IsIntegralCurve β (fun _ y ↦ G y))
    (r : C(Circle, Plane)) (hinj : Injective r)
    (O : Set Plane) {base : Plane} (hbase : G base ≠ 0)
    {A B : ℝ} (hAB : A < B)
    (hOclosed : IsClosed O) (hOne : O.Nonempty)
    (hOdisj : ∀ u ∈ Ioo A B,
      Transversal.sectionPoint (G base) base u ∉ O)
    (hrange :
      range r =
        O ∪
          [Transversal.sectionPoint (G base) base A -[ℝ]
            Transversal.sectionPoint (G base) base B])
    (hpositive : ∀ u ∈ Icc A B,
      0 <
        Transversal.transverseFunctional (G base)
          (G (Transversal.sectionPoint (G base) base u)))
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (haCompl : β a ∈ (range r)ᶜ)
    (hbCompl : β b ∈ (range r)ᶜ)
    (hcCompl : β c ∈ (range r)ᶜ)
    (habComp :
      connectedComponentIn (range r)ᶜ (β a) ≠
        connectedComponentIn (range r)ᶜ (β b))
    (hbcComp :
      connectedComponentIn (range r)ᶜ (β b) ≠
        connectedComponentIn (range r)ᶜ (β c))
    (havoidO : ∀ t ∈ Icc a c, β t ∉ O)
    (havoidEndpoints : ∀ t ∈ Icc a c,
      β t ≠ Transversal.sectionPoint (G base) base A ∧
      β t ≠ Transversal.sectionPoint (G base) base B)
    (hβinj : InjOn β (Icc a c)) :
    False := by
  have hhitAB :
      ∃ t ∈ Icc a b, β t ∈ range r := by
    by_contra hnone
    push Not at hnone
    have hSsub : β '' Icc a b ⊆ (range r)ᶜ := by
      rintro _ ⟨t, ht, rfl⟩ htRange
      exact hnone t ht htRange
    apply habComp
    apply connectedComponentIn_eq
    exact
      (isPreconnected_Icc.image β hβ.continuous.continuousOn)
        |>.subset_connectedComponentIn
          ⟨a, left_mem_Icc.mpr hab.le, rfl⟩ hSsub
          ⟨b, right_mem_Icc.mpr hab.le, rfl⟩
  have hhitBC :
      ∃ t ∈ Icc b c, β t ∈ range r := by
    by_contra hnone
    push Not at hnone
    have hSsub : β '' Icc b c ⊆ (range r)ᶜ := by
      rintro _ ⟨t, ht, rfl⟩ htRange
      exact hnone t ht htRange
    apply hbcComp
    apply connectedComponentIn_eq
    exact
      (isPreconnected_Icc.image β hβ.continuous.continuousOn)
        |>.subset_connectedComponentIn
          ⟨b, left_mem_Icc.mpr hbc.le, rfl⟩ hSsub
          ⟨c, right_mem_Icc.mpr hbc.le, rfl⟩
  obtain ⟨s, hs, hsRange⟩ := hhitAB
  obtain ⟨t, ht, htRange⟩ := hhitBC
  have has : a < s := hs.1.lt_of_ne fun h ↦
    haCompl (by simpa only [h] using hsRange)
  have hsb : s < b := hs.2.lt_of_ne fun h ↦
    hbCompl (by simpa only [h] using hsRange)
  have hbt : b < t := ht.1.lt_of_ne fun h ↦
    hbCompl (by simpa only [h] using htRange)
  have htc : t < c := ht.2.lt_of_ne fun h ↦
    hcCompl (by simpa only [h] using htRange)
  have hst : s < t := hsb.trans hbt
  have hsO : β s ∉ O :=
    havoidO s ⟨has.le, hsb.le.trans hbc.le⟩
  have hsSegment :
      β s ∈
        [Transversal.sectionPoint (G base) base A -[ℝ]
          Transversal.sectionPoint (G base) base B] := by
    rw [hrange] at hsRange
    exact hsRange.resolve_left hsO
  obtain ⟨C, hC, hβs⟩ :=
    Transversal.exists_eq_sectionPoint_of_mem_segment hAB hsSegment
  have hCA : C ≠ A := by
    intro h
    exact
      (havoidEndpoints s
        ⟨has.le, hsb.le.trans hbc.le⟩).1
        (by simpa only [h] using hβs)
  have hCB : C ≠ B := by
    intro h
    exact
      (havoidEndpoints s
        ⟨has.le, hsb.le.trans hbc.le⟩).2
        (by simpa only [h] using hβs)
  have hCopen : C ∈ Ioo A B :=
    ⟨hC.1.lt_of_ne hCA.symm, hC.2.lt_of_ne hCB⟩
  have hβinjST : InjOn β (Icc s t) := by
    apply hβinj.mono
    intro u hu
    exact ⟨has.le.trans hu.1, hu.2.trans htc.le⟩
  exact
    ReturnCrossing.no_two_positive_crossings
      β hβ r hinj O hbase hAB hOclosed hOne hOdisj
      hrange hpositive hst hCopen hβs htRange
      (fun u hu ↦ havoidO u
        ⟨has.le.trans hu.1, hu.2.trans htc.le⟩)
      (fun u hu ↦ havoidEndpoints u
        ⟨has.le.trans hu.1.le, hu.2.trans htc.le⟩)
      hβinjST

end

end Submission.EndpointBridge
