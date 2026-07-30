import Mathlib

namespace Submission.JordanHelpers

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem not_continuous_injective_to_real (hrank : 1 < Module.rank ℝ E)
    (f : E → ℝ) (hf : Continuous f) : ¬ Function.Injective f := by
  intro hinj
  obtain ⟨p, hp⟩ := (isConnected_sphere hrank 0 zero_le_one).nonempty
  have hp0 : p ≠ 0 := by
    intro hpzero
    subst p
    simp at hp
  have hvalues : f 0 ≠ f p := hinj.ne hp0.symm
  have himpossible (a b : E) (hab : f a < f b) : False := by
    let m : ℝ := (f a + f b) / 2
    have ham : f a < m := by
      dsimp [m]
      linarith
    have hmb : m < f b := by
      dsimp [m]
      linarith
    obtain ⟨c, _hcuniv, hfc⟩ :=
      convex_univ.isPreconnected.intermediate_value (Set.mem_univ a)
        (Set.mem_univ b) hf.continuousOn ⟨ham.le, hmb.le⟩
    have hca : c ≠ a := by
      intro hca
      subst c
      linarith
    have hcb : c ≠ b := by
      intro hcb
      subst c
      linarith
    have ha : a ∈ ({c}ᶜ : Set E) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hca.symm
    have hb : b ∈ ({c}ᶜ : Set E) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hcb.symm
    obtain ⟨d, hdc, hfd⟩ :=
      (isPathConnected_compl_singleton_of_one_lt_rank hrank c).isConnected.isPreconnected
        |>.intermediate_value ha hb hf.continuousOn ⟨ham.le, hmb.le⟩
    have hdc' : d = c := hinj (hfd.trans hfc.symm)
    exact hdc (by simpa only [Set.mem_singleton_iff] using hdc')
  rcases lt_or_gt_of_ne hvalues with h | h
  · exact himpossible 0 p h
  · exact himpossible p 0 h

theorem natCard_eq_two_of_partition {α : Type*} (p : α → Prop)
    (hp : ∃ x, p x) (hn : ∃ x, ¬p x)
    (huniqp : ∀ x y, p x → p y → x = y)
    (huniqn : ∀ x y, ¬p x → ¬p y → x = y) :
    Nat.card α = 2 := by
  classical
  let classify : α → Bool := fun x ↦ decide (p x)
  have hinj : Function.Injective classify := by
    intro x y hxy
    by_cases hx : p x <;> by_cases hy : p y
    · exact huniqp x y hx hy
    · simp [classify, hx, hy] at hxy
    · simp [classify, hx, hy] at hxy
    · exact huniqn x y hx hy
  have hsurj : Function.Surjective classify := by
    intro b
    cases b with
    | false =>
        obtain ⟨x, hx⟩ := hn
        exact ⟨x, by simp [classify, hx]⟩
    | true =>
        obtain ⟨x, hx⟩ := hp
        exact ⟨x, by simp [classify, hx]⟩
  calc
    Nat.card α = Nat.card Bool :=
      Nat.card_congr (Equiv.ofBijective classify ⟨hinj, hsurj⟩)
    _ = 2 := by simp

omit [NormedSpace ℝ E] in
theorem natCard_connectedComponents_eq_two_of_bounded_partition (s : Set E)
    (hb : ∃ x ∈ s, Bornology.IsBounded (connectedComponentIn s x))
    (hu : ∃ x ∈ s, ¬ Bornology.IsBounded (connectedComponentIn s x))
    (huniqb : ∀ x ∈ s, ∀ y ∈ s,
      Bornology.IsBounded (connectedComponentIn s x) →
      Bornology.IsBounded (connectedComponentIn s y) →
      connectedComponentIn s x = connectedComponentIn s y)
    (huniqu : ∀ x ∈ s, ∀ y ∈ s,
      ¬ Bornology.IsBounded (connectedComponentIn s x) →
      ¬ Bornology.IsBounded (connectedComponentIn s y) →
      connectedComponentIn s x = connectedComponentIn s y) :
    Nat.card (ConnectedComponents (s : Set E)) = 2 := by
  classical
  have hcomponent (x y : (s : Set E)) :
      (x : ConnectedComponents (s : Set E)) = y ↔
        connectedComponentIn s x = connectedComponentIn s y := by
    rw [ConnectedComponents.coe_eq_coe,
      connectedComponentIn_eq_image x.2, connectedComponentIn_eq_image y.2]
    constructor
    · exact fun h ↦ congrArg (fun t ↦ Subtype.val '' t) h
    · intro h
      exact Set.image_injective.mpr Subtype.val_injective h
  let p : ConnectedComponents (s : Set E) → Prop := fun c ↦
    ∃ x : (s : Set E),
      (x : ConnectedComponents (s : Set E)) = c ∧
        Bornology.IsBounded (connectedComponentIn s x)
  apply natCard_eq_two_of_partition p
  · obtain ⟨x, hxs, hx⟩ := hb
    exact ⟨(⟨x, hxs⟩ : (s : Set E)), ⟨⟨x, hxs⟩, rfl, hx⟩⟩
  · obtain ⟨x, hxs, hx⟩ := hu
    refine ⟨(⟨x, hxs⟩ : (s : Set E)), ?_⟩
    rintro ⟨y, hyc, hy⟩
    apply hx
    have heq : connectedComponentIn s y = connectedComponentIn s x :=
      (hcomponent y ⟨x, hxs⟩).mp hyc
    simpa only [heq] using hy
  · intro c d hc hd
    obtain ⟨x, hxc, hx⟩ := hc
    obtain ⟨y, hyd, hy⟩ := hd
    have hxy : (x : ConnectedComponents (s : Set E)) = y :=
      (hcomponent x y).mpr (huniqb x x.2 y y.2 hx hy)
    exact hxc.symm.trans (hxy.trans hyd)
  · intro c d hc hd
    obtain ⟨x, hxc⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨y, hyd⟩ := ConnectedComponents.surjective_coe d
    have hx : ¬ Bornology.IsBounded (connectedComponentIn s x) :=
      fun hx ↦ hc ⟨x, hxc, hx⟩
    have hy : ¬ Bornology.IsBounded (connectedComponentIn s y) :=
      fun hy ↦ hd ⟨y, hyd, hy⟩
    have hxy : (x : ConnectedComponents (s : Set E)) = y :=
      (hcomponent x y).mpr (huniqu x x.2 y y.2 hx hy)
    exact hxc.symm.trans (hxy.trans hyd)

noncomputable def connectedComponentsEquiv {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := e.continuous.connectedComponentsMap
  invFun := e.symm.continuous.connectedComponentsMap
  left_inv x := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    simp
  right_inv y := by
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
    simp

omit [NormedSpace ℝ E] in
theorem natCard_connectedComponents_compl_eq_of_homeomorph
    (e : E ≃ₜ E) {s t : Set E} (himage : e '' s = t) :
    Nat.card (ConnectedComponents (sᶜ : Set E)) =
      Nat.card (ConnectedComponents (tᶜ : Set E)) := by
  have hcomp : sᶜ = e ⁻¹' tᶜ := by
    ext x
    simp only [mem_compl_iff, mem_preimage]
    rw [← himage]
    simp
  exact Nat.card_congr (connectedComponentsEquiv (e.sets hcomp))

theorem isPathConnected_norm_gt (hrank : 1 < Module.rank ℝ E)
    (R : ℝ) (hR : 0 ≤ R) : IsPathConnected {x : E | R < ‖x‖} := by
  let f : E → E := fun y ↦ ((R + ‖y‖) * ‖y‖⁻¹) • y
  have hf : ContinuousOn f ({0}ᶜ : Set E) := by
    intro y hy
    change ContinuousWithinAt
      (fun z : E ↦ ((R + ‖z‖) * ‖z‖⁻¹) • z) {0}ᶜ y
    exact (((continuousAt_const.add continuousAt_id.norm).mul
      (ContinuousAt.inv₀ continuousAt_id.norm (by simpa using hy))).smul
        continuousAt_id).continuousWithinAt
  have hdomain : IsPathConnected ({0}ᶜ : Set E) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  rw [← show f '' ({0}ᶜ : Set E) = {x : E | R < ‖x‖} by
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have hynorm : ‖y‖ ≠ 0 := by simpa using hy
      have hcoef : 0 ≤ (R + ‖y‖) * ‖y‖⁻¹ :=
        mul_nonneg (add_nonneg hR (norm_nonneg y))
          (inv_nonneg.mpr (norm_nonneg y))
      change R < ‖((R + ‖y‖) * ‖y‖⁻¹) • y‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]
      rw [mul_assoc, inv_mul_cancel₀ hynorm, mul_one]
      exact lt_add_of_pos_right R
        (lt_of_le_of_ne (norm_nonneg y) hynorm.symm)
    · intro x hx
      have hxnorm : ‖x‖ ≠ 0 := ne_of_gt (hR.trans_lt hx)
      let a : ℝ := (‖x‖ - R) * ‖x‖⁻¹
      have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) hxnorm.symm
      have ha : 0 < a := mul_pos (sub_pos.mpr hx) (inv_pos.mpr hxpos)
      refine ⟨a • x, ?_, ?_⟩
      · have hxzero : x ≠ 0 := norm_ne_zero_iff.mp hxnorm
        simpa only [mem_compl_iff, mem_singleton_iff] using
          smul_ne_zero ha.ne' hxzero
      · simp only [f, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
        have hsub : ‖x‖ - R ≠ 0 := ne_of_gt (sub_pos.mpr hx)
        rw [smul_smul]
        rw [show ((R + a * ‖x‖) * (a * ‖x‖)⁻¹) * a = 1 by
          dsimp [a]
          field_simp [hsub, hxnorm]
          ring]
        exact one_smul ℝ x]
  exact hdomain.image' hf

omit [NormedSpace ℝ E] in
theorem sphere_isClosedEmbedding [ProperSpace E]
    (r : Metric.sphere (0 : E) 1 → E) (hcont : Continuous r)
    (hinj : Function.Injective r) : Topology.IsClosedEmbedding r :=
  hcont.isClosedEmbedding hinj

omit [NormedSpace ℝ E] in
theorem isOpen_compl_range_sphere_embedding [ProperSpace E]
    (r : Metric.sphere (0 : E) 1 → E) (hcont : Continuous r)
    (hinj : Function.Injective r) : IsOpen (Set.range r)ᶜ :=
  (sphere_isClosedEmbedding r hcont hinj).isClosed_range.isOpen_compl

theorem locPathConnectedSpace_compl_range_sphere_embedding [ProperSpace E]
    (r : Metric.sphere (0 : E) 1 → E) (hcont : Continuous r)
    (hinj : Function.Injective r) : LocPathConnectedSpace ((Set.range r)ᶜ : Set E) :=
  (isOpen_compl_range_sphere_embedding r hcont hinj).locPathConnectedSpace

theorem exists_pathConnected_exterior_subset_compl [ProperSpace E]
    (hrank : 1 < Module.rank ℝ E)
    (r : Metric.sphere (0 : E) 1 → E) (hcont : Continuous r) :
    ∃ R : ℝ, 0 < R ∧ IsPathConnected {x : E | R < ‖x‖} ∧
      {x : E | R < ‖x‖} ⊆ (Set.range r)ᶜ := by
  obtain ⟨R, hbound⟩ := (isCompact_range hcont).isBounded.subset_ball (0 : E)
  obtain ⟨p, hp⟩ := (isConnected_sphere hrank 0 zero_le_one).nonempty
  let q : Metric.sphere (0 : E) 1 := ⟨p, hp⟩
  have hR : 0 < R := by
    have hrp := hbound (⟨q, rfl⟩ : r q ∈ Set.range r)
    rw [Metric.mem_ball, dist_zero_right] at hrp
    exact (norm_nonneg (r q)).trans_lt hrp
  refine ⟨R, hR, isPathConnected_norm_gt hrank R hR.le, ?_⟩
  intro x hx
  rw [Set.mem_compl_iff]
  intro hxrange
  have hxball := hbound hxrange
  rw [Metric.mem_ball, dist_zero_right] at hxball
  exact (not_lt_of_ge hx.le) hxball

theorem exists_radius_connectedComponentIn_eq [ProperSpace E]
    (hrank : 1 < Module.rank ℝ E)
    (r : Metric.sphere (0 : E) 1 → E) (hcont : Continuous r) :
    ∃ R : ℝ, 0 < R ∧ ∀ x y : E, R < ‖x‖ → R < ‖y‖ →
      connectedComponentIn (Set.range r)ᶜ x =
        connectedComponentIn (Set.range r)ᶜ y := by
  obtain ⟨R, hR, hpath, hsubset⟩ :=
    exists_pathConnected_exterior_subset_compl hrank r hcont
  refine ⟨R, hR, ?_⟩
  intro x y hx hy
  apply connectedComponentIn_eq
  exact hpath.isConnected.isPreconnected.subset_connectedComponentIn hx hsubset hy

theorem connectedComponentIn_eq_of_not_isBounded [ProperSpace E]
    (hrank : 1 < Module.rank ℝ E)
    (r : Metric.sphere (0 : E) 1 → E) (hcont : Continuous r) {x y : E}
    (hx : ¬ Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x))
    (hy : ¬ Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ y)) :
    connectedComponentIn (Set.range r)ᶜ x =
      connectedComponentIn (Set.range r)ᶜ y := by
  obtain ⟨R, _hR, hfar⟩ := exists_radius_connectedComponentIn_eq hrank r hcont
  have hxfar : ∃ z ∈ connectedComponentIn (Set.range r)ᶜ x, R < ‖z‖ := by
    by_contra h
    push Not at h
    apply hx
    exact (isBounded_iff_forall_norm_le
      (s := connectedComponentIn (Set.range r)ᶜ x)).2 ⟨R, h⟩
  have hyfar : ∃ z ∈ connectedComponentIn (Set.range r)ᶜ y, R < ‖z‖ := by
    by_contra h
    push Not at h
    apply hy
    exact (isBounded_iff_forall_norm_le
      (s := connectedComponentIn (Set.range r)ᶜ y)).2 ⟨R, h⟩
  obtain ⟨z, hzx, hzR⟩ := hxfar
  obtain ⟨w, hwy, hwR⟩ := hyfar
  exact (connectedComponentIn_eq hzx).trans
    ((hfar z w hzR hwR).trans (connectedComponentIn_eq hwy).symm)

theorem exists_not_isBounded_connectedComponentIn_compl_range [ProperSpace E]
    (hrank : 1 < Module.rank ℝ E)
    (r : Metric.sphere (0 : E) 1 → E) (hcont : Continuous r) :
    ∃ x ∈ (Set.range r)ᶜ,
      ¬ Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x) := by
  obtain ⟨R, hR, hpath, hsubset⟩ :=
    exists_pathConnected_exterior_subset_compl hrank r hcont
  obtain ⟨x, hx⟩ := hpath.nonempty
  refine ⟨x, hsubset hx, ?_⟩
  intro hbounded
  have hexterior : Bornology.IsBounded {z : E | R < ‖z‖} :=
    hbounded.subset (hpath.isConnected.isPreconnected.subset_connectedComponentIn hx hsubset)
  obtain ⟨C, hC⟩ :=
    (isBounded_iff_forall_norm_le (s := {z : E | R < ‖z‖})).mp hexterior
  obtain ⟨p, hp⟩ := (isConnected_sphere hrank 0 zero_le_one).nonempty
  have hpnorm : ‖p‖ = 1 := by
    simpa [Metric.mem_sphere] using hp
  let a : ℝ := |C| + R + 1
  have ha : 0 < a := by
    dsimp [a]
    linarith [abs_nonneg C]
  have hnorm : ‖a • p‖ = a := by
    simp [norm_smul, hpnorm, abs_of_pos ha]
  have hmem : a • p ∈ {z : E | R < ‖z‖} := by
    change R < ‖a • p‖
    rw [hnorm]
    dsimp [a]
    linarith [abs_nonneg C]
  have hle := hC (a • p) hmem
  rw [hnorm] at hle
  dsimp [a] at hle
  linarith [le_abs_self C]

theorem natCard_connectedComponents_compl_range_eq_two_of_bounded_component
    [ProperSpace E] (hrank : 1 < Module.rank ℝ E)
    (r : Metric.sphere (0 : E) 1 → E) (hcont : Continuous r)
    (hb : ∃ x ∈ (Set.range r)ᶜ,
      Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x))
    (huniqb : ∀ x ∈ (Set.range r)ᶜ, ∀ y ∈ (Set.range r)ᶜ,
      Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x) →
      Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ y) →
      connectedComponentIn (Set.range r)ᶜ x =
        connectedComponentIn (Set.range r)ᶜ y) :
    Nat.card (ConnectedComponents ((Set.range r)ᶜ : Set E)) = 2 := by
  apply natCard_connectedComponents_eq_two_of_bounded_partition
  · exact hb
  · exact exists_not_isBounded_connectedComponentIn_compl_range hrank r hcont
  · exact huniqb
  · intro x hx y hy
    exact connectedComponentIn_eq_of_not_isBounded hrank r hcont

theorem frontier_connectedComponentIn_compl_range_subset [ProperSpace E]
    (r : Metric.sphere (0 : E) 1 → E) (hcont : Continuous r) {x : E}
    (_hx : x ∈ (Set.range r)ᶜ) :
    frontier (connectedComponentIn (Set.range r)ᶜ x) ⊆ Set.range r := by
  have hopenCompl : IsOpen (Set.range r)ᶜ :=
    (isCompact_range hcont).isClosed.isOpen_compl
  have hopenComponent (z : E) :
      IsOpen (connectedComponentIn (Set.range r)ᶜ z) :=
    hopenCompl.connectedComponentIn
  intro y hy
  by_contra hyr
  have hycompl : y ∈ (Set.range r)ᶜ := hyr
  have hynot : y ∉ connectedComponentIn (Set.range r)ᶜ x := by
    intro hyx
    exact hy.2 (mem_interior_iff_mem_nhds.mpr
      (IsOpen.mem_nhds (hopenComponent x) hyx))
  have hycomponent : y ∈ connectedComponentIn (Set.range r)ᶜ y :=
    mem_connectedComponentIn hycompl
  obtain ⟨z, hzy, hzx⟩ :=
    mem_closure_iff.mp hy.1 (connectedComponentIn (Set.range r)ᶜ y)
      (hopenComponent y) hycomponent
  have hzy' : connectedComponentIn (Set.range r)ᶜ y =
      connectedComponentIn (Set.range r)ᶜ z :=
    connectedComponentIn_eq (x := y) (y := z) hzy
  have hzx' : connectedComponentIn (Set.range r)ᶜ x =
      connectedComponentIn (Set.range r)ᶜ z :=
    connectedComponentIn_eq (x := x) (y := z) hzx
  have heq : connectedComponentIn (Set.range r)ᶜ y =
      connectedComponentIn (Set.range r)ᶜ x := hzy'.trans hzx'.symm
  exact hynot (heq ▸ hycomponent)

theorem frontier_connectedComponentIn_compl_range_nonempty [ProperSpace E]
    (hrank : 1 < Module.rank ℝ E)
    (r : Metric.sphere (0 : E) 1 → E) {x : E}
    (hx : x ∈ (Set.range r)ᶜ) :
    (frontier (connectedComponentIn (Set.range r)ᶜ x)).Nonempty := by
  rw [nonempty_frontier_iff]
  refine ⟨⟨x, mem_connectedComponentIn hx⟩, ?_⟩
  obtain ⟨z, hz⟩ := (isConnected_sphere hrank 0 zero_le_one).nonempty
  intro hcomponent
  have hrz : r ⟨z, hz⟩ ∈ connectedComponentIn (Set.range r)ᶜ x := by
    rw [hcomponent]
    exact Set.mem_univ _
  exact (connectedComponentIn_subset (Set.range r)ᶜ x hrz) ⟨⟨z, hz⟩, rfl⟩

theorem isPathConnected_one_lt_norm (hrank : 1 < Module.rank ℝ E) :
    IsPathConnected {x : E | 1 < ‖x‖} := by
  let f : E × ℝ → E := fun x ↦ x.2 • x.1
  have hsphere : IsPathConnected (Metric.sphere (0 : E) 1) :=
    isPathConnected_sphere hrank 0 zero_le_one
  have hIoi : IsPathConnected (Set.Ioi (1 : ℝ)) := by
    exact (convex_Ioi 1).isPathConnected ⟨2, by norm_num⟩
  have hprod : IsPathConnected (Metric.sphere (0 : E) 1 ×ˢ Set.Ioi (1 : ℝ)) :=
      by
    rcases hsphere with ⟨u, hu, hpaths_u⟩
    rcases hIoi with ⟨t, ht, hpaths_t⟩
    refine ⟨(u, t), ⟨hu, ht⟩, ?_⟩
    rintro ⟨v, s⟩ ⟨hv, hs⟩
    rcases hpaths_u hv with ⟨pu, hpu⟩
    rcases hpaths_t hs with ⟨pt, hpt⟩
    exact ⟨pu.prod pt, fun z ↦ ⟨hpu z, hpt z⟩⟩
  have hf : Continuous f := continuous_snd.smul continuous_fst
  have himage : f '' (Metric.sphere (0 : E) 1 ×ˢ Set.Ioi (1 : ℝ)) =
      {x : E | 1 < ‖x‖} := by
    ext x
    constructor
    · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      have hunorm : ‖u‖ = 1 := by simpa [Metric.mem_sphere] using hu
      simpa [f, norm_smul, abs_of_pos ht0, hunorm] using ht
    · intro hx
      have hx0 : ‖x‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
      refine ⟨(‖x‖⁻¹ • x, ‖x‖), ?_, ?_⟩
      · constructor
        · simp [norm_smul, hx0]
        · exact hx
      · simp [f, smul_smul, hx0]
  rw [← himage]
  exact hprod.image hf

theorem natCard_connectedComponents_compl_unit_sphere
    (hrank : 1 < Module.rank ℝ E) :
    Nat.card
        (ConnectedComponents ((Metric.sphere (0 : E) 1)ᶜ : Set E)) =
      2 := by
  let X : Set E := (Metric.sphere (0 : E) 1)ᶜ
  let U : Bool → Set X
    | false => {x | ‖(x : E)‖ < 1}
    | true => {x | 1 < ‖(x : E)‖}
  have hnorm_ne (x : X) : ‖(x : E)‖ ≠ 1 := by
    have hx := x.2
    change (x : E) ∉ Metric.sphere (0 : E) 1 at hx
    rw [Metric.mem_sphere] at hx
    simpa only [dist_zero_right] using hx
  have hopen : ∀ i, IsOpen (U i) := by
    intro i
    cases i with
    | false =>
        exact isOpen_lt continuous_subtype_val.norm continuous_const
    | true =>
        exact isOpen_lt continuous_const continuous_subtype_val.norm
  have hclosed : ∀ i, IsClosed (U i) := by
    intro i
    cases i with
    | false =>
        have heq : U false = {x : X | ‖(x : E)‖ ≤ 1} := by
          ext x
          simp only [U, mem_setOf_eq]
          constructor
          · exact fun hx ↦ hx.le
          · exact fun hx ↦ lt_of_le_of_ne hx (hnorm_ne x)
        rw [heq]
        exact isClosed_le continuous_subtype_val.norm continuous_const
    | true =>
        have heq : U true = {x : X | 1 ≤ ‖(x : E)‖} := by
          ext x
          simp only [U, mem_setOf_eq]
          constructor
          · exact fun hx ↦ hx.le
          · intro hx
            exact lt_of_le_of_ne hx (hnorm_ne x).symm
        rw [heq]
        exact isClosed_le continuous_const continuous_subtype_val.norm
  have hclopen : ∀ i, IsClopen (U i) := fun i ↦ ⟨hclosed i, hopen i⟩
  have hdisj : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · apply Set.disjoint_left.2
      intro x hx hy
      change ‖(x : E)‖ < 1 at hx
      change 1 < ‖(x : E)‖ at hy
      exact (not_lt_of_ge hy.le) hx
    · apply Set.disjoint_left.2
      intro x hx hy
      change 1 < ‖(x : E)‖ at hx
      change ‖(x : E)‖ < 1 at hy
      exact (not_lt_of_ge hx.le) hy
    · exact (hij rfl).elim
  have hunion : ⋃ i, U i = Set.univ := by
    rw [Set.iUnion_eq_univ_iff]
    intro x
    rcases lt_or_gt_of_ne (hnorm_ne x) with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  have himage_false : Subtype.val '' U false = Metric.ball (0 : E) 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [U, Metric.mem_ball]
    · intro hx
      have hxnorm : ‖x‖ < 1 := by simpa [Metric.mem_ball] using hx
      have hxsphere : x ∈ X := by
        simpa [X, Metric.mem_sphere] using ne_of_lt hxnorm
      exact ⟨⟨x, hxsphere⟩, hxnorm, rfl⟩
  have himage_true : Subtype.val '' U true = {x : E | 1 < ‖x‖} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hxsphere : x ∈ X := by
        simpa [X, Metric.mem_sphere] using ne_of_gt hx
      exact ⟨⟨x, hxsphere⟩, hx, rfl⟩
  have hconn : ∀ i, IsConnected (U i) := by
    intro i
    cases i with
    | false =>
        apply IsPathConnected.isConnected
        rw [Topology.IsInducing.subtypeVal.isPathConnected_iff, himage_false]
        exact Metric.isPathConnected_ball zero_lt_one
    | true =>
        apply IsPathConnected.isConnected
        rw [Topology.IsInducing.subtypeVal.isPathConnected_iff, himage_true]
        exact isPathConnected_one_lt_norm hrank
  calc
    Nat.card (ConnectedComponents X) = Nat.card Bool :=
      Nat.card_congr
        (ConnectedComponents.equivOfIsClopenOfIsConnected hclopen hdisj hunion hconn)
    _ = 2 := by simp

theorem natCard_connectedComponents_compl_range_of_ambient_homeomorph
    {r : Metric.sphere (0 : E) 1 → E} (hrank : 1 < Module.rank ℝ E)
    (e : E ≃ₜ E) (himage : e '' Metric.sphere (0 : E) 1 = Set.range r) :
    Nat.card (ConnectedComponents ((Set.range r)ᶜ : Set E)) = 2 := by
  calc
    Nat.card (ConnectedComponents ((Set.range r)ᶜ : Set E)) =
        Nat.card (ConnectedComponents ((Metric.sphere (0 : E) 1)ᶜ : Set E)) :=
      (natCard_connectedComponents_compl_eq_of_homeomorph e himage).symm
    _ = 2 := natCard_connectedComponents_compl_unit_sphere hrank

theorem natCard_connectedComponents_compl_range_of_schoenflies
    {r : Metric.sphere (0 : E) 1 → E} (hrank : 1 < Module.rank ℝ E)
    (e : E ≃ₜ E) (himage : e '' Set.range r = Metric.sphere (0 : E) 1) :
    Nat.card (ConnectedComponents ((Set.range r)ᶜ : Set E)) = 2 := by
  apply natCard_connectedComponents_compl_range_of_ambient_homeomorph hrank e.symm
  calc
    e.symm '' Metric.sphere (0 : E) 1 = e.symm '' (e '' Set.range r) :=
      congrArg (fun s : Set E ↦ e.symm '' s) himage.symm
    _ = Set.range r := by
      ext x
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

theorem exists_strict_unitBall_extension [ProperSpace E] [FiniteDimensional ℝ E]
    (hrank : 1 < Module.rank ℝ E)
    (r : Metric.sphere (0 : E) 1 → E) (hcont : Continuous r)
    (hinj : Function.Injective r) :
    ∃ f : C(E, E),
      (∀ z, f (r z) = z) ∧
      (∀ x, ‖f x‖ ≤ 1) ∧
      (∀ x, x ∉ Set.range r → ‖f x‖ < 1) := by
  let inclusion : C(Metric.sphere (0 : E) 1, E) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hclosedEmbedding := sphere_isClosedEmbedding r hcont hinj
  obtain ⟨F, hFball, hF⟩ :=
    inclusion.exists_extension_forall_mem hclosedEmbedding
      (t := Metric.closedBall (0 : E) 1) fun z ↦
        Metric.sphere_subset_closedBall z.2
  obtain ⟨z, hz⟩ := (isConnected_sphere hrank 0 zero_le_one).nonempty
  have hrange : (Set.range r).Nonempty :=
    ⟨r ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩⟩
  have hrangeClosed : IsClosed (Set.range r) :=
    hclosedEmbedding.isClosed_range
  let scale : E → ℝ :=
    fun x ↦ (1 + Metric.infDist x (Set.range r))⁻¹
  have hdenom (x : E) :
      0 < 1 + Metric.infDist x (Set.range r) :=
    add_pos_of_pos_of_nonneg zero_lt_one Metric.infDist_nonneg
  have hscale : Continuous scale := by
    exact (continuous_const.add
      (Metric.continuous_infDist_pt (Set.range r))).inv₀ fun x ↦ by
        exact (hdenom x).ne'
  let f : C(E, E) :=
    ⟨fun x ↦ scale x • F x, hscale.smul F.continuous⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro w
    have hdist : Metric.infDist (r w) (Set.range r) = 0 :=
      Metric.infDist_zero_of_mem ⟨w, rfl⟩
    have hFw : F (r w) = w := by
      exact DFunLike.congr_fun hF w
    simp [f, scale, hdist, hFw]
  · intro x
    have hFnorm : ‖F x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hFball x
    have hdist : 0 ≤ Metric.infDist x (Set.range r) :=
      Metric.infDist_nonneg
    have hscale_nonneg : 0 ≤ scale x := by
      exact inv_nonneg.mpr (hdenom x).le
    have hscale_le_one : scale x ≤ 1 := by
      change (1 + Metric.infDist x (Set.range r))⁻¹ ≤ 1
      rw [inv_le_one₀ (hdenom x)]
      linarith
    calc
      ‖f x‖ = scale x * ‖F x‖ := by
        simp [f, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale_nonneg]
      _ ≤ scale x * 1 := mul_le_mul_of_nonneg_left hFnorm hscale_nonneg
      _ ≤ 1 := by simpa using hscale_le_one
  · intro x hx
    have hFnorm : ‖F x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hFball x
    have hdist : 0 < Metric.infDist x (Set.range r) :=
      (hrangeClosed.notMem_iff_infDist_pos hrange).mp hx
    have hscale_pos : 0 < scale x := by
      exact inv_pos.mpr (hdenom x)
    have hscale_lt_one : scale x < 1 := by
      change (1 + Metric.infDist x (Set.range r))⁻¹ < 1
      rw [inv_lt_one₀ (hdenom x)]
      linarith
    calc
      ‖f x‖ = scale x * ‖F x‖ := by
        simp [f, norm_smul, Real.norm_eq_abs, abs_of_pos hscale_pos]
      _ ≤ scale x * 1 := mul_le_mul_of_nonneg_left hFnorm hscale_pos.le
      _ < 1 := by simpa using hscale_lt_one

theorem one_lt_rank_euclideanSpace_fin_two :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
  rw [(WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).rank_eq, rank_fin_fun]
  norm_num

theorem interior_range_sphere_embedding_eq_empty
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    interior (Set.range r) = ∅ := by
  let E := EuclideanSpace ℝ (Fin 2)
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
  obtain ⟨p, hp⟩ :=
    (isConnected_sphere one_lt_rank_euclideanSpace_fin_two 0 zero_le_one).nonempty
  have hpnorm : ‖p‖ = 1 := by
    simpa [Metric.mem_sphere] using hp
  let q : E := y + (3 * ε / 4) • p
  have hdistq : dist y q = 3 * ε / 4 := by
    rw [dist_eq_norm]
    simp [q, norm_smul, hpnorm]
    positivity
  have hqbig : q ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, dist_comm, hdistq]
    linarith
  have hqsmall : q ∉ Metric.ball y (ε / 2) := by
    rw [Metric.mem_ball, dist_comm, hdistq]
    linarith
  have hεhalf : 0 < ε / 2 := half_pos hε
  let g : E → E := OpenPartialHomeomorph.univBall y (ε / 2)
  have hgcont : Continuous g :=
    OpenPartialHomeomorph.continuous_univBall y (ε / 2)
  have hgsmall (x : E) : g x ∈ Metric.ball y (ε / 2) := by
    rw [← OpenPartialHomeomorph.univBall_target y hεhalf]
    exact (OpenPartialHomeomorph.univBall y (ε / 2)).map_source (by simp)
  have hginj : Function.Injective g := by
    intro x x' hxx'
    exact (OpenPartialHomeomorph.univBall y (ε / 2)).injOn
      (by simp) (by simp) hxx'
  have hsmallRange : Metric.ball y (ε / 2) ⊆ Set.range r :=
    (Metric.ball_subset_ball (by linarith : ε / 2 ≤ ε)).trans hball
  let e : Metric.sphere (0 : E) 1 ≃ₜ Set.range r :=
    (sphere_isClosedEmbedding r hcont hinj).toIsEmbedding.toHomeomorph
  let zfun : E → Metric.sphere (0 : E) 1 := fun x ↦
    e.symm ⟨g x, hsmallRange (hgsmall x)⟩
  have hzcont : Continuous zfun := by
    exact e.symm.continuous.comp (hgcont.subtype_mk fun x ↦ hsmallRange (hgsmall x))
  have hzinj : Function.Injective zfun := by
    intro x x' hxx'
    apply hginj
    exact congrArg Subtype.val (e.symm.injective hxx')
  have hrz (x : E) : r (zfun x) = g x := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨g x, hsmallRange (hgsmall x)⟩)
  obtain ⟨w, hw⟩ := hball hqbig
  have hzw (x : E) : zfun x ≠ w := by
    intro hxw
    apply hqsmall
    rw [← hw, ← hxw, hrz]
    exact hgsmall x
  letI : Fact (Module.finrank ℝ E = 1 + 1) := ⟨by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2
    simp⟩
  let stereo := stereographic' 1 w
  have hzsource (x : E) : zfun x ∈ stereo.source := by
    rw [stereographic'_source]
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzw x
  let u : E → EuclideanSpace ℝ (Fin 1) := fun x ↦ stereo (zfun x)
  have hucont : Continuous u := by
    exact stereo.continuousOn.comp_continuous hzcont hzsource
  have huinj : Function.Injective u := by
    intro x x' hxx'
    apply hzinj
    exact stereo.injOn (hzsource x) (hzsource x') hxx'
  let f : E → ℝ := fun x ↦ u x 0
  have hfcont : Continuous f :=
    (PiLp.continuous_apply (p := (2 : ENNReal))
      (β := fun _ : Fin 1 => ℝ) 0).comp hucont
  have hevalinj : Function.Injective
      (fun z : EuclideanSpace ℝ (Fin 1) ↦ z 0) := by
    intro z z' hzz'
    ext i
    fin_cases i
    exact hzz'
  have hfinj : Function.Injective f := fun _ _ h ↦ huinj (hevalinj h)
  exact not_continuous_injective_to_real one_lt_rank_euclideanSpace_fin_two f hfcont hfinj

theorem exists_continuous_injective_to_real_of_subset_range_of_omits_point
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hcont : Continuous r) (hinj : Function.Injective r)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : A ⊆ Set.range r)
    (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (hw : r w ∉ A) :
    ∃ f : A → ℝ, Continuous f ∧ Function.Injective f := by
  let E := EuclideanSpace ℝ (Fin 2)
  let e : Metric.sphere (0 : E) 1 ≃ₜ Set.range r :=
    (sphere_isClosedEmbedding r hcont hinj).toIsEmbedding.toHomeomorph
  let zfun : A → Metric.sphere (0 : E) 1 := fun x ↦
    e.symm ⟨x, hA x.2⟩
  have hzcont : Continuous zfun := by
    exact e.symm.continuous.comp
      (continuous_subtype_val.subtype_mk fun x ↦ hA x.2)
  have hzinj : Function.Injective zfun := by
    intro x x' hxx'
    have hpair : (⟨(x : E), hA x.2⟩ : Set.range r) =
        ⟨(x' : E), hA x'.2⟩ := e.symm.injective hxx'
    exact Subtype.ext (congrArg (fun z : Set.range r ↦ (z : E)) hpair)
  have hrz (x : A) : r (zfun x) = x := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hA x.2⟩)
  have hzw (x : A) : zfun x ≠ w := by
    intro hxw
    apply hw
    rw [← hxw, hrz]
    exact x.2
  letI : Fact (Module.finrank ℝ E = 1 + 1) := ⟨by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2
    simp⟩
  let stereo := stereographic' 1 w
  have hzsource (x : A) : zfun x ∈ stereo.source := by
    rw [stereographic'_source]
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzw x
  let u : A → EuclideanSpace ℝ (Fin 1) := fun x ↦ stereo (zfun x)
  have hucont : Continuous u :=
    stereo.continuousOn.comp_continuous hzcont hzsource
  have huinj : Function.Injective u := by
    intro x x' hxx'
    apply hzinj
    exact stereo.injOn (hzsource x) (hzsource x') hxx'
  let f : A → ℝ := fun x ↦ u x 0
  have hfcont : Continuous f :=
    (PiLp.continuous_apply (p := (2 : ENNReal))
      (β := fun _ : Fin 1 => ℝ) 0).comp hucont
  have hevalinj : Function.Injective
      (fun z : EuclideanSpace ℝ (Fin 1) ↦ z 0) := by
    intro z z' hzz'
    ext i
    fin_cases i
    exact hzz'
  exact ⟨f, hfcont, fun _ _ h ↦ huinj (hevalinj h)⟩

theorem frontier_compl_range_sphere_embedding_eq
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    frontier ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2))) = Set.range r := by
  rw [frontier_compl]
  have hclosed : IsClosed (Set.range r) := (isCompact_range hcont).isClosed
  rw [hclosed.frontier_eq, interior_range_sphere_embedding_eq_empty r hcont hinj]
  simp

theorem dense_compl_range_sphere_embedding
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    Dense ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [dense_iff_closure_eq]
  rw [closure_compl]
  simp [interior_range_sphere_embedding_eq_empty r hcont hinj]

end Submission.JordanHelpers
