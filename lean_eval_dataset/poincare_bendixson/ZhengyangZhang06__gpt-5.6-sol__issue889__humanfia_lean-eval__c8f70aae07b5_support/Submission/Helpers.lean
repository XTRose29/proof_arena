import ChallengeDeps

open Filter Topology Set
open scoped NNReal

open LeanEval.Dynamics

namespace Submission.Helpers

/-- The set of cluster points of a curve along its positive-time tails. -/
def omegaSet (γ : ℝ → Plane) : Set Plane :=
  ⋂ s : ℝ, closure (γ '' Ici s)

theorem isClosed_omegaSet (γ : ℝ → Plane) : IsClosed (omegaSet γ) := by
  exact isClosed_iInter fun _ ↦ isClosed_closure

theorem omegaSet_subset_closure_image_Ici (γ : ℝ → Plane) (s : ℝ) :
    omegaSet γ ⊆ closure (γ '' Ici s) := by
  exact iInter_subset _ s

theorem omegaSet_eq_iInter_nat (γ : ℝ → Plane) :
    omegaSet γ = ⋂ n : ℕ, closure (γ '' Ici (n : ℝ)) := by
  apply Subset.antisymm
  · intro x hx
    exact mem_iInter.2 fun n ↦ omegaSet_subset_closure_image_Ici γ n hx
  · intro x hx
    rw [omegaSet, mem_iInter]
    intro s
    obtain ⟨n, hn⟩ := exists_nat_ge s
    exact closure_mono (image_mono (Ici_subset_Ici.mpr hn)) (mem_iInter.1 hx n)

theorem mem_omegaSet_iff_mapClusterPt (γ : ℝ → Plane) (x : Plane) :
    x ∈ omegaSet γ ↔ MapClusterPt x atTop γ := by
  rw [omegaSet, mem_iInter]
  exact mapClusterPt_atTop_iff_forall_mem_closure.symm

theorem exists_nat_subset_of_iInter_subset_open (K : ℕ → Set Plane)
    (hK : ∀ n, IsCompact (K n)) (hanti : Antitone K)
    {u : Set Plane} (hu : IsOpen u) (hsub : (⋂ n, K n) ⊆ u) :
    ∃ n, K n ⊆ u := by
  by_contra hn
  simp only [not_exists, not_subset] at hn
  have hnonempty : ∀ n, (K n ∩ uᶜ).Nonempty := by
    intro n
    obtain ⟨x, hxK, hxu⟩ := hn n
    exact ⟨x, hxK, hxu⟩
  have hinter : (⋂ n, K n ∩ uᶜ).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n ↦ K n ∩ uᶜ)
      (fun n ↦ inter_subset_inter (hanti (Nat.le_succ n)) Subset.rfl)
      hnonempty ((hK 0).inter_right hu.isClosed_compl)
      (fun n ↦ (hK n).isClosed.inter hu.isClosed_compl)
  obtain ⟨x, hx⟩ := hinter
  have hxall := mem_iInter.1 hx
  exact (hxall 0).2 (hsub (mem_iInter.2 fun n ↦ (hxall n).1))

theorem isPreconnected_iInter_of_antitone_compact (K : ℕ → Set Plane)
    (hK : ∀ n, IsCompact (K n)) (hanti : Antitone K)
    (hpreconnected : ∀ n, IsPreconnected (K n)) :
    IsPreconnected (⋂ n, K n) := by
  have hclosed : IsClosed (⋂ n, K n) :=
    isClosed_iInter fun n ↦ (hK n).isClosed
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hclosed]
  intro a b ha hb hcover hab
  obtain ⟨u, v, hu, hv, hau, hbv, huv⟩ := normal_separation ha hb hab
  obtain ⟨n, hn⟩ := exists_nat_subset_of_iInter_subset_open K hK hanti
    (hu.union hv) (hcover.trans (union_subset_union hau hbv))
  rcases (hpreconnected n).subset_or_subset hu hv huv hn with hnu | hnv
  · refine Or.inl ?_
    intro x hx
    rcases hcover hx with hxa | hxb
    · exact hxa
    · exact (Set.disjoint_left.1 huv (hnu (mem_iInter.1 hx n)) (hbv hxb)).elim
  · refine Or.inr ?_
    intro x hx
    rcases hcover hx with hxa | hxb
    · exact (Set.disjoint_left.1 huv (hau hxa) (hnv (mem_iInter.1 hx n))).elim
    · exact hxb

theorem isCompact_omegaSet (γ : ℝ → Plane)
    (hγ : Bornology.IsBounded (γ '' Ici 0)) :
    IsCompact (omegaSet γ) := by
  exact hγ.isCompact_closure.of_isClosed_subset
    (isClosed_omegaSet γ) (omegaSet_subset_closure_image_Ici γ 0)

theorem isPreconnected_omegaSet (γ : ℝ → Plane)
    (hγ : ContinuousOn γ (Ici 0))
    (hbounded : Bornology.IsBounded (γ '' Ici 0)) :
    IsPreconnected (omegaSet γ) := by
  rw [omegaSet_eq_iInter_nat]
  apply isPreconnected_iInter_of_antitone_compact
  · intro n
    exact
      (hbounded.subset
        (image_mono (Ici_subset_Ici.mpr (Nat.cast_nonneg n)))).isCompact_closure
  · intro m n hmn
    exact closure_mono (image_mono (Ici_subset_Ici.mpr (by exact_mod_cast hmn)))
  · intro n
    exact
      (isPreconnected_Ici.image γ
        (hγ.mono (Ici_subset_Ici.mpr (Nat.cast_nonneg n)))).closure

theorem eventually_mem_of_omegaSet_subset_open (γ : ℝ → Plane)
    (hbounded : Bornology.IsBounded (γ '' Ici 0))
    {u : Set Plane} (hu : IsOpen u) (hsub : omegaSet γ ⊆ u) :
    ∀ᶠ t in atTop, γ t ∈ u := by
  let K : ℕ → Set Plane := fun n ↦ closure (γ '' Ici (n : ℝ))
  have hK : ∀ n, IsCompact (K n) := by
    intro n
    exact
      (hbounded.subset
        (image_mono (Ici_subset_Ici.mpr (Nat.cast_nonneg n)))).isCompact_closure
  have hanti : Antitone K := by
    intro m n hmn
    exact closure_mono (image_mono (Ici_subset_Ici.mpr (by exact_mod_cast hmn)))
  obtain ⟨n, hn⟩ :=
    exists_nat_subset_of_iInter_subset_open K hK hanti hu (by
      rw [← omegaSet_eq_iInter_nat γ]
      exact hsub)
  filter_upwards [eventually_ge_atTop (n : ℝ)] with t ht
  exact hn (subset_closure ⟨t, ht, rfl⟩)

theorem tendsto_atTop_of_omegaSet_eq_singleton (γ : ℝ → Plane)
    (hbounded : Bornology.IsBounded (γ '' Ici 0)) {x : Plane}
    (homega : omegaSet γ = {x}) :
    Tendsto γ atTop (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  apply eventually_mem_of_omegaSet_subset_open γ hbounded Metric.isOpen_ball
  rw [homega, singleton_subset_iff]
  exact Metric.mem_ball_self hε

theorem equilibrium_of_tendsto_integralCurveOn
    (F : Plane → Plane) (hF : Continuous F) (γ : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    {x : Plane} (hlim : Tendsto γ atTop (𝓝 x)) :
    F x = 0 := by
  by_contra hFx
  let p : Plane →L[ℝ] ℝ := innerSL ℝ (F x)
  let d : ℝ := p (F x)
  have hd : 0 < d := by
    dsimp [d, p]
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hFx)
  have hFγ : Tendsto (fun t ↦ F (γ t)) atTop (𝓝 (F x)) := by
    simpa [Function.comp_def] using
      (Filter.Tendsto.comp hF.continuousAt hlim)
  have hvelocity : Tendsto (fun t ↦ p (F (γ t))) atTop (𝓝 d) := by
    simpa [d, Function.comp_def] using
      (Filter.Tendsto.comp p.continuous.continuousAt hFγ)
  have hvelocity_lower : ∀ᶠ t in atTop, d / 2 < p (F (γ t)) :=
    hvelocity.eventually (Ioi_mem_nhds (half_lt_self hd))
  obtain ⟨T, hT⟩ :=
    eventually_atTop.1 ((eventually_ge_atTop (0 : ℝ)).and hvelocity_lower)
  have hT0 : 0 ≤ T := (hT T le_rfl).1
  let g : ℝ → ℝ := fun t ↦ p (γ t)
  let l : ℝ := p x
  have hglim : Tendsto g atTop (𝓝 l) := by
    simpa [g, l, Function.comp_def] using
      (Filter.Tendsto.comp p.continuous.continuousAt hlim)
  have hg_upper : ∀ᶠ t in atTop, g t < l + 1 :=
    hglim.eventually (Iio_mem_nhds (lt_add_one l))
  obtain ⟨U, hU⟩ := eventually_atTop.1 hg_upper
  have hderiv (t : ℝ) (ht : 0 < t) :
      HasDerivAt g (p (F (γ t))) t := by
    simpa [g, Function.comp_def] using
      (p.hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht.le)).hasDerivAt
        (Ici_mem_nhds ht)
  have hgcont : ContinuousOn g (Ici T) := by
    simpa [g, Function.comp_def] using
      p.continuous.comp_continuousOn
        (hγ.continuousOn.mono (Ici_subset_Ici.mpr hT0))
  have hgdiff : DifferentiableOn ℝ g (interior (Ici T)) := by
    intro t ht
    rw [interior_Ici] at ht
    exact
      (hderiv t (lt_of_le_of_lt hT0 ht)).differentiableAt.differentiableWithinAt
  have hgderiv : ∀ t ∈ interior (Ici T), d / 2 ≤ deriv g t := by
    intro t ht
    rw [interior_Ici] at ht
    rw [(hderiv t (lt_of_le_of_lt hT0 ht)).deriv]
    exact (hT t ht.le).2.le
  let A : ℝ := |l - g T| + 1
  have hA : 0 < A := by
    dsimp [A]
    positivity
  let y : ℝ := max T U + 2 * A / d
  have hdelta : 0 < 2 * A / d := div_pos (mul_pos two_pos hA) hd
  have hTy : T ≤ y := by
    dsimp [y]
    linarith [le_max_left T U]
  have hUy : U ≤ y := by
    dsimp [y]
    linarith [le_max_right T U]
  have hgrowth : d / 2 * (y - T) ≤ g y - g T :=
    (convex_Ici T).mul_sub_le_image_sub_of_le_deriv hgcont hgdiff hgderiv
      T (by simpa only [mem_Ici] using le_refl T) y hTy hTy
  have hidentity : d / 2 * (2 * A / d) = A := by
    field_simp [ne_of_gt hd]
  have hdelta_le : 2 * A / d ≤ y - T := by
    dsimp [y]
    linarith [le_max_left T U]
  have hA_le : A ≤ g y - g T := by
    calc
      A = d / 2 * (2 * A / d) := hidentity.symm
      _ ≤ d / 2 * (y - T) :=
        mul_le_mul_of_nonneg_left hdelta_le (half_pos hd).le
      _ ≤ g y - g T := hgrowth
  have hy_upper : g y < l + 1 := hU y hUy
  have habs : l - g T ≤ |l - g T| := le_abs_self _
  dsimp [A] at hA_le
  linarith

theorem omegaSet_nonempty (γ : ℝ → Plane)
    (hγ : Bornology.IsBounded (γ '' Ici 0)) :
    (omegaSet γ).Nonempty := by
  have heventually : ∀ᶠ t in atTop, γ t ∈ closure (γ '' Ici 0) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact subset_closure ⟨t, ht, rfl⟩
  have hfrequent : ∃ᶠ t in atTop, γ t ∈ closure (γ '' Ici 0) :=
    Eventually.frequently heventually
  obtain ⟨x, _, hx⟩ :=
    hγ.isCompact_closure.exists_mapClusterPt_of_frequently hfrequent
  exact ⟨x, (mem_omegaSet_iff_mapClusterPt γ x).2 hx⟩

theorem equilibrium_of_omegaSet_eq_singleton
    (F : Plane → Plane) (hF : Continuous F) (γ : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    (hbounded : Bornology.IsBounded (γ '' Ici 0)) {x : Plane}
    (homega : omegaSet γ = {x}) :
    F x = 0 :=
  equilibrium_of_tendsto_integralCurveOn F hF γ hγ
    (tendsto_atTop_of_omegaSet_eq_singleton γ hbounded homega)

theorem exists_distinct_mem_omegaSet_of_regular
    (F : Plane → Plane) (hF : Continuous F) (γ : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ F x) (Ici 0))
    (hbounded : Bornology.IsBounded (γ '' Ici 0))
    (hregular : ∀ x ∈ omegaSet γ, F x ≠ 0) :
    ∃ x ∈ omegaSet γ, ∃ y ∈ omegaSet γ, y ≠ x := by
  obtain ⟨x, hx⟩ := omegaSet_nonempty γ hbounded
  by_cases h : ∃ y ∈ omegaSet γ, y ≠ x
  · obtain ⟨y, hy, hyx⟩ := h
    exact ⟨x, hx, y, hy, hyx⟩
  · have homega : omegaSet γ = {x} := by
      ext y
      constructor
      · intro hy
        have hyx : y = x := by
          by_contra hyx
          exact h ⟨y, hy, hyx⟩
        simpa only [mem_singleton_iff] using hyx
      · intro hy
        have hyx : y = x := by
          simpa only [mem_singleton_iff] using hy
        subst y
        exact hx
    exact
      (hregular x hx
        (equilibrium_of_omegaSet_eq_singleton F hF γ hγ hbounded homega)).elim

theorem exists_pos_le_norm_on_omegaSet (F : Plane → Plane) (hF : Continuous F)
    (γ : ℝ → Plane) (hγ : Bornology.IsBounded (γ '' Ici 0))
    (hregular : ∀ x ∈ omegaSet γ, F x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ omegaSet γ, ε ≤ ‖F x‖ := by
  exact (isCompact_omegaSet γ hγ).exists_forall_le'
    hF.norm.continuousOn fun x hx ↦ norm_pos_iff.mpr (hregular x hx)

theorem equilibrium_or_uniform_speed (F : Plane → Plane) (hF : Continuous F)
    (γ : ℝ → Plane) (hγ : Bornology.IsBounded (γ '' Ici 0)) :
    (∃ x, F x = 0 ∧ x ∈ omegaSet γ) ∨
      ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ omegaSet γ, ε ≤ ‖F x‖ := by
  classical
  by_cases h : ∃ x ∈ omegaSet γ, F x = 0
  · obtain ⟨x, hx, hFx⟩ := h
    exact Or.inl ⟨x, hFx, hx⟩
  · refine Or.inr (exists_pos_le_norm_on_omegaSet F hF γ hγ ?_)
    intro x hx hFx
    exact h ⟨x, hx, hFx⟩

theorem integralCurve_eq_of_lipschitz {F : Plane → Plane} {K : ℝ≥0}
    (hF : LipschitzWith K F) {α β : ℝ → Plane}
    (hα : IsIntegralCurve α (fun _ x ↦ F x))
    (hβ : IsIntegralCurve β (fun _ x ↦ F x))
    {t₀ : ℝ} (heq : α t₀ = β t₀) :
    α = β := by
  apply ODE_solution_unique_univ
    (v := fun _ x ↦ F x) (s := fun _ ↦ univ) (K := K) (t₀ := t₀)
  · intro _
    exact hF.lipschitzOnWith
  · intro t
    exact ⟨hα t, mem_univ _⟩
  · intro t
    exact ⟨hβ t, mem_univ _⟩
  · exact heq

theorem integralCurve_periodic_of_eq_of_lipschitz
    {F : Plane → Plane} {K : ℝ≥0} (hF : LipschitzWith K F)
    {β : ℝ → Plane} (hβ : IsIntegralCurve β (fun _ x ↦ F x))
    {a b : ℝ} (heq : β a = β b) :
    Function.Periodic β (a - b) := by
  let βshift : ℝ → Plane := β ∘ fun t ↦ t + (a - b)
  have hshift : IsIntegralCurve βshift (fun _ x ↦ F x) := by
    simpa [βshift, Function.comp_def] using hβ.comp_add (a - b)
  have hshift_b : βshift b = β b := by
    change β (b + (a - b)) = β b
    rw [show b + (a - b) = a by ring, heq]
  have hall : βshift = β :=
    integralCurve_eq_of_lipschitz hF hshift hβ hshift_b
  intro t
  simpa [βshift, Function.comp_def] using congrFun hall t

theorem exists_compactlySupported_lipschitz_extension
    (F : Plane → Plane) (hF : ContDiff ℝ 1 F)
    {s : Set Plane} (hs : Bornology.IsBounded s) :
    ∃ (G : Plane → Plane) (K : ℝ≥0),
      HasCompactSupport G ∧ ContDiff ℝ 1 G ∧
      LipschitzWith K G ∧ EqOn G F s := by
  obtain ⟨R, hR, hsub⟩ := hs.subset_closedBall_lt 0 (0 : Plane)
  let b : ContDiffBump (0 : Plane) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hR
      rIn_lt_rOut := lt_add_one R }
  let G : Plane → Plane := fun x ↦ b x • F x
  have hGcompact : HasCompactSupport G := by
    exact b.hasCompactSupport.smul_right
  have hGdiff : ContDiff ℝ 1 G := by
    exact b.contDiff.smul hF
  obtain ⟨K, hK⟩ :=
    hGdiff.lipschitzWith_of_hasCompactSupport hGcompact one_ne_zero
  refine ⟨G, K, hGcompact, hGdiff, hK, ?_⟩
  intro x hx
  change b x • F x = F x
  rw [b.one_of_mem_closedBall (hsub hx), one_smul]

end Submission.Helpers
