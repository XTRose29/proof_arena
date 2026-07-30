import Submission.Helpers

open LeanEval.ComplexAnalysis.FatouJuliaProblem
open Function

namespace Submission.Connected

noncomputable section

open Polynomial Topology

lemma connectedSpace_of_open_involution_quotient
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ConnectedSpace Y]
    (q : X → Y) (hq_open : IsOpenMap q) (hq_surjective : Surjective q)
    (e : X ≃ₜ X) (he_e : ∀ x, e (e x) = x)
    (hq_fiber : ∀ x y, q y = q x → y = x ∨ y = e x)
    (x₀ : X) (he_x₀ : e x₀ = x₀) : ConnectedSpace X := by
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨x₀⟩, ?_⟩
  intro A hA
  have hmem_imp_univ : ∀ B : Set X, IsClopen B → x₀ ∈ B → B = Set.univ := by
    intro B hB hx₀
    let D := B ∩ e ⁻¹' B
    have hD : IsClopen D := hB.inter (hB.preimage e.continuous)
    have hx₀D : x₀ ∈ D := by
      refine ⟨hx₀, ?_⟩
      simpa only [Set.mem_preimage, he_x₀] using hx₀
    have hD_e (x : X) : x ∈ D ↔ e x ∈ D := by
      change (x ∈ B ∧ e x ∈ B) ↔ (e x ∈ B ∧ e (e x) ∈ B)
      rw [he_e]
      exact and_comm
    have hD_saturated {x y : X} (hxy : q y = q x) (hx : x ∈ D) : y ∈ D := by
      rcases hq_fiber x y hxy with rfl | rfl
      · exact hx
      · exact (hD_e x).mp hx
    have hcompl_image : (q '' D)ᶜ = q '' Dᶜ := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, rfl⟩ := hq_surjective y
        refine ⟨x, ?_, rfl⟩
        intro hxD
        exact hy ⟨x, hxD, rfl⟩
      · rintro ⟨x, hxD, rfl⟩ hqx
        obtain ⟨y, hyD, hyx⟩ := hqx
        exact hxD (hD_saturated hyx.symm hyD)
    have hqD : IsClopen (q '' D) := by
      refine ⟨?_, hq_open D hD.isOpen⟩
      rw [← isOpen_compl_iff, hcompl_image]
      exact hq_open Dᶜ hD.compl.isOpen
    have hqD_univ : q '' D = Set.univ :=
      hqD.eq_univ ⟨q x₀, x₀, hx₀D, rfl⟩
    apply Set.eq_univ_of_forall
    intro x
    have hqx : q x ∈ q '' D := by rw [hqD_univ]; exact Set.mem_univ _
    obtain ⟨y, hyD, hyx⟩ := hqx
    exact (hD_saturated hyx.symm hyD).1
  by_cases hx₀ : x₀ ∈ A
  · exact Or.inr (hmem_imp_univ A hA hx₀)
  · left
    have hAc : Aᶜ = Set.univ := hmem_imp_univ Aᶜ hA.compl hx₀
    simpa using congrArg (fun s : Set X ↦ sᶜ) hAc

lemma isOpenMap_tc (c : ℂ) : IsOpenMap (Tc c) := by
  convert ((Polynomial.X ^ 2 + Polynomial.C c).isOpenQuotientMap_eval (by simp)).isOpenMap using 1
  funext z
  simp [Tc]

lemma isConnected_preimage_tc {c : ℂ} {s : Set ℂ} (hs : IsConnected s) (hc : c ∈ s) :
    IsConnected (Tc c ⁻¹' s) := by
  let q : (Tc c ⁻¹' s) → s := fun z ↦ ⟨Tc c z.1, z.2⟩
  let negX : (Tc c ⁻¹' s) → (Tc c ⁻¹' s) := fun z ↦
    ⟨-z.1, by
      change Tc c (-z.1) ∈ s
      rw [show Tc c (-z.1) = Tc c z.1 by simp [Tc]]
      exact z.2⟩
  have hnegX_involutive : Involutive negX := by
    intro z
    apply Subtype.ext
    exact neg_neg z.1
  have hnegX_continuous : Continuous negX := by
    apply Continuous.subtype_mk (continuous_neg.comp continuous_subtype_val)
  let e : (Tc c ⁻¹' s) ≃ₜ (Tc c ⁻¹' s) := {
    toFun := negX
    invFun := negX
    left_inv := hnegX_involutive
    right_inv := hnegX_involutive
    continuous_toFun := hnegX_continuous
    continuous_invFun := hnegX_continuous
  }
  let x₀ : (Tc c ⁻¹' s) := ⟨0, by simpa [Tc] using hc⟩
  letI : ConnectedSpace s := isConnected_iff_connectedSpace.mp hs
  have hq_open : IsOpenMap q := by
    change IsOpenMap (s.restrictPreimage (Tc c))
    exact (isOpenMap_tc c).restrictPreimage s
  have hq_surjective : Surjective q := by
    rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y - c) zero_lt_two
    refine ⟨⟨z, ?_⟩, Subtype.ext ?_⟩
    · simpa [Tc, hz] using hy
    · simp [q, Tc, hz]
  have he_e (x : Tc c ⁻¹' s) : e (e x) = x := by
    change negX (negX x) = x
    exact hnegX_involutive x
  have hq_fiber (x y : Tc c ⁻¹' s) (hxy : q y = q x) : y = x ∨ y = e x := by
    have hsq : y.1 ^ 2 = x.1 ^ 2 := by
      have hval := congrArg Subtype.val hxy
      simpa [q, Tc] using congrArg (· - c) hval
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (by simpa [e] using h))
  have he_x₀ : e x₀ = x₀ := by
    change negX x₀ = x₀
    apply Subtype.ext
    simp [negX, x₀]
  exact isConnected_iff_connectedSpace.mpr
    (connectedSpace_of_open_involution_quotient q hq_open hq_surjective e he_e
      hq_fiber x₀ he_x₀)

lemma exists_subset_open_of_iInter_subset
    {X : Type*} [TopologicalSpace X] (t : ℕ → Set X)
    (htd : ∀ n, t (n + 1) ⊆ t n) (ht₀ : IsCompact (t 0)) (htc : ∀ n, IsClosed (t n))
    {u : Set X} (hu : IsOpen u) (hsub : (⋂ n, t n) ⊆ u) : ∃ n, t n ⊆ u := by
  by_contra! h
  let s : ℕ → Set X := fun n ↦ t n ∩ uᶜ
  have hsd : ∀ n, s (n + 1) ⊆ s n := fun n ↦
    Set.inter_subset_inter_left _ (htd n)
  have hsn : ∀ n, (s n).Nonempty := by
    intro n
    obtain ⟨x, hxt, hxu⟩ := Set.not_subset.mp (h n)
    exact ⟨x, hxt, hxu⟩
  have hs₀ : IsCompact (s 0) := ht₀.inter_right hu.isClosed_compl
  have hsc : ∀ n, IsClosed (s n) := fun n ↦ (htc n).inter hu.isClosed_compl
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed s hsd hsn hs₀ hsc
  have hxt : x ∈ ⋂ n, t n := Set.mem_iInter.mpr fun n ↦ (Set.mem_iInter.mp hx n).1
  exact (Set.mem_iInter.mp hx 0).2 (hsub hxt)

lemma isConnected_iInter_of_sequence
    {X : Type*} [TopologicalSpace X] [NormalSpace X] (t : ℕ → Set X)
    (htd : ∀ n, t (n + 1) ⊆ t n) (ht₀ : IsCompact (t 0)) (htc : ∀ n, IsClosed (t n))
    (ht_conn : ∀ n, IsConnected (t n)) : IsConnected (⋂ n, t n) := by
  have hnonempty : (⋂ n, t n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd
      (fun n ↦ (ht_conn n).nonempty) ht₀ htc
  have hclosed : IsClosed (⋂ n, t n) := isClosed_iInter htc
  refine ⟨hnonempty, (isPreconnected_iff_subset_of_fully_disjoint_closed hclosed).2 ?_⟩
  intro a b ha hb hab hdisj
  obtain ⟨u, v, hu, hv, hau, hbv, huv⟩ := normal_separation ha hb hdisj
  have hinter_subset : (⋂ n, t n) ⊆ u ∪ v := fun x hx ↦
    (hab hx).elim (fun hxa ↦ Or.inl (hau hxa)) (fun hxb ↦ Or.inr (hbv hxb))
  obtain ⟨n, hn⟩ := exists_subset_open_of_iInter_subset t htd ht₀ htc
    (hu.union hv) hinter_subset
  have hnuv : t n ∩ (u ∩ v) = ∅ := by
    rw [huv.inter_eq, Set.inter_empty]
  rcases (isPreconnected_iff_subset_of_disjoint.mp (ht_conn n).isPreconnected)
      u v hu hv hn hnuv with htu | htv
  · left
    intro x hx
    have hxu := htu (Set.mem_iInter.mp hx n)
    rcases hab hx with hxa | hxb
    · exact hxa
    · exact (Set.disjoint_left.mp huv hxu (hbv hxb)).elim
  · right
    intro x hx
    have hxv := htv (Set.mem_iInter.mp hx n)
    rcases hab hx with hxa | hxb
    · exact (Set.disjoint_left.mp huv (hau hxa) hxv).elim
    · exact hxb

def filledApprox (c : ℂ) (n : ℕ) : Set ℂ :=
  (Tc c)^[n] ⁻¹' Metric.closedBall 0 (Helpers.escapeRadius c)

lemma filledApprox_succ (c : ℂ) (n : ℕ) :
    filledApprox c (n + 1) = Tc c ⁻¹' filledApprox c n := by
  ext z
  simp only [filledApprox, Set.mem_preimage, Function.iterate_succ_apply]

lemma isClosed_filledApprox (c : ℂ) (n : ℕ) : IsClosed (filledApprox c n) := by
  apply Metric.isClosed_closedBall.preimage
  exact (by unfold Tc; fun_prop : Continuous (Tc c)).iterate n

lemma filledApprox_succ_subset (c : ℂ) (n : ℕ) :
    filledApprox c (n + 1) ⊆ filledApprox c n := by
  intro z hz
  simp only [filledApprox, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hz ⊢
  by_contra! hn
  have hstep := Helpers.norm_add_one_lt_norm_tc_of_escape (c := c)
    (z := (Tc c)^[n] z) hn
  have hstep' :
      ‖(Tc c)^[n] z‖ + 1 < ‖(Tc c)^[n + 1] z‖ := by
    simpa only [Function.iterate_succ_apply'] using hstep
  exact (not_lt_of_ge hz) (hn.trans (lt_add_of_pos_right _ zero_lt_one) |>.trans hstep')

lemma isCompact_filledApprox_zero (c : ℂ) : IsCompact (filledApprox c 0) := by
  simpa [filledApprox] using isCompact_closedBall (0 : ℂ) (Helpers.escapeRadius c)

lemma isConnected_filledApprox_of_mem_mandelbrot {c : ℂ} (hc : c ∈ Mandelbrot) :
    ∀ n, IsConnected (filledApprox c n) := by
  intro n
  induction n with
  | zero =>
      simpa [filledApprox] using
        (Metric.isConnected_closedBall (x := (0 : ℂ))
          (show 0 ≤ Helpers.escapeRadius c by
            dsimp [Helpers.escapeRadius]
            positivity))
  | succ n ih =>
      rw [filledApprox_succ]
      apply isConnected_preimage_tc ih
      rw [filledApprox, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
      have hcrit := Helpers.norm_criticalOrbit_le_escapeRadius_of_mem_mandelbrot hc n.succ
      simpa only [Function.iterate_succ_apply, Tc, zero_pow (by norm_num : 2 ≠ 0), zero_add]
        using hcrit

lemma isConnected_filledJulia_of_mem_mandelbrot {c : ℂ} (hc : c ∈ Mandelbrot) :
    IsConnected (FilledJulia c) := by
  rw [Helpers.filledJulia_eq_iInter_closedBall]
  change IsConnected (⋂ n, filledApprox c n)
  exact isConnected_iInter_of_sequence (filledApprox c) (filledApprox_succ_subset c)
    (isCompact_filledApprox_zero c) (isClosed_filledApprox c)
    (isConnected_filledApprox_of_mem_mandelbrot hc)

end

end Submission.Connected
