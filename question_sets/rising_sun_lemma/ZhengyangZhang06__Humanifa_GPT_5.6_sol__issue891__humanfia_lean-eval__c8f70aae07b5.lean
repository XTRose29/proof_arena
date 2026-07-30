import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis.RisingSun
open Set MeasureTheory
open scoped Topology

namespace Submission

theorem rising_sun_lemma {a b : ℝ} (_hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    HasRisingSunProperty a b f := by
  classical
  let E : Set ℝ := risingSunSet a b f
  have hE_subset : E ⊆ Ioo a b := by
    intro x hx
    change x ∈ Ioo a b ∧ _ at hx
    exact hx.1
  have hE_open : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    change x ∈ Ioo a b ∧ ∃ t ∈ Icc x b, x < t ∧ f x < f t at hx
    obtain ⟨hxab, t, ht, hxt, hfxt⟩ := hx
    let U : Set ℝ := Ioo a t ∩ f ⁻¹' Iio (f t)
    have hU_open : IsOpen U := by
      apply (hf.mono ?_).isOpen_inter_preimage isOpen_Ioo isOpen_Iio
      intro y hy
      exact ⟨hy.1.le, hy.2.le.trans ht.2⟩
    have hxU : x ∈ U := ⟨⟨hxab.1, hxt⟩, hfxt⟩
    refine Filter.mem_of_superset (hU_open.mem_nhds hxU) ?_
    intro y hy
    change y ∈ Ioo a b ∧ ∃ u ∈ Icc y b, y < u ∧ f y < f u
    exact
      ⟨⟨hy.1.1, hy.1.2.trans_le ht.2⟩, t, ⟨hy.1.2.le, ht.2⟩, hy.1.2, hy.2⟩
  have hE_empty_iff : E = ∅ ↔ AntitoneOn f (Icc a b) := by
    constructor
    · intro hE_empty
      have hanti_Ioc : AntitoneOn f (Ioc a b) := by
        intro x hx y hy hxy
        by_contra hnot
        have hfxy : f x < f y := lt_of_not_ge hnot
        have hxy_strict : x < y := hxy.lt_of_ne fun h => by
          subst y
          exact (lt_irrefl (f x)) hfxy
        have hxE : x ∈ E := by
          change x ∈ Ioo a b ∧ ∃ t ∈ Icc x b, x < t ∧ f x < f t
          exact
            ⟨⟨hx.1, hxy_strict.trans_le hy.2⟩, y, ⟨hxy, hy.2⟩, hxy_strict, hfxy⟩
        rw [hE_empty] at hxE
        exact hxE
      intro x hx y hy hxy
      by_cases hxa : x = a
      · subst x
        by_cases hya : y = a
        · subst y
          exact le_rfl
        · have hay : a < y := lt_of_le_of_ne hy.1 (Ne.symm hya)
          have ha_closure : a ∈ closure (Ioc a y) := by
            rw [closure_Ioc hay.ne]
            exact ⟨le_rfl, hay.le⟩
          have hf_within : ContinuousWithinAt f (Ioc a y) a :=
            (hf a hx).mono fun z hz => ⟨hz.1.le, hz.2.trans hy.2⟩
          exact
            ContinuousWithinAt.closure_le ha_closure continuousWithinAt_const hf_within
              fun z hz =>
                hanti_Ioc ⟨hz.1, hz.2.trans hy.2⟩ ⟨hay, hy.2⟩ hz.2
      · have hax : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
        exact hanti_Ioc ⟨hax, hx.2⟩ ⟨hax.trans_le hxy, hy.2⟩ hxy
    · intro hanti
      apply eq_empty_iff_forall_notMem.2
      intro x hx
      change x ∈ Ioo a b ∧ ∃ t ∈ Icc x b, x < t ∧ f x < f t at hx
      obtain ⟨hxab, t, ht, hxt, hfxt⟩ := hx
      have hxIcc : x ∈ Icc a b := ⟨hxab.1.le, hxab.2.le⟩
      have htIcc : t ∈ Icc a b := ⟨hxab.1.le.trans ht.1, ht.2⟩
      exact (not_lt_of_ge (hanti hxIcc htIcc hxt.le)) hfxt
  change IsOpen E ∧ (E = ∅ ↔ AntitoneOn f (Icc a b)) ∧
    (E.Nonempty → HasRisingSunDecomposition E f)
  refine ⟨hE_open, hE_empty_iff, ?_⟩
  intro _
  let components : Set (Set ℝ) :=
    {C | ∃ x ∈ E, C = connectedComponentIn E x}
  have hcomponent_subset (C : Set ℝ) (hC : C ∈ components) : C ⊆ E := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact connectedComponentIn_subset E x
  have hcomponent_open (C : Set ℝ) (hC : C ∈ components) : IsOpen C := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact hE_open.connectedComponentIn
  have hcomponent_nonempty (C : Set ℝ) (hC : C ∈ components) : C.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hcomponent_pairwise : components.PairwiseDisjoint id := by
    intro C hC D hD hCD
    obtain ⟨x, hx, rfl⟩ := hC
    obtain ⟨y, hy, rfl⟩ := hD
    refine Set.disjoint_left.2 ?_
    intro z hzx hzy
    apply hCD
    exact (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm
  have hcomponents_countable : components.Countable :=
    hcomponent_pairwise.countable_of_isOpen hcomponent_open hcomponent_nonempty
  have hcomponent_interval (C : Set ℝ) (hC : C ∈ components) :
      C = Ioo (sInf C) (sSup C) := by
    obtain ⟨x, hx, rfl⟩ := hC
    apply Helpers.open_preconnected_eq_Ioo hE_open.connectedComponentIn
      (connectedComponentIn_nonempty_iff.2 hx) isPreconnected_connectedComponentIn
    · refine ⟨a, ?_⟩
      intro y hy
      exact (hE_subset (connectedComponentIn_subset E x hy)).1.le
    · refine ⟨b, ?_⟩
      intro y hy
      exact (hE_subset (connectedComponentIn_subset E x hy)).2.le
  have hcomponent_endpoint (C : Set ℝ) (hC : C ∈ components) :
      f (sInf C) ≤ f (sSup C) := by
    let c : ℝ := sInf C
    let d : ℝ := sSup C
    have hC_subset_E : C ⊆ E := hcomponent_subset C hC
    have hC_subset_Ioo : C ⊆ Ioo a b := hC_subset_E.trans hE_subset
    have hC_nonempty : C.Nonempty := hcomponent_nonempty C hC
    have hC_eq : C = Ioo c d := hcomponent_interval C hC
    have hac : a ≤ c := le_csInf hC_nonempty fun y hy => (hC_subset_Ioo hy).1.le
    have hdb : d ≤ b := csSup_le hC_nonempty fun y hy => (hC_subset_Ioo hy).2.le
    obtain ⟨w, hwC⟩ := hC_nonempty
    have hw : w ∈ Ioo c d := hC_eq ▸ hwC
    have hcd : c < d := hw.1.trans hw.2
    have hcIcc : c ∈ Icc a b := ⟨hac, hcd.le.trans hdb⟩
    have hdIcc : d ∈ Icc a b := ⟨hac.trans hcd.le, hdb⟩
    have hd_not_E : d ∉ E := by
      intro hdE
      let D : Set ℝ := connectedComponentIn E d
      have hdD : d ∈ D := mem_connectedComponentIn hdE
      have hD_open : IsOpen D := hE_open.connectedComponentIn
      obtain ⟨l, hl, hlD⟩ :=
        exists_Ioc_subset_of_mem_nhds' (hD_open.mem_nhds hdD) hcd
      let y : ℝ := (l + d) / 2
      have hyld : y ∈ Ioc l d := by
        dsimp [y]
        constructor <;> linarith [hl.2]
      have hyd : y < d := by
        dsimp [y]
        linarith [hl.2]
      have hyD : y ∈ D := hlD hyld
      have hyC : y ∈ C := by
        rw [hC_eq]
        exact ⟨lt_of_le_of_lt hl.1 hyld.1, hyd⟩
      have hCy : C = connectedComponentIn E y := by
        obtain ⟨x, _hx, hC_component⟩ := hC
        exact hC_component.trans (connectedComponentIn_eq (hC_component ▸ hyC))
      have hDy : D = connectedComponentIn E y := by
        exact connectedComponentIn_eq hyD
      have hdC : d ∈ C := (hCy.trans hDy.symm).symm ▸ hdD
      rw [hC_eq] at hdC
      exact (lt_irrefl d) hdC.2
    have hd_future : ∀ t ∈ Icc d b, f t ≤ f d := by
      intro t ht
      by_cases htd : t = d
      · subst t
        exact le_rfl
      · have hdt : d < t := ht.1.lt_of_ne (Ne.symm htd)
        by_contra hnot
        apply hd_not_E
        change d ∈ Ioo a b ∧ ∃ u ∈ Icc d b, d < u ∧ f d < f u
        exact
          ⟨⟨hac.trans_lt hcd, hdt.trans_le ht.2⟩, t, ht, hdt, lt_of_not_ge hnot⟩
    have hinside_le : ∀ y ∈ C, f y ≤ f d := by
      intro y hyC
      have hycd : y ∈ Ioo c d := hC_eq ▸ hyC
      have hyd : y ≤ d := hycd.2.le
      have hIcc_subset : Icc y d ⊆ Icc a b := by
        intro z hz
        exact ⟨hac.trans (hycd.1.le.trans hz.1), hz.2.trans hdb⟩
      obtain ⟨z, hz, hzmax⟩ :=
        isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hyd) (hf.mono hIcc_subset)
      by_cases hzd : z = d
      · subst z
        exact hzmax ⟨le_rfl, hyd⟩
      · have hzd_lt : z < d := hz.2.lt_of_ne hzd
        have hzC : z ∈ C := by
          rw [hC_eq]
          exact ⟨hycd.1.trans_le hz.1, hzd_lt⟩
        have hzE := hC_subset_E hzC
        change z ∈ Ioo a b ∧ ∃ t ∈ Icc z b, z < t ∧ f z < f t at hzE
        obtain ⟨hzab, t, ht, hzt, hfzt⟩ := hzE
        exfalso
        by_cases htd : t ≤ d
        · exact (not_lt_of_ge (hzmax ⟨hz.1.trans hzt.le, htd⟩)) hfzt
        · have hdt : d < t := lt_of_not_ge htd
          have hftd : f t ≤ f d := hd_future t ⟨hdt.le, ht.2⟩
          have hfdz : f d ≤ f z := hzmax ⟨hyd, le_rfl⟩
          exact (not_lt_of_ge (hftd.trans hfdz)) hfzt
    have hc_closure : c ∈ closure C := by
      rw [hC_eq, closure_Ioo hcd.ne]
      exact ⟨le_rfl, hcd.le⟩
    exact
      ContinuousWithinAt.closure_le hc_closure
        ((hf c hcIcc).mono (hC_subset_Ioo.trans Ioo_subset_Icc_self))
        continuousWithinAt_const hinside_le
  letI : Encodable components := hcomponents_countable.toEncodable
  let eligible : ℕ → Prop := fun n =>
    ∃ C : components, Encodable.encode C = n
  let pick : (n : ℕ) → eligible n → components := fun _ h =>
    Classical.choose h
  let K : ℕ → Set ℝ := fun n =>
    if h : eligible n then
      (pick n h).val
    else
      ∅
  have hpick_encode (n : ℕ) (h : eligible n) :
      Encodable.encode (pick n h) = n := by
    exact Classical.choose_spec h
  have hK_of (n : ℕ) (h : eligible n) : K n = (pick n h).val := by
    simp only [K, dif_pos h]
  have hK_not (n : ℕ) (h : ¬eligible n) : K n = ∅ := by
    simp only [K, dif_neg h]
  have hK_component (n : ℕ) : K n = ∅ ∨ K n ∈ components := by
    by_cases h : eligible n
    · right
      rw [hK_of n h]
      exact (pick n h).property
    · left
      exact hK_not n h
  have hK_pairwise : Set.PairwiseDisjoint (Set.univ : Set ℕ) K := by
    intro m hm n hn hmn
    change Disjoint (K m) (K n)
    by_cases hm' : eligible m
    · by_cases hn' : eligible n
      · have hchosen :
          pick m hm' ≠ pick n hn' := by
          intro hEq
          apply hmn
          calc
            m = Encodable.encode (pick m hm') := (hpick_encode m hm').symm
            _ = Encodable.encode (pick n hn') := congrArg Encodable.encode hEq
            _ = n := hpick_encode n hn'
        rw [hK_of m hm', hK_of n hn']
        exact
          hcomponent_pairwise (pick m hm').property (pick n hn').property
            fun hEq => hchosen (Subtype.ext hEq)
      · rw [hK_not n hn']
        exact disjoint_bot_right
    · rw [hK_not m hm']
      exact disjoint_bot_left
  have hK_union : E = ⋃ n : ℕ, K n := by
    apply Subset.antisymm
    · intro y hyE
      let Cy : components :=
        ⟨connectedComponentIn E y, ⟨y, hyE, rfl⟩⟩
      let n : ℕ := Encodable.encode Cy
      have hn : eligible n := ⟨Cy, rfl⟩
      have hchoose : pick n hn = Cy :=
        Encodable.encode_injective (hpick_encode n hn)
      apply mem_iUnion.2
      refine ⟨n, ?_⟩
      rw [hK_of n hn, hchoose]
      exact mem_connectedComponentIn hyE
    · intro y hy
      obtain ⟨n, hyn⟩ := mem_iUnion.1 hy
      rcases hK_component n with hKn | hKn
      · rw [hKn] at hyn
        exact hyn.elim
      · exact hcomponent_subset (K n) hKn hyn
  have hK_interval (n : ℕ) : K n = Ioo (sInf (K n)) (sSup (K n)) := by
    by_cases h : eligible n
    · rw [hK_of n h]
      exact hcomponent_interval (pick n h).val (pick n h).property
    · rw [hK_not n h]
      simp
  have hK_endpoint (n : ℕ) : f (sInf (K n)) ≤ f (sSup (K n)) := by
    by_cases h : eligible n
    · rw [hK_of n h]
      exact hcomponent_endpoint (pick n h).val (pick n h).property
    · rw [hK_not n h]
      simp
  refine ⟨fun n => sInf (K n), fun n => sSup (K n), ?_, ?_, hK_endpoint⟩
  · exact hK_union.trans (Set.iUnion_congr hK_interval)
  · intro m hm n hn hmn
    change Disjoint (Ioo (sInf (K m)) (sSup (K m)))
      (Ioo (sInf (K n)) (sSup (K n)))
    rw [← hK_interval m, ← hK_interval n]
    exact hK_pairwise hm hn hmn

end Submission
