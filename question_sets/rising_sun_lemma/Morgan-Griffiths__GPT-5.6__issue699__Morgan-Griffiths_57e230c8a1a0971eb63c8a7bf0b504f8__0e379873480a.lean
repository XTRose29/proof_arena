import Mathlib

namespace Submission

namespace LeanEval.Analysis.RisingSun

/-!
# Riesz's rising sun lemma

`rising_sun_lemma`: every continuous real function on a compact interval has the
rising-sun property (the shadow set is open, empty iff the function is
antitone, and otherwise decomposes into disjoint open intervals with endpoint
inequality `f(c) ≤ f(d)`). Trusted helpers (`risingSunSet`,
`HasRisingSunDecomposition`, `HasRisingSunProperty`) are non-holes. Mathlib has
the monotone-a.e.-differentiable consequence but not the rising-sun lemma.
Category-(b) candidate from §163 of the Knill survey.
-/

open Set MeasureTheory
open scoped Topology

/-- Points of `(a,b)` lower than some later point. -/
def risingSunSet (a b : ℝ) (f : ℝ → ℝ) : Set ℝ :=
  {x | x ∈ Ioo a b ∧ ∃ t ∈ Icc x b, x < t ∧ f x < f t}

/-- A countable disjoint open-interval decomposition with the endpoint
inequality `f(c_n) ≤ f(d_n)`. -/
def HasRisingSunDecomposition (E : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ c d : ℕ → ℝ,
    E = ⋃ n : ℕ, Ioo (c n) (d n) ∧
    (Set.PairwiseDisjoint (Set.univ : Set ℕ) fun n => Ioo (c n) (d n)) ∧
    ∀ n : ℕ, f (c n) ≤ f (d n)

/-- The rising-sun property on `[a,b]`. -/
def HasRisingSunProperty (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  IsOpen (risingSunSet a b f) ∧
  (risingSunSet a b f = ∅ ↔ AntitoneOn f (Icc a b)) ∧
  ((risingSunSet a b f).Nonempty → HasRisingSunDecomposition (risingSunSet a b f) f)



end LeanEval.Analysis.RisingSun

open LeanEval.Analysis.RisingSun
open Set MeasureTheory
open scoped Topology
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/


-- Some interval facts about components of a bounded open subset of the line.
noncomputable section
open Classical Filter

private abbrev SunComp (E : Set ℝ) (x : ℝ) : Set ℝ := connectedComponentIn E x

private lemma sunComp_open {E : Set ℝ} (hE : IsOpen E) (x : ℝ) :
    IsOpen (SunComp E x) :=
  hE.connectedComponentIn

private lemma sunComp_interval {E : Set ℝ} (hE : IsOpen E) {x : ℝ} (hx : x ∈ E)
    (hbelow : BddBelow E) (habove : BddAbove E) :
    SunComp E x = Ioo (sInf (SunComp E x)) (sSup (SunComp E x)) := by
  let C : Set ℝ := SunComp E x
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hne : C.Nonempty := ⟨x, hxC⟩
  have hsub : C ⊆ E := connectedComponentIn_subset _ _
  have hb : BddBelow C := hbelow.mono hsub
  have ha : BddAbove C := habove.mono hsub
  have hconn : IsConnected C :=
    ⟨hne, isPreconnected_connectedComponentIn⟩
  have hinside : Ioo (sInf C) (sSup C) ⊆ C :=
    hconn.Ioo_csInf_csSup_subset hb ha
  have hopen : IsOpen C := sunComp_open hE x
  have hleft_right : ∀ z ∈ C, ∃ u ∈ C, u < z ∧ ∃ v ∈ C, z < v := by
    intro z hz
    rcases (Metric.isOpen_iff.1 hopen z hz) with ⟨ε, hε, hball⟩
    let u : ℝ := z - ε/2
    let v : ℝ := z + ε/2
    have hu_ball : u ∈ Metric.ball z ε := by
      have : |u - z| < ε := by
        dsimp [u]
        rw [sub_sub_cancel_left]
        rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ ε/2)]
        linarith
      simpa [Real.dist_eq] using this
    have hv_ball : v ∈ Metric.ball z ε := by
      have : |v - z| < ε := by
        dsimp [v]
        rw [add_sub_cancel_left]
        rw [abs_of_nonneg (by positivity : 0 ≤ ε/2)]
        linarith
      simpa [Real.dist_eq] using this
    refine ⟨u, hball hu_ball, by dsimp [u]; linarith, v, hball hv_ball, by dsimp [v]; linarith⟩
  change C = Ioo (sInf C) (sSup C)
  apply subset_antisymm ?_ hinside
  intro z hz
  rcases hleft_right z hz with ⟨u, hu, huz, v, hv, hzv⟩
  exact ⟨lt_of_le_of_lt (csInf_le hb hu) huz, lt_of_lt_of_le hzv (le_csSup ha hv)⟩


private lemma sunComp_endpoints_not_mem {E : Set ℝ} (hE : IsOpen E)
    (hbelow : BddBelow E) (habove : BddAbove E) {x : ℝ} (hx : x ∈ E) :
    sInf (SunComp E x) ∉ E ∧ sSup (SunComp E x) ∉ E := by
  let C : Set ℝ := SunComp E x
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hsub : C ⊆ E := connectedComponentIn_subset _ _
  have hb : BddBelow C := hbelow.mono hsub
  have ha : BddAbove C := habove.mono hsub
  have hCeq : C = Ioo (sInf C) (sSup C) := sunComp_interval hE hx hbelow habove
  have hx' : x ∈ Ioo (sInf C) (sSup C) := hCeq ▸ hxC
  have hcd : sInf C < sSup C := lt_trans hx'.1 hx'.2
  have hpre : IsClosed ((Subtype.val : E → ℝ) ⁻¹' C) := by
    rw [show C = (Subtype.val : E → ℝ) '' connectedComponent (⟨x,hx⟩ : E) from
      connectedComponentIn_eq_image hx]
    rw [Set.preimage_image_eq _ Subtype.val_injective]
    exact isClosed_connectedComponent
  have hrel : E ∩ closure (E ∩ C) ⊆ C :=
    (isClosed_preimage_val).1 hpre
  have hrel' : E ∩ closure C ⊆ C := by
    simpa [inter_eq_self_of_subset_right hsub] using hrel
  have hcl_eq : closure C = Icc (sInf C) (sSup C) := by
    calc
      closure C = closure (Ioo (sInf C) (sSup C)) := congrArg closure hCeq
      _ = Icc (sInf C) (sSup C) := closure_Ioo hcd.ne
  have hiff (z : ℝ) : z ∈ C ↔ z ∈ Ioo (sInf C) (sSup C) :=
    Set.ext_iff.mp hCeq z
  have hcl_left : sInf C ∈ closure C :=
    (Set.ext_iff.mp hcl_eq _).2 ⟨le_rfl, hcd.le⟩
  have hcl_right : sSup C ∈ closure C :=
    (Set.ext_iff.mp hcl_eq _).2 ⟨hcd.le, le_rfl⟩
  constructor
  · intro h
    change sInf C ∈ E at h
    have hm : sInf C ∈ C := hrel' ⟨h, hcl_left⟩
    have hm' := (hiff _).1 hm
    exact (lt_irrefl _) hm'.1
  · intro h
    change sSup C ∈ E at h
    have hm : sSup C ∈ C := hrel' ⟨h, hcl_right⟩
    have hm' := (hiff _).1 hm
    exact (lt_irrefl _) hm'.2

private lemma sunComp_endpoints_bounds {a b : ℝ} {E : Set ℝ}
    (hsubE : E ⊆ Ioo a b) {x : ℝ} (hx : x ∈ E) :
    sInf (SunComp E x) ∈ Icc a b ∧ sSup (SunComp E x) ∈ Icc a b := by
  let C : Set ℝ := SunComp E x
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hne : C.Nonempty := ⟨x, hxC⟩
  have hsub : C ⊆ Ioo a b := (connectedComponentIn_subset E x) |>.trans hsubE
  have hb : BddBelow C := ⟨a, fun z hz => (hsub hz).1.le⟩
  have ha : BddAbove C := ⟨b, fun z hz => (hsub hz).2.le⟩
  have hAc : a ≤ sInf C := le_csInf hne (fun z hz => (hsub hz).1.le)
  have hcb : sInf C ≤ b :=
    le_trans (csInf_le hb hxC) (hsub hxC).2.le
  have hAd : a ≤ sSup C :=
    le_trans (hsub hxC).1.le (le_csSup ha hxC)
  have hdb : sSup C ≤ b := csSup_le hne (fun z hz => (hsub hz).2.le)
  exact ⟨⟨hAc,hcb⟩, ⟨hAd,hdb⟩⟩


private lemma risingSun_open {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    IsOpen (risingSunSet a b f) := by
  have hf' : ContinuousOn f (Ioo a b) := hf.mono Ioo_subset_Icc_self
  let U : ℝ → Set ℝ := fun t => (Ioo a b ∩ f ⁻¹' Iio (f t)) ∩ Iio t
  have hU : ∀ t, IsOpen (U t) := by
    intro t
    dsimp [U]
    exact (hf'.isOpen_inter_preimage isOpen_Ioo isOpen_Iio).inter isOpen_Iio
  have heq : risingSunSet a b f = ⋃ t : (Icc a b : Set ℝ), U (t:ℝ) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxab, t, ht, hxt, hft⟩
      have ht' : t ∈ Icc a b := ⟨le_trans hxab.1.le ht.1, ht.2⟩
      have hxU : x ∈ U t := ⟨⟨hxab, hft⟩, hxt⟩
      exact Set.mem_iUnion.2 ⟨(⟨t, ht'⟩ : (Icc a b : Set ℝ)), hxU⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨t, ht⟩
      rcases ht with ⟨⟨hxab, hft⟩, hxt⟩
      exact ⟨hxab, (t:ℝ), ⟨le_of_lt hxt, t.property.2⟩, hxt, hft⟩
  rw [heq]
  exact isOpen_iUnion (fun t => hU _)


private lemma risingSun_empty_iff {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    risingSunSet a b f = ∅ ↔ AntitoneOn f (Icc a b) := by
  constructor
  · intro hzero
    intro x hx y hy hxy
    rcases lt_or_eq_of_le hxy with hxy' | rfl
    · by_cases hxa : x = a
      · subst x
        -- continuity from the right at the left endpoint
        by_contra hnot
        have hlt : f a < f y := lt_of_not_ge hnot
        have hcont := hf a (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
        have hpre : f ⁻¹' Iio (f y) ∈ 𝓝[Icc a b] a :=
          hcont.preimage_mem_nhdsWithin (isOpen_Iio.mem_nhds hlt)
        rcases Metric.mem_nhdsWithin_iff.mp hpre with ⟨ε, hε, hsub⟩
        have haup : a < min (a + ε) y := lt_min (by linarith) hxy'
        rcases exists_between haup with ⟨z, haz, hzup⟩
        have hzy : z < y := lt_of_lt_of_le hzup (min_le_right _ _)
        have hze : z < a + ε := lt_of_lt_of_le hzup (min_le_left _ _)
        have hzball : z ∈ Metric.ball a ε := by
          have h' : |z-a| < ε := by
            rw [abs_of_pos (sub_pos.mpr haz)]
            linarith
          simpa [Real.dist_eq] using h'
        have hzcc : z ∈ Icc a b :=
          ⟨haz.le, (lt_of_lt_of_le hzy hy.2).le⟩
        have hzlt : f z < f y := hsub ⟨hzball, hzcc⟩
        have hzoo : z ∈ Ioo a b :=
          ⟨haz, lt_of_lt_of_le hzy hy.2⟩
        have hzE : z ∈ risingSunSet a b f :=
          ⟨hzoo, y, ⟨hzy.le, hy.2⟩, hzy, hzlt⟩
        rw [hzero] at hzE
        exact hzE.elim
      · have hax : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
        have hxb : x < b := lt_of_lt_of_le hxy' hy.2
        apply le_of_not_gt
        intro hlt
        have hxE : x ∈ risingSunSet a b f :=
          ⟨⟨hax, hxb⟩, y, ⟨hxy'.le, hy.2⟩, hxy', hlt⟩
        rw [hzero] at hxE
        exact hxE.elim
    · exact le_rfl
  · intro hanti
    apply Set.subset_empty_iff.mp
    intro x hx
    rcases hx with ⟨hxab, t, ht, hxt, hft⟩
    have hx' : x ∈ Icc a b := ⟨hxab.1.le, hxab.2.le⟩
    have ht' : t ∈ Icc a b := ⟨le_trans hxab.1.le ht.1, ht.2⟩
    have hge := hanti hx' ht' hxt.le
    exact (not_lt_of_ge hge) hft


private lemma risingSun_component_values {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {x : ℝ}
    (hx : x ∈ risingSunSet a b f) :
    f (sInf (SunComp (risingSunSet a b f) x)) ≤
      f (sSup (SunComp (risingSunSet a b f) x)) := by
  let E : Set ℝ := risingSunSet a b f
  let C : Set ℝ := SunComp E x
  let c : ℝ := sInf C
  let d : ℝ := sSup C
  change x ∈ E at hx
  have hE : IsOpen E := risingSun_open hf
  have hsubE : E ⊆ Ioo a b := by intro z hz; exact hz.1
  have hbE : BddBelow E := ⟨a, fun z hz => (hsubE hz).1.le⟩
  have haE : BddAbove E := ⟨b, fun z hz => (hsubE hz).2.le⟩
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hsubC : C ⊆ E := connectedComponentIn_subset _ _
  have hCeq : C = Ioo c d := sunComp_interval hE hx hbE haE
  have hiff (z : ℝ) : z ∈ C ↔ z ∈ Ioo c d := Set.ext_iff.mp hCeq z
  have hxint : x ∈ Ioo c d := (hiff x).1 hxC
  have hcd : c < d := lt_trans hxint.1 hxint.2
  have hbounds := sunComp_endpoints_bounds (a:=a) (b:=b) hsubE hx
  change c ∈ Icc a b ∧ d ∈ Icc a b at hbounds
  rcases hbounds with ⟨hcbd, hdbd⟩
  have hnot := sunComp_endpoints_not_mem hE hbE haE hx
  change c ∉ E ∧ d ∉ E at hnot
  have had : a < d := lt_trans (hsubE (hsubC hxC)).1 hxint.2
  -- points after the right end never rise above its value
  have hright : ∀ t ∈ Icc d b, f t ≤ f d := by
    intro t ht
    by_cases hdB : d = b
    · have ht' : t = d := le_antisymm (hdB ▸ ht.2) ht.1
      simpa [ht']
    · by_cases htd : t = d
      · subst t; exact le_rfl
      · have hdb : d < b := lt_of_le_of_ne hdbd.2 hdB
        have hdt : d < t := lt_of_le_of_ne ht.1 (Ne.symm htd)
        apply le_of_not_gt
        intro hlt
        have hdE : d ∈ E :=
          ⟨⟨had, hdb⟩,
            t, ⟨hdt.le, ht.2⟩, hdt, hlt⟩
        exact hnot.2 hdE
  have hpoint : ∀ z ∈ C, f z ≤ f d := by
    intro z hz
    have hzE : z ∈ E := hsubC hz
    rcases hzE.2 with ⟨w, hw, hzw, hfw⟩
    have hzab : z ∈ Icc a b :=
      ⟨(hsubE (hsubC hz)).1.le, (hsubE (hsubC hz)).2.le⟩
    have hnon : (Icc z b : Set ℝ).Nonempty := nonempty_Icc.mpr hzab.2
    have hcont : ContinuousOn f (Icc z b) := by
      apply hf.mono
      intro u hu
      exact ⟨le_trans hzab.1 hu.1, hu.2⟩
    rcases isCompact_Icc.exists_isMaxOn hnon hcont with ⟨m, hm, hmax⟩
    have hw' : w ∈ Icc z b := hw
    have hwm : f w ≤ f m := hmax hw'
    have hfm : f z < f m := lt_of_lt_of_le hfw hwm
    have hzmle : z ≤ m := hm.1
    have hzm : z < m := lt_of_le_of_ne hzmle (fun heq => (ne_of_lt hfm) (congrArg f heq))
    have hdm : d ≤ m := by
      apply le_of_not_gt
      intro hmd
      have hzint : z ∈ Ioo c d := (hiff z).1 hz
      have hmC : m ∈ C := (hiff m).2 ⟨lt_trans hzint.1 hzm, hmd⟩
      have hmE : m ∈ E := hsubC hmC
      rcases hmE.2 with ⟨v, hv, hmv, hfv⟩
      have hv' : v ∈ Icc z b := ⟨le_trans hzmle hv.1, hv.2⟩
      have hvmax : f v ≤ f m := hmax hv'
      exact (not_lt_of_ge hvmax) hfv
    have hm_le : f m ≤ f d := hright m ⟨hdm, hm.2⟩
    exact le_trans (le_of_lt hfm) hm_le
  have hclosed : IsClosed (Icc a b ∩ f ⁻¹' Iic (f d)) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsubset : C ⊆ Icc a b ∩ f ⁻¹' Iic (f d) := by
    intro z hz
    exact ⟨⟨(hsubE (hsubC hz)).1.le, (hsubE (hsubC hz)).2.le⟩, hpoint z hz⟩
  have hcl_eq : closure C = Icc c d := by
    calc
      closure C = closure (Ioo c d) := congrArg closure hCeq
      _ = Icc c d := closure_Ioo hcd.ne
  have hccl : c ∈ closure C :=
    (Set.ext_iff.mp hcl_eq _).2 ⟨le_rfl, hcd.le⟩
  have hc_in : c ∈ Icc a b ∩ f ⁻¹' Iic (f d) :=
    closure_minimal hsubset hclosed hccl
  exact hc_in.2


private lemma open_bounded_decomposition {a b : ℝ} {E : Set ℝ} (hE : IsOpen E)
    (hsubE : E ⊆ Ioo a b) {f : ℝ → ℝ}
    (hval : ∀ x ∈ E,
      f (sInf (SunComp E x)) ≤ f (sSup (SunComp E x))) :
    HasRisingSunDecomposition E f := by
  classical
  have hbE : BddBelow E := ⟨a, fun z hz => (hsubE hz).1.le⟩
  have haE : BddAbove E := ⟨b, fun z hz => (hsubE hz).2.le⟩
  let q : ℕ → ℚ := Classical.choose (exists_surjective_nat ℚ)
  have hq : Function.Surjective q := Classical.choose_spec (exists_surjective_nat ℚ)
  let r : ℕ → ℝ := fun n => (q n : ℝ)
  let mark : ℕ → Prop := fun n => r n ∈ E ∧ ∀ m < n, r m ∉ SunComp E (r n)
  letI : DecidablePred mark := Classical.decPred _
  let cc : ℕ → ℝ := fun n => if mark n then sInf (SunComp E (r n)) else a
  let dd : ℕ → ℝ := fun n => if mark n then sSup (SunComp E (r n)) else a
  have hinterval {n : ℕ} (hn : mark n) :
      Ioo (cc n) (dd n) = SunComp E (r n) := by
    have he := sunComp_interval hE hn.1 hbE haE
    change Ioo (if mark n then sInf (SunComp E (r n)) else a)
      (if mark n then sSup (SunComp E (r n)) else a) = _
    simp only [if_pos hn]
    exact he.symm
  have hempty {n : ℕ} (hn : ¬ mark n) : Ioo (cc n) (dd n) = (∅ : Set ℝ) := by
    dsimp [cc, dd]
    simp [hn]
  refine ⟨cc, dd, ?_, ?_, ?_⟩
  · ext z
    constructor
    · intro hz
      let C : Set ℝ := SunComp E z
      have hzC : z ∈ C := mem_connectedComponentIn hz
      have hzsub : C ⊆ E := connectedComponentIn_subset _ _
      have hzeq : C = Ioo (sInf C) (sSup C) := sunComp_interval hE hz hbE haE
      have hzint : z ∈ Ioo (sInf C) (sSup C) := (Set.ext_iff.mp hzeq z).1 hzC
      have hcd : sInf C < sSup C := lt_trans hzint.1 hzint.2
      rcases exists_rat_btwn hcd with ⟨u, hu1, hu2⟩
      rcases hq u with ⟨n, hnq⟩
      have hrn : r n = (u : ℝ) := by dsimp [r]; rw [hnq]
      have hnC : r n ∈ C := (Set.ext_iff.mp hzeq _).2 <| by
        simpa [hrn] using And.intro hu1 hu2
      have hex : ∃ n, r n ∈ C := ⟨n, hnC⟩
      let k : ℕ := Nat.find hex
      have hkC : r k ∈ C := Nat.find_spec hex
      have hEq : C = SunComp E (r k) := connectedComponentIn_eq hkC
      have hkmark : mark k := by
        constructor
        · exact hzsub hkC
        · intro m hm hmem
          have hmC : r m ∈ C := by
            have : r m ∈ SunComp E (r k) := hmem
            exact (Set.ext_iff.mp hEq _).2 this
          exact (Nat.find_min hex hm) hmC
      have hzComp : z ∈ SunComp E (r k) := (Set.ext_iff.mp hEq z).1 hzC
      have hzintk : z ∈ Ioo (cc k) (dd k) := by
        have hi := hinterval hkmark
        exact (Set.ext_iff.mp hi z).2 hzComp
      exact Set.mem_iUnion.2 ⟨k, hzintk⟩
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨n, hn⟩
      by_cases hmn : mark n
      · have hcMem : z ∈ SunComp E (r n) :=
          (Set.ext_iff.mp (hinterval hmn) z).1 hn
        exact connectedComponentIn_subset _ _ hcMem
      · have : z ∈ (∅ : Set ℝ) := (Set.ext_iff.mp (hempty hmn) z).1 hn
        exact this.elim
  · -- distinct surviving components are disjoint
    intro i hi j hj hij
    change Disjoint (Ioo (cc i) (dd i)) (Ioo (cc j) (dd j))
    by_cases hmi : mark i
    · by_cases hmj : mark j
      · apply Set.disjoint_left.2
        intro z hzi hzj
        have hzi' : z ∈ SunComp E (r i) :=
          (Set.ext_iff.mp (hinterval hmi) z).1 hzi
        have hzj' : z ∈ SunComp E (r j) :=
          (Set.ext_iff.mp (hinterval hmj) z).1 hzj
        have heq : SunComp E (r i) = SunComp E (r j) :=
          (connectedComponentIn_eq hzi').trans (connectedComponentIn_eq hzj').symm
        rcases lt_or_gt_of_ne hij with hij' | hji'
        · have hself : r i ∈ SunComp E (r i) := mem_connectedComponentIn hmi.1
          have hbad : r i ∈ SunComp E (r j) := (Set.ext_iff.mp heq _).1 hself
          exact hmj.2 i hij' hbad
        · have hself : r j ∈ SunComp E (r j) := mem_connectedComponentIn hmj.1
          have hbad : r j ∈ SunComp E (r i) := (Set.ext_iff.mp heq _).2 hself
          exact hmi.2 j hji' hbad
      · have he : Ioo (cc j) (dd j) = (∅ : Set ℝ) := hempty hmj
        rw [he]
        exact Set.disjoint_empty _
    · have he : Ioo (cc i) (dd i) = (∅ : Set ℝ) := hempty hmi
      rw [he]
      exact empty_disjoint _
  · intro n
    by_cases hn : mark n
    · have hv := hval (r n) hn.1
      simpa [cc, dd, hn] using hv
    · simp [cc, dd, hn]

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem rising_sun_lemma {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    HasRisingSunProperty a b f :=
/-ResultProofBegin-/by
  refine ⟨risingSun_open hf, risingSun_empty_iff hab hf, ?_⟩
  intro _hne
  apply open_bounded_decomposition (risingSun_open hf) (fun z hz => hz.1)
  intro x hx
  exact risingSun_component_values hab hf hx
/-ResultProofEnd-/
/-ResultEnd-/

end
end Submission
