import Mathlib
import Submission.Helpers

open Filter
open scoped BigOperators InnerProductSpace RealInnerProductSpace
open Submission.Helpers

private def SimplexStructure {V : Type*} (s : Finset V)
    (t : Finset (Finset V)) : Prop :=
  t.card = s.card ∧
    (∀ q ∈ t, q.Nonempty ∧ q ⊆ s) ∧
    ∀ q ∈ t, ∀ r ∈ t, q ⊆ r ∨ r ⊆ q

private theorem subdivideSimplex_structure {V : Type*} [DecidableEq V]
    (s : Finset V) : ∀ t : Finset (Finset V),
    subdivideSimplex s t ≠ 0 → SimplexStructure s t := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
      intro t ht
      by_cases hs : s = ∅
      · subst s
        have ht' : t = ∅ := by
          by_contra hne
          apply ht
          simp [subdivideSimplex, singletonChain, hne]
        subst t
        simp [SimplexStructure]
      · rw [subdivideSimplex, if_neg hs] at ht
        obtain ⟨r, hr, hsr, rfl⟩ :=
          show ∃ r, (∑ v : s, subdivideSimplex (s.erase v)) r ≠ 0 ∧
            s ∉ r ∧ t = insert s r from by
            unfold chainCone at ht
            simp only [Finsupp.sum_apply] at ht
            contrapose! ht
            apply Finset.sum_eq_zero
            intro r hrSupport
            by_cases hsr : s ∈ r
            · simp [hsr]
            · have hcoeff : (∑ v : s, subdivideSimplex (s.erase v)) r ≠ 0 :=
                  Finsupp.mem_support_iff.mp hrSupport
              have hne : t ≠ insert s r := ht r hcoeff hsr
              have hne' : insert s r ≠ t := Ne.symm hne
              simp [hsr, singletonChain, hne']
        have hev : ∃ v : s, subdivideSimplex (s.erase v) r ≠ 0 := by
          contrapose! hr
          simp [hr]
        obtain ⟨v, hv⟩ := hev
        have hvr := ih (s.erase v) (Finset.erase_ssubset v.property) r hv
        rcases hvr with ⟨hcard, hfaces, hchain⟩
        refine ⟨?_, ?_, ?_⟩
        · have hspos : 0 < s.card := Finset.card_pos.mpr ⟨v, v.property⟩
          rw [Finset.card_insert_of_notMem hsr, hcard,
            Finset.card_erase_of_mem v.property]
          omega
        · intro q hq
          rcases Finset.mem_insert.mp hq with hqs | hqr
          · subst q
            exact ⟨Finset.nonempty_iff_ne_empty.mpr hs, fun _ h ↦ h⟩
          · exact ⟨(hfaces q hqr).1, (hfaces q hqr).2.trans (Finset.erase_subset _ _)⟩
        · intro q hq q' hq'
          rcases Finset.mem_insert.mp hq with hqs | hqr
          · subst q
            exact Or.inr <| (show q' ⊆ s from by
              rcases Finset.mem_insert.mp hq' with rfl | hq'r
              · exact fun _ h ↦ h
              · exact (hfaces q' hq'r).2.trans (Finset.erase_subset _ _))
          · rcases Finset.mem_insert.mp hq' with rfl | hq'r
            · exact Or.inl <| (hfaces q hqr).2.trans (Finset.erase_subset _ _)
            · exact hchain q hqr q' hq'r

private theorem exists_of_subdivideChain_apply_ne_zero {V : Type*} [DecidableEq V]
    (c : ModTwoChain V)
    (t : Finset (Finset V)) (ht : subdivideChain c t ≠ 0) :
    ∃ s : Finset V, c s ≠ 0 ∧ subdivideSimplex s t ≠ 0 := by
  classical
  unfold subdivideChain at ht
  simp only [Finsupp.sum_apply] at ht
  contrapose! ht
  apply Finset.sum_eq_zero
  intro s hs
  by_cases hcs : c s = 0
  · simp [hcs]
  · simp [ht s hcs]

private def IteratedStructure {V : Type*} [DecidableEq V] (s : Finset V)
    (k : ℕ) (t : Finset (SubdivisionVertex V k)) : Prop :=
  t.card = s.card ∧
    ∀ q ∈ t, (vertexCarrier k q).Nonempty ∧ vertexCarrier k q ⊆ s

private theorem iteratedSubdivision_structure {V : Type*} [DecidableEq V]
    (s : Finset V) (k : ℕ)
    (t : Finset (SubdivisionVertex V k)) (ht : iteratedSubdivision s k t ≠ 0) :
    IteratedStructure s k t := by
  classical
  induction k with
  | zero =>
      change singletonChain s t ≠ 0 at ht
      have ht' : t = s := by
        by_contra hne
        apply ht
        have hne' : s ≠ t := Ne.symm hne
        simp [singletonChain, hne']
      subst t
      refine ⟨rfl, ?_⟩
      · intro q hq
        change ({q} : Finset V).Nonempty ∧ ({q} : Finset V) ⊆ s
        exact ⟨Finset.singleton_nonempty q, Finset.singleton_subset_iff.mpr hq⟩
  | succ k ih =>
      change (subdivideChain (iteratedSubdivision s k)) t ≠ 0 at ht
      obtain ⟨u, hu, hsub⟩ :=
        exists_of_subdivideChain_apply_ne_zero (iteratedSubdivision s k) t ht
      have huStructure := ih u hu
      have htStructure : SimplexStructure u t := subdivideSimplex_structure u t hsub
      rcases huStructure with ⟨hucard, hucarrier⟩
      rcases htStructure with ⟨htcard, htfaces, _⟩
      refine ⟨htcard.trans hucard, ?_⟩
      · intro q hqt
        have hqne := (htfaces q hqt).1
        obtain ⟨v, hvq⟩ := hqne
        have hvu := (htfaces q hqt).2 hvq
        change (q.biUnion (vertexCarrier k)).Nonempty ∧
          q.biUnion (vertexCarrier k) ⊆ s
        refine ⟨?_, ?_⟩
        · exact Finset.biUnion_nonempty.2 ⟨v, hvq, (hucarrier v hvu).1⟩
        · intro a ha
          simp only [Finset.mem_biUnion] at ha
          obtain ⟨v', hv'q, hav'⟩ := ha
          exact (hucarrier v' ((htfaces q hqt).2 hv'q)).2 hav'

private theorem image_erase_eq_of_injOn {U V : Type*} [DecidableEq U]
    [DecidableEq V] (label : U → V) (s : Finset U)
    (hinj : Set.InjOn label s) (u : U) (hu : u ∈ s) :
    (s.erase u).image label = (s.image label).erase (label u) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨w, ⟨hwu, hws⟩, rfl⟩
    refine ⟨?_, w, hws, rfl⟩
    intro hlabel
    exact hwu (hinj hws hu hlabel)
  · rintro ⟨_, w, hws, rfl⟩
    refine ⟨w, ⟨?_, hws⟩, rfl⟩
    intro hwu
    subst w
    contradiction

private theorem card_goodRemovals_modTwo {U V : Type*} [DecidableEq U]
    [DecidableEq V] (label : U → V) (s : Finset U) (t : Finset V)
    (v : V) (hv : v ∈ t) (hcard : s.card = t.card)
    (himage : s.image label ⊆ t) :
    ((s.filter fun u ↦ (s.erase u).image label = t.erase v).card : ZMod 2) =
      if s.image label = t then 1 else 0 := by
  classical
  by_cases hfull : s.image label = t
  · rw [if_pos hfull]
    have hinj : Set.InjOn label s := Finset.card_image_iff.mp <| by
      rw [hfull, hcard]
    have hvimage : v ∈ s.image label := by
      rw [hfull]
      exact hv
    obtain ⟨u₀, hu₀s, hu₀v⟩ := Finset.mem_image.mp hvimage
    have hfilter : s.filter (fun u ↦ (s.erase u).image label = t.erase v) = {u₀} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hus, hugood⟩
        by_contra huu₀
        have hlu : label u ∈ t := himage (Finset.mem_image.mpr ⟨u, hus, rfl⟩)
        have hlu_ne : label u ≠ v := by
          intro huv
          apply huu₀
          exact hinj hus hu₀s (huv.trans hu₀v.symm)
        have hluErase : label u ∈ t.erase v := Finset.mem_erase.mpr ⟨hlu_ne, hlu⟩
        rw [← hugood] at hluErase
        obtain ⟨w, hwErase, hwu⟩ := Finset.mem_image.mp hluErase
        have hwData := Finset.mem_erase.mp hwErase
        exact hwData.1 (hinj hwData.2 hus hwu)
      · rintro hu
        rw [hu]
        refine ⟨hu₀s, ?_⟩
        rw [image_erase_eq_of_injOn label s hinj u₀ hu₀s, hfull, hu₀v]
    rw [hfilter]
    norm_num
  · rw [if_neg hfull]
    let A := s.filter fun u ↦ (s.erase u).image label = t.erase v
    by_cases hA : A = ∅
    · simp [A, hA]
    · obtain ⟨u₀, hu₀A⟩ := Finset.nonempty_iff_ne_empty.mpr hA
      have hu₀s : u₀ ∈ s := (Finset.mem_filter.mp hu₀A).1
      have hu₀good : (s.erase u₀).image label = t.erase v :=
        (Finset.mem_filter.mp hu₀A).2
      have hlu₀R : label u₀ ∈ t.erase v := by
        have hlu₀t : label u₀ ∈ t :=
          himage (Finset.mem_image.mpr ⟨u₀, hu₀s, rfl⟩)
        refine Finset.mem_erase.mpr ⟨?_, hlu₀t⟩
        intro hu₀v
        apply hfull
        apply Finset.Subset.antisymm himage
        intro y hy
        by_cases hyv : y = v
        · subst y
          exact Finset.mem_image.mpr ⟨u₀, hu₀s, hu₀v⟩
        · have hyR : y ∈ t.erase v := Finset.mem_erase.mpr ⟨hyv, hy⟩
          rw [← hu₀good] at hyR
          exact (Finset.image_mono label (Finset.erase_subset u₀ s)) hyR
      have himage_eq : s.image label = t.erase v := by
        apply Finset.Subset.antisymm
        · intro y hy
          rcases Finset.mem_image.mp hy with ⟨u, hus, rfl⟩
          by_cases huu₀ : u = u₀
          · simpa [huu₀] using hlu₀R
          · rw [← hu₀good]
            exact Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨huu₀, hus⟩, rfl⟩
        · rw [← hu₀good]
          exact Finset.image_mono label (Finset.erase_subset u₀ s)
      have hcardErase : (s.erase u₀).card = (t.erase v).card := by
        rw [Finset.card_erase_of_mem hu₀s, Finset.card_erase_of_mem hv, hcard]
      have hinjErase : Set.InjOn label (s.erase u₀) :=
        Finset.card_image_iff.mp <| by rw [hu₀good, hcardErase]
      obtain ⟨u₁, hu₁Erase, hu₁eq⟩ :
          ∃ u₁ ∈ s.erase u₀, label u₁ = label u₀ := by
        rw [← hu₀good] at hlu₀R
        exact Finset.mem_image.mp hlu₀R
      have hu₁s : u₁ ∈ s := (Finset.mem_erase.mp hu₁Erase).2
      have hu₁u₀ : u₁ ≠ u₀ := (Finset.mem_erase.mp hu₁Erase).1
      have hu₁good : (s.erase u₁).image label = t.erase v := by
        rw [← himage_eq]
        apply Finset.Subset.antisymm
        · exact Finset.image_mono label (Finset.erase_subset u₁ s)
        · intro y hy
          obtain ⟨u, hus, rfl⟩ := Finset.mem_image.mp hy
          by_cases huu₁ : u = u₁
          · subst u
            exact Finset.mem_image.mpr ⟨u₀,
              Finset.mem_erase.mpr ⟨hu₁u₀.symm, hu₀s⟩, hu₁eq.symm⟩
          · exact Finset.mem_image.mpr
              ⟨u, Finset.mem_erase.mpr ⟨huu₁, hus⟩, rfl⟩
      have hfilter : A = {u₀, u₁} := by
        ext u
        simp only [A, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hus, hugood⟩
          by_cases huu₀ : u = u₀
          · exact Or.inl huu₀
          · right
            have hluR : label u ∈ t.erase v := by
              rw [← himage_eq]
              exact Finset.mem_image.mpr ⟨u, hus, rfl⟩
            rw [← hugood] at hluR
            obtain ⟨w, hwErase, hwu⟩ := Finset.mem_image.mp hluR
            have hwData := Finset.mem_erase.mp hwErase
            have hwu₀ : w = u₀ := by
              by_contra hwu₀
              have hwE : w ∈ s.erase u₀ :=
                Finset.mem_erase.mpr ⟨hwu₀, hwData.2⟩
              have huE : u ∈ s.erase u₀ :=
                Finset.mem_erase.mpr ⟨huu₀, hus⟩
              exact hwData.1 (hinjErase hwE huE hwu)
            have hlu₀ : label u = label u₀ :=
              hwu.symm.trans (congrArg label hwu₀)
            exact hinjErase (Finset.mem_erase.mpr ⟨huu₀, hus⟩) hu₁Erase
              (hlu₀.trans hu₁eq.symm)
        · rintro (rfl | rfl)
          · exact ⟨hu₀s, hu₀good⟩
          · exact ⟨hu₁s, hu₁good⟩
      change (A.card : ZMod 2) = 0
      rw [hfilter]
      simpa [Finset.card_insert_of_notMem, hu₁u₀, Ne.symm hu₁u₀] using
        (CharP.cast_eq_zero (ZMod 2) 2)

private def labeledCount {U V : Type*} [DecidableEq V] (label : U → V)
    (target : Finset V) (c : ModTwoChain U) : ZMod 2 :=
  c.sum fun simplex coeff ↦
    if simplex.card = target.card ∧ simplex.image label = target then coeff else 0

@[simp] private theorem labeledCount_zero {U V : Type*} [DecidableEq V]
    (label : U → V) (target : Finset V) :
    labeledCount label target (0 : ModTwoChain U) = 0 := by
  simp [labeledCount]

private theorem labeledCount_add {U V : Type*} [DecidableEq U] [DecidableEq V]
    (label : U → V) (target : Finset V) (a b : ModTwoChain U) :
    labeledCount label target (a + b) =
      labeledCount label target a + labeledCount label target b := by
  classical
  unfold labeledCount
  rw [Finsupp.sum_add_index']
  · intro s
    split <;> simp
  · intro s a b
    split <;> simp

private theorem labeledCount_smul {U V : Type*} [DecidableEq U] [DecidableEq V]
    (label : U → V) (target : Finset V) (a : ZMod 2) (c : ModTwoChain U) :
    labeledCount label target (a • c) = a * labeledCount label target c := by
  classical
  unfold labeledCount
  rw [Finsupp.sum_smul_index]
  · change _ = a • Finsupp.sum c (fun simplex coeff ↦
      if simplex.card = target.card ∧ simplex.image label = target then coeff else 0)
    rw [Finsupp.smul_sum]
    apply Finsupp.sum_congr
    intro simplex _
    split <;> simp
  · intro simplex
    split <;> simp

@[simp] private theorem labeledCount_singletonChain {U V : Type*}
    [DecidableEq U] [DecidableEq V] (label : U → V) (target : Finset V)
    (s : Finset U) :
    labeledCount label target (singletonChain s) =
      if s.card = target.card ∧ s.image label = target then 1 else 0 := by
  classical
  simp [labeledCount, singletonChain]

private theorem labeledCount_finset_sum {U V I : Type*} [DecidableEq U]
    [DecidableEq V] (label : U → V) (target : Finset V) (s : Finset I)
    (c : I → ModTwoChain U) :
    labeledCount label target (∑ i ∈ s, c i) =
      ∑ i ∈ s, labeledCount label target (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, labeledCount_add]

private theorem labeledCount_boundary_singleton {U V : Type*}
    [DecidableEq U] [DecidableEq V] (label : U → V) (s : Finset U)
    (t : Finset V) (v : V) (hv : v ∈ t) (hcard : s.card = t.card)
    (himage : s.image label ⊆ t) :
    labeledCount label (t.erase v) (chainBoundary (singletonChain s)) =
      if s.image label = t then 1 else 0 := by
  classical
  rw [chainBoundary_singletonChain, simplexBoundary, labeledCount_finset_sum]
  simp_rw [labeledCount_singletonChain]
  calc
    (∑ x ∈ s, if (s.erase x).card = (t.erase v).card ∧
        (s.erase x).image label = t.erase v then (1 : ZMod 2) else 0) =
        ∑ x ∈ s, if (s.erase x).image label = t.erase v then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.card_erase_of_mem hx, Finset.card_erase_of_mem hv, hcard]
    _ = if s.image label = t then 1 else 0 := by
      rw [Finset.sum_boole]
      exact card_goodRemovals_modTwo label s t v hv hcard himage

private theorem labeledCount_boundary {U V : Type*} [DecidableEq U]
    [DecidableEq V] (label : U → V) (c : ModTwoChain U) (t : Finset V)
    (v : V) (hv : v ∈ t)
    (hcard : ∀ s, c s ≠ 0 → s.card = t.card)
    (himage : ∀ s, c s ≠ 0 → s.image label ⊆ t) :
    labeledCount label (t.erase v) (chainBoundary c) = labeledCount label t c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add s a c hs ha ih =>
      have hcs : c s = 0 := Finsupp.notMem_support_iff.mp hs
      have htotal_s : (Finsupp.single s a + c : ModTwoChain U) s ≠ 0 := by
        simp [hcs, ha]
      have hscard : s.card = t.card := hcard s htotal_s
      have hsimage : s.image label ⊆ t := himage s htotal_s
      have hcard_c : ∀ r, c r ≠ 0 → r.card = t.card := by
        intro r hr
        apply hcard r
        by_cases hrs : r = s
        · subst r
          exact (hr hcs).elim
        · simpa [Finsupp.single_apply, hrs]
      have himage_c : ∀ r, c r ≠ 0 → r.image label ⊆ t := by
        intro r hr
        apply himage r
        by_cases hrs : r = s
        · subst r
          exact (hr hcs).elim
        · simpa [Finsupp.single_apply, hrs]
      have hsform : Finsupp.single s a = a • singletonChain s := by
        ext r
        simp [singletonChain]
      rw [chainBoundary_add, labeledCount_add, labeledCount_add,
        ih hcard_c himage_c, hsform, chainBoundary_smul,
        labeledCount_smul, labeledCount_smul,
        labeledCount_boundary_singleton label s t v hv hscard hsimage,
        labeledCount_singletonChain]
      simp [hscard]

private theorem chainBoundary_iteratedSubdivision {V : Type*} [DecidableEq V]
    (s : Finset V) (k : ℕ) :
    chainBoundary (iteratedSubdivision s k) =
      ∑ v ∈ s, iteratedSubdivision (s.erase v) k := by
  classical
  induction k with
  | zero =>
      change chainBoundary (singletonChain s) =
        ∑ v ∈ s, singletonChain (s.erase v)
      rw [chainBoundary_singletonChain]
      rfl
  | succ k ih =>
      change chainBoundary (subdivideChain (iteratedSubdivision s k)) =
        ∑ v ∈ s, subdivideChain (iteratedSubdivision (s.erase v) k)
      rw [chainBoundary_subdivideChain, ih, subdivideChain_finset_sum]

private theorem iteratedSubdivision_empty {V : Type*} [DecidableEq V] (k : ℕ) :
    iteratedSubdivision (∅ : Finset V) k = singletonChain ∅ := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
      change subdivideChain (iteratedSubdivision (∅ : Finset V) k) =
        singletonChain ∅
      rw [ih, subdivideChain_singletonChain, subdivideSimplex]
      simp only [ite_true]

private theorem labeledCount_eq_zero_of_missing {U V : Type*} [DecidableEq U]
    [DecidableEq V] (label : U → V) (target : Finset V) (c : ModTwoChain U)
    (v : V) (hv : v ∈ target)
    (hmissing : ∀ simplex, c simplex ≠ 0 → v ∉ simplex.image label) :
    labeledCount label target c = 0 := by
  classical
  unfold labeledCount
  calc
    c.sum (fun simplex coeff ↦
        if simplex.card = target.card ∧ simplex.image label = target
        then coeff else 0) = c.sum (fun _ _ ↦ 0) := by
      apply Finsupp.sum_congr
      intro simplex hs
      rw [if_neg]
      intro h
      exact hmissing simplex (Finsupp.mem_support_iff.mp hs) (h.2 ▸ hv)
    _ = 0 := Finsupp.sum_fun_zero c

private theorem labeledCount_iteratedSubdivision {V : Type*} [DecidableEq V]
    (s : Finset V) (k : ℕ) (label : SubdivisionVertex V k → V)
    (hlabel : ∀ q, vertexCarrier k q ⊆ s →
      (vertexCarrier k q).Nonempty → label q ∈ vertexCarrier k q) :
    labeledCount label s (iteratedSubdivision s k) = 1 := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
      by_cases hs : s = ∅
      · subst s
        simp [iteratedSubdivision_empty, labeledCount, singletonChain]
      · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        rw [← labeledCount_boundary label (iteratedSubdivision s k) s v hv]
        · rw [chainBoundary_iteratedSubdivision,
            labeledCount_finset_sum label (s.erase v) s]
          rw [Finset.sum_eq_single v]
          · exact ih (s.erase v) (Finset.erase_ssubset hv) <| by
              intro q hqsub hqne
              exact hlabel q (hqsub.trans (Finset.erase_subset _ _)) hqne
          · intro w hw hwv
            apply labeledCount_eq_zero_of_missing label (s.erase v)
              (iteratedSubdivision (s.erase w) k) w
            · exact Finset.mem_erase.mpr ⟨hwv, hw⟩
            · intro simplex hsimp hwimage
              obtain ⟨q, hqsimp, hqw⟩ := Finset.mem_image.mp hwimage
              have hstruct := iteratedSubdivision_structure (s.erase w) k simplex hsimp
              have hqcarrier := hstruct.2 q hqsimp
              have hqlabel := hlabel q
                (hqcarrier.2.trans (Finset.erase_subset _ _)) hqcarrier.1
              exact (Finset.mem_erase.mp (hqcarrier.2 hqlabel)).1 hqw
          · exact fun hvs ↦ (hvs hv).elim
        · intro simplex hsimp
          exact (iteratedSubdivision_structure s k simplex hsimp).1
        · intro simplex hsimp a ha
          obtain ⟨q, hqsimp, rfl⟩ := Finset.mem_image.mp ha
          have hstruct := iteratedSubdivision_structure s k simplex hsimp
          have hqcarrier := hstruct.2 q hqsimp
          exact hqcarrier.2 (hlabel q hqcarrier.2 hqcarrier.1)

private theorem exists_fullyLabeled_iteratedSubdivision {V : Type*}
    [DecidableEq V] (s : Finset V) (k : ℕ)
    (label : SubdivisionVertex V k → V)
    (hlabel : ∀ q, vertexCarrier k q ⊆ s →
      (vertexCarrier k q).Nonempty → label q ∈ vertexCarrier k q) :
    ∃ simplex, iteratedSubdivision s k simplex ≠ 0 ∧ simplex.image label = s := by
  classical
  have hcount := labeledCount_iteratedSubdivision s k label hlabel
  by_contra! h
  have hzero : labeledCount label s (iteratedSubdivision s k) = 0 := by
    unfold labeledCount
    calc
      (iteratedSubdivision s k).sum (fun simplex coeff ↦
          if simplex.card = s.card ∧ simplex.image label = s
          then coeff else 0) = (iteratedSubdivision s k).sum (fun _ _ ↦ 0) := by
        apply Finsupp.sum_congr
        intro simplex hs
        rw [if_neg]
        exact fun hsimp ↦
          h simplex (Finsupp.mem_support_iff.mp hs) hsimp.2
      _ = 0 := Finsupp.sum_fun_zero (iteratedSubdivision s k)
  rw [hzero] at hcount
  exact zero_ne_one hcount

private def ValidSubdivisionVertex (V : Type*) :
    (k : ℕ) → SubdivisionVertex V k → Prop
  | 0, _ => True
  | k + 1, q =>
      let q' : Finset (SubdivisionVertex V k) := q
      q'.Nonempty ∧ ∀ v ∈ q', ValidSubdivisionVertex V k v

private theorem iteratedSubdivision_validVertices {V : Type*} [DecidableEq V]
    (s : Finset V) (k : ℕ) (simplex : Finset (SubdivisionVertex V k))
    (hsimplex : iteratedSubdivision s k simplex ≠ 0) :
    ∀ q ∈ simplex, ValidSubdivisionVertex V k q := by
  classical
  induction k with
  | zero => simp [ValidSubdivisionVertex]
  | succ k ih =>
      change (subdivideChain (iteratedSubdivision s k)) simplex ≠ 0 at hsimplex
      obtain ⟨parent, hparent, hsub⟩ :=
        exists_of_subdivideChain_apply_ne_zero (iteratedSubdivision s k) simplex hsimplex
      have hsubStructure := subdivideSimplex_structure parent simplex hsub
      intro q hqsimplex
      change (show Finset (SubdivisionVertex V k) from q).Nonempty ∧
        ∀ v ∈ (show Finset (SubdivisionVertex V k) from q),
          ValidSubdivisionVertex V k v
      refine ⟨(hsubStructure.2.1 q hqsimplex).1, ?_⟩
      intro v hvq
      exact ih parent hparent v ((hsubStructure.2.1 q hqsimplex).2 hvq)

private theorem subdivisionPosition_mem_convexHull {V E : Type*}
    [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) (k : ℕ) (q : SubdivisionVertex V k)
    (hq : ValidSubdivisionVertex V k q) :
    subdivisionPosition p k q ∈
      convexHull ℝ (p '' (vertexCarrier k q : Set V)) := by
  classical
  induction k with
  | zero =>
      rw [subdivisionPosition, vertexCarrier]
      exact subset_convexHull ℝ
        (p '' (({(show V from q)} : Finset V) : Set V))
        ⟨(show V from q), by simp, rfl⟩
  | succ k ih =>
      change (show Finset (SubdivisionVertex V k) from q).Nonempty ∧
        ∀ v ∈ (show Finset (SubdivisionVertex V k) from q),
          ValidSubdivisionVertex V k v at hq
      rcases hq with ⟨hqne, hqvalid⟩
      simp only [subdivisionPosition, vertexCarrier]
      unfold finsetAverage
      rw [Finset.smul_sum]
      apply (convex_convexHull ℝ
        (p '' ((show Finset (SubdivisionVertex V k) from q).biUnion
          (vertexCarrier k) : Set V))).sum_mem
      · intro i hi
        positivity
      · simp [hqne.ne_empty]
      · intro v hvq
        apply (convexHull_mono ?_) (ih v (hqvalid v hvq))
        rintro x ⟨a, ha, rfl⟩
        exact ⟨a, Finset.mem_biUnion.mpr ⟨v, hvq, ha⟩, rfl⟩

private theorem sum_sub_finsetAverage_eq_zero {V E : Type*}
    [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) (s : Finset V) (hs : s.Nonempty) :
    ∑ v ∈ s, (p v - finsetAverage p s) = 0 := by
  unfold finsetAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [hs.ne_empty]

private theorem finsetAverage_sub_eq_sdiff {V E : Type*}
    [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) (q r : Finset V) (hq : q.Nonempty) (hqr : q ⊆ r) :
    finsetAverage p r - finsetAverage p q =
      (r.card : ℝ)⁻¹ • ∑ v ∈ r \ q, (p v - finsetAverage p q) := by
  have hr : r.Nonempty := hq.mono hqr
  have hsum :
      ∑ v ∈ r \ q, (p v - finsetAverage p q) =
        ∑ v ∈ r, (p v - finsetAverage p q) := by
    calc
      (∑ v ∈ r \ q, (p v - finsetAverage p q)) =
          (∑ v ∈ r \ q, (p v - finsetAverage p q)) +
            ∑ v ∈ q, (p v - finsetAverage p q) := by
        rw [sum_sub_finsetAverage_eq_zero p q hq, add_zero]
      _ = ∑ v ∈ r, (p v - finsetAverage p q) := Finset.sum_sdiff hqr
  rw [hsum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const]
  have hrcard : (r.card : ℝ) ≠ 0 := by positivity
  unfold finsetAverage
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hrcard, one_smul]

private theorem finsetAverage_mem_convexHull {V E : Type*}
    [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) (s : Finset V) (hs : s.Nonempty) :
    finsetAverage p s ∈ convexHull ℝ (p '' (s : Set V)) := by
  classical
  unfold finsetAverage
  rw [Finset.smul_sum]
  apply (convex_convexHull ℝ (p '' (s : Set V))).sum_mem
  · intro i hi
    positivity
  · simp [hs.ne_empty]
  · intro v hv
    exact subset_convexHull ℝ (p '' (s : Set V)) ⟨v, hv, rfl⟩

private theorem dist_point_finsetAverage_le_diam {V E : Type*}
    [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) (s q : Finset V) (hq : q.Nonempty) (hqs : q ⊆ s)
    (v : V) (hvs : v ∈ s) :
    dist (p v) (finsetAverage p q) ≤ Metric.diam (p '' (s : Set V)) := by
  have hfinite : (p '' (s : Set V)).Finite := s.finite_toSet.image p
  have hbounded : Bornology.IsBounded (convexHull ℝ (p '' (s : Set V))) :=
    isBounded_convexHull.mpr hfinite.isBounded
  rw [← convexHull_diam]
  apply Metric.dist_le_diam_of_mem hbounded
  · exact subset_convexHull ℝ (p '' (s : Set V)) ⟨v, hvs, rfl⟩
  · exact (convexHull_mono (Set.image_mono hqs)) (finsetAverage_mem_convexHull p q hq)

private theorem dist_finsetAverage_le_fraction_diam {V E : Type*}
    [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) (s q r : Finset V) (hq : q.Nonempty)
    (hqr : q ⊆ r) (hrs : r ⊆ s) :
    dist (finsetAverage p q) (finsetAverage p r) ≤
      ((r \ q).card : ℝ) / r.card * Metric.diam (p '' (s : Set V)) := by
  have hr : r.Nonempty := hq.mono hqr
  rw [dist_comm, dist_eq_norm, finsetAverage_sub_eq_sdiff p q r hq hqr,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    (r.card : ℝ)⁻¹ * ‖∑ v ∈ r \ q, (p v - finsetAverage p q)‖ ≤
        (r.card : ℝ)⁻¹ * ∑ v ∈ r \ q, ‖p v - finsetAverage p q‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (r.card : ℝ)⁻¹ *
        ∑ _v ∈ r \ q, Metric.diam (p '' (s : Set V)) := by
      gcongr with v hv
      rw [← dist_eq_norm]
      exact dist_point_finsetAverage_le_diam p s q hq
        (hqr.trans hrs) v (hrs (Finset.mem_sdiff.mp hv).1)
    _ = ((r \ q).card : ℝ) / r.card * Metric.diam (p '' (s : Set V)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

private theorem card_sdiff_div_card_le {V : Type*} [DecidableEq V]
    (s q r : Finset V) (hq : q.Nonempty) (hqr : q ⊆ r) (hrs : r ⊆ s) :
    ((r \ q).card : ℝ) / r.card ≤ (s.card : ℝ) / (s.card + 1) := by
  have hr : r.Nonempty := hq.mono hqr
  have hs : s.Nonempty := hr.mono hrs
  have ha : ((r \ q).card : ℝ) ≤ s.card := by
    exact_mod_cast Finset.card_le_card ((Finset.sdiff_subset).trans hrs)
  have hb : (1 : ℝ) ≤ q.card := by
    exact_mod_cast Finset.card_pos.mpr hq
  have hn : (0 : ℝ) ≤ s.card := by positivity
  have hanb : ((r \ q).card : ℝ) ≤ (s.card : ℝ) * q.card := by
    calc
      ((r \ q).card : ℝ) ≤ s.card := ha
      _ = (s.card : ℝ) * 1 := by ring
      _ ≤ (s.card : ℝ) * q.card := mul_le_mul_of_nonneg_left hb hn
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < r.card)
    (by positivity : (0 : ℝ) < s.card + 1)]
  have hcard : (r.card : ℝ) = (r \ q).card + q.card := by
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card hqr).symm
  rw [hcard]
  nlinarith

private theorem dist_finsetAverage_le_meshFactor {V E : Type*}
    [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) (s q r : Finset V) (hq : q.Nonempty)
    (hqr : q ⊆ r) (hrs : r ⊆ s) :
    dist (finsetAverage p q) (finsetAverage p r) ≤
      ((s.card : ℝ) / (s.card + 1)) * Metric.diam (p '' (s : Set V)) := by
  calc
    dist (finsetAverage p q) (finsetAverage p r) ≤
        ((r \ q).card : ℝ) / r.card * Metric.diam (p '' (s : Set V)) :=
      dist_finsetAverage_le_fraction_diam p s q r hq hqr hrs
    _ ≤ ((s.card : ℝ) / (s.card + 1)) * Metric.diam (p '' (s : Set V)) :=
      mul_le_mul_of_nonneg_right (card_sdiff_div_card_le s q r hq hqr hrs)
        Metric.diam_nonneg

private theorem iteratedSubdivision_mesh {V E : Type*}
    [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) (s : Finset V) (hs : s.Nonempty) (k : ℕ)
    (simplex : Finset (SubdivisionVertex V k))
    (hsimplex : iteratedSubdivision s k simplex ≠ 0) :
    ∀ q ∈ simplex, ∀ r ∈ simplex,
      dist (subdivisionPosition p k q) (subdivisionPosition p k r) ≤
        ((s.card : ℝ) / (s.card + 1)) ^ k * Metric.diam (p '' (s : Set V)) := by
  classical
  induction k with
  | zero =>
      change singletonChain s simplex ≠ 0 at hsimplex
      have hsimp : simplex = s := by
        by_contra hne
        apply hsimplex
        have hne' : s ≠ simplex := Ne.symm hne
        simp [singletonChain, hne']
      subst simplex
      intro q hq r hr
      rw [subdivisionPosition, subdivisionPosition]
      simp only [pow_zero, one_mul]
      exact Metric.dist_le_diam_of_mem (s.finite_toSet.image p).isBounded
        ⟨(show V from q), hq, rfl⟩ ⟨(show V from r), hr, rfl⟩
  | succ k ih =>
      change (subdivideChain (iteratedSubdivision s k)) simplex ≠ 0 at hsimplex
      obtain ⟨parent, hparent, hsub⟩ :=
        exists_of_subdivideChain_apply_ne_zero (iteratedSubdivision s k) simplex hsimplex
      have hparentStructure := iteratedSubdivision_structure s k parent hparent
      have hsubStructure := subdivideSimplex_structure parent simplex hsub
      have hparentNonempty : parent.Nonempty := by
        apply Finset.card_pos.mp
        rw [hparentStructure.1]
        exact Finset.card_pos.mpr hs
      have hdiam : Metric.diam
          (subdivisionPosition p k '' (parent : Set (SubdivisionVertex V k))) ≤
          ((s.card : ℝ) / (s.card + 1)) ^ k *
            Metric.diam (p '' (s : Set V)) := by
        apply Metric.diam_le_of_forall_dist_le
        · positivity
        · rintro _ ⟨q, hq, rfl⟩ _ ⟨r, hr, rfl⟩
          exact ih parent hparent q hq r hr
      intro q hq r hr
      have hqData := hsubStructure.2.1 q hq
      have hrData := hsubStructure.2.1 r hr
      have hfactor :
          ((parent.card : ℝ) / (parent.card + 1)) =
            ((s.card : ℝ) / (s.card + 1)) := by
        rw [hparentStructure.1]
      have hfactorNonneg : (0 : ℝ) ≤ (s.card : ℝ) / (s.card + 1) := by positivity
      simp only [subdivisionPosition]
      rcases hsubStructure.2.2 q hq r hr with hqr | hrq
      · calc
          dist (finsetAverage (subdivisionPosition p k) q)
              (finsetAverage (subdivisionPosition p k) r) ≤
              ((parent.card : ℝ) / (parent.card + 1)) *
                Metric.diam
                  (subdivisionPosition p k '' (parent : Set (SubdivisionVertex V k))) :=
            dist_finsetAverage_le_meshFactor (subdivisionPosition p k)
              parent q r hqData.1 hqr hrData.2
          _ = ((s.card : ℝ) / (s.card + 1)) *
                Metric.diam
                  (subdivisionPosition p k '' (parent : Set (SubdivisionVertex V k))) := by
            rw [hfactor]
          _ ≤ ((s.card : ℝ) / (s.card + 1)) *
                (((s.card : ℝ) / (s.card + 1)) ^ k *
                  Metric.diam (p '' (s : Set V))) :=
            mul_le_mul_of_nonneg_left hdiam hfactorNonneg
          _ = ((s.card : ℝ) / (s.card + 1)) ^ (k + 1) *
                Metric.diam (p '' (s : Set V)) := by
            rw [pow_succ']
            ring
      · rw [dist_comm]
        calc
          dist (finsetAverage (subdivisionPosition p k) r)
              (finsetAverage (subdivisionPosition p k) q) ≤
              ((parent.card : ℝ) / (parent.card + 1)) *
                Metric.diam
                  (subdivisionPosition p k '' (parent : Set (SubdivisionVertex V k))) :=
            dist_finsetAverage_le_meshFactor (subdivisionPosition p k)
              parent r q hrData.1 hrq hqData.2
          _ = ((s.card : ℝ) / (s.card + 1)) *
                Metric.diam
                  (subdivisionPosition p k '' (parent : Set (SubdivisionVertex V k))) := by
            rw [hfactor]
          _ ≤ ((s.card : ℝ) / (s.card + 1)) *
                (((s.card : ℝ) / (s.card + 1)) ^ k *
                  Metric.diam (p '' (s : Set V))) :=
            mul_le_mul_of_nonneg_left hdiam hfactorNonneg
          _ = ((s.card : ℝ) / (s.card + 1)) ^ (k + 1) *
                Metric.diam (p '' (s : Set V)) := by
            rw [pow_succ']
            ring

namespace Submission

private theorem convex_inner_sub_right_pos {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x z : E) :
    Convex ℝ {y | 0 < ⟪x - z, x - y⟫_ℝ} := by
  intro y hy w hw a b ha hb hab
  simp only [Set.mem_setOf_eq] at hy hw ⊢
  have hidentity : x - (a • y + b • w) = a • (x - y) + b • (x - w) := by
    calc
      x - (a • y + b • w) =
          (a + b) • x - (a • y + b • w) := by rw [hab, one_smul]
      _ = a • (x - y) + b • (x - w) := by module
  rw [hidentity, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  by_cases hapos : 0 < a
  · exact add_pos_of_pos_of_nonneg (mul_pos hapos hy) (mul_nonneg hb hw.le)
  · have ha0 : a = 0 := le_antisymm (le_of_not_gt hapos) ha
    have hb1 : b = 1 := by linarith
    simp [ha0, hb1, hw]

/-- Finite Knaster--Kuratowski--Mazurkiewicz lemma, in the form needed below. -/
theorem finite_kkm {V E : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) (C : V → Set E)
    (hCclosed : ∀ v, IsClosed (C v))
    (hcover : ∀ s : Finset V, s.Nonempty →
      convexHull ℝ (p '' (s : Set V)) ⊆ ⋃ v ∈ s, C v) :
    ∃ x ∈ convexHull ℝ (Set.range p), ∀ v, x ∈ C v := by
  classical
  let coverWitness : ∀ (k : ℕ) (q : SubdivisionVertex V k),
      ValidSubdivisionVertex V k q → (vertexCarrier k q).Nonempty →
        ∃ v ∈ vertexCarrier k q, subdivisionPosition p k q ∈ C v := by
    intro k q hq hcarrier
    have hpos := subdivisionPosition_mem_convexHull p k q hq
    have hcovered := hcover (vertexCarrier k q) hcarrier hpos
    simp only [Set.mem_iUnion] at hcovered
    rcases hcovered with ⟨v, hv, hCv⟩
    exact ⟨v, hv, hCv⟩
  let label : ∀ k : ℕ, SubdivisionVertex V k → V := fun k q ↦
    if hq : ValidSubdivisionVertex V k q then
      if hcarrier : (vertexCarrier k q).Nonempty then
        Classical.choose (coverWitness k q hq hcarrier)
      else Classical.choice inferInstance
    else if hcarrier : (vertexCarrier k q).Nonempty then
      Classical.choose (Finset.nonempty_def.mp hcarrier)
    else Classical.choice inferInstance
  have label_mem_carrier : ∀ k (q : SubdivisionVertex V k),
      (vertexCarrier k q).Nonempty → label k q ∈ vertexCarrier k q := by
    intro k q hcarrier
    dsimp only [label]
    split
    · rename_i hq
      exact (Classical.choose_spec (coverWitness k q hq hcarrier)).1
    ·
      exact Classical.choose_spec (Finset.nonempty_def.mp hcarrier)
  have label_mem_set : ∀ k (q : SubdivisionVertex V k),
      ValidSubdivisionVertex V k q → (vertexCarrier k q).Nonempty →
        subdivisionPosition p k q ∈ C (label k q) := by
    intro k q hq hcarrier
    dsimp only [label]
    rw [dif_pos hq, dif_pos hcarrier]
    exact (Classical.choose_spec (coverWitness k q hq hcarrier)).2
  have fullyLabeled : ∀ k : ℕ,
      ∃ simplex, iteratedSubdivision (Finset.univ : Finset V) k simplex ≠ 0 ∧
        simplex.image (label k) = Finset.univ := by
    intro k
    apply exists_fullyLabeled_iteratedSubdivision Finset.univ k (label k)
    intro q _ hcarrier
    exact label_mem_carrier k q hcarrier
  let simplex : (k : ℕ) → Finset (SubdivisionVertex V k) :=
    fun k ↦ Classical.choose (fullyLabeled k)
  have simplex_mem : ∀ k, iteratedSubdivision (Finset.univ : Finset V) k (simplex k) ≠ 0 :=
    fun k ↦ (Classical.choose_spec (fullyLabeled k)).1
  have simplex_labels : ∀ k, (simplex k).image (label k) = Finset.univ :=
    fun k ↦ (Classical.choose_spec (fullyLabeled k)).2
  have hasVertex : ∀ k v, ∃ q ∈ simplex k, label k q = v := by
    intro k v
    have hv : v ∈ (simplex k).image (label k) := by
      rw [simplex_labels k]
      exact Finset.mem_univ v
    simpa only [Finset.mem_image] using hv
  let vertex : (k : ℕ) → V → SubdivisionVertex V k :=
    fun k v ↦ Classical.choose (hasVertex k v)
  have vertex_mem : ∀ k v, vertex k v ∈ simplex k :=
    fun k v ↦ (Classical.choose_spec (hasVertex k v)).1
  have vertex_label : ∀ k v, label k (vertex k v) = v :=
    fun k v ↦ (Classical.choose_spec (hasVertex k v)).2
  let y : ℕ → V → E := fun k v ↦ subdivisionPosition p k (vertex k v)
  have vertex_valid : ∀ k v, ValidSubdivisionVertex V k (vertex k v) := by
    intro k v
    exact iteratedSubdivision_validVertices Finset.univ k (simplex k)
      (simplex_mem k) (vertex k v) (vertex_mem k v)
  have y_mem_set : ∀ k v, y k v ∈ C v := by
    intro k v
    have hcarrier :=
      (iteratedSubdivision_structure Finset.univ k (simplex k) (simplex_mem k)).2
        (vertex k v) (vertex_mem k v)
    have hmem := label_mem_set k (vertex k v) (vertex_valid k v) hcarrier.1
    rw [vertex_label k v] at hmem
    simpa only [y] using hmem
  have y_mem_hull : ∀ k v, y k v ∈ convexHull ℝ (Set.range p) := by
    intro k v
    apply (convexHull_mono ?_)
      (subdivisionPosition_mem_convexHull p k (vertex k v) (vertex_valid k v))
    rintro _ ⟨a, _, rfl⟩
    exact Set.mem_range_self a
  let v₀ : V := Classical.choice inferInstance
  let xseq : ℕ → E := fun k ↦ y k v₀
  have xseq_mem_hull : ∀ k, xseq k ∈ convexHull ℝ (Set.range p) :=
    fun k ↦ y_mem_hull k v₀
  have xy_dist : ∀ k v,
      dist (xseq k) (y k v) ≤
        ((Fintype.card V : ℝ) / (Fintype.card V + 1)) ^ k *
          Metric.diam (Set.range p) := by
    intro k v
    simpa only [xseq, y, Finset.card_univ, Finset.coe_univ, Set.image_univ,
      Set.range_comp, Function.comp_def] using
      iteratedSubdivision_mesh p (Finset.univ : Finset V) Finset.univ_nonempty k
        (simplex k) (simplex_mem k) (vertex k v₀) (vertex_mem k v₀)
          (vertex k v) (vertex_mem k v)
  have hfactor_nonneg :
      (0 : ℝ) ≤ (Fintype.card V : ℝ) / (Fintype.card V + 1) := by positivity
  have hfactor_lt :
      (Fintype.card V : ℝ) / (Fintype.card V + 1) < 1 := by
    apply (div_lt_one (by positivity : (0 : ℝ) < Fintype.card V + 1)).2
    linarith
  have mesh_tendsto : Tendsto
      (fun k : ℕ ↦ ((Fintype.card V : ℝ) / (Fintype.card V + 1)) ^ k *
        Metric.diam (Set.range p)) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hfactor_nonneg hfactor_lt).mul_const
      (Metric.diam (Set.range p))
  have hcompact : IsCompact (convexHull ℝ (Set.range p)) :=
    (Set.finite_range p).isCompact_convexHull ℝ
  obtain ⟨x, hx, φ, hφ, hxlim⟩ := hcompact.tendsto_subseq xseq_mem_hull
  refine ⟨x, hx, ?_⟩
  intro v
  have mesh_subseq : Tendsto
      (fun n : ℕ ↦ ((Fintype.card V : ℝ) / (Fintype.card V + 1)) ^ (φ n) *
        Metric.diam (Set.range p)) atTop (nhds 0) :=
    mesh_tendsto.comp hφ.tendsto_atTop
  have hdist : Tendsto (fun n ↦ dist (xseq (φ n)) (y (φ n) v)) atTop (nhds 0) :=
    squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ xy_dist (φ n) v) mesh_subseq
  have hylim : Tendsto (fun n ↦ y (φ n) v) atTop (nhds x) :=
    hxlim.congr_dist hdist
  exact (hCclosed v).mem_of_tendsto hylim (Eventually.of_forall fun n ↦ y_mem_set (φ n) v)

private def fanSet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (F : E → Set E) (y : E) : Set E :=
  {x | x ∈ K ∧ ∃ z ∈ F x, ⟪x - z, x - y⟫_ℝ ≤ 0}

private theorem isClosed_fanSet {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hKcompact : IsCompact K) (F : E → Set E)
    (hgraph : IsClosed {q : E × E | q.2 ∈ F q.1})
    (hmaps : ∀ x ∈ K, F x ⊆ K) (y : E) :
    IsClosed (fanSet K F y) := by
  let P : Set (E × E) :=
    {q | q.1 ∈ K ∧ q.2 ∈ F q.1 ∧ ⟪q.1 - q.2, q.1 - y⟫_ℝ ≤ 0}
  have hinner : Continuous (fun q : E × E ↦ ⟪q.1 - q.2, q.1 - y⟫_ℝ) := by
    fun_prop
  have hPclosed : IsClosed P := by
    change IsClosed ({q : E × E | q.1 ∈ K} ∩
      ({q : E × E | q.2 ∈ F q.1} ∩ {q | ⟪q.1 - q.2, q.1 - y⟫_ℝ ≤ 0}))
    exact (hKcompact.isClosed.preimage continuous_fst).inter
      (hgraph.inter (isClosed_le hinner continuous_const))
  have hPsubset : P ⊆ K ×ˢ K := by
    rintro q ⟨hqK, hqF, _⟩
    exact ⟨hqK, hmaps q.1 hqK hqF⟩
  have hPcompact : IsCompact P :=
    (hKcompact.prod hKcompact).of_isClosed_subset hPclosed hPsubset
  have himage : Prod.fst '' P = fanSet K F y := by
    ext x
    simp only [Set.mem_image, P, fanSet, Set.mem_setOf_eq, Prod.exists]
    constructor
    · rintro ⟨a, z, ⟨haK, hzF, hinner⟩, rfl⟩
      exact ⟨haK, z, hzF, hinner⟩
    · rintro ⟨hxK, z, hzF, hinner⟩
      exact ⟨x, z, ⟨hxK, hzF, hinner⟩, rfl⟩
  rw [← himage]
  exact (hPcompact.image continuous_fst).isClosed

private theorem exists_mem_all_fanSet {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    (hKnonempty : K.Nonempty) (F : E → Set E)
    (hgraph : IsClosed {q : E × E | q.2 ∈ F q.1})
    (hFnonempty : ∀ x ∈ K, (F x).Nonempty)
    (hmaps : ∀ x ∈ K, F x ⊆ K) :
    ∃ x ∈ K, ∀ y ∈ K, x ∈ fanSet K F y := by
  classical
  let family : {y // y ∈ K} → Set E := fun y ↦ fanSet K F y.1
  have hfamilyClosed : ∀ y, IsClosed (family y) := fun y ↦
    isClosed_fanSet hKcompact F hgraph hmaps y.1
  have hfinite : ∀ u : Finset {y // y ∈ K},
      (K ∩ ⋂ y ∈ u, family y).Nonempty := by
    intro u
    by_cases hu : u.Nonempty
    · let i₀ : {y // y ∈ K} := Classical.choose hu
      letI : Nonempty {i : {y // y ∈ K} // i ∈ u} :=
        ⟨⟨i₀, Classical.choose_spec hu⟩⟩
      let p : {i : {y // y ∈ K} // i ∈ u} → E := fun i ↦ i.1.1
      let C : {i : {y // y ∈ K} // i ∈ u} → Set E :=
        fun i ↦ family i.1
      have hcoverFinite : ∀ s : Finset {i : {y // y ∈ K} // i ∈ u},
          s.Nonempty → convexHull ℝ (p '' (s : Set _)) ⊆ ⋃ i ∈ s, C i := by
        intro s hs x hx
        have hpointsK : p '' (s : Set _) ⊆ K := by
          rintro _ ⟨i, _, rfl⟩
          exact i.1.2
        have hxK : x ∈ K := (convexHull_min hpointsK hKconvex) hx
        obtain ⟨z, hzF⟩ := hFnonempty x hxK
        by_contra hnone
        simp only [Set.mem_iUnion, not_exists] at hnone
        have hvertices : p '' (s : Set _) ⊆ {y | 0 < ⟪x - z, x - y⟫_ℝ} := by
          rintro _ ⟨i, hi, rfl⟩
          have hnot : x ∉ C i := hnone i hi
          have hnle : ¬ ⟪x - z, x - p i⟫_ℝ ≤ 0 := by
            intro hle
            apply hnot
            exact ⟨hxK, z, hzF, hle⟩
          exact lt_of_not_ge hnle
        have hxpos := (convexHull_min hvertices (convex_inner_sub_right_pos x z)) hx
        have hzero : (0 : ℝ) < 0 := by
          simpa only [Set.mem_setOf_eq, sub_self, inner_zero_right] using hxpos
        exact (lt_irrefl 0) hzero
      obtain ⟨x, hxhull, hxall⟩ :=
        finite_kkm p C (fun i ↦ hfamilyClosed i.1) hcoverFinite
      have hxK : x ∈ K := by
        apply (convexHull_min ?_ hKconvex) hxhull
        rintro _ ⟨i, rfl⟩
        exact i.1.2
      refine ⟨x, hxK, ?_⟩
      simp only [Set.mem_iInter]
      intro y hyu
      exact hxall ⟨y, hyu⟩
    · rw [Finset.not_nonempty_iff_eq_empty.mp hu]
      simpa using hKnonempty
  obtain ⟨x, hxK, hxall⟩ :=
    hKcompact.inter_iInter_nonempty family hfamilyClosed hfinite
  refine ⟨x, hxK, ?_⟩
  intro y hyK
  have hxall' : ∀ i, x ∈ family i := by
    simpa only [Set.mem_iInter] using hxall
  exact hxall' ⟨y, hyK⟩

theorem kakutani_fixed_point_aux {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    (hKnonempty : K.Nonempty) (F : E → Set E)
    (hgraph : IsClosed {q : E × E | q.2 ∈ F q.1})
    (hFnonempty : ∀ x ∈ K, (F x).Nonempty)
    (hFconvex : ∀ x ∈ K, Convex ℝ (F x))
    (hFclosed : ∀ x ∈ K, IsClosed (F x))
    (hmaps : ∀ x ∈ K, F x ⊆ K) :
    ∃ x ∈ K, x ∈ F x := by
  obtain ⟨a, haK, haFan⟩ := exists_mem_all_fanSet hKcompact hKconvex hKnonempty
    F hgraph hFnonempty hmaps
  obtain ⟨v, hvF, hvMin⟩ := exists_norm_eq_iInf_of_complete_convex
    (hFnonempty a haK) (hFclosed a haK).isComplete (hFconvex a haK) a
  have hprojection : ∀ w ∈ F a, ⟪a - v, w - v⟫_ℝ ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero (hFconvex a haK) hvF).mp hvMin
  have hvK : v ∈ K := hmaps a haK hvF
  obtain ⟨_, w, hwF, hwInner⟩ := haFan v hvK
  have hprojection' : ⟪w - v, a - v⟫_ℝ ≤ 0 := by
    rw [real_inner_comm]
    exact hprojection w hwF
  have hnormSq : ‖a - v‖ ^ 2 ≤ ⟪a - w, a - v⟫_ℝ := by
    rw [show a - w = (a - v) - (w - v) by abel, inner_sub_left,
      real_inner_self_eq_norm_sq]
    linarith
  have hnormZero : ‖a - v‖ = 0 := by
    nlinarith [sq_nonneg ‖a - v‖]
  have hav : a = v := sub_eq_zero.mp (norm_eq_zero.mp hnormZero)
  refine ⟨a, haK, ?_⟩
  simpa only [hav] using hvF

end Submission
