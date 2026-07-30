import Mathlib
import ChallengeDeps

-- BEGIN INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/BooleanAtoms.lean
section
open Set MeasureTheory

namespace HalmosSupport
section
variable {X ι : Type*} [Fintype ι] [DecidableEq ι]
-- a finite Boolean cell records membership in every member of a family
def boolCell (A : ι → Set X) (s : Set ι) : Set X :=
  {x | ∀ i, x ∈ A i ↔ i ∈ s}

lemma mem_boolCell {A : ι → Set X} {s : Set ι} {x : X} :
    x ∈ boolCell A s ↔ ∀ i, x ∈ A i ↔ i ∈ s := Iff.rfl

lemma measurableSet_boolCell [MeasurableSpace X]
    {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i)) (s : Set ι) :
    MeasurableSet (boolCell A s) := by
  classical
  -- write a cell as a finite intersection of choices.
  have heq : boolCell A s = ⋂ i : ι, if i ∈ s then A i else (A i)ᶜ := by
    ext x
    constructor
    · intro hx
      have hx' := (mem_boolCell).1 hx
      exact Set.mem_iInter.2 (fun i => by
        by_cases hi : i ∈ s
        · simpa [hi] using ( (hx' i).2 hi)
        · have hn : x ∉ A i := fun hai => hi ((hx' i).1 hai)
          simpa [hi] using hn)
    · intro hx
      have hx' := Set.mem_iInter.1 hx
      apply (mem_boolCell).2
      intro i
      by_cases hi : i ∈ s
      · constructor
        · intro _; exact hi
        · intro _
          simpa [hi] using (hx' i)
      · constructor
        · intro hai
          have hc : x ∈ (A i)ᶜ := by simpa [hi] using (hx' i)
          exact ((hc : x ∉ A i) hai).elim
        · intro his; exact (hi his).elim
  rw [heq]
  exact MeasurableSet.iInter (fun i => by split_ifs <;> simp_all)

lemma boolCell_disjoint {A : ι → Set X} {s t : Set ι} (hst : s ≠ t) :
    Disjoint (boolCell A s) (boolCell A t) := by
  classical
  apply Set.disjoint_left.2
  intro x hx hs'
  have hx1 : ∀ i, x ∈ A i ↔ i ∈ s := (mem_boolCell).1 hx
  have hx2 : ∀ i, x ∈ A i ↔ i ∈ t := (mem_boolCell).1 hs'
  apply hst
  ext i
  exact (hx1 i).symm.trans (hx2 i)

lemma union_boolCell (A : ι → Set X) : (⋃ s : Set ι, boolCell A s) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro; trivial
  · intro _
    let s : Set ι := {i | x ∈ A i}
    apply Set.mem_iUnion.2
    refine ⟨s, ?_⟩
    exact fun i => Iff.rfl

lemma union_boolCell_of_mem (A : ι → Set X) (i : ι) :
    (⋃ s : {s : Set ι // i ∈ s}, boolCell A s.1) = A i := by
  classical
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨s, hs⟩
    exact ((mem_boolCell).1 hs i).2 s.2
  · intro hx
    let s : Set ι := {j | x ∈ A j}
    have his : i ∈ s := hx
    apply Set.mem_iUnion.2
    refine ⟨(⟨s, his⟩ : {s : Set ι // i ∈ s}), ?_⟩
    exact (mem_boolCell).2 (fun _ => Iff.rfl)

end
end HalmosSupport

open Set MeasureTheory
open scoped symmDiff BigOperators
namespace HalmosSupport
/- Symmetric difference behaves subadditively when a finite union is tested.
No measurability is needed for this outer-measure bound. -/
lemma symmDiff_image_finUnion_subset
    {X Y J : Type*}
    (F : Finset J) (P : J → Set X) (u v : X → Y) :
    ((u '' (⋃ j ∈ F, P j)) ∆ (v '' (⋃ j ∈ F, P j)))
       ⊆ ⋃ j ∈ F, ((u '' P j) ∆ (v '' P j)) := by
  classical
  intro y hy
  rcases (Set.mem_symmDiff.1 hy) with h | h
  · rcases h.1 with ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.1 hx with ⟨j, hxj⟩
    rcases Set.mem_iUnion.1 hxj with ⟨hj, hxP⟩
    have hnv : u x ∉ v '' P j := by
      intro hh
      apply h.2
      rcases hh with ⟨z, hz, heq⟩
      exact ⟨z, Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hz⟩⟩, heq⟩
    have hcell : u x ∈ (u '' P j) ∆ (v '' P j) :=
      Set.mem_symmDiff.2 (Or.inl ⟨⟨x, hxP, rfl⟩, hnv⟩)
    exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hcell⟩⟩
  · rcases h.1 with ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.1 hx with ⟨j, hxj⟩
    rcases Set.mem_iUnion.1 hxj with ⟨hj, hxP⟩
    have hnu : v x ∉ u '' P j := by
      intro hh
      apply h.2
      rcases hh with ⟨z, hz, heq⟩
      exact ⟨z, Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hz⟩⟩, heq⟩
    have hcell : v x ∈ (u '' P j) ∆ (v '' P j) :=
      Set.mem_symmDiff.2 (Or.inr ⟨⟨x, hxP, rfl⟩, hnu⟩)
    exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hcell⟩⟩

lemma measure_symmDiff_image_finUnion_le
    {X Y J : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (F : Finset J) (P : J → Set X) (u v : X → Y) :
    μ ((u '' (⋃ j ∈ F, P j)) ∆ (v '' (⋃ j ∈ F, P j)))
       ≤ ∑ j ∈ F, μ ((u '' P j) ∆ (v '' P j)) := by
  classical
  refine le_trans (measure_mono (symmDiff_image_finUnion_subset F P u v)) ?_
  exact measure_biUnion_finset_le F (fun j => (u '' P j) ∆ (v '' P j))
end HalmosSupport

end
-- END INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/BooleanAtoms.lean

-- BEGIN INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/ColorRound.lean
section

/-!
A small finite bookkeeping lemma used when two finite Boolean partitions of
an equal-weight cube have almost the same weights.  One may change just the
surplus points of the second labelling to obtain *exactly* the histogram of
the first.
-/
namespace HalmosSupport
open scoped BigOperators
open Classical

section
variable {α κ : Type*} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]

noncomputable def colorFiber (c : α → κ) (i : κ) : Finset α :=
  Finset.univ.filter (fun x => c x = i)

@[simp] lemma mem_colorFiber (c : α → κ) (i : κ) (x : α) :
    x ∈ colorFiber c i ↔ c x = i := by
  classical simp [colorFiber]

lemma pairwise_colorFiber (c : α → κ) :
    (↑(Finset.univ : Finset κ) : Set κ).PairwiseDisjoint (colorFiber c) := by
  classical
  intro i hi j hj hne
  exact Finset.disjoint_left.mpr (by
    intro x hxi hxj
    have h1 := (mem_colorFiber c i x).1 hxi
    have h2 := (mem_colorFiber c j x).1 hxj
    exact hne (h1.symm.trans h2))

lemma biUnion_colorFiber (c : α → κ) :
    (Finset.univ : Finset κ).biUnion (colorFiber c) = Finset.univ := by
  classical
  ext x
  simp [colorFiber]

lemma sum_card_colorFiber (c : α → κ) :
    ∑ i : κ, (colorFiber c i).card = Fintype.card α := by
  classical
  rw [← Finset.card_biUnion (pairwise_colorFiber c)]
  rw [biUnion_colorFiber]
  simp

/-- Correct the histogram of a colouring of a finite type.  The new colouring
agrees with the old one off at most the sum of the (one-sided) deficits.  In a
uniform probability space this is the clean rounding step: no list of atom
swaps has to be chosen at the measure-theoretic level.

We formulate the bound on the *number* of changed atoms; multiplication by
the common atom mass is a separate, harmless step. -/
theorem exists_colorRound (c d : α → κ) :
    ∃ d' : α → κ,
      (∀ i : κ, (colorFiber d' i).card = (colorFiber c i).card) ∧
      ((Finset.univ.filter (fun x : α => d' x ≠ d x)).card
         ≤ ∑ i : κ, ((colorFiber c i).card -
                         min (colorFiber c i).card (colorFiber d i).card)) := by
  classical
  -- retain exactly as many old points of colour `i` as possible
  let a : κ → ℕ := fun i => (colorFiber c i).card
  let b : κ → ℕ := fun i => (colorFiber d i).card
  let t : κ → ℕ := fun i => min (a i) (b i)
  have ht_le (i : κ) : t i ≤ (colorFiber d i).card := by
    dsimp [t, b]
    exact min_le_right _ _
  choose keep hk hkc using (fun i : κ =>
    Finset.exists_subset_card_eq (s := colorFiber d i) (n := t i) (ht_le i))
  have hkeep_d (i : κ) : keep i ⊆ colorFiber d i := hk i
  have hkeep_card (i : κ) : (keep i).card = t i := hkc i
  have hpw : (↑(Finset.univ : Finset κ) : Set κ).PairwiseDisjoint keep := by
    intro i hi j hj hne
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have h1 : d x = i := (mem_colorFiber d i x).1 (hkeep_d i hxi)
    have h2 : d x = j := (mem_colorFiber d j x).1 (hkeep_d j hxj)
    exact hne (h1.symm.trans h2)
  let kept : Finset α := (Finset.univ : Finset κ).biUnion keep
  have hkept_card : kept.card = ∑ i : κ, t i := by
    dsimp [kept]
    rw [Finset.card_biUnion hpw]
    exact Finset.sum_congr rfl (by
      intro i hi
      exact hkeep_card i)
  have hi_keep_of (i : κ) (x : α) (hx : x ∈ keep i) : d x = i :=
    (mem_colorFiber d i x).1 (hkeep_d i hx)
  have hi_unique (i : κ) (x : α) (hx : x ∈ kept) (hcol : d x = i) :
      x ∈ keep i := by
    rcases (Finset.mem_biUnion.mp hx) with ⟨j,hj,hxj⟩
    have hcolj := hi_keep_of j x hxj
    have : j = i := hcolj.symm.trans hcol
    simpa [this] using hxj
  -- unused points are put in bijection with the outstanding colour slots
  let Free := {x : α // x ∉ kept}
  let Slots := (Σ i : κ, Fin (a i - t i))
  letI : Fintype Free := Fintype.ofFinite _
  letI : Fintype Slots := inferInstance
  have hfree_card : Fintype.card Free = Fintype.card α - kept.card := by
    simpa [Free, Fintype.card_coe] using
      (Fintype.card_subtype_compl (fun x : α => x ∈ kept))
  have hslots_card : Fintype.card Slots = ∑ i : κ, (a i - t i) := by
    simp [Slots]
  have ht_a (i : κ) : t i ≤ a i := min_le_left _ _
  have hsum_a : (∑ i : κ, a i) = Fintype.card α := by
    simpa [a] using sum_card_colorFiber c
  have hsum_sub : (∑ i : κ, (a i - t i)) = (∑ i : κ, a i) - (∑ i : κ, t i) := by
    classical
    exact Finset.sum_tsub_distrib (Finset.univ : Finset κ)
      (by intro i hi; exact ht_a i)
  have heq_card : Fintype.card Free = Fintype.card Slots := by
    rw [hfree_card, hslots_card, hsum_sub, hsum_a, hkept_card]
  let put : Free ≃ Slots := Fintype.equivOfCardEq heq_card
  let d' : α → κ := fun x => if hx : x ∈ kept then d x else (put ⟨x,hx⟩).1
  refine ⟨d', ?_, ?_⟩
  · intro i
    -- split the fibre into the retained part and the filled slots
    let old : Finset α := keep i
    let fresh : Finset α := Finset.univ.filter
        (fun x : α => x ∉ kept ∧ d' x = i)
    have hold_sub : old ⊆ colorFiber d' i := by
      intro x hx
      have hk' : x ∈ kept := Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, hx⟩
      apply (mem_colorFiber d' i x).2
      dsimp [d']
      simp [hk', hi_keep_of i x hx]
    have hfresh_sub : fresh ⊆ colorFiber d' i := by
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      exact (mem_colorFiber d' i x).2 hx'.2
    have hdecomp : colorFiber d' i = old ∪ fresh := by
      apply Finset.Subset.antisymm ?_ ?_
      · intro x hx
        have hdx : d' x = i := (mem_colorFiber d' i x).1 hx
        by_cases hkx : x ∈ kept
        · have hdx0 : d x = i := by
            simpa [d', hkx] using hdx
          exact Finset.mem_union_left _ (hi_unique i x hkx hdx0)
        · have hv : (put ⟨x,hkx⟩ : Slots).1 = i := by
            simpa [d', hkx] using hdx
          exact Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              ⟨hkx, by simpa [d', hkx] using hdx⟩⟩)
      · intro x hx
        rcases Finset.mem_union.mp hx with ho | hf
        · exact hold_sub ho
        · exact hfresh_sub hf
    have hdis : Disjoint old fresh := by
      apply Finset.disjoint_left.mpr
      intro x ho hf
      have hn := (Finset.mem_filter.mp hf).2.1
      exact hn (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ho⟩)
    have hfresh_card : fresh.card = a i - t i := by
      -- First forget the ambient `α` and regard a fresh point as a free
      -- point whose assigned slot carries colour `i`.
      let Fresh := {x : Free // (put x : Slots).1 = i}
      let ech : ↥fresh ≃ Fresh :=
        { toFun := fun x =>
            ⟨⟨x.1, (Finset.mem_filter.mp x.2).2.1⟩,
              (by
                have hxv := (Finset.mem_filter.mp x.2).2.2
                have hn := (Finset.mem_filter.mp x.2).2.1
                simpa [d', hn] using hxv)⟩
          invFun := fun z =>
            ⟨z.1.1, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _,
                ⟨z.1.2, by
                  have hz := z.2
                  simpa [d', z.1.2] using hz⟩⟩⟩
          left_inv := by
            intro x; cases x; rfl
          right_inv := by
            intro z; cases z with
            | mk z hz => cases z; rfl }
      let eput : Fresh ≃ {z : Slots // z.1 = i} :=
        Equiv.subtypeEquiv put (fun x => Iff.rfl)
      let elast : {z : Slots // z.1 = i} ≃ Fin (a i - t i) :=
        { toFun := fun z => by
            rcases z with ⟨⟨j,v⟩, h⟩
            change j = i at h
            subst j
            exact v
          invFun := fun v => ⟨⟨i,v⟩, rfl⟩
          left_inv := by
            intro z
            rcases z with ⟨⟨j,v⟩, h⟩
            change j = i at h
            subst j
            rfl
          right_inv := by intro v; rfl }
      have hec := Fintype.card_congr (ech.trans (eput.trans elast))
      -- the subtype of a finset has its expected card
      simpa [Fintype.card_coe] using hec
    rw [hdecomp, Finset.card_union_of_disjoint hdis]
    rw [hkeep_card, hfresh_card]
    exact Nat.add_sub_of_le (ht_a i)
  · -- every changed point is fresh
    have hsub : (Finset.univ.filter (fun x : α => d' x ≠ d x)) ⊆
          (Finset.univ.filter (fun x : α => x ∉ kept)) := by
      intro x hx
      have hne := (Finset.mem_filter.mp hx).2
      have hxu := (Finset.mem_filter.mp hx).1
      by_cases hkx : x ∈ kept
      · exfalso
        exact hne (by simp [d', hkx])
      · exact Finset.mem_filter.mpr ⟨hxu,hkx⟩
    have hcard := Finset.card_le_card hsub
    have hfilt : (Finset.univ.filter (fun x : α => x ∉ kept)).card =
          Fintype.card Free := by
      -- both sides are the cardinal of the complement
      rw [hfree_card]
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset α)) (p := fun x : α => x ∈ kept)
      have hs : (Finset.univ.filter (fun x : α => x ∈ kept)) = kept := by
        ext x; simp
      rw [hs] at hpart
      -- the second filtered set is definitionally our complement
      change kept.card + (Finset.univ.filter (fun x : α => x ∉ kept)).card =
          Fintype.card α at hpart
      omega
    -- the complement cardinal is the sum of the deficits
    rw [hfilt, hfree_card, hkept_card, ← hsum_a, ← hsum_sub]
      at hcard
    exact hcard

end
end HalmosSupport

end
-- END INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/ColorRound.lean

-- BEGIN INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/Equipart.lean
section
open MeasureTheory
open scoped ENNReal BigOperators

namespace HalmosSupport

-- calculations for carving one of k+2 equal pieces from a finite mass.
lemma ofReal_one_div_succ_lt_one (k : ℕ) :
    ENNReal.ofReal (1 / ( (k+2 : ℕ) : ℝ)) < (1 : ENNReal) := by
  have hp : (0:ℝ) < (k+2 : ℕ) := by exact_mod_cast (Nat.zero_lt_succ (k+1))
  have hlt : (1/((k+2:ℕ):ℝ)) < (1:ℝ) := by
    have hbig : (1:ℝ) < (k+2:ℕ) := by exact_mod_cast (Nat.lt_succ.mpr (Nat.zero_lt_succ k))
    exact (div_lt_one hp).2 hbig
  -- translate through ofReal
  have hnon : 0 ≤ (1:ℝ) := by norm_num
  -- the iff form only needs positivity of RHS
  exact (by simpa using ((ENNReal.ofReal_lt_ofReal_iff (p := (1/((k+2:ℕ):ℝ))) (by norm_num : (0:ℝ)<1)).2 hlt))

lemma ofReal_one_div_pos (k : ℕ) :
    0 < ENNReal.ofReal (1 / ((k+1:ℕ):ℝ)) := by
  apply ENNReal.ofReal_pos.2
  have h : (0:ℝ) < (k+1:ℕ) := by exact_mod_cast Nat.zero_lt_succ k
  positivity

lemma mass_step_formula (a : ENNReal) (ha : a ≠ ⊤) (k : ℕ) :
    (a - a * ENNReal.ofReal (1 / ((k+2:ℕ):ℝ))) *
        ENNReal.ofReal (1 / ((k+1:ℕ):ℝ))
      = a * ENNReal.ofReal (1 / ((k+2:ℕ):ℝ)) := by
  -- both sides are finite, so compare their real values
  let q : ENNReal := ENNReal.ofReal (1 / ((k+2:ℕ):ℝ))
  let p : ENNReal := ENNReal.ofReal (1 / ((k+1:ℕ):ℝ))
  have hkp : (0:ℝ) < ((k+1:ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_succ k
  have hkq : (0:ℝ) < ((k+2:ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_succ (k+1)
  have hp0r : (0:ℝ) ≤ (1 / ((k+1:ℕ):ℝ)) := (by positivity)
  have hq0r : (0:ℝ) ≤ (1 / ((k+2:ℕ):ℝ)) := (by positivity)
  have hp_top : p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hq_top : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have haq_top : a * q ≠ ⊤ := ENNReal.mul_ne_top ha hq_top
  have hsub_top : a - a*q ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (tsub_le_self) (lt_top_iff_ne_top.mpr ha))
  have hl_top : (a - a*q) * p ≠ ⊤ := ENNReal.mul_ne_top hsub_top hp_top
  have hr_top : a*q ≠ ⊤ := haq_top
  have hqle : a*q ≤ a := by
    have hqle1 : q ≤ 1 := le_of_lt (by
      change ENNReal.ofReal (1 / ((k+2:ℕ):ℝ)) < (1:ENNReal) at *
      exact ofReal_one_div_succ_lt_one k)
    simpa [mul_one] using (mul_le_mul_left' hqle1 a)
  change (a - a*q) * p = a*q
  apply (ENNReal.toReal_eq_toReal_iff' hl_top hr_top).1
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_sub_of_le hqle ha]
  -- simplification of the remaining products is automatic: `toReal_mul` was
  -- already used underneath the subtraction by the previous rewrite.
  simp only [p, q, ENNReal.toReal_ofReal hp0r]
  -- At this point `q` still occurs under products; expose those two products
  -- before rewriting the value of `ofReal`. This avoids syntactic changes of
  -- `1 / t` to an inverse interfering with rewriting.
  simp only [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal hq0r]
  -- there is a second occurrence, on the right hand side
  -- `rw` rewrites both occurrences at once if present.
  field_simp <;> simp [Nat.cast_add, Nat.cast_one]
  left
  ring


lemma diff_mass_pos (a : ENNReal) (ha0 : 0 < a) (ha : a ≠ ⊤) (k : ℕ) :
    0 < a - a * ENNReal.ofReal (1 / ((k+2:ℕ):ℝ)) := by
  apply (tsub_pos_iff_lt).2
  have hq : ENNReal.ofReal (1 / ((k+2:ℕ):ℝ)) < (1: ENNReal) :=
    ofReal_one_div_succ_lt_one k
  have hm := ENNReal.mul_lt_mul_left (ne_of_gt ha0) ha hq
  -- hm is q*a < 1*a
  simpa [mul_comm] using hm

/- A splitting operation is the only analytic input. The rest is a finite induction. -/
theorem equal_partition_of_splittable
    {X : Type*} [MeasurableSpace X] (m : Measure X) [IsFiniteMeasure m]
    (split : ∀ (C : Set X), MeasurableSet C → 0 < m C →
      ∀ {r : ℝ}, 0 < r → r < 1 →
        ∃ D : Set X, MeasurableSet D ∧ D ⊆ C ∧
          m D = m C * ENNReal.ofReal r) :
    ∀ (k : ℕ) (C : Set X), MeasurableSet C → 0 < m C →
      ∃ P : Fin (k+1) → Set X,
        (∀ i, MeasurableSet (P i)) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (⋃ i, P i) = C ∧
        (∀ i, m (P i) = m C * ENNReal.ofReal (1 / ((k+1:ℕ):ℝ))) := by
  intro k
  induction k with
  | zero =>
      intro C hC hp
      let P : Fin (0+1) → Set X := fun _ => C
      refine ⟨P, ?_, ?_, ?_, ?_⟩
      · intro i
        exact hC
      · intro i j hne
        have hi : i = (0 : Fin 1) := Fin.eq_zero i
        have hj : j = (0 : Fin 1) := Fin.eq_zero j
        have h : i = j := hi.trans hj.symm
        exact (hne h).elim
      · ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
          exact hi
        · intro hx
          exact Set.mem_iUnion.2 ⟨(0 : Fin 1), hx⟩
      · intro i
        have hval : (1 / (((0:ℕ)+1:ℕ):ℝ)) = (1:ℝ) := by norm_num
        simp [P, hval]
  | succ k ih =>
      intro C hC hpC
      -- choose the first of k+2 pieces
      have hr0 : (0:ℝ) < 1 / ((k+2:ℕ):ℝ) := by positivity
      have hr1 : (1 / ((k+2:ℕ):ℝ)) < (1:ℝ) := by
        have ht := ofReal_one_div_succ_lt_one k
        -- reflect to reals
        exact (ENNReal.ofReal_lt_ofReal_iff (p := (1/((k+2:ℕ):ℝ))) (by norm_num : (0:ℝ)<1)).1 (by simpa using ht)
      obtain ⟨D, hD, hDC, hmassD⟩ := split C hC hpC hr0 hr1
      let E : Set X := C \ D
      have hE : MeasurableSet E := hC.diff hD
      have hmassE : m E = m C - m D := by
        simpa [E] using (measure_diff hDC hD.nullMeasurableSet (measure_ne_top m D))
      have hposE : 0 < m E := by
        rw [hmassE, hmassD]
        exact diff_mass_pos (m C) hpC (measure_ne_top m C) k
      obtain ⟨Q, hQmeas, hQdisj, hQunion, hQmass⟩ := ih E hE hposE
      let P : Fin ((k+1)+1) → Set X := Fin.cases D Q
      have hPE0 : P 0 = D := rfl
      have hPEs (i : Fin (k+1)) : P i.succ = Q i := rfl
      refine ⟨P, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hD
        · exact hQmeas _
      · -- pairwise disjoint; stating the motives avoids dependent `Fin.cases` surprises
        intro i
        refine Fin.cases (motive := fun i =>
          ∀ j, i ≠ j → Disjoint (P i) (P j)) ?_ ?_ i
        · intro j
          refine Fin.cases (motive := fun j =>
            (0 : Fin ((k+1)+1)) ≠ j → Disjoint (P 0) (P j)) ?_ ?_ j
          · intro h; exact (h rfl).elim
          · intro j' hj
            -- D is disjoint from every tail piece, as tails lie in `E=C\D`.
            change Disjoint D (Q j')
            apply Set.disjoint_left.2
            intro x hxD hxQ
            have hxE : x ∈ E := by
              have hxU : x ∈ ⋃ t, Q t := Set.mem_iUnion.2 ⟨j', hxQ⟩
              rw [hQunion] at hxU
              exact hxU
            exact hxE.2 hxD
        · intro i'
          intro j
          refine Fin.cases (motive := fun j =>
            (Fin.succ i' : Fin ((k+1)+1)) ≠ j →
              Disjoint (P i'.succ) (P j)) ?_ ?_ j
          · intro hj
            change Disjoint (Q i') D
            apply Set.disjoint_left.2
            intro x hxQ hxD
            have hxE : x ∈ E := by
              have hxU : x ∈ ⋃ t, Q t := Set.mem_iUnion.2 ⟨i', hxQ⟩
              rw [hQunion] at hxU
              exact hxU
            exact hxE.2 hxD
          · intro j' hne'
            change Disjoint (Q i') (Q j')
            exact hQdisj i' j' (by
              intro hh
              apply hne'
              exact congrArg Fin.succ hh)
      · -- union of the first piece and the tail recovers C
        -- it is slightly easier to prove both inclusions pointwise
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
          refine Fin.cases (motive := fun i => x ∈ P i → x ∈ C)
            ?_ (fun j hj => ?_) i hi
          · intro hx0
            exact hDC hx0
          · have hxE : x ∈ E := by
              have : x ∈ ⋃ t, Q t := Set.mem_iUnion.2 ⟨j, hj⟩
              simpa [hQunion] using this
            exact hxE.1
        · intro hxC
          by_cases hxD : x ∈ D
          · exact Set.mem_iUnion.2 ⟨0, hxD⟩
          · have hxE : x ∈ E := ⟨hxC, hxD⟩
            have hu : x ∈ ⋃ t, Q t := by simpa [hQunion] using hxE
            rcases Set.mem_iUnion.1 hu with ⟨j, hj⟩
            exact Set.mem_iUnion.2 ⟨j.succ, hj⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · -- the first piece
          simpa [P, Nat.cast_add, Nat.cast_one, add_assoc] using hmassD
        · -- all remaining k+1 pieces have the same mass as the first
          have hqm := hQmass j
          -- Q-mass is expressed with E; replace it with C and calculate.
          rw [hmassE, hmassD] at hqm
          have hformula := mass_step_formula (m C) (measure_ne_top m C) k
          -- desired target agrees with the carved fraction.
          -- rewrite arithmetic of dimensions.
          have hqtarget :
              m C * ENNReal.ofReal (1 / (((Nat.succ k)+1:ℕ):ℝ)) =
                m C * ENNReal.ofReal (1 / ((k+2:ℕ):ℝ)) := by
            rfl
          change m (Q j) = m C * ENNReal.ofReal (1 / (((Nat.succ k)+1:ℕ):ℝ))
          -- ih had k+1 in its denominator
          calc
            m (Q j) = (m C - m C * ENNReal.ofReal (1 / ((k+2:ℕ):ℝ))) *
                ENNReal.ofReal (1 / ((k+1:ℕ):ℝ)) := by
                  simpa using hqm
            _ = m C * ENNReal.ofReal (1 / ((k+2:ℕ):ℝ)) := hformula
            _ = _ := hqtarget.symm

end HalmosSupport

end
-- END INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/Equipart.lean

-- BEGIN INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/MarkerClock.lean
section
/-!
Elementary finite word clocks.  A convenient way of obtaining a *balanced*
colour on a window is to choose a site using only marker (or ``tag'')
coordinates, and then read an independent colour at that site.  One may
rotate the colour by any power depending on the chosen site.  The resulting
map is exactly uniform.  This is the balance half of the Rokhlin/marker
construction; importantly it is exact cardinal arithmetic, not a statement
modulo measure or a limiting argument.
-/
namespace HalmosSupport
open Classical

section Fibres
variable {ι α β : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype α] [Fintype β]

/-- A colour read from a tagged word.  The selector is allowed to be
completely arbitrary, as long as it sees only the tags. -/
noncomputable def clockColor (σ : α ≃ α)
    (sel : (ι → β) → ι) (phase : ι → ℕ)
    (w : ι → (α × β)) : α := by
  classical
  let tags : ι → β := fun i => (w i).2
  let j : ι := sel tags
  exact (σ ^ (phase j)) ((w j).1)

/-- Replace the decoded colour of a word by `d`.  Tags are never touched.
The selected position is computed with the original tags, so after a
replacement it is still the selected position. -/
noncomputable def setClockColor (σ : α ≃ α)
    (sel : (ι → β) → ι) (phase : ι → ℕ) (d : α)
    (w : ι → (α × β)) : ι → (α × β) := by
  classical
  let j : ι := sel (fun i => (w i).2)
  exact fun i => if h : i = j
    then (((σ ^ (phase j)).symm d), (w i).2)
    else w i

@[simp] lemma setClockColor_tag (σ : α ≃ α)
    (sel : (ι → β) → ι) (phase : ι → ℕ) (d : α)
    (w : ι → (α × β)) (i : ι) :
    (setClockColor σ sel phase d w i).2 = (w i).2 := by
  classical
  unfold setClockColor
  split_ifs <;> rfl

lemma setClockColor_tags (σ : α ≃ α)
    (sel : (ι → β) → ι) (phase : ι → ℕ) (d : α)
    (w : ι → (α × β)) :
    (fun i => (setClockColor σ sel phase d w i).2) =
       (fun i => (w i).2) := by
  classical
  funext i
  exact setClockColor_tag σ sel phase d w i

@[simp] lemma clockColor_setClockColor (σ : α ≃ α)
    (sel : (ι → β) → ι) (phase : ι → ℕ) (d : α)
    (w : ι → (α × β)) :
    clockColor σ sel phase (setClockColor σ sel phase d w) = d := by
  classical
  -- both selections see the same vector of tags
  let j : ι := sel (fun i => (w i).2)
  have htags := setClockColor_tags σ sel phase d w
  -- expose `clockColor`
  change (σ ^ (phase (sel (fun i =>
       (setClockColor σ sel phase d w i).2))))
       ((setClockColor σ sel phase d w
          (sel (fun i => (setClockColor σ sel phase d w i).2))).1) = d
  rw [htags]
  -- now the branch at `j` is the one that was overwritten
  dsimp [setClockColor]
  simp

lemma setClockColor_setClockColor (σ : α ≃ α)
    (sel : (ι → β) → ι) (phase : ι → ℕ) (d d' : α)
    (w : ι → (α × β)) :
    setClockColor σ sel phase d'
        (setClockColor σ sel phase d w) =
      setClockColor σ sel phase d' w := by
  classical
  have htags : (fun i => (setClockColor σ sel phase d w i).2) =
       (fun i => (w i).2) := setClockColor_tags σ sel phase d w
  funext i
  -- unfold the *outside* replacement first; at this point its selector is
  -- still visible, so the tag identity can be rewritten once and for all.
  change (if hi : i = sel (fun k => (setClockColor σ sel phase d w k).2)
     then (((σ ^ (phase (sel (fun k =>
              (setClockColor σ sel phase d w k).2)))).symm d'),
                (setClockColor σ sel phase d w i).2)
     else setClockColor σ sel phase d w i) =
    (if hi : i = sel (fun k => (w k).2)
     then (((σ ^ (phase (sel (fun k => (w k).2)))).symm d'),
                (w i).2)
     else w i)
  rw [htags]
  by_cases h : i = sel (fun k => (w k).2)
  · simp [h, setClockColor_tag]
  · -- outside the selected position both replacements are the identity
    simp [h, setClockColor]

/-- On a fibre, writing its value back does nothing. -/
lemma setClockColor_eq_self_of_clockColor_eq (σ : α ≃ α)
    (sel : (ι → β) → ι) (phase : ι → ℕ) {b : α}
    (w : ι → (α × β))
    (hw : clockColor σ sel phase w = b) :
    setClockColor σ sel phase b w = w := by
  classical
  let j : ι := sel (fun i => (w i).2)
  funext i
  by_cases h : i = j
  · subst i
    -- at the selected position `hw` solves for the old colour
    have hv : (σ ^ (phase j)) ((w j).1) = b := by
      simpa [clockColor, j] using hw
    have hv' : (σ ^ (phase j)).symm b = (w j).1 :=
      (Equiv.symm_apply_eq (σ ^ (phase j))).2 hv.symm
    simp [setClockColor, j, hv']
  · simp [setClockColor, j, h]

/-- All colours have the same number of words.  This is the little exact
balance lemma used in marker/clock constructions.  No nonemptiness of the
tag alphabet is required; if a word type is empty both sides are empty. -/
lemma card_clockColor_fiber_eq (σ : α ≃ α)
    (sel : (ι → β) → ι) (phase : ι → ℕ) (b c : α) :
    Nat.card {w : (ι → (α × β)) // clockColor σ sel phase w = b} =
    Nat.card {w : (ι → (α × β)) // clockColor σ sel phase w = c} := by
  classical
  -- simply overwrite the chosen colour
  let F :
      {w : (ι → (α × β)) // clockColor σ sel phase w = b} →
        {w : (ι → (α × β)) // clockColor σ sel phase w = c} :=
    fun w => ⟨setClockColor σ sel phase c w.1,
       clockColor_setClockColor σ sel phase c w.1⟩
  let G :
      {w : (ι → (α × β)) // clockColor σ sel phase w = c} →
        {w : (ι → (α × β)) // clockColor σ sel phase w = b} :=
    fun w => ⟨setClockColor σ sel phase b w.1,
       clockColor_setClockColor σ sel phase b w.1⟩
  let E : {w : (ι → (α × β)) // clockColor σ sel phase w = b} ≃
        {w : (ι → (α × β)) // clockColor σ sel phase w = c} :=
    { toFun := F
      invFun := G
      left_inv := by
        intro w
        apply Subtype.ext
        change setClockColor σ sel phase b
           (setClockColor σ sel phase c w.1) = w.1
        rw [setClockColor_setClockColor]
        exact setClockColor_eq_self_of_clockColor_eq σ sel phase w.1 w.2
      right_inv := by
        intro w
        apply Subtype.ext
        change setClockColor σ sel phase c
           (setClockColor σ sel phase b w.1) = w.1
        rw [setClockColor_setClockColor]
        exact setClockColor_eq_self_of_clockColor_eq σ sel phase w.1 w.2 }
  exact Nat.card_congr E

end Fibres
end HalmosSupport

namespace HalmosSupport
open Classical
section First
variable {β : Type*} [DecidableEq β]

/-- First marked site of a nonempty linear window.  If a window has no
marker we use its left end; the no-marker case is deliberately counted as
bad later. -/
noncomputable def firstMarker (n : ℕ) (hn : 0 < n) (star : β)
    (u : Fin n → β) : Fin n := by
  classical
  by_cases h : ∃ i : ℕ, ∃ hi : i < n, u ⟨i,hi⟩ = star
  · let m : ℕ := Nat.find h
    have hm : ∃ hi : m < n, u ⟨m,hi⟩ = star := Nat.find_spec h
    exact ⟨m, hm.choose⟩
  · exact ⟨0, hn⟩

lemma firstMarker_eq_find (n : ℕ) (hn : 0 < n) (star : β)
    (u : Fin n → β)
    (h : ∃ i : ℕ, ∃ hi : i < n, u ⟨i,hi⟩ = star) :
    (firstMarker n hn star u).val = Nat.find h := by
  classical
  simp [firstMarker, h]

lemma firstMarker_mem (n : ℕ) (hn : 0 < n) (star : β)
    (u : Fin n → β)
    {i : ℕ} (hi : i < n) (hmark : u ⟨i,hi⟩ = star) :
    u (firstMarker n hn star u) = star := by
  classical
  have h : ∃ t : ℕ, ∃ ht : t < n, u ⟨t,ht⟩ = star :=
    ⟨i, hi, hmark⟩
  obtain ⟨hm_lt, hm_val⟩ := Nat.find_spec h
  have heq : firstMarker n hn star u = ⟨Nat.find h, hm_lt⟩ := by
    apply Fin.ext
    exact firstMarker_eq_find n hn star u h
  rw [heq]
  exact hm_val

lemma firstMarker_le (n : ℕ) (hn : 0 < n) (star : β)
    (u : Fin n → β)
    {i : ℕ} (hi : i < n) (hmark : u ⟨i,hi⟩ = star) :
    (firstMarker n hn star u).val ≤ i := by
  classical
  have h : ∃ t : ℕ, ∃ ht : t < n, u ⟨t,ht⟩ = star :=
    ⟨i, hi, hmark⟩
  rw [firstMarker_eq_find n hn star u h]
  exact Nat.find_min' h ⟨hi, hmark⟩

/-- On two overlapping windows the first-marker selectors refer to the same
absolute site, except for two transparent exceptional cases: a fresh marker
at the old left endpoint, or no marker in the overlap at all. -/
lemma firstMarker_overlap
    (N : ℕ) (hN1 : 1 < N) (star : β)
    (z : Fin (N+1) → β)
    (hleft : z ⟨0, Nat.succ_pos _⟩ ≠ star)
    (hover : ∃ t : ℕ, ∃ ht0 : 0 < t, ∃ htN : t < N,
          z ⟨t, Nat.lt_succ_of_lt htN⟩ = star) :
    let prev : Fin N → β := fun i => z ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
    let pres : Fin N → β := fun i => z ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩
    (firstMarker N (lt_trans (by decide : 0 < 1) hN1) star prev).val =
       (firstMarker N (lt_trans (by decide : 0 < 1) hN1) star pres).val + 1 := by
  classical
  let hn : 0 < N := lt_trans (by decide : 0 < 1) hN1
  let prev : Fin N → β := fun i => z ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  let pres : Fin N → β := fun i => z ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩
  change (firstMarker N hn star prev).val =
       (firstMarker N hn star pres).val + 1
  rcases hover with ⟨t, ht0, htN, ht⟩
  have htminus : t-1 < N := by omega
  have htmark : pres ⟨t-1, htminus⟩ = star := by
    dsimp [pres]
    have heq : t - 1 + 1 = t := by omega
    simpa [heq] using ht
  let j : Fin N := firstMarker N hn star pres
  have hjmark : pres j = star :=
    firstMarker_mem N hn star pres htminus htmark
  have hjle : j.val ≤ t-1 :=
    firstMarker_le N hn star pres htminus htmark
  have hjs : j.val + 1 < N := by omega
  have hprevj : prev ⟨j.val+1, hjs⟩ = star := by
    -- both expressions read the same absolute site
    change z ⟨j.val+1, _⟩ = star
    exact hjmark
  let i : Fin N := firstMarker N hn star prev
  have himark : prev i = star :=
    firstMarker_mem N hn star prev hjs hprevj
  have hile : i.val ≤ j.val + 1 :=
    firstMarker_le N hn star prev hjs hprevj
  have hine0 : i.val ≠ 0 := by
    intro hz
    have hz' : prev i = z ⟨0, Nat.succ_pos _⟩ := by
      dsimp [prev]
      congr
    exact hleft (by simpa [hz'] using himark)
  have hge : j.val + 1 ≤ i.val := by
    by_contra hbad
    have hlt : i.val < j.val + 1 := (Nat.lt_of_not_ge hbad)
    have hipos : 0 < i.val := Nat.pos_of_ne_zero hine0
    have himin : i.val - 1 < N := by omega
    have hpmark : pres ⟨i.val-1, himin⟩ = star := by
      change z ⟨i.val - 1 + 1, _⟩ = star
      have heq : i.val - 1 + 1 = i.val := by omega
      -- rewrite to the value seen in the previous window
      change z _ = star at himark
      simpa [heq] using himark
    have hjmin : j.val ≤ i.val - 1 :=
      firstMarker_le N hn star pres himin hpmark
    omega
  exact le_antisymm hile hge

end First
end HalmosSupport
namespace HalmosSupport
open Classical
section Advance
variable {α β : Type*} [DecidableEq β]

lemma clockColor_overlap_advance (σ : α ≃ α)
    (N : ℕ) (hN1 : 1 < N) (star : β)
    (z : Fin (N+1) → (α × β))
    (hleft : (z ⟨0, Nat.succ_pos _⟩).2 ≠ star)
    (hover : ∃ t : ℕ, ∃ ht0 : 0 < t, ∃ htN : t < N,
          (z ⟨t, Nat.lt_succ_of_lt htN⟩).2 = star) :
    let prev : Fin N → (α × β) :=
       fun i => z ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
    let pres : Fin N → (α × β) :=
       fun i => z ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩
    clockColor σ (firstMarker N
          (lt_trans (by decide : 0 < 1) hN1) star)
       (fun i : Fin N => N-1-i.val) pres =
      σ (clockColor σ (firstMarker N
          (lt_trans (by decide : 0 < 1) hN1) star)
       (fun i : Fin N => N-1-i.val) prev) := by
  classical
  let hn : 0 < N := lt_trans (by decide : 0 < 1) hN1
  let prev : Fin N → (α × β) :=
       fun i => z ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  let pres : Fin N → (α × β) :=
       fun i => z ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩
  change clockColor σ (firstMarker N hn star)
       (fun i : Fin N => N-1-i.val) pres =
      σ (clockColor σ (firstMarker N hn star)
       (fun i : Fin N => N-1-i.val) prev)
  have hind := firstMarker_overlap N hN1 star
       (fun i => (z i).2) hleft hover
  change (firstMarker N hn star (fun i => (prev i).2)).val =
       (firstMarker N hn star (fun i => (pres i).2)).val + 1 at hind
  let i : Fin N := firstMarker N hn star (fun k => (prev k).2)
  let j : Fin N := firstMarker N hn star (fun k => (pres k).2)
  have hv : i.val = j.val + 1 := hind
  have hcore : (prev i).1 = (pres j).1 := by
    dsimp [prev, pres]
    apply congrArg (fun p : α × β => p.1)
      (show z ⟨i.val, _⟩ = z ⟨j.val+1, _⟩ by
        congr 1
        apply Fin.ext
        exact hv)
  change (σ ^ (N-1-j.val)) ((pres j).1) =
    σ ((σ ^ (N-1-i.val)) ((prev i).1))
  have hiN : i.val < N := i.isLt
  have hjN : j.val < N := j.isLt
  have hexp : N-1-j.val = (N-1-i.val) + 1 := by
    omega
  rw [hexp]
  -- `pow_succ` computes composition with one more permutation
  rw [pow_succ, (Commute.refl σ).pow_left (N-1-i.val)]
  change σ ((σ ^ (N-1-i.val)) ((pres j).1)) = _
  rw [hcore]
end Advance
end HalmosSupport

namespace HalmosSupport
open Classical
/-- Two uniformly distributed readings of the *same* finite word have the
same fibres.  It is enough to know that every fibre of each reading has the
same size; no formula for that size is needed.  This avoids all powers and
subtractions when a marker window is embedded in a larger union window. -/
lemma card_fiber_eq_of_constant
    {Ω γ : Type*} [Fintype Ω] [Fintype γ] [Nonempty γ]
    (f g : Ω → γ)
    (hf : ∀ b c : γ, Nat.card {x : Ω // f x = b} =
                          Nat.card {x : Ω // f x = c})
    (hg : ∀ b c : γ, Nat.card {x : Ω // g x = b} =
                          Nat.card {x : Ω // g x = c}) :
    ∀ b : γ, Nat.card {x : Ω // f x = b} =
             Nat.card {x : Ω // g x = b} := by
  classical
  let b0 : γ := Classical.choice (inferInstance : Nonempty γ)
  have hsumf : (∑ b : γ, Nat.card {x : Ω // f x = b}) =
        Nat.card Ω := by
    have hsig := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
    rw [Fintype.card_sigma] at hsig
    simpa [Nat.card_eq_fintype_card] using hsig
  have hsumg : (∑ b : γ, Nat.card {x : Ω // g x = b}) =
        Nat.card Ω := by
    have hsig := Fintype.card_congr (Equiv.sigmaFiberEquiv g)
    rw [Fintype.card_sigma] at hsig
    simpa [Nat.card_eq_fintype_card] using hsig
  have hconstf : (∑ b : γ, Nat.card {x : Ω // f x = b}) =
        Fintype.card γ * (Nat.card {x : Ω // f x = b0}) := by
    simp_rw [hf _ b0]
    simp
  have hconstg : (∑ b : γ, Nat.card {x : Ω // g x = b}) =
        Fintype.card γ * (Nat.card {x : Ω // g x = b0}) := by
    simp_rw [hg _ b0]
    simp
  have hmul : Fintype.card γ * (Nat.card {x : Ω // f x = b0}) =
          Fintype.card γ * (Nat.card {x : Ω // g x = b0}) := by
    rw [← hconstf, ← hconstg, hsumf, hsumg]
  have hpos : 0 < Fintype.card γ := Fintype.card_pos
  have hz : Nat.card {x : Ω // f x = b0} =
          Nat.card {x : Ω // g x = b0} := by
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
  intro b
  calc
    Nat.card {x : Ω // f x = b} =
        Nat.card {x : Ω // f x = b0} := hf b b0
    _ = Nat.card {x : Ω // g x = b0} := hz
    _ = Nat.card {x : Ω // g x = b} := (hg _ _).symm
end HalmosSupport
namespace HalmosSupport
open Classical
/-- Taking an independent finite product and then changing coordinates doesn't
alter the fact that all fibres of a reading have the same cardinality. -/
lemma card_fiber_const_prod_equiv
    {Ω U V γ : Type*} [Fintype Ω] [Fintype U] [Fintype V]
    [Fintype γ]
    (e : Ω ≃ (U × V)) (f : U → γ)
    (hf : ∀ b c : γ, Nat.card {x : U // f x = b} =
                          Nat.card {x : U // f x = c}) :
    ∀ b c : γ,
      Nat.card {x : Ω // f (e x).1 = b} =
      Nat.card {x : Ω // f (e x).1 = c} := by
  classical
  intro b c
  let t : {x : U // f x = b} ≃ {x : U // f x = c} :=
    Fintype.equivOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using (hf b c))
  let F : {x : Ω // f (e x).1 = b} → {x : Ω // f (e x).1 = c} :=
    fun x =>
      ⟨ e.symm ⟨(t ⟨(e x.1).1, x.2⟩).1, (e x.1).2⟩,
        (by
          change f (e (e.symm _)).1 = c
          simpa using (t ⟨(e x.1).1, x.2⟩).2) ⟩
  let G : {x : Ω // f (e x).1 = c} → {x : Ω // f (e x).1 = b} :=
    fun x =>
      ⟨ e.symm ⟨(t.symm ⟨(e x.1).1, x.2⟩).1, (e x.1).2⟩,
        (by
          change f (e (e.symm _)).1 = b
          simpa using (t.symm ⟨(e x.1).1, x.2⟩).2) ⟩
  let E : {x : Ω // f (e x).1 = b} ≃ {x : Ω // f (e x).1 = c} :=
    { toFun := F
      invFun := G
      left_inv := by
        intro x
        apply Subtype.ext
        dsimp [F, G]
        simp
      right_inv := by
        intro x
        apply Subtype.ext
        dsimp [F, G]
        simp }
  exact Nat.card_congr E

end HalmosSupport
namespace HalmosSupport
open Classical
/-- Split a finite coordinate tuple into a subblock and its complement.  This
is purely about functions; the order on a finset never matters. -/
noncomputable def splitFinword {δ γ : Type*} [DecidableEq δ]
    (A B : Finset δ) (h : A ⊆ B) :
    (∀ _j : (↥B), γ) ≃
       ((∀ _i : (↥A), γ) × (∀ _i : (↥(B \ A)), γ)) := by
  classical
  let f (z : (∀ _j : (↥B), γ)) :
      ((∀ _i : (↥A), γ) × (∀ _i : (↥(B \ A)), γ)) :=
    ⟨ (fun i => z ⟨i.val, h i.property⟩),
      (fun i => z ⟨i.val, ((Finset.mem_sdiff.mp i.property).1)⟩) ⟩
  let g (z : ((∀ _i : (↥A), γ) × (∀ _i : (↥(B \ A)), γ))) :
        (∀ _j : (↥B), γ) := fun j =>
    if hj : j.val ∈ A then z.1 ⟨j.val, hj⟩
    else z.2 ⟨j.val, Finset.mem_sdiff.mpr ⟨j.property, hj⟩⟩
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro z
        funext j
        by_cases hj : j.val ∈ A
        · simp [f, g, hj]
        · simp [f, g, hj]
      right_inv := by
        intro z
        cases z with
        | mk x y =>
          apply Prod.ext
          · funext i
            simp [f, g, i.property]
          · funext i
            have hi := (Finset.mem_sdiff.mp i.property).2
            simp [f, g, hi] }

/-- Lifting a constant-fibre reading of a subblock to any larger window keeps
its fibres constant. -/
lemma lift_subblock_const_fiber {δ γ κ : Type*}
    [DecidableEq δ] [Fintype γ]
    (A B : Finset δ) (h : A ⊆ B)
    (f : (∀ _i : (↥A), γ) → κ) [Fintype κ]
    (hf : ∀ b c : κ, Nat.card {x : (∀ _i : (↥A), γ) // f x = b} =
                         Nat.card {x : (∀ _i : (↥A), γ) // f x = c}) :
    ∀ b c : κ,
       Nat.card {z : (∀ _j : (↥B), γ) //
          f (fun i => z ⟨i.val, h i.property⟩) = b} =
       Nat.card {z : (∀ _j : (↥B), γ) //
          f (fun i => z ⟨i.val, h i.property⟩) = c} := by
  classical
  let e := splitFinword (γ:=γ) A B h
  have hh := card_fiber_const_prod_equiv e f hf
  -- its first projection is literally restriction
  change ∀ b c : κ,
       Nat.card {z : (∀ _j : (↥B), γ) //
          f (fun i => z ⟨i.val, h i.property⟩) = b} =
       Nat.card {z : (∀ _j : (↥B), γ) //
          f (fun i => z ⟨i.val, h i.property⟩) = c} at hh
  exact hh

/-- Balance on a union window only asks for constant fibres on the small
colour reading.  This form is precisely the first field of `EdgeData` and is
useful independently of whichever marker is used for the rare-edge bound. -/
lemma balance_union_of_const_fiber {δ γ : Type*}
    [DecidableEq δ] [Fintype γ] [Nonempty γ]
    (K L : Finset δ)
    (l : (∀ _j : (↥L), γ) → (∀ _i : (↥K), γ))
    (hl : ∀ b c : (∀ _i : (↥K), γ),
       Nat.card {z : (∀ _j : (↥L), γ) // l z = b} =
       Nat.card {z : (∀ _j : (↥L), γ) // l z = c}) :
    let W : Finset δ := K ∪ L
    let old : (∀ _j : (↥W), γ) → (∀ _i : (↥K), γ) :=
       fun z i => z ⟨i.val, Finset.mem_union_left _ i.property⟩
    let col : (∀ _j : (↥W), γ) → (∀ _i : (↥K), γ) :=
       fun z => l (fun j => z ⟨j.val, Finset.mem_union_right _ j.property⟩)
    ∀ b,
      Nat.card {z : (∀ _j : (↥W), γ) // old z = b} =
      Nat.card {z : (∀ _j : (↥W), γ) // col z = b} := by
  classical
  dsimp
  let W : Finset δ := K ∪ L
  let hK : K ⊆ W := Finset.subset_union_left
  let hL : L ⊆ W := Finset.subset_union_right
  let old : (∀ _j : (↥W), γ) → (∀ _i : (↥K), γ) :=
       fun z i => z ⟨i.val, hK i.property⟩
  let col : (∀ _j : (↥W), γ) → (∀ _i : (↥K), γ) :=
       fun z => l (fun j => z ⟨j.val, hL j.property⟩)
  have hold : ∀ b c : (∀ _i : (↥K), γ),
      Nat.card {z : (∀ _j : (↥W), γ) // old z = b} =
      Nat.card {z : (∀ _j : (↥W), γ) // old z = c} := by
    have hid : ∀ b c : (∀ _i : (↥K), γ),
        Nat.card {z : (∀ _i : (↥K), γ) // (id z) = b} =
        Nat.card {z : (∀ _i : (↥K), γ) // (id z) = c} := by
      intro b c
      -- there is exactly one word in a fibre of the identity; using the
      -- obvious singleton equivalence avoids any `2^|K|` arithmetic.
      exact Nat.card_congr
        { toFun := fun x => ⟨c, rfl⟩
          invFun := fun x => ⟨b, rfl⟩
          left_inv := by intro x; cases x with | mk x hx =>
            apply Subtype.ext; simpa using hx.symm
          right_inv := by intro x; cases x with | mk x hx =>
            apply Subtype.ext; simpa using hx.symm }
    have hh := lift_subblock_const_fiber K W hK
       (id : (∀ _i : (↥K), γ) → (∀ _i : (↥K), γ)) hid
    simpa [old] using hh
  have hcol : ∀ b c : (∀ _i : (↥K), γ),
      Nat.card {z : (∀ _j : (↥W), γ) // col z = b} =
      Nat.card {z : (∀ _j : (↥W), γ) // col z = c} := by
    have hh := lift_subblock_const_fiber L W hL l hl
    simpa [col] using hh
  have hEq := card_fiber_eq_of_constant old col hold hcol
  simpa [W, old, col] using hEq
end HalmosSupport
namespace HalmosSupport
open Classical
lemma card_fiber_const_equiv
    {U V γ : Type*} [Fintype U] [Fintype V]
    (e : U ≃ V) (f : V → γ)
    (hf : ∀ b c : γ, Nat.card {x : V // f x = b} =
                        Nat.card {x : V // f x = c}) :
    ∀ b c : γ, Nat.card {x : U // f (e x) = b} =
                 Nat.card {x : U // f (e x) = c} := by
  classical
  intro b c
  let E (d : γ) : {x : U // f (e x) = d} ≃ {x : V // f x = d} :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun x => ⟨e.symm x.1, (by simpa using x.2)⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp }
  exact (Nat.card_congr (E b)).trans ((hf b c).trans (Nat.card_congr (E c)).symm)

lemma card_clockColor_equiv
    {U ι α β : Type*} [Fintype U] [Fintype ι]
       [DecidableEq ι] [Fintype α] [Fintype β]
    (e : U ≃ (ι → (α × β))) (σ : α ≃ α)
    (pick : (ι → β) → ι) (phase : ι → ℕ) :
    ∀ b c : α,
       Nat.card {x : U // clockColor σ pick phase (e x) = b} =
       Nat.card {x : U // clockColor σ pick phase (e x) = c} := by
  classical
  exact card_fiber_const_equiv e _
    (card_clockColor_fiber_eq σ pick phase)
end HalmosSupport

end
-- END INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/MarkerClock.lean

-- BEGIN INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/MarkerNumeric.lean
section
namespace HalmosSupport
open Filter Topology
/- Quantitative elementary estimate; marker. -/
lemma exists_marker_parameters (r : ℝ) (hr : 0 < r) :
    ∃ b m : ℕ, 0 < b ∧ 0 < m ∧
      ∀ d : ℕ,
        let A : ℕ := 2^d
        let B : ℕ := 2^b
        (((A * (A*B)^(m+1) + (A*B) * (A*(B-1))^m * (A*B) : ℕ) : ENNReal) *
          ((2:ENNReal)⁻¹)^((m+2)*(d+b)) < ENNReal.ofReal r) := by
  -- a tag appears at the old left endpoint with probability `1/B`.
  obtain ⟨b0, hb0⟩ := exists_pow_lt_of_lt_one (K:=ℝ)
    (x := r/2) (y := (1/2:ℝ)) (by linarith) (by norm_num)
  let b : ℕ := b0 + 1
  have hb : 0 < b := by dsimp [b]; omega
  let B : ℕ := 2^b
  have hB1 : 1 < B := by dsimp [B]; exact one_lt_pow₀ (by norm_num) (by omega)
  have hBposR : (0:ℝ) < (B:ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hsmall1 : (1:ℝ) / (B:ℝ) < r / 2 := by
    have hhalf_nonneg : 0 ≤ (1/2:ℝ) := by norm_num
    have hdec : (1/2:ℝ)^b ≤ (1/2:ℝ)^b0 := by
      dsimp [b]
      rw [pow_succ]
      nlinarith [pow_nonneg hhalf_nonneg b0]
    have hlt : (1/2:ℝ)^b < r/2 := lt_of_le_of_lt hdec hb0
    have hpow : (B:ℝ) = (2:ℝ)^b := by dsimp [B]; norm_cast
    rw [hpow]
    simp at hlt
    simpa [div_eq_mul_inv] using hlt
  let t : ℝ := ((B:ℝ) - 1) / (B:ℝ)
  have ht0 : 0 < t := by
    dsimp [t]
    have hx : (1:ℝ) < (B:ℝ) := by exact_mod_cast hB1
    exact div_pos (sub_pos.mpr hx) hBposR
  have ht1 : t < 1 := by
    dsimp [t]
    exact (div_lt_one hBposR).2 (by linarith)
  obtain ⟨m0, hm0⟩ := exists_pow_lt_of_lt_one (K:=ℝ)
      (x := r/2) (y := t) (by linarith) ht1
  let m : ℕ := m0 + 1
  have hm : 0 < m := by dsimp [m]; omega
  have ht_nonneg : 0 ≤ t := le_of_lt ht0
  have ht_le : t ≤ 1 := le_of_lt ht1
  have hdec2 : t^m ≤ t^m0 := by
    dsimp [m]
    rw [pow_succ]
    nlinarith [pow_nonneg ht_nonneg m0]
  have hsmall2 : t^m < r/2 := lt_of_le_of_lt hdec2 hm0
  refine ⟨b, m, hb, hm, ?_⟩
  intro d
  dsimp
  -- name the colour size locally
  let A : ℕ := 2^d
  have hApos : 0 < A := by dsimp [A]; positivity
  have hCpos : (0:ℝ) < (A:ℝ) * (B:ℝ) := by positivity
  have hBA : (A:ℝ) = (2:ℝ)^d := by dsimp [A]; norm_cast
  have hBR : (B:ℝ) = (2:ℝ)^b := by dsimp [B]; norm_cast
  have hden : ((2:ℝ)⁻¹)^((m+2)*(d+b)) = (((A:ℝ)*(B:ℝ))^(m+2))⁻¹ := by
    rw [← one_div]
    rw [one_div, inv_pow]
    congr 1
    rw [hBA, hBR, ← pow_add, ← pow_mul]
    simp [Nat.mul_comm]
  have hrealeq :
      (((((A * (A*B)^(m+1) + (A*B) * (A*(B-1))^m * (A*B) : ℕ) : ENNReal) *
        ((2:ENNReal)⁻¹)^((m+2)*(d+b))).toReal)) =
        (1:ℝ) / (B:ℝ) + t^m := by
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
    push_cast
    rw [hden]
    rw [Nat.cast_sub (by omega : 1 ≤ B)]
    push_cast
    dsimp [t]
    have ha : (A:ℝ) ≠ 0 := by positivity
    have hb' : (B:ℝ) ≠ 0 := by positivity
    rw [pow_add ((A:ℝ)*(B:ℝ)) m 1, pow_add ((A:ℝ)*(B:ℝ)) m 2]
    field_simp
    rw [mul_pow (A:ℝ) (B:ℝ), div_pow]
    field_simp
    rw [mul_pow (A:ℝ) ((B:ℝ)-1)]
    ring
  have hltreal :
      ((((A * (A*B)^(m+1) + (A*B) * (A*(B-1))^m * (A*B) : ℕ) : ENNReal) *
        ((2:ENNReal)⁻¹)^((m+2)*(d+b))).toReal) < r := by
    rw [hrealeq]
    linarith [hsmall1, hsmall2]
  refine (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top (by exact ENNReal.natCast_ne_top _) (by simp))
       (by simp : ENNReal.ofReal r ≠ ⊤)).1 ?_
  rw [ENNReal.toReal_ofReal (le_of_lt hr)]
  change (((((A * (A*B)^(m+1) + (A*B)*(A*(B-1))^m*(A*B) : ℕ) : ENNReal) *
        ((2:ENNReal)⁻¹)^((m+2)*(d+b))).toReal) < r)
  exact hltreal
end HalmosSupport

end
-- END INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/MarkerNumeric.lean

-- BEGIN INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/RealLaw.lean
section
open MeasureTheory Filter Topology Set
open ProbabilityTheory
noncomputable section
namespace HalmosRealLaw

lemma volume_image_scale (a : ℝ) (ha : a ≠ 0) (S : Set ℝ) :
    volume ((fun x : ℝ => a * x) '' S) = ENNReal.ofReal |a| * volume S := by
  have hset : (fun x : ℝ => a * x) '' S = (fun y : ℝ => a⁻¹ * y) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change a⁻¹ * (a*x) ∈ S
      rw [← mul_assoc, inv_mul_cancel₀ ha]
      simpa using hx
    · intro hy
      change a⁻¹ * y ∈ S at hy
      refine ⟨a⁻¹*y, hy, ?_⟩
      change a * (a⁻¹*y) = y
      rw [← mul_assoc, mul_inv_cancel₀ ha]
      simp
  rw [hset, Real.volume_preimage_mul_left (inv_ne_zero ha)]
  congr 1
  have ha0 : 0 ≤ |a| := abs_nonneg _
  have hi : a⁻¹⁻¹ = a := inv_inv a
  -- abs of inverse of inverse
  simp

lemma volume_image_translate (c : ℝ) (S : Set ℝ) :
    volume ((fun x : ℝ => c + x) '' S) = volume S := by
  have hset : (fun x : ℝ => c + x) '' S = (fun y : ℝ => (-c) + y) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change -c + (c+x) ∈ S
      simpa [add_assoc] using hx
    · intro hy
      change -c + y ∈ S at hy
      refine ⟨-c+y, hy, ?_⟩
      abel
  rw [hset]
  have h := (measurePreserving_add_left (volume : Measure ℝ) (-c)).measure_preimage_emb
    ((Homeomorph.addLeft (-c)).measurableEmbedding) S
  simpa using h

lemma volume_cantorSet_zero : (volume : Measure ℝ) cantorSet = 0 := by
  let v : ENNReal := (volume : Measure ℝ) cantorSet
  have hvfin : v ≠ ⊤ := by
    have hsub := cantorSet_subset_unitInterval
    have hle : v ≤ (volume : Measure ℝ) (Set.Icc 0 1) := measure_mono hsub
    have hval : (volume : Measure ℝ) (Set.Icc 0 1) = 1 := by
      simp [Real.volume_Icc]
    rw [hval] at hle
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  have hhalf1 : (volume : Measure ℝ) ((fun x : ℝ => x / 3) '' cantorSet) =
      ENNReal.ofReal (1/3:ℝ) * v := by
    have h := volume_image_scale (1/3:ℝ) (by norm_num) cantorSet
    simpa [div_eq_mul_inv, v, mul_comm, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3)] using h
  have hfun : (fun x : ℝ => x / 3) = (fun x : ℝ => (1/3:ℝ) * x) := by
    funext x; ring
  -- correct previous used simp handles function equality
  have hhalf2 :
      (volume : Measure ℝ) ((fun x : ℝ => (2 + x) / 3) '' cantorSet) =
      ENNReal.ofReal (1/3:ℝ) * v := by
    have heq : (fun x : ℝ => (2 + x) / 3) =
        (fun x : ℝ => (2/3:ℝ) + ((1/3:ℝ)*x)) := by
      funext x; ring
    rw [heq]
    have himg : (fun x : ℝ => (2/3:ℝ) + ((1/3:ℝ)*x)) '' cantorSet =
        (fun y : ℝ => (2/3:ℝ) + y) ''
          ((fun x : ℝ => (1/3:ℝ)*x) '' cantorSet) := by
      rw [← Set.image_comp]
      rfl
    rw [himg, volume_image_translate]
    have h := volume_image_scale (1/3:ℝ) (by norm_num) cantorSet
    simpa [v, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3)] using h
  -- fix first branch via expression
  have hhalf1' : (volume : Measure ℝ) ((fun x : ℝ => x / 3) '' cantorSet) =
      ENNReal.ofReal (1/3:ℝ) * v := by
    rw [hfun]
    have h := volume_image_scale (1/3:ℝ) (by norm_num) cantorSet
    simpa [v, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3)] using h
  have hvle : v ≤ ENNReal.ofReal (2/3:ℝ) * v := by
    have hu := measure_union_le
      ((fun x : ℝ => x/3) '' cantorSet)
      ((fun x : ℝ => (2+x)/3) '' cantorSet) (μ := (volume : Measure ℝ))
    rw [← cantorSet_eq_union_halves] at hu
    rw [hhalf1', hhalf2] at hu
    change v ≤ _ at hu
    calc v ≤ ENNReal.ofReal (1/3:ℝ) * v + ENNReal.ofReal (1/3:ℝ) * v := hu
    _ = ENNReal.ofReal (2/3:ℝ) * v := by
      rw [← add_mul]
      congr 1
      rw [← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num : (0:ℝ) ≤ 1/3)]
      norm_num
  have hreal : v.toReal ≤ (2/3:ℝ) * v.toReal := by
    have := ENNReal.toReal_mono (by exact ENNReal.mul_ne_top (by simp) hvfin) hvle
    norm_num at this ⊢
    exact this
  have hz : v.toReal = 0 := by
    have hnon : 0 ≤ v.toReal := ENNReal.toReal_nonneg
    linarith
  exact (ENNReal.toReal_eq_zero_iff v).1 hz |>.resolve_right hvfin
end HalmosRealLaw
namespace HalmosRealLaw

lemma continuous_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    Continuous (fun x : ℝ => (ProbabilityTheory.cdf ν) x) := by
  apply continuous_iff_continuousAt.2
  intro x
  let f : StieltjesFunction ℝ := ProbabilityTheory.cdf ν
  have hzero : f.measure ({x} : Set ℝ) = 0 := by
    change (ProbabilityTheory.cdf ν).measure ({x} : Set ℝ) = 0
    rw [ProbabilityTheory.measure_cdf]
    exact measure_singleton x
  have hjump : (f : ℝ → ℝ) x - Function.leftLim (f : ℝ → ℝ) x ≤ 0 := by
    rw [StieltjesFunction.measure_singleton] at hzero
    exact ENNReal.ofReal_eq_zero.mp hzero
  have hxleft : Function.leftLim (f : ℝ → ℝ) x = (f : ℝ → ℝ) x := by
    apply le_antisymm
    · exact f.mono.leftLim_le le_rfl
    · exact sub_nonpos.mp hjump
  have hL : ContinuousWithinAt (f : ℝ → ℝ) (Set.Iio x) x :=
    (Monotone.continuousWithinAt_Iio_iff_leftLim_eq f.mono).2 hxleft
  have hR : ContinuousWithinAt (f : ℝ → ℝ) (Set.Ici x) x := f.right_continuous x
  have hu : ContinuousWithinAt (f : ℝ → ℝ) Set.univ x := by
    simpa [Set.Iio_union_Ici] using hL.union hR
  exact (continuousWithinAt_univ _ _).1 hu

lemma exists_cdf_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ x : ℝ, (ProbabilityTheory.cdf ν) x = r := by
  have hc := continuous_cdf ν
  have hlo := ProbabilityTheory.tendsto_cdf_atBot ν
  have hhi := ProbabilityTheory.tendsto_cdf_atTop ν
  have evlo : ∀ᶠ x : ℝ in Filter.atBot, (ProbabilityTheory.cdf ν) x < r :=
    hlo.eventually (Iio_mem_nhds hr0)
  have evhi : ∀ᶠ x : ℝ in Filter.atTop, r < (ProbabilityTheory.cdf ν) x :=
    hhi.eventually (Ioi_mem_nhds hr1)
  obtain ⟨a,ha'⟩ := Filter.eventually_atBot.1 evlo
  obtain ⟨b,hb'⟩ := Filter.eventually_atTop.1 evhi
  have ha := ha' a le_rfl
  have hb := hb' b le_rfl
  have hab : a ≤ b := by
    by_contra hn
    have hm := ProbabilityTheory.monotone_cdf ν (le_of_lt (lt_of_not_ge hn))
    linarith
  have hv := intermediate_value_Icc (α:=ℝ) (δ:=ℝ) hab (hc.continuousOn)
    (show r ∈ Set.Icc ((ProbabilityTheory.cdf ν) a) ((ProbabilityTheory.cdf ν) b) from
      ⟨ha.le, hb.le⟩)
  rcases hv with ⟨x, hx, hxv⟩
  exact ⟨x, hxv⟩

noncomputable def pick (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
    (t : Set.Ioo (0:ℝ) 1) : ℝ :=
  Classical.choose (exists_cdf_eq ν t.property.1 t.property.2)
lemma pick_spec (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
    (t : Set.Ioo (0:ℝ) 1) : (ProbabilityTheory.cdf ν) (pick ν t) = t.1 :=
  Classical.choose_spec (exists_cdf_eq ν t.property.1 t.property.2)
lemma pick_strict (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    StrictMono (pick ν) := by
  intro a b hab
  have hv : (ProbabilityTheory.cdf ν) (pick ν a) <
      (ProbabilityTheory.cdf ν) (pick ν b) := by simpa [pick_spec] using hab
  exact lt_of_not_ge (fun h => not_lt_of_ge
    (ProbabilityTheory.monotone_cdf ν h) hv)
lemma pick_measurable (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    Measurable (pick ν) := (pick_strict ν).monotone.measurable


lemma map_cdf_eq (ν μ : Measure ℝ)
    [IsProbabilityMeasure ν] [NoAtoms ν]
    [IsProbabilityMeasure μ] [NoAtoms μ] :
    Measure.map (fun x : ℝ => (ProbabilityTheory.cdf ν) x) ν =
    Measure.map (fun x : ℝ => (ProbabilityTheory.cdf μ) x) μ := by
  let f := fun x : ℝ => (ProbabilityTheory.cdf ν) x
  let g := fun x : ℝ => (ProbabilityTheory.cdf μ) x
  have hf : Measurable f := (continuous_cdf ν).measurable
  have hg : Measurable g := (continuous_cdf μ).measurable
  letI : IsFiniteMeasure (Measure.map f ν) := Measure.isFiniteMeasure_map ν f
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hf measurableSet_Iic, Measure.map_apply hg measurableSet_Iic]
  change ν {x | (ProbabilityTheory.cdf ν) x ≤ t} = μ {x | (ProbabilityTheory.cdf μ) x ≤ t}
  have evalUpper (ρ : Measure ℝ) [IsProbabilityMeasure ρ] [NoAtoms ρ]
      (t a : ℝ) (hta : t < a) (ha0 : 0 < a) (ha1 : a < 1) :
      ρ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} ≤ ENNReal.ofReal a := by
    let u : Set.Ioo (0:ℝ) 1 := ⟨a, ha0, ha1⟩
    have sub : {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} ⊆ Set.Iic (pick ρ u) := by
      intro x hx
      by_contra hb
      have hbad : pick ρ u < x := lt_of_not_ge hb
      have hm := ProbabilityTheory.monotone_cdf ρ (le_of_lt hbad)
      have hp : (ProbabilityTheory.cdf ρ) (pick ρ u) = a := pick_spec ρ u
      have hlt : t < (ProbabilityTheory.cdf ρ) (pick ρ u) := by rw [hp]; exact hta
      have : (ProbabilityTheory.cdf ρ) x ≤ t := hx
      exact (not_lt_of_ge (hm.trans this)) hlt
    refine le_trans (measure_mono sub) ?_
    rw [← ProbabilityTheory.ofReal_cdf ρ, pick_spec]
  have upper0 (ρ : Measure ℝ) [IsProbabilityMeasure ρ] [NoAtoms ρ]
      (t : ℝ) (ht : t ≤ 0) :
      ρ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} = 0 := by
    let L : ENNReal := ρ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t}
    have topL : L ≠ ⊤ := measure_ne_top _ _
    have nonneg : 0 ≤ L.toReal := ENNReal.toReal_nonneg
    have upper : L.toReal ≤ (0:ℝ) := by
      apply le_of_forall_gt_imp_ge_of_dense
      intro a ha
      by_cases ha1 : a < 1
      · have H : L ≤ ENNReal.ofReal a := evalUpper ρ t a (lt_of_le_of_lt ht ha) ha ha1
        have HH := (ENNReal.toReal_le_toReal topL (by simp)).2 H
        simpa [ENNReal.toReal_ofReal (le_of_lt ha)] using HH
      · have hprob : L ≤ 1 := by
          dsimp [L]; exact prob_le_one
        have hh := (ENNReal.toReal_le_toReal topL (by simp : (1:ENNReal) ≠ ⊤)).2 hprob
        simpa using hh.trans (le_of_not_gt ha1)
    have z : L.toReal = 0 := le_antisymm upper nonneg
    exact (ENNReal.toReal_eq_zero_iff L).1 z |>.resolve_right topL
  by_cases h0 : t ≤ 0
  · rw [upper0 ν t h0, upper0 μ t h0]
  · have ht : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · have eval (ρ : Measure ℝ) [IsProbabilityMeasure ρ] [NoAtoms ρ] :
          ρ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} = ENNReal.ofReal t := by
        let L : ENNReal := ρ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t}
        have topL : L ≠ ⊤ := measure_ne_top _ _
        let u : Set.Ioo (0:ℝ) 1 := ⟨t, ht, h1⟩
        have lower : ENNReal.ofReal t ≤ L := by
          have sub : Set.Iic (pick ρ u) ⊆ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} := by
            intro x hx
            have hm := ProbabilityTheory.monotone_cdf ρ hx
            have hp : (ProbabilityTheory.cdf ρ) (pick ρ u) = t := pick_spec ρ u
            exact hm.trans (le_of_eq hp)
          have H := measure_mono sub (μ:=ρ)
          rw [← ProbabilityTheory.ofReal_cdf ρ, pick_spec] at H
          exact H
        have upper : L.toReal ≤ t := by
          apply le_of_forall_gt_imp_ge_of_dense
          intro a ha
          by_cases ha1 : a < 1
          · have H : L ≤ ENNReal.ofReal a := evalUpper ρ t a ha (lt_trans ht ha) ha1
            have HH := (ENNReal.toReal_le_toReal topL (by simp)).2 H
            simpa [ENNReal.toReal_ofReal (le_of_lt (lt_trans ht ha))] using HH
          · have hprob : L ≤ 1 := by dsimp [L]; exact prob_le_one
            have hh := (ENNReal.toReal_le_toReal topL (by simp : (1:ENNReal)≠⊤)).2 hprob
            exact (by simpa using hh.trans (le_of_not_gt ha1))
        have upENN : L ≤ ENNReal.ofReal t :=
          (ENNReal.toReal_le_toReal topL (by simp)).1
            (by simpa [ENNReal.toReal_ofReal ht.le] using upper)
        exact le_antisymm upENN lower
      rw [eval ν, eval μ]
    · have hge : 1 ≤ t := le_of_not_gt h1
      have all (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
          {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} = Set.univ := by
        ext x
        have hx : (ProbabilityTheory.cdf ρ) x ≤ t :=
          le_trans (ProbabilityTheory.cdf_le_one ρ x) hge
        simp [hx]
      rw [all ν, all μ]
      simp
end HalmosRealLaw
namespace HalmosRealLaw

def goodLevels : Set (Set.Ioo (0:ℝ) 1) :=
  {t | (3*t.1 - 1) ∉ cantorSet}
lemma measurable_goodLevels : MeasurableSet goodLevels := by
  have hc : MeasurableSet (cantorSet : Set ℝ) := isClosed_cantorSet.measurableSet
  have hm : Measurable (fun t : Set.Ioo (0:ℝ) 1 => 3*t.1 - 1) := by
    fun_prop
  exact (hm hc).compl

noncomputable def gp (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    goodLevels → ℝ := fun t => pick ν t.1
lemma gp_inj (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    Function.Injective (gp ν) := by
  intro a b h
  have h' : (a.1 : Set.Ioo (0:ℝ) 1) = b.1 := (pick_strict ν).injective h
  exact Subtype.ext h'
lemma gp_meas (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    Measurable (gp ν) := (pick_measurable ν).comp measurable_subtype_coe
lemma gp_embedding (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    MeasurableEmbedding (gp ν) := by
  letI : StandardBorelSpace (Set.Ioo (0:ℝ) 1) := measurableSet_Ioo.standardBorel
  letI : StandardBorelSpace goodLevels := measurable_goodLevels.standardBorel
  exact (gp_meas ν).measurableEmbedding (gp_inj ν)
lemma gp_range_measurable (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    MeasurableSet (Set.range (gp ν)) := by
  letI : StandardBorelSpace (Set.Ioo (0:ℝ) 1) := measurableSet_Ioo.standardBorel
  letI : StandardBorelSpace goodLevels := measurable_goodLevels.standardBorel
  simpa using (gp_embedding ν).measurableSet_image' (MeasurableSet.univ)

lemma not_countable_natBool : ¬ Countable (ℕ → Bool) := by
  intro h
  letI : Countable (ℕ → Bool) := h
  obtain ⟨f,hf⟩ := exists_surjective_nat (ℕ → Bool)
  let w : ℕ → Bool := fun n => !(f n n)
  obtain ⟨k,hk⟩ := hf w
  have he : f k k = w k := congrFun hk k
  change f k k = !(f k k) at he
  cases hval : f k k <;> simp [hval] at he

-- Each discarded complement is a large Borel reserve: although it will have
-- measure zero, it is uncountable, so it can absorb all flat intervals of a
-- cdf. This no-cardinality obstruction is often handy in the null-set repair.
lemma not_countable_compl_gp (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    ¬ Countable (↑((Set.range (gp ν))ᶜ) : Type) := by
  intro hc
  letI : Countable (↑((Set.range (gp ν))ᶜ) : Type) := hc
  -- inject the Cantor set via its affine copy of levels
  let lev : (z : cantorSet) → Set.Ioo (0:ℝ) 1 := fun z =>
    ⟨((z:ℝ)+1)/3,
      (by have hz := cantorSet_subset_unitInterval z.property
          linarith [hz.1]),
      (by have hz := cantorSet_subset_unitInterval z.property
          linarith [hz.2])⟩
  have hlev (z : cantorSet) :
      (3 * ((lev z : Set.Ioo (0:ℝ) 1) : ℝ) - 1) = (z:ℝ) := by
    dsimp [lev]; ring
  let inj : cantorSet → ↑((Set.range (gp ν))ᶜ) := fun z =>
    ⟨pick ν (lev z), by
      intro h
      rcases h with ⟨u,hu⟩
      have hp : (u.1 : Set.Ioo (0:ℝ) 1) = lev z :=
        (pick_strict ν).injective hu
      have bad : (3 * ((u.1 : Set.Ioo (0:ℝ) 1) : ℝ) - 1) ∉ cantorSet := u.property
      rw [hp, hlev] at bad
      exact bad z.property⟩
  have hi : Function.Injective inj := by
    intro a b hab
    have h' : pick ν (lev a) = pick ν (lev b) := congrArg Subtype.val hab
    have hh := (pick_strict ν).injective h'
    have hx : (a:ℝ) = (b:ℝ) := by rw [← hlev a, ← hlev b, hh]
    exact Subtype.ext hx
  haveI : Countable cantorSet := hi.countable
  haveI : Countable (ℕ → Bool) :=
    (cantorSetEquivNatToBool.symm.injective).countable
  exact not_countable_natBool (inferInstance : Countable (ℕ → Bool))

-- On the large pieces the two laws are already Borel isomorphic, with the
-- cdf as exact intertwining invariant. Only the null complements remain to
-- be patched.
noncomputable def gp_equiv
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
      [IsProbabilityMeasure μ] [NoAtoms μ] :
    (Set.range (gp ν)) ≃ᵐ (Set.range (gp μ)) := by
  letI : StandardBorelSpace (Set.Ioo (0:ℝ) 1) := measurableSet_Ioo.standardBorel
  letI : StandardBorelSpace goodLevels := measurable_goodLevels.standardBorel
  exact (gp_embedding ν).equivRange |>.symm |>.trans
    (gp_embedding μ).equivRange
end HalmosRealLaw
namespace HalmosRealLaw
noncomputable def compl_equiv
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
      [IsProbabilityMeasure μ] [NoAtoms μ] :
    (↥((Set.range (gp ν))ᶜ)) ≃ᵐ (↥((Set.range (gp μ))ᶜ)) := by
  letI : StandardBorelSpace (↥((Set.range (gp ν))ᶜ)) :=
    (gp_range_measurable ν).compl.standardBorel
  letI : StandardBorelSpace (↥((Set.range (gp μ))ᶜ)) :=
    (gp_range_measurable μ).compl.standardBorel
  exact PolishSpace.measurableEquivOfNotCountable
    (not_countable_compl_gp ν) (not_countable_compl_gp μ)

/-- The representative pieces and the null reserves give a Borel equivalence
of the two *carriers*. Proving it measure-preserving reduces just to checking
that the reserves are null. -/
noncomputable def cdfBorelEquiv
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
      [IsProbabilityMeasure μ] [NoAtoms μ] : ℝ ≃ᵐ ℝ := by
  classical
  let s : Set ℝ := Set.range (gp ν)
  let t : Set ℝ := Set.range (gp μ)
  letI : DecidablePred (fun x : ℝ => x ∈ s) := Classical.decPred _
  letI : DecidablePred (fun x : ℝ => x ∈ t) := Classical.decPred _
  exact (MeasurableEquiv.sumCompl (s := s) (gp_range_measurable ν)).symm |>.trans
    ((MeasurableEquiv.sumCongr (gp_equiv ν μ) (compl_equiv ν μ)).trans
      (MeasurableEquiv.sumCompl (s := t) (gp_range_measurable μ)))

end HalmosRealLaw

end

end
-- END INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/RealLaw.lean

-- BEGIN INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/RoundMeasure.lean
section

/-!
Very small ENNReal bookkeeping for the finite rounding step of the weak
Halmos approximation.  A word in a finite fair cube has a common weight `w`.
If the mass of one colour class is at most `L` more than that of another,
then the one-sided surplus of its *number* of words costs at most `L` after
multiplying by `w`.  Stating this without division is useful even at `w=0`.
-/
open Classical
namespace HalmosSupport

/-- Conversion of a one-sided histogram surplus into a measure bound.  The
`min` is the number of points that can be retained.  The argument is in
`ℝ≥0∞`; no cancellation by the word mass is used.  Thus it is valid for
`w=0` too.  We only need that the common word mass is finite in the branch
where distributing a subtraction through multiplication is necessary. -/
theorem nat_sub_min_cast_mul_le_of_le_add
    (a b : ℕ) (w L : ENNReal) (hw : w ≠ ⊤)
    (h : (a : ENNReal) * w ≤ L + (b : ENNReal) * w) :
    ((a - min a b : ℕ) : ENNReal) * w ≤ L := by
  classical
  by_cases hba : b ≤ a
  · have hm : min a b = b := min_eq_right hba
    rw [hm]
    rw [ENNReal.natCast_sub]
    rw [ENNReal.sub_mul (by
      intro _ _
      exact hw)]
    exact (tsub_le_iff_right).2 h
  · have hab : a ≤ b := le_of_not_ge hba
    have hm : min a b = a := min_eq_left hab
    simp [hm]

/-- A summable form of `nat_sub_min_cast_mul_le_of_le_add`.  Each colour may
come with its own error, but the word weight is the same for the whole finite
block.  Notice that the cast of the natural-valued sum is taken *before*
multiplying; this is often the form returned by a combinatorial rounding
lemma. -/
theorem sum_nat_sub_min_cast_mul_le_of_le_add
    {κ : Type*} [Fintype κ]
    (a b : κ → ℕ) (w : ENNReal) (hw : w ≠ ⊤)
    (L : κ → ENNReal)
    (h : ∀ i, (a i : ENNReal) * w ≤ L i + (b i : ENNReal) * w) :
    ((∑ i : κ, (a i - min (a i) (b i))) : ENNReal) * w
       ≤ ∑ i : κ, L i := by
  classical
  -- Cast the finite sum and distribute multiplication; the pointwise
  -- inequality above now sums directly in the ordered semiring `ℝ≥0∞`.
  -- multiplication over a finite sum is safe in `ENNReal`
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (by
    intro i hi
    simpa [ENNReal.natCast_sub] using
      (nat_sub_min_cast_mul_le_of_le_add
        (a i) (b i) w (L i) hw (h i)))

end HalmosSupport

end
-- END INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/RoundMeasure.lean

-- BEGIN INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/MarkerBad.lean
section
/-! Quantitative exceptional rows for the elementary first-marker clock.  This
file is deliberately independent of cylinders/measure; every assertion is a
cardinality bound on ordinary finite words. -/
namespace HalmosSupport
open Classical

noncomputable def markerRead {α β : Type*} [DecidableEq β]
    (σ : α ≃ α) (N : ℕ) (hN : 0 < N) (star : β)
    (u : Fin N → (α × β)) : α :=
  clockColor σ (firstMarker N hN star)
    (fun i : Fin N => N-1-i.val) u

@[simp] lemma markerRead_def {α β : Type*} [DecidableEq β]
    (σ : α ≃ α) (N : ℕ) (hN : 0 < N) (star : β)
    (u : Fin N → (α × β)) :
    markerRead σ N hN star u =
      clockColor σ (firstMarker N hN star)
        (fun i : Fin N => N-1-i.val) u := rfl

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- `badRow` is the bad edge, written before any coordinates have been put on
an integer line. The row has `N+1` sites; the old window starts at 0. -/
def markerBadRow (σ : α ≃ α) (N : ℕ) (hN : 0 < N) (star : β)
    (z : Fin (N+1) → (α × β)) : Prop :=
  let prev : Fin N → (α × β) := fun i => z ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  let pres : Fin N → (α × β) := fun i => z ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩
  markerRead σ N hN star pres ≠ σ (markerRead σ N hN star prev)

noncomputable instance markerBadRow_decidable (σ : α ≃ α) (N : ℕ) (hN : 0 < N) (star : β) :
    DecidablePred (markerBadRow σ N hN star) := Classical.decPred _

/-- A bad edge has a very short explanation. Either the lost left site is a
marker, or the common interior contains no marker. This is the pointwise
heart of the first-marker construction. -/
lemma markerBadRow_exception (σ : α ≃ α) (N : ℕ) (hN1 : 1 < N) (star : β)
    {z : Fin (N+1) → (α × β)}
    (hz : markerBadRow σ N (lt_trans (by decide : 0<1) hN1) star z) :
    (z ⟨0, Nat.succ_pos _⟩).2 = star ∨
      ∀ t : ℕ, 0 < t → (htN : t < N) →
        (z ⟨t, Nat.lt_succ_of_lt htN⟩).2 ≠ star := by
  classical
  by_cases hleft : (z ⟨0, Nat.succ_pos _⟩).2 = star
  · exact Or.inl hleft
  right
  intro t ht htN heq
  have hover : ∃ t : ℕ, ∃ ht0 : 0 < t, ∃ htN : t < N,
          (z ⟨t, Nat.lt_succ_of_lt htN⟩).2 = star :=
    ⟨t, ht, htN, heq⟩
  have hgood := clockColor_overlap_advance (α:=α) σ N hN1 star z hleft hover
  exact hz hgood

-- no repeated arithmetic side conditions in the counting lemmas
private lemma __MarkerBad_card_filter_eq_card_subtype {γ : Type*} [Fintype γ]
    (p : γ → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Fintype.card {x : γ // p x} := by
  classical
  symm
  exact Fintype.card_subtype p

/-- The elementary union bound for bad rows. This form, still in
cardinalities, is useful when the line-window is encoded in a less convenient
order. -/
lemma card_markerBad_le_exception (σ : α ≃ α) (N : ℕ) (hN1 : 1 < N)
    (star : β) :
    (Finset.univ.filter (markerBadRow σ N
        (lt_trans (by decide : 0<1) hN1) star)).card ≤
      (Finset.univ.filter (fun z : Fin (N+1) → (α × β) =>
          (z ⟨0, Nat.succ_pos _⟩).2 = star)).card +
      (Finset.univ.filter (fun z : Fin (N+1) → (α × β) =>
          ∀ t : ℕ, 0 < t → (htN : t < N) →
            (z ⟨t, Nat.lt_succ_of_lt htN⟩).2 ≠ star)).card := by
  classical
  let Bad := Finset.univ.filter (markerBadRow σ N
        (lt_trans (by decide : 0<1) hN1) star)
  let Left := Finset.univ.filter (fun z : Fin (N+1) → (α × β) =>
          (z ⟨0, Nat.succ_pos _⟩).2 = star)
  let Gap := Finset.univ.filter (fun z : Fin (N+1) → (α × β) =>
          ∀ t : ℕ, 0 < t → (htN : t < N) →
            (z ⟨t, Nat.lt_succ_of_lt htN⟩).2 ≠ star)
  change Bad.card ≤ Left.card + Gap.card
  calc
    Bad.card ≤ (Left ∪ Gap).card := Finset.card_le_card (by
      intro z hz
      have hzbad : markerBadRow σ N
          (lt_trans (by decide : 0<1) hN1) star z :=
        (Finset.mem_filter.mp hz).2
      rcases markerBadRow_exception σ N hN1 star hzbad with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    _ ≤ Left.card + Gap.card := Finset.card_union_le _ _

/-- A row whose left endpoint is fixed to be a marker has one free colour at
that endpoint and `N` entirely free following sites. -/
lemma card_markerLeft (N : ℕ) (star : β) :
   (Finset.univ.filter (fun z : Fin (N+1) → (α × β) =>
       (z ⟨0, Nat.succ_pos _⟩).2 = star)).card =
      Fintype.card α * (Fintype.card (α × β))^N := by
  classical
  let left : Type _ := {z : (Fin (N+1) → (α × β)) //
       (z ⟨0, Nat.succ_pos _⟩).2 = star}
  let dec (z : (α × (Fin N → (α × β)))) :
      Fin (N+1) → (α × β) :=
    Fin.cases (z.1, star) z.2
  let enc (z : left) : α × (Fin N → (α × β)) :=
    ⟨(z.1 ⟨0, Nat.succ_pos _⟩).1,
      (fun i => z.1 i.succ)⟩
  let e : left ≃ α × (Fin N → (α × β)) :=
    { toFun := enc
      invFun := fun z => ⟨dec z, by simp [dec]⟩
      left_inv := by
        intro z
        apply Subtype.ext
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · have hz := z.2
          apply Prod.ext
          · rfl
          · simpa [dec, enc] using hz.symm
        · simp [dec, enc]
      right_inv := by
        intro z
        rcases z with ⟨x,y⟩
        apply Prod.ext
        · simp [enc, dec]
        · funext i; simp [enc, dec] }
  have hcard := Fintype.card_congr e
  have hf : (Finset.univ.filter (fun z : Fin (N+1) → (α × β) =>
       (z ⟨0, Nat.succ_pos _⟩).2 = star)).card = Fintype.card left :=
       __MarkerBad_card_filter_eq_card_subtype _
  rw [hf, hcard]
  simp [Fintype.card_fun]

/-- Exact count for a run of `m` forbidden markers. There is an unrestricted
site at either end.  Expressing `N-1` as `m` makes the reindexing transparent:
the middle sites are exactly `i+1`, `i : Fin m`. -/
lemma card_markerGap_mid (m : ℕ) (star : β) :
   (Finset.univ.filter (fun z : Fin (m+2) → (α × β) =>
       ∀ i : Fin m,
         (z ⟨i.val+1, by omega⟩).2 ≠ star)).card =
    Fintype.card (α × β) *
      (Fintype.card α * (Fintype.card β - 1))^m *
        Fintype.card (α × β) := by
  classical
  let neβ : Type _ := {b : β // b ≠ star}
  have hne : Fintype.card neβ = Fintype.card β - 1 := by
    change Fintype.card {b : β // ¬ b = star} = _
    rw [Fintype.card_subtype_compl (fun b : β => b = star)]
    have h : Fintype.card {b : β // b = star} = 1 := by
      classical
      let ee : {b : β // b = star} ≃ PUnit.{0} :=
        { toFun := fun _ => PUnit.unit
          invFun := fun _ => ⟨star, rfl⟩
          left_inv := by intro b; apply Subtype.ext; simpa using b.2.symm
          right_inv := by intro b; cases b; rfl }
      simpa using Fintype.card_congr ee
    rw [h]
  let midty : Type _ := Fin m → (α × neβ)
  let full : Type _ := {z : Fin (m+2) → (α × β) //
       ∀ i : Fin m, (z ⟨i.val+1, by omega⟩).2 ≠ star}
  let src : Type _ := (α × β) × midty × (α × β)
  let dec (v : src) : Fin (m+2) → (α × β) :=
    Fin.cases v.1
      (fun j : Fin (m+1) =>
         Fin.lastCases v.2.2
            (fun i : Fin m => ((v.2.1 i).1, (v.2.1 i).2.1)) j)
  have dec_mid (v : src) (i : Fin m) :
      dec v ⟨i.val+1, by omega⟩ =
        ((v.2.1 i).1, (v.2.1 i).2.1) := by
    have hi : (⟨i.val+1, by omega⟩ : Fin (m+2)) = i.castSucc.succ := by
      apply Fin.ext; rfl
    rw [hi]
    change (@Fin.cases (m+1) (fun _ => α × β) v.1 (fun j : Fin (m+1) =>
      Fin.lastCases v.2.2
       (fun i : Fin m => ((v.2.1 i).1, (v.2.1 i).2.1)) j)
         i.castSucc.succ) = _
    rw [Fin.cases_succ, Fin.lastCases_castSucc]
  have dec_last (v : src) : dec v (Fin.last (m+1)) = v.2.2 := by
    have hi : Fin.last (m+1) = (Fin.last m).succ := by
      apply Fin.ext; rfl
    rw [hi]
    change (@Fin.cases (m+1) (fun _ => α × β) v.1 (fun j : Fin (m+1) =>
      Fin.lastCases v.2.2
       (fun i : Fin m => ((v.2.1 i).1, (v.2.1 i).2.1)) j)
        (Fin.last m).succ) = _
    rw [Fin.cases_succ, Fin.lastCases_last]
  let enc (z : full) : src :=
    (z.1 ⟨0, by omega⟩,
      (fun i : Fin m =>
        ((z.1 ⟨i.val+1, by omega⟩).1,
          ⟨(z.1 ⟨i.val+1, by omega⟩).2, z.2 i⟩)),
      z.1 (Fin.last (m+1)))
  let ee : full ≃ src :=
    { toFun := enc
      invFun := fun v => ⟨dec v, fun i => by
        rw [dec_mid]
        exact (v.2.1 i).2.2⟩
      left_inv := by
        intro z
        apply Subtype.ext
        funext j
        refine Fin.cases ?_ (fun q : Fin (m+1) => ?_) j
        · simp [enc, dec]
        · refine Fin.lastCases ?_ (fun i : Fin m => ?_) q
          · -- last
            simpa [enc] using (dec_last (enc z))
          · have hidx : (i.castSucc.succ : Fin (m+2)) =
                 ⟨i.val+1, by omega⟩ := by apply Fin.ext; rfl
            rw [hidx]
            have hh := dec_mid (enc z) i
            simpa [enc] using hh
      right_inv := by
        intro v
        rcases v with ⟨x,y,z⟩
        dsimp [enc]
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · funext i
            -- expose the middle projection of the rebuilt tuple
            change ((dec (x,y,z) ⟨i.val+1, by omega⟩).1,
                ⟨(dec (x,y,z) ⟨i.val+1, by omega⟩).2, _⟩) = y i
            have hh := dec_mid (x,y,z) i
            apply Prod.ext
            · change (dec (x,y,z) ⟨i.val+1, by omega⟩).1 = (y i).1
              exact congrArg Prod.fst hh
            · apply Subtype.ext
              change (dec (x,y,z) ⟨i.val+1, by omega⟩).2 = (y i).2.1
              exact congrArg Prod.snd hh
          · exact dec_last (x,y,z) }
  have hf :
      (Finset.univ.filter (fun z : Fin (m+2) → (α × β) =>
         ∀ i : Fin m, (z ⟨i.val+1, by omega⟩).2 ≠ star)).card =
         Fintype.card full := __MarkerBad_card_filter_eq_card_subtype _
  rw [hf, Fintype.card_congr ee]
  change Fintype.card ((α × β) × midty × (α × β)) = _
  simp [midty, hne, mul_assoc]

lemma card_markerBad_le_formula (σ : α ≃ α) (m : ℕ) (hm : 0 < m)
    (star : β) :
    (Finset.univ.filter (markerBadRow σ (m+1) (by omega) star)).card ≤
      Fintype.card α * Fintype.card (α × β) ^ (m+1) +
       Fintype.card (α × β) *
        (Fintype.card α * (Fintype.card β - 1))^m *
          Fintype.card (α × β) := by
  classical
  have hN1 : 1 < m+1 := by omega
  have h := card_markerBad_le_exception (α:=α) (β:=β) σ (m+1) hN1 star
  have hleft := card_markerLeft (α:=α) (β:=β) (m+1) star
  have hgap := card_markerGap_mid (α:=α) (β:=β) m star
  -- the gap in `h` is the middle predicate of `hgap`
  have heq : (Finset.univ.filter (fun z : Fin ((m+1)+1) → (α × β) =>
          ∀ t : ℕ, 0 < t → (htN : t < m+1) →
            (z ⟨t, Nat.lt_succ_of_lt htN⟩).2 ≠ star)) =
       (Finset.univ.filter (fun z : Fin (m+2) → (α × β) =>
          ∀ i : Fin m, (z ⟨i.val+1, by omega⟩).2 ≠ star)) := by
    apply Finset.ext
    intro z
    -- definitional `m+1+1 = m+2`
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz i
      exact hz (i.val+1) (by omega) (by omega)
    · intro hz t ht htN
      have ht' : t-1 < m := by omega
      have h0 := hz (⟨t-1, ht'⟩ : Fin m)
      have he : (⟨(⟨t-1, ht'⟩ : Fin m).val + 1, by omega⟩ : Fin (m+2)) =
          ⟨t, Nat.lt_succ_of_lt htN⟩ := by
        apply Fin.ext
        simp
        omega
      simpa [he] using h0
  rw [hleft, heq, hgap] at h
  exact h

end HalmosSupport

end
-- END INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/MarkerBad.lean

-- BEGIN INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/RealLawPreserve.lean
section
open MeasureTheory Filter Topology Set ProbabilityTheory
noncomputable section
namespace HalmosRealLaw
lemma cdfBorelEquiv_on_gp
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
      [IsProbabilityMeasure μ] [NoAtoms μ]
    (u : goodLevels) :
    cdfBorelEquiv ν μ (gp ν u) = gp μ u := by
  classical
  letI : StandardBorelSpace (Set.Ioo (0:ℝ) 1) := measurableSet_Ioo.standardBorel
  letI : StandardBorelSpace goodLevels := measurable_goodLevels.standardBorel
  have hx : gp ν u ∈ Set.range (gp ν) := ⟨u,rfl⟩
  change
    (MeasurableEquiv.sumCompl (gp_range_measurable μ))
      ((MeasurableEquiv.sumCongr (gp_equiv ν μ) (compl_equiv ν μ))
        ((MeasurableEquiv.sumCompl (gp_range_measurable ν)).symm (gp ν u))) = _
  have hfirst :
      (MeasurableEquiv.sumCompl (gp_range_measurable ν)).symm (gp ν u)
        = Sum.inl (⟨gp ν u, hx⟩ : Set.range (gp ν)) := by
    change (if h : gp ν u ∈ Set.range (gp ν) then _ else _) = _
    simp [hx]
    -- the proof of membership is immaterial
    congr
  rw [hfirst]
  -- sum congr acts trivially on this inl
  change
    (MeasurableEquiv.sumCompl (gp_range_measurable μ))
      (Sum.inl ((gp_equiv ν μ) (⟨gp ν u, hx⟩))) = _
  change (((gp_equiv ν μ) (⟨gp ν u, hx⟩ : Set.range (gp ν))) : ℝ) = _
  -- compute the range chart
  change (((MeasurableEmbedding.equivRange (gp_embedding ν)).symm |>.trans
        (MeasurableEmbedding.equivRange (gp_embedding μ)))
        ⟨gp ν u, hx⟩ : Set.range (gp μ)).1 = _
  rw [MeasurableEquiv.trans_apply]
  rw [MeasurableEmbedding.equivRange_symm_apply_mk]
  exact congrArg Subtype.val (MeasurableEmbedding.equivRange_apply (gp_embedding μ) u)
end HalmosRealLaw
namespace HalmosRealLaw
-- elementary evaluation of the distribution of a continuous atomless cdf
lemma map_cdf_Iic_value (ρ : Measure ℝ) [IsProbabilityMeasure ρ] [NoAtoms ρ]
    (t : ℝ) :
    ρ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} =
      if t ≤ 0 then 0 else if t < 1 then ENNReal.ofReal t else 1 := by
  -- the proof is the quantile squeeze; it does not require strictness of the cdf
  have evalUpper (u : ℝ) (htu : t < u) (hu0 : 0 < u) (hu1 : u < 1) :
      ρ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} ≤ ENNReal.ofReal u := by
    let v : Set.Ioo (0:ℝ) 1 := ⟨u, hu0, hu1⟩
    have sub : {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} ⊆ Set.Iic (pick ρ v) := by
      intro x hx
      by_contra hb
      have hbad : pick ρ v < x := lt_of_not_ge hb
      have hm := ProbabilityTheory.monotone_cdf ρ (le_of_lt hbad)
      have hp : (ProbabilityTheory.cdf ρ) (pick ρ v) = u := pick_spec ρ v
      have hlt : t < (ProbabilityTheory.cdf ρ) (pick ρ v) := by rw [hp]; exact htu
      have hxx : (ProbabilityTheory.cdf ρ) x ≤ t := hx
      exact (not_lt_of_ge (hm.trans hxx)) hlt
    refine le_trans (measure_mono sub) ?_
    rw [← ProbabilityTheory.ofReal_cdf ρ, pick_spec]
  have upper0 (ht : t ≤ 0) :
      ρ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} = 0 := by
    let L : ENNReal := ρ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t}
    have topL : L ≠ ⊤ := measure_ne_top _ _
    have nonneg : 0 ≤ L.toReal := ENNReal.toReal_nonneg
    have upper : L.toReal ≤ (0:ℝ) := by
      apply le_of_forall_gt_imp_ge_of_dense
      intro a ha
      by_cases ha1 : a < 1
      · have H : L ≤ ENNReal.ofReal a := evalUpper a (lt_of_le_of_lt ht ha) ha ha1
        have HH := (ENNReal.toReal_le_toReal topL (by simp)).2 H
        simpa [ENNReal.toReal_ofReal (le_of_lt ha)] using HH
      · have hprob : L ≤ 1 := by
          dsimp [L]; exact prob_le_one
        have hh := (ENNReal.toReal_le_toReal topL (by simp : (1:ENNReal) ≠ ⊤)).2 hprob
        simpa using hh.trans (le_of_not_gt ha1)
    have z : L.toReal = 0 := le_antisymm upper nonneg
    exact (ENNReal.toReal_eq_zero_iff L).1 z |>.resolve_right topL
  by_cases h0 : t ≤ 0
  · rw [if_pos h0]
    exact upper0 h0
  · rw [if_neg h0]
    have ht : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · rw [if_pos h1]
      let L : ENNReal := ρ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t}
      have topL : L ≠ ⊤ := measure_ne_top _ _
      let v : Set.Ioo (0:ℝ) 1 := ⟨t, ht, h1⟩
      have lower : ENNReal.ofReal t ≤ L := by
        have sub : Set.Iic (pick ρ v) ⊆ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} := by
          intro x hx
          have hm := ProbabilityTheory.monotone_cdf ρ hx
          have hp : (ProbabilityTheory.cdf ρ) (pick ρ v) = t := pick_spec ρ v
          exact hm.trans (le_of_eq hp)
        have H := measure_mono sub (μ:=ρ)
        rw [← ProbabilityTheory.ofReal_cdf ρ, pick_spec] at H
        exact H
      have upper : L.toReal ≤ t := by
        apply le_of_forall_gt_imp_ge_of_dense
        intro a ha
        by_cases ha1 : a < 1
        · have H : L ≤ ENNReal.ofReal a := evalUpper a ha (lt_trans ht ha) ha1
          have HH := (ENNReal.toReal_le_toReal topL (by simp)).2 H
          simpa [ENNReal.toReal_ofReal (le_of_lt (lt_trans ht ha))] using HH
        · have hprob : L ≤ 1 := by dsimp [L]; exact prob_le_one
          have hh := (ENNReal.toReal_le_toReal topL (by simp : (1:ENNReal)≠⊤)).2 hprob
          exact (by simpa using hh.trans (le_of_not_gt ha1))
      have upENN : L ≤ ENNReal.ofReal t :=
        (ENNReal.toReal_le_toReal topL (by simp)).1
          (by simpa [ENNReal.toReal_ofReal ht.le] using upper)
      -- re-expose the abbreviation
      exact le_antisymm upENN lower
    · rw [if_neg h1]
      have hge : 1 ≤ t := le_of_not_gt h1
      have all : {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} = Set.univ := by
        ext x
        have hx : (ProbabilityTheory.cdf ρ) x ≤ t :=
          le_trans (ProbabilityTheory.cdf_le_one ρ x) hge
        simp [hx]
      rw [all]
      simp
end HalmosRealLaw
namespace HalmosRealLaw
lemma map_cdf_uniform01 (ρ : Measure ℝ) [IsProbabilityMeasure ρ] [NoAtoms ρ] :
    Measure.map (fun x : ℝ => (ProbabilityTheory.cdf ρ) x) ρ =
      (volume : Measure ℝ).restrict (Set.Icc 0 1) := by
  let F := fun x : ℝ => (ProbabilityTheory.cdf ρ) x
  have hF : Measurable F := (continuous_cdf ρ).measurable
  letI : IsFiniteMeasure (Measure.map F ρ) := Measure.isFiniteMeasure_map ρ F
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hF measurableSet_Iic]
  rw [Measure.restrict_apply measurableSet_Iic]
  change ρ {x : ℝ | (ProbabilityTheory.cdf ρ) x ≤ t} = _
  rw [map_cdf_Iic_value ρ t]
  by_cases h0 : t ≤ 0
  · rw [if_pos h0]
    by_cases he : t < 0
    · have hs : Set.Iic t ∩ Set.Icc (0:ℝ) 1 = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false]
        constructor
        · intro h
          linarith [h.1, h.2.1]
        · tauto
      simp [hs]
    · have hz : t = 0 := le_antisymm h0 (le_of_not_gt he)
      subst t
      have hs : Set.Iic (0:ℝ) ∩ Set.Icc (0:ℝ) 1 = ({0} : Set ℝ) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc,
           Set.mem_singleton_iff]
        constructor
        · intro h
          exact le_antisymm h.1 h.2.1
        · intro h; subst x
          norm_num
      simp [hs]
  · rw [if_neg h0]
    have ht : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · rw [if_pos h1]
      have hs : Set.Iic t ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 t := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · intro h; exact ⟨h.2.1, h.1⟩
        · intro h; exact ⟨h.2, h.1, le_trans h.2 (le_of_lt h1)⟩
      rw [hs, Real.volume_Icc]
      simp
    · rw [if_neg h1]
      have hge : 1 ≤ t := le_of_not_gt h1
      have hs : Set.Iic t ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 1 := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · intro h; exact h.2
        · intro h; exact ⟨le_trans h.2 hge, h⟩
      rw [hs, Real.volume_Icc]
      norm_num
end HalmosRealLaw
namespace HalmosRealLaw
/-- The little set of levels discarded in `goodLevels`, regarded in the real line. -/
def badValues : Set ℝ := {r : ℝ | 3*r - 1 ∈ cantorSet}
lemma measurable_badValues : MeasurableSet badValues := by
  have hm : Measurable (fun r : ℝ => 3*r - 1) := by fun_prop
  exact hm isClosed_cantorSet.measurableSet

lemma volume_badValues_zero : (volume : Measure ℝ) badValues = 0 := by
  have hs : badValues = (fun z : ℝ => (z+1)/3) '' cantorSet := by
    ext y
    constructor
    · intro hy
      have hz : 3*y - 1 ∈ cantorSet := hy
      refine ⟨3*y-1, hz, ?_⟩
      ring
    · rintro ⟨z,hz,rfl⟩
      change 3 * ((z+1)/3) - 1 ∈ cantorSet
      convert hz using 1 <;> ring
  rw [hs]
  have him : (fun z : ℝ => (z+1)/3) '' cantorSet =
       (fun q : ℝ => (1/3:ℝ) * q) '' ((fun z : ℝ => 1 + z) '' cantorSet) := by
    rw [← Set.image_comp]
    congr 1
    funext z
    change (z+1)/3 = (1/3:ℝ) * (1+z)
    ring
  rw [him]
  rw [volume_image_scale (1/3:ℝ) (by norm_num)]
  rw [volume_image_translate]
  rw [volume_cantorSet_zero]
  simp

lemma cdf_preimage_singleton_zero (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] [NoAtoms ρ] (a : ℝ) :
    ρ {x : ℝ | (ProbabilityTheory.cdf ρ) x = a} = 0 := by
  have hF : Measurable (fun x : ℝ => (ProbabilityTheory.cdf ρ) x) :=
    (continuous_cdf ρ).measurable
  have heq := map_cdf_uniform01 ρ
  have hzero : ((volume : Measure ℝ).restrict (Set.Icc 0 1)) ({a} : Set ℝ) = 0 :=
    measure_singleton a
  have hmap : (Measure.map (fun x : ℝ => (ProbabilityTheory.cdf ρ) x) ρ)
      ({a} : Set ℝ) = 0 := by rw [heq]; exact hzero
  rw [Measure.map_apply hF (MeasurableSet.singleton a)] at hmap
  have hs : (fun x : ℝ => (ProbabilityTheory.cdf ρ) x) ⁻¹' ({a} : Set ℝ) =
      {x : ℝ | (ProbabilityTheory.cdf ρ) x = a} := by
    ext x
    simp
  rwa [hs] at hmap

lemma cdf_preimage_badValues_zero (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] [NoAtoms ρ] :
    ρ ((fun x : ℝ => (ProbabilityTheory.cdf ρ) x) ⁻¹' badValues) = 0 := by
  let F := fun x : ℝ => (ProbabilityTheory.cdf ρ) x
  have hF : Measurable F := (continuous_cdf ρ).measurable
  have heq := map_cdf_uniform01 ρ
  have hzero : ((volume : Measure ℝ).restrict (Set.Icc 0 1)) badValues = 0 := by
    rw [Measure.restrict_apply measurable_badValues]
    exact measure_mono_null (Set.inter_subset_left) volume_badValues_zero
  have hmap : (Measure.map F ρ) badValues = 0 := by rw [heq]; exact hzero
  rwa [Measure.map_apply hF measurable_badValues] at hmap
end HalmosRealLaw
namespace HalmosRealLaw
lemma compl_range_gp_null (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] [NoAtoms ρ] :
    ρ ((Set.range (gp ρ))ᶜ) = 0 := by
  classical
  let F : ℝ → ℝ := fun x => (ProbabilityTheory.cdf ρ) x
  let Bad : Set ℝ := F ⁻¹' badValues
  let Z0 : Set ℝ := {x : ℝ | F x = 0}
  let Z1 : Set ℝ := {x : ℝ | F x = 1}
  let RatFib : Set ℝ := ⋃ q : ℚ, {x : ℝ | F x = F (q:ℝ)}
  have hBad : ρ Bad = 0 := by
    exact cdf_preimage_badValues_zero ρ
  have hZ0 : ρ Z0 = 0 := by
    exact cdf_preimage_singleton_zero ρ 0
  have hZ1 : ρ Z1 = 0 := by
    exact cdf_preimage_singleton_zero ρ 1
  have hRat : ρ RatFib = 0 := by
    dsimp [RatFib]
    apply measure_iUnion_null
    intro q
    exact cdf_preimage_singleton_zero ρ (F (q:ℝ))
  have hsub : (Set.range (gp ρ))ᶜ ⊆ ((Bad ∪ Z0) ∪ Z1) ∪ RatFib := by
    intro x hx
    have hnot : x ∉ Set.range (gp ρ) := hx
    have hnon : 0 ≤ F x := ProbabilityTheory.cdf_nonneg _ _
    have hle : F x ≤ 1 := ProbabilityTheory.cdf_le_one _ _
    by_cases hz : F x = 0
    · exact Or.inl (Or.inl (Or.inr hz))
    by_cases ho : F x = 1
    · exact Or.inl (Or.inr ho)
    have hp0 : 0 < F x := lt_of_le_of_ne hnon (Ne.symm hz)
    have hp1 : F x < 1 := lt_of_le_of_ne hle ho
    let t : Set.Ioo (0:ℝ) 1 := ⟨F x, hp0, hp1⟩
    by_cases ht : t ∈ goodLevels
    · let u : goodLevels := ⟨t, ht⟩
      have hpv : F (pick ρ t) = F x := by
        have hp := pick_spec ρ t
        exact hp
      have hneq : pick ρ t ≠ x := by
        intro h
        apply hnot
        refine ⟨u, ?_⟩
        change pick ρ t = x
        exact h
      rcases lt_or_gt_of_ne hneq with hleft | hright
      · -- the representative is to the left of `x`
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hleft
        have hlow := ProbabilityTheory.monotone_cdf ρ (le_of_lt hq1)
        have hupp := ProbabilityTheory.monotone_cdf ρ (le_of_lt hq2)
        have heq : F x = F (q:ℝ) := by
          change (ProbabilityTheory.cdf ρ) x = (ProbabilityTheory.cdf ρ) (q:ℝ)
          apply le_antisymm
          · have : (ProbabilityTheory.cdf ρ) (pick ρ t) =
                  (ProbabilityTheory.cdf ρ) x := hpv
            rw [← this]
            exact hlow
          · exact hupp
        apply Or.inr
        change x ∈ ⋃ q : ℚ, {y : ℝ | F y = F (q:ℝ)}
        exact Set.mem_iUnion.2 ⟨q, heq⟩
      · -- `x` is to the left
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hright
        have hlow := ProbabilityTheory.monotone_cdf ρ (le_of_lt hq1)
        have hupp := ProbabilityTheory.monotone_cdf ρ (le_of_lt hq2)
        have heq : F x = F (q:ℝ) := by
          change (ProbabilityTheory.cdf ρ) x = (ProbabilityTheory.cdf ρ) (q:ℝ)
          apply le_antisymm
          · exact hlow
          · have : (ProbabilityTheory.cdf ρ) (pick ρ t) =
                  (ProbabilityTheory.cdf ρ) x := hpv
            -- the right end is the representative
            -- `hupp : F q ≤ F (pick ...)`
            simpa [this] using hupp
        apply Or.inr
        change x ∈ ⋃ q : ℚ, {y : ℝ | F y = F (q:ℝ)}
        exact Set.mem_iUnion.2 ⟨q, heq⟩
    · apply Or.inl
      apply Or.inl
      apply Or.inl
      change 3 * F x - 1 ∈ cantorSet
      -- this is exactly failure of membership in `goodLevels`
      change ¬ (3 * F x - 1 ∉ cantorSet) at ht
      exact Classical.byContradiction (fun h => ht h)
  refine measure_mono_null hsub ?_
  exact measure_union_null
    (measure_union_null (measure_union_null hBad hZ0) hZ1) hRat
end HalmosRealLaw
namespace HalmosRealLaw
lemma cdfBorelEquiv_preimage_Iic
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
      [IsProbabilityMeasure μ] [NoAtoms μ]
    (a : ℝ) :
    ν ((cdfBorelEquiv ν μ : ℝ → ℝ) ⁻¹' Set.Iic a) = μ (Set.Iic a) := by
  classical
  let F : ℝ → ℝ := fun x => (ProbabilityTheory.cdf ν) x
  let G : ℝ → ℝ := fun x => (ProbabilityTheory.cdf μ) x
  let t : ℝ := G a
  let S : Set ℝ := Set.range (gp ν)
  let P : Set ℝ := (cdfBorelEquiv ν μ : ℝ → ℝ) ⁻¹' Set.Iic a
  let Q : Set ℝ := {x : ℝ | F x ≤ t}
  have hcomp : ν (Sᶜ) = 0 := compl_range_gp_null ν
  have hlev : ν {x : ℝ | F x = t} = 0 := by
    exact cdf_preimage_singleton_zero ν t
  have forw {x : ℝ} (hx : x ∈ S) (hp : x ∈ P) : x ∈ Q := by
    rcases hx with ⟨u, rfl⟩
    change cdfBorelEquiv ν μ (gp ν u) ≤ a at hp
    have hm : (ProbabilityTheory.cdf μ)
          (cdfBorelEquiv ν μ (gp ν u)) ≤ (ProbabilityTheory.cdf μ) a :=
      ProbabilityTheory.monotone_cdf μ hp
    have hvν : F (gp ν u) = (u.1 : ℝ) := pick_spec ν u.1
    have hvμ : G (gp μ u) = (u.1 : ℝ) := pick_spec μ u.1
    change F (gp ν u) ≤ t
    dsimp [t]
    rw [hvν]
    change (u.1 : ℝ) ≤ G a
    rw [← hvμ]
    -- rewrite the equivalence on its good part
    simpa [G, cdfBorelEquiv_on_gp ν μ u] using hm
  have back {x : ℝ} (hx : x ∈ S) (hlt : F x < t) : x ∈ P := by
    rcases hx with ⟨u, rfl⟩
    have hvν : F (gp ν u) = (u.1 : ℝ) := pick_spec ν u.1
    have hvμ : G (gp μ u) = (u.1 : ℝ) := pick_spec μ u.1
    have hs : (u.1 : ℝ) < G a := by
      simpa [hvν, t] using hlt
    change cdfBorelEquiv ν μ (gp ν u) ∈ Set.Iic a
    change cdfBorelEquiv ν μ (gp ν u) ≤ a
    rw [cdfBorelEquiv_on_gp ν μ u]
    -- strict cdf inequality forces strict ordering of representatives against `a`
    by_contra hn
    have ha' : a < gp μ u := lt_of_not_ge hn
    have hm := ProbabilityTheory.monotone_cdf μ (le_of_lt ha')
    have hh : G a ≤ G (gp μ u) := hm
    rw [hvμ] at hh
    exact (not_lt_of_ge hh) hs
  have hPQ : ν (P \ Q) = 0 := by
    refine measure_mono_null (t := Sᶜ) ?_ hcomp
    intro x hx
    rcases hx with ⟨hp,hq⟩
    change x ∉ S
    intro hs
    exact hq (forw hs hp)
  have hQP : ν (Q \ P) = 0 := by
    have hsub : Q \ P ⊆ (Sᶜ ∪ {x : ℝ | F x = t}) := by
      intro x hx
      rcases hx with ⟨hq,hp⟩
      by_cases hs : x ∈ S
      · right
        change F x = t
        have hle : F x ≤ t := hq
        rcases lt_or_eq_of_le hle with hl | he
        · exact False.elim (hp (back hs hl))
        · exact he
      · exact Or.inl hs
    exact measure_mono_null hsub (measure_union_null hcomp hlev)
  have heq : ν P = ν Q := measure_congr (ae_eq_set.2 ⟨hPQ,hQP⟩)
  change ν P = μ (Set.Iic a)
  rw [heq]
  change ν {x : ℝ | F x ≤ t} = μ (Set.Iic a)
  rw [map_cdf_Iic_value ν t]
  rw [← ProbabilityTheory.ofReal_cdf μ a]
  change (if t ≤ 0 then 0 else if t < 1 then ENNReal.ofReal t else 1) =
      ENNReal.ofReal t
  have hn : 0 ≤ t := ProbabilityTheory.cdf_nonneg _ _
  have hu : t ≤ 1 := ProbabilityTheory.cdf_le_one _ _
  by_cases hz : t = 0
  · simp [hz]
  · have ht0 : ¬ t ≤ 0 := not_le_of_gt (lt_of_le_of_ne hn (Ne.symm hz))
    rw [if_neg ht0]
    by_cases h1 : t = 1
    · simp [h1]
    · have hh : t < 1 := lt_of_le_of_ne hu h1
      simp [hh]
end HalmosRealLaw

end

end
-- END INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/RealLawPreserve.lean

-- BEGIN INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/RoundBound.lean
section

/-!
Some finite bookkeeping that complements `ColorRound`.  If the colours of
points in a finite set are read two different ways, the one-sided histogram
deficit is no bigger than the number of points on which the two readings
disagree.  This is useful when colours are Boolean cells of two partitions of
a finite block.
-/
open Classical
namespace HalmosSupport
variable {α κ : Type*} [Fintype α] [Fintype κ]
variable [DecidableEq α] [DecidableEq κ]

/-- The total one-sided difference of two finite histograms is bounded by the
number of points whose colours differ.  This is deliberately about finite
sets (not probabilities); the latter are obtained by multiplying by a common
atom mass. -/
theorem sum_card_sub_min_colorFiber_le_disagree
    (c d : α → κ) :
    (∑ i : κ, ((colorFiber c i).card -
        min (colorFiber c i).card (colorFiber d i).card)) ≤
      (Finset.univ.filter (fun x : α => c x ≠ d x)).card := by
  classical
  -- For a fixed colour the retained common points form the literal
  -- intersection of the two fibres.  It embeds into the second fibre, hence
  -- removing it from the first costs at least the histogram deficit.
  let miss : κ → Finset α := fun i =>
    (colorFiber c i) \ (colorFiber d i)
  have hi (i : κ) :
      (colorFiber c i).card - min (colorFiber c i).card (colorFiber d i).card
        ≤ (miss i).card := by
    have hle : ((colorFiber c i) ∩ (colorFiber d i)).card ≤
        (colorFiber d i).card :=
      Finset.card_le_card (Finset.inter_subset_right)
    have hrewrite : (miss i).card =
        (colorFiber c i).card - ((colorFiber c i) ∩ (colorFiber d i)).card := by
      simpa [miss, Finset.inter_comm] using
        (Finset.card_sdiff (s := colorFiber d i) (t := colorFiber c i))
    rw [hrewrite]
    -- `a - min a b` is at most `a - t` for every `t ≤ b` (and `t ≤ a`).
    have hmin : ((colorFiber c i) ∩ (colorFiber d i)).card ≤
        min (colorFiber c i).card (colorFiber d i).card := by
      exact le_min (Finset.card_le_card Finset.inter_subset_left) hle
    exact Nat.sub_le_sub_left hmin _
  have hsum :
      (∑ i : κ, ((colorFiber c i).card -
        min (colorFiber c i).card (colorFiber d i).card)) ≤
        ∑ i : κ, (miss i).card :=
    Finset.sum_le_sum (by
      intro i hi'
      exact hi i)
  refine hsum.trans ?_
  -- The missing pieces are disjoint, since their first colour is different.
  have hpw : (↑(Finset.univ : Finset κ) : Set κ).PairwiseDisjoint miss := by
    intro i hii j hjj hne
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hci : c x = i := (mem_colorFiber c i x).1
      ((Finset.mem_sdiff.mp hxi).1)
    have hcj : c x = j := (mem_colorFiber c j x).1
      ((Finset.mem_sdiff.mp hxj).1)
    exact hne (hci.symm.trans hcj)
  rw [← Finset.card_biUnion hpw]
  apply Finset.card_le_card
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨i, hiu, hxi⟩
  have hc : c x = i :=
    (mem_colorFiber c i x).1 ((Finset.mem_sdiff.mp hxi).1)
  have hn : x ∉ colorFiber d i := (Finset.mem_sdiff.mp hxi).2
  have hne : c x ≠ d x := by
    intro heq
    apply hn
    exact (mem_colorFiber d i x).2 (by simpa [hc] using heq.symm)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩

/-- In particular the colouring produced by `exists_colorRound` may be chosen
so that it changes no more points than the old two readings disagreed on.
The sharper histogram bound from `exists_colorRound` is often convenient too,
so we keep both estimates. -/
theorem exists_colorRound_le_disagree (c d : α → κ) :
    ∃ d' : α → κ,
      (∀ i : κ, (colorFiber d' i).card = (colorFiber c i).card) ∧
      ((Finset.univ.filter (fun x : α => d' x ≠ d x)).card
         ≤ (Finset.univ.filter (fun x : α => c x ≠ d x)).card) := by
  classical
  obtain ⟨d', hd', hbad⟩ := exists_colorRound c d
  exact ⟨d', hd', le_trans hbad (sum_card_sub_min_colorFiber_le_disagree c d)⟩

end HalmosSupport

end
-- END INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/RoundBound.lean

-- BEGIN INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/MarkerLine.lean
section
namespace HalmosSupport
open Classical
/-- coordinates `0,...,n-1`, embedded in the integer line. -/
def natWindow (n : ℕ) : Finset ℤ := (Finset.range n).map ⟨Int.ofNat, fun _ _ h => Int.ofNat_inj.mp h⟩
@[simp] lemma mem_natWindow {j : ℤ} {n : ℕ} : j ∈ natWindow n ↔ 0 ≤ j ∧ j.toNat < n := by
  classical
  simp [natWindow]
  constructor
  · rintro ⟨i,hi,rfl⟩
    simp_all
  · rintro ⟨hj,hl⟩
    refine ⟨j.toNat, hl, ?_⟩
    simp [hj]

def twoNatWindow (t N : ℕ) : Finset ℤ :=
   (natWindow (N*t)).image (fun j : ℤ => j - (t:ℤ)) ∪ natWindow (N*t)

@[simp] lemma mem_twoNatWindow {j : ℤ} {t N : ℕ} (ht : 0 < t) (hN : 0 < N) :
  j ∈ twoNatWindow t N ↔ -(t:ℤ) ≤ j ∧ j < (N*t:ℕ) := by
  classical
  simp only [twoNatWindow, Finset.mem_union, Finset.mem_image]
  constructor
  · intro hj
    rcases hj with ⟨i, hi, heq⟩ | hi
    · have hi' : 0 ≤ i ∧ i.toNat < N*t := (mem_natWindow).1 hi
      subst j
      constructor
      · linarith
      · have hicast : i < ((N*t:ℕ):ℤ) := (Int.toNat_lt hi'.1).mp hi'.2
        have : (0:ℤ) < t := by exact_mod_cast ht
        linarith
    · have hi' : 0 ≤ j ∧ j.toNat < N*t := (mem_natWindow).1 hi
      constructor
      · have : (0:ℤ) ≤ t := by exact_mod_cast (Nat.zero_le t)
        linarith
      · exact (Int.toNat_lt hi'.1).mp hi'.2
  · rintro ⟨hl,hr⟩
    by_cases hj : 0 ≤ j
    · right
      exact mem_natWindow.mpr ⟨hj, (Int.toNat_lt hj).mpr hr⟩
    · left
      let i : ℤ := j + (t:ℤ)
      have hi0 : 0 ≤ i := by dsimp [i]; linarith
      have hitop : i < (N*t:ℕ) := by
        dsimp [i]
        have ht' : (0:ℤ) < t := by exact_mod_cast ht
        -- since j negative, i < t ≤ N*t
        have htle : (t:ℤ) ≤ (N*t:ℕ) := by
          exact_mod_cast (show t ≤ N*t by
            calc t = 1*t := by simp
                 _ ≤ N*t := Nat.mul_le_mul_right t hN)
        push_cast
        push_cast at htle
        omega
      refine ⟨i, mem_natWindow.mpr ⟨hi0, (Int.toNat_lt hi0).mpr hitop⟩, ?_⟩
      dsimp [i]
      omega

/-- enumeration of a `natWindow`. -/
def enumWindow (n : ℕ) : (↥(natWindow n)) ≃ Fin n :=
 { toFun := fun j => ⟨j.val.toNat, (mem_natWindow.mp j.property).2⟩
   invFun := fun i => ⟨(i.val : ℤ), mem_natWindow.mpr ⟨by omega, by simpa⟩⟩
   left_inv := by intro j; apply Subtype.ext; dsimp; exact (Int.toNat_of_nonneg (mem_natWindow.mp j.property).1)
   right_inv := by intro i; apply Fin.ext; simp }

/-- enumeration of the double window, with zero corresponding to site `-t`. -/
def enumTwoWindow (t N : ℕ) (ht : 0 < t) (hN : 0 < N) :
     (↥(twoNatWindow t N)) ≃ Fin ((N+1)*t) := by
  let f (j : ↥(twoNatWindow t N)) : Fin ((N+1)*t) :=
    ⟨Int.toNat (j.val + (t:ℤ)), by
      have hh := mem_twoNatWindow (j:=j.val) ht hN |>.1 j.property
      have hz : 0 ≤ j.val + (t:ℤ) := by linarith [hh.1]
      have hu : j.val + (t:ℤ) < (((N+1)*t:ℕ) : ℤ) := by
        push_cast
        push_cast at hh
        ring_nf at *
        omega
      exact (Int.toNat_lt hz).mpr hu ⟩
  let g (i : Fin ((N+1)*t)) : ↥(twoNatWindow t N) :=
    ⟨(i.val : ℤ) - (t:ℤ), by
      apply mem_twoNatWindow (j := (i.val:ℤ) - (t:ℤ)) ht hN |>.2
      constructor
      · omega
      · have hi : (i.val:ℤ) < (((N+1)*t:ℕ):ℤ) := by exact_mod_cast i.isLt
        have hid : (((N+1)*t:ℕ):ℤ) = ((N*t:ℕ):ℤ) + t := by
          exact_mod_cast (show (N+1)*t = N*t+t by simp [Nat.add_mul])
        rw [hid] at hi
        omega ⟩
  exact
   { toFun := f, invFun := g
     left_inv := by
        intro j
        apply Subtype.ext
        dsimp [f,g]
        have hh := mem_twoNatWindow (j:=j.val) ht hN |>.1 j.property
        have hz : 0 ≤ j.val + (t:ℤ) := by linarith
        simp [Int.toNat_of_nonneg hz]
     right_inv := by
        intro i
        apply Fin.ext
        dsimp [f,g]
        have hz : (0 : ℤ) ≤ (i.val:ℤ) := by omega
        simp }

/-- Split a block of `N*t` bits into `N` consecutive words of length `t`. -/
def splitWords (N t : ℕ) : (Fin (N*t) → Bool) ≃ (Fin N → Fin t → Bool) := by
  -- reindex and uncurry
  let ix : (Fin (N*t) → Bool) ≃ ((Fin N × Fin t) → Bool) :=
     (Equiv.arrowCongr (finProdFinEquiv) (Equiv.refl Bool)).symm -- wait direction
  exact ix.trans (Equiv.curry _ _ _)

/- check curry name -/

def lineWords (N t : ℕ) :
  ((↥(natWindow (N*t))) → Bool) ≃ (Fin N → Fin t → Bool) :=
 (Equiv.arrowCongr (enumWindow (N*t)) (Equiv.refl Bool)).trans (splitWords N t)

def lineRows (N t : ℕ) (ht : 0 < t) (hN : 0 < N) :
  ((↥(twoNatWindow t N)) → Bool) ≃ (Fin (N+1) → Fin t → Bool) :=
 (Equiv.arrowCongr (enumTwoWindow t N ht hN) (Equiv.refl Bool)).trans (splitWords (N+1) t)

-- computation rules: the equivalences merely reindex.
@[simp] lemma lineWords_apply (N t : ℕ)
    (w : (↥(natWindow (N*t)) → Bool)) (i : Fin N) (j : Fin t) :
    lineWords N t w i j =
       w ⟨((j.val + t*i.val : ℕ) : ℤ), mem_natWindow.mpr
          ⟨by omega, by
             have hi:= i.isLt; have hj:= j.isLt
             have : j.val + t*i.val < N*t := by nlinarith
             exact_mod_cast this⟩⟩ := by
  rfl

@[simp] lemma lineRows_apply (N t : ℕ) (ht : 0 < t) (hN : 0 < N)
    (w : (↥(twoNatWindow t N) → Bool)) (i : Fin (N+1)) (j : Fin t) :
    lineRows N t ht hN w i j =
       w ⟨((j.val + t*i.val : ℕ) : ℤ) - (t:ℤ), by
          apply mem_twoNatWindow (j:=(((j.val+t*i.val:ℕ):ℤ)-(t:ℤ))) ht hN |>.2
          constructor
          · have : 0 ≤ (i.val*t:ℤ) := by positivity
            have : (0:ℤ) ≤ ((j.val+t*i.val:ℕ):ℤ) := by omega
            omega
          · have hi:=i.isLt; have hj:=j.isLt
            have hh : j.val+t*i.val < (N+1)*t := by nlinarith
            have hcast : (((j.val+t*i.val:ℕ):ℤ)) < (((N+1)*t:ℕ):ℤ) := by exact_mod_cast hh
            have hid : (((N+1)*t:ℕ):ℤ) = ((N*t:ℕ):ℤ) + t := by
              exact_mod_cast (show (N+1)*t = N*t+t by simp [Nat.add_mul])
            rw [hid] at hcast
            omega ⟩ := by
 rfl

/-- splitting a sum of two packets of bits. -/
def splitBits (d b : ℕ) :
    (Fin (d+b) → Bool) ≃ ((Fin d → Bool) × (Fin b → Bool)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin b => Bool))

@[simp] lemma splitBits_left (d b : ℕ) (u : Fin (d+b) → Bool) (i : Fin d) :
  (splitBits d b u).1 i = u ⟨i.val, by omega⟩ := by
  rfl
@[simp] lemma splitBits_right (d b : ℕ) (u : Fin (d+b) → Bool) (i : Fin b) :
  (splitBits d b u).2 i = u ⟨d+i.val, by omega⟩ := by
  rfl

/-- Decoding one packet into a K-word and a tag word. -/
noncomputable def packet {δ : Type*} [Fintype δ] (b : ℕ) :
    (Fin (Fintype.card δ + b) → Bool) ≃
       ((δ → Bool) × (Fin b → Bool)) :=
  (splitBits (Fintype.card δ) b).trans
    (Equiv.prodCongr
      (Equiv.arrowCongr (Fintype.equivFin δ).symm (Equiv.refl Bool))
      (Equiv.refl _))

@[simp] lemma packet_left {δ : Type*} [Fintype δ] (b : ℕ)
 (u : Fin (Fintype.card δ+b) → Bool) (i : δ) :
 (packet (δ:=δ) b u).1 i = u ⟨(Fintype.equivFin δ i).val, by
   have hh := (Fintype.equivFin δ i).isLt; omega⟩ := by
 rfl
@[simp] lemma packet_right {δ : Type*} [Fintype δ] (b : ℕ)
 (u : Fin (Fintype.card δ+b) → Bool) (i : Fin b) :
 (packet (δ:=δ) b u).2 i = u ⟨Fintype.card δ + i.val, by omega⟩ := by rfl

/-- packetize a whole line. -/
noncomputable def packetWindow {δ : Type*} [Fintype δ]
    (b N : ℕ) :
    (↥(natWindow (N*(Fintype.card δ+b))) → Bool) ≃
      (Fin N → ((δ → Bool) × (Fin b → Bool))) :=
 (lineWords N (Fintype.card δ+b)).trans
   (Equiv.piCongrRight (fun _ => packet (δ:=δ) b))

noncomputable def packetRows {δ : Type*} [Fintype δ]
    (b N : ℕ) (ht : 0 < Fintype.card δ + b) (hN : 0 < N) :
    (↥(twoNatWindow (Fintype.card δ+b) N) → Bool) ≃
      (Fin (N+1) → ((δ → Bool) × (Fin b → Bool))) :=
 (lineRows N (Fintype.card δ+b) ht hN).trans
   (Equiv.piCongrRight (fun _ => packet (δ:=δ) b))

end HalmosSupport

end
-- END INLINED FILE: Mathlib/Support/halmos_generic_weak_mixing_6e52366a64/MarkerLine.lean

-- BEGIN INLINED MAIN PRELUDE

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory Filter Topology
open scoped symmDiff

variable {X : Type*} [MeasurableSpace X]
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/



-- A useful elementary fact about a generated topology.  The basic opens of
-- ``generateFrom q`` are exactly finite intersections of members of `q`.
-- Writing this down explicitly avoids an induction over `GenerateOpen` when
-- one wants to prove density.
lemma dense_generateFrom_of_forall_finite
    {α : Type*} [t : TopologicalSpace α]
    (q : Set (Set α)) (ht : t = TopologicalSpace.generateFrom q)
    {D : Set α}
    (hD : ∀ f : Set (Set α), f.Finite → f ⊆ q →
      (⋂₀ f).Nonempty → ((⋂₀ f) ∩ D).Nonempty) : Dense D := by
  -- `isTopologicalBasis_of_subbasis` is slightly more convenient here than
  -- the `GenerateOpen` induction: it includes the empty finite intersection
  -- (so the argument also handles the indiscrete case).
  have hb := TopologicalSpace.isTopologicalBasis_of_subbasis (α := α) ht
  apply (TopologicalSpace.IsTopologicalBasis.dense_iff hb).2
  intro o ho hne
  rcases ho with ⟨f, hf, rfl⟩
  exact hD f hf.1 hf.2 hne

-- Specialising the preceding lemma to the weak topology is often the first
-- step in approximation arguments.  Notice that the members of the
-- subbasis remember a *centre* automorphism as well as the set being tested.
lemma dense_weakTopology_of_finite_subbasic
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    {D : Set (Automorphism m)}
    (hD : ∀ f : Set (Set (Automorphism m)),
      f.Finite →
      f ⊆ { U | ∃ (T₀ : Automorphism m) (A : Set X) (ε : ℝ),
        MeasurableSet A ∧ 0 < ε ∧
        U = { T : Automorphism m |
          m ((T.toEquiv '' A) ∆ (T₀.toEquiv '' A)) < ENNReal.ofReal ε } } →
      (⋂₀ f).Nonempty → ((⋂₀ f) ∩ D).Nonempty) : Dense D := by
  classical
  let q : Set (Set (Automorphism m)) :=
    { U | ∃ (T₀ : Automorphism m) (A : Set X) (ε : ℝ),
        MeasurableSet A ∧ 0 < ε ∧
        U = { T : Automorphism m |
          m ((T.toEquiv '' A) ∆ (T₀.toEquiv '' A)) < ENNReal.ofReal ε } }
  change Dense D
  apply dense_generateFrom_of_forall_finite q (t := weakTopologyAutomorphism m) rfl
  intro f hf hfq hne
  apply hD f hf ?_ hne
  exact hfq

-- A more useful version of the criterion puts a distinguished centre in the
-- finite intersection.  This is precisely the finite-neighbourhood statement
-- one has to verify by a measure-theoretic approximation construction.
lemma dense_weakMixing_of_finite_neighborhoods
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (hApprox : ∀ (T₀ : Automorphism m) (f : Set (Set (Automorphism m))),
      f.Finite →
      f ⊆ { U | ∃ (S₀ : Automorphism m) (A : Set X) (ε : ℝ),
        MeasurableSet A ∧ 0 < ε ∧
        U = { S : Automorphism m |
          m ((S.toEquiv '' A) ∆ (S₀.toEquiv '' A)) < ENNReal.ofReal ε } } →
      T₀ ∈ ⋂₀ f →
      ∃ T ∈ ⋂₀ f, IsWeaklyMixing m T) :
    Dense {T : Automorphism m | IsWeaklyMixing m T} := by
  classical
  refine dense_weakTopology_of_finite_subbasic m ?_
  intro f hf hfq hne
  rcases hne with ⟨T₀, hT₀⟩
  obtain ⟨T, hTf, hmix⟩ := hApprox T₀ f hf hfq hT₀
  refine ⟨T, hTf, ?_⟩
  exact hmix

-- Each of the inequalities used to generate the weak topology is indeed
-- an open set, not merely a member of a set of nominal generators.  The
-- statement with a centre is handy for later neighbourhood-basis arguments.
lemma isOpen_weak_ball
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T₀ : Automorphism m) (A : Set X) (hA : MeasurableSet A)
    {ε : ℝ} (hε : 0 < ε) :
    IsOpen { T : Automorphism m |
      m ((T.toEquiv '' A) ∆ (T₀.toEquiv '' A)) < ENNReal.ofReal ε } := by
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  exact ⟨T₀, A, ε, hA, hε, rfl⟩

-- The open generated above contains its centre.  In particular no
-- strict-positivity condition is lost on passing from a real radius to
-- `ENNReal.ofReal`.
lemma mem_weak_ball_self
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T₀ : Automorphism m) (A : Set X)
    {ε : ℝ} (hε : 0 < ε) :
    T₀ ∈ { T : Automorphism m |
      m ((T.toEquiv '' A) ∆ (T₀.toEquiv '' A)) < ENNReal.ofReal ε } := by
  change m ((T₀.toEquiv '' A) ∆ (T₀.toEquiv '' A)) < ENNReal.ofReal ε
  have hp : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  simpa using hp


-- If a centre `T₀` lies in one of the generating balls, a *smaller* ball
-- with centre `T₀` is contained in it.  The proof is just the triangle
-- inequality for symmetric difference, but it is worth doing with `ENNReal`:
-- the subbasis uses real radii through `ofReal`.
lemma exists_weak_ball_subset
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (S₀ T₀ : Automorphism m) (A : Set X)
    {ε : ℝ} (hε : 0 < ε)
    (hmem : T₀ ∈ { S : Automorphism m |
      m ((S.toEquiv '' A) ∆ (S₀.toEquiv '' A)) < ENNReal.ofReal ε }) :
    ∃ δ : ℝ, 0 < δ ∧
      {S : Automorphism m |
        m ((S.toEquiv '' A) ∆ (T₀.toEquiv '' A)) < ENNReal.ofReal δ}
        ⊆ {S : Automorphism m |
          m ((S.toEquiv '' A) ∆ (S₀.toEquiv '' A)) < ENNReal.ofReal ε} := by
  classical
  let d : ENNReal := m ((T₀.toEquiv '' A) ∆ (S₀.toEquiv '' A))
  have hdlt : d < ENNReal.ofReal ε := hmem
  have he_top_lt : ENNReal.ofReal ε < (⊤ : ENNReal) := ENNReal.ofReal_lt_top
  have he_top : ENNReal.ofReal ε ≠ (⊤ : ENNReal) := ne_of_lt he_top_lt
  have hdtop : d ≠ (⊤ : ENNReal) :=
    ne_of_lt (lt_of_lt_of_le hdlt le_top)
  have hdr : d.toReal < ε := by
    have hz := (ENNReal.toReal_lt_toReal hdtop he_top).2 hdlt
    simpa [ENNReal.toReal_ofReal hε.le] using hz
  let δ : ℝ := (ε - d.toReal) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  refine ⟨δ, hδ, ?_⟩
  intro S hS
  -- First compare the two radii in `ENNReal`.
  have hsumreal : d.toReal + δ < ε := by
    dsimp [δ]
    linarith
  have hsum : d + ENNReal.ofReal δ < ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hdtop]
    rw [← ENNReal.ofReal_add (ENNReal.toReal_nonneg) hδ.le]
    have hiff := (ENNReal.ofReal_lt_ofReal_iff (p := d.toReal + δ) hε)
    exact hiff.2 hsumreal
  change m ((S.toEquiv '' A) ∆ (S₀.toEquiv '' A)) < ENNReal.ofReal ε
  have htri :
      m ((S.toEquiv '' A) ∆ (S₀.toEquiv '' A))
        ≤ m ((S.toEquiv '' A) ∆ (T₀.toEquiv '' A)) + d := by
    simpa [d] using
      (MeasureTheory.measure_symmDiff_le
        (μ := m) (S.toEquiv '' A) (T₀.toEquiv '' A) (S₀.toEquiv '' A))
  have hsmall :
      m ((S.toEquiv '' A) ∆ (T₀.toEquiv '' A)) < ENNReal.ofReal δ := hS
  have hadd :
      m ((S.toEquiv '' A) ∆ (T₀.toEquiv '' A)) + d
        < ENNReal.ofReal ε := by
    have h' :
        m ((S.toEquiv '' A) ∆ (T₀.toEquiv '' A)) + d
          < ENNReal.ofReal δ + d :=
      ENNReal.add_lt_add_right hdtop hsmall
    have hcomm : ENNReal.ofReal δ + d = d + ENNReal.ofReal δ := by
      ac_rfl
    exact lt_trans h' (by simpa [hcomm] using hsum)
  exact lt_of_le_of_lt htri hadd


-- Consequently a common-centre approximation theorem (with finitely many
-- measurable sets) is enough for density.  This reduces finite intersections
-- of subbasic opens, whose written centres may all be different, to the
-- usual formulation with the centre equal to the point of the neighbourhood.
universe u
lemma dense_weakMixing_of_common_center
    {X : Type u} [MeasurableSpace X] (m : Measure X)
    (hCommon : ∀ (ι : Type u) [Fintype ι]
      (T₀ : Automorphism m) (A : ι → Set X) (ε : ι → ℝ),
      (∀ i, MeasurableSet (A i)) →
      (∀ i, 0 < ε i) →
      ∃ T : Automorphism m, IsWeaklyMixing m T ∧
        ∀ i, m ((T.toEquiv '' (A i)) ∆ (T₀.toEquiv '' (A i))) <
          ENNReal.ofReal (ε i)) :
    Dense { T : Automorphism m | IsWeaklyMixing m T } := by
  classical
  -- use the finite-intersection criterion above
  apply dense_weakMixing_of_finite_neighborhoods m
  intro T₀ f hf hfq hT₀
  letI : Fintype {U : Set (Automorphism m) // U ∈ f} := hf.fintype
  have hi (i : {U : Set (Automorphism m) // U ∈ f}) :
      ∃ S₀ : Automorphism m, ∃ A : Set X, ∃ ε : ℝ,
        MeasurableSet A ∧ 0 < ε ∧
        i.1 = { S : Automorphism m |
          m ((S.toEquiv '' A) ∆ (S₀.toEquiv '' A)) < ENNReal.ofReal ε } := by
    simpa using (hfq i.2)
  choose S₀ h1 using hi
  choose A h2 using h1
  choose e h3 using h2
  have hmem (i : {U : Set (Automorphism m) // U ∈ f}) :
      T₀ ∈ { S : Automorphism m |
        m ((S.toEquiv '' (A i)) ∆ ((S₀ i).toEquiv '' (A i))) <
          ENNReal.ofReal (e i) } := by
    rw [← (h3 i).2.2]
    exact (Set.mem_sInter.mp hT₀) i.1 i.2
  have hsmall (i : {U : Set (Automorphism m) // U ∈ f}) :
      ∃ δ : ℝ, 0 < δ ∧
        { S : Automorphism m |
          m ((S.toEquiv '' (A i)) ∆ (T₀.toEquiv '' (A i))) <
            ENNReal.ofReal δ } ⊆
        { S : Automorphism m |
          m ((S.toEquiv '' (A i)) ∆ ((S₀ i).toEquiv '' (A i))) <
            ENNReal.ofReal (e i) } := by
    exact exists_weak_ball_subset m (S₀ i) T₀ (A i) (h3 i).2.1 (hmem i)
  choose δ hδ using hsmall
  obtain ⟨T, hmix, hclose⟩ :=
    hCommon {U : Set (Automorphism m) // U ∈ f} T₀ A δ
      (fun i => (h3 i).1) (fun i => (hδ i).1)
  refine ⟨T, ?_, hmix⟩
  apply Set.mem_sInter.mpr
  intro U hU
  change T ∈ (⟨U, hU⟩ : {V : Set (Automorphism m) // V ∈ f}).1
  rw [(h3 (⟨U, hU⟩ : {V : Set (Automorphism m) // V ∈ f})).2.2]
  exact (hδ (⟨U, hU⟩ : {V : Set (Automorphism m) // V ∈ f})).2
    (hclose (⟨U, hU⟩ : {V : Set (Automorphism m) // V ∈ f}))


-- Equivalently, it is enough to prove the common-centre statement for
-- numbered finite families.  This formulation has no universe issue with
-- the subtype of members of a finite subfamily of the subbasis.
lemma dense_weakMixing_of_fin_center
    {X : Type u} [MeasurableSpace X] (m : Measure X)
    (hFin : ∀ (n : ℕ) (T₀ : Automorphism m)
      (A : Fin n → Set X) (ε : Fin n → ℝ),
      (∀ i, MeasurableSet (A i)) →
      (∀ i, 0 < ε i) →
      ∃ T : Automorphism m, IsWeaklyMixing m T ∧
        ∀ i, m ((T.toEquiv '' (A i)) ∆ (T₀.toEquiv '' (A i))) <
          ENNReal.ofReal (ε i)) :
    Dense { T : Automorphism m | IsWeaklyMixing m T } := by
  classical
  apply dense_weakMixing_of_common_center m
  intro ι _inst T₀ A ε hA hε
  let eι := Fintype.equivFin ι
  obtain ⟨T, hT, hclose⟩ :=
    hFin (Fintype.card ι) T₀
      (fun j : Fin (Fintype.card ι) => A (eι.symm j))
      (fun j : Fin (Fintype.card ι) => ε (eι.symm j))
      (fun j => hA (eι.symm j)) (fun j => hε (eι.symm j))
  refine ⟨T, hT, ?_⟩
  intro i
  simpa [eι] using (hclose (eι i))



-- Conversely a dense collection already meets every one of the finite
-- common-centre neighbourhoods.  This direction is often handy: it exposes
-- exactly the finite approximation datum with no choice of a basis or a
-- countability assumption.  In particular the empty family causes no
-- exception (`iInter` is `univ`).
lemma fin_center_of_dense
    {X : Type u} [MeasurableSpace X] (m : Measure X)
    {D : Set (Automorphism m)} (hD : Dense D) :
    ∀ (n : ℕ) (T₀ : Automorphism m)
      (A : Fin n → Set X) (ε : Fin n → ℝ),
      (∀ i, MeasurableSet (A i)) → (∀ i, 0 < ε i) →
      ∃ T : Automorphism m, T ∈ D ∧
        ∀ i, m ((T.toEquiv '' (A i)) ∆ (T₀.toEquiv '' (A i))) <
          ENNReal.ofReal (ε i) := by
  classical
  intro n T₀ A ε hA hε
  let U : Set (Automorphism m) :=
    ⋂ i : Fin n,
      {T : Automorphism m |
        m ((T.toEquiv '' (A i)) ∆ (T₀.toEquiv '' (A i))) <
          ENNReal.ofReal (ε i)}
  have hUopen : IsOpen U := by
    dsimp [U]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_weak_ball m T₀ (A i) (hA i) (hε i)
  have hUmem : T₀ ∈ U := by
    dsimp [U]
    apply Set.mem_iInter.mpr
    intro i
    exact mem_weak_ball_self m T₀ (A i) (hε i)
  obtain ⟨T, hTD, hTU⟩ := hD.exists_mem_open hUopen ⟨T₀, hUmem⟩
  refine ⟨T, hTD, ?_⟩
  intro i
  exact Set.mem_iInter.mp hTU i

lemma fin_center_weakMixing_of_dense
    {X : Type u} [MeasurableSpace X] (m : Measure X)
    (hd : Dense {T : Automorphism m | IsWeaklyMixing m T}) :
    ∀ (n : ℕ) (T₀ : Automorphism m)
      (A : Fin n → Set X) (ε : Fin n → ℝ),
      (∀ i, MeasurableSet (A i)) → (∀ i, 0 < ε i) →
      ∃ T : Automorphism m, IsWeaklyMixing m T ∧
        ∀ i, m ((T.toEquiv '' (A i)) ∆ (T₀.toEquiv '' (A i))) <
          ENNReal.ofReal (ε i) := by
  intro n T₀ A ε hA hε
  obtain ⟨T,hmem,hclose⟩ := fin_center_of_dense m hd n T₀ A ε hA hε
  exact ⟨T,hmem,hclose⟩




-- Coordinates under a measure-preserving measurable equivalence can be changed
-- exactly.  Unlike the unitary ``mod null'' conjugations one often uses in the
-- subject, this uses the genuine measurable equivalences in the definition of
-- `Automorphism`.
noncomputable def transportAutomorphism
    {Y : Type*} [MeasurableSpace Y]
    (m : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y)
    (he : MeasurePreserving (e : X → Y) m ν)
    (S : Automorphism ν) : Automorphism m where
  toEquiv := e.trans (S.toEquiv.trans e.symm)
  measurePreserving := by
    have h1 : MeasurePreserving
        ((e.symm : Y → X) ∘ (S.toEquiv : Y → Y) ∘ (e : X → Y)) m m :=
      (MeasurePreserving.symm e he).comp (S.measurePreserving.comp he)
    -- `MeasurableEquiv.trans` has this as its coercion.
    exact h1

@[simp] lemma transportAutomorphism_apply
    {Y : Type*} [MeasurableSpace Y]
    (m : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y)
    (he : MeasurePreserving (e : X → Y) m ν)
    (S : Automorphism ν) (x : X) :
    (transportAutomorphism m ν e he S).toEquiv x = e.symm (S.toEquiv (e x)) := rfl

-- Iterates of the transported map intertwine pointwise with the old ones.
lemma transport_iterate_intertwine
    {Y : Type*} [MeasurableSpace Y]
    (m : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y)
    (he : MeasurePreserving (e : X → Y) m ν)
    (S : Automorphism ν) (k : ℕ) (x : X) :
    e (((transportAutomorphism m ν e he S).toEquiv : X → X)^[k] x)
      = ((S.toEquiv : Y → Y)^[k]) (e x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [Function.iterate_succ_apply']
      -- choose the expansion with the new step on the outside
      simp only [transportAutomorphism_apply]
      -- the defining step is `e (e.symm (S _)) = S _`
      simp
      rw [ih x]

-- It is often useful to measure images rather than preimages of the coordinate
-- map. There are no measurability side conditions here: a measurable equivalence
-- is a measurable embedding, so `measure_preimage_emb` applies to *all* sets.
lemma transport_measure_image
    {Y : Type*} [MeasurableSpace Y]
    (m : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y)
    (he : MeasurePreserving (e : X → Y) m ν)
    (A : Set X) : m A = ν (e '' A) := by
  have h := he.measure_preimage_emb e.measurableEmbedding (e '' A)
  simpa using h

-- Weak mixing is invariant under a genuine change of measured coordinates.
-- Keeping the proof with sets rather than with Koopman operators makes the
-- convention on inverse images in the definition completely explicit.
lemma transport_weakMixing
    {Y : Type*} [MeasurableSpace Y]
    (m : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y)
    (he : MeasurePreserving (e : X → Y) m ν)
    (S : Automorphism ν)
    (hS : IsWeaklyMixing ν S) :
    IsWeaklyMixing m (transportAutomorphism m ν e he S) := by
  classical
  intro A B hA hB
  let A' : Set Y := e '' A
  let B' : Set Y := e '' B
  have hA' : MeasurableSet A' := e.measurableEmbedding.measurableSet_image' hA
  have hB' : MeasurableSet B' := e.measurableEmbedding.measurableSet_image' hB
  have hpre (k : ℕ) :
      (((transportAutomorphism m ν e he S).toEquiv : X → X)^[k] ⁻¹' A)
        = e ⁻¹' (((S.toEquiv : Y → Y)^[k] ⁻¹' A')) := by
    ext x
    change (((transportAutomorphism m ν e he S).toEquiv : X → X)^[k] x ∈ A)
      ↔ ((S.toEquiv : Y → Y)^[k] (e x) ∈ A')
    rw [← transport_iterate_intertwine m ν e he S k x]
    -- membership in the image of a bijection
    constructor
    · intro hx
      exact ⟨_, hx, rfl⟩
    · intro hx
      rcases hx with ⟨z, hz, hezx⟩
      have : z =
          (((transportAutomorphism m ν e he S).toEquiv : X → X)^[k] x) :=
        e.injective hezx
      simpa [this] using hz
  have hBpre : (e : X → Y) ⁻¹' B' = B := by
    exact e.injective.preimage_image B
  have hterm (k : ℕ) :
      m ((((transportAutomorphism m ν e he S).toEquiv : X → X)^[k] ⁻¹' A) ∩ B)
        = ν (((S.toEquiv : Y → Y)^[k] ⁻¹' A') ∩ B') := by
    rw [hpre k]
    rw [← hBpre]
    rw [← Set.preimage_inter]
    exact he.measure_preimage_emb e.measurableEmbedding _
  have hma : m A = ν A' := transport_measure_image m ν e he A
  have hmb : m B = ν B' := transport_measure_image m ν e he B
  have hlim := hS A' B' hA' hB'
  -- The two sequences of real numbers are definitionally the same after
  -- the preceding set and measure equalities.
  simpa [hterm, hma, hmb] using hlim

lemma automorphism_ext {m : Measure X} {T U : Automorphism m}
    (h : T.toEquiv = U.toEquiv) : T = U := by
  cases T with
  | mk f hf =>
    cases U with
    | mk g hg =>
      dsimp at h
      cases h
      rfl

-- The reverse implication too; this is the convenient form when transporting
-- examples or approximation statements.
lemma transport_weakMixing_iff
    {Y : Type*} [MeasurableSpace Y]
    (m : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y)
    (he : MeasurePreserving (e : X → Y) m ν)
    (S : Automorphism ν) :
    IsWeaklyMixing m (transportAutomorphism m ν e he S) ↔ IsWeaklyMixing ν S := by
  constructor
  · intro h
    have he' : MeasurePreserving (e.symm : Y → X) ν m :=
      MeasurePreserving.symm e he
    have hback := transport_weakMixing ν m e.symm he'
      (transportAutomorphism m ν e he S) h
    -- transporting twice is the original automorphism.  The first proof of
    -- invariance was pointwise; here it is useful to record the exact bundled
    -- equality.
    have hEq : transportAutomorphism ν m e.symm he'
          (transportAutomorphism m ν e he S) = S := by
      apply automorphism_ext
      apply MeasurableEquiv.ext
      funext y
      simp [transportAutomorphism_apply]
    rw [hEq] at hback
    exact hback
  · exact fun h => transport_weakMixing m ν e he S h


lemma transport_image
    {Y : Type*} [MeasurableSpace Y] {X : Type*} [MeasurableSpace X]
    (m : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y)
    (he : MeasurePreserving (e : X → Y) m ν)
    (S : Automorphism ν) (A : Set X) :
    e '' ((transportAutomorphism m ν e he S).toEquiv '' A) =
      S.toEquiv '' (e '' A) := by
  ext y
  constructor
  · rintro ⟨x', ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
    simp [transportAutomorphism_apply]
  · rintro ⟨y', ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(transportAutomorphism m ν e he S).toEquiv x,
      ⟨x, hx, rfl⟩, ?_⟩
    simp [transportAutomorphism_apply]

lemma transport_image_preimage
    {Y : Type*} [MeasurableSpace Y] {X : Type*} [MeasurableSpace X]
    (m : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y)
    (he : MeasurePreserving (e : X → Y) m ν)
    (S : Automorphism ν) (A : Set X) :
    (transportAutomorphism m ν e he S).toEquiv '' A =
      (e : X → Y) ⁻¹' (S.toEquiv '' (e '' A)) := by
  rw [← transport_image m ν e he S A]
  exact (Set.preimage_image_eq _ e.injective).symm

-- Consequently the finite-centre approximation problem is independent of
-- exact measurable coordinates. This is a useful reduction because the Borel
-- structure of an arbitrary atom-free standard space may first be replaced by
-- a familiar standard Borel carrier; the centre and all the requested finite
-- errors are transported literally, not merely almost everywhere.
lemma dense_weakMixing_of_fin_center_via_equiv
    {X : Type u} [MeasurableSpace X]
    {Y : Type*} [MeasurableSpace Y]
    (m : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y)
    (he : MeasurePreserving (e : X → Y) m ν)
    (hFinY : ∀ (n : ℕ) (R₀ : Automorphism ν)
      (C : Fin n → Set Y) (ε : Fin n → ℝ),
      (∀ i, MeasurableSet (C i)) →
      (∀ i, 0 < ε i) →
      ∃ R : Automorphism ν, IsWeaklyMixing ν R ∧
        ∀ i, ν ((R.toEquiv '' (C i)) ∆ (R₀.toEquiv '' (C i))) <
          ENNReal.ofReal (ε i)) :
    Dense {T : Automorphism m | IsWeaklyMixing m T} := by
  classical
  apply dense_weakMixing_of_fin_center m
  intro n T₀ A ε hA hε
  let he' : MeasurePreserving (e.symm : Y → X) ν m :=
    MeasurePreserving.symm e he
  let R₀ : Automorphism ν := transportAutomorphism ν m e.symm he' T₀
  let C : Fin n → Set Y := fun i => e '' (A i)
  have hC (i : Fin n) : MeasurableSet (C i) :=
    e.measurableEmbedding.measurableSet_image' (hA i)
  obtain ⟨R, hR, hclose⟩ := hFinY n R₀ C ε hC hε
  let T : Automorphism m := transportAutomorphism m ν e he R
  have hT : IsWeaklyMixing m T := transport_weakMixing m ν e he R hR
  refine ⟨T, hT, ?_⟩
  intro i
  have hceni : transportAutomorphism m ν e he R₀ = T₀ := by
    apply automorphism_ext
    apply MeasurableEquiv.ext
    funext x
    simp [R₀, transportAutomorphism_apply]
  have h1 :
      (transportAutomorphism m ν e he R).toEquiv '' (A i) =
        (e : X → Y) ⁻¹' (R.toEquiv '' (C i)) := by
    simpa [C] using (transport_image_preimage m ν e he R (A i))
  have h2 :
      T₀.toEquiv '' (A i) =
        (e : X → Y) ⁻¹' (R₀.toEquiv '' (C i)) := by
    rw [← hceni]
    simpa [C] using (transport_image_preimage m ν e he R₀ (A i))
  change m ((T.toEquiv '' (A i)) ∆ (T₀.toEquiv '' (A i))) <
      ENNReal.ofReal (ε i)
  have hm :
      m (((e : X → Y) ⁻¹' (R.toEquiv '' (C i))) ∆
         ((e : X → Y) ⁻¹' (R₀.toEquiv '' (C i)))) =
        ν ((R.toEquiv '' (C i)) ∆ (R₀.toEquiv '' (C i))) := by
    rw [← Set.preimage_symmDiff]
    exact he.measure_preimage_emb e.measurableEmbedding _
  change m (((transportAutomorphism m ν e he R).toEquiv '' (A i)) ∆
      (T₀.toEquiv '' (A i))) < ENNReal.ofReal (ε i)
  rw [h1, h2, hm]
  exact hclose i

lemma noAtoms_map_measurableEquiv
    {X : Type*} {Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (m : Measure X) [NoAtoms m] (e : X ≃ᵐ Y) :
    NoAtoms (Measure.map (e : X → Y) m) where
  measure_singleton y := by
    rw [MeasurableEquiv.map_apply]
    have hset : (e : X → Y) ⁻¹' ({y} : Set Y) = {e.symm y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        -- apply the inverse of the equivalence to the equality
        simpa using congrArg (fun z : Y => e.symm z) h
      · intro h
        simp [h]
    rw [hset]
    exact measure_singleton _


-- Conjugacy is the special case of the preceding change-of-coordinates where
-- the two underlying measures agree.  Stating the finite approximation in
-- this form isolates precisely the Rokhlin/cutting-and-stacking ingredient:
-- the conjugates of one weakly mixing map have to meet each finite family of
-- weak balls.
noncomputable def conjugateAutomorphism
    {X : Type*} [MeasurableSpace X]
    (m : Measure X) (U R : Automorphism m) : Automorphism m :=
  transportAutomorphism m m U.toEquiv U.measurePreserving R

lemma conjugate_weakMixing
    {X : Type*} [MeasurableSpace X]
    (m : Measure X) (U R : Automorphism m)
    (hR : IsWeaklyMixing m R) :
    IsWeaklyMixing m (conjugateAutomorphism m U R) := by
  exact
    transport_weakMixing m m U.toEquiv U.measurePreserving R hR

lemma dense_weakMixing_of_conjugates_fin
    {X : Type u} [MeasurableSpace X]
    (m : Measure X) (R : Automorphism m)
    (hR : IsWeaklyMixing m R)
    (hconj : ∀ (n : ℕ) (T₀ : Automorphism m)
      (A : Fin n → Set X) (ε : Fin n → ℝ),
      (∀ i, MeasurableSet (A i)) →
      (∀ i, 0 < ε i) →
      ∃ U : Automorphism m,
        ∀ i, m (((conjugateAutomorphism m U R).toEquiv '' (A i)) ∆
                    (T₀.toEquiv '' (A i))) < ENNReal.ofReal (ε i)) :
    Dense {T : Automorphism m | IsWeaklyMixing m T} := by
  classical
  apply dense_weakMixing_of_fin_center m
  intro n T₀ A ε hA hε
  obtain ⟨U, hU⟩ := hconj n T₀ A ε hA hε
  exact ⟨conjugateAutomorphism m U R, conjugate_weakMixing m U R hR, hU⟩

-- A probability measure without points cannot live on a countable space.
-- This elementary fact is the starting point for applying the Borel
-- isomorphism theorem before a cutting-and-stacking construction.
lemma not_countable_of_noAtoms_prob (m : Measure X)
    [IsProbabilityMeasure m] [NoAtoms m] : ¬ Countable X := by
  intro h
  letI : Countable X := h
  have hz : m (Set.univ) = 0 := Set.countable_univ.measure_zero m
  have ho : m (Set.univ) = 1 := measure_univ
  rw [ho] at hz
  norm_num at hz


-- It is enough for the density ingredient to work on the single carrier
-- `ℝ`, with an arbitrary atom-free probability law.  This is an exact Borel
-- change of coordinates (the law is pushed forward), not the much harder
-- still-missing statement that every such law is Lebesgue up to null sets.
-- Thus all the remaining cutting-and-stacking/weak-mixing content after this
-- lemma is a statement about one concrete standard Borel type.
lemma dense_weakMixing_reduce_real
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    (hReal : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν]
      (n : ℕ) (R₀ : Automorphism ν)
      (C : Fin n → Set ℝ) (ε : Fin n → ℝ),
      (∀ i, MeasurableSet (C i)) →
      (∀ i, 0 < ε i) →
      ∃ R : Automorphism ν, IsWeaklyMixing ν R ∧
        ∀ i, ν ((R.toEquiv '' (C i)) ∆ (R₀.toEquiv '' (C i))) <
          ENNReal.ofReal (ε i)) :
    Dense {T : Automorphism m | IsWeaklyMixing m T} := by
  classical
  let e : X ≃ᵐ ℝ :=
    PolishSpace.measurableEquivOfNotCountable
      (not_countable_of_noAtoms_prob m) (not_countable : ¬ Countable ℝ)
  let ν : Measure ℝ := Measure.map (e : X → ℝ) m
  letI hνp : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (e.measurable.aemeasurable)
  letI hνa : NoAtoms ν := noAtoms_map_measurableEquiv m e
  have he : MeasurePreserving (e : X → ℝ) m ν :=
    e.measurable.measurePreserving m
  exact dense_weakMixing_of_fin_center_via_equiv m ν e he
    (fun n R₀ C ε => hReal ν n R₀ C ε)


-- On the real-line model no atom forces the cumulative distribution function
-- to be continuous on both sides. This small regularity fact is a basic
-- ingredient for making finite equal-measure partitions (quantiles). The
-- general cdf in mathlib is right-continuous; the possible left jump is
-- exactly its Stieltjes measure of the singleton.
lemma continuous_cdf_of_noAtoms (ν : Measure ℝ)
    [IsProbabilityMeasure ν] [NoAtoms ν] :
    Continuous (fun x : ℝ => (ProbabilityTheory.cdf ν) x) := by
  -- it suffices to check continuity at a point from the left and the right
  apply continuous_iff_continuousAt.2
  intro x
  let f : StieltjesFunction ℝ := ProbabilityTheory.cdf ν
  have hzero : f.measure ({x} : Set ℝ) = 0 := by
    change (ProbabilityTheory.cdf ν).measure ({x} : Set ℝ) = 0
    rw [ProbabilityTheory.measure_cdf]
    exact measure_singleton x
  have hjump : (f : ℝ → ℝ) x - Function.leftLim (f : ℝ → ℝ) x ≤ 0 := by
    -- Stieltjes measure of a singleton is the jump
    rw [StieltjesFunction.measure_singleton] at hzero
    exact ENNReal.ofReal_eq_zero.mp hzero
  have hxleft : Function.leftLim (f : ℝ → ℝ) x = (f : ℝ → ℝ) x := by
    apply le_antisymm
    · exact f.mono.leftLim_le le_rfl
    · exact sub_nonpos.mp hjump
  have hL : ContinuousWithinAt (f : ℝ → ℝ) (Set.Iio x) x :=
    (Monotone.continuousWithinAt_Iio_iff_leftLim_eq f.mono).2 hxleft
  have hR : ContinuousWithinAt (f : ℝ → ℝ) (Set.Ici x) x :=
    f.right_continuous x
  have hu : ContinuousWithinAt (f : ℝ → ℝ) Set.univ x := by
    simpa [Set.Iio_union_Ici] using hL.union hR
  -- finally remove the bundled notation for the cdf
  have hat : ContinuousAt (f : ℝ → ℝ) x :=
    ((continuousWithinAt_univ (f : ℝ → ℝ) x).1 hu)
  exact hat

-- In particular every level strictly between the two limiting values is a
-- quantile. This weak form (existence only) is frequently the first split in
-- a dyadic tower construction.
lemma exists_cdf_eq_of_mem_unit (ν : Measure ℝ)
    [IsProbabilityMeasure ν] [NoAtoms ν]
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ x : ℝ, (ProbabilityTheory.cdf ν) x = r := by
  have hc : Continuous (fun x : ℝ => (ProbabilityTheory.cdf ν) x) :=
    continuous_cdf_of_noAtoms ν
  have hlo := ProbabilityTheory.tendsto_cdf_atBot ν
  have hhi := ProbabilityTheory.tendsto_cdf_atTop ν
  -- get one point below and one above the requested level by the two limits
  have evlo : ∀ᶠ x : ℝ in Filter.atBot,
      (ProbabilityTheory.cdf ν) x < r := by
    have hop : Set.Iio r ∈ (𝓝 (0 : ℝ)) := Iio_mem_nhds hr0
    exact hlo.eventually hop
  have evhi : ∀ᶠ x : ℝ in Filter.atTop,
      r < (ProbabilityTheory.cdf ν) x := by
    have hop : Set.Ioi r ∈ (𝓝 (1 : ℝ)) := Ioi_mem_nhds hr1
    exact hhi.eventually hop
  obtain ⟨a₀, ha₀⟩ := (Filter.eventually_atBot.1 evlo)
  obtain ⟨b₀, hb₀⟩ := (Filter.eventually_atTop.1 evhi)
  have ha : (ProbabilityTheory.cdf ν) a₀ < r := ha₀ a₀ le_rfl
  have hb : r < (ProbabilityTheory.cdf ν) b₀ := hb₀ b₀ le_rfl
  let a : ℝ := a₀
  let b : ℝ := b₀
  change (ProbabilityTheory.cdf ν) a < r at ha
  change r < (ProbabilityTheory.cdf ν) b at hb
  have hab : a ≤ b := by
    by_contra hn
    have hba : b ≤ a := le_of_lt (lt_of_not_ge hn)
    have hmono := ProbabilityTheory.monotone_cdf ν hba
    linarith
  have hsub := intermediate_value_Icc (α := ℝ) (δ := ℝ) hab
    (hc.continuousOn)
  have hmem : r ∈ Set.Icc ((ProbabilityTheory.cdf ν) a)
      ((ProbabilityTheory.cdf ν) b) := ⟨le_of_lt ha, le_of_lt hb⟩
  have := hsub hmem
  rcases this with ⟨x, hx, hxval⟩
  exact ⟨x, hxval⟩

-- Thus an atom-free real distribution admits a measurable half (and more
-- generally any strictly intermediate mass) as a lower interval. No quotient
-- by null sets is involved in this split.
lemma exists_Iic_measure_of_level (ν : Measure ℝ)
    [IsProbabilityMeasure ν] [NoAtoms ν]
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ x : ℝ, ν (Set.Iic x) = ENNReal.ofReal r := by
  obtain ⟨x, hx⟩ := exists_cdf_eq_of_mem_unit ν hr0 hr1
  refine ⟨x, ?_⟩
  rw [← ProbabilityTheory.ofReal_cdf ν x, hx]



-- The same quantile argument may be run inside any measurable positive
-- piece on the real line, by normalizing its restricted measure. This is the
-- elementary splitting operation needed to refine finite partitions.
lemma exists_measurable_part_inside_real (ν : Measure ℝ)
    [IsProbabilityMeasure ν] [NoAtoms ν]
    (C : Set ℝ) (hC : MeasurableSet C) (hp : 0 < ν C)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ D : Set ℝ, MeasurableSet D ∧ D ⊆ C ∧
      ν D = ν C * ENNReal.ofReal r := by
  let μ' : Measure ℝ := (ν C)⁻¹ • (ν.restrict C)
  have hne0 : ν C ≠ 0 := ne_of_gt hp
  have hnetop : ν C ≠ (⊤ : ENNReal) := measure_ne_top ν C
  letI hμp : IsProbabilityMeasure μ' := by
    constructor
    -- simplification leaves exactly `a⁻¹*a`
    simp [μ', Measure.smul_apply, smul_eq_mul, Measure.restrict_apply,
      ENNReal.inv_mul_cancel hne0 hnetop]
  letI hμa : NoAtoms μ' := by
    constructor
    intro x
    change ((ν C)⁻¹ • (ν.restrict C)) ({x} : Set ℝ) = 0
    simp only [Measure.smul_apply, smul_eq_mul]
    -- the restricted measure still vanishes on points
    have hx : (ν.restrict C) ({x} : Set ℝ) = 0 := measure_singleton x
    simp [hx]
  obtain ⟨x, hx⟩ := exists_Iic_measure_of_level μ' hr0 hr1
  refine ⟨Set.Iic x ∩ C, measurableSet_Iic.inter hC,
    Set.inter_subset_right, ?_⟩
  have hscaled : (ν C)⁻¹ * ν (Set.Iic x ∩ C) =
      ENNReal.ofReal r := by
    simpa [μ', Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply measurableSet_Iic] using hx
  calc
    ν (Set.Iic x ∩ C) =
        ν C * ((ν C)⁻¹ * ν (Set.Iic x ∩ C)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hne0 hnetop]
          simp
    _ = ν C * ENNReal.ofReal r := by rw [hscaled]


lemma exists_measurable_half_inside_real (ν : Measure ℝ)
    [IsProbabilityMeasure ν] [NoAtoms ν]
    (C : Set ℝ) (hC : MeasurableSet C) (hp : 0 < ν C) :
    ∃ D : Set ℝ, MeasurableSet D ∧ D ⊆ C ∧
      ν D = ν C * ENNReal.ofReal (1 / 2 : ℝ) := by
  let μ' : Measure ℝ := (ν C)⁻¹ • (ν.restrict C)
  have hne0 : ν C ≠ 0 := ne_of_gt hp
  have hnetop : ν C ≠ (⊤ : ENNReal) := measure_ne_top ν C
  letI hμp : IsProbabilityMeasure μ' := by
    constructor
    -- simplification leaves exactly `a⁻¹*a`
    simp [μ', Measure.smul_apply, smul_eq_mul, Measure.restrict_apply,
      ENNReal.inv_mul_cancel hne0 hnetop]
  letI hμa : NoAtoms μ' := by
    constructor
    intro x
    change ((ν C)⁻¹ • (ν.restrict C)) ({x} : Set ℝ) = 0
    simp only [Measure.smul_apply, smul_eq_mul]
    -- the restricted measure still vanishes on points
    have hx : (ν.restrict C) ({x} : Set ℝ) = 0 := measure_singleton x
    simp [hx]
  have hr0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨x, hx⟩ := exists_Iic_measure_of_level μ' hr0 hr1
  refine ⟨Set.Iic x ∩ C, measurableSet_Iic.inter hC,
    Set.inter_subset_right, ?_⟩
  have hscaled : (ν C)⁻¹ * ν (Set.Iic x ∩ C) =
      ENNReal.ofReal (1 / 2 : ℝ) := by
    simpa [μ', Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply measurableSet_Iic] using hx
  calc
    ν (Set.Iic x ∩ C) =
        ν C * ((ν C)⁻¹ * ν (Set.Iic x ∩ C)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hne0 hnetop]
          simp
    _ = ν C * ENNReal.ofReal (1 / 2 : ℝ) := by rw [hscaled]


lemma exists_measurable_part_inside_standard
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    (C : Set X) (hC : MeasurableSet C) (hp : 0 < m C)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ D : Set X, MeasurableSet D ∧ D ⊆ C ∧
      m D = m C * ENNReal.ofReal r := by
  classical
  let e : X ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable
    (not_countable_of_noAtoms_prob m) (not_countable : ¬ Countable ℝ)
  let ν : Measure ℝ := Measure.map (e : X → ℝ) m
  letI hνp : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  letI hνa : NoAtoms ν := noAtoms_map_measurableEquiv m e
  have he : MeasurePreserving (e : X → ℝ) m ν :=
    e.measurable.measurePreserving m
  have himg : m C = ν (e '' C) :=
    transport_measure_image m ν e he C
  have hp' : 0 < ν (e '' C) := by rw [← himg]; exact hp
  obtain ⟨E, hE, hEC, hmass⟩ :=
    exists_measurable_part_inside_real ν (e '' C)
      (e.measurableEmbedding.measurableSet_image' hC) hp' hr0 hr1
  refine ⟨(e : X → ℝ) ⁻¹' E, e.measurable hE, ?_, ?_⟩
  · intro z hz
    have : e z ∈ e '' C := hEC hz
    rcases this with ⟨w, hw, heq⟩
    exact e.injective heq ▸ hw
  · have hback : m ((e : X → ℝ) ⁻¹' E) = ν E :=
      he.measure_preimage_emb e.measurableEmbedding E
    rw [hback, hmass, himg]



-- Iterating the preceding splitting operation produces *exact* equal finite
-- partitions inside any positive measurable piece. This is a useful combinatorial
-- prerequisite for a Rokhlin/cutting-and-stacking approximation. Notice that the
-- statement is about actual Borel sets, not classes modulo null; it can therefore
-- be used with the bundled measurable equivalences of `Automorphism`.
lemma exists_equal_partition_inside_standard
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    (k : ℕ) (C : Set X) (hC : MeasurableSet C) (hp : 0 < m C) :
    ∃ P : Fin (k+1) → Set X,
        (∀ i, MeasurableSet (P i)) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (⋃ i, P i) = C ∧
        (∀ i, m (P i) = m C * ENNReal.ofReal (1 / ((k+1:ℕ):ℝ))) := by
  classical
  refine HalmosSupport.equal_partition_of_splittable (m := m) ?_ k C hC hp
  intro E hE hpos r h0 h1
  exact exists_measurable_part_inside_standard m E hE hpos h0 h1

-- A convenient specialization is a partition of the entire space. In the
-- induction above the mass is stated as `m C * _`; here the probability
-- normalization simplifies it to the advertised reciprocal.
lemma exists_equal_partition_standard
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    (k : ℕ) :
    ∃ P : Fin (k+1) → Set X,
        (∀ i, MeasurableSet (P i)) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (⋃ i, P i) = (Set.univ : Set X) ∧
        (∀ i, m (P i) = ENNReal.ofReal (1 / ((k+1:ℕ):ℝ))) := by
  classical
  have hp : 0 < m (Set.univ : Set X) := by simp
  obtain ⟨P, hP, hdis, hU, hmass⟩ :=
    exists_equal_partition_inside_standard m k Set.univ MeasurableSet.univ hp
  refine ⟨P, hP, hdis, hU, ?_⟩
  intro i
  simpa using (hmass i)

-- For a finite family of measurable test sets it is helpful to replace it by
-- its finite Boolean partition. Each test is then literally a union of atoms.
-- This exact/set-level fact precedes any measure estimates.
lemma finite_boolean_atoms
    {X : Type*} [MeasurableSpace X]
    (n : ℕ) (A : Fin n → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    let cell : Set (Fin n) → Set X := fun s => HalmosSupport.boolCell A s
    (∀ s, MeasurableSet (cell s)) ∧
    (∀ s t, s ≠ t → Disjoint (cell s) (cell t)) ∧
    (⋃ s : Set (Fin n), cell s) = Set.univ ∧
    (∀ i, (⋃ s : {s : Set (Fin n) // i ∈ s}, cell s.1) = A i) := by
  classical
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun s => HalmosSupport.measurableSet_boolCell hA s
  · exact fun s t hst => HalmosSupport.boolCell_disjoint hst
  · exact HalmosSupport.union_boolCell A
  · exact fun i => HalmosSupport.union_boolCell_of_mem A i


-- Positive Boolean cells may in turn be chopped into an arbitrary prescribed
-- number of equal layers. Keeping the positivity proof as an argument in the
-- indexing type means that no claim about null cells (which may still be
-- nonempty Borel sets) is hidden here.
lemma refine_positive_boolean_cells
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    (n k : ℕ) (A : Fin n → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    ∃ Q : (s : Set (Fin n)) → 0 < m (HalmosSupport.boolCell A s) →
          Fin (k+1) → Set X,
      ∀ (s : Set (Fin n)) (hs : 0 < m (HalmosSupport.boolCell A s)),
        (∀ j, MeasurableSet (Q s hs j)) ∧
        (∀ j l, j ≠ l → Disjoint (Q s hs j) (Q s hs l)) ∧
        (⋃ j, Q s hs j) = HalmosSupport.boolCell A s ∧
        (∀ j, m (Q s hs j) = m (HalmosSupport.boolCell A s) *
             ENNReal.ofReal (1 / ((k+1:ℕ):ℝ))) := by
  classical
  have hcell (s : Set (Fin n)) (hs : 0 < m (HalmosSupport.boolCell A s)) :
      ∃ P : Fin (k+1) → Set X,
        (∀ j, MeasurableSet (P j)) ∧
        (∀ j l, j ≠ l → Disjoint (P j) (P l)) ∧
        (⋃ j, P j) = HalmosSupport.boolCell A s ∧
        (∀ j, m (P j) = m (HalmosSupport.boolCell A s) *
             ENNReal.ofReal (1 / ((k+1:ℕ):ℝ))) :=
    exists_equal_partition_inside_standard m k _
      (HalmosSupport.measurableSet_boolCell hA s) hs
  choose P hP using hcell
  exact ⟨P, hP⟩


-- Atomwise errors suffice. This version is often the entry point for a
-- tower construction: one estimates the images of the cells separately,
-- then sums. In particular it removes any need to compare errors on
-- overlapping test sets.
lemma dense_weakMixing_of_boolean_atom_sums
    {X : Type u} [MeasurableSpace X]
    (m : Measure X)
    (hAtom : ∀ (n : ℕ) (T₀ : Automorphism m)
      (A : Fin n → Set X) (ε : Fin n → ℝ),
      (∀ i, MeasurableSet (A i)) → (∀ i, 0 < ε i) →
      ∃ T : Automorphism m, IsWeaklyMixing m T ∧
        ∀ i : Fin n,
          ∑ s ∈ (Finset.univ.filter (fun s : Finset (Fin n) => i ∈ s)),
              m ((T.toEquiv '' (HalmosSupport.boolCell A (↑s : Set (Fin n)))) ∆
                   (T₀.toEquiv '' (HalmosSupport.boolCell A (↑s : Set (Fin n)))))
             < ENNReal.ofReal (ε i)) :
     Dense {T : Automorphism m | IsWeaklyMixing m T} := by
  classical
  apply dense_weakMixing_of_fin_center m
  intro n T₀ A ε hA hε
  obtain ⟨T, hT, hsum⟩ := hAtom n T₀ A ε hA hε
  refine ⟨T, hT, ?_⟩
  intro i
  let ok : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun s : Finset (Fin n) => i ∈ s)
  let cells : Finset (Fin n) → Set X :=
    fun s => HalmosSupport.boolCell A (↑s : Set (Fin n))
  have hU : (⋃ s ∈ ok, cells s) = A i := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨s, hx₁⟩
      rcases Set.mem_iUnion.1 hx₁ with ⟨his, hxc⟩
      have hiS : i ∈ s := (Finset.mem_filter.1 his).2
      exact ((HalmosSupport.mem_boolCell).1 hxc i).2 hiS
    · intro hx
      let s : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => x ∈ A j)
      have hisi : i ∈ s := by simp [s, hx]
      have hsok : s ∈ ok := by simp [ok, hisi]
      apply Set.mem_iUnion.2
      refine ⟨s, Set.mem_iUnion.2 ⟨hsok, ?_⟩⟩
      apply (HalmosSupport.mem_boolCell).2
      intro j
      simp [s]
  have hle := HalmosSupport.measure_symmDiff_image_finUnion_le
      (μ := m) ok cells (T.toEquiv : X → X) (T₀.toEquiv : X → X)
  rw [hU] at hle
  -- the notation in the assumption is the same finite set `ok`.
  have ht : (∑ s ∈ ok,
              m ((T.toEquiv '' cells s) ∆ (T₀.toEquiv '' cells s)))
             < ENNReal.ofReal (ε i) := by
    simpa [ok, cells] using (hsum i)
  exact lt_of_le_of_lt hle ht



lemma dense_weakMixing_of_boolean_atom_uniform
    {X : Type u} [MeasurableSpace X] (m : Measure X)
    (hUniform : ∀ (n : ℕ) (T₀ : Automorphism m)
      (A : Fin n → Set X) (η : ℝ),
      (∀ i, MeasurableSet (A i)) → 0 < η →
      ∃ T : Automorphism m, IsWeaklyMixing m T ∧
        ∀ s : Finset (Fin n),
          m ((T.toEquiv '' (HalmosSupport.boolCell A (↑s : Set (Fin n)))) ∆
             (T₀.toEquiv '' (HalmosSupport.boolCell A (↑s : Set (Fin n))))) <
               ENNReal.ofReal η) :
    Dense {T : Automorphism m | IsWeaklyMixing m T} := by
  classical
  apply dense_weakMixing_of_boolean_atom_sums m
  intro n T₀ A ε hA hε
  by_cases hn : n = 0
  · subst n
    obtain ⟨T,hT,hcl⟩ := hUniform 0 T₀ A 1 hA (by norm_num)
    refine ⟨T,hT,?_⟩
    exact fun i => Fin.elim0 i
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    let i0 : Fin n := ⟨0, hn'⟩
    let vals : Finset ℝ := Finset.univ.image ε
    have hv : vals.Nonempty := by
      refine ⟨ε i0, ?_⟩
      simp [vals]
    let e : ℝ := vals.min' hv
    have hepos : 0 < e := by
      change 0 < vals.min' hv
      have he := vals.min'_mem hv
      rcases Finset.mem_image.1 he with ⟨i, hi, heq⟩
      rw [← heq]
      exact hε i
    have hele (i : Fin n) : e ≤ ε i := by
      exact vals.min'_le _ (by simp [vals])
    let N : ℕ := Fintype.card (Finset (Fin n)) + 1
    have hNpos : (0:ℝ) < N := by
      exact_mod_cast (Nat.zero_lt_succ (Fintype.card (Finset (Fin n))))
    let η : ℝ := e / (N:ℝ)
    have hη : 0 < η := div_pos hepos hNpos
    obtain ⟨T,hT,hclose⟩ := hUniform n T₀ A η hA hη
    refine ⟨T,hT,?_⟩
    intro i
    let F : Finset (Finset (Fin n)) :=
      Finset.univ.filter (fun s : Finset (Fin n) => i ∈ s)
    let term : Finset (Fin n) → ENNReal := fun s =>
      m ((T.toEquiv '' (HalmosSupport.boolCell A (↑s : Set (Fin n)))) ∆
         (T₀.toEquiv '' (HalmosSupport.boolCell A (↑s : Set (Fin n)))))
    have hsle : (∑ s ∈ F, term s) ≤ F.card • ENNReal.ofReal η :=
      Finset.sum_le_card_nsmul F term (ENNReal.ofReal η)
        (fun j hj => le_of_lt (hclose j))
    have hcardnat : F.card < N := by
      have hsub : F ⊆ (Finset.univ : Finset (Finset (Fin n))) :=
        fun j hj => Finset.mem_univ j
      have hc := Finset.card_le_card hsub
      dsimp [N]
      exact lt_of_le_of_lt hc (Nat.lt_succ_self _)
    have hcard : (F.card : ℝ) < (N:ℝ) := by exact_mod_cast hcardnat
    have hreal : (F.card : ℝ) * η < ε i := by
      have hx : (F.card : ℝ) * η < e := by
        dsimp [η]
        have hh : (F.card : ℝ) * e / (N:ℝ) < e :=
          (div_lt_iff₀ hNpos).2 (by nlinarith [hepos, hcard])
        convert hh using 1 <;> ring
      exact lt_of_lt_of_le hx (hele i)
    have hsum' : F.card • ENNReal.ofReal η < ENNReal.ofReal (ε i) := by
      have hf : F.card • ENNReal.ofReal η =
          ENNReal.ofReal ((F.card : ℝ) * η) := by
        simp [ENNReal.ofReal_mul (show (0:ℝ) ≤ (F.card:ℝ) by positivity)]
      rw [hf]
      exact (ENNReal.ofReal_lt_ofReal_iff (by exact hε i)).2 hreal
    change (∑ s ∈ F, term s) < ENNReal.ofReal (ε i)
    exact lt_of_le_of_lt hsle hsum'


lemma exists_measurable_half_inside_standard
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m]
    (C : Set X) (hC : MeasurableSet C) (hp : 0 < m C) :
    ∃ D : Set X, MeasurableSet D ∧ D ⊆ C ∧
      m D = m C * ENNReal.ofReal (1 / 2 : ℝ) := by
  classical
  let e : X ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable
    (not_countable_of_noAtoms_prob m) (not_countable : ¬ Countable ℝ)
  let ν : Measure ℝ := Measure.map (e : X → ℝ) m
  letI hνp : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  letI hνa : NoAtoms ν := noAtoms_map_measurableEquiv m e
  have he : MeasurePreserving (e : X → ℝ) m ν :=
    e.measurable.measurePreserving m
  have himg : m C = ν (e '' C) :=
    transport_measure_image m ν e he C
  have hp' : 0 < ν (e '' C) := by rw [← himg]; exact hp
  obtain ⟨E, hE, hEC, hmass⟩ :=
    exists_measurable_half_inside_real ν (e '' C)
      (e.measurableEmbedding.measurableSet_image' hC) hp'
  refine ⟨(e : X → ℝ) ⁻¹' E, e.measurable hE, ?_, ?_⟩
  · intro z hz
    have : e z ∈ e '' C := hEC hz
    rcases this with ⟨w, hw, heq⟩
    exact e.injective heq ▸ hw
  · have hback : m ((e : X → ℝ) ⁻¹' E) = ν E :=
      he.measure_preimage_emb e.measurableEmbedding E
    rw [hback, hmass, himg]

lemma exists_measurable_half_standard
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m] :
    ∃ E : Set X, MeasurableSet E ∧ m E = ENNReal.ofReal (1 / 2 : ℝ) := by
  classical
  let e : X ≃ᵐ ℝ :=
    PolishSpace.measurableEquivOfNotCountable
      (not_countable_of_noAtoms_prob m) (not_countable : ¬ Countable ℝ)
  let ν : Measure ℝ := Measure.map (e : X → ℝ) m
  letI hνp : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  letI hνa : NoAtoms ν := noAtoms_map_measurableEquiv m e
  have hr0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨x, hx⟩ := exists_Iic_measure_of_level ν hr0 hr1
  refine ⟨(e : X → ℝ) ⁻¹' Set.Iic x,
    e.measurable (measurableSet_Iic), ?_⟩
  -- `ν` was the map along a measurable equivalence, whose `map_apply`
  -- has no null-measurability side condition.
  have hmap : ν (Set.Iic x) =
      m ((e : X → ℝ) ⁻¹' Set.Iic x) :=
    MeasurableEquiv.map_apply e (Set.Iic x)
  simpa [hmap] using hx

-- Weak mixing forces the zero-one law on strictly invariant measurable sets.
lemma weakMixing_ergodic_aux (m : Measure X) [IsProbabilityMeasure m]
    (T : Automorphism m) (hwm : IsWeaklyMixing m T) :
    Ergodic (T.toEquiv : X → X) m := by
  refine { toMeasurePreserving := T.measurePreserving,
           toPreErgodic := ?_ }
  refine ⟨?_⟩
  intro s hs h_inv
  -- On an invariant set all the summands in the defining average are the same.
  let a : ℝ := (m s).toReal
  let c : ℝ := |a - a * a|
  have h_iter (k : ℕ) :
      (T.toEquiv : X → X)^[k] ⁻¹' s = s :=
    Function.IsFixedPt.preimage_iterate h_inv k
  have h_ev :
      (fun n : ℕ =>
        (∑ k ∈ Finset.range n,
          |(m ((T.toEquiv : X → X)^[k] ⁻¹' s ∩ s)).toReal -
            (m s).toReal * (m s).toReal|) / (n : ℝ))
        =ᶠ[atTop] (fun _ : ℕ => c) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hterm (k : ℕ) :
        |(m ((T.toEquiv : X → X)^[k] ⁻¹' s ∩ s)).toReal -
          (m s).toReal * (m s).toReal| = c := by
      rw [h_iter k]
      simp [a, c]
    -- The sum of a constant over `range n` is `n` times that constant.
    calc
      (∑ k ∈ Finset.range n,
          |(m ((T.toEquiv : X → X)^[k] ⁻¹' s ∩ s)).toReal -
            (m s).toReal * (m s).toReal|) / (n : ℝ)
          = (∑ _k ∈ Finset.range n, c) / (n : ℝ) := by
              congr 1
              apply Finset.sum_congr rfl
              intro k hk
              simp [hterm k]
      _ = c := by
        simp [hn0]
  have hlim0 : Tendsto
      (fun n : ℕ =>
        (∑ k ∈ Finset.range n,
          |(m ((T.toEquiv : X → X)^[k] ⁻¹' s ∩ s)).toReal -
            (m s).toReal * (m s).toReal|) / (n : ℝ))
      atTop (𝓝 0) := hwm s s hs hs
  have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_congr' h_ev).1 hlim0
  have hc : c = 0 := (tendsto_const_nhds_iff.mp hconst)
  have ha' : a - a * a = 0 := abs_eq_zero.mp (by simpa [c] using hc)
  have ha0or1 : a = 0 ∨ a = 1 := by
    have hfac : a * (1 - a) = 0 := by nlinarith [ha']
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact Or.inl h0
    · right
      nlinarith
  apply eventuallyConst_set'.2
  rcases ha0or1 with h0 | h1
  · left
    apply ae_eq_empty.mpr
    have hzr : (m s).toReal = 0 := by simpa [a] using h0
    exact (ENNReal.toReal_eq_zero_iff _).1 hzr |>.resolve_right (measure_ne_top m s)
  · right
    apply ae_eq_univ.mpr
    have hzr : (m s).toReal = 1 := by simpa [a] using h1
    have hone : m s = 1 := (ENNReal.toReal_eq_one_iff _).1 hzr
    rw [measure_compl hs (measure_ne_top m s)]
    simp [hone]


-- A pointwise (strong) mixing statement is more than is needed in the
-- definition.  Recording the elementary Cesaro step separately is useful
-- when constructing examples: one only has to prove convergence of the
-- individual correlations.  This is exactly `Filter.Tendsto.cesaro` applied
-- after absolute value.
lemma weakMixing_of_strong (m : Measure X) (T : Automorphism m)
    (hstrong : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun k : ℕ =>
        (m ((T.toEquiv : X → X)^[k] ⁻¹' A ∩ B)).toReal -
          (m A).toReal * (m B).toReal) atTop (𝓝 (0 : ℝ))) :
    IsWeaklyMixing m T := by
  intro A B hA hB
  have h := hstrong A B hA hB
  have habs : Tendsto
      (fun k : ℕ =>
        |(m ((T.toEquiv : X → X)^[k] ⁻¹' A ∩ B)).toReal -
          (m A).toReal * (m B).toReal|) atTop (𝓝 (0 : ℝ)) := by
    simpa using (h.abs)
  have hc := Filter.Tendsto.cesaro habs
  -- the definitional average in `IsWeaklyMixing` writes division on the
  -- right rather than an inverse on the left
  simpa [div_eq_mul_inv, mul_comm] using hc

-- Exact finite-time independence on an algebra of tests immediately gives
-- the required convergence for those tests.  This tiny lemma is handy for the
-- Bernoulli-shift construction: far-apart cylinders are independent, hence
-- their correlations are eventually literally zero.
lemma tendsto_zero_of_eventually_eq_zero {u : ℕ → ℝ}
    (h : ∀ᶠ n in atTop, u n = 0) : Tendsto u atTop (𝓝 (0 : ℝ)) := by
  exact (tendsto_congr' (by
    filter_upwards [h] with n hn
    exact hn)).2 tendsto_const_nhds


-- Extension from an algebra of finite tests.  On a probability space the
-- distance between two events is the measure of their symmetric difference.
-- Consequently an *eventually exact* independence calculation on a set ring
-- generating the sigma algebra already implies strong mixing for all
-- measurable events.  This is a useful interface to product/cylinder
-- constructions; it keeps the analytic approximation out of the symbolic
-- shift calculation.
lemma strong_of_setRing_eventually_independent
    {Y : Type*} [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : Y → Y) (hf : MeasurePreserving f μ μ)
    (C : Set (Set Y)) (hC : IsSetRing C)
    (hcover : ∃ D : Set (Set Y), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0)
    (hgen : mY = MeasurableSpace.generateFrom C)
    (hevent : ∀ P ∈ C, ∀ Q ∈ C, ∃ N : ℕ, ∀ k ≥ N,
       μ (f^[k] ⁻¹' P ∩ Q) = μ P * μ Q) :
    ∀ A B : Set Y, MeasurableSet A → MeasurableSet B →
      Tendsto (fun k : ℕ =>
        (μ (f^[k] ⁻¹' A ∩ B)).toReal -
          (μ A).toReal * (μ B).toReal) atTop (𝓝 (0 : ℝ)) := by
  classical
  intro A B hA hB
  apply (Metric.tendsto_atTop).2
  intro eps heps
  -- take much smaller algebraic approximants; four errors below have plenty
  -- of room, which avoids any optimization of constants
  let δ : ℝ := eps / 10
  have hδ : 0 < δ := div_pos heps (by norm_num)
  obtain ⟨P, hPC, hPerr⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := μ) hC hcover hgen hA (ε := ENNReal.ofReal δ)
        (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨Q, hQC, hQerr⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := μ) hC hcover hgen hB (ε := ENNReal.ofReal δ)
        (ENNReal.ofReal_pos.2 hδ)
  have hPm : MeasurableSet P := by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hPC
  have hQm : MeasurableSet Q := by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hQC
  have hPr : μ.real (P ∆ A) < δ := by
    exact ENNReal.toReal_lt_of_lt_ofReal hPerr
  have hQr : μ.real (Q ∆ B) < δ := by
    exact ENNReal.toReal_lt_of_lt_ofReal hQerr
  obtain ⟨N, hN⟩ := hevent P hPC Q hQC
  refine ⟨N, ?_⟩
  intro k hk
  let U : Set Y := f^[k] ⁻¹' A ∩ B
  let V : Set Y := f^[k] ⁻¹' P ∩ Q
  have hfm : MeasurePreserving (f^[k]) μ μ := hf.iterate k
  have hUm : MeasurableSet U := (hfm.measurable hA).inter hB
  have hVm : MeasurableSet V := (hfm.measurable hPm).inter hQm
  have hsub : U ∆ V ⊆ (f^[k] ⁻¹' (P ∆ A)) ∪ (Q ∆ B) := by
    intro x hx
    -- this is just the Boolean inequality for intersections
    dsimp [U, V] at hx
    simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_union] at hx ⊢
    tauto
  have hpre : μ.real (f^[k] ⁻¹' (P ∆ A)) = μ.real (P ∆ A) := by
    have h := hfm.measure_preimage ( (hPm.symmDiff hA).nullMeasurableSet )
    -- `.real` here is just `toReal`
    exact congrArg ENNReal.toReal h
  have hUVreal : μ.real (U ∆ V) < 2 * δ := by
    calc
      μ.real (U ∆ V)
          ≤ μ.real ((f^[k] ⁻¹' (P ∆ A)) ∪ (Q ∆ B)) :=
              measureReal_mono hsub
      _ ≤ μ.real (f^[k] ⁻¹' (P ∆ A)) + μ.real (Q ∆ B) :=
              measureReal_union_le _ _
      _ < 2 * δ := by rw [hpre]; linarith
  have hUV : |μ.real U - μ.real V| < 2 * δ :=
    lt_of_le_of_lt
      (abs_measureReal_sub_le_measureReal_symmDiff hUm.nullMeasurableSet
        hVm.nullMeasurableSet) hUVreal
  have habP : |μ.real A - μ.real P| < δ := by
    have hbase := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := μ) hA.nullMeasurableSet hPm.nullMeasurableSet
    have hEq : μ.real (A ∆ P) = μ.real (P ∆ A) := by
      rw [symmDiff_comm]
    exact lt_of_le_of_lt hbase (by simpa [hEq] using hPr)
  have hbbQ : |μ.real B - μ.real Q| < δ := by
    have hbase := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := μ) hB.nullMeasurableSet hQm.nullMeasurableSet
    have hEq : μ.real (B ∆ Q) = μ.real (Q ∆ B) := by rw [symmDiff_comm]
    exact lt_of_le_of_lt hbase (by simpa [hEq] using hQr)
  -- all event probabilities lie in `[0,1]`
  have hprob (S : Set Y) : 0 ≤ μ.real S ∧ μ.real S ≤ 1 := by
    constructor
    · exact ENNReal.toReal_nonneg
    · have hle : μ S ≤ (1 : ENNReal) := prob_le_one
      simpa [Measure.real] using (ENNReal.toReal_mono (by simp : (1:ENNReal) ≠ ⊤) hle)
  have hp := hprob P
  have hq := hprob B
  have hprod : |μ.real A * μ.real B - μ.real P * μ.real Q| < 2 * δ := by
    calc
      |μ.real A * μ.real B - μ.real P * μ.real Q|
          = |(μ.real A - μ.real P) * μ.real B +
                μ.real P * (μ.real B - μ.real Q)| := by ring_nf
      _ ≤ |μ.real A - μ.real P| * |μ.real B| +
            |μ.real P| * |μ.real B - μ.real Q| := by
              simpa [abs_mul] using
                (abs_add_le ((μ.real A - μ.real P) * μ.real B)
                  (μ.real P * (μ.real B - μ.real Q)))
      _ < 2 * δ := by
        rw [abs_of_nonneg hq.1, abs_of_nonneg hp.1]
        have h1 : |μ.real A - μ.real P| * μ.real B < δ := by
          nlinarith [habP, abs_nonneg (μ.real A - μ.real P)]
        have h2 : μ.real P * |μ.real B - μ.real Q| < δ := by
          nlinarith [hbbQ, abs_nonneg (μ.real B - μ.real Q)]
        linarith
  have hVe : μ.real V = (μ P * μ Q).toReal := by
    dsimp [V]
    unfold Measure.real
    rw [hN k hk]
  have htopP : μ P ≠ (⊤ : ENNReal) := measure_ne_top μ P
  have htopQ : μ Q ≠ (⊤ : ENNReal) := measure_ne_top μ Q
  have hVe' : μ.real V = μ.real P * μ.real Q := by
    rw [hVe]
    exact ENNReal.toReal_mul
  -- triangle inequality for the two error contributions
  have herr :
      |(μ.real U - μ.real A * μ.real B)| < eps := by
    have htri : |μ.real U - μ.real A * μ.real B| ≤
        |μ.real U - μ.real V| +
        |μ.real P * μ.real Q - μ.real A * μ.real B| := by
      calc
        |μ.real U - μ.real A * μ.real B| =
            |(μ.real U - μ.real V) +
              (μ.real V - μ.real A * μ.real B)| := by
                congr 1 <;> ring
        _ ≤ |μ.real U - μ.real V| +
              |μ.real V - μ.real A * μ.real B| :=
                abs_add_le _ _
        _ = _ := by rw [hVe']

    have hs : |μ.real P * μ.real Q - μ.real A * μ.real B| < 2 * δ := by
      simpa [abs_sub_comm] using hprod
    have : |μ.real U - μ.real V| +
          |μ.real P * μ.real Q - μ.real A * μ.real B| < eps := by
      dsimp [δ] at hUV hs ⊢
      linarith
    exact lt_of_le_of_lt htri this
  -- `dist x 0` is absolute value on the real line
  simpa [Real.dist_eq, U, Measure.real] using herr



-- Independence of two blocks of coordinates in the infinite product.  It is
-- occasionally convenient to use arbitrary measurable subsets of the finite
-- coordinate tuple rather than boxes; `iIndepFun.indepFun_finset` gives
-- exactly that formulation.
lemma infinitePi_cylinders_indep
    {ι : Type*} {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (p : (i : ι) → Measure (Z i)) [∀ i, IsProbabilityMeasure (p i)]
    {I J : Finset ι} (hIJ : Disjoint I J)
    {S : Set (∀ i : (↥I), Z i)} {R : Set (∀ j : (↥J), Z j)}
    (hS : MeasurableSet S) (hR : MeasurableSet R) :
    (Measure.infinitePi p) (cylinder I S ∩ cylinder J R) =
      (Measure.infinitePi p) (cylinder I S) *
        (Measure.infinitePi p) (cylinder J R) := by
  classical
  have hind : ProbabilityTheory.iIndepFun
      (fun i (w : (∀ i, Z i)) => w i) (Measure.infinitePi p) :=
    ProbabilityTheory.iIndepFun_infinitePi (P := p)
      (X := fun i (z : Z i) => z) (fun i => measurable_id)
  have hpair := ProbabilityTheory.iIndepFun.indepFun_finset I J hIJ hind
      (fun i => measurable_pi_apply i)
  have hcalc := ProbabilityTheory.IndepFun.measure_inter_preimage_eq_mul
        hpair S R hS hR
  exact hcalc


-- left translation of the integer coordinates.  Choosing `n ↦ n-1` as
-- the reindexing equivalence makes `piCongrLeft` act by `w n ↦ w (n+1)`.
def intSubOneEquiv : ℤ ≃ ℤ where
  toFun n := n - 1
  invFun n := n + 1
  left_inv n := by
    change n - 1 + 1 = n
    omega
  right_inv n := by
    change n + 1 - 1 = n
    omega

@[simp] lemma intSubOneEquiv_apply (n : ℤ) : intSubOneEquiv n = n - 1 := rfl
@[simp] lemma intSubOneEquiv_symm_apply (n : ℤ) : intSubOneEquiv.symm n = n + 1 := rfl

noncomputable def intShiftMeasurableEquiv
    (V : Type*) [MeasurableSpace V] :
    (ℤ → V) ≃ᵐ (ℤ → V) :=
  MeasurableEquiv.piCongrLeft (fun _ : ℤ => V) intSubOneEquiv

@[simp] lemma intShiftMeasurableEquiv_apply
    (V : Type*) [MeasurableSpace V] (w : ℤ → V) (n : ℤ) :
    intShiftMeasurableEquiv V w n = w (n + 1) := by
  change (MeasurableEquiv.piCongrLeft (fun _ : ℤ => V)
       intSubOneEquiv) w n = _
  have h := MeasurableEquiv.piCongrLeft_apply_apply
      intSubOneEquiv (β := fun _ : ℤ => V) w (intSubOneEquiv.symm n)
  simpa using h

noncomputable def intShiftAutomorphism
    (V : Type*) [MeasurableSpace V] (p : Measure V)
    [IsProbabilityMeasure p] :
    Automorphism (Measure.infinitePi (fun _ : ℤ => p)) where
  toEquiv := intShiftMeasurableEquiv V
  measurePreserving := by
    refine ⟨?_, ?_⟩
    · exact (intShiftMeasurableEquiv V).measurable
    · simpa [intShiftMeasurableEquiv] using
        (Measure.infinitePi_map_piCongrLeft
          (μ := fun _ : ℤ => p) intSubOneEquiv)

-- coordinates of an iterate of the shift
lemma intShift_iterate
    (V : Type*) [MeasurableSpace V] (p : Measure V)
    [IsProbabilityMeasure p]
    (k : ℕ) (w : ℤ → V) (n : ℤ) :
    (((intShiftAutomorphism V p).toEquiv : (ℤ → V) → (ℤ → V))^[k] w) n =
       w (n + (k : ℤ)) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      -- new step is outside
      change _ = _
      change intShiftMeasurableEquiv V _ n = _
      rw [intShiftMeasurableEquiv_apply]
      rw [ih]
      congr 1
      push_cast
      ring


-- A pair of finite blocks of integer coordinates separate after enough
-- translates.  Stating the bound with a sum of `natAbs` avoids choosing extrema
-- of an empty block.
lemma int_finset_eventually_disjoint (I J : Finset ℤ) :
    ∃ N : ℕ, ∀ k ≥ N,
      Disjoint (I.image (fun i : ℤ => i + (k : ℤ))) J := by
  classical
  let N : ℕ := (∑ i ∈ I, i.natAbs) + (∑ j ∈ J, j.natAbs) + 1
  refine ⟨N, ?_⟩
  intro k hk
  apply Finset.disjoint_left.2
  intro a haI haJ
  rcases Finset.mem_image.1 haI with ⟨i, hi, rfl⟩
  have hiabs : i.natAbs ≤ ∑ t ∈ I, t.natAbs := by
    exact Finset.single_le_sum (fun t ht => Nat.zero_le _) hi
  have hjabs : (i + (k:ℤ)).natAbs ≤ ∑ t ∈ J, t.natAbs := by
    exact Finset.single_le_sum (fun t ht => Nat.zero_le _) haJ
  have hi_low : -(i.natAbs : ℤ) ≤ i := by
    have hh : (-i) ≤ (i.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -i))
    omega
  have hj_up : i + (k:ℤ) ≤ ((i + (k:ℤ)).natAbs : ℤ) :=
    Int.le_natAbs
  have hcast_i : (i.natAbs : ℤ) ≤
        ((∑ t ∈ I, t.natAbs) : ℤ) := by exact_mod_cast hiabs
  have hcast_j : ((i + (k:ℤ)).natAbs : ℤ) ≤
        ((∑ t ∈ J, t.natAbs) : ℤ) := by exact_mod_cast hjabs
  have hcastk : (N : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  dsimp [N] at hcastk
  push_cast at hcastk
  omega

-- Cylinders form a set ring generating the product sigma algebra.  Combining
-- the preceding extension lemma with this fact isolates the only symbolic
-- work for a Bernoulli shift: checking eventual independence of two finite
-- cylinders.
lemma weakMixing_of_cylinder_eventual
    {ι : Type*} {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (μ : Measure (∀ i, Z i)) [IsProbabilityMeasure μ]
    (T : Automorphism μ)
    (hev : ∀ P ∈ (measurableCylinders Z),
           ∀ Q ∈ (measurableCylinders Z),
             ∃ N : ℕ, ∀ k ≥ N,
               μ ((T.toEquiv : (∀ i, Z i) → (∀ i, Z i))^[k] ⁻¹' P ∩ Q)
                 = μ P * μ Q) :
    IsWeaklyMixing μ T := by
  classical
  apply weakMixing_of_strong μ T
  let C : Set (Set (∀ i, Z i)) := measurableCylinders Z
  have hring : IsSetRing C := isSetRing_measurableCylinders
  have hcov : ∃ D : Set (Set (∀ i, Z i)), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · intro U hU
      have hu : U = (Set.univ : Set (∀ i, Z i)) := (Set.mem_singleton_iff.mp hU)
      simpa [C, hu] using (univ_mem_measurableCylinders Z)
    · simp
  have hgen : (inferInstance : MeasurableSpace (∀ i, Z i)) =
        MeasurableSpace.generateFrom C := by
    have h := generateFrom_measurableCylinders (α := Z)
    -- the product measurable space is the instance on a dependent function
    exact h.symm
  exact strong_of_setRing_eventually_independent μ
    (T.toEquiv : (∀ i, Z i) → (∀ i, Z i)) T.measurePreserving
      C hring hcov hgen hev


-- The bilateral Bernoulli shift is weakly mixing.  The point of using
-- the two-sided product is that its left shift is a genuine measurable
-- equivalence (and not merely an endomorphism).  We first describe exactly
-- what happens to a finite cylinder under an iterate.  The base of the pulled
-- back cylinder is a pullback along a finite-coordinate relabelling; this
-- works for arbitrary measurable bases, not just for product rectangles.
lemma intShift_cylinder_eventual
    (V : Type*) [MeasurableSpace V] (p : Measure V)
    [IsProbabilityMeasure p] :
    ∀ P ∈ measurableCylinders (fun _ : ℤ => V),
      ∀ Q ∈ measurableCylinders (fun _ : ℤ => V),
        ∃ N : ℕ, ∀ k ≥ N,
          (Measure.infinitePi (fun _ : ℤ => p))
              ((((intShiftAutomorphism V p).toEquiv :
                   (ℤ → V) → (ℤ → V))^[k] ⁻¹' P) ∩ Q) =
            (Measure.infinitePi (fun _ : ℤ => p)) P *
              (Measure.infinitePi (fun _ : ℤ => p)) Q := by
  classical
  intro P hP Q hQ
  rcases (mem_measurableCylinders P).1 hP with ⟨I, S, hS, rfl⟩
  rcases (mem_measurableCylinders Q).1 hQ with ⟨J, R, hR, rfl⟩
  obtain ⟨N, hN⟩ := int_finset_eventually_disjoint I J
  refine ⟨N, ?_⟩
  intro k hk
  let g : ℤ → ℤ := fun i => i + (k : ℤ)
  have hg : Function.Injective g := by
    intro a b hab
    dsimp [g] at hab
    linarith
  let I' : Finset ℤ := I.image g
  have hgood : Disjoint I' J := by
    simpa [I', g] using hN k hk
  -- restriction to the old block, viewed as a map from the translated block
  let phi : (∀ j : (↥I'), V) → (∀ i : (↥I), V) :=
    fun w i => w ⟨g (i : ℤ), (by
      -- every translated index belongs to the image
      dsimp [I']
      exact Finset.mem_image.2 ⟨(i:ℤ), i.property, rfl⟩)⟩
  have hphi : Measurable phi := by
    -- all finite-coordinate evaluation maps are measurable
    unfold phi
    fun_prop
  let S' : Set (∀ j : (↥I'), V) := phi ⁻¹' S
  have hS' : MeasurableSet S' := hphi hS
  have hpre :
      ((((intShiftAutomorphism V p).toEquiv :
          (ℤ → V) → (ℤ → V))^[k] ⁻¹' cylinder I S)) =
        cylinder I' S' := by
    ext w
    -- cylinders are just restrictions to their coordinate blocks
    change (((((intShiftAutomorphism V p).toEquiv :
          (ℤ → V) → (ℤ → V))^[k]) w) ∈ cylinder I S) ↔
            w ∈ cylinder I' S'
    simp only [mem_cylinder]
    -- after unfolding the relabelling, both sides assert exactly the same
    -- tuple belongs to `S`.
    change (I.restrict
      ((((intShiftAutomorphism V p).toEquiv :
          (ℤ → V) → (ℤ → V))^[k]) w) ∈ S) ↔
        (phi (I'.restrict w) ∈ S)
    have hfun : I.restrict
      ((((intShiftAutomorphism V p).toEquiv :
          (ℤ → V) → (ℤ → V))^[k]) w) = phi (I'.restrict w) := by
      funext i
      -- the explicit coordinate formula for the shift
      change (((((intShiftAutomorphism V p).toEquiv :
          (ℤ → V) → (ℤ → V))^[k]) w) (i : ℤ)) = _
      rw [intShift_iterate V p k w (i : ℤ)]
      rfl
    rw [hfun]
  have hind := infinitePi_cylinders_indep
      (ι := ℤ) (Z := fun _ : ℤ => V)
      (fun _ : ℤ => p) hgood hS' hR
  -- the shifted cylinder has the same measure as the original one, since
  -- an iterate of a measure-preserving equivalence preserves *preimages* of
  -- every measurable set.
  have hmeas : MeasurableSet (cylinder I S : Set (ℤ → V)) := hS.cylinder
  have hmp : MeasurePreserving
      ((((intShiftAutomorphism V p).toEquiv :
          (ℤ → V) → (ℤ → V))^[k]))
        (Measure.infinitePi (fun _ : ℤ => p))
        (Measure.infinitePi (fun _ : ℤ => p)) :=
    (intShiftAutomorphism V p).measurePreserving.iterate k
  have hmass :
      (Measure.infinitePi (fun _ : ℤ => p)) (cylinder I' S') =
        (Measure.infinitePi (fun _ : ℤ => p)) (cylinder I S) := by
    rw [← hpre]
    exact hmp.measure_preimage hmeas.nullMeasurableSet
  rw [hpre]
  -- now it is precisely independence of the disjoint translated blocks
  simpa [hmass] using hind

lemma intShift_weakMixing
    (V : Type*) [MeasurableSpace V] (p : Measure V)
    [IsProbabilityMeasure p] :
    IsWeaklyMixing (Measure.infinitePi (fun _ : ℤ => p))
      (intShiftAutomorphism V p) := by
  classical
  apply weakMixing_of_cylinder_eventual
    (μ := Measure.infinitePi (fun _ : ℤ => p))
    (T := intShiftAutomorphism V p)
  exact intShift_cylinder_eventual V p


-- a concrete fair two-point law, used below only to have a standard
-- nondegenerate Bernoulli example.  Using a `PMF` keeps the probability
-- normalization completely explicit.
noncomputable def fairBool : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

noncomputable instance fairBool_probability : IsProbabilityMeasure fairBool := by
  change IsProbabilityMeasure (PMF.toMeasure _)
  infer_instance

@[simp] lemma fairBool_singleton (b : Bool) :
    fairBool ({b} : Set Bool) = (2 : ENNReal)⁻¹ := by
  change (PMF.toMeasure _) {b} = _
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  simp

-- In the countable Bernoulli product every singleton is contained in
-- cylinders of arbitrarily small measure.  Recording atom-freeness at the
-- level of the *exact* product measure is important: later changes of
-- coordinates for automorphisms use genuine measurable equivalences rather
-- than equivalences modulo null sets.
noncomputable instance fairBernoulli_noAtoms :
    NoAtoms (Measure.infinitePi (fun _ : ℤ => fairBool)) := by
  classical
  constructor
  intro w
  let r : ENNReal := (2 : ENNReal)⁻¹
  have hr : r < 1 := by
    dsimp [r]
    exact ENNReal.inv_lt_one.mpr (by norm_num)
  let block : ℕ → Finset ℤ :=
    fun n => (Finset.range n).image (fun i : ℕ => (i : ℤ))
  let boxset : ℤ → Set Bool := fun i => {w i}
  have hbmeas (i : ℤ) : MeasurableSet (boxset i) :=
    MeasurableSet.singleton _
  have hcard (n : ℕ) : (block n).card = n := by
    dsimp [block]
    simpa using
      (Finset.card_image_of_injective (Finset.range n)
        (fun {_ _} h => Int.ofNat_inj.mp h))
  have hbound (n : ℕ) :
      (Measure.infinitePi (fun _ : ℤ => fairBool)) ({w} : Set (ℤ → Bool))
         ≤ r ^ n := by
    have hsub : ({w} : Set (ℤ → Bool)) ⊆
        ((↑(block n) : Set ℤ).pi boxset) := by
      intro z hz
      have hz' : z = w := Set.mem_singleton_iff.mp hz
      subst z
      exact (Set.mem_pi).2 (by
        intro i hi
        exact Set.mem_singleton _)
    refine le_trans (measure_mono hsub) ?_
    have hprod := Measure.infinitePi_pi
      (fun _ : ℤ => fairBool) (s := block n) (t := boxset)
        (fun i hi => hbmeas i)
    rw [hprod]
    -- every factor in this finite product is exactly `1/2`
    have heach (i : ℤ) : fairBool (boxset i) = r := by
      dsimp [boxset, r]
      exact fairBool_singleton (w i)
    simp_rw [heach]
    simp [hcard]
  have hzero :
      (Measure.infinitePi (fun _ : ℤ => fairBool)) ({w} : Set (ℤ → Bool)) ≤
        (0 : ENNReal) := by
    exact ge_of_tendsto
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr)
        (Filter.Eventually.of_forall hbound)
  exact bot_unique hzero


-- A measurable set in the fair product can be approximated in measure by
-- a single finite cylinder (whose base is allowed to be an arbitrary finite
-- measurable tuple set).  This follows from the set-ring approximation
-- theorem already used above for extension of independence.  Spelling it out
-- here is a useful starting interface for constructive finite block arguments:
-- on a finite Boolean block its atoms all have *equal* mass.
lemma fairBernoulli_exists_close_cylinder
    (A : Set (ℤ → Bool)) (hA : MeasurableSet A)
    {η : ENNReal} (hη : 0 < η) :
    ∃ (I : Finset ℤ) (S : Set (∀ i : (↥I), Bool)),
      MeasurableSet S ∧
      (Measure.infinitePi (fun _ : ℤ => fairBool))
        ((cylinder I S) ∆ A) < η := by
  classical
  let μ : Measure (ℤ → Bool) :=
    Measure.infinitePi (fun _ : ℤ => fairBool)
  let C : Set (Set (ℤ → Bool)) :=
    measurableCylinders (fun _ : ℤ => Bool)
  have hring : IsSetRing C := isSetRing_measurableCylinders
  have hcov : ∃ D : Set (Set (ℤ → Bool)),
      D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · intro U hU
      have hu : U = (Set.univ : Set (ℤ → Bool)) :=
        Set.mem_singleton_iff.mp hU
      simpa [C, hu] using
        (univ_mem_measurableCylinders (fun _ : ℤ => Bool))
    · simp
  have hgen : (inferInstance : MeasurableSpace (ℤ → Bool)) =
        MeasurableSpace.generateFrom C := by
    have hg := generateFrom_measurableCylinders
      (α := fun _ : ℤ => Bool)
    exact hg.symm
  change ∃ (I : Finset ℤ) (S : Set (∀ i : (↥I), Bool)),
      MeasurableSet S ∧ μ ((cylinder I S) ∆ A) < η
  obtain ⟨P, hPC, hP⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := μ) hring hcov hgen hA hη
  rcases (mem_measurableCylinders P).1 hPC with ⟨I, S, hS, hEq⟩
  refine ⟨I, S, hS, ?_⟩
  simpa [hEq] using hP


lemma extend_finite_cylinder_bool
    {I K : Finset ℤ} (hIK : I ⊆ K)
    {S : Set (∀ i : (↥I), Bool)} (hS : MeasurableSet S) :
    ∃ S' : Set (∀ j : (↥K), Bool),
      MeasurableSet S' ∧
        (cylinder (α := fun _ : ℤ => Bool) K S') =
          (cylinder (α := fun _ : ℤ => Bool) I S) := by
  classical
  let phi : (∀ j : (↥K), Bool) → (∀ i : (↥I), Bool) :=
    fun w i => w ⟨(i : ℤ), hIK i.property⟩
  have hm : Measurable phi := by
    unfold phi
    fun_prop
  refine ⟨phi ⁻¹' S, hm hS, ?_⟩
  ext w
  simp only [mem_cylinder]
  change (phi (K.restrict w) ∈ S) ↔ (I.restrict w ∈ S)
  have heq : phi (K.restrict w) = I.restrict w := by
    funext i; rfl
  rw [heq]

-- Formula for masses of Boolean blocks.  In particular the atoms of a
-- finite block of size d are all exactly `(1/2)^d`; this permits finite
-- equal-cardinality matching later without introducing null boundary sets.
lemma fairBernoulli_box_mass (I : Finset ℤ)
    (a : (i : ℤ) → Bool) :
    (Measure.infinitePi (fun _ : ℤ => fairBool))
      ((↑I : Set ℤ).pi (fun i : ℤ => ({a i} : Set Bool))) =
        ((2 : ENNReal)⁻¹) ^ I.card := by
  classical
  rw [Measure.infinitePi_pi]
  · simp
  · intro i hi
    exact MeasurableSet.singleton _


lemma fairBool_pi_singleton (I : Finset ℤ)
    (z : (∀ i : (↥I), Bool)) :
    (Measure.pi (fun _ : (↥I) => fairBool)) ({z} : Set (∀ i : (↥I), Bool)) =
        ((2 : ENNReal)⁻¹) ^ I.card := by
  classical
  -- a singleton in a finite product is the product of its singletons
  have hp := Measure.pi_pi (fun _ : (↥I) => fairBool)
      (fun i : (↥I) => ({z i} : Set Bool))
  have hset :
      (Set.univ.pi (fun i : (↥I) => ({z i} : Set Bool))) =
        ({z} : Set (∀ i : (↥I), Bool)) :=
    Set.univ_pi_singleton _
  rw [hset] at hp
  -- all factors are `1/2`; a fintype subtype of a finset has cardinal `I.card`
  simpa using hp

-- On a finite measurable type one can expand the measure as a finite sum of
-- its atoms.  We only need the singleton-measurable version, so this does not
-- assume that *all* subsets are declared measurable.
lemma measure_finite_sum_singletons {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (s : Set α) :
    μ s = ∑ x ∈ s.toFinite.toFinset, μ {x} := by
  classical
  have hu : (⋃ (x ∈ s.toFinite.toFinset), ({x} : Set α)) = s := by
    simp
  rw [← hu]
  convert MeasureTheory.measure_biUnion_finset (μ := μ)
    (s := s.toFinite.toFinset) (f := fun x : α => {x}) ?_ ?_
  · intro x hx y hy hxy
    simpa using (Set.disjoint_singleton.2 (by omega : x ≠ y))
  · intro i hi
    exact MeasurableSet.singleton i

-- Consequently the mass of *any* measurable base of a Boolean block depends
-- only on how many words it contains.
lemma fairBernoulli_cylinder_mass_card
    (K : Finset ℤ) (D : Set (∀ _j : (↥K), Bool)) (hD : MeasurableSet D) :
    (Measure.infinitePi (fun _ : ℤ => fairBool))
        (cylinder (α := fun _ : ℤ => Bool) K D) =
      (D.toFinite.toFinset.card : ENNReal) *
        ((2 : ENNReal)⁻¹) ^ K.card := by
  classical
  rw [Measure.infinitePi_cylinder _ hD]
  rw [measure_finite_sum_singletons]
  simp_rw [fairBool_pi_singleton K]
  simp



-- A changed collection of words on a finite Boolean block costs exactly their
-- count times the common word mass.  This is the useful link between the
-- purely combinatorial `ColorRound` step and estimates on cylinders: outside
-- the reported `bad` words the two Boolean families coincide pointwise, so a
-- symmetric difference on any one test lives in that bad cylinder.
lemma fairBernoulli_cylinder_symmDiff_le_bad
    (K : Finset ℤ) {ι : Type*}
    (B E : ι → Set (∀ _j : (↥K), Bool)) (bad : Finset (∀ _j : (↥K), Bool))
    (hsame : ∀ (i : ι) x, x ∉ bad → (x ∈ B i ↔ x ∈ E i)) :
    ∀ i : ι,
      (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((cylinder (α := fun _ : ℤ => Bool) K (B i)) ∆
            (cylinder (α := fun _ : ℤ => Bool) K (E i)))
        ≤ (bad.card : ENNReal) * ((2 : ENNReal)⁻¹) ^ K.card := by
  classical
  intro i
  let Bad : Set (∀ _j : (↥K), Bool) := (↑bad : Set (∀ _j : (↥K), Bool))
  have hsub : ((cylinder (α := fun _ : ℤ => Bool) K (B i)) ∆
            (cylinder (α := fun _ : ℤ => Bool) K (E i))) ⊆
          cylinder (α := fun _ : ℤ => Bool) K Bad := by
    intro w hw
    have hw' := hw
    -- membership in a cylinder is restriction to the block.
    simp only [Set.mem_symmDiff, mem_cylinder] at hw'
    have hn : K.restrict w ∈ bad := by
      by_contra hnot
      have he := hsame i (K.restrict w) hnot
      rcases hw' with h | h
      · exact h.2 (he.1 h.1)
      · exact h.2 (he.2 h.1)
    -- the base of the bad cylinder is the finset as a set of words
    change K.restrict w ∈ Bad
    exact hn
  refine le_trans (measure_mono hsub) ?_
  have hBad : MeasurableSet Bad := by
    -- finite products of the discrete Boolean sigma algebra have measurable
    -- singletons; a finset of them is therefore measurable.
    exact (bad.finite_toSet).measurableSet
  have hmass := fairBernoulli_cylinder_mass_card K Bad hBad
  calc
    (Measure.infinitePi (fun _ : ℤ => fairBool))
      (cylinder (α := fun _ : ℤ => Bool) K Bad) =
        (Bad.toFinite.toFinset.card : ENNReal) *
          ((2 : ENNReal)⁻¹) ^ K.card := hmass
    _ = (bad.card : ENNReal) * ((2 : ENNReal)⁻¹) ^ K.card := by
        simp [Bad]
    _ ≤ _ := le_rfl

-- Every permutation of a finite Boolean cube is measure preserving for the
-- product fair law.  Notice that this holds for arbitrary permutations of
-- *atoms*, not just coordinate permutations.
lemma fairBool_finblock_permutation (I : Finset ℤ)
    (σ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool)) :
    MeasurePreserving (σ : (∀ _i : (↥I), Bool) → (∀ _i : (↥I), Bool))
      (Measure.pi (fun _ : (↥I) => fairBool))
      (Measure.pi (fun _ : (↥I) => fairBool)) := by
  classical
  let μI : Measure (∀ _i : (↥I), Bool) :=
    Measure.pi (fun _ : (↥I) => fairBool)
  have hmeas : Measurable (σ : (∀ _i : (↥I), Bool) →
      (∀ _i : (↥I), Bool)) :=
    measurable_of_finite _
  refine ⟨hmeas, ?_⟩
  -- finite measures on a finite measurable space are determined by points
  apply Measure.ext_of_singleton
  intro y
  change (Measure.map (σ : (∀ _i : (↥I), Bool) →
        (∀ _i : (↥I), Bool)) μI) {y} = μI {y}
  rw [Measure.map_apply hmeas (MeasurableSet.singleton y)]
  have hpre : (σ : (∀ _i : (↥I), Bool) →
        (∀ _i : (↥I), Bool)) ⁻¹' ({y} : Set _) = {σ.symm y} := by
    ext x
    change σ x = y ↔ x = σ.symm y
    exact (Equiv.eq_symm_apply σ).symm
  rw [hpre]
  exact fairBool_pi_singleton I _ |>.trans (fairBool_pi_singleton I _).symm


-- Lift a permutation of the atoms of a finite coordinate block to a Borel
-- equivalence of the full Boolean shift.  Outside the chosen block it is the
-- identity.  The equivalence itself is quite useful independently of its
-- invariance of product measure below.
noncomputable def fairBlockMeasurableEquiv (I : Finset ℤ)
    (σ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool)) :
    (ℤ → Bool) ≃ᵐ (ℤ → Bool) := by
  classical
  let act (τ : (∀ _i : (↥I), Bool) → (∀ _i : (↥I), Bool))
      (w : ℤ → Bool) (j : ℤ) : Bool :=
        if hj : j ∈ I then τ (I.restrict w) ⟨j, hj⟩ else w j
  have hres (τ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool))
      (w : ℤ → Bool) :
      I.restrict (act (τ : _ → _) w) = τ (I.restrict w) := by
    funext i
    change (if h : (i : ℤ) ∈ I then _ else _) = _
    simp [i.property]
  let e : (ℤ → Bool) ≃ (ℤ → Bool) :=
    { toFun := act (σ : _ → _)
      invFun := act (σ.symm : _ → _)
      left_inv := by
        intro w
        funext j
        by_cases hj : j ∈ I
        · change (if h : j ∈ I then
              (σ.symm (I.restrict (act (σ : _ → _) w))) ⟨j,h⟩
            else _) = _
          simp only [dif_pos hj]
          rw [hres σ w]
          rw [σ.symm_apply_apply]
          rfl
        · change (if h : j ∈ I then _ else (act (σ : _ → _) w j)) = _
          simp [hj, act]
      right_inv := by
        intro w
        funext j
        by_cases hj : j ∈ I
        · change (if h : j ∈ I then
              (σ (I.restrict (act (σ.symm : _ → _) w))) ⟨j,h⟩
            else _) = _
          simp only [dif_pos hj]
          rw [hres σ.symm w]
          rw [σ.apply_symm_apply]
          rfl
        · change (if h : j ∈ I then _ else (act (σ.symm : _ → _) w j)) = _
          simp [hj, act] }
  have hm (τ : (∀ _i : (↥I), Bool) → (∀ _i : (↥I), Bool))
      (hτ : Measurable τ) :
      Measurable (act τ) := by
    -- the condition on a coordinate is fixed, so each evaluation is
    -- either a measurable finite-block composite or the old coordinate
    apply measurable_pi_lambda
    intro j
    by_cases hj : j ∈ I
    · have hrest : Measurable (fun w : ℤ → Bool => I.restrict w) := by
        fun_prop
      have hev : Measurable
          (fun z : (∀ _i : (↥I), Bool) => z ⟨j, hj⟩) := by
        fun_prop
      have hc := hev.comp (hτ.comp hrest)
      -- expose the compositions explicitly before simplifying the fixed branch
      change Measurable (fun w : ℤ → Bool =>
        (if h : j ∈ I then τ (I.restrict w) ⟨j,h⟩ else w j))
      simp only [dif_pos hj]
      simpa [Function.comp_def] using hc
    · have hc : Measurable (fun w : ℤ → Bool => w j) := by fun_prop
      simpa [act, hj] using hc
  exact MeasurableEquiv.mk e
    (hm _ (measurable_of_finite _))
    (hm _ (measurable_of_finite _))

@[simp] lemma fairBlockMeasurableEquiv_apply_of_mem
    (I : Finset ℤ)
    (σ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool))
    (w : ℤ → Bool) (j : ℤ) (hj : j ∈ I) :
    fairBlockMeasurableEquiv I σ w j = σ (I.restrict w) ⟨j,hj⟩ := by
  classical
  simp [fairBlockMeasurableEquiv, hj]

@[simp] lemma fairBlockMeasurableEquiv_apply_of_not_mem
    (I : Finset ℤ)
    (σ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool))
    (w : ℤ → Bool) (j : ℤ) (hj : j ∉ I) :
    fairBlockMeasurableEquiv I σ w j = w j := by
  classical
  simp [fairBlockMeasurableEquiv, hj]

lemma fairBlockMeasurableEquiv_restrict
    (I : Finset ℤ)
    (σ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool))
    (w : ℤ → Bool) :
    I.restrict (fairBlockMeasurableEquiv I σ w) = σ (I.restrict w) := by
  classical
  funext j
  simp [fairBlockMeasurableEquiv_apply_of_mem I σ w (j:ℤ) j.property]



-- In a finite Boolean cube, equality of the number of atoms is exactly what is
-- needed to match two events by a permutation.  Keeping this at the level of
-- the *whole* cube (rather than just an equivalence between the two
-- subtypes) is useful: `fairBlockMeasurableEquiv` accepts permutations of the
-- whole block.  On the complement we use any bijection; the cardinality of
-- the complements follows by subtraction in the finite ambient type.
noncomputable def finitePermOfSetCardEq {α : Type*} [Fintype α]
    (s t : Set α)
    (h : Nat.card {x : α // x ∈ s} = Nat.card {x : α // x ∈ t}) : α ≃ α := by
  classical
  let hs : Fintype.card s = Fintype.card t := by
    simpa [Nat.card_eq_fintype_card] using h
  let es : {x : α // x ∈ s} ≃ {x : α // x ∈ t} :=
    Fintype.equivOfCardEq hs
  have hcomp : Fintype.card (sᶜ : Set α) = Fintype.card (tᶜ : Set α) := by
    change Fintype.card {x : α // ¬ x ∈ s} =
      Fintype.card {x : α // ¬ x ∈ t}
    rw [Fintype.card_subtype_compl (fun x : α => x ∈ s),
        Fintype.card_subtype_compl (fun x : α => x ∈ t)]
    exact congrArg (fun q : Nat => Fintype.card α - q) hs
  let ec : {x : α // x ∈ sᶜ} ≃ {x : α // x ∈ tᶜ} :=
    Fintype.equivOfCardEq hcomp
  -- the standard `sumCompl` equivalence turns a point into either a member
  -- of the set or of its complement
  exact (Equiv.Set.sumCompl s).symm |>.trans
    ((es.sumCongr ec).trans (Equiv.Set.sumCompl t))

lemma finitePermOfSetCardEq_mem {α : Type*} [Fintype α]
    (s t : Set α)
    (h : Nat.card {x : α // x ∈ s} = Nat.card {x : α // x ∈ t})
    (x : α) : finitePermOfSetCardEq s t h x ∈ t ↔ x ∈ s := by
  classical
  by_cases hx : x ∈ s
  · have heq : (Equiv.Set.sumCompl s).symm x = Sum.inl ⟨x,hx⟩ :=
      Equiv.Set.sumCompl_symm_apply_of_mem hx
    change ((Equiv.Set.sumCompl t) _ ∈ t ↔ x ∈ s)
    simp [finitePermOfSetCardEq, heq, hx]
  · have heq : (Equiv.Set.sumCompl s).symm x = Sum.inr ⟨x,hx⟩ :=
      Equiv.Set.sumCompl_symm_apply_of_notMem hx
    -- On this branch the image is a point of the complement.  Asking it
    -- to be in the set is an immediate contradiction.  Written this way the
    -- proof does not rely on the particular `equivOfCardEq` chosen above.
    simp [finitePermOfSetCardEq, heq, hx]
    have hcompl : ∀ (z : (tᶜ : Set α)), (z:α) ∉ t := fun z => z.property
    exact hcompl _

lemma finitePermOfSetCardEq_preimage {α : Type*} [Fintype α]
    (s t : Set α)
    (h : Nat.card {x : α // x ∈ s} = Nat.card {x : α // x ∈ t}) :
    (finitePermOfSetCardEq s t h : α → α) ⁻¹' t = s := by
  ext x
  exact finitePermOfSetCardEq_mem s t h x

-- Restricting a finite-block recoding to the very same block has no edge
-- effects.  This inexpensive formula is often more pleasant to use than
-- `fairBlock_preimage_cylinder`, where a larger auxiliary block appears.
lemma fairBlock_preimage_cylinder_same
    (K : Finset ℤ)
    (σ : (∀ _j : (↥K), Bool) ≃ (∀ _j : (↥K), Bool))
    (B : Set (∀ j : (↥K), Bool)) :
    (fairBlockMeasurableEquiv K σ : (ℤ → Bool) → (ℤ → Bool)) ⁻¹'
          (cylinder (α := fun _ : ℤ => Bool) K B) =
      cylinder (α := fun _ : ℤ => Bool) K ((σ : _ → _) ⁻¹' B) := by
  classical
  ext w
  simp only [Set.mem_preimage, mem_cylinder]
  change K.restrict (fairBlockMeasurableEquiv K σ w) ∈ B ↔
    σ (K.restrict w) ∈ B
  rw [fairBlockMeasurableEquiv_restrict K σ w]

-- Hence two subsets of a block that contain the same number of atoms are
-- literally interchanged by a measurable, measure-preserving block
-- automorphism, and their cylinder measures agree.  Later tower estimates
-- only have to make the cardinalities match; no null representatives are
-- hidden in this assertion.
lemma fairBlock_exists_map_cylinder_of_card_eq
    (K : Finset ℤ)
    (D E : Set (∀ _j : (↥K), Bool))
    (hcard : Nat.card {z : (∀ _j : (↥K), Bool) // z ∈ D} =
             Nat.card {z : (∀ _j : (↥K), Bool) // z ∈ E}) :
    ∃ σ : (∀ _j : (↥K), Bool) ≃ (∀ _j : (↥K), Bool),
      (fairBlockMeasurableEquiv K σ : (ℤ → Bool) → (ℤ → Bool)) ⁻¹'
          (cylinder (α := fun _ : ℤ => Bool) K E) =
            cylinder (α := fun _ : ℤ => Bool) K D := by
  classical
  let σ : (∀ _j : (↥K), Bool) ≃ (∀ _j : (↥K), Bool) :=
    finitePermOfSetCardEq D E hcard
  refine ⟨σ, ?_⟩
  rw [fairBlock_preimage_cylinder_same]
  have hpre : (σ : (∀ _j : (↥K), Bool) → (∀ _j : (↥K), Bool)) ⁻¹' E = D := by
    simpa [σ] using
      (finitePermOfSetCardEq_preimage D E hcard)
  rw [hpre]



noncomputable def liftBlockEquiv
    {I K : Finset ℤ} (hIK : I ⊆ K)
    (σ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool)) :
    (∀ _j : (↥K), Bool) ≃ (∀ _j : (↥K), Bool) := by
  classical
  let res : (∀ _j : (↥K), Bool) → (∀ _i : (↥I), Bool) :=
    fun z i => z ⟨(i:ℤ), hIK i.property⟩
  let act (τ : (∀ _i : (↥I), Bool) → (∀ _i : (↥I), Bool))
      (z : (∀ _j : (↥K), Bool)) (j : (↥K)) : Bool :=
        if hj : (j:ℤ) ∈ I then τ (res z) ⟨(j:ℤ), hj⟩ else z j
  have hres (τ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool))
      (z : (∀ _j : (↥K), Bool)) :
      res (act (τ : _ → _) z) = τ (res z) := by
    funext i
    change (if h : (i:ℤ) ∈ I then _ else _) = _
    simp [i.property]
  exact
    { toFun := act (σ : _ → _)
      invFun := act (σ.symm : _ → _)
      left_inv := by
        intro z
        funext j
        by_cases hj : (j:ℤ) ∈ I
        · change (if h : (j:ℤ) ∈ I then
              (σ.symm (res (act (σ : _ → _) z))) ⟨(j:ℤ),h⟩
            else _) = _
          simp only [dif_pos hj]
          rw [hres σ z]
          rw [σ.symm_apply_apply]
        · change (if h : (j:ℤ) ∈ I then _ else
              (act (σ : _ → _) z j)) = _
          simp [hj, act]
      right_inv := by
        intro z
        funext j
        by_cases hj : (j:ℤ) ∈ I
        · change (if h : (j:ℤ) ∈ I then
              (σ (res (act (σ.symm : _ → _) z))) ⟨(j:ℤ),h⟩
            else _) = _
          simp only [dif_pos hj]
          rw [hres σ.symm z]
          rw [σ.apply_symm_apply]
        · change (if h : (j:ℤ) ∈ I then _ else
              (act (σ.symm : _ → _) z j)) = _
          simp [hj, act] }

lemma liftBlock_restrict_compat
    {I K : Finset ℤ} (hIK : I ⊆ K)
    (σ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool))
    (w : ℤ → Bool) :
    K.restrict (fairBlockMeasurableEquiv I σ w) =
      liftBlockEquiv hIK σ (K.restrict w) := by
  classical
  funext j
  by_cases hj : (j:ℤ) ∈ I
  · change fairBlockMeasurableEquiv I σ w (j:ℤ) = _
    rw [fairBlockMeasurableEquiv_apply_of_mem I σ w _ hj]
    change _ = (if h : (j:ℤ) ∈ I then
       σ (fun i : (↥I) => K.restrict w ⟨(i:ℤ), hIK i.property⟩) ⟨(j:ℤ), h⟩
       else _)
    simp only [dif_pos hj]
    congr 1
  · change fairBlockMeasurableEquiv I σ w (j:ℤ) = _
    rw [fairBlockMeasurableEquiv_apply_of_not_mem I σ w _ hj]
    change _ = (if h : (j:ℤ) ∈ I then _ else K.restrict w j)
    simp [hj]

lemma fairBlock_preimage_cylinder
    {I K : Finset ℤ} (hIK : I ⊆ K)
    (σ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool))
    (B : Set (∀ j : (↥K), Bool)) :
    (fairBlockMeasurableEquiv I σ : (ℤ → Bool) → (ℤ → Bool)) ⁻¹'
          (cylinder (α := fun _ : ℤ => Bool) K B) =
      cylinder (α := fun _ : ℤ => Bool) K
          ((liftBlockEquiv hIK σ : _ → _) ⁻¹' B) := by
  classical
  ext w
  simp only [Set.mem_preimage, mem_cylinder]
  change K.restrict (fairBlockMeasurableEquiv I σ w) ∈ B ↔
       liftBlockEquiv hIK σ (K.restrict w) ∈ B
  rw [liftBlock_restrict_compat hIK σ w]

lemma fairBlock_cylinder_mass
    {I K : Finset ℤ} (hIK : I ⊆ K)
    (σ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool))
    (B : Set (∀ j : (↥K), Bool)) (hB : MeasurableSet B) :
    (Measure.infinitePi (fun _ : ℤ => fairBool))
      ((fairBlockMeasurableEquiv I σ : (ℤ → Bool) → (ℤ → Bool)) ⁻¹'
          (cylinder (α := fun _ : ℤ => Bool) K B)) =
    (Measure.infinitePi (fun _ : ℤ => fairBool))
          (cylinder (α := fun _ : ℤ => Bool) K B) := by
  classical
  rw [fairBlock_preimage_cylinder hIK σ B]
  rw [Measure.infinitePi_cylinder, Measure.infinitePi_cylinder]
  · -- invariance in the finite cube
    have hmp := fairBool_finblock_permutation K (liftBlockEquiv hIK σ)
    have heq := hmp.measure_preimage hB.nullMeasurableSet
    exact heq
  · exact hB
  · exact (measurable_of_finite _ hB)


lemma fairBlock_measurePreserving
    (I : Finset ℤ)
    (σ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool)) :
    MeasurePreserving
      (fairBlockMeasurableEquiv I σ : (ℤ → Bool) → (ℤ → Bool))
      (Measure.infinitePi (fun _ : ℤ => fairBool))
      (Measure.infinitePi (fun _ : ℤ => fairBool)) := by
  classical
  let μ : Measure (ℤ → Bool) :=
    Measure.infinitePi (fun _ : ℤ => fairBool)
  let f : (ℤ → Bool) → (ℤ → Bool) :=
    (fairBlockMeasurableEquiv I σ : (ℤ → Bool) → (ℤ → Bool))
  have hf : Measurable f := (fairBlockMeasurableEquiv I σ).measurable
  refine ⟨hf, ?_⟩
  let C : Set (Set (ℤ → Bool)) :=
    measurableCylinders (fun _ : ℤ => Bool)
  have hgen : (inferInstance : MeasurableSpace (ℤ → Bool)) =
        MeasurableSpace.generateFrom C :=
    (generateFrom_measurableCylinders
      (α := fun _ : ℤ => Bool)).symm
  have hinter : IsPiSystem C := isPiSystem_measurableCylinders
  -- equality just on the finite cylinders already determines the two
  -- probability measures
  have hcyl (P : Set (ℤ → Bool)) (hP : P ∈ C) : μ (f ⁻¹' P) = μ P := by
    rcases (mem_measurableCylinders P).1 hP with ⟨L, B, hB, rfl⟩
    let K : Finset ℤ := I ∪ L
    have hIK : I ⊆ K := Finset.subset_union_left
    have hLK : L ⊆ K := Finset.subset_union_right
    obtain ⟨B', hB', hEq⟩ := extend_finite_cylinder_bool hLK hB
    change μ (f ⁻¹' (cylinder (α := fun _ : ℤ => Bool) L B)) =
      μ (cylinder (α := fun _ : ℤ => Bool) L B)
    rw [← hEq]
    change
      (Measure.infinitePi (fun _ : ℤ => fairBool))
        ((fairBlockMeasurableEquiv I σ : (ℤ → Bool) → (ℤ → Bool)) ⁻¹'
          (cylinder (α := fun _ : ℤ => Bool) K B')) =
      (Measure.infinitePi (fun _ : ℤ => fairBool))
          (cylinder (α := fun _ : ℤ => Bool) K B')
    exact fairBlock_cylinder_mass hIK σ B' hB'
  -- the pi-system extension criterion needs a countable cover; the single
  -- set `univ` is a cylinder.
  have heq : Measure.map f μ = μ := by
    apply Measure.ext_of_generateFrom_of_cover
      (μ := Measure.map f μ) (ν := μ)
      (S := C) (T := ({Set.univ} : Set (Set (ℤ → Bool))))
      hgen (Set.countable_singleton _) hinter
    · simp
    · intro t ht
      have ht' : t = (Set.univ : Set (ℤ → Bool)) :=
        Set.mem_singleton_iff.mp ht
      subst t
      rw [Measure.map_apply_of_aemeasurable hf.aemeasurable MeasurableSet.univ]
      change μ (f ⁻¹' Set.univ) ≠ (⊤ : ENNReal)
      simp [μ]
    · intro t ht s hs
      have ht' : t = (Set.univ : Set (ℤ → Bool)) :=
        Set.mem_singleton_iff.mp ht
      subst t
      have hsm : MeasurableSet s :=
        MeasurableSet.of_mem_measurableCylinders hs
      have hv : μ (f ⁻¹' s) = μ s := hcyl s hs
      simpa [Measure.map_apply_of_aemeasurable hf.aemeasurable hsm, hsm,
        hv] using hv
    · intro t ht
      have ht' : t = (Set.univ : Set (ℤ → Bool)) :=
        Set.mem_singleton_iff.mp ht
      subst t
      rw [Measure.map_apply_of_aemeasurable hf.aemeasurable MeasurableSet.univ]
      change μ (f ⁻¹' Set.univ) = μ Set.univ
      simp [μ]
  exact heq


lemma fairBernoulli_cylinder_mass_eq_of_card_eq
    (K : Finset ℤ)
    (D E : Set (∀ _j : (↥K), Bool))
    (hcard : Nat.card {z : (∀ _j : (↥K), Bool) // z ∈ D} =
             Nat.card {z : (∀ _j : (↥K), Bool) // z ∈ E})
    (hE : MeasurableSet E) :
    (Measure.infinitePi (fun _ : ℤ => fairBool))
        (cylinder (α := fun _ : ℤ => Bool) K D) =
    (Measure.infinitePi (fun _ : ℤ => fairBool))
        (cylinder (α := fun _ : ℤ => Bool) K E) := by
  classical
  obtain ⟨σ, hσ⟩ :=
    fairBlock_exists_map_cylinder_of_card_eq K D E hcard
  let U : (ℤ → Bool) → (ℤ → Bool) :=
    (fairBlockMeasurableEquiv K σ : (ℤ → Bool) → (ℤ → Bool))
  have hpres := fairBlock_measurePreserving K σ
  have hmeas : MeasurableSet (cylinder
      (α := fun _ : ℤ => Bool) K E) := hE.cylinder
  have hm := hpres.measure_preimage hmeas.nullMeasurableSet
  change
    (Measure.infinitePi (fun _ : ℤ => fairBool))
       (U ⁻¹' (cylinder (α := fun _ : ℤ => Bool) K E)) =
      (Measure.infinitePi (fun _ : ℤ => fairBool))
       (cylinder (α := fun _ : ℤ => Bool) K E) at hm
  change
    (Measure.infinitePi (fun _ : ℤ => fairBool))
        (cylinder (α := fun _ : ℤ => Bool) K D) =
      (Measure.infinitePi (fun _ : ℤ => fairBool))
        (cylinder (α := fun _ : ℤ => Bool) K E)
  rw [← hm]
  change
    (Measure.infinitePi (fun _ : ℤ => fairBool))
        (cylinder (α := fun _ : ℤ => Bool) K D) =
      (Measure.infinitePi (fun _ : ℤ => fairBool))
        ((fairBlockMeasurableEquiv K σ : (ℤ → Bool) → (ℤ → Bool)) ⁻¹'
          (cylinder (α := fun _ : ℤ => Bool) K E))
  rw [hσ]


noncomputable def fairBlockAutomorphism
    (I : Finset ℤ)
    (σ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool)) :
    Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)) where
  toEquiv := fairBlockMeasurableEquiv I σ
  measurePreserving := fairBlock_measurePreserving I σ

-- Consequently the concrete product model has not only one, but many
-- explicitly presented weakly mixing automorphisms: every finite block
-- recoding of the bilateral Bernoulli shift. These are the transformations
-- one uses in the finite-neighbourhood (tower) step.
lemma fairBernoulli_block_conjugate_weakMixing
    (I : Finset ℤ)
    (σ : (∀ _i : (↥I), Bool) ≃ (∀ _i : (↥I), Bool)) :
    IsWeaklyMixing (Measure.infinitePi (fun _ : ℤ => fairBool))
      (conjugateAutomorphism
        (Measure.infinitePi (fun _ : ℤ => fairBool))
        (fairBlockAutomorphism I σ)
        (intShiftAutomorphism Bool fairBool)) := by
  exact conjugate_weakMixing _ _ _ (intShift_weakMixing Bool fairBool)


-- Simultaneous approximation: finitely many events of the shift may be
-- put on one common Boolean block.  Extending a cylinder to a larger block
-- does not change it, so no new error is paid here.
lemma fairBernoulli_exists_common_block
    (n : ℕ) (A : Fin n → Set (ℤ → Bool))
    (hA : ∀ i, MeasurableSet (A i))
    (η : Fin n → ENNReal) (hη : ∀ i, 0 < η i) :
    ∃ (K : Finset ℤ) (B : Fin n → Set (∀ _j : (↥K), Bool)),
      (∀ i, MeasurableSet (B i)) ∧
      (∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((cylinder (α := fun _ : ℤ => Bool) K (B i)) ∆ A i) < η i) := by
  classical
  have hi (i : Fin n) :
      ∃ (I : Finset ℤ) (S : Set (∀ _j : (↥I), Bool)),
        MeasurableSet S ∧
        (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((cylinder (α := fun _ : ℤ => Bool) I S) ∆ A i) < η i :=
    fairBernoulli_exists_close_cylinder (A i) (hA i) (hη i)
  choose I h1 using hi
  choose S h2 using h1
  let K : Finset ℤ :=
    Finset.univ.biUnion (fun i : Fin n => I i)
  have hsub (i : Fin n) : I i ⊆ K := by
    intro a ha
    have him : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    exact (Finset.mem_biUnion).2 ⟨i, him, ha⟩
  have hex (i : Fin n) :
      ∃ E : Set (∀ _j : (↥K), Bool),
        MeasurableSet E ∧
        cylinder (α := fun _ : ℤ => Bool) K E =
          cylinder (α := fun _ : ℤ => Bool) (I i) (S i) :=
    extend_finite_cylinder_bool (hsub i) (h2 i).1
  choose E hE using hex
  refine ⟨K, E, (fun i => (hE i).1), ?_⟩
  intro i
  rw [(hE i).2]
  exact (h2 i).2


-- Often a centre and its image have to be compared simultaneously.  Two
-- applications of the preceding lemma can be put on a *single* cube simply
-- by taking the union of their supports.  No estimates are used in this
-- step--the extended cylinders are equal as actual sets.  This is the useful
-- finite-block input to any later matching/tower construction.
lemma fairBernoulli_exists_common_block_pair
    (n : ℕ) (A D : Fin n → Set (ℤ → Bool))
    (hA : ∀ i, MeasurableSet (A i))
    (hD : ∀ i, MeasurableSet (D i))
    (η θ : Fin n → ENNReal) (hη : ∀ i, 0 < η i)
    (hθ : ∀ i, 0 < θ i) :
    ∃ (K : Finset ℤ)
        (B E : Fin n → Set (∀ _j : (↥K), Bool)),
      (∀ i, MeasurableSet (B i)) ∧
      (∀ i, MeasurableSet (E i)) ∧
      (∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((cylinder (α := fun _ : ℤ => Bool) K (B i)) ∆ A i) < η i) ∧
      (∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((cylinder (α := fun _ : ℤ => Bool) K (E i)) ∆ D i) < θ i) := by
  classical
  obtain ⟨I, B0, hB0, hcloseB⟩ :=
    fairBernoulli_exists_common_block n A hA η hη
  obtain ⟨J, E0, hE0, hcloseE⟩ :=
    fairBernoulli_exists_common_block n D hD θ hθ
  let K : Finset ℤ := I ∪ J
  have hIK : I ⊆ K := by
    intro x hx
    exact Finset.mem_union_left _ hx
  have hJK : J ⊆ K := by
    intro x hx
    exact Finset.mem_union_right _ hx
  have hBx (i : Fin n) :
      ∃ S : Set (∀ _j : (↥K), Bool),
        MeasurableSet S ∧ cylinder (α := fun _ : ℤ => Bool) K S =
          cylinder (α := fun _ : ℤ => Bool) I (B0 i) :=
    extend_finite_cylinder_bool hIK (hB0 i)
  have hEx (i : Fin n) :
      ∃ S : Set (∀ _j : (↥K), Bool),
        MeasurableSet S ∧ cylinder (α := fun _ : ℤ => Bool) K S =
          cylinder (α := fun _ : ℤ => Bool) J (E0 i) :=
    extend_finite_cylinder_bool hJK (hE0 i)
  choose B hB using hBx
  choose E hE using hEx
  refine ⟨K, B, E, (fun i => (hB i).1), (fun i => (hE i).1), ?_, ?_⟩
  · intro i
    rw [(hB i).2]
    exact hcloseB i
  · intro i
    rw [(hE i).2]
    exact hcloseE i

-- Applying this to the image under a centre keeps track of the elementary
-- but important measurability point: images of Borel sets under our bundled
-- automorphisms are again Borel (they are measurable embeddings).
lemma fairBernoulli_exists_common_block_and_center_image
    (n : ℕ)
    (R₀ : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)))
    (A : Fin n → Set (ℤ → Bool)) (hA : ∀ i, MeasurableSet (A i))
    (η θ : Fin n → ENNReal) (hη : ∀ i, 0 < η i)
    (hθ : ∀ i, 0 < θ i) :
    ∃ (K : Finset ℤ)
        (B E : Fin n → Set (∀ _j : (↥K), Bool)),
      (∀ i, MeasurableSet (B i)) ∧
      (∀ i, MeasurableSet (E i)) ∧
      (∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((cylinder (α := fun _ : ℤ => Bool) K (B i)) ∆ A i) < η i) ∧
      (∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((cylinder (α := fun _ : ℤ => Bool) K (E i)) ∆
              (R₀.toEquiv '' (A i))) < θ i) := by
  classical
  have hRA (i : Fin n) : MeasurableSet (R₀.toEquiv '' A i) :=
    R₀.toEquiv.measurableEmbedding.measurableSet_image' (hA i)
  simpa using
    (fairBernoulli_exists_common_block_pair
      n A (fun i => R₀.toEquiv '' A i) hA hRA η θ hη hθ)



-- Matching all the atoms of a finite Boolean family at once. The one-set
-- permutation above does not suffice for a simultaneous neighbourhood: the
-- common Boolean partition is what has to be matched. This finite observation
-- has no measure in its statement.
variable {ι α : Type*}

noncomputable def boolLabel [Fintype ι] [DecidableEq ι]
    (B : ι → Set α) (x : α) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => x ∈ B i)

lemma mem_boolCell_label [Fintype ι] [DecidableEq ι]
    (B : ι → Set α) (x : α) :
    x ∈ HalmosSupport.boolCell B (↑(boolLabel B x) : Set ι) := by
  classical
  apply (HalmosSupport.mem_boolCell).2
  intro i
  simp [boolLabel]

lemma boolLabel_eq_of_mem [Fintype ι] [DecidableEq ι]
    (B : ι → Set α) (s : Finset ι) (x : α)
    (hx : x ∈ HalmosSupport.boolCell B (↑s : Set ι)) :
    boolLabel B x = s := by
  classical
  ext i
  simpa [boolLabel] using (HalmosSupport.mem_boolCell.1 hx i)

noncomputable def encodeBoolCells [Fintype ι] [DecidableEq ι]
    (B : ι → Set α) :
    α ≃ (s : Finset ι) ×
      {x : α // x ∈ HalmosSupport.boolCell B (↑s : Set ι)} := by
  classical
  refine
    { toFun := fun x => ⟨boolLabel B x, ⟨x, mem_boolCell_label B x⟩⟩
      invFun := fun z => z.2.1
      left_inv := ?_
      right_inv := ?_ }
  · intro x; rfl
  · intro z
    rcases z with ⟨s, ⟨x,hx⟩⟩
    have hs : boolLabel B x = s := boolLabel_eq_of_mem B s x hx
    -- dependent equality
    subst s
    rfl

noncomputable def blockPermOfCells [Fintype ι] [DecidableEq ι]
    [Fintype α]
    (B E : ι → Set α)
    (hcard : ∀ s : Finset ι,
      Nat.card {x : α // x ∈ HalmosSupport.boolCell B (↑s : Set ι)} =
      Nat.card {x : α // x ∈ HalmosSupport.boolCell E (↑s : Set ι)}) :
    α ≃ α := by
  classical
  let es (s : Finset ι) :
      {x : α // x ∈ HalmosSupport.boolCell B (↑s : Set ι)} ≃
      {x : α // x ∈ HalmosSupport.boolCell E (↑s : Set ι)} :=
        Fintype.equivOfCardEq (by
          simpa [Nat.card_eq_fintype_card] using hcard s)
  exact (encodeBoolCells B).trans
    ((Equiv.sigmaCongrRight es).trans (encodeBoolCells E).symm)

lemma blockPermOfCells_mem [Fintype ι] [DecidableEq ι]
    [Fintype α]
    (B E : ι → Set α)
    (hcard : ∀ s : Finset ι,
      Nat.card {x : α // x ∈ HalmosSupport.boolCell B (↑s : Set ι)} =
      Nat.card {x : α // x ∈ HalmosSupport.boolCell E (↑s : Set ι)})
    (x : α) (i : ι) :
    blockPermOfCells B E hcard x ∈ E i ↔ x ∈ B i := by
  classical
  -- unfold construction by fixing its source label
  let s : Finset ι := boolLabel B x
  have hx : x ∈ HalmosSupport.boolCell B (↑s : Set ι) := by
    dsimp [s]
    exact mem_boolCell_label B x
  let es : {x : α // x ∈ HalmosSupport.boolCell B (↑s : Set ι)} ≃
      {x : α // x ∈ HalmosSupport.boolCell E (↑s : Set ι)} :=
        Fintype.equivOfCardEq (by
          simpa [Nat.card_eq_fintype_card] using hcard s)
  let y : α := (es ⟨x,hx⟩ : {z : α // z ∈ HalmosSupport.boolCell E (↑s : Set ι)}).1
  have hycell : y ∈ HalmosSupport.boolCell E (↑s : Set ι) :=
    (es ⟨x,hx⟩ : {z : α // z ∈ HalmosSupport.boolCell E (↑s : Set ι)}).2
  have himgy : blockPermOfCells B E hcard x = y := by
    -- computation of the sigma equivalences
    change _ = _
    rfl
  rw [himgy]
  have hi1 := (HalmosSupport.mem_boolCell.1 hx i)
  have hi2 := (HalmosSupport.mem_boolCell.1 hycell i)
  exact hi2.trans hi1.symm



-- Rounding the labels on a *finite* block.  This is the only combinatorial
-- part of simultaneous cylinder approximation: a word has exactly one
-- Boolean label.  Retain as many labels of the target block as possible and
-- reassign the surplus words.  The atoms all have equal mass later, but doing
-- the calculation with cardinalities keeps it useful for any finite carrier.
lemma exists_rounded_bool_labels {α : Type*} [Fintype α]
    (n : ℕ) (B E : Fin n → Set α) :
    ∃ l : α → Finset (Fin n),
      (∀ s : Finset (Fin n),
        (Finset.univ.filter (fun x : α => l x = s)).card =
        (Finset.univ.filter (fun x : α => boolLabel B x = s)).card) ∧
      (Finset.univ.filter
          (fun x : α => l x ≠ boolLabel E x)).card ≤
        ∑ s : Finset (Fin n),
          ((Finset.univ.filter
              (fun x : α => boolLabel B x = s)).card -
            min ((Finset.univ.filter
              (fun x : α => boolLabel B x = s)).card)
                ((Finset.univ.filter
                  (fun x : α => boolLabel E x = s)).card)) := by
  classical
  simpa [HalmosSupport.colorFiber] using
    (HalmosSupport.exists_colorRound
      (c := fun x : α => boolLabel B x)
      (d := fun x : α => boolLabel E x))

-- Read the rounded labels as an actual Boolean family.  Equality of labels
-- is exactly membership in a Boolean cell, so this gives the cell-card
-- hypothesis required by `blockPermOfCells`; moreover the changed cells are
-- still bounded by the finite surplus of the target approximation.
lemma exists_rounded_bool_family {α : Type*} [Fintype α]
    (n : ℕ) (B E : Fin n → Set α) :
    ∃ E' : Fin n → Set α,
      (∀ s : Finset (Fin n),
        (Finset.univ.filter (fun x : α =>
          boolLabel E' x = s)).card =
        (Finset.univ.filter (fun x : α =>
          boolLabel B x = s)).card) ∧
      ∃ bad : Finset α,
        bad.card ≤
          ∑ s : Finset (Fin n),
            ((Finset.univ.filter
                (fun x : α => boolLabel B x = s)).card -
             min ((Finset.univ.filter
                    (fun x : α => boolLabel B x = s)).card)
                 ((Finset.univ.filter
                    (fun x : α => boolLabel E x = s)).card)) ∧
        ∀ i x, x ∉ bad -> (x ∈ E' i ↔ x ∈ E i) := by
  classical
  obtain ⟨l, hl, hbad⟩ := exists_rounded_bool_labels n B E
  let E' : Fin n → Set α := fun i => {x | i ∈ l x}
  let bad : Finset α := Finset.univ.filter
     (fun x : α => l x ≠ boolLabel E x)
  have hlabel (x : α) : boolLabel E' x = l x := by
    ext i
    simp [boolLabel, E']
  refine ⟨E', ?_, bad, ?_, ?_⟩
  · intro s
    have hu : (Finset.univ.filter (fun x : α => boolLabel E' x = s)) =
        (Finset.univ.filter (fun x : α => l x = s)) := by
      ext x
      simp [hlabel]
    rw [hu]
    exact hl s
  · exact hbad
  · intro i x hx
    have heq : l x = boolLabel E x := by
      by_contra hne
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    change i ∈ l x ↔ x ∈ E i
    rw [heq]
    simp [boolLabel]


lemma boolLabel_card_cell {α : Type*} [Fintype α]
    {n : ℕ} (P : Fin n → Set α) (s : Finset (Fin n)) :
    Nat.card {x : α //
        x ∈ HalmosSupport.boolCell P (↑s : Set (Fin n))} =
      (Finset.univ.filter (fun x : α => boolLabel P x = s)).card := by
  classical
  have hiff (x : α) : (x ∈ HalmosSupport.boolCell P
      (↑s : Set (Fin n))) ↔ boolLabel P x = s := by
    constructor
    · exact boolLabel_eq_of_mem P s x
    · intro h
      simpa [h] using (mem_boolCell_label P x)
  let p : α → Prop := fun x =>
      x ∈ HalmosSupport.boolCell P (↑s : Set (Fin n))
  letI : DecidablePred p := Classical.decPred _
  letI : Fintype {x : α // p x} := Fintype.ofFinite _
  change Nat.card {x : α // p x} = _
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype p]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hiff x

lemma exists_rounded_bool_family_cells {α : Type*} [Fintype α]
    (n : ℕ) (B E : Fin n → Set α) :
    ∃ E' : Fin n → Set α,
      (∀ s : Finset (Fin n),
        Nat.card {x : α //
          x ∈ HalmosSupport.boolCell E' (↑s : Set (Fin n))} =
        Nat.card {x : α //
          x ∈ HalmosSupport.boolCell B (↑s : Set (Fin n))}) ∧
      ∃ bad : Finset α,
        bad.card ≤
          ∑ s : Finset (Fin n),
            ((Finset.univ.filter
                (fun x : α => boolLabel B x = s)).card -
             min ((Finset.univ.filter
                    (fun x : α => boolLabel B x = s)).card)
                 ((Finset.univ.filter
                    (fun x : α => boolLabel E x = s)).card)) ∧
        ∀ i x, x ∉ bad -> (x ∈ E' i ↔ x ∈ E i) := by
  classical
  obtain ⟨E', hc, bad, hbad, hsame⟩ :=
    exists_rounded_bool_family n B E
  refine ⟨E', ?_, bad, hbad, hsame⟩
  intro s
  rw [boolLabel_card_cell, boolLabel_card_cell]
  exact hc s



-- The surplus bound from the rounding construction has another pleasantly
-- robust form.  It is no larger than the number of words on which the two
-- original Boolean readings already disagreed.  Taking this form avoids the
-- `min` expression when the words all have the same mass (as they do on a
-- fair block).
lemma exists_rounded_bool_family_cells_le_disagree {α : Type*} [Fintype α]
    (n : ℕ) (B E : Fin n → Set α) :
    ∃ E' : Fin n → Set α,
      (∀ s : Finset (Fin n),
        Nat.card {x : α //
          x ∈ HalmosSupport.boolCell E' (↑s : Set (Fin n))} =
        Nat.card {x : α //
          x ∈ HalmosSupport.boolCell B (↑s : Set (Fin n))}) ∧
      ∃ bad : Finset α,
        bad.card ≤
          (Finset.univ.filter (fun x : α =>
              boolLabel B x ≠ boolLabel E x)).card ∧
        ∀ i x, x ∉ bad -> (x ∈ E' i ↔ x ∈ E i) := by
  classical
  obtain ⟨E', hc, bad, hbad, hsame⟩ :=
    exists_rounded_bool_family_cells n B E
  refine ⟨E', hc, bad, ?_, hsame⟩
  refine le_trans hbad ?_
  -- Here `colorFiber` is just the filtered finset displayed in the
  -- construction.  The finite histogram inequality is independent of the
  -- ambient measurable space, hence useful even before a block is put into
  -- the Bernoulli product.
  simpa [HalmosSupport.colorFiber] using
    (HalmosSupport.sum_card_sub_min_colorFiber_le_disagree
      (c := fun x : α => boolLabel B x)
      (d := fun x : α => boolLabel E x))

-- Applying the simultaneous finite permutation on a block gives a single
-- block automorphism carrying all the cylinders in the first family to their
-- mates in the second.
lemma fairBlock_exists_map_cylinders_of_cells
    (K : Finset ℤ) (n : ℕ)
    (B E : Fin n → Set (∀ _j : (↥K), Bool))
    (hcard : ∀ s : Finset (Fin n),
      Nat.card {z : (∀ _j : (↥K), Bool) //
        z ∈ HalmosSupport.boolCell B (↑s : Set (Fin n))} =
      Nat.card {z : (∀ _j : (↥K), Bool) //
        z ∈ HalmosSupport.boolCell E (↑s : Set (Fin n))}) :
    ∃ U : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)),
      ∀ i : Fin n,
        U.toEquiv '' (cylinder (α := fun _ : ℤ => Bool) K (B i)) =
          (cylinder (α := fun _ : ℤ => Bool) K (E i)) := by
  classical
  let σ : (∀ _j : (↥K), Bool) ≃ (∀ _j : (↥K), Bool) :=
    blockPermOfCells B E hcard
  refine ⟨fairBlockAutomorphism K σ, ?_⟩
  intro i
  have hmem (z : (∀ _j : (↥K), Bool)) :
      σ z ∈ E i ↔ z ∈ B i := by
    simpa [σ] using (blockPermOfCells_mem B E hcard z i)
  have hbase :
      (σ : (∀ _j : (↥K), Bool) → (∀ _j : (↥K), Bool)) ⁻¹' (E i) = B i := by
    ext z
    exact hmem z
  have hpre :
      (fairBlockMeasurableEquiv K σ : (ℤ → Bool) → (ℤ → Bool)) ⁻¹'
        (cylinder (α := fun _ : ℤ => Bool) K (E i)) =
      cylinder (α := fun _ : ℤ => Bool) K (B i) := by
    rw [fairBlock_preimage_cylinder_same]
    rw [hbase]
  change (fairBlockMeasurableEquiv K σ : (ℤ → Bool) → (ℤ → Bool)) ''
      (cylinder (α := fun _ : ℤ => Bool) K (B i)) =
        cylinder (α := fun _ : ℤ => Bool) K (E i)
  rw [← hpre]
  exact ((fairBlockMeasurableEquiv K σ).toEquiv.image_preimage _)


-- Combining the rounding and block recoding steps: a single block
-- automorphism sends the first Boolean family exactly to a rounded version
-- of the second.  The latter differs from its target only on the words for
-- which the two original complete labels disagreed.  This has no dynamics in
-- it yet; it is the finite-cube matching datum to which a Rokhlin tower (or a
-- block model of one) has to be applied.
lemma fairBlock_exists_map_cylinders_round
    (K : Finset ℤ) (n : ℕ)
    (B E : Fin n → Set (∀ _j : (↥K), Bool)) :
    ∃ (U : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)))
      (E' : Fin n → Set (∀ _j : (↥K), Bool))
      (bad : Finset (∀ _j : (↥K), Bool)),
      bad.card ≤
        (Finset.univ.filter (fun x : (∀ _j : (↥K), Bool) =>
          boolLabel B x ≠ boolLabel E x)).card ∧
      (∀ i x, x ∉ bad → (x ∈ E' i ↔ x ∈ E i)) ∧
      (∀ i : Fin n,
        U.toEquiv '' (cylinder (α := fun _ : ℤ => Bool) K (B i)) =
          cylinder (α := fun _ : ℤ => Bool) K (E' i)) ∧
      (∀ i : Fin n,
        (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((cylinder (α := fun _ : ℤ => Bool) K (E' i)) ∆
           (cylinder (α := fun _ : ℤ => Bool) K (E i))) ≤
             (bad.card : ENNReal) * ((2 : ENNReal)⁻¹) ^ K.card) := by
  classical
  obtain ⟨E', hc, bad, hbad, hsame⟩ :=
    exists_rounded_bool_family_cells_le_disagree n B E
  obtain ⟨U, hU⟩ :=
    fairBlock_exists_map_cylinders_of_cells K n B E' (by
      intro s
      exact (hc s).symm)
  refine ⟨U, E', bad, hbad, hsame, hU, ?_⟩
  exact fairBernoulli_cylinder_symmDiff_le_bad K E' E bad hsame




lemma exists_weakMixing_of_equiv_fairBernoulli
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z)
    (e : Z ≃ᵐ (ℤ → Bool))
    (he : MeasurePreserving (e : Z → (ℤ → Bool)) μ
       (Measure.infinitePi (fun _ : ℤ => fairBool))) :
    ∃ R : Automorphism μ, IsWeaklyMixing μ R := by
  refine ⟨transportAutomorphism μ
      (Measure.infinitePi (fun _ : ℤ => fairBool)) e he
        (intShiftAutomorphism Bool fairBool), ?_⟩
  exact transport_weakMixing μ
      (Measure.infinitePi (fun _ : ℤ => fairBool)) e he
        (intShiftAutomorphism Bool fairBool)
          (intShift_weakMixing Bool fairBool)



-- A reference diffuse probability law on the real line.  At this point we
-- really do have an exact measurable equivalence, not just an isomorphism of
-- completed spaces: both carriers are uncountable standard Borel spaces.
-- Packaging this model is a convenient anchor for the later conjugacy
-- approximation question.
noncomputable def bernoulliRealEquiv : ℝ ≃ᵐ (ℤ → Bool) := by
  -- mathlib's proof of the uncountable standard-Borel isomorphism uses
  -- `ℕ → Bool` as its intermediate model.  Reindexing it by `ℤ` is a
  -- `piCongrLeft`.
  let e₁ : ℝ ≃ᵐ (ℕ → Bool) :=
    PolishSpace.measurableEquivNatBoolOfNotCountable
      (not_countable : ¬ Countable ℝ)
  let e₂ : (ℕ → Bool) ≃ᵐ (ℤ → Bool) :=
    MeasurableEquiv.piCongrLeft (fun _ : ℤ => Bool)
      (Equiv.intEquivNat.symm)
  exact e₁.trans e₂

noncomputable def bernoulliRealLaw : Measure ℝ :=
  Measure.map (bernoulliRealEquiv.symm : (ℤ → Bool) → ℝ)
    (Measure.infinitePi (fun _ : ℤ => fairBool))

noncomputable instance bernoulliRealLaw_probability :
    IsProbabilityMeasure bernoulliRealLaw := by
  unfold bernoulliRealLaw
  exact Measure.isProbabilityMeasure_map
    bernoulliRealEquiv.symm.measurable.aemeasurable

noncomputable instance bernoulliRealLaw_noAtoms :
    NoAtoms bernoulliRealLaw := by
  unfold bernoulliRealLaw
  exact noAtoms_map_measurableEquiv
    (Measure.infinitePi (fun _ : ℤ => fairBool))
      bernoulliRealEquiv.symm

lemma bernoulliRealLaw_has_weakMixing :
    ∃ R : Automorphism bernoulliRealLaw,
      IsWeaklyMixing bernoulliRealLaw R := by
  have he' : MeasurePreserving
      (bernoulliRealEquiv.symm : (ℤ → Bool) → ℝ)
      (Measure.infinitePi (fun _ : ℤ => fairBool))
      bernoulliRealLaw := by
    exact bernoulliRealEquiv.symm.measurable.measurePreserving _
  have he : MeasurePreserving
      (bernoulliRealEquiv : ℝ → (ℤ → Bool))
      bernoulliRealLaw (Measure.infinitePi (fun _ : ℤ => fairBool)) := by
    exact MeasurePreserving.symm bernoulliRealEquiv.symm he'
  exact exists_weakMixing_of_equiv_fairBernoulli
    bernoulliRealLaw bernoulliRealEquiv he


-- images carry the whole Boolean partition, not only the individual tests.
-- In particular a centre and its images have *identical* cell masses before
-- any finite-cylinder approximation. This is the bookkeeping fact behind the
-- later rounding of common blocks.
lemma image_boolCell_equiv {X Y ι : Type*}
  [Fintype ι] [DecidableEq ι]
  (e : X ≃ Y) (A : ι → Set X) (s : Set ι) :
  e '' (HalmosSupport.boolCell A s) =
    HalmosSupport.boolCell (fun i => e '' (A i)) s := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    apply (HalmosSupport.mem_boolCell).2
    intro i
    constructor
    · intro hh
      exact (HalmosSupport.mem_boolCell.1 hx i).1
        (e.injective.mem_set_image.mp hh)
    · intro hi
      exact ⟨x, (HalmosSupport.mem_boolCell.1 hx i).2 hi, rfl⟩
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (HalmosSupport.mem_boolCell).2
    intro i
    constructor
    · intro hx
      have : y ∈ e '' A i := ⟨_, hx, e.apply_symm_apply y⟩
      exact (HalmosSupport.mem_boolCell.1 hy i).1 this
    · intro hi
      have hm : y ∈ e '' A i :=
        (HalmosSupport.mem_boolCell.1 hy i).2 hi
      rcases hm with ⟨x,hx, hxe⟩
      have hxx : x = e.symm y := by
        apply e.injective
        simpa using hxe
      simpa [hxx] using hx


-- If labels are read through two different Boolean families, a point can
-- have changed its cell only by changing membership in one of the original
-- tests. The finite outside-measure union bound is useful for the rounding of
-- block atoms.
lemma boolCell_symmDiff_subset_union {Y ι : Type*} [Fintype ι]
    (A P : ι → Set Y) (s : Set ι) :
    (HalmosSupport.boolCell A s) ∆ (HalmosSupport.boolCell P s) ⊆
      ⋃ i : ι, (A i ∆ P i) := by
  classical
  intro x hx
  classical
  by_contra hn
  have hnone : x ∉ (⋃ i : ι, (A i ∆ P i)) := hn
  have hi (i : ι) : x ∈ A i ↔ x ∈ P i := by
    have hz : x ∉ A i ∆ P i := by
      intro h
      exact hnone (Set.mem_iUnion.2 ⟨i, h⟩)
    -- two booleans not different
    simp only [Set.mem_symmDiff] at hz
    tauto
  have hcell : x ∈ HalmosSupport.boolCell A s ↔
      x ∈ HalmosSupport.boolCell P s := by
    constructor
    · intro hxA
      exact (HalmosSupport.mem_boolCell).2 (by
        intro i
        rw [← hi i]
        exact (HalmosSupport.mem_boolCell.1 hxA i))
    · intro hxP
      exact (HalmosSupport.mem_boolCell).2 (by
        intro i
        rw [hi i]
        exact (HalmosSupport.mem_boolCell.1 hxP i))
  simp only [Set.mem_symmDiff] at hx
  exact (by tauto)

lemma measure_boolCell_symmDiff_le_sum
    {Y ι : Type*} [Fintype ι]
    [MeasurableSpace Y]
    (μ : Measure Y) (A P : ι → Set Y) (s : Set ι) :
    μ ((HalmosSupport.boolCell A s) ∆ (HalmosSupport.boolCell P s)) ≤
        ∑ i : ι, μ (A i ∆ P i) := by
  classical
  have sub := boolCell_symmDiff_subset_union A P s
  refine le_trans (measure_mono sub) ?_
  have h := MeasureTheory.measure_biUnion_finset_le
     (μ:=μ) (Finset.univ : Finset ι) (fun i => A i ∆ P i)
  simpa using h


-- exact invariance of the measure-distance on events under an
-- automorphism.  `measure_preimage_emb` can be used without
-- measurability hypotheses; this is important when the centre varies.
lemma automorphism_measure_image
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T : Automorphism m) (E : Set X) :
    m (T.toEquiv '' E) = m E := by
  have h := T.measurePreserving.measure_preimage_emb
      T.toEquiv.measurableEmbedding (T.toEquiv '' E)
  simpa using h.symm

lemma automorphism_boolCell_measure
    {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (m : Measure X) (T : Automorphism m)
    (A : ι → Set X) (s : Set ι) :
    m (HalmosSupport.boolCell (fun i => T.toEquiv '' (A i)) s) =
      m (HalmosSupport.boolCell A s) := by
  have himg :
      (T.toEquiv : X → X) '' (HalmosSupport.boolCell A s) =
        HalmosSupport.boolCell (fun i => T.toEquiv '' (A i)) s := by
    simpa using (image_boolCell_equiv T.toEquiv.toEquiv A s)
  rw [← himg]
  exact automorphism_measure_image m T _

lemma automorphism_measure_symmDiff_image
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T : Automorphism m) (E F : Set X) :
    m ((T.toEquiv '' E) ∆ (T.toEquiv '' F)) = m (E ∆ F) := by
  rw [← Set.image_symmDiff T.toEquiv.injective]
  exact automorphism_measure_image m T (E ∆ F)

-- A simple three-set bookkeeping inequality.  It is useful when a source
-- event and its prescribed image have first been replaced by finite-block
-- approximants.  There are three, not four, errors: pushing the error on the
-- source through an automorphism preserves it *exactly*.  Notice again that
-- no measurability hypotheses are needed for this ENNReal statement.


-- Null Boolean cells cost no neighbourhood error.  This tiny observation is
-- useful in the atomwise/tower reduction: cutting-and-stacking only has to
-- be performed on the (finitely many) positive cells.  It is deliberately
-- stated without any measurability of `E`: a measurable equivalence preserves
-- the measure of *every* image.
lemma automorphism_symmDiff_images_le_two
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T R : Automorphism m) (E : Set X) :
    m ((T.toEquiv '' E) ∆ (R.toEquiv '' E)) ≤ m E + m E := by
  have hle := MeasureTheory.measure_symmDiff_le (μ := m)
      (T.toEquiv '' E) (∅ : Set X) (R.toEquiv '' E)
  have h1 : m (((T.toEquiv '' E) ∆ (∅ : Set X))) = m E := by
    change m ((T.toEquiv '' E) ∆ (⊥ : Set X)) = m E
    rw [symmDiff_bot, automorphism_measure_image m T E]
  have h2 : m (((∅ : Set X) ∆ (R.toEquiv '' E))) = m E := by
    change m ((⊥ : Set X) ∆ (R.toEquiv '' E)) = m E
    rw [bot_symmDiff, automorphism_measure_image m R E]
  calc
    m ((T.toEquiv '' E) ∆ (R.toEquiv '' E))
      ≤ m (((T.toEquiv '' E) ∆ (∅ : Set X))) +
          m (((∅ : Set X) ∆ (R.toEquiv '' E))) := hle
    _ = m E + m E := by rw [h1, h2]

/-- The same cheap estimate can of course be read on complements.  For a
nearly conull atom this is the useful bound.  Since an equivalence is
surjective, image commutes with complement exactly. -/
lemma automorphism_symmDiff_images_le_two_compl
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T R : Automorphism m) (E : Set X) :
    m ((T.toEquiv '' E) ∆ (R.toEquiv '' E)) ≤
      m (Eᶜ) + m (Eᶜ) := by
  have h := automorphism_symmDiff_images_le_two m T R (Eᶜ)
  have hT : T.toEquiv '' (Eᶜ) = (T.toEquiv '' E)ᶜ := by
    exact Set.image_compl_eq T.toEquiv.bijective
  have hR : R.toEquiv '' (Eᶜ) = (R.toEquiv '' E)ᶜ := by
    exact Set.image_compl_eq R.toEquiv.bijective
  rw [hT, hR] at h
  -- `(Aᶜ ∆ Bᶜ) = A ∆ B` in any Boolean algebra
  simpa only [compl_symmDiff_compl] using h

lemma automorphism_null_symmDiff_images
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T R : Automorphism m) (E : Set X) (hE : m E = 0) :
    m ((T.toEquiv '' E) ∆ (R.toEquiv '' E)) = 0 := by
  have hT : m (T.toEquiv '' E) = 0 := by
    rw [automorphism_measure_image m T E, hE]
  have hR : m (R.toEquiv '' E) = 0 := by
    rw [automorphism_measure_image m R E, hE]
  have hle := MeasureTheory.measure_symmDiff_le (μ := m)
      (T.toEquiv '' E) (∅ : Set X) (R.toEquiv '' E)
  have hz : m (((T.toEquiv '' E) ∆ (∅ : Set X))) +
        m (((∅ : Set X) ∆ (R.toEquiv '' E))) = (0 : ENNReal) := by
    change m ((T.toEquiv '' E) ∆ (⊥ : Set X)) +
        m ((⊥ : Set X) ∆ (R.toEquiv '' E)) = (0 : ENNReal)
    rw [symmDiff_bot, bot_symmDiff, hT, hR]
    exact add_zero _
  have h : m ((T.toEquiv '' E) ∆ (R.toEquiv '' E)) ≤ (0 : ENNReal) := by
    simpa [hz] using (show
      m ((T.toEquiv '' E) ∆ (R.toEquiv '' E)) ≤
        m (((T.toEquiv '' E) ∆ (∅ : Set X))) +
          m (((∅ : Set X) ∆ (R.toEquiv '' E))) from hle)
  exact bot_unique h

-- The dual edge case (a conull cell) also carries no matching data.  Passing
-- to complements is safe because an equivalence is onto; this keeps all
-- measure statements at the set level, with no measurability assumption.
lemma automorphism_conull_symmDiff_images
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T R : Automorphism m) (E : Set X) (hE : m (Eᶜ) = 0) :
    m ((T.toEquiv '' E) ∆ (R.toEquiv '' E)) = 0 := by
  have h := automorphism_null_symmDiff_images m T R (Eᶜ) hE
  have hT : T.toEquiv '' (Eᶜ) = (T.toEquiv '' E)ᶜ := by
    exact Set.image_compl_eq T.toEquiv.bijective
  have hR : R.toEquiv '' (Eᶜ) = (R.toEquiv '' E)ᶜ := by
    exact Set.image_compl_eq R.toEquiv.bijective
  rw [hT, hR] at h
  -- the symmetric difference is unchanged after complementing both sides
  change m ((T.toEquiv '' E) ∆ (R.toEquiv '' E)) = 0
  simpa only [compl_symmDiff_compl] using h

lemma automorphism_image_error_le_three
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T R : Automorphism m) (A D F : Set X) :
    m ((T.toEquiv '' A) ∆ (R.toEquiv '' A)) ≤
       (m (A ∆ D) + m ((T.toEquiv '' D) ∆ F)) +
         m (F ∆ (R.toEquiv '' A)) := by
  have h1 := MeasureTheory.measure_symmDiff_le (μ := m)
    (T.toEquiv '' A) (T.toEquiv '' D) (R.toEquiv '' A)
  have h2 := MeasureTheory.measure_symmDiff_le (μ := m)
    (T.toEquiv '' D) F (R.toEquiv '' A)
  calc
    m ((T.toEquiv '' A) ∆ (R.toEquiv '' A))
        ≤ m ((T.toEquiv '' A) ∆ (T.toEquiv '' D)) +
          m ((T.toEquiv '' D) ∆ (R.toEquiv '' A)) := h1
    _ ≤ m ((T.toEquiv '' A) ∆ (T.toEquiv '' D)) +
          (m ((T.toEquiv '' D) ∆ F) +
             m (F ∆ (R.toEquiv '' A))) :=
        add_le_add_right h2 _
    _ = _ := by
      rw [automorphism_measure_symmDiff_image m T A D]
      simp [add_assoc]

lemma automorphism_image_error_of_sum_lt
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T R : Automorphism m) (A D F : Set X) {r : ENNReal}
    (hs : (m (A ∆ D) + m ((T.toEquiv '' D) ∆ F)) +
          m (F ∆ (R.toEquiv '' A)) < r) :
    m ((T.toEquiv '' A) ∆ (R.toEquiv '' A)) < r :=
  lt_of_le_of_lt (automorphism_image_error_le_three m T R A D F) hs


-- A common cylinder commutes exactly with taking the Boolean cells of its
-- bases. No approximation occurs at this stage: restriction to a finite
-- block is an ordinary function.
lemma cylinder_boolCell
  (K : Finset ℤ) (ι : Type*) [Fintype ι]
  (B : ι → Set (∀ _j : (↥K), Bool)) (s : Set ι) :
    (cylinder (α := fun _ : ℤ => Bool) K
        (HalmosSupport.boolCell B s)) =
      HalmosSupport.boolCell
        (fun i => cylinder (α := fun _ : ℤ => Bool) K (B i)) s := by
  classical
  ext w
  -- membership through restrict
  simp only [mem_cylinder]
  exact Iff.rfl


-- Consequently the error on a whole cell is bounded by the sum of the
-- errors of the tests. Keeping this in ENNReal avoids null-measurable side
-- conditions and makes it directly applicable to the weak subbasic balls.
lemma fairBernoulli_boolCell_of_common_block_le
    {ι : Type*} [Fintype ι]
    (K : Finset ℤ)
    (B : ι → Set (∀ _j : (↥K), Bool))
    (A : ι → Set (ℤ → Bool)) (δ : ι → ENNReal)
    (h : ∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
        ((cylinder (α := fun _ : ℤ => Bool) K (B i)) ∆ A i) < δ i)
    (s : Set ι) :
    (Measure.infinitePi (fun _ : ℤ => fairBool))
      ((cylinder (α := fun _ : ℤ => Bool) K
          (HalmosSupport.boolCell B s)) ∆
           HalmosSupport.boolCell A s)
      ≤ ∑ i : ι, δ i := by
  classical
  rw [cylinder_boolCell K ι B s]
  let μ : Measure (ℤ → Bool) :=
      Measure.infinitePi (fun _ : ℤ => fairBool)
  let C : ι → Set (ℤ → Bool) :=
      fun i => cylinder (α := fun _ : ℤ => Bool) K (B i)
  change μ ((HalmosSupport.boolCell C s) ∆
        HalmosSupport.boolCell A s) ≤ _
  have hb := measure_boolCell_symmDiff_le_sum μ C A s
  refine le_trans hb ?_
  exact Finset.sum_le_sum (fun i hi => le_of_lt (h i))

lemma fairBernoulli_boolCell_cylinder_mass_card
    {ι : Type*} [Fintype ι]
    (K : Finset ℤ) (B : ι → Set (∀ _j : (↥K), Bool))
    (hB : ∀ i, MeasurableSet (B i)) (s : Set ι) :
    (Measure.infinitePi (fun _ : ℤ => fairBool))
      (cylinder (α := fun _ : ℤ => Bool) K
        (HalmosSupport.boolCell B s)) =
      (Nat.card { z : (∀ _j : (↥K), Bool) //
          z ∈ HalmosSupport.boolCell B s} : ENNReal) *
          ((2 : ENNReal)⁻¹) ^ K.card := by
  classical
  have hm : MeasurableSet (HalmosSupport.boolCell B s) :=
    HalmosSupport.measurableSet_boolCell hB s
  have hc := fairBernoulli_cylinder_mass_card K
     (HalmosSupport.boolCell B s) hm
  -- for a finite carrier the two cardinalities in the formula are literally
  -- `Nat.card` of its subtype.
  have heq : (HalmosSupport.boolCell B s).toFinite.toFinset.card =
      Nat.card { z : (∀ _j : (↥K), Bool) //
          z ∈ HalmosSupport.boolCell B s} := by
    simpa [Nat.card_eq_fintype_card] using
      (Set.ncard_eq_toFinset_card' (HalmosSupport.boolCell B s)).symm
  rw [heq] at hc
  exact hc

-- A quantitative form of the simultaneous matching statement. Once Boolean
-- atoms on a common cube have the same cardinalities, no approximate
-- argument about overlapping events remains: the corresponding block
-- automorphism puts the source cylinders on the target cylinders *exactly*.
-- Thus the only two errors are replacing the events on either side by their
-- cylinders. This isolates the future rounding/tower step from the very
-- mundane triangle inequality.
lemma fairBernoulli_block_approximation_of_cell_cards
    (n : ℕ)
    (R₀ : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)))
    (A : Fin n → Set (ℤ → Bool))
    (K : Finset ℤ)
    (B E : Fin n → Set (∀ _j : (↥K), Bool))
    (η θ : Fin n → ENNReal)
    (hBclose : ∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((cylinder (α := fun _ : ℤ => Bool) K (B i)) ∆ A i) < η i)
    (hEclose : ∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((cylinder (α := fun _ : ℤ => Bool) K (E i)) ∆
              (R₀.toEquiv '' (A i))) < θ i)
    (hcard : ∀ s : Finset (Fin n),
      Nat.card {z : (∀ _j : (↥K), Bool) //
        z ∈ HalmosSupport.boolCell B (↑s : Set (Fin n))} =
      Nat.card {z : (∀ _j : (↥K), Bool) //
        z ∈ HalmosSupport.boolCell E (↑s : Set (Fin n))}) :
    ∃ U : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)),
      ∀ i : Fin n,
        (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((U.toEquiv '' A i) ∆ (R₀.toEquiv '' A i)) < η i + θ i := by
  classical
  let μ : Measure (ℤ → Bool) :=
      Measure.infinitePi (fun _ : ℤ => fairBool)
  obtain ⟨U,hU⟩ := fairBlock_exists_map_cylinders_of_cells K n B E hcard
  refine ⟨U, ?_⟩
  intro i
  let D : Set (ℤ → Bool) := cylinder (α := fun _ : ℤ => Bool) K (B i)
  let F : Set (ℤ → Bool) := cylinder (α := fun _ : ℤ => Bool) K (E i)
  have hDF : U.toEquiv '' D = F := by
    dsimp [D, F]
    exact hU i
  have hzero : μ ((U.toEquiv '' D) ∆ F) = 0 := by
    rw [hDF]
    simp
  have hsymA : μ (A i ∆ D) < η i := by
    dsimp [D]
    -- the approximation lemma writes the symmetric difference in the other
    -- order.
    simpa [symmDiff_comm] using (hBclose i)
  have hlast : μ (F ∆ (R₀.toEquiv '' (A i))) < θ i := by
    simpa [μ, F] using (hEclose i)
  change μ ((U.toEquiv '' A i) ∆ (R₀.toEquiv '' A i)) < _
  have hle := automorphism_image_error_le_three μ U R₀ (A i) D F
  -- after the exact cylinder match the middle term of the bound is zero;
  -- strict addition in ENNReal avoids any finiteness/coercion detour.
  have hsum :
       (μ (A i ∆ D) + μ ((U.toEquiv '' D) ∆ F)) +
          μ (F ∆ (R₀.toEquiv '' A i)) < η i + θ i := by
    rw [hzero]
    simp only [add_zero]
    exact ENNReal.add_lt_add hsymA hlast
  exact lt_of_le_of_lt hle hsum

-- A version with the outside errors reinstated.  It stops at a *finite block
-- automorphism* (not a mixing one): turning that automorphism into a
-- conjugate of a Bernoulli shift is exactly the remaining dynamical step.
-- All the rounding/error accounting has disappeared into the count of bad
-- words.
lemma fairBernoulli_block_approximation_round
    (n : ℕ)
    (R₀ : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)))
    (A : Fin n → Set (ℤ → Bool)) (K : Finset ℤ)
    (B E : Fin n → Set (∀ _j : (↥K), Bool))
    (η θ : Fin n → ENNReal)
    (hBclose : ∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((cylinder (α := fun _ : ℤ => Bool) K (B i)) ∆ A i) < η i)
    (hEclose : ∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((cylinder (α := fun _ : ℤ => Bool) K (E i)) ∆
            (R₀.toEquiv '' A i)) < θ i) :
    ∃ (U : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)))
      (b : ℕ),
      b ≤ (Finset.univ.filter (fun x : (∀ _j : (↥K), Bool) =>
          boolLabel B x ≠ boolLabel E x)).card ∧
      ∀ i : Fin n,
        (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((U.toEquiv '' A i) ∆ (R₀.toEquiv '' A i)) ≤
            (η i + (b : ENNReal) * ((2 : ENNReal)⁻¹) ^ K.card) + θ i := by
  classical
  let μ : Measure (ℤ → Bool) :=
      Measure.infinitePi (fun _ : ℤ => fairBool)
  obtain ⟨U, E', bad, hbad, hsame, himg, hcost⟩ :=
    fairBlock_exists_map_cylinders_round K n B E
  refine ⟨U, bad.card, hbad, ?_⟩
  intro i
  let D : Set (ℤ → Bool) :=
    cylinder (α := fun _ : ℤ => Bool) K (B i)
  let F' : Set (ℤ → Bool) :=
    cylinder (α := fun _ : ℤ => Bool) K (E' i)
  let F : Set (ℤ → Bool) :=
    cylinder (α := fun _ : ℤ => Bool) K (E i)
  have hmid : μ ((U.toEquiv '' D) ∆ F) ≤
      (bad.card : ENNReal) * ((2 : ENNReal)⁻¹) ^ K.card := by
    have hDF : U.toEquiv '' D = F' := by
      dsimp [D, F']
      exact himg i
    rw [hDF]
    -- this is precisely the bad-cylinder estimate, with the abbreviations
    -- unfolded only at the last moment
    simpa [μ, F', F] using (hcost i)
  have hfirst : μ (A i ∆ D) ≤ η i := by
    exact le_of_lt (by
      simpa [μ, D, symmDiff_comm] using (hBclose i))
  have hlast : μ (F ∆ (R₀.toEquiv '' A i)) ≤ θ i := by
    exact le_of_lt (by simpa [μ, F] using (hEclose i))
  have hle := automorphism_image_error_le_three μ U R₀ (A i) D F
  -- after grouping the three contributions this is just monotonicity of
  -- addition in `ENNReal`; no subtraction or finiteness arguments enter.
  exact hle.trans (by
    calc
      (μ (A i ∆ D) + μ ((U.toEquiv '' D) ∆ F)) +
            μ (F ∆ (R₀.toEquiv '' A i))
          ≤ (η i +
              (bad.card : ENNReal) * ((2 : ENNReal)⁻¹) ^ K.card) +
              θ i := add_le_add (add_le_add hfirst hmid) hlast
      _ = _ := rfl)


-- A one-sided version of the triangle inequality for the distance of
-- events.  Writing it without any subtraction is convenient in `ENNReal`,
-- and it needs no measurability assumptions.  In the common-block rounding
-- step the two middle events need not be the *same* set: it is enough that
-- their measures agree (one is the image of the other under the centre).
lemma measure_le_symmDiff_add {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (P S : Set Y) :
    μ P ≤ μ (P ∆ S) + μ S := by
  have h := MeasureTheory.measure_symmDiff_le (μ := μ) P S (∅ : Set Y)
  -- rewrite the empty set as the bottom element of the set Boolean algebra
  change μ (P ∆ (⊥ : Set Y)) ≤ μ (P ∆ S) + μ (S ∆ (⊥ : Set Y)) at h
  simpa only [symmDiff_bot] using h

lemma measure_le_two_symmDiff_add_of_eq
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (P S T Q : Set Y) (hST : μ S = μ T) :
    μ P ≤ (μ (P ∆ S) + μ (T ∆ Q)) + μ Q := by
  have h1 : μ P ≤ μ (P ∆ S) + μ S := measure_le_symmDiff_add μ P S
  have h2 : μ T ≤ μ (T ∆ Q) + μ Q := measure_le_symmDiff_add μ T Q
  calc
    μ P ≤ μ (P ∆ S) + μ S := h1
    _ = μ (P ∆ S) + μ T := by rw [hST]
    _ ≤ μ (P ∆ S) + (μ (T ∆ Q) + μ Q) :=
        (by simpa [add_comm] using (add_le_add_left h2 (μ (P ∆ S))))
    _ = (μ (P ∆ S) + μ (T ∆ Q)) + μ Q := by
        rw [add_assoc]

-- The price of the histogram surplus of two Boolean readings of a *single
-- common block*.  The actual events on the two sides may not coincide, but
-- if their Boolean cells have equal measure then only the two outside
-- approximation errors matter.  This is the finite accounting step preceding
-- a tower construction; it does not assert that the resulting block map is
-- mixing.
lemma fairBernoulli_histogram_surplus_mul_le
    (n : ℕ)
    (R₀ : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)))
    (A : Fin n → Set (ℤ → Bool))
    (K : Finset ℤ)
    (B E : Fin n → Set (∀ _j : (↥K), Bool))
    (hB : ∀ i, MeasurableSet (B i))
    (hE : ∀ i, MeasurableSet (E i)) :
    let a : Finset (Fin n) → ℕ := fun t =>
      (Finset.univ.filter (fun x : (∀ _j : (↥K), Bool) =>
        boolLabel B x = t)).card
    let b : Finset (Fin n) → ℕ := fun t =>
      (Finset.univ.filter (fun x : (∀ _j : (↥K), Bool) =>
        boolLabel E x = t)).card
    let μ : Measure (ℤ → Bool) :=
      Measure.infinitePi (fun _ : ℤ => fairBool)
    let PB : Finset (Fin n) → Set (ℤ → Bool) := fun t =>
      cylinder (α := fun _ : ℤ => Bool) K
        (HalmosSupport.boolCell B (↑t : Set (Fin n)))
    let QE : Finset (Fin n) → Set (ℤ → Bool) := fun t =>
      cylinder (α := fun _ : ℤ => Bool) K
        (HalmosSupport.boolCell E (↑t : Set (Fin n)))
    let SA : Finset (Fin n) → Set (ℤ → Bool) := fun t =>
      HalmosSupport.boolCell A (↑t : Set (Fin n))
    let TA : Finset (Fin n) → Set (ℤ → Bool) := fun t =>
      HalmosSupport.boolCell (fun i => R₀.toEquiv '' (A i))
        (↑t : Set (Fin n))
    ((∑ t : Finset (Fin n), (a t - min (a t) (b t))) : ENNReal) *
        ((2 : ENNReal)⁻¹) ^ K.card ≤
      ∑ t : Finset (Fin n),
        (μ ((PB t) ∆ (SA t)) + μ ((TA t) ∆ (QE t))) := by
  classical
  dsimp
  let μ : Measure (ℤ → Bool) :=
      Measure.infinitePi (fun _ : ℤ => fairBool)
  let w : ENNReal := ((2 : ENNReal)⁻¹) ^ K.card
  let a : Finset (Fin n) → ℕ := fun t =>
      (Finset.univ.filter (fun x : (∀ _j : (↥K), Bool) =>
        boolLabel B x = t)).card
  let b : Finset (Fin n) → ℕ := fun t =>
      (Finset.univ.filter (fun x : (∀ _j : (↥K), Bool) =>
        boolLabel E x = t)).card
  let PB : Finset (Fin n) → Set (ℤ → Bool) := fun t =>
      cylinder (α := fun _ : ℤ => Bool) K
        (HalmosSupport.boolCell B (↑t : Set (Fin n)))
  let QE : Finset (Fin n) → Set (ℤ → Bool) := fun t =>
      cylinder (α := fun _ : ℤ => Bool) K
        (HalmosSupport.boolCell E (↑t : Set (Fin n)))
  let SA : Finset (Fin n) → Set (ℤ → Bool) := fun t =>
      HalmosSupport.boolCell A (↑t : Set (Fin n))
  let TA : Finset (Fin n) → Set (ℤ → Bool) := fun t =>
      HalmosSupport.boolCell (fun i => R₀.toEquiv '' (A i))
         (↑t : Set (Fin n))
  have hw : w ≠ (⊤ : ENNReal) := by
    dsimp [w]
    -- the word mass is a finite power of one half
    apply ne_of_lt
    exact ENNReal.pow_lt_top
      ((ENNReal.inv_lt_top).2 (by norm_num : (0 : ENNReal) < 2))
  have hmassB (t : Finset (Fin n)) : μ (PB t) = (a t : ENNReal) * w := by
    dsimp [PB]
    rw [fairBernoulli_boolCell_cylinder_mass_card K B hB (↑t : Set (Fin n))]
    congr 1
    -- `Nat.card` of a Boolean cell is its label fibre
    exact congrArg (fun m : ℕ => (m : ENNReal))
      (boolLabel_card_cell B t)
  have hmassE (t : Finset (Fin n)) : μ (QE t) = (b t : ENNReal) * w := by
    dsimp [QE]
    rw [fairBernoulli_boolCell_cylinder_mass_card K E hE (↑t : Set (Fin n))]
    congr 1
    exact congrArg (fun m : ℕ => (m : ENNReal))
      (boolLabel_card_cell E t)
  have hcellEq (t : Finset (Fin n)) : μ (SA t) = μ (TA t) := by
    dsimp [SA, TA]
    -- the centre is an actual measurable equivalence, so it carries the
    -- whole Boolean cell, not merely each generator separately.
    exact (automorphism_boolCell_measure μ R₀ A
      (↑t : Set (Fin n))).symm
  change ((∑ t : Finset (Fin n),
      (a t - min (a t) (b t))) : ENNReal) * w ≤
    ∑ t : Finset (Fin n),
      (μ (PB t ∆ SA t) + μ (TA t ∆ QE t))
  -- Apply the completely algebraic cast lemma colour by colour.  The
  -- hypothesis `a*w ≤ L + b*w` follows from two triangles and the equality
  -- of the middle cell masses.
  apply HalmosSupport.sum_nat_sub_min_cast_mul_le_of_le_add
    a b w hw (fun t => μ (PB t ∆ SA t) + μ (TA t ∆ QE t))
  intro t
  rw [← hmassB t, ← hmassE t]
  exact measure_le_two_symmDiff_add_of_eq μ (PB t) (SA t) (TA t) (QE t)
    (hcellEq t)

-- In particular small errors for the original tests give a uniform error
-- for the *histogram* retained by rounding.  There are only `2^n` Boolean
-- labels, so their discrepancies can safely be summed.  This is sharper than
-- comparing the words on which the two readings disagree: source and target
-- events need not overlap as subsets of the common cube.
lemma fairBernoulli_histogram_surplus_mul_le_of_close
    (n : ℕ)
    (R₀ : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)))
    (A : Fin n → Set (ℤ → Bool))
    (K : Finset ℤ)
    (B E : Fin n → Set (∀ _j : (↥K), Bool))
    (hB : ∀ i, MeasurableSet (B i))
    (hE : ∀ i, MeasurableSet (E i))
    (η θ : Fin n → ENNReal)
    (hBc : ∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
       ((cylinder (α := fun _ : ℤ => Bool) K (B i)) ∆ A i) < η i)
    (hEc : ∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
       ((cylinder (α := fun _ : ℤ => Bool) K (E i)) ∆
         (R₀.toEquiv '' (A i))) < θ i) :
    let a : Finset (Fin n) → ℕ := fun t =>
      (Finset.univ.filter (fun x : (∀ _j : (↥K), Bool) =>
        boolLabel B x = t)).card
    let b : Finset (Fin n) → ℕ := fun t =>
      (Finset.univ.filter (fun x : (∀ _j : (↥K), Bool) =>
        boolLabel E x = t)).card
    ((∑ t : Finset (Fin n), (a t - min (a t) (b t))) : ENNReal) *
        ((2 : ENNReal)⁻¹) ^ K.card ≤
        Fintype.card (Finset (Fin n)) •
          ((∑ i : Fin n, η i) + (∑ i : Fin n, θ i)) := by
  classical
  dsimp
  let μ : Measure (ℤ → Bool) :=
     Measure.infinitePi (fun _ : ℤ => fairBool)
  let PB : Finset (Fin n) → Set (ℤ → Bool) := fun t =>
      cylinder (α := fun _ : ℤ => Bool) K
        (HalmosSupport.boolCell B (↑t : Set (Fin n)))
  let QE : Finset (Fin n) → Set (ℤ → Bool) := fun t =>
      cylinder (α := fun _ : ℤ => Bool) K
        (HalmosSupport.boolCell E (↑t : Set (Fin n)))
  let SA : Finset (Fin n) → Set (ℤ → Bool) := fun t =>
      HalmosSupport.boolCell A (↑t : Set (Fin n))
  let TA : Finset (Fin n) → Set (ℤ → Bool) := fun t =>
      HalmosSupport.boolCell (fun i => R₀.toEquiv '' (A i))
        (↑t : Set (Fin n))
  have hb0 := fairBernoulli_histogram_surplus_mul_le n R₀ A K B E hB hE
  -- abbreviations in the preceding lemma are merely `let`s
  dsimp at hb0
  have hleft (t : Finset (Fin n)) : μ ((PB t) ∆ (SA t)) ≤
        ∑ i : Fin n, η i := by
    dsimp [μ, PB, SA]
    exact fairBernoulli_boolCell_of_common_block_le K B A η hBc
      (↑t : Set (Fin n))
  have hright (t : Finset (Fin n)) : μ ((TA t) ∆ (QE t)) ≤
        ∑ i : Fin n, θ i := by
    have hh := fairBernoulli_boolCell_of_common_block_le K E
      (fun i => R₀.toEquiv '' (A i)) θ hEc (↑t : Set (Fin n))
    simpa [μ, QE, TA, symmDiff_comm] using hh
  calc
    ((∑ t : Finset (Fin n),
        ((Finset.univ.filter (fun x : (∀ _j : (↥K), Bool) =>
           boolLabel B x = t)).card -
         min ((Finset.univ.filter (fun x : (∀ _j : (↥K), Bool) =>
           boolLabel B x = t)).card)
             ((Finset.univ.filter (fun x : (∀ _j : (↥K), Bool) =>
           boolLabel E x = t)).card))) : ENNReal) *
          ((2 : ENNReal)⁻¹) ^ K.card
        ≤ ∑ t : Finset (Fin n),
            (μ ((PB t) ∆ (SA t)) + μ ((TA t) ∆ (QE t))) := by
              simpa [μ, PB, QE, SA, TA] using hb0
    _ ≤ ∑ _t : Finset (Fin n),
          ((∑ i : Fin n, η i) + (∑ i : Fin n, θ i)) :=
          Finset.sum_le_sum (by
            intro t ht
            exact add_le_add (hleft t) (hright t))
    _ = Fintype.card (Finset (Fin n)) •
          ((∑ i : Fin n, η i) + (∑ i : Fin n, θ i)) := by
            simp

-- Using the sharper histogram form of the rounding lemma, negligible
-- outside errors already give a finite-block automorphism close to the
-- prescribed centre on every test.  No weak-mixing assertion is made here;
-- replacing this block automorphism by a conjugate of the bilateral shift is
-- precisely the remaining Rokhlin step.
lemma fairBernoulli_block_approximation_round_hist
    (n : ℕ)
    (R₀ : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)))
    (A : Fin n → Set (ℤ → Bool))
    (K : Finset ℤ)
    (B E : Fin n → Set (∀ _j : (↥K), Bool))
    (hB : ∀ i, MeasurableSet (B i))
    (hE : ∀ i, MeasurableSet (E i))
    (η θ : Fin n → ENNReal)
    (hBc : ∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
       ((cylinder (α := fun _ : ℤ => Bool) K (B i)) ∆ A i) < η i)
    (hEc : ∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
       ((cylinder (α := fun _ : ℤ => Bool) K (E i)) ∆
         (R₀.toEquiv '' (A i))) < θ i) :
    ∃ U : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)),
      ∀ i : Fin n,
        (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((U.toEquiv '' (A i)) ∆ (R₀.toEquiv '' (A i))) ≤
          (η i +
             (Fintype.card (Finset (Fin n)) •
                ((∑ j : Fin n, η j) + (∑ j : Fin n, θ j)))) + θ i := by
  classical
  let μ : Measure (ℤ → Bool) :=
     Measure.infinitePi (fun _ : ℤ => fairBool)
  -- keep the surplus bound (rather than the cruder disagreement estimate)
  obtain ⟨E', hc, bad, hbad, hsame⟩ :=
    exists_rounded_bool_family_cells n B E
  obtain ⟨U, hU⟩ := fairBlock_exists_map_cylinders_of_cells K n B E'
    (by intro t; exact (hc t).symm)
  refine ⟨U, ?_⟩
  have hbadmass : (bad.card : ENNReal) * ((2 : ENNReal)⁻¹) ^ K.card ≤
        Fintype.card (Finset (Fin n)) •
          ((∑ j : Fin n, η j) + (∑ j : Fin n, θ j)) := by
    have hcast : (bad.card : ENNReal) ≤
        ((∑ t : Finset (Fin n),
          ((Finset.univ.filter
              (fun x : (∀ _j : (↥K), Bool) => boolLabel B x = t)).card -
            min ((Finset.univ.filter
              (fun x : (∀ _j : (↥K), Bool) => boolLabel B x = t)).card)
                ((Finset.univ.filter
                   (fun x : (∀ _j : (↥K), Bool) => boolLabel E x = t)).card))) : ℕ) := by
      exact_mod_cast hbad
    have hmul : (bad.card : ENNReal) * ((2 : ENNReal)⁻¹) ^ K.card ≤
        (((∑ t : Finset (Fin n),
          ((Finset.univ.filter
              (fun x : (∀ _j : (↥K), Bool) => boolLabel B x = t)).card -
            min ((Finset.univ.filter
              (fun x : (∀ _j : (↥K), Bool) => boolLabel B x = t)).card)
                ((Finset.univ.filter
                   (fun x : (∀ _j : (↥K), Bool) => boolLabel E x = t)).card))) : ℕ) : ENNReal) *
              ((2 : ENNReal)⁻¹) ^ K.card :=
      mul_le_mul_right' hcast _
    refine hmul.trans ?_
    convert (fairBernoulli_histogram_surplus_mul_le_of_close
        n R₀ A K B E hB hE η θ hBc hEc) using 1 <;>
      (first | simp only [Nat.cast_sum, ENNReal.natCast_sub] | rfl | exact Subsingleton.elim _ _)
  intro i
  let D : Set (ℤ → Bool) :=
    cylinder (α := fun _ : ℤ => Bool) K (B i)
  let F' : Set (ℤ → Bool) :=
    cylinder (α := fun _ : ℤ => Bool) K (E' i)
  let F : Set (ℤ → Bool) :=
    cylinder (α := fun _ : ℤ => Bool) K (E i)
  have hmid : μ ((U.toEquiv '' D) ∆ F) ≤
      (bad.card : ENNReal) * ((2 : ENNReal)⁻¹) ^ K.card := by
    have hDF : U.toEquiv '' D = F' := by
      dsimp [D, F']; exact hU i
    rw [hDF]
    -- the changed labels are a subset of the bad words
    simpa [μ, F', F] using
      (fairBernoulli_cylinder_symmDiff_le_bad K E' E bad hsame i)
  have hfirst : μ (A i ∆ D) ≤ η i :=
    le_of_lt (by simpa [μ, D, symmDiff_comm] using (hBc i))
  have hlast : μ (F ∆ (R₀.toEquiv '' A i)) ≤ θ i :=
    le_of_lt (by simpa [μ, F] using (hEc i))
  have hle := automorphism_image_error_le_three μ U R₀ (A i) D F
  exact hle.trans (by
    calc
      (μ (A i ∆ D) + μ ((U.toEquiv '' D) ∆ F)) +
            μ (F ∆ (R₀.toEquiv '' A i))
        ≤ (η i +
             (Fintype.card (Finset (Fin n)) •
                ((∑ j : Fin n, η j) + (∑ j : Fin n, θ j)))) + θ i :=
          add_le_add (add_le_add hfirst (hmid.trans hbadmass)) hlast)


-- Keeping track of the particular automorphism in the histogram argument is
-- important for the (still dynamical) tower step.  The existential in
-- `fairBernoulli_block_approximation_round_hist` can be chosen to be an honest
-- finite-block permutation.  Thus the missing approximation need only replace
-- maps of this very concrete shape, rather than arbitrary automorphisms.
lemma fairBernoulli_block_approximation_round_hist_block
    (n : ℕ)
    (R₀ : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)))
    (A : Fin n → Set (ℤ → Bool))
    (K : Finset ℤ)
    (B E : Fin n → Set (∀ _j : (↥K), Bool))
    (hB : ∀ i, MeasurableSet (B i))
    (hE : ∀ i, MeasurableSet (E i))
    (η θ : Fin n → ENNReal)
    (hBc : ∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
       ((cylinder (α := fun _ : ℤ => Bool) K (B i)) ∆ A i) < η i)
    (hEc : ∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
       ((cylinder (α := fun _ : ℤ => Bool) K (E i)) ∆
         (R₀.toEquiv '' (A i))) < θ i) :
    ∃ σ : (∀ _j : (↥K), Bool) ≃ (∀ _j : (↥K), Bool),
      ∀ i : Fin n,
        (Measure.infinitePi (fun _ : ℤ => fairBool))
          (((fairBlockAutomorphism K σ).toEquiv '' (A i)) ∆
            (R₀.toEquiv '' (A i))) ≤
          (η i +
             (Fintype.card (Finset (Fin n)) •
                ((∑ j : Fin n, η j) + (∑ j : Fin n, θ j)))) + θ i := by
  classical
  let μ : Measure (ℤ → Bool) :=
     Measure.infinitePi (fun _ : ℤ => fairBool)
  obtain ⟨E', hc, bad, hbad, hsame⟩ :=
    exists_rounded_bool_family_cells n B E
  -- write the simultaneous finite permutation explicitly
  let hcards : ∀ s : Finset (Fin n),
      Nat.card {z : (∀ _j : (↥K), Bool) //
        z ∈ HalmosSupport.boolCell B (↑s : Set (Fin n))} =
      Nat.card {z : (∀ _j : (↥K), Bool) //
        z ∈ HalmosSupport.boolCell E' (↑s : Set (Fin n))} :=
        fun s => (hc s).symm
  let σ : (∀ _j : (↥K), Bool) ≃ (∀ _j : (↥K), Bool) :=
    blockPermOfCells B E' hcards
  let U : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)) :=
    fairBlockAutomorphism K σ
  have himg (i : Fin n) :
      U.toEquiv '' (cylinder (α := fun _ : ℤ => Bool) K (B i)) =
        cylinder (α := fun _ : ℤ => Bool) K (E' i) := by
    -- same computation as in the simultaneous-cells lemma, but with the
    -- named permutation above so that later a tower hypothesis can mention it
    have hmem (z : (∀ _j : (↥K), Bool)) :
        σ z ∈ E' i ↔ z ∈ B i := by
      simpa [σ] using (blockPermOfCells_mem B E' hcards z i)
    have hbase :
        (σ : (∀ _j : (↥K), Bool) → (∀ _j : (↥K), Bool)) ⁻¹' (E' i) = B i := by
      ext z
      exact hmem z
    have hpre :
        (fairBlockMeasurableEquiv K σ : (ℤ → Bool) → (ℤ → Bool)) ⁻¹'
          (cylinder (α := fun _ : ℤ => Bool) K (E' i)) =
        cylinder (α := fun _ : ℤ => Bool) K (B i) := by
      rw [fairBlock_preimage_cylinder_same]
      rw [hbase]
    change (fairBlockMeasurableEquiv K σ : (ℤ → Bool) → (ℤ → Bool)) ''
        (cylinder (α := fun _ : ℤ => Bool) K (B i)) =
          cylinder (α := fun _ : ℤ => Bool) K (E' i)
    rw [← hpre]
    exact ((fairBlockMeasurableEquiv K σ).toEquiv.image_preimage _)
  refine ⟨σ, ?_⟩
  have hbadmass : (bad.card : ENNReal) * ((2 : ENNReal)⁻¹) ^ K.card ≤
        Fintype.card (Finset (Fin n)) •
          ((∑ j : Fin n, η j) + (∑ j : Fin n, θ j)) := by
    have hcast : (bad.card : ENNReal) ≤
        ((∑ t : Finset (Fin n),
          ((Finset.univ.filter
              (fun x : (∀ _j : (↥K), Bool) => boolLabel B x = t)).card -
            min ((Finset.univ.filter
              (fun x : (∀ _j : (↥K), Bool) => boolLabel B x = t)).card)
                ((Finset.univ.filter
                   (fun x : (∀ _j : (↥K), Bool) => boolLabel E x = t)).card))) : ℕ) := by
      exact_mod_cast hbad
    have hmul : (bad.card : ENNReal) * ((2 : ENNReal)⁻¹) ^ K.card ≤
        (((∑ t : Finset (Fin n),
          ((Finset.univ.filter
              (fun x : (∀ _j : (↥K), Bool) => boolLabel B x = t)).card -
            min ((Finset.univ.filter
              (fun x : (∀ _j : (↥K), Bool) => boolLabel B x = t)).card)
                ((Finset.univ.filter
                   (fun x : (∀ _j : (↥K), Bool) => boolLabel E x = t)).card))) : ℕ) : ENNReal) *
              ((2 : ENNReal)⁻¹) ^ K.card :=
      mul_le_mul_right' hcast _
    refine hmul.trans ?_
    convert (fairBernoulli_histogram_surplus_mul_le_of_close
        n R₀ A K B E hB hE η θ hBc hEc) using 1 <;>
      (first | simp only [Nat.cast_sum, ENNReal.natCast_sub] | rfl | exact Subsingleton.elim _ _)
  intro i
  let D : Set (ℤ → Bool) :=
    cylinder (α := fun _ : ℤ => Bool) K (B i)
  let F' : Set (ℤ → Bool) :=
    cylinder (α := fun _ : ℤ => Bool) K (E' i)
  let F : Set (ℤ → Bool) :=
    cylinder (α := fun _ : ℤ => Bool) K (E i)
  have hmid : μ ((U.toEquiv '' D) ∆ F) ≤
      (bad.card : ENNReal) * ((2 : ENNReal)⁻¹) ^ K.card := by
    have hDF : U.toEquiv '' D = F' := by
      dsimp [D, F']; exact himg i
    rw [hDF]
    simpa [μ, F', F] using
      (fairBernoulli_cylinder_symmDiff_le_bad K E' E bad hsame i)
  have hfirst : μ (A i ∆ D) ≤ η i :=
    le_of_lt (by simpa [μ, D, symmDiff_comm] using (hBc i))
  have hlast : μ (F ∆ (R₀.toEquiv '' A i)) ≤ θ i :=
    le_of_lt (by simpa [μ, F] using (hEc i))
  have hle := automorphism_image_error_le_three μ U R₀ (A i) D F
  change μ ((U.toEquiv '' A i) ∆ (R₀.toEquiv '' A i)) ≤ _
  exact hle.trans (by
    calc
      (μ (A i ∆ D) + μ ((U.toEquiv '' D) ∆ F)) +
            μ (F ∆ (R₀.toEquiv '' A i))
        ≤ (η i +
             (Fintype.card (Finset (Fin n)) •
                ((∑ j : Fin n, η j) + (∑ j : Fin n, θ j)))) + θ i :=
          add_le_add (add_le_add hfirst (hmid.trans hbadmass)) hlast)



-- This isolates the genuine Rokhlin assertion even further.  One only has
-- to replace a permutation of a *finite fair cube* by weak mixers, with a
-- uniform error on the cylinders of that cube.  Assuming that assertion,
-- all measurable finite tests on the Bernoulli model follow.  In particular
-- no further cardinal matching is hidden in the outstanding tower problem.
lemma fairBernoulli_fin_of_block_tower
    (htower : ∀ (K : Finset ℤ)
      (σ : (∀ _j : (↥K), Bool) ≃ (∀ _j : (↥K), Bool))
      (r : ℝ), 0 < r →
        ∃ W : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)),
          IsWeaklyMixing (Measure.infinitePi (fun _ : ℤ => fairBool)) W ∧
          ∀ H : Set (∀ _j : (↥K), Bool),
            (Measure.infinitePi (fun _ : ℤ => fairBool))
              ((W.toEquiv '' (cylinder (α := fun _ : ℤ => Bool) K H)) ∆
               ((fairBlockAutomorphism K σ).toEquiv ''
                  (cylinder (α := fun _ : ℤ => Bool) K H))) <
                    ENNReal.ofReal r) :
    ∀ (n : ℕ)
      (R₀ : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)))
      (A : Fin n → Set (ℤ → Bool)),
      (∀ i, MeasurableSet (A i)) →
      ∀ (r : ℝ), 0 < r →
      ∃ W : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)),
        IsWeaklyMixing (Measure.infinitePi (fun _ : ℤ => fairBool)) W ∧
        ∀ i, (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((W.toEquiv '' (A i)) ∆ (R₀.toEquiv '' (A i))) <
             ENNReal.ofReal r := by
  classical
  intro n R₀ A hA r hr
  let μ : Measure (ℤ → Bool) := Measure.infinitePi (fun _ : ℤ => fairBool)
  -- `a` is the error used on either side, and also the error paid for
  -- replacing the finite permutation by the tower.  A deliberately loose
  -- integer coefficient keeps the arithmetic in `ENNReal` elementary.
  let M : ℕ := Fintype.card (Finset (Fin n))
  let L : ℕ := 5 + 2 * M * n
  have hL : (0:ℝ) < L := by
    exact_mod_cast (show 0 < L from by dsimp [L]; omega)
  let aR : ℝ := r / (L:ℝ)
  have haR : 0 < aR := div_pos hr hL
  let a : ENNReal := ENNReal.ofReal aR
  have ha : 0 < a := ENNReal.ofReal_pos.2 haR
  obtain ⟨K, B, E, hB, hE, hBc, hEc⟩ :=
    fairBernoulli_exists_common_block_and_center_image n R₀ A hA
      (fun _ => a) (fun _ => a) (fun _ => ha) (fun _ => ha)
  obtain ⟨σ, hσ⟩ :=
    fairBernoulli_block_approximation_round_hist_block n R₀ A K B E hB hE
      (fun _ => a) (fun _ => a) hBc hEc
  let U : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)) :=
    fairBlockAutomorphism K σ
  obtain ⟨W, hW, hWt⟩ := htower K σ aR haR
  refine ⟨W, hW, ?_⟩
  intro i
  let D : Set (ℤ → Bool) :=
       cylinder (α := fun _ : ℤ => Bool) K (B i)
  let F : Set (ℤ → Bool) := U.toEquiv '' D
  have hfirst : μ (A i ∆ D) ≤ a := by
    exact le_of_lt (by simpa [μ, D, symmDiff_comm] using (hBc i))
  have hlast : μ (F ∆ (U.toEquiv '' A i)) ≤ a := by
    dsimp [F]
    rw [automorphism_measure_symmDiff_image μ U D (A i)]
    simpa [symmDiff_comm] using hfirst
  have hmid : μ ((W.toEquiv '' D) ∆ F) < a := by
    have h := hWt (B i)
    simpa [μ, F, D, U, a] using h
  have hWU_le := automorphism_image_error_le_three μ W U (A i) D F
  have hWU : μ ((W.toEquiv '' A i) ∆ (U.toEquiv '' A i)) < a + a + a := by
    refine lt_of_le_of_lt hWU_le ?_
    calc
      (μ (A i ∆ D) + μ ((W.toEquiv '' D) ∆ F)) +
            μ (F ∆ (U.toEquiv '' A i))
        < (a + a) + a := by
             have hin : μ (A i ∆ D) + μ ((W.toEquiv '' D) ∆ F) < a + a :=
               ENNReal.add_lt_add_of_le_of_lt
                 (measure_ne_top _ _) hfirst hmid
             exact ENNReal.add_lt_add_of_lt_of_le
               (measure_ne_top _ _) hin hlast
      _ = a + a + a := rfl
  have htri := MeasureTheory.measure_symmDiff_le (μ := μ)
     (W.toEquiv '' A i) (U.toEquiv '' A i) (R₀.toEquiv '' A i)
  have hUR : μ ((U.toEquiv '' A i) ∆ (R₀.toEquiv '' A i)) ≤
        (a + (Fintype.card (Finset (Fin n)) •
            ((∑ _j : Fin n, a) + (∑ _j : Fin n, a)))) + a := by
     simpa [μ, U] using (hσ i)
  have hbig : μ ((W.toEquiv '' A i) ∆ (R₀.toEquiv '' A i)) <
      (a + a + a) +
        ((a + (Fintype.card (Finset (Fin n)) •
            ((∑ _j : Fin n, a) + (∑ _j : Fin n, a)))) + a) := by
    refine lt_of_le_of_lt htri ?_
    exact ENNReal.add_lt_add_of_lt_of_le (measure_ne_top _ _) hWU hUR
  have hcalc :
      (a + a + a) +
        ((a + (Fintype.card (Finset (Fin n)) •
            ((∑ _j : Fin n, a) + (∑ _j : Fin n, a)))) + a)
          = (L : ℕ) • a := by
    simp [nsmul_eq_mul, L, M]
    ring
  rw [hcalc] at hbig
  have hLa : (L : ℕ) • a = ENNReal.ofReal r := by
    rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast L]
    change ENNReal.ofReal (L:ℝ) * ENNReal.ofReal aR = ENNReal.ofReal r
    rw [← ENNReal.ofReal_mul (by exact_mod_cast (le_of_lt hL))]
    congr 1
    dsimp [aR]
    have hn : (L:ℝ) ≠ 0 := ne_of_gt hL
    field_simp
  rw [hLa] at hbig
  exact hbig



lemma fin_of_equiv_fair_block_tower
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z)
    (e : Z ≃ᵐ (ℤ → Bool))
    (he : MeasurePreserving (e : Z → (ℤ → Bool)) μ
       (Measure.infinitePi (fun _ : ℤ => fairBool)))
    (htower : ∀ (K : Finset ℤ)
      (σ : (∀ _j : (↥K), Bool) ≃ (∀ _j : (↥K), Bool))
      (r : ℝ), 0 < r →
        ∃ W : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)),
          IsWeaklyMixing (Measure.infinitePi (fun _ : ℤ => fairBool)) W ∧
          ∀ H : Set (∀ _j : (↥K), Bool),
            (Measure.infinitePi (fun _ : ℤ => fairBool))
              ((W.toEquiv '' (cylinder (α := fun _ : ℤ => Bool) K H)) ∆
               ((fairBlockAutomorphism K σ).toEquiv ''
                  (cylinder (α := fun _ : ℤ => Bool) K H))) <
                    ENNReal.ofReal r) :
    ∀ (n : ℕ) (S₀ : Automorphism μ)
      (D : Fin n → Set Z), (∀ i, MeasurableSet (D i)) →
      ∀ (r : ℝ), 0 < r →
        ∃ W : Automorphism μ, IsWeaklyMixing μ W ∧
          ∀ i, μ ((W.toEquiv '' (D i)) ∆ (S₀.toEquiv '' (D i))) <
             ENNReal.ofReal r := by
  classical
  intro n S₀ D hD r hr
  let μb : Measure (ℤ → Bool) :=
       Measure.infinitePi (fun _ : ℤ => fairBool)
  have he' : MeasurePreserving (e.symm : (ℤ → Bool) → Z) μb μ :=
    MeasurePreserving.symm e he
  let R₀ : Automorphism μb :=
    transportAutomorphism μb μ e.symm he' S₀
  let C : Fin n → Set (ℤ → Bool) := fun i => e '' (D i)
  have hC (i : Fin n) : MeasurableSet (C i) :=
    e.measurableEmbedding.measurableSet_image' (hD i)
  obtain ⟨R, hR, hclose⟩ :=
    fairBernoulli_fin_of_block_tower htower n R₀ C hC r hr
  let W : Automorphism μ := transportAutomorphism μ μb e he R
  have hW : IsWeaklyMixing μ W := transport_weakMixing μ μb e he R hR
  refine ⟨W, hW, ?_⟩
  intro i
  have hcen : transportAutomorphism μ μb e he R₀ = S₀ := by
    apply automorphism_ext
    apply MeasurableEquiv.ext
    funext x
    simp [R₀, transportAutomorphism_apply]
  have h1 : W.toEquiv '' (D i) =
        (e : Z → (ℤ → Bool)) ⁻¹' (R.toEquiv '' (C i)) := by
    simpa [W, C] using (transport_image_preimage μ μb e he R (D i))
  have h2 : S₀.toEquiv '' (D i) =
        (e : Z → (ℤ → Bool)) ⁻¹' (R₀.toEquiv '' (C i)) := by
    rw [← hcen]
    simpa [C] using (transport_image_preimage μ μb e he R₀ (D i))
  have hm :
      μ (((e : Z → (ℤ → Bool)) ⁻¹' (R.toEquiv '' (C i))) ∆
         ((e : Z → (ℤ → Bool)) ⁻¹' (R₀.toEquiv '' (C i)))) =
       μb ((R.toEquiv '' (C i)) ∆ (R₀.toEquiv '' (C i))) := by
    rw [← Set.preimage_symmDiff]
    exact he.measure_preimage_emb e.measurableEmbedding _
  rw [h1, h2, hm]
  simpa [μb] using (hclose i)


-- The same equality for an iterate.  This formulation avoids repeatedly
-- constructing a bundled automorphism for the power.
lemma automorphism_iterate_measure_image
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T : Automorphism m) (q : ℕ) (E : Set X) :
    m ((((T.toEquiv : X → X)^[q]) '' E)) = m E := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hset : (((T.toEquiv : X → X)^[q.succ]) '' E)
          = (T.toEquiv : X → X) '' (((T.toEquiv : X → X)^[q]) '' E) := by
        -- the successor on the outside gives the image-image formula
        rw [Set.image_image]
        congr 1
        funext x
        exact Function.iterate_succ_apply' (T.toEquiv : X → X) q x
      rw [hset, automorphism_measure_image m T, ih]

lemma automorphism_iterate_measure_symmDiff_image
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T : Automorphism m) (q : ℕ) (E F : Set X) :
    m (((((T.toEquiv : X → X)^[q]) '' E) ∆
         (((T.toEquiv : X → X)^[q]) '' F))) = m (E ∆ F) := by
  rw [← Set.image_symmDiff (T.toEquiv.injective.iterate q)]
  exact automorphism_iterate_measure_image m T q (E ∆ F)

-- A telescoping estimate.  At a centre `T₀` the distance between the
-- `q`th images of a set for `T` and for `T₀` is controlled by `q` many
-- *ordinary* subbasic coordinates of `T`.  The testing sets in those
-- coordinates are frozen images along `T₀`, hence they are measurable
-- whenever the original set is.
lemma iterate_image_symmDiff_le_sum
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T T₀ : Automorphism m) (q : ℕ) (B : Set X) :
    m (((((T.toEquiv : X → X)^[q]) '' B) ∆
       (((T₀.toEquiv : X → X)^[q]) '' B)))
       ≤ ∑ j ∈ Finset.range q,
          m (((T.toEquiv : X → X) ''
               (((T₀.toEquiv : X → X)^[j]) '' B)) ∆
             ((T₀.toEquiv : X → X) ''
               (((T₀.toEquiv : X → X)^[j]) '' B))) := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hs₁ : (((T.toEquiv : X → X)^[q.succ]) '' B) =
          (T.toEquiv : X → X) '' (((T.toEquiv : X → X)^[q]) '' B) := by
        rw [Set.image_image]
        congr 1
        funext x
        exact Function.iterate_succ_apply' (T.toEquiv : X → X) q x
      have hs₀ : (((T₀.toEquiv : X → X)^[q.succ]) '' B) =
          (T₀.toEquiv : X → X) '' (((T₀.toEquiv : X → X)^[q]) '' B) := by
        rw [Set.image_image]
        congr 1
        funext x
        exact Function.iterate_succ_apply' (T₀.toEquiv : X → X) q x
      rw [hs₁, hs₀]
      have htri := MeasureTheory.measure_symmDiff_le (μ := m)
        ((T.toEquiv : X → X) '' (((T.toEquiv : X → X)^[q]) '' B))
        ((T.toEquiv : X → X) '' (((T₀.toEquiv : X → X)^[q]) '' B))
        ((T₀.toEquiv : X → X) '' (((T₀.toEquiv : X → X)^[q]) '' B))
      have hleft :
          m (((T.toEquiv : X → X) '' (((T.toEquiv : X → X)^[q]) '' B)) ∆
             ((T.toEquiv : X → X) '' (((T₀.toEquiv : X → X)^[q]) '' B))) =
            m (((((T.toEquiv : X → X)^[q]) '' B) ∆
               (((T₀.toEquiv : X → X)^[q]) '' B))) :=
        automorphism_measure_symmDiff_image m T _ _
      -- now append the last summand to the induction hypothesis
      calc
        m (((T.toEquiv : X → X) '' (((T.toEquiv : X → X)^[q]) '' B)) ∆
             ((T₀.toEquiv : X → X) '' (((T₀.toEquiv : X → X)^[q]) '' B)))
          ≤ m (((T.toEquiv : X → X) '' (((T.toEquiv : X → X)^[q]) '' B)) ∆
             ((T.toEquiv : X → X) '' (((T₀.toEquiv : X → X)^[q]) '' B))) +
            m (((T.toEquiv : X → X) '' (((T₀.toEquiv : X → X)^[q]) '' B)) ∆
             ((T₀.toEquiv : X → X) '' (((T₀.toEquiv : X → X)^[q]) '' B))) := htri
        _ = m (((((T.toEquiv : X → X)^[q]) '' B) ∆
               (((T₀.toEquiv : X → X)^[q]) '' B))) +
            m (((T.toEquiv : X → X) '' (((T₀.toEquiv : X → X)^[q]) '' B)) ∆
             ((T₀.toEquiv : X → X) '' (((T₀.toEquiv : X → X)^[q]) '' B))) := by rw [hleft]
        _ ≤ (∑ j ∈ Finset.range q,
          m (((T.toEquiv : X → X) ''
               (((T₀.toEquiv : X → X)^[j]) '' B)) ∆
             ((T₀.toEquiv : X → X) ''
               (((T₀.toEquiv : X → X)^[j]) '' B)))) +
            m (((T.toEquiv : X → X) '' (((T₀.toEquiv : X → X)^[q]) '' B)) ∆
             ((T₀.toEquiv : X → X) '' (((T₀.toEquiv : X → X)^[q]) '' B))) :=
              add_le_add_left ih _
        _ = _ := by simp [Finset.sum_range_succ]

lemma iterate_image_symmDiff_real_le_sum
    {X : Type*} [MeasurableSpace X] (m : Measure X) [IsFiniteMeasure m]
    (T T₀ : Automorphism m) (q : ℕ) (B : Set X) :
    (m (((((T.toEquiv : X → X)^[q]) '' B) ∆
       (((T₀.toEquiv : X → X)^[q]) '' B)))).toReal
       ≤ ∑ j ∈ Finset.range q,
          (m (((T.toEquiv : X → X) ''
               (((T₀.toEquiv : X → X)^[j]) '' B)) ∆
             ((T₀.toEquiv : X → X) ''
               (((T₀.toEquiv : X → X)^[j]) '' B)))).toReal := by
  have h := iterate_image_symmDiff_le_sum m T T₀ q B
  have htop : (∑ j ∈ Finset.range q,
          m (((T.toEquiv : X → X) ''
               (((T₀.toEquiv : X → X)^[j]) '' B)) ∆
             ((T₀.toEquiv : X → X) ''
               (((T₀.toEquiv : X → X)^[j]) '' B)))) ≠ (⊤ : ENNReal) := by
    apply ne_of_lt
    exact ENNReal.sum_lt_top.2 (by
      intro i hi
      exact (measure_lt_top m _))
  have hh := (ENNReal.toReal_le_toReal (measure_ne_top m _) htop).2 h
  rw [ENNReal.toReal_sum (fun i hi => measure_ne_top m _)] at hh
  exact hh

-- Correlations may be written using an image of the second event.  For a
-- measurable equivalence this identity holds for every set (no completed
-- sigma-algebra or null representative has to be chosen).
lemma automorphism_correlation_image
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (T : Automorphism m) (q : ℕ) (A B : Set X) :
    m ((((T.toEquiv : X → X)^[q]) ⁻¹' A) ∩ B) =
      m (A ∩ (((T.toEquiv : X → X)^[q]) '' B)) := by
  classical
  let f : X → X := ((T.toEquiv : X → X)^[q])
  have hi : Function.Injective f := T.toEquiv.injective.iterate q
  have hs : Function.Surjective f := T.toEquiv.surjective.iterate q
  have hm (E : Set X) : m (f '' E) = m E := by
    exact automorphism_iterate_measure_image m T q E
  have hset : f '' (f ⁻¹' A ∩ B) = A ∩ (f '' B) := by
    ext x
    constructor
    · rintro ⟨z, ⟨hzA,hzB⟩, rfl⟩
      exact ⟨hzA, ⟨z,hzB,rfl⟩⟩
    · intro hx
      rcases hx.2 with ⟨z,hzB,hzx⟩
      refine ⟨z, ⟨?_,hzB⟩, hzx⟩
      -- the first component follows by rewriting the image witness
      simpa [hzx] using hx.1
  rw [← hm]
  exact congrArg m hset

lemma automorphism_measurable_iterate_image
    {X : Type*} [MeasurableSpace X] {m : Measure X}
    (T : Automorphism m) {E : Set X} (hE : MeasurableSet E) (q : ℕ) :
    MeasurableSet (((T.toEquiv : X → X)^[q]) '' E) := by
  induction q with
  | zero => simpa using hE
  | succ q ih =>
      have hset : (((T.toEquiv : X → X)^[q.succ]) '' E) =
            (T.toEquiv : X → X) ''
              (((T.toEquiv : X → X)^[q]) '' E) := by
              rw [Set.image_image]
              congr 1
              funext x
              exact Function.iterate_succ_apply' (T.toEquiv : X → X) q x
      rw [hset]
      exact T.toEquiv.measurableEmbedding.measurableSet_image' ih

-- The intersection in the image formula is `1`-Lipschitz in the image
-- event for the symmetric-difference metric.
lemma correlation_real_sub_le_iterate_sum
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    [IsProbabilityMeasure m]
    (T T₀ : Automorphism m) (q : ℕ) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |(m ((((T.toEquiv : X → X)^[q]) ⁻¹' A) ∩ B)).toReal -
        (m ((((T₀.toEquiv : X → X)^[q]) ⁻¹' A) ∩ B)).toReal|
       ≤ ∑ j ∈ Finset.range q,
          (m (((T.toEquiv : X → X) ''
               (((T₀.toEquiv : X → X)^[j]) '' B)) ∆
             ((T₀.toEquiv : X → X) ''
               (((T₀.toEquiv : X → X)^[j]) '' B)))).toReal := by
  classical
  let E : Set X := (((T.toEquiv : X → X)^[q]) '' B)
  let F : Set X := (((T₀.toEquiv : X → X)^[q]) '' B)
  have hE : MeasurableSet E := by
    dsimp [E]
    have hm := (T.measurePreserving.iterate q).measurable hB
    -- measurability of the image follows from a measurable equivalence;
    -- equivalently express it as a preimage under the inverse iterate.
    -- induction keeps the bundled equivalence at each step
    clear hm
    induction q with
    | zero => simpa [E] using hB
    | succ q ih =>
        -- after simplifying the successor it is the image by an equivalence
        have hset : (((T.toEquiv : X → X)^[q.succ]) '' B) =
            (T.toEquiv : X → X) ''
              (((T.toEquiv : X → X)^[q]) '' B) := by
              rw [Set.image_image]
              congr 1
              funext x
              exact Function.iterate_succ_apply' (T.toEquiv : X → X) q x
        change MeasurableSet (((T.toEquiv : X → X)^[q.succ]) '' B)
        rw [hset]
        exact T.toEquiv.measurableEmbedding.measurableSet_image' (by
          -- use the induction statement, with E unfolded
          change MeasurableSet (((T.toEquiv : X → X)^[q]) '' B) at ih ⊢
          exact ih)
  have hF : MeasurableSet F := by
    dsimp [F]
    clear hE E
    induction q with
    | zero => simpa using hB
    | succ q ih =>
        have hset : (((T₀.toEquiv : X → X)^[q.succ]) '' B) =
            (T₀.toEquiv : X → X) ''
              (((T₀.toEquiv : X → X)^[q]) '' B) := by
              rw [Set.image_image]
              congr 1
              funext x
              exact Function.iterate_succ_apply' (T₀.toEquiv : X → X) q x
        rw [hset]
        exact T₀.toEquiv.measurableEmbedding.measurableSet_image' ih
  rw [automorphism_correlation_image m T q,
      automorphism_correlation_image m T₀ q]
  have hbase : |(m (A ∩ E)).toReal - (m (A ∩ F)).toReal| ≤
      (m ((A ∩ E) ∆ (A ∩ F))).toReal :=
    abs_measureReal_sub_le_measureReal_symmDiff
      (hA.inter hE).nullMeasurableSet (hA.inter hF).nullMeasurableSet
  have hsub : (A ∩ E) ∆ (A ∩ F) ⊆ E ∆ F := by
    intro x hx
    simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hx ⊢
    tauto
  have hmon : (m ((A ∩ E) ∆ (A ∩ F))).toReal ≤ (m (E ∆ F)).toReal :=
    measureReal_mono hsub
  exact le_trans (le_trans hbase hmon)
    (iterate_image_symmDiff_real_le_sum m T T₀ q B)

lemma correlation_real_sub_le_iterate_image
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    [IsProbabilityMeasure m]
    (T T₀ : Automorphism m) (q : ℕ) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |(m ((((T.toEquiv : X → X)^[q]) ⁻¹' A) ∩ B)).toReal -
        (m ((((T₀.toEquiv : X → X)^[q]) ⁻¹' A) ∩ B)).toReal| ≤
       (m (((((T.toEquiv : X → X)^[q]) '' B) ∆
           (((T₀.toEquiv : X → X)^[q]) '' B)))).toReal := by
  rw [automorphism_correlation_image m T q,
      automorphism_correlation_image m T₀ q]
  have hE : MeasurableSet (((T.toEquiv : X → X)^[q]) '' B) :=
    automorphism_measurable_iterate_image T hB q
  have hF : MeasurableSet (((T₀.toEquiv : X → X)^[q]) '' B) :=
    automorphism_measurable_iterate_image T₀ hB q
  have hbase := abs_measureReal_sub_le_measureReal_symmDiff
    (μ := m)
    (hA.inter hE).nullMeasurableSet
    (hA.inter hF).nullMeasurableSet
  refine le_trans hbase ?_
  apply measureReal_mono (h₂ := measure_ne_top m _)
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hx ⊢
  tauto

-- Subbasic coordinates control a whole finite iterate.  This is a
-- neighbourhood statement rather than a global metric on the group;
-- subbasic opens are exactly what the proof of openness of correlations
-- needs.
lemma exists_open_iterate_image_near
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    [IsProbabilityMeasure m]
    (T₀ : Automorphism m) (q : ℕ) (B : Set X) (hB : MeasurableSet B)
    {η : ℝ} (hη : 0 < η) :
    ∃ U : Set (Automorphism m), IsOpen U ∧ T₀ ∈ U ∧
      ∀ T ∈ U,
        (m (((((T.toEquiv : X → X)^[q]) '' B) ∆
          (((T₀.toEquiv : X → X)^[q]) '' B)))).toReal < η := by
  classical
  by_cases hz : q = 0
  · subst q
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, ?_⟩
    intro T hT
    simpa using hη
  · have hq : 0 < q := Nat.pos_of_ne_zero hz
    let δ : ℝ := η / (q : ℝ)
    have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
    have hδ : 0 < δ := div_pos hη hqR
    let E : ℕ → Set X := fun j =>
      (((T₀.toEquiv : X → X)^[j]) '' B)
    let U : Set (Automorphism m) :=
      ⋂ j ∈ Finset.range q,
        {S : Automorphism m |
          m ((S.toEquiv '' (E j)) ∆ (T₀.toEquiv '' (E j))) <
            ENNReal.ofReal δ}
    have hEm (j : ℕ) : MeasurableSet (E j) := by
      dsimp [E]
      exact automorphism_measurable_iterate_image T₀ hB j
    have ho : IsOpen U := by
      dsimp [U]
      apply isOpen_biInter_finset
      intro j hj
      exact isOpen_weak_ball m T₀ (E j) (hEm j) hδ
    have hc : T₀ ∈ U := by
      dsimp [U]
      apply Set.mem_iInter.mpr
      intro j
      apply Set.mem_iInter.mpr
      intro hj
      exact mem_weak_ball_self m T₀ (E j) hδ
    refine ⟨U, ho, hc, ?_⟩
    intro T hT
    have hjlt (j : ℕ) (hj : j ∈ Finset.range q) :
        (m (((T.toEquiv : X → X) '' (E j)) ∆
          ((T₀.toEquiv : X → X) '' (E j)))).toReal < δ := by
      have hu := Set.mem_iInter.mp (Set.mem_iInter.mp hT j) hj
      exact ENNReal.toReal_lt_of_lt_ofReal hu
    have hsumlt :
        (∑ j ∈ Finset.range q,
          (m (((T.toEquiv : X → X) '' (E j)) ∆
             ((T₀.toEquiv : X → X) '' (E j)))).toReal) < η := by
      have hs : (∑ j ∈ Finset.range q,
          (m (((T.toEquiv : X → X) '' (E j)) ∆
             ((T₀.toEquiv : X → X) '' (E j)))).toReal) <
          ∑ _j ∈ Finset.range q, δ := by
            apply Finset.sum_lt_sum_of_nonempty
            · exact Finset.nonempty_range_iff.mpr hz
            · intro j hj
              exact hjlt j hj
      have hcalc : ∑ _j ∈ Finset.range q, δ = (q:ℝ) * δ := by
        simp
      have hcancel : (q : ℝ) * δ = η := by
        dsimp [δ]
        field_simp
      exact hs.trans_le (by rw [hcalc, hcancel])
    have hle := iterate_image_symmDiff_real_le_sum m T T₀ q B
    change _ < η
    apply lt_of_le_of_lt hle
    simpa [E] using hsumlt

-- Consequently every *fixed finite-time* correlation is a continuous real
-- valued coordinate in the generated weak topology.  The dependence on
-- the iterate is finite, which is why the preceding finite telescoping
-- neighbourhood suffices.
lemma continuous_correlation_real
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    [IsProbabilityMeasure m]
    (q : ℕ) (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Continuous (fun T : Automorphism m =>
      (m ((((T.toEquiv : X → X)^[q]) ⁻¹' A) ∩ B)).toReal) := by
  classical
  apply continuous_iff_continuousAt.2
  intro T₀
  rw [continuousAt_def]
  intro Z hZ
  rcases Metric.mem_nhds_iff.mp hZ with ⟨η, hη, hsub⟩
  obtain ⟨U, hUopen, hU₀, hUclose⟩ :=
    exists_open_iterate_image_near m T₀ q B hB hη
  apply mem_nhds_iff.mpr
  refine ⟨U, ?_, hUopen, hU₀⟩
  intro T hTU
  apply hsub
  have hle := correlation_real_sub_le_iterate_image m T T₀ q A B hA hB
  have hlt := lt_of_le_of_lt hle (hUclose T hTU)
  -- the metric on the real line is absolute value of the difference
  simpa [Real.dist_eq] using hlt

lemma continuous_weak_average
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    [IsProbabilityMeasure m]
    (n : ℕ) (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Continuous (fun T : Automorphism m =>
      (∑ k ∈ Finset.range n,
        |(m ((((T.toEquiv : X → X)^[k]) ⁻¹' A) ∩ B)).toReal -
          (m A).toReal * (m B).toReal|) / (n : ℝ)) := by
  classical
  have hterm (k : ℕ) : Continuous
      (fun T : Automorphism m =>
        |(m ((((T.toEquiv : X → X)^[k]) ⁻¹' A) ∩ B)).toReal -
          (m A).toReal * (m B).toReal|) := by
    have hcorr := continuous_correlation_real m k A B hA hB
    exact (hcorr.sub continuous_const).abs
  have hsum : Continuous (fun T : Automorphism m =>
      ∑ k ∈ Finset.range n,
        |(m ((((T.toEquiv : X → X)^[k]) ⁻¹' A) ∩ B)).toReal -
          (m A).toReal * (m B).toReal|) := by
    apply continuous_finset_sum (Finset.range n)
    intro k hk
    -- the notation for the doubled sum is just `sum` over the range;
    -- `simp_rw` in the goal only packages the membership proof.
    exact hterm k
  exact hsum.div_const _

lemma isOpen_weak_average_lt
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    [IsProbabilityMeasure m]
    (n : ℕ) (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (r : ℝ) :
    IsOpen {T : Automorphism m |
      (∑ k ∈ Finset.range n,
        |(m ((((T.toEquiv : X → X)^[k]) ⁻¹' A) ∩ B)).toReal -
          (m A).toReal * (m B).toReal|) / (n : ℝ) < r} := by
  have h := continuous_weak_average m n A B hA hB
  exact isOpen_lt h continuous_const

-- Uniform set-error estimate: replacing the two test events changes every
-- correlation term by at most the sum of their symmetric-difference
-- errors.  The bound is uniform in the time `k`; this is what allows one
-- to pass from the countable test ring to arbitrary measurable events.
lemma abs_correlation_change_le
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Automorphism μ) (k : ℕ)
    (A P B Q : Set Y)
    (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hB : MeasurableSet B) (hQ : MeasurableSet Q) :
    |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
       (μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal| ≤
       (μ (A ∆ P)).toReal + (μ (B ∆ Q)).toReal := by
  classical
  let f : Y → Y := ((T.toEquiv : Y → Y)^[k])
  have hf : MeasurePreserving f μ μ := T.measurePreserving.iterate k
  let U : Set Y := f ⁻¹' A ∩ B
  let V : Set Y := f ⁻¹' P ∩ Q
  have hUm : MeasurableSet U := (hf.measurable hA).inter hB
  have hVm : MeasurableSet V := (hf.measurable hP).inter hQ
  have hsub : U ∆ V ⊆ (f ⁻¹' (A ∆ P)) ∪ (B ∆ Q) := by
    intro x hx
    dsimp [U, V] at hx
    simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_union] at hx ⊢
    tauto
  have hpre : (μ (f ⁻¹' (A ∆ P))).toReal = (μ (A ∆ P)).toReal := by
    have h := hf.measure_preimage ((hA.symmDiff hP).nullMeasurableSet)
    exact congrArg ENNReal.toReal h
  have hle := abs_measureReal_sub_le_measureReal_symmDiff
    (μ := μ) hUm.nullMeasurableSet hVm.nullMeasurableSet
  change |(μ U).toReal - (μ V).toReal| ≤ _
  refine le_trans hle ?_
  calc
    (μ (U ∆ V)).toReal
        ≤ (μ ((f ⁻¹' (A ∆ P)) ∪ (B ∆ Q))).toReal :=
          measureReal_mono hsub
    _ ≤ (μ (f ⁻¹' (A ∆ P))).toReal + (μ (B ∆ Q)).toReal :=
          measureReal_union_le _ _
    _ = _ := by rw [hpre]

lemma abs_product_change_le
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (A P B Q : Set Y)
    (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hB : MeasurableSet B) (hQ : MeasurableSet Q) :
    |(μ A).toReal * (μ B).toReal -
       (μ P).toReal * (μ Q).toReal| ≤
       (μ (A ∆ P)).toReal + (μ (B ∆ Q)).toReal := by
  have hAP : |(μ A).toReal - (μ P).toReal| ≤
      (μ (A ∆ P)).toReal :=
    abs_measureReal_sub_le_measureReal_symmDiff
      (μ := μ) hA.nullMeasurableSet hP.nullMeasurableSet
  have hBQ : |(μ B).toReal - (μ Q).toReal| ≤
      (μ (B ∆ Q)).toReal :=
    abs_measureReal_sub_le_measureReal_symmDiff
      (μ := μ) hB.nullMeasurableSet hQ.nullMeasurableSet
  have hprob (S : Set Y) : 0 ≤ (μ S).toReal ∧ (μ S).toReal ≤ 1 := by
    constructor
    · exact ENNReal.toReal_nonneg
    · have hle : μ S ≤ (1 : ENNReal) := prob_le_one
      simpa using (ENNReal.toReal_mono (by simp : (1:ENNReal) ≠ ⊤) hle)
  have hb₁ := hprob B
  have hp₁ := hprob P
  calc
    |(μ A).toReal * (μ B).toReal - (μ P).toReal * (μ Q).toReal| =
        |((μ A).toReal - (μ P).toReal) * (μ B).toReal +
          (μ P).toReal * ((μ B).toReal - (μ Q).toReal)| := by
            congr 1 <;> ring
    _ ≤ |(μ A).toReal - (μ P).toReal| * |(μ B).toReal| +
         |(μ P).toReal| * |(μ B).toReal - (μ Q).toReal| := by
          simpa [abs_mul] using
            (abs_add_le
              (((μ A).toReal - (μ P).toReal) * (μ B).toReal)
              ((μ P).toReal * ((μ B).toReal - (μ Q).toReal)))
    _ ≤ (μ (A ∆ P)).toReal + (μ (B ∆ Q)).toReal := by
      rw [abs_of_nonneg hb₁.1, abs_of_nonneg hp₁.1]
      have hx : |(μ A).toReal - (μ P).toReal| * (μ B).toReal ≤
          (μ (A ∆ P)).toReal := by
        nlinarith [hAP, hb₁.1, hb₁.2,
          ENNReal.toReal_nonneg (a := μ (A ∆ P)),
          abs_nonneg ((μ A).toReal - (μ P).toReal)]
      have hy : (μ P).toReal * |(μ B).toReal - (μ Q).toReal| ≤
          (μ (B ∆ Q)).toReal := by
        nlinarith [hBQ, hp₁.1, hp₁.2,
          ENNReal.toReal_nonneg (a := μ (B ∆ Q)),
          abs_nonneg ((μ B).toReal - (μ Q).toReal)]
      linarith

lemma weak_term_change_le
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Automorphism μ) (k : ℕ)
    (A P B Q : Set Y)
    (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hB : MeasurableSet B) (hQ : MeasurableSet Q) :
    |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
          (μ A).toReal * (μ B).toReal| ≤
      |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal -
          (μ P).toReal * (μ Q).toReal| +
          2 * ((μ (A ∆ P)).toReal + (μ (B ∆ Q)).toReal) := by
  have hx := abs_correlation_change_le μ T k A P B Q hA hP hB hQ
  have hp := abs_product_change_le μ A P B Q hA hP hB hQ
  have htri :
    |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
          (μ A).toReal * (μ B).toReal| ≤
      |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal -
          (μ P).toReal * (μ Q).toReal| +
      |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
        (μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal| +
      |(μ A).toReal * (μ B).toReal -
          (μ P).toReal * (μ Q).toReal| := by
    -- break the difference into its three summands
    calc
      |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
          (μ A).toReal * (μ B).toReal| =
        |((μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal -
            (μ P).toReal * (μ Q).toReal) +
          ((μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
             (μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal) +
          ((μ P).toReal * (μ Q).toReal -
             (μ A).toReal * (μ B).toReal)| := by
              congr 1 <;> ring
      _ ≤ |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal -
              (μ P).toReal * (μ Q).toReal| +
            |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
             (μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal| +
            |(μ P).toReal * (μ Q).toReal -
                 (μ A).toReal * (μ B).toReal| := by
            have h1 := abs_add_le
              ((μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal -
                (μ P).toReal * (μ Q).toReal)
              ((μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
                 (μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal)
            have h2 := abs_add_le
              (((μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal -
                (μ P).toReal * (μ Q).toReal) +
               ((μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
                 (μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal))
              ((μ P).toReal * (μ Q).toReal - (μ A).toReal * (μ B).toReal)
            calc
              _ ≤ |((μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal -
                    (μ P).toReal * (μ Q).toReal) +
                    ((μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
                      (μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal)| +
                    |(μ P).toReal * (μ Q).toReal - (μ A).toReal * (μ B).toReal| := h2
              _ ≤ _ := by
                rw [abs_sub_comm ((μ P).toReal * (μ Q).toReal)
                      ((μ A).toReal * (μ B).toReal)]
                nlinarith [h1]
      _ = _ := by
            rw [abs_sub_comm ((μ P).toReal * (μ Q).toReal)
                    ((μ A).toReal * (μ B).toReal)]
  nlinarith

lemma weak_average_change_le
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Automorphism μ) (n : ℕ)
    (A P B Q : Set Y)
    (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hB : MeasurableSet B) (hQ : MeasurableSet Q) :
    (∑ k ∈ Finset.range n,
      |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
          (μ A).toReal * (μ B).toReal|) / (n:ℝ) ≤
    (∑ k ∈ Finset.range n,
      |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal -
          (μ P).toReal * (μ Q).toReal|) / (n:ℝ) +
      2 * ((μ (A ∆ P)).toReal + (μ (B ∆ Q)).toReal) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hz : 0 ≤
        2 * ((μ (A ∆ P)).toReal + (μ (B ∆ Q)).toReal) := by positivity
    simpa using hz
  · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hsum :
      (∑ k ∈ Finset.range n,
        |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
          (μ A).toReal * (μ B).toReal|) ≤
      (∑ k ∈ Finset.range n,
          (|(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal -
              (μ P).toReal * (μ Q).toReal| +
            2 * ((μ (A ∆ P)).toReal + (μ (B ∆ Q)).toReal))) := by
        apply Finset.sum_le_sum
        intro k hk
        exact weak_term_change_le μ T k A P B Q hA hP hB hQ
    have hdiv := (div_le_div_iff_of_pos_right hnpos).2 hsum
    calc
      (∑ k ∈ Finset.range n,
        |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
          (μ A).toReal * (μ B).toReal|) / (n:ℝ) ≤
        (∑ k ∈ Finset.range n,
          (|(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal -
              (μ P).toReal * (μ Q).toReal| +
            2 * ((μ (A ∆ P)).toReal + (μ (B ∆ Q)).toReal))) / (n:ℝ) :=
              hdiv
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

-- A concrete countable ring of measurable tests.  Keeping the syntax
-- countable (rather than merely taking all measurable sets) is what makes
-- the countable topological construction below possible.
inductive HalmosTest where
  | empty : HalmosTest
  | univ : HalmosTest
  | atom : ℕ → HalmosTest
  | union : HalmosTest → HalmosTest → HalmosTest
  | diff : HalmosTest → HalmosTest → HalmosTest
  deriving Countable

namespace HalmosTest
variable {Y : Type*}

def eval (g : ℕ → Set Y) : HalmosTest → Set Y
  | .empty => ∅
  | .univ => Set.univ
  | .atom i => g i
  | .union p q => eval g p ∪ eval g q
  | .diff p q => eval g p \ eval g q

lemma measurable_eval {Y : Type*} [MeasurableSpace Y]
    (g : ℕ → Set Y) (hg : ∀ i, MeasurableSet (g i)) (t : HalmosTest) :
    MeasurableSet (t.eval g) := by
  induction t with
  | empty => exact MeasurableSet.empty
  | univ => exact MeasurableSet.univ
  | atom i => exact hg i
  | union p q hp hq => exact hp.union hq
  | diff p q hp hq => exact hp.diff hq

end HalmosTest

def halmosTestRing (Y : Type*) (g : ℕ → Set Y) : Set (Set Y) :=
  Set.range (fun t : HalmosTest => t.eval g)

lemma countable_halmosTestRing
    (Y : Type*) (g : ℕ → Set Y) : (halmosTestRing Y g).Countable := by
  exact Set.countable_range _

lemma isSetRing_halmosTestRing
    {Y : Type*} (g : ℕ → Set Y) :
    MeasureTheory.IsSetRing (halmosTestRing Y g) := by
  constructor
  · exact ⟨HalmosTest.empty, rfl⟩
  · intro s t hs ht
    rcases hs with ⟨p, rfl⟩
    rcases ht with ⟨q, rfl⟩
    exact ⟨HalmosTest.union p q, rfl⟩
  · intro s t hs ht
    rcases hs with ⟨p, rfl⟩
    rcases ht with ⟨q, rfl⟩
    exact ⟨HalmosTest.diff p q, rfl⟩

lemma measurable_halmosTestRing
    {Y : Type*} [MeasurableSpace Y]
    (g : ℕ → Set Y) (hg : ∀ i, MeasurableSet (g i))
    {s : Set Y} (hs : s ∈ halmosTestRing Y g) : MeasurableSet s := by
  rcases hs with ⟨t, rfl⟩
  exact HalmosTest.measurable_eval g hg t

lemma univ_mem_halmosTestRing
    {Y : Type*} (g : ℕ → Set Y) :
    (Set.univ : Set Y) ∈ halmosTestRing Y g := by
  exact ⟨HalmosTest.univ, rfl⟩

lemma generateFrom_halmosTestRing
    (Y : Type*) [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] :
    MeasurableSpace.generateFrom
      (halmosTestRing Y (MeasurableSpace.natGeneratingSequence Y)) =
        (inferInstance : MeasurableSpace Y) := by
  classical
  let g : ℕ → Set Y := MeasurableSpace.natGeneratingSequence Y
  have hg (i : ℕ) : MeasurableSet (g i) :=
    MeasurableSpace.measurableSet_natGeneratingSequence i
  have hle : MeasurableSpace.generateFrom (halmosTestRing Y g) ≤
      (inferInstance : MeasurableSpace Y) := by
    apply MeasurableSpace.generateFrom_le
    intro t ht
    exact measurable_halmosTestRing g hg ht
  have hge : (inferInstance : MeasurableSpace Y) ≤
      MeasurableSpace.generateFrom (halmosTestRing Y g) := by
    have hnat := MeasurableSpace.generateFrom_natGeneratingSequence Y
    -- every original generator occurs as an atom of the ring
    have hinc : Set.range g ⊆ halmosTestRing Y g := by
      intro s hs
      rcases hs with ⟨i, rfl⟩
      exact ⟨HalmosTest.atom i, rfl⟩
    have hmono := MeasurableSpace.generateFrom_mono hinc
    -- `hnat` is oriented with `generateFrom` on the left
    rw [← hnat]
    exact hmono
  exact le_antisymm hle hge

-- Approximation by a member of the countable ring, with an actual Borel
-- representative.  The trivial one-set cover is why `univ` was included
-- explicitly in the syntax.
lemma exists_halmosTest_approx
    {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (A : Set Y) (hA : MeasurableSet A) {r : ENNReal} (hr : 0 < r) :
    ∃ t : HalmosTest,
      μ ((t.eval (MeasurableSpace.natGeneratingSequence Y)) ∆ A) < r := by
  let g : ℕ → Set Y := MeasurableSpace.natGeneratingSequence Y
  let C : Set (Set Y) := halmosTestRing Y g
  have hcov : ∃ D : Set (Set Y),
      D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · intro U hU
      have hu : U = (Set.univ : Set Y) := Set.mem_singleton_iff.mp hU
      simpa [C, hu] using (univ_mem_halmosTestRing g)
    · simp
  have hg : (inferInstance : MeasurableSpace Y) =
        MeasurableSpace.generateFrom C := by
    have h := generateFrom_halmosTestRing Y
    exact h.symm
  obtain ⟨P, hPC, hp⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := μ) (isSetRing_halmosTestRing g) hcov hg hA hr
  rcases hPC with ⟨t, rfl⟩
  exact ⟨t, hp⟩

-- A countable `Gδ` condition that occurs in the usual Baire proof.  One
-- asks, for every two ring tests and every precision and lower bound on
-- the time, for *some* longer average below that precision.  The passage
-- from this `liminf` formulation to full weak mixing is the analytical
-- zero-correlation step of the argument; the point of recording the
-- condition is that its `Gδ` nature uses only the weak topology just
-- analysed.
def HalmosSubseqSet
    {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure Y) : Set (Automorphism μ) :=
  {T | ∀ (a b : HalmosTest) (l N : ℕ),
      ∃ n : ℕ, N ≤ n ∧
        (∑ k ∈ Finset.range n,
          |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹'
               (a.eval (MeasurableSpace.natGeneratingSequence Y))) ∩
               (b.eval (MeasurableSpace.natGeneratingSequence Y)))).toReal -
              (μ (a.eval (MeasurableSpace.natGeneratingSequence Y))).toReal *
              (μ (b.eval (MeasurableSpace.natGeneratingSequence Y))).toReal|)
          / (n:ℝ) < (1 / ((l+1:ℕ):ℝ))}

lemma isGδ_halmosSubseqSet
    {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    IsGδ (HalmosSubseqSet μ) := by
  classical
  let g : ℕ → Set Y := MeasurableSpace.natGeneratingSequence Y
  let av : HalmosTest → HalmosTest → ℕ → Automorphism μ → ℝ :=
    fun a b n T =>
      (∑ k ∈ Finset.range n,
        |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' (a.eval g)) ∩
                    (b.eval g))).toReal -
                 (μ (a.eval g)).toReal * (μ (b.eval g)).toReal|) / (n:ℝ)
  let O : HalmosTest → HalmosTest → ℕ → ℕ → Set (Automorphism μ) :=
    fun a b l N => ⋃ (n : {n : ℕ // N ≤ n}),
        {T : Automorphism μ | av a b n.1 T < (1 / ((l+1:ℕ):ℝ))}
  have hopen (a b : HalmosTest) (l N : ℕ) : IsOpen (O a b l N) := by
    dsimp [O]
    apply isOpen_iUnion
    intro n
    dsimp [av]
    apply isOpen_weak_average_lt μ n.1 (a.eval g) (b.eval g)
    · exact HalmosTest.measurable_eval g
        (fun i => MeasurableSpace.measurableSet_natGeneratingSequence i) a
    · exact HalmosTest.measurable_eval g
        (fun i => MeasurableSpace.measurableSet_natGeneratingSequence i) b
  have heq : HalmosSubseqSet μ =
      ⋂ a : HalmosTest, ⋂ b : HalmosTest,
        ⋂ l : ℕ, ⋂ N : ℕ, O a b l N := by
    ext T
    constructor
    · intro h
      have ht := h
      change ∀ (a b : HalmosTest) (l N : ℕ), _ at ht
      -- unpack the four countable intersections
      apply Set.mem_iInter.mpr
      intro a
      apply Set.mem_iInter.mpr
      intro b
      apply Set.mem_iInter.mpr
      intro l
      apply Set.mem_iInter.mpr
      intro N
      obtain ⟨n, hn, hv⟩ := ht a b l N
      apply Set.mem_iUnion.mpr
      refine ⟨(⟨n, hn⟩ : {n : ℕ // N ≤ n}), ?_⟩
      exact hv
    · intro h
      change ∀ (a b : HalmosTest) (l N : ℕ), _
      intro a b l N
      have hz := Set.mem_iInter.mp
        (Set.mem_iInter.mp
          (Set.mem_iInter.mp
            (Set.mem_iInter.mp h a) b) l) N
      rcases Set.mem_iUnion.mp hz with ⟨n, hn⟩
      exact ⟨n.1, n.2, hn⟩
  rw [heq]
  apply IsGδ.iInter
  intro a
  apply IsGδ.iInter
  intro b
  apply IsGδ.iInter
  intro l
  apply IsGδ.iInter
  intro N
  exact (hopen a b l N).isGδ

lemma weakMixing_mem_halmosSubseqSet
    {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Automorphism μ) (hT : IsWeaklyMixing μ T) :
    T ∈ HalmosSubseqSet μ := by
  classical
  let g : ℕ → Set Y := MeasurableSpace.natGeneratingSequence Y
  change ∀ (a b : HalmosTest) (l N : ℕ), _
  intro a b l N
  have ha : MeasurableSet (a.eval g) :=
    HalmosTest.measurable_eval g
      (fun i => MeasurableSpace.measurableSet_natGeneratingSequence i) a
  have hb : MeasurableSet (b.eval g) :=
    HalmosTest.measurable_eval g
      (fun i => MeasurableSpace.measurableSet_natGeneratingSequence i) b
  have ht := hT (a.eval g) (b.eval g) ha hb
  have hr : (0:ℝ) < (1 / ((l+1:ℕ):ℝ)) := by
    positivity
  have hev : ∀ᶠ n : ℕ in atTop,
      (∑ k ∈ Finset.range n,
          |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' (a.eval g)) ∩
                    (b.eval g))).toReal -
                 (μ (a.eval g)).toReal * (μ (b.eval g)).toReal|) / (n:ℝ)
        < (1 / ((l+1:ℕ):ℝ)) :=
      (tendsto_order.1 ht).2 _ hr
  obtain ⟨M, hM⟩ := (Filter.eventually_atTop.1 hev)
  let n : ℕ := max N M
  refine ⟨n, Nat.le_max_left _ _, ?_⟩
  exact hM n (Nat.le_max_right _ _)

-- The countable test condition already yields the same `liminf` smallness
-- for *all* measurable events.  The replacement estimate is uniform in
-- time, so a single approximation in the ring works for any requested
-- lower bound on the averaging length.
lemma halmosSubseq_all_tests
    {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Automorphism μ) (hT : T ∈ HalmosSubseqSet μ)
    (A B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (l N : ℕ) :
       ∃ n : ℕ, N ≤ n ∧
        (∑ k ∈ Finset.range n,
          |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
               (μ A).toReal * (μ B).toReal|) / (n:ℝ) <
          (1 / ((l+1:ℕ):ℝ)) := by
  classical
  let r : ℝ := 1 / ((l+1:ℕ):ℝ)
  have hr : 0 < r := by dsimp [r]; positivity
  let δ : ℝ := r / 20
  have hδ : 0 < δ := div_pos hr (by norm_num)
  obtain ⟨a, ha⟩ := exists_halmosTest_approx μ A hA
      (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨b, hb⟩ := exists_halmosTest_approx μ B hB
      (ENNReal.ofReal_pos.2 hδ)
  let g : ℕ → Set Y := MeasurableSpace.natGeneratingSequence Y
  let P : Set Y := a.eval g
  let Q : Set Y := b.eval g
  have hP : MeasurableSet P :=
    HalmosTest.measurable_eval g
      (fun i => MeasurableSpace.measurableSet_natGeneratingSequence i) a
  have hQ : MeasurableSet Q :=
    HalmosTest.measurable_eval g
      (fun i => MeasurableSpace.measurableSet_natGeneratingSequence i) b
  have hpa : (μ (A ∆ P)).toReal < δ := by
    have hh : μ (P ∆ A) < ENNReal.ofReal δ := by simpa [P, g] using ha
    have ht := ENNReal.toReal_lt_of_lt_ofReal hh
    simpa [symmDiff_comm] using ht
  have hqb : (μ (B ∆ Q)).toReal < δ := by
    have hh : μ (Q ∆ B) < ENNReal.ofReal δ := by simpa [Q, g] using hb
    have ht := ENNReal.toReal_lt_of_lt_ofReal hh
    simpa [symmDiff_comm] using ht
  let l' : ℕ := 2*l + 1
  obtain ⟨n, hn, hnsmall⟩ := hT a b l' N
  refine ⟨n, hn, ?_⟩
  have hcomp := weak_average_change_le μ T n A P B Q hA hP hB hQ
  have hsmall :
    (∑ k ∈ Finset.range n,
       |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal -
          (μ P).toReal * (μ Q).toReal|) / (n:ℝ) < r/2 := by
      have heq : (1 / ((l'+1:ℕ):ℝ)) = r/2 := by
        dsimp [l', r]
        push_cast
        field_simp
        <;> ring
      change (∑ k ∈ Finset.range n,
       |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' P) ∩ Q)).toReal -
          (μ P).toReal * (μ Q).toReal|) / (n:ℝ) <
            (1 / ((l'+1:ℕ):ℝ)) at hnsmall
      rw [heq] at hnsmall
      exact hnsmall
  -- the replacement cost is less than `r/5`, leaving plenty of room
  change _ < 1 / ((l+1:ℕ):ℝ)
  change _ < r
  dsimp [δ] at hpa hqb

  nlinarith

lemma isGδ_weakMixing_of_subseq_criterion
    {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (hcrit : ∀ T : Automorphism μ,
       T ∈ HalmosSubseqSet μ → IsWeaklyMixing μ T) :
    IsGδ {T : Automorphism μ | IsWeaklyMixing μ T} := by
  have heq : {T : Automorphism μ | IsWeaklyMixing μ T} =
      HalmosSubseqSet μ := by
    ext T
    constructor
    · intro h
      exact weakMixing_mem_halmosSubseqSet μ T h
    · intro h
      exact hcrit T h
  rw [heq]
  exact isGδ_halmosSubseqSet μ



-- A small real-analytic part of the passage from the usual G-delta
-- subsequence condition to weak mixing.  If the Cesaro averages of the
-- *squares* have a limit, then arbitrarily small Cesaro averages force
-- actual convergence to zero.  Isolating this estimate is useful since
-- the missing part in the spectral argument is precisely the existence
-- of the square-average limit; no uniformity on the small subsequence is
-- needed.
lemma tendsto_zero_average_of_subseq_of_square_limit
    (u : ℕ → ℝ)
    (hu₀ : ∀ k, 0 ≤ u k) (hu₁ : ∀ k, u k ≤ 1)
    (hsub : ∀ (l N : ℕ), ∃ n : ℕ, N ≤ n ∧
      (∑ k ∈ Finset.range n, u k) / (n : ℝ) <
        (1 / ((l+1:ℕ):ℝ)))
    {c : ℝ}
    (hsq : Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.range n, (u k)^2) / (n : ℝ))
      atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, u k) / (n : ℝ))
      atTop (𝓝 0) := by
  classical
  let av : ℕ → ℝ := fun n =>
    (∑ k ∈ Finset.range n, u k) / (n : ℝ)
  let sqav : ℕ → ℝ := fun n =>
    (∑ k ∈ Finset.range n, (u k)^2) / (n : ℝ)
  have hav_nonneg (n : ℕ) : 0 ≤ av n := by
    dsimp [av]
    exact div_nonneg (Finset.sum_nonneg
      (fun i hi => hu₀ i)) (by positivity)
  have hsq_nonneg (n : ℕ) : 0 ≤ sqav n := by
    dsimp [sqav]
    positivity
  have hsq_le (n : ℕ) : sqav n ≤ av n := by
    by_cases hn : n = 0
    · subst n
      simp [sqav, av]
    · have hnR : (0:ℝ) < (n:ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hn)
      apply (div_le_div_iff_of_pos_right hnR).2
      apply Finset.sum_le_sum
      intro k hk
      have h0 := hu₀ k
      have h1 := hu₁ k
      nlinarith
  have hc0 : 0 ≤ c := by
    exact ge_of_tendsto hsq
      (Filter.Eventually.of_forall (fun n => hsq_nonneg n))
  have hc : c = 0 := by
    apply le_antisymm ?_ hc0
    by_contra hcpos'
    have hcpos : 0 < c := lt_of_not_ge hcpos'
    -- a tail on which the limiting square average is above c/2
    have hevent : ∀ᶠ n : ℕ in atTop, c/2 < sqav n := by
      have hlt : c/2 < c := by linarith
      have ht := (tendsto_order.1 hsq).1 _ hlt
      exact ht
    obtain ⟨M, hM⟩ := (Filter.eventually_atTop.1 hevent)
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt (show (0:ℝ) < c/2 by linarith)
    obtain ⟨n, hn, hnsmall⟩ := hsub l M
    have hsquarelarge : c/2 < sqav n := hM n hn
    have hsmall : av n < (1 / (((l+1:ℕ)):ℝ)) := hnsmall
    have hfrac : (1 / (((l+1:ℕ)):ℝ)) = (1 / ((l:ℝ) + 1)) := by
      push_cast
      rfl
    rw [hfrac] at hsmall
    have hle' := hsq_le n
    -- the square average cannot sit strictly between these two bounds
    linarith
  have hsq0 : Tendsto sqav atTop (𝓝 (0:ℝ)) := by
    simpa [sqav, hc] using hsq
  -- Cauchy--Schwarz on a finite block.  Written with `g = 1`, it says
  -- that the square of the average is bounded by the average of squares.
  have hav_sq_le (n : ℕ) (hn : n ≠ 0) : (av n)^2 ≤ sqav n := by
    have hnR : (0:ℝ) < (n:ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (R := ℝ) (Finset.range n) u (fun _ : ℕ => (1:ℝ))
    have hcalc1 : (∑ i ∈ Finset.range n, u i * (1:ℝ)) =
        ∑ i ∈ Finset.range n, u i := by
      simp
    have hcalc2 : (∑ _i ∈ Finset.range n, (1:ℝ) ^ 2) = (n:ℝ) := by
      simp
    rw [hcalc1, hcalc2] at hcs
    dsimp [av, sqav]
    -- divide the squared inequality by `n^2`
    have hnR0 : (n:ℝ) ≠ 0 := ne_of_gt hnR
    calc
      ((∑ k ∈ Finset.range n, u k) / (n:ℝ))^2 =
          (∑ k ∈ Finset.range n, u k)^2 / (n:ℝ)^2 := by ring
      _ ≤ ((∑ k ∈ Finset.range n, (u k)^2) * (n:ℝ)) /
            (n:ℝ)^2 := by
            exact (div_le_div_of_nonneg_right hcs (by positivity))
      _ = (∑ k ∈ Finset.range n, (u k)^2) / (n:ℝ) := by
            field_simp
  -- and now the epsilon proof; the exceptional value `n=0` is simply
  -- discarded together with the initial finite part of the sequence.
  change Tendsto av atTop (𝓝 (0:ℝ))
  apply (Metric.tendsto_atTop).2
  intro ε hε
  have hεsq : 0 < ε^2 := sq_pos_of_pos hε
  have hevsmall : ∀ᶠ n : ℕ in atTop, sqav n < ε^2 :=
    (tendsto_order.1 hsq0).2 _ hεsq
  have hevpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hevdist : ∀ᶠ n : ℕ in atTop, dist (av n) (0:ℝ) < ε := by
    filter_upwards [hevsmall, hevpos] with n hnsmall hnpos
    have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
    have hav2 : (av n)^2 < ε^2 := lt_of_le_of_lt (hav_sq_le n hn0) hnsmall
    have havlt : av n < ε := by
      nlinarith [hav_nonneg n]
    have hz : dist (av n) (0:ℝ) = av n := by
      simp [Real.dist_eq, abs_of_nonneg (hav_nonneg n)]
    simpa [Real.dist_eq, abs_of_nonneg (hav_nonneg n)] using havlt
  exact (Filter.eventually_atTop.1 hevdist)

-- A formulation directly suited to the set averages.  Once a square
-- Cesaro limit has been supplied (by the Koopman/mean-ergodic argument),
-- the countable subsequence condition already gives the *whole* weak
-- mixing limit.  All estimates here are on probabilities, so the bound
-- `u k ≤ 1` costs nothing.
-- A coefficient version of von Neumann's mean ergodic theorem.  The
-- packaging of this consequence is convenient: in applications to weak
-- mixing one applies it on the product Hilbert space, to the tensor-square
-- of the two indicator vectors.  The limit need not be identified here.
lemma real_inner_iterate_cesaro_has_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (L : H →ₗᵢ[ℝ] H) (x y : H) :
    ∃ c : ℝ, Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.range n,
        @inner ℝ _ _ ((L : H → H)^[k] x) y) / (n:ℝ))
      atTop (𝓝 c) := by
  let F : H →L[ℝ] H := L.toContinuousLinearMap
  have hn : ‖F‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le L
  have ht :=
    ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection F hn x
  let z : H := ((F.eqLocus (1 : H →L[ℝ] H)).orthogonalProjectionOnto x : H)
  refine ⟨inner ℝ z y, ?_⟩
  have hc : Tendsto
      (fun n : ℕ =>
        inner ℝ (birkhoffAverage ℝ (F : H → H) id n x) y)
      atTop (𝓝 (inner ℝ z y)) := by
    exact ht.inner tendsto_const_nhds
  have heq (k : ℕ) : ((F : H → H)^[k] x) =
        ((L : H → H)^[k] x) := by rfl
  have hinner (n : ℕ) :
      inner ℝ (∑ k ∈ Finset.range n, ((L : H → H)^[k] x)) y =
        ∑ k ∈ Finset.range n, inner ℝ ((L : H → H)^[k] x) y := by
    rw [real_inner_comm, inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
  have hpoint (n : ℕ) :
      (∑ k ∈ Finset.range n, inner ℝ ((L : H → H)^[k] x) y) /
          (n:ℝ) =
        inner ℝ (birkhoffAverage ℝ (F : H → H) id n x) y := by
    simp [birkhoffAverage, birkhoffSum, real_inner_smul_left,
      heq, hinner, div_eq_mul_inv, mul_comm]
  have he : (fun n : ℕ => (∑ k ∈ Finset.range n,
      @inner ℝ _ _ ((L : H → H)^[k] x) y) / (n:ℝ)) =
      (fun n : ℕ => inner ℝ (birkhoffAverage ℝ (F : H → H) id n x) y) := by
    funext n
    exact hpoint n
  rw [he]
  exact hc



-- L2 and product helpers giving the square-Cesaro limit for every measure-preserving map.
lemma l2_comp_indicator_preimage
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (f : Y → Y) (hf : MeasurePreserving f μ μ)
    (A : Set Y) (hA : MeasurableSet A) (k : ℕ) :
    ((Lp.compMeasurePreserving (E:=ℝ) (p:=(2:ENNReal)) f hf)^[k])
       (indicatorConstLp (p:=(2:ENNReal)) hA (measure_ne_top μ A) (1:ℝ))
       = indicatorConstLp (p:=(2:ENNReal))
          ((hf.iterate k).measurable hA)
          (measure_ne_top μ ((f^[k]) ⁻¹' A)) (1:ℝ) := by
    rw [Lp.compMeasurePreserving_iterate hf k]
    -- functions agree a.e.
    apply Lp.ext (μ := μ)
    have hco := Lp.coeFn_compMeasurePreserving
       (f := f^[k]) (indicatorConstLp (p:=(2:ENNReal)) hA (measure_ne_top μ A) (1:ℝ))
       (hf.iterate k)
    -- hco: comp... =ᵐ comp
    -- target eq via trans
    refine hco.trans ?_
    have hleft := @indicatorConstLp_coeFn Y _ _ (2:ENNReal) μ _ A hA (measure_ne_top μ A) (1:ℝ)
    have hright := @indicatorConstLp_coeFn Y _ _ (2:ENNReal) μ _ ((f^[k]) ⁻¹' A) ((hf.iterate k).measurable hA) (measure_ne_top μ ((f^[k]) ⁻¹' A)) (1:ℝ)
    -- need comp a.e. pullback: preimage of ae along measure-preserving
    have hpull : (fun x => (indicatorConstLp (p:=(2:ENNReal)) hA (measure_ne_top μ A) (1:ℝ)) (f^[k] x))
                    =ᵐ[μ]
               (fun x => (A.indicator (fun _ : Y => (1:ℝ))) (f^[k] x)) :=
        (hf.iterate k).quasiMeasurePreserving.ae_eq_comp hleft
    have hpt :
        (fun x => (A.indicator (fun _ : Y => (1:ℝ))) (f^[k] x))
          =ᵐ[μ] (fun x => ((f^[k]) ⁻¹' A).indicator (fun _ : Y => (1:ℝ)) x) := by
      filter_upwards [] with x
      by_cases hx : f^[k] x ∈ A
      · rw [Set.indicator_of_mem hx]
        rw [Set.indicator_of_mem (show x ∈ (f^[k]) ⁻¹' A from hx)]
      · rw [Set.indicator_of_notMem hx]
        rw [Set.indicator_of_notMem (show x ∉ (f^[k]) ⁻¹' A from hx)]
    exact hpull.trans (hpt.trans hright.symm)


lemma correlation_iterate_cesaro_has_limit
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : Y → Y) (hf : MeasurePreserving f μ μ)
    (A B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∃ c : ℝ, Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.range n,
        (μ ((f^[k] ⁻¹' A) ∩ B)).toReal) / (n:ℝ))
      atTop (𝓝 c) := by
  let L : Lp ℝ (2:ENNReal) μ →ₗᵢ[ℝ] Lp ℝ (2:ENNReal) μ :=
     Lp.compMeasurePreservingₗᵢ ℝ f hf
  let x : Lp ℝ (2:ENNReal) μ :=
    indicatorConstLp (p:=(2:ENNReal)) hA (measure_ne_top μ A) (1:ℝ)
  let y : Lp ℝ (2:ENNReal) μ :=
    indicatorConstLp (p:=(2:ENNReal)) hB (measure_ne_top μ B) (1:ℝ)
  obtain ⟨c, hc⟩ := real_inner_iterate_cesaro_has_limit L x y
  refine ⟨c, ?_⟩
  have heach (k : ℕ) :
      inner ℝ (((L : Lp ℝ (2:ENNReal) μ → Lp ℝ (2:ENNReal) μ)^[k]) x) y
       = (μ ((f^[k] ⁻¹' A) ∩ B)).toReal := by
    have hpre := l2_comp_indicator_preimage μ f hf A hA k
    have heqL : ((L : Lp ℝ (2:ENNReal) μ → Lp ℝ (2:ENNReal) μ)^[k]) x =
       indicatorConstLp (p:=(2:ENNReal))
          ((hf.iterate k).measurable hA)
          (measure_ne_top μ ((f^[k]) ⁻¹' A)) (1:ℝ) := by
      dsimp [L, x]
      -- equality of iterates of linear isometry vs additive map
      exact hpre
    rw [heqL]
    dsimp [y]
    exact L2.real_inner_indicatorConstLp_one_indicatorConstLp_one _ _ _ _
  -- replace summands
  simpa [heach] using hc


lemma square_correlation_iterate_has_limit
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : Y → Y) (hf : MeasurePreserving f μ μ)
    (A B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∃ c : ℝ, Tendsto
        (fun n : ℕ =>
          (∑ k ∈ Finset.range n,
            (|(μ ((f^[k]) ⁻¹' A ∩ B)).toReal -
                (μ A).toReal * (μ B).toReal|)^2) / (n:ℝ))
        atTop (𝓝 c) := by
  classical
  let p : ℕ → ℝ := fun k => (μ ((f^[k]) ⁻¹' A ∩ B)).toReal
  let d : ℝ := (μ A).toReal * (μ B).toReal
  obtain ⟨c₁, hc₁⟩ := correlation_iterate_cesaro_has_limit μ f hf A B hA hB
  have hc1 : Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.range n, p k) / (n:ℝ)) atTop (𝓝 c₁) := by
    simpa [p] using hc₁
  let g : (Y × Y) → (Y × Y) := Prod.map f f
  have hg : MeasurePreserving g (μ.prod μ) (μ.prod μ) := hf.prod hf
  let AA : Set (Y × Y) := A ×ˢ A
  let BB : Set (Y × Y) := B ×ˢ B
  have hAA : MeasurableSet AA := hA.prod hA
  have hBB : MeasurableSet BB := hB.prod hB
  obtain ⟨c₂, hc₂⟩ := correlation_iterate_cesaro_has_limit (μ.prod μ) g hg AA BB hAA hBB
  have hp2 (k : ℕ) :
      ((μ.prod μ) (g^[k] ⁻¹' AA ∩ BB)).toReal = (p k)^2 := by
    have hfst : Function.Semiconj (fun z : Y × Y => z.1) g f := by
      intro z; rfl
    have hsnd : Function.Semiconj (fun z : Y × Y => z.2) g f := by
      intro z; rfl
    have hiter (z : Y × Y) : (g^[k]) z = ((f^[k]) z.1, (f^[k]) z.2) := by
      apply Prod.ext
      · exact hfst.iterate_right k z
      · exact hsnd.iterate_right k z
    have hset : g^[k] ⁻¹' AA ∩ BB =
        ((f^[k] ⁻¹' A ∩ B) ×ˢ (f^[k] ⁻¹' A ∩ B)) := by
      ext z
      rcases z with ⟨x,y⟩
      simp only [Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_prod]
      -- rewrite iterate coordinate
      rw [hiter (x,y)]
      change (((f^[k]) x ∈ A ∧ (f^[k]) y ∈ A) ∧
              (x ∈ B ∧ y ∈ B)) ↔ _
      tauto
    rw [hset, Measure.prod_prod]
    dsimp [p]
    rw [ENNReal.toReal_mul]
    ring
  have hc2 : Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.range n, (p k)^2) / (n:ℝ)) atTop (𝓝 c₂) := by
    have he : (fun n : ℕ =>
      (∑ k ∈ Finset.range n, ((μ.prod μ) (g^[k] ⁻¹' AA ∩ BB)).toReal) /
          (n:ℝ)) =
       (fun n : ℕ => (∑ k ∈ Finset.range n, (p k)^2) /(n:ℝ)) := by
      funext n
      apply congrArg (fun t : ℝ => t / (n:ℝ))
      apply Finset.sum_congr rfl
      intro k hk
      exact hp2 k
    rw [← he]
    exact hc₂
  refine ⟨c₂ - 2*d*c₁ + d^2, ?_⟩
  have ht : Tendsto
       (fun n : ℕ =>
          (∑ k ∈ Finset.range n, (p k)^2) / (n:ℝ) -
             2*d*((∑ k ∈ Finset.range n, p k)/(n:ℝ)) + d^2)
       atTop (𝓝 (c₂ - 2*d*c₁ + d^2)) := by
    convert (hc2.sub ((tendsto_const_nhds.mul tendsto_const_nhds).mul hc1) |>.add tendsto_const_nhds) using 1
  -- use eventual equality algebra
  apply (tendsto_congr' ?_).2 ht
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  -- expand summation
  change (∑ k ∈ Finset.range n, |p k - d|^2)/(n:ℝ) =
     (∑ k ∈ Finset.range n, (p k)^2)/(n:ℝ) -
       2*d*((∑ k ∈ Finset.range n, p k)/(n:ℝ)) + d^2
  simp_rw [sq_abs]
  have he :
      (∑ k ∈ Finset.range n, (p k - d)^2) =
        (∑ k ∈ Finset.range n, (p k)^2) -
          (2*d)*(∑ k ∈ Finset.range n, p k) + (n:ℝ)*d^2 := by
    calc
      _ = ∑ k ∈ Finset.range n,
          ((p k)^2 - (2*d)*p k + d^2) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
        simp
  rw [he]
  field_simp


lemma automorphism_square_correlation_has_limit
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Automorphism μ) (A B : Set Y)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∃ c : ℝ, Tendsto
        (fun n : ℕ =>
          (∑ k ∈ Finset.range n,
            (|(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
                (μ A).toReal * (μ B).toReal|)^2) / (n:ℝ))
        atTop (𝓝 c) := by
  exact square_correlation_iterate_has_limit μ
    (T.toEquiv : Y → Y) T.measurePreserving A B hA hB


lemma weakMixing_of_halmosSubseq_of_square_limits
    {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Automorphism μ) (hT : T ∈ HalmosSubseqSet μ)
    (hsquare : ∀ (A B : Set Y), MeasurableSet A → MeasurableSet B →
      ∃ c : ℝ, Tendsto
        (fun n : ℕ =>
          (∑ k ∈ Finset.range n,
            (|(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
                (μ A).toReal * (μ B).toReal|)^2) / (n:ℝ))
        atTop (𝓝 c)) :
    IsWeaklyMixing μ T := by
  classical
  intro A B hA hB
  let u : ℕ → ℝ := fun k =>
      |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
          (μ A).toReal * (μ B).toReal|
  have hu0 (k : ℕ) : 0 ≤ u k := abs_nonneg _
  have hprob (S : Set Y) : 0 ≤ (μ S).toReal ∧ (μ S).toReal ≤ 1 := by
    constructor
    · exact ENNReal.toReal_nonneg
    · have hle : μ S ≤ (1 : ENNReal) := prob_le_one
      simpa using
        (ENNReal.toReal_mono (by simp : (1:ENNReal) ≠ ⊤) hle)
  have hu1 (k : ℕ) : u k ≤ 1 := by
    -- both the intersection probability and the product probability are
    -- in [0,1]
    have hx := hprob ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)
    have ha := hprob A
    have hb := hprob B
    change
      |(μ ((((T.toEquiv : Y → Y)^[k]) ⁻¹' A) ∩ B)).toReal -
          (μ A).toReal * (μ B).toReal| ≤ 1
    have hp0 : 0 ≤ (μ A).toReal * (μ B).toReal :=
      mul_nonneg ha.1 hb.1
    have hp1 : (μ A).toReal * (μ B).toReal ≤ 1 := by
      nlinarith
    rw [abs_le]
    constructor <;> nlinarith
  obtain ⟨c, hc⟩ := hsquare A B hA hB
  have hsub : ∀ (l N : ℕ), ∃ n : ℕ, N ≤ n ∧
      (∑ k ∈ Finset.range n, u k) / (n:ℝ) <
        (1 / ((l+1:ℕ):ℝ)) := by
    intro l N
    simpa [u] using
      (halmosSubseq_all_tests μ T hT A B hA hB l N)
  have hlim := tendsto_zero_average_of_subseq_of_square_limit u hu0 hu1
      hsub (c := c) (by simpa [u] using hc)
  simpa [u] using hlim


-- A general integer-coordinate translation.  We will use a positive stride
-- when several independent streams of fair bits are needed.  Keeping the
-- stride in the index permutation (rather than regrouping infinitePi) avoids
-- any issue about iterated product sigma algebras.
def intSubEquiv (a : ℤ) : ℤ ≃ ℤ where
  toFun n := n - a
  invFun n := n + a
  left_inv n := by simp
  right_inv n := by simp

@[simp] lemma intSubEquiv_apply (a n : ℤ) : intSubEquiv a n = n-a := rfl
@[simp] lemma intSubEquiv_symm_apply (a n : ℤ) : (intSubEquiv a).symm n = n+a := rfl

noncomputable def intTranslateMeasurableEquiv
    (V : Type*) [MeasurableSpace V] (a : ℤ) :
    (ℤ → V) ≃ᵐ (ℤ → V) :=
  MeasurableEquiv.piCongrLeft (fun _ : ℤ => V) (intSubEquiv a)

@[simp] lemma intTranslateMeasurableEquiv_apply
    (V : Type*) [MeasurableSpace V] (a : ℤ) (w : ℤ → V) (n : ℤ) :
    intTranslateMeasurableEquiv V a w n = w (n+a) := by
  change (MeasurableEquiv.piCongrLeft (fun _ : ℤ => V)
       (intSubEquiv a)) w n = _
  have h := MeasurableEquiv.piCongrLeft_apply_apply
      (intSubEquiv a) (β := fun _ : ℤ => V) w ((intSubEquiv a).symm n)
  simpa using h

noncomputable def intTranslateAutomorphism
    (V : Type*) [MeasurableSpace V] (p : Measure V)
    [IsProbabilityMeasure p] (a : ℤ) :
    Automorphism (Measure.infinitePi (fun _ : ℤ => p)) where
  toEquiv := intTranslateMeasurableEquiv V a
  measurePreserving := by
    refine ⟨?_, ?_⟩
    · exact (intTranslateMeasurableEquiv V a).measurable
    · simpa [intTranslateMeasurableEquiv] using
        (Measure.infinitePi_map_piCongrLeft
          (μ := fun _ : ℤ => p) (intSubEquiv a))

lemma intTranslate_iterate
    (V : Type*) [MeasurableSpace V] (p : Measure V)
    [IsProbabilityMeasure p] (a : ℤ)
    (k : ℕ) (w : ℤ → V) (n : ℤ) :
    (((intTranslateAutomorphism V p a).toEquiv : (ℤ → V) → (ℤ → V))^[k] w) n =
       w (n + (k:ℤ)*a) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change intTranslateMeasurableEquiv V a _ n = _
      rw [intTranslateMeasurableEquiv_apply]
      rw [ih]
      congr 1
      push_cast
      ring

-- Positive strides send any finite block past another.  This will also show
-- that a product shift with finitely many independent streams is still
-- strongly mixing.
lemma int_finset_eventually_disjoint_mul (I J : Finset ℤ) (a : ℕ)
    (ha : 0 < a) :
    ∃ N : ℕ, ∀ k ≥ N,
      Disjoint (I.image (fun i : ℤ => i + (k : ℤ) * (a:ℤ))) J := by
  classical
  let N : ℕ := (∑ i ∈ I, i.natAbs) + (∑ j ∈ J, j.natAbs) + 1
  refine ⟨N, ?_⟩
  intro k hk
  apply Finset.disjoint_left.2
  intro z hz hzJ
  rcases Finset.mem_image.1 hz with ⟨i, hi, rfl⟩
  have hiabs : i.natAbs ≤ ∑ t ∈ I, t.natAbs :=
    Finset.single_le_sum (fun t ht => Nat.zero_le _) hi
  have hjabs : (i + (k:ℤ)*(a:ℤ)).natAbs ≤ ∑ t ∈ J, t.natAbs :=
    Finset.single_le_sum (fun t ht => Nat.zero_le _) hzJ
  have hi_low : -(i.natAbs : ℤ) ≤ i := by
    have hh : (-i) ≤ (i.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -i))
    omega
  have hj_up : i + (k:ℤ)*(a:ℤ) ≤
       ((i + (k:ℤ)*(a:ℤ)).natAbs : ℤ) := Int.le_natAbs
  have hcast_i : (i.natAbs : ℤ) ≤
       ((∑ t ∈ I, t.natAbs):ℤ) := by exact_mod_cast hiabs
  have hcast_j : ((i + (k:ℤ)*(a:ℤ)).natAbs:ℤ) ≤
       ((∑ t ∈ J, t.natAbs):ℤ) := by exact_mod_cast hjabs
  have hcastk : (((∑ t ∈ I, t.natAbs) + (∑ t ∈ J, t.natAbs) + 1 : ℕ) : ℤ) ≤ (k:ℤ) := by
    dsimp [N] at hk
    exact_mod_cast hk
  have ha1 : (1:ℤ) ≤ (a:ℤ) := by exact_mod_cast ha
  have hk0 : (0:ℤ) ≤ (k:ℤ) := by exact_mod_cast (Nat.zero_le k)
  push_cast at hcastk
  simp [Int.natCast_natAbs] at hcast_i hcast_j hi_low hj_up
  nlinarith

lemma intTranslate_cylinder_eventual
    (V : Type*) [MeasurableSpace V] (p : Measure V)
    [IsProbabilityMeasure p] (a : ℕ) (ha : 0 < a) :
    ∀ P ∈ measurableCylinders (fun _ : ℤ => V),
      ∀ Q ∈ measurableCylinders (fun _ : ℤ => V),
        ∃ N : ℕ, ∀ k ≥ N,
          (Measure.infinitePi (fun _ : ℤ => p))
              ((((intTranslateAutomorphism V p (a:ℤ)).toEquiv :
                   (ℤ → V) → (ℤ → V))^[k] ⁻¹' P) ∩ Q) =
            (Measure.infinitePi (fun _ : ℤ => p)) P *
              (Measure.infinitePi (fun _ : ℤ => p)) Q := by
  classical
  intro P hP Q hQ
  rcases (mem_measurableCylinders P).1 hP with ⟨I, S, hS, rfl⟩
  rcases (mem_measurableCylinders Q).1 hQ with ⟨J, R, hR, rfl⟩
  obtain ⟨N, hN⟩ := int_finset_eventually_disjoint_mul I J a ha
  refine ⟨N, ?_⟩
  intro k hk
  let g : ℤ → ℤ := fun i => i + (k:ℤ)*(a:ℤ)
  have hg : Function.Injective g := by
    intro x y hxy
    dsimp [g] at hxy
    linarith
  let I' : Finset ℤ := I.image g
  have hgood : Disjoint I' J := by simpa [I', g] using hN k hk
  let phi : (∀ j : (↥I'), V) → (∀ i : (↥I), V) :=
    fun w i => w ⟨g (i:ℤ), (by
      dsimp [I']
      exact Finset.mem_image.2 ⟨(i:ℤ), i.property, rfl⟩)⟩
  have hphi : Measurable phi := by unfold phi; fun_prop
  let S' : Set (∀ j : (↥I'), V) := phi ⁻¹' S
  have hS' : MeasurableSet S' := hphi hS
  have hpre :
      ((((intTranslateAutomorphism V p (a:ℤ)).toEquiv :
          (ℤ → V) → (ℤ → V))^[k] ⁻¹' cylinder I S)) =
        cylinder I' S' := by
    ext w
    change (((((intTranslateAutomorphism V p (a:ℤ)).toEquiv :
          (ℤ → V) → (ℤ → V))^[k]) w) ∈ cylinder I S) ↔
            w ∈ cylinder I' S'
    simp only [mem_cylinder]
    change (I.restrict
      ((((intTranslateAutomorphism V p (a:ℤ)).toEquiv :
          (ℤ → V) → (ℤ → V))^[k]) w) ∈ S) ↔
        (phi (I'.restrict w) ∈ S)
    have hfun : I.restrict
      ((((intTranslateAutomorphism V p (a:ℤ)).toEquiv :
          (ℤ → V) → (ℤ → V))^[k]) w) = phi (I'.restrict w) := by
      funext i
      change (((((intTranslateAutomorphism V p (a:ℤ)).toEquiv :
          (ℤ → V) → (ℤ → V))^[k]) w) (i:ℤ)) = _
      rw [intTranslate_iterate V p (a:ℤ) k w (i:ℤ)]
      rfl
    rw [hfun]
  have hind := infinitePi_cylinders_indep
      (ι := ℤ) (Z := fun _ : ℤ => V) (fun _ : ℤ => p)
         hgood hS' hR
  have hmeas : MeasurableSet (cylinder I S : Set (ℤ → V)) := hS.cylinder
  have hmp : MeasurePreserving
      ((((intTranslateAutomorphism V p (a:ℤ)).toEquiv :
          (ℤ → V) → (ℤ → V))^[k]))
        (Measure.infinitePi (fun _ : ℤ => p))
        (Measure.infinitePi (fun _ : ℤ => p)) :=
      (intTranslateAutomorphism V p (a:ℤ)).measurePreserving.iterate k
  have hmass :
      (Measure.infinitePi (fun _ : ℤ => p)) (cylinder I' S') =
        (Measure.infinitePi (fun _ : ℤ => p)) (cylinder I S) := by
    rw [← hpre]
    exact hmp.measure_preimage hmeas.nullMeasurableSet
  rw [hpre]
  simpa [hmass] using hind

lemma intTranslate_weakMixing
    (V : Type*) [MeasurableSpace V] (p : Measure V)
    [IsProbabilityMeasure p] (a : ℕ) (ha : 0 < a) :
    IsWeaklyMixing (Measure.infinitePi (fun _ : ℤ => p))
      (intTranslateAutomorphism V p (a:ℤ)) := by
  classical
  apply weakMixing_of_cylinder_eventual
    (μ := Measure.infinitePi (fun _ : ℤ => p))
    (T := intTranslateAutomorphism V p (a:ℤ))
  exact intTranslate_cylinder_eventual V p a ha

-- Images of a block cylinder can be read on its base.  It is important here
-- that the word map is an actual permutation rather than an a.e. code.
lemma fairBlock_image_cylinder
    (K : Finset ℤ)
    (σ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
    (H : Set (∀ _i : (↥K), Bool)) :
    (fairBlockAutomorphism K σ).toEquiv ''
        (cylinder (α := fun _ : ℤ => Bool) K H) =
      cylinder (α := fun _ : ℤ => Bool) K (σ '' H) := by
  classical
  ext w
  constructor
  · intro hw
    rcases hw with ⟨z, hz, hzw⟩
    have hz' : K.restrict z ∈ H := (mem_cylinder K H z).1 hz
    have hw' : K.restrict w = σ (K.restrict z) := by
      rw [← hzw]
      exact fairBlockMeasurableEquiv_restrict K σ z
    exact (mem_cylinder K (σ '' H) w).2
      ⟨K.restrict z, hz', hw'.symm⟩
  · intro hw
    have hw' : K.restrict w ∈ σ '' H := (mem_cylinder K (σ '' H) w).1 hw
    rcases hw' with ⟨x, hx, hxe⟩
    -- undo the equivalence on w; its restriction is x
    let z : (ℤ → Bool) := (fairBlockMeasurableEquiv K σ).symm w
    have hzw : fairBlockMeasurableEquiv K σ z = w := by
      exact (fairBlockMeasurableEquiv K σ).apply_symm_apply w
    have hzres : K.restrict z = x := by
      have h := fairBlockMeasurableEquiv_restrict K σ z
      rw [hzw] at h
      exact σ.injective (h.symm.trans hxe.symm)
    refine ⟨z, (mem_cylinder K H z).2 (by simpa [hzres] using hx), ?_⟩
    exact hzw

-- A useful stopping point in the Rokhlin part is a *finite-window clock*.
-- If the ordinary shift has a finite coding of the K-word whose colours
-- advance by `σ` off a set of measure < r, and a measure preserving change
-- of coordinates sends the literal K-word to this code, the desired weak
-- mixer is immediate.  The proof is just conjugacy and has no a.e.
-- representatives.  Thus a future construction of markers in the iid bits
-- has a very small interface to meet.
lemma fair_block_tower_of_code
    (K : Finset ℤ)
    (σ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
    (r : ℝ)
    (a : ℕ) (ha : 0 < a)
    (E : (∀ _i : (↥K), Bool) → Set (ℤ → Bool))
    (U : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)))
    (hcode : ∀ H : Set (∀ _i : (↥K), Bool),
       U.toEquiv '' (cylinder (α := fun _ : ℤ => Bool) K H) =
         ⋃ b : {z : (∀ _i : (↥K), Bool) // z ∈ H}, E b.1)
    (hclock : ∀ H : Set (∀ _i : (↥K), Bool),
       (Measure.infinitePi (fun _ : ℤ => fairBool))
          (((intTranslateAutomorphism Bool fairBool (a:ℤ)).toEquiv ''
              (⋃ b : {z : (∀ _i : (↥K), Bool) // z ∈ H}, E b.1)) ∆
            (⋃ b : {z : (∀ _i : (↥K), Bool) // z ∈ σ '' H}, E b.1)) <
          ENNReal.ofReal r) :
    ∃ V : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)),
       IsWeaklyMixing (Measure.infinitePi (fun _ : ℤ => fairBool)) V ∧
       ∀ H : Set (∀ _i : (↥K), Bool),
        (Measure.infinitePi (fun _ : ℤ => fairBool))
          ((V.toEquiv '' (cylinder (α := fun _ : ℤ => Bool) K H)) ∆
            ((fairBlockAutomorphism K σ).toEquiv ''
                (cylinder (α := fun _ : ℤ => Bool) K H))) <
          ENNReal.ofReal r := by
  classical
  let μ : Measure (ℤ → Bool) :=
    Measure.infinitePi (fun _ : ℤ => fairBool)
  let R : Automorphism μ := intTranslateAutomorphism Bool fairBool (a:ℤ)
  let V : Automorphism μ := conjugateAutomorphism μ U R
  have hmixR : IsWeaklyMixing μ R :=
    intTranslate_weakMixing Bool fairBool a ha
  have hmix : IsWeaklyMixing μ V :=
    conjugate_weakMixing μ U R hmixR
  refine ⟨V, hmix, ?_⟩
  intro H
  let C : Set (ℤ → Bool) := cylinder (α := fun _ : ℤ => Bool) K H
  let C' : Set (ℤ → Bool) :=
      cylinder (α := fun _ : ℤ => Bool) K (σ '' H)
  have htarget : (fairBlockAutomorphism K σ).toEquiv '' C = C' := by
    dsimp [C, C']
    exact fairBlock_image_cylinder K σ H
  -- measure the error after applying U.  Image under a measurable equivalence
  -- preserves all sets, not only Borel ones.
  have himV : U.toEquiv '' (V.toEquiv '' C) = R.toEquiv '' (U.toEquiv '' C) := by
    -- this is precisely the transport image formula
    exact transport_image μ μ U.toEquiv U.measurePreserving R C
  have hdist : μ ((V.toEquiv '' C) ∆ C') =
        μ ((R.toEquiv '' (U.toEquiv '' C)) ∆ (U.toEquiv '' C')) := by
    calc
      μ ((V.toEquiv '' C) ∆ C') =
          μ (U.toEquiv '' ((V.toEquiv '' C) ∆ C')) := by
             symm
             exact automorphism_measure_image μ U _
      _ = μ ((U.toEquiv '' (V.toEquiv '' C)) ∆
              (U.toEquiv '' C')) := by
             rw [Set.image_symmDiff U.toEquiv.injective]
      _ = _ := by rw [himV]
  have hc0 : U.toEquiv '' C =
         ⋃ b : {z : (∀ _i : (↥K), Bool) // z ∈ H}, E b.1 := by
    exact hcode H
  have hc1 : U.toEquiv '' C' =
         ⋃ b : {z : (∀ _i : (↥K), Bool) // z ∈ σ '' H}, E b.1 := by
    exact hcode (σ '' H)
  change μ ((V.toEquiv '' C) ∆
      ((fairBlockAutomorphism K σ).toEquiv '' C)) < _
  rw [htarget]
  rw [hdist, hc0, hc1]
  exact hclock H

-- purely finite-window/renewal input.  There is no weak mixing in this
-- predicate; the only transformation mentioned in the clock error is a
-- fixed positive translation, whose mixing was proved above.  For example a
-- sparse-marker colouring of fair bits is expected to provide these data.
def HasFiniteClocks : Prop :=
  ∀ (K : Finset ℤ)
    (σ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
    (r : ℝ), 0 < r →
    ∃ (a : ℕ), ∃ ha : 0 < a,
      ∃ (E : (∀ _i : (↥K), Bool) → Set (ℤ → Bool)),
      ∃ U : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)),
       (∀ H : Set (∀ _i : (↥K), Bool),
         U.toEquiv '' (cylinder (α := fun _ : ℤ => Bool) K H) =
           ⋃ b : {z : (∀ _i : (↥K), Bool) // z ∈ H}, E b.1) ∧
       (∀ H : Set (∀ _i : (↥K), Bool),
        (Measure.infinitePi (fun _ : ℤ => fairBool))
          (((intTranslateAutomorphism Bool fairBool (a:ℤ)).toEquiv ''
              (⋃ b : {z : (∀ _i : (↥K), Bool) // z ∈ H}, E b.1)) ∆
            (⋃ b : {z : (∀ _i : (↥K), Bool) // z ∈ σ '' H}, E b.1)) <
          ENNReal.ofReal r)

lemma fair_tower_of_finiteClocks (hclock : HasFiniteClocks) :
    ∀ (K : Finset ℤ)
      (σ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
      (r : ℝ), 0 < r →
        ∃ V : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)),
          IsWeaklyMixing (Measure.infinitePi (fun _ : ℤ => fairBool)) V ∧
          ∀ H : Set (∀ _i : (↥K), Bool),
            (Measure.infinitePi (fun _ : ℤ => fairBool))
              ((V.toEquiv '' (cylinder (α := fun _ : ℤ => Bool) K H)) ∆
               ((fairBlockAutomorphism K σ).toEquiv ''
                 (cylinder (α := fun _ : ℤ => Bool) K H))) <
                ENNReal.ofReal r := by
  intro K σ r hr
  obtain ⟨a, ha, E, U, hmap, herr⟩ := hclock K σ r hr
  exact fair_block_tower_of_code K σ r a ha E U hmap herr

noncomputable def encodeFiber {α β : Type*} [Fintype α]
    [Fintype β] [DecidableEq β] (f : α → β) :
    α ≃ (b : β) × {x : α // f x = b} := by
  classical
  exact
    { toFun := fun x => ⟨f x, ⟨x, rfl⟩⟩
      invFun := fun z => z.2.1
      left_inv := fun x => rfl
      right_inv := by
        intro z
        rcases z with ⟨b,⟨x,hx⟩⟩
        have h : f x = b := hx
        subst b
        rfl }

noncomputable def permOfFiberCards {α β : Type*} [Fintype α]
    [Fintype β] [DecidableEq β]
    (f g : α → β)
    (h : ∀ b : β, Nat.card {x : α // f x = b} =
                    Nat.card {x : α // g x = b}) : α ≃ α := by
  classical
  let eb (b : β) : {x : α // f x = b} ≃ {x : α // g x = b} :=
    Fintype.equivOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using h b)
  exact (encodeFiber f).trans
    ((Equiv.sigmaCongrRight eb).trans (encodeFiber g).symm)

@[simp] lemma permOfFiberCards_spec {α β : Type*} [Fintype α]
    [Fintype β] [DecidableEq β]
    (f g : α → β)
    (h : ∀ b : β, Nat.card {x : α // f x = b} =
                    Nat.card {x : α // g x = b}) (x : α) :
    g (permOfFiberCards f g h x) = f x := by
  classical
  -- on the sigma representation the first component is untouched
  simp [permOfFiberCards, encodeFiber]
  exact ((Fintype.equivOfCardEq (by simpa [Nat.card_eq_fintype_card] using h (f x)) :
      {y : α // f y = f x} ≃ {y : α // g y = f x}) ⟨x, rfl⟩).property

-- Balanced finite clocks no longer mention any conjugating automorphism.
-- A label `l` is read on some finite window L.  Balance says that on the
-- joint window M=K∪L each colour has exactly as many words as the old
-- K-word.  The following elementary fibre permutation supplies the U in
-- `HasFiniteClocks`.
def HasBalancedFiniteClocks : Prop :=
  ∀ (K : Finset ℤ)
    (σ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
    (r : ℝ), 0 < r →
    ∃ (a : ℕ), ∃ ha : 0 < a,
    ∃ (L : Finset ℤ),
    ∃ (l : (∀ _j : (↥L), Bool) → (∀ _i : (↥K), Bool)),
      let M : Finset ℤ := K ∪ L
      let old : (∀ _j : (↥M), Bool) → (∀ _i : (↥K), Bool) :=
        fun z i => z ⟨(i:ℤ), Finset.mem_union_left _ i.property⟩
      let newc : (∀ _j : (↥M), Bool) → (∀ _i : (↥K), Bool) :=
        fun z => l (fun j => z ⟨(j:ℤ), Finset.mem_union_right _ j.property⟩)
      (∀ b : (∀ _i : (↥K), Bool),
         Nat.card {z : (∀ _j : (↥M), Bool) // old z = b} =
         Nat.card {z : (∀ _j : (↥M), Bool) // newc z = b}) ∧
      (let μ : Measure (ℤ → Bool) :=
          Measure.infinitePi (fun _ : ℤ => fairBool)
       ∀ H : Set (∀ _i : (↥K), Bool),
        μ (((intTranslateAutomorphism Bool fairBool (a:ℤ)).toEquiv ''
               (cylinder (α := fun _ : ℤ => Bool) L {z | l z ∈ H})) ∆
             (cylinder (α := fun _ : ℤ => Bool) L {z | l z ∈ σ '' H})) <
           ENNReal.ofReal r)

lemma finiteClocks_of_balanced (h : HasBalancedFiniteClocks) :
    HasFiniteClocks := by
  classical
  intro K τ r hr
  obtain ⟨a, ha, L, l, hbal, hstep⟩ := h K τ r hr
  let M : Finset ℤ := K ∪ L
  have hKM : K ⊆ M := Finset.subset_union_left
  have hLM : L ⊆ M := Finset.subset_union_right
  let old : (∀ _j : (↥M), Bool) → (∀ _i : (↥K), Bool) :=
       fun z i => z ⟨(i:ℤ), hKM i.property⟩
  let newc : (∀ _j : (↥M), Bool) → (∀ _i : (↥K), Bool) :=
       fun z => l (fun j => z ⟨(j:ℤ), hLM j.property⟩)
  have hbal' : ∀ b : (∀ _i : (↥K), Bool),
       Nat.card {z : (∀ _j : (↥M), Bool) // old z = b} =
       Nat.card {z : (∀ _j : (↥M), Bool) // newc z = b} := by
    exact hbal
  let π : (∀ _j : (↥M), Bool) ≃ (∀ _j : (↥M), Bool) :=
       permOfFiberCards old newc hbal'
  have hπ (z : (∀ _j : (↥M), Bool)) : newc (π z) = old z := by
    simpa [π] using (permOfFiberCards_spec old newc hbal' z)
  let U : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)) :=
       fairBlockAutomorphism M π
  let E : (∀ _i : (↥K), Bool) → Set (ℤ → Bool) :=
       fun b => cylinder (α := fun _ : ℤ => Bool) L {z | l z = b}
  refine ⟨a, ha, E, U, ?_, ?_⟩
  · intro H
    -- the finite permutation changes the old K-label into the window colour
    ext w
    constructor
    · rintro ⟨v, hv, hvw⟩
      have hvH : K.restrict v ∈ H := (mem_cylinder K H v).1 hv
      have hrest := fairBlockMeasurableEquiv_restrict M π v
      have hbase : newc (M.restrict w) = old (M.restrict v) := by
        change newc (M.restrict w) = old (M.restrict v)
        change fairBlockMeasurableEquiv M π v = w at hvw
        rw [← hvw]
        rw [hrest]
        exact hπ _
      have h1 : l (fun j : (↥L) => w (j:ℤ)) = (fun i : (↥K) => v (i:ℤ)) := by
        simpa [newc, old] using hbase
      have hfunL : (fun j : (↥L) => w (j:ℤ)) = L.restrict w := by rfl
      have hfunK : (fun i : (↥K) => v (i:ℤ)) = K.restrict v := by rfl
      have hL : l (L.restrict w) = K.restrict v := by rw [← hfunL, ← hfunK]; exact h1
      apply Set.mem_iUnion.2
      refine ⟨⟨K.restrict v, hvH⟩, ?_⟩
      change L.restrict w ∈ {z | l z = K.restrict v}
      exact hL
    · intro hw
      rcases Set.mem_iUnion.1 hw with ⟨b, hb⟩
      change L.restrict w ∈ {z | l z = b.1} at hb
      let v : (ℤ → Bool) := (fairBlockMeasurableEquiv M π).symm w
      have hvw : fairBlockMeasurableEquiv M π v = w :=
        (fairBlockMeasurableEquiv M π).apply_symm_apply w
      have hrest := fairBlockMeasurableEquiv_restrict M π v
      have hbase : newc (M.restrict w) = old (M.restrict v) := by
        change newc (M.restrict w) = old (M.restrict v)
        change fairBlockMeasurableEquiv M π v = w at hvw
        rw [← hvw]
        rw [hrest]
        exact hπ _
      have h1 : l (fun j : (↥L) => w (j:ℤ)) = (fun i : (↥K) => v (i:ℤ)) := by
        simpa [newc, old] using hbase
      have hfunL : (fun j : (↥L) => w (j:ℤ)) = L.restrict w := by rfl
      have hfunK : (fun i : (↥K) => v (i:ℤ)) = K.restrict v := by rfl
      have hsimp : l (L.restrict w) = K.restrict v := by rw [← hfunL, ← hfunK]; exact h1
      have hold : K.restrict v = b.1 := hsimp.symm.trans hb
      refine ⟨v, (mem_cylinder K H v).2 ?_, hvw⟩
      simpa [hold] using b.2
  · intro H
    -- a union of the singleton fibres is just one coloured cylinder
    have hun (S : Set (∀ _i : (↥K), Bool)) :
        (⋃ b : {z : (∀ _i : (↥K), Bool) // z ∈ S}, E b.1) =
          cylinder (α := fun _ : ℤ => Bool) L {z | l z ∈ S} := by
      ext w
      constructor
      · intro hw
        rcases Set.mem_iUnion.1 hw with ⟨b, hb⟩
        change L.restrict w ∈ {z | l z = b.1} at hb
        exact (mem_cylinder L {z | l z ∈ S} w).2 (by
          change l (L.restrict w) ∈ S
          rw [hb]
          exact b.2)
      · intro hw
        have hh : l (L.restrict w) ∈ S := by
          have hmem := (mem_cylinder L {z | l z ∈ S} w).1 hw
          exact hmem
        apply Set.mem_iUnion.2
        refine ⟨⟨l (L.restrict w), hh⟩, ?_⟩
        change L.restrict w ∈ {z | l z = l (L.restrict w)}
        rfl
    rw [hun H, hun (τ '' H)]
    simpa using (hstep H)

-- Images of a single finite window by a strided translation are again
-- finite windows.  This is a useful way to finish a clock construction: the
-- clock inequality is just a comparison of two finite sets of words.
lemma intTranslate_image_cylinder_bool
    (I : Finset ℤ) (S : Set (∀ _i : (↥I), Bool)) (a : ℤ) :
    let g : ℤ → ℤ := fun i => i - a
    let I' : Finset ℤ := I.image g
    let pull : (∀ _j : (↥I'), Bool) → (∀ _i : (↥I), Bool) :=
       fun z i => z ⟨g (i:ℤ),
         (by dsimp [I']; exact Finset.mem_image.2 ⟨(i:ℤ), i.property, rfl⟩)⟩
    (intTranslateAutomorphism Bool fairBool a).toEquiv ''
       (cylinder (α := fun _ : ℤ => Bool) I S) =
      cylinder (α := fun _ : ℤ => Bool) I' (pull ⁻¹' S) := by
  classical
  dsimp
  let g : ℤ → ℤ := fun i => i - a
  have hg : Function.Injective g := by
    intro x y h
    dsimp [g] at h
    linarith
  let I' : Finset ℤ := I.image g
  let pull : (∀ _j : (↥I'), Bool) → (∀ _i : (↥I), Bool) :=
       fun z i => z ⟨g (i:ℤ),
         (by dsimp [I']; exact Finset.mem_image.2 ⟨(i:ℤ), i.property, rfl⟩)⟩
  change (intTranslateAutomorphism Bool fairBool a).toEquiv ''
       (cylinder (α := fun _ : ℤ => Bool) I S) =
      cylinder (α := fun _ : ℤ => Bool) I' (pull ⁻¹' S)
  ext w
  constructor
  · rintro ⟨v, hv, hvw⟩
    have hvr : I.restrict v ∈ S := (mem_cylinder I S v).1 hv
    apply (mem_cylinder I' (pull ⁻¹' S) w).2
    change pull (I'.restrict w) ∈ S
    have heq : pull (I'.restrict w) = I.restrict v := by
      funext i
      change w (g (i:ℤ)) = v (i:ℤ)
      rw [← hvw]
      change intTranslateMeasurableEquiv Bool a v (g (i:ℤ)) = _
      rw [intTranslateMeasurableEquiv_apply]
      dsimp [g]
      simp
    rw [heq]
    exact hvr
  · intro hw
    have htmp := (mem_cylinder I' (pull ⁻¹' S) w).1 hw
    change pull (I'.restrict w) ∈ S at htmp
    have hwr : pull (I'.restrict w) ∈ S := htmp
    -- translate backwards; no extra coordinates matter
    let v : (ℤ → Bool) :=
       (intTranslateMeasurableEquiv Bool a).symm w
    have hvw : intTranslateMeasurableEquiv Bool a v = w :=
       (intTranslateMeasurableEquiv Bool a).apply_symm_apply w
    have heq : I.restrict v = pull (I'.restrict w) := by
      funext i
      have ht : (intTranslateMeasurableEquiv Bool a v) (g (i:ℤ)) =
           v (i:ℤ) := by
        rw [intTranslateMeasurableEquiv_apply]
        dsimp [g]
        simp
      change v (i:ℤ) = w (g (i:ℤ))
      rw [← hvw]
      exact ht.symm
    refine ⟨v, (mem_cylinder I S v).2 ?_, ?_⟩
    · rw [heq]
      exact hwr
    · exact hvw

lemma cylinder_symmDiff_same_bool (I : Finset ℤ)
    (S T : Set (∀ _i : (↥I), Bool)) :
    (cylinder (α := fun _ : ℤ => Bool) I S) ∆
        (cylinder (α := fun _ : ℤ => Bool) I T) =
      cylinder (α := fun _ : ℤ => Bool) I (S ∆ T) := by
  classical
  ext w
  simp only [Set.mem_symmDiff, mem_cylinder]

lemma fairBernoulli_same_window_symmDiff_card
    (I : Finset ℤ) (S T : Set (∀ _i : (↥I), Bool)) :
    (Measure.infinitePi (fun _ : ℤ => fairBool))
       ((cylinder (α := fun _ : ℤ => Bool) I S) ∆
        (cylinder (α := fun _ : ℤ => Bool) I T)) =
       ((S ∆ T).toFinite.toFinset.card : ENNReal) *
          ((2 : ENNReal)⁻¹) ^ I.card := by
  rw [cylinder_symmDiff_same_bool]
  exact fairBernoulli_cylinder_mass_card I _ (by
    exact (S ∆ T).toFinite.measurableSet)

lemma fair_clock_of_joint_card
    (L : Finset ℤ) (a : ℕ)
    (S T : Set (∀ _i : (↥L), Bool))
    (M : Finset ℤ)
    (D E : Set (∀ _j : (↥M), Bool))
    (hD :
      let g : ℤ → ℤ := fun i => i - (a:ℤ)
      let L' : Finset ℤ := L.image g
      let pull : (∀ _j : (↥L'), Bool) → (∀ _i : (↥L), Bool) :=
        fun z i => z ⟨g (i:ℤ),
          (by dsimp [L']; exact Finset.mem_image.2 ⟨(i:ℤ), i.property, rfl⟩)⟩
      cylinder (α := fun _ : ℤ => Bool) M D = cylinder L' (pull ⁻¹' S))
    (hE : cylinder (α := fun _ : ℤ => Bool) M E = cylinder L T)
    (hsmall : ((D ∆ E).toFinite.toFinset.card : ENNReal) *
          ((2 : ENNReal)⁻¹) ^ M.card < ENNReal.ofReal (1:ℝ)) :
    (Measure.infinitePi (fun _ : ℤ => fairBool))
       (((intTranslateAutomorphism Bool fairBool (a:ℤ)).toEquiv ''
           (cylinder (α := fun _ : ℤ => Bool) L S)) ∆
         (cylinder (α := fun _ : ℤ => Bool) L T)) < (1:ENNReal) := by
  classical
  -- This unit-radius version suffices to expose that there is no
  -- measurability/coercion issue in a clock: the exact rational bound is a
  -- count of bad joint words.  Scaling the last inequality gives any radius.
  have him := intTranslate_image_cylinder_bool L S (a:ℤ)
  dsimp at him hD
  rw [him]
  rw [← hD, ← hE]
  rw [fairBernoulli_same_window_symmDiff_card]
  have h1 : ENNReal.ofReal (1:ℝ) = (1:ENNReal) := by simp
  simpa [h1] using hsmall

-- the general-radius formulation used by marker counts
lemma fair_clock_of_joint_card'
    (L : Finset ℤ) (a : ℕ)
    (S T : Set (∀ _i : (↥L), Bool))
    (M : Finset ℤ)
    (D E : Set (∀ _j : (↥M), Bool))
    (hD :
      let g : ℤ → ℤ := fun i => i - (a:ℤ)
      let L' : Finset ℤ := L.image g
      let pull : (∀ _j : (↥L'), Bool) → (∀ _i : (↥L), Bool) :=
        fun z i => z ⟨g (i:ℤ),
          (by dsimp [L']; exact Finset.mem_image.2 ⟨(i:ℤ), i.property, rfl⟩)⟩
      cylinder (α := fun _ : ℤ => Bool) M D = cylinder L' (pull ⁻¹' S))
    (hE : cylinder (α := fun _ : ℤ => Bool) M E = cylinder L T)
    (r : ℝ)
    (hsmall : ((D ∆ E).toFinite.toFinset.card : ENNReal) *
          ((2 : ENNReal)⁻¹) ^ M.card < ENNReal.ofReal r) :
    (Measure.infinitePi (fun _ : ℤ => fairBool))
       (((intTranslateAutomorphism Bool fairBool (a:ℤ)).toEquiv ''
           (cylinder (α := fun _ : ℤ => Bool) L S)) ∆
         (cylinder (α := fun _ : ℤ => Bool) L T)) < ENNReal.ofReal r := by
  classical
  have him := intTranslate_image_cylinder_bool L S (a:ℤ)
  dsimp at him hD
  rw [him]
  rw [← hD, ← hE]
  rw [fairBernoulli_same_window_symmDiff_card]
  exact hsmall

-- A completely finite version of the missing clock.  Joint extensions may
-- be chosen separately for each subset of colours, so setting `M` to the
-- union of the translated and untranslated windows is always allowed.  All
-- fields after the balance equation are just cardinalities of finite Boolean
-- cubes.
def HasWordClocks : Prop :=
  ∀ (K : Finset ℤ)
    (τ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
    (r : ℝ), 0 < r →
    ∃ (a : ℕ), ∃ ha : 0 < a,
    ∃ (L : Finset ℤ),
    ∃ (l : (∀ _j : (↥L), Bool) → (∀ _i : (↥K), Bool)),
      let W : Finset ℤ := K ∪ L
      let old : (∀ _j : (↥W), Bool) → (∀ _i : (↥K), Bool) :=
        fun z i => z ⟨(i:ℤ), Finset.mem_union_left _ i.property⟩
      let col : (∀ _j : (↥W), Bool) → (∀ _i : (↥K), Bool) :=
        fun z => l (fun j => z ⟨(j:ℤ), Finset.mem_union_right _ j.property⟩)
      (∀ b, Nat.card {z : (∀ _j : (↥W), Bool) // old z = b} =
             Nat.card {z : (∀ _j : (↥W), Bool) // col z = b}) ∧
      ∀ H : Set (∀ _i : (↥K), Bool),
       ∃ (M : Finset ℤ)
         (D E : Set (∀ _j : (↥M), Bool)),
       (let g : ℤ → ℤ := fun i => i - (a:ℤ)
        let L' : Finset ℤ := L.image g
        let pull : (∀ _j : (↥L'), Bool) → (∀ _i : (↥L), Bool) :=
          fun z i => z ⟨g (i:ℤ),
             (by dsimp [L'];
                 exact Finset.mem_image.2 ⟨(i:ℤ), i.property, rfl⟩)⟩
        cylinder (α := fun _ : ℤ => Bool) M D =
           cylinder L' (pull ⁻¹' ({z | l z ∈ H} : Set _))) ∧
       cylinder (α := fun _ : ℤ => Bool) M E =
           cylinder L ({z | l z ∈ τ '' H} : Set _) ∧
       ((D ∆ E).toFinite.toFinset.card : ENNReal) *
          ((2 : ENNReal)⁻¹) ^ M.card < ENNReal.ofReal r



-- A stricter, entirely single-window way to ask for the finite clocks.  Instead of
-- producing joint extensions separately for every subset of colours we read two
-- neighbouring windows at once.  The set of bad words below is independent of the
-- tested subset.  This removes a surprisingly distracting existential (`M,D,E`)
-- from the marker construction: it really is only a problem about colouring the
-- vertices of one finite Boolean cube so that almost all of its overlap edges
-- advance the colour by `τ`.
def prevWindow (L : Finset ℤ) (a : ℕ) : Finset ℤ :=
  L.image (fun i : ℤ => i - (a:ℤ))

def doubleWindow (L : Finset ℤ) (a : ℕ) : Finset ℤ :=
  prevWindow L a ∪ L

noncomputable def previousWord (L : Finset ℤ) (a : ℕ)
    (z : (∀ _j : (↥(doubleWindow L a)), Bool)) :
      (∀ _i : (↥L), Bool) := by
  classical
  intro i
  exact z ⟨(i:ℤ) - (a:ℤ),
    Finset.mem_union_left _
      (Finset.mem_image.2 ⟨(i:ℤ), i.property, rfl⟩)⟩

noncomputable def presentWord (L : Finset ℤ) (a : ℕ)
    (z : (∀ _j : (↥(doubleWindow L a)), Bool)) :
      (∀ _i : (↥L), Bool) := by
  classical
  intro i
  exact z ⟨(i:ℤ), Finset.mem_union_right _ i.property⟩

@[simp] lemma previousWord_restrict (L : Finset ℤ) (a : ℕ)
    (w : ℤ → Bool) :
    previousWord L a ((doubleWindow L a).restrict w) =
      (fun i : (↥L) => w ((i:ℤ) - (a:ℤ))) := by
  classical
  funext i
  rfl

@[simp] lemma presentWord_restrict (L : Finset ℤ) (a : ℕ)
    (w : ℤ → Bool) :
    presentWord L a ((doubleWindow L a).restrict w) = L.restrict w := by
  classical
  funext i
  rfl

-- A line model for the marker row.  Taking packets of `t` consecutive
-- integer coordinates avoids any arbitrary enumeration of the overlap.
-- In this concrete model the present and previous windows are the tail
-- and the head of the decoded row.  This was the awkward set-theoretic
-- part of using the finite marker counts; all statements are identities
-- of ordinary functions, not merely equicardinalities.
lemma doubleWindow_natWindow (t N : ℕ) :
    doubleWindow (HalmosSupport.natWindow (N*t)) t =
       HalmosSupport.twoNatWindow t N := by
  rfl

lemma card_doubleWindow_natWindow (t N : ℕ) (ht : 0 < t) (hN : 0 < N) :
    (doubleWindow (HalmosSupport.natWindow (N*t)) t).card = (N+1)*t := by
  classical
  rw [doubleWindow_natWindow]
  simpa using (Fintype.card_congr (HalmosSupport.enumTwoWindow t N ht hN))

-- The raw bit version is the useful computation rule; packetizing or changing
-- the alphabet is then just applying an equivalence to each row.
lemma lineWords_present
    (t N : ℕ) (ht : 0 < t) (hN : 0 < N)
    (z : (↥(doubleWindow (HalmosSupport.natWindow (N*t)) t) → Bool)) :
    HalmosSupport.lineWords N t
       (presentWord (HalmosSupport.natWindow (N*t)) t z)
       = (fun i : Fin N =>
           HalmosSupport.lineRows N t ht hN
             ((by simpa [doubleWindow_natWindow] using z)) i.succ) := by
  classical
  funext i j
  -- both sides read coordinate `j + t*i`
  rw [HalmosSupport.lineWords_apply, HalmosSupport.lineRows_apply]
  change z _ = z _
  congr 2
  dsimp
  push_cast
  ring_nf

lemma lineWords_previous
    (t N : ℕ) (ht : 0 < t) (hN : 0 < N)
    (z : (↥(doubleWindow (HalmosSupport.natWindow (N*t)) t) → Bool)) :
    HalmosSupport.lineWords N t
       (previousWord (HalmosSupport.natWindow (N*t)) t z)
       = (fun i : Fin N =>
           HalmosSupport.lineRows N t ht hN
             ((by simpa [doubleWindow_natWindow] using z)) i.castSucc) := by
  classical
  funext i j
  rw [HalmosSupport.lineWords_apply, HalmosSupport.lineRows_apply]
  rfl


lemma packetWindow_present {δ : Type*} [Fintype δ]
    (b N : ℕ) (hb : 0 < b) (hN : 0 < N)
    (z : (↥(doubleWindow
          (HalmosSupport.natWindow (N*(Fintype.card δ + b)))
            (Fintype.card δ + b)) → Bool)) :
    HalmosSupport.packetWindow (δ:=δ) b N
       (presentWord (HalmosSupport.natWindow (N*(Fintype.card δ+b)))
          (Fintype.card δ+b) z)
      = (fun i : Fin N =>
          HalmosSupport.packetRows (δ:=δ) b N
            (by omega) hN
            ((by simpa [doubleWindow_natWindow] using z)) i.succ) := by
  classical
  -- packet decoding is functorial, so this is the raw bit identity above.
  change (fun i => HalmosSupport.packet (δ:=δ) b
       (HalmosSupport.lineWords N (Fintype.card δ+b)
          (presentWord (HalmosSupport.natWindow (N*(Fintype.card δ+b)))
             (Fintype.card δ+b) z) i)) = _
  rw [lineWords_present (Fintype.card δ+b) N (by omega) hN]
  rfl

lemma packetWindow_previous {δ : Type*} [Fintype δ]
    (b N : ℕ) (hb : 0 < b) (hN : 0 < N)
    (z : (↥(doubleWindow
          (HalmosSupport.natWindow (N*(Fintype.card δ + b)))
            (Fintype.card δ + b)) → Bool)) :
    HalmosSupport.packetWindow (δ:=δ) b N
       (previousWord (HalmosSupport.natWindow (N*(Fintype.card δ+b)))
          (Fintype.card δ+b) z)
      = (fun i : Fin N =>
          HalmosSupport.packetRows (δ:=δ) b N
            (by omega) hN
            ((by simpa [doubleWindow_natWindow] using z)) i.castSucc) := by
  classical
  change (fun i => HalmosSupport.packet (δ:=δ) b
       (HalmosSupport.lineWords N (Fintype.card δ+b)
          (previousWord (HalmosSupport.natWindow (N*(Fintype.card δ+b)))
             (Fintype.card δ+b) z) i)) = _
  rw [lineWords_previous (Fintype.card δ+b) N (by omega) hN]
  rfl

lemma marker_line_bad_card {δ : Type*} [Fintype δ] [DecidableEq δ]
    (b m : ℕ) (hb : 0 < b) (hm : 0 < m)
    (τ : (δ → Bool) ≃ (δ → Bool)) (star : Fin b → Bool) :
    let t : ℕ := Fintype.card δ + b
    let N : ℕ := m+1
    let L : Finset ℤ := HalmosSupport.natWindow (N*t)
    let l : ((↥L) → Bool) → (δ → Bool) := fun u =>
       HalmosSupport.markerRead τ N (by omega) star
         (HalmosSupport.packetWindow (δ:=δ) b N u)
    (Finset.univ.filter (fun z : (↥(doubleWindow L t)) → Bool =>
        l (presentWord L t z) ≠ τ (l (previousWord L t z)))).card =
     (Finset.univ.filter
       (HalmosSupport.markerBadRow τ N (by omega) star)).card := by
  classical
  dsimp
  let t := Fintype.card δ+b
  let NN := m+1
  have ht : 0 < t := by dsimp [t]; omega
  have hNN : 0 < NN := by dsimp [NN]; omega
  -- row decoder is a bijection: no bits have been forgotten.
  let row : ((↥(doubleWindow (HalmosSupport.natWindow (NN*t)) t)) → Bool) ≃
           (Fin (NN+1) → ((δ → Bool) × (Fin b → Bool))) := by
     simpa [doubleWindow_natWindow] using
       (HalmosSupport.packetRows (δ:=δ) b NN ht hNN)
  let p (z : (↥(doubleWindow (HalmosSupport.natWindow (NN*t)) t)) → Bool) : Prop :=
       HalmosSupport.markerRead τ NN (by omega) star
           (HalmosSupport.packetWindow (δ:=δ) b NN
             (presentWord (HalmosSupport.natWindow (NN*t)) t z)) ≠
         τ (HalmosSupport.markerRead τ NN (by omega) star
           (HalmosSupport.packetWindow (δ:=δ) b NN
             (previousWord (HalmosSupport.natWindow (NN*t)) t z)))
  let q (v : Fin (NN+1) → ((δ → Bool) × (Fin b → Bool))) : Prop :=
        HalmosSupport.markerBadRow τ NN (by omega) star v
  have hpq (z : (↥(doubleWindow (HalmosSupport.natWindow (NN*t)) t)) → Bool) :
       p z ↔ q (row z) := by
    -- decoded present and previous windows are tail/head of the row
    change
      HalmosSupport.markerRead τ NN _ star
        (HalmosSupport.packetWindow (δ:=δ) b NN
          (presentWord _ t z)) ≠
          τ (HalmosSupport.markerRead τ NN _ star
            (HalmosSupport.packetWindow (δ:=δ) b NN
              (previousWord _ t z))) ↔ _
    rw [packetWindow_present (δ:=δ) b NN hb hNN,
        packetWindow_previous (δ:=δ) b NN hb hNN]
    rfl
  change (Finset.univ.filter p).card = (Finset.univ.filter q).card
  let left := Finset.univ.filter p
  let right := Finset.univ.filter q
  change left.card = right.card
  classical
  -- restrict the row equivalence to the decidable subsets
  let er : (↥left) ≃ (↥right) :=
    { toFun := fun x => ⟨row x.1, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (hpq x.1).mp (Finset.mem_filter.mp x.2).2⟩⟩
      invFun := fun x => ⟨row.symm x.1, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (hpq (row.symm x.1)).mpr (by
              simpa [q] using (Finset.mem_filter.mp x.2).2)⟩⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp }
  simpa using (Fintype.card_congr er)

-- The marker bound on the abstract `(m+2)` row therefore applies literally
-- to consecutive integer coordinates.  This is the finite-line bridge; no
-- asymptotic estimate or casting of measures is involved.
-- All data in this hypothesis are finite.  In particular the last `filter` is a
-- finset of words, not an asymptotic or a statement modulo null sets.
def HasEdgeLabels : Prop :=
  ∀ (K : Finset ℤ)
    (τ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
    (r : ℝ), 0 < r →
    ∃ (a : ℕ), ∃ ha : 0 < a,
    ∃ (L : Finset ℤ),
    ∃ (l : (∀ _j : (↥L), Bool) → (∀ _i : (↥K), Bool)),
      let W : Finset ℤ := K ∪ L
      let old : (∀ _j : (↥W), Bool) → (∀ _i : (↥K), Bool) :=
        fun z i => z ⟨(i:ℤ), Finset.mem_union_left _ i.property⟩
      let col : (∀ _j : (↥W), Bool) → (∀ _i : (↥K), Bool) :=
        fun z => l (fun j => z ⟨(j:ℤ), Finset.mem_union_right _ j.property⟩)
      (∀ b, Nat.card {z : (∀ _j : (↥W), Bool) // old z = b} =
             Nat.card {z : (∀ _j : (↥W), Bool) // col z = b}) ∧
      ((Finset.univ.filter (fun z :
              (∀ _j : (↥(doubleWindow L a)), Bool) =>
              l (presentWord L a z) ≠ τ (l (previousWord L a z)))).card : ENNReal) *
          ((2 : ENNReal)⁻¹) ^ (doubleWindow L a).card < ENNReal.ofReal r



-- The data for one prescribed block.  Pulling this out as a predicate makes a
-- negated clock precise: a counterexample consists of a *finite*, nonempty K and
-- a radius.  There are no measurable spaces in it.
def EdgeData
    (K : Finset ℤ)
    (τ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
    (r : ℝ) : Prop :=
    ∃ (a : ℕ), ∃ ha : 0 < a,
    ∃ (L : Finset ℤ),
    ∃ (l : (∀ _j : (↥L), Bool) →
              (∀ _i : (↥K), Bool)),
      let W : Finset ℤ := K ∪ L
      let old : (∀ _j : (↥W), Bool) →
            (∀ _i : (↥K), Bool) :=
        fun z i => z ⟨(i:ℤ), Finset.mem_union_left _ i.property⟩
      let col : (∀ _j : (↥W), Bool) →
            (∀ _i : (↥K), Bool) :=
        fun z => l (fun j => z ⟨(j:ℤ), Finset.mem_union_right _ j.property⟩)
      (∀ b, Nat.card {z : (∀ _j : (↥W), Bool) // old z = b} =
             Nat.card {z : (∀ _j : (↥W), Bool) // col z = b}) ∧
      ((Finset.univ.filter (fun z :
              (∀ _j : (↥(doubleWindow L a)), Bool) =>
              l (presentWord L a z) ≠ τ (l (previousWord L a z)))).card
            : ENNReal) *
          ((2 : ENNReal)⁻¹) ^ (doubleWindow L a).card < ENNReal.ofReal r

/-- In the finite edge problem there is never any balance bookkeeping to
  do in the large union `K ∪ L`.  It suffices that the small reading `l` is
  exactly uniform on its own window.  This avoids formulas for `2^|K|` and
  for intersections with the auxiliary marker block. -/
lemma edgeData_of_const_fiber
    (K : Finset ℤ)
    (τ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
    (r : ℝ) (a : ℕ) (ha : 0 < a)
    (L : Finset ℤ)
    (l : (∀ _j : (↥L), Bool) → (∀ _i : (↥K), Bool))
    (hl : ∀ b c : (∀ _i : (↥K), Bool),
       Nat.card {z : (∀ _j : (↥L), Bool) // l z = b} =
       Nat.card {z : (∀ _j : (↥L), Bool) // l z = c})
    (hedge : ((Finset.univ.filter (fun z :
             (∀ _j : (↥(doubleWindow L a)), Bool) =>
               l (presentWord L a z) ≠ τ (l (previousWord L a z)))).card
             : ENNReal) *
          ((2 : ENNReal)⁻¹) ^ (doubleWindow L a).card < ENNReal.ofReal r) :
    EdgeData K τ r := by
  classical
  refine ⟨a, ha, L, l, ?_⟩
  dsimp
  constructor
  · simpa using (HalmosSupport.balance_union_of_const_fiber
        (γ := Bool) K L l hl)
  · exact hedge

/-- A useful prepackaged marker row.  Choosing a site with tags gives the
exact balance field of a clock for free.  The sole remaining issue is the
single exceptional-edge count; this formulation isolates it from the union
window cardinalities. -/
lemma edgeData_of_marker
    (K : Finset ℤ)
    (τ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
    (r : ℝ) (a : ℕ) (ha : 0 < a)
    (L : Finset ℤ) (ι β : Type*) [Fintype ι] [DecidableEq ι]
       [Fintype β]
    (e : (∀ _j : (↥L), Bool) ≃
          (ι → (((∀ _i : (↥K), Bool)) × β)))
    (starPick : (ι → β) → ι) (phase : ι → ℕ)
    (hedge :
      ((Finset.univ.filter (fun z :
             (∀ _j : (↥(doubleWindow L a)), Bool) =>
          (HalmosSupport.clockColor τ starPick phase (e (presentWord L a z))) ≠
            τ (HalmosSupport.clockColor τ starPick phase (e (previousWord L a z))))).card
           : ENNReal) *
          ((2 : ENNReal)⁻¹) ^ (doubleWindow L a).card < ENNReal.ofReal r) :
    EdgeData K τ r := by
  classical
  let l : (∀ _j : (↥L), Bool) → (∀ _i : (↥K), Bool) :=
      fun z => HalmosSupport.clockColor τ starPick phase (e z)
  apply edgeData_of_const_fiber K τ r a ha L l
  · exact HalmosSupport.card_clockColor_equiv e τ starPick phase
  · simpa [l] using hedge

lemma hasEdgeLabels_iff : HasEdgeLabels ↔
    ∀ (K : Finset ℤ)
      (τ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
      (r : ℝ), 0 < r → EdgeData K τ r := by
  rfl

-- There is no colour-clock obstruction on an empty block.  This harmless edge
-- case is useful when using the edge formulation: every word has the unique
-- empty colour, so it advances by any permutation automatically.
lemma edge_labels_empty
    (τ : (∀ _i : (↥(∅ : Finset ℤ)), Bool) ≃
         (∀ _i : (↥(∅ : Finset ℤ)), Bool))
    (r : ℝ) (hr : 0 < r) :
    ∃ (a : ℕ), ∃ ha : 0 < a,
    ∃ (L : Finset ℤ),
    ∃ (l : (∀ _j : (↥L), Bool) →
              (∀ _i : (↥(∅ : Finset ℤ)), Bool)),
      let W : Finset ℤ := (∅ : Finset ℤ) ∪ L
      let old : (∀ _j : (↥W), Bool) →
            (∀ _i : (↥(∅ : Finset ℤ)), Bool) :=
        fun z i => z ⟨(i:ℤ), Finset.mem_union_left _ i.property⟩
      let col : (∀ _j : (↥W), Bool) →
            (∀ _i : (↥(∅ : Finset ℤ)), Bool) :=
        fun z => l (fun j => z ⟨(j:ℤ), Finset.mem_union_right _ j.property⟩)
      (∀ b, Nat.card {z : (∀ _j : (↥W), Bool) // old z = b} =
             Nat.card {z : (∀ _j : (↥W), Bool) // col z = b}) ∧
      ((Finset.univ.filter (fun z :
              (∀ _j : (↥(doubleWindow L a)), Bool) =>
              l (presentWord L a z) ≠ τ (l (previousWord L a z)))).card
            : ENNReal) *
          ((2 : ENNReal)⁻¹) ^ (doubleWindow L a).card < ENNReal.ofReal r := by
  classical
  have emptyidx (i : (↥(∅ : Finset ℤ))) : False := by
    have hn : ∀ x : ℤ, ¬ x ∈ (∅ : Finset ℤ) := by
      intro x; simp
    exact hn (i:ℤ) i.property
  let emptyWord : (∀ _i : (↥(∅ : Finset ℤ)), Bool) := fun i =>
    False.elim (emptyidx i)
  refine ⟨1, by norm_num, (∅ : Finset ℤ),
    (fun _ => emptyWord), ?_⟩
  dsimp
  constructor
  · intro b
    have hb : b = emptyWord := by
      funext i
      exact False.elim (emptyidx i)
    subst b
    -- the two fibre predicates are extensionally the same: all functions
    -- into the empty coordinate tuple equal `emptyWord`.
    have hfun (z : (∀ _j : (↥((∅ : Finset ℤ) ∪ (∅ : Finset ℤ))), Bool)) :
        (fun i : (↥(∅ : Finset ℤ)) =>
          z ⟨(i:ℤ), Finset.mem_union_left _ i.property⟩) =
          emptyWord := by
        funext i
        exact False.elim (emptyidx i)
    -- avoiding any arithmetic of `Nat.card`, identify the two predicates
    -- as sets and use the induced equivalence of subtypes.
    let s : Set (∀ _j : (↥((∅ : Finset ℤ) ∪ (∅ : Finset ℤ))), Bool) :=
      {z | (fun i : (↥(∅ : Finset ℤ)) =>
            z ⟨(i:ℤ), Finset.mem_union_left _ i.property⟩) = emptyWord}
    let t : Set (∀ _j : (↥((∅ : Finset ℤ) ∪ (∅ : Finset ℤ))), Bool) :=
      {z | (fun (_u : (∀ _j : (↥(∅ : Finset ℤ)), Bool)) => emptyWord)
              (fun j : (↥(∅ : Finset ℤ)) =>
                z ⟨(j:ℤ), Finset.mem_union_right _ j.property⟩) = emptyWord}
    change Nat.card (↥s) = Nat.card (↥t)
    have hst : s = t := by
      ext z
      change ((fun i : (↥(∅ : Finset ℤ)) =>
        z ⟨(i:ℤ), Finset.mem_union_left _ i.property⟩) = emptyWord) ↔
          ((fun (_u : (∀ _j : (↥(∅ : Finset ℤ)), Bool)) => emptyWord)
            (fun j : (↥(∅ : Finset ℤ)) =>
              z ⟨(j:ℤ), Finset.mem_union_right _ j.property⟩) = emptyWord)
      constructor
      · intro hz
        rfl
      · intro hz
        exact hfun z
    exact Nat.card_congr (Equiv.setCongr hst)
  ·
    have hnone (z : (∀ _j : (↥(doubleWindow (∅ : Finset ℤ) 1)), Bool)) :
        (fun _ => emptyWord) (presentWord (∅ : Finset ℤ) 1 z) =
          τ ((fun _ => emptyWord)
            (previousWord (∅ : Finset ℤ) 1 z)) := by
      -- every map into the empty tuple is the same
      funext i
      exact False.elim (emptyidx i)
    have hempty :
        (Finset.univ.filter (fun z :
          (∀ _j : (↥(doubleWindow (∅ : Finset ℤ) 1)), Bool) =>
          (fun _ => emptyWord) (presentWord (∅ : Finset ℤ) 1 z) ≠
             τ ((fun _ => emptyWord)
              (previousWord (∅ : Finset ℤ) 1 z)))) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx hne
      exact hne (hnone x)
    rw [hempty]
    simp [hr, ENNReal.ofReal_pos.2 hr]


lemma edgeData_empty
    (τ : (∀ _i : (↥(∅ : Finset ℤ)), Bool) ≃
         (∀ _i : (↥(∅ : Finset ℤ)), Bool))
    (r : ℝ) (hr : 0 < r) : EdgeData (∅ : Finset ℤ) τ r := by
  exact edge_labels_empty τ r hr

-- Therefore failure of the edge statement has a witness with a genuinely
-- nonempty alphabet block.  This is often a cleaner final obstruction than
-- `¬ HasWordClocks`: neither weak mixing nor the real law occurs in it.

-- For radii above one nothing is at stake.  Taking the old K-word itself as
-- colour is balanced exactly, and every set of joint words costs at most the
-- full cube.  Thus a genuine clock obstruction must also have radius at most
-- one.
lemma edgeData_of_one_lt
    (K : Finset ℤ)
    (τ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
    (r : ℝ) (hr : (1:ℝ) < r) : EdgeData K τ r := by
  classical
  refine ⟨1, by norm_num, K,
    (fun z => z), ?_⟩
  dsimp
  constructor
  · intro b
    -- in `K ∪ K` the old and current restrictions coincide
    have hpred (z : (∀ _j : (↥(K ∪ K)), Bool)) :
       (fun i : (↥K) =>
          z ⟨(i:ℤ), Finset.mem_union_left _ i.property⟩) =
       (fun i : (↥K) =>
          z ⟨(i:ℤ), Finset.mem_union_right _ i.property⟩) := by
         funext i
         rfl
    -- equal predicates give equicardinal subtypes
    let s : Set (∀ _j : (↥(K ∪ K)), Bool) :=
      {z | (fun i : (↥K) =>
          z ⟨(i:ℤ), Finset.mem_union_left _ i.property⟩) = b}
    let t : Set (∀ _j : (↥(K ∪ K)), Bool) :=
      {z | (fun i : (↥K) =>
          z ⟨(i:ℤ), Finset.mem_union_right _ i.property⟩) = b}
    change Nat.card (↥s) = Nat.card (↥t)
    have hst : s = t := by
      ext z
      change ((fun i : (↥K) =>
          z ⟨(i:ℤ), Finset.mem_union_left _ i.property⟩) = b) ↔
        ((fun i : (↥K) =>
          z ⟨(i:ℤ), Finset.mem_union_right _ i.property⟩) = b)
      rw [hpred z]
    exact Nat.card_congr (Equiv.setCongr hst)
  ·
    let M : Finset ℤ := doubleWindow K 1
    let bad : Finset (∀ _j : (↥M), Bool) :=
      Finset.univ.filter (fun z : (∀ _j : (↥(doubleWindow K 1)), Bool) =>
          (fun z => z) (presentWord K 1 z) ≠
            τ ((fun z => z) (previousWord K 1 z)))
    have hn : bad.card ≤ 2 ^ M.card := by
      have hs : bad ⊆ (Finset.univ : Finset (∀ _j : (↥M), Bool)) :=
        fun x hx => Finset.mem_univ _
      have hc := Finset.card_le_card hs
      simpa [Fintype.card_fun, Fintype.card_coe] using hc
    have hn' : (bad.card : ENNReal) ≤ (2 : ENNReal) ^ M.card := by
      exact_mod_cast hn
    have hmul : (bad.card : ENNReal) *
        ((2 : ENNReal)⁻¹)^M.card ≤ (1 : ENNReal) := by
      have hle := mul_le_mul_right' hn' (((2 : ENNReal)⁻¹)^M.card)
      -- the mass of the whole Boolean cube is one
      calc
        (bad.card : ENNReal) * ((2 : ENNReal)⁻¹)^M.card ≤
            (2 : ENNReal)^M.card * ((2 : ENNReal)⁻¹)^M.card := hle
        _ = ((2 : ENNReal)^M.card) * (((2 : ENNReal)^M.card)⁻¹) := by
              simp only [ENNReal.inv_pow]
        _ ≤ 1 := ENNReal.mul_inv_le_one _
    have hone : (1 : ENNReal) < ENNReal.ofReal r := by
      exact (by
        have := (ENNReal.ofReal_lt_ofReal_iff (by linarith : (0:ℝ) < r)).2 hr
        simpa using this)
    change (bad.card : ENNReal) * ((2 : ENNReal)⁻¹)^M.card <
      ENNReal.ofReal r
    exact lt_of_le_of_lt hmul hone

lemma nonempty_edge_obstruction (h : ¬ HasEdgeLabels) :
    ∃ (K : Finset ℤ)
      (hK : K.Nonempty)
      (τ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
      (r : ℝ), 0 < r ∧ r ≤ 1 ∧ ¬ EdgeData K τ r := by
  classical
  rw [hasEdgeLabels_iff] at h
  push_neg at h
  rcases h with ⟨K, τ, r, hr, hfail⟩
  have hsmall : r ≤ (1 : ℝ) := by
    by_contra hn
    have hlarge : (1:ℝ) < r := lt_of_not_ge hn
    exact hfail (edgeData_of_one_lt K τ r hlarge)
  by_cases hK : K.Nonempty
  · exact ⟨K, hK, τ, r, hr, hsmall, hfail⟩
  · have h0 : K = (∅ : Finset ℤ) :=
      Finset.not_nonempty_iff_eq_empty.mp hK
    subst K
    exact False.elim (hfail (edgeData_empty τ r hr))

-- Inflating a cylinder to a union window just amounts to restrict and then
-- restrict once more.  Stating the two identities explicitly avoids any
-- measurable-set or a.e. bookkeeping in the edge reduction.
lemma cylinder_doubleWindow_previous (L : Finset ℤ) (a : ℕ)
    (S : Set (∀ _i : (↥L), Bool)) :
    let g : ℤ → ℤ := fun i => i - (a:ℤ)
    let L' : Finset ℤ := L.image g
    let pull : (∀ _j : (↥L'), Bool) → (∀ _i : (↥L), Bool) :=
      fun z i => z ⟨g (i:ℤ),
         (by dsimp [L']; exact Finset.mem_image.2 ⟨(i:ℤ), i.property, rfl⟩)⟩
    cylinder (α := fun _ : ℤ => Bool) (doubleWindow L a)
       {z | previousWord L a z ∈ S} = cylinder L' (pull ⁻¹' S) := by
  classical
  dsimp
  ext w
  simp only [mem_cylinder, Set.mem_setOf_eq, Set.mem_preimage]
  -- both restrictions read the coordinate `i-a` from the original stream
  change previousWord L a ((doubleWindow L a).restrict w) ∈ S ↔
    (fun i : (↥L) => w ((i:ℤ) - (a:ℤ))) ∈ S
  rw [previousWord_restrict]

lemma cylinder_doubleWindow_present (L : Finset ℤ) (a : ℕ)
    (S : Set (∀ _i : (↥L), Bool)) :
    cylinder (α := fun _ : ℤ => Bool) (doubleWindow L a)
       {z | presentWord L a z ∈ S} = cylinder L S := by
  classical
  ext w
  simp only [mem_cylinder, Set.mem_setOf_eq]
  rw [presentWord_restrict]

-- One bad edge controls *all* subsets of colours.  If the two readings have
-- advanced by `τ`, membership in `H` on the first is precisely membership in
-- `τ '' H` on the second.  This little finite lemma is often the most useful
-- formulation of the marker/clock target.
lemma edge_symmDiff_card_le
    (K : Finset ℤ)
    (τ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
    (a : ℕ) (L : Finset ℤ)
    (l : (∀ _j : (↥L), Bool) → (∀ _i : (↥K), Bool))
    (H : Set (∀ _i : (↥K), Bool)) :
  let D : Set (∀ _j : (↥(doubleWindow L a)), Bool) :=
      {z | l (previousWord L a z) ∈ H}
  let E : Set (∀ _j : (↥(doubleWindow L a)), Bool) :=
      {z | l (presentWord L a z) ∈ τ '' H}
  ((D ∆ E).toFinite.toFinset.card : ℕ) ≤
      (Finset.univ.filter (fun z :
          (∀ _j : (↥(doubleWindow L a)), Bool) =>
            l (presentWord L a z) ≠ τ (l (previousWord L a z)))).card := by
  classical
  dsimp
  -- use inclusion of finsets; it is completely pointwise
  apply Finset.card_le_card
  intro z hz
  have hz' : z ∈ ({z : (∀ _j : (↥(doubleWindow L a)), Bool) |
                  l (previousWord L a z) ∈ H} ∆
                {z : (∀ _j : (↥(doubleWindow L a)), Bool) |
                  l (presentWord L a z) ∈ τ '' H}) := by
    -- `toFinset` forgets no points on a finite carrier
    exact (Set.Finite.mem_toFinset _).1 hz
  apply Finset.mem_filter.2
  refine ⟨Finset.mem_univ _, ?_⟩
  intro heq
  -- on a good edge the two booleans agree
  have hequiv :
      l (presentWord L a z) ∈ τ '' H ↔
        l (previousWord L a z) ∈ H := by
    constructor
    · intro hp
      rcases hp with ⟨y,hy,hyq⟩
      have : y = l (previousWord L a z) := by
        apply τ.injective
        simpa [heq] using hyq
      simpa [this] using hy
    · intro hp
      refine ⟨l (previousWord L a z), hp, ?_⟩
      simpa [heq]
  -- unfold membership in a symmetric difference
  simp only [Set.mem_symmDiff, Set.mem_setOf_eq] at hz'
  rcases hz' with h | h
  · exact h.2 (hequiv.mpr h.1)
  · exact h.2 (hequiv.mp h.1)

-- Thus the single-window finite edge problem implies the older formulation
-- with separately enlarged cylinders.  No probability theorem is used here;
-- the factor `2^-|M|` is exactly the mass of a word in the common cube.
lemma word_clocks_of_edge_labels (h : HasEdgeLabels) :
    HasWordClocks := by
  classical
  intro K τ r hr
  obtain ⟨a, ha, L, l, hbal, hbad⟩ := h K τ r hr
  refine ⟨a, ha, L, l, ?_, ?_⟩
  · exact hbal
  · intro H
    let D : Set (∀ _j : (↥(doubleWindow L a)), Bool) :=
      {z | l (previousWord L a z) ∈ H}
    let E : Set (∀ _j : (↥(doubleWindow L a)), Bool) :=
      {z | l (presentWord L a z) ∈ τ '' H}
    refine ⟨doubleWindow L a, D, E, ?_, ?_, ?_⟩
    · -- previous (translated) window
      simpa [D] using
        (cylinder_doubleWindow_previous L a
          ({z | l z ∈ H} : Set (∀ _i : (↥L), Bool)))
    · simpa [E] using
        (cylinder_doubleWindow_present L a
          ({z | l z ∈ τ '' H} : Set (∀ _i : (↥L), Bool)))
    ·
      have hc : ((D ∆ E).toFinite.toFinset.card : ℕ) ≤
          (Finset.univ.filter (fun z :
            (∀ _j : (↥(doubleWindow L a)), Bool) =>
              l (presentWord L a z) ≠ τ (l (previousWord L a z)))).card := by
        simpa [D, E] using
          (edge_symmDiff_card_le K τ a L l H)
      have hc' : (((D ∆ E).toFinite.toFinset.card : ℕ) : ENNReal) ≤
          (((Finset.univ.filter (fun z :
            (∀ _j : (↥(doubleWindow L a)), Bool) =>
              l (presentWord L a z) ≠ τ (l (previousWord L a z)))).card : ℕ)
                : ENNReal) := by
        exact_mod_cast hc
      exact lt_of_le_of_lt (mul_le_mul_right' hc' _ ) hbad

lemma balanced_clocks_of_word (h : HasWordClocks) :
    HasBalancedFiniteClocks := by
  classical
  intro K τ r hr
  obtain ⟨a, ha, L, l, hbal, hword⟩ := h K τ r hr
  refine ⟨a, ha, L, l, hbal, ?_⟩
  dsimp
  intro H
  obtain ⟨M, D, E, hD, hE, hcnt⟩ := hword H
  exact fair_clock_of_joint_card' L a
    ({z | l z ∈ H} : Set _)
    ({z | l z ∈ τ '' H} : Set _) M D E hD hE r hcnt

lemma tower_of_word_clocks (h : HasWordClocks) :
    ∀ (K : Finset ℤ)
      (σ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
      (r : ℝ), 0 < r →
        ∃ V : Automorphism (Measure.infinitePi (fun _ : ℤ => fairBool)),
          IsWeaklyMixing (Measure.infinitePi (fun _ : ℤ => fairBool)) V ∧
          ∀ H : Set (∀ _i : (↥K), Bool),
            (Measure.infinitePi (fun _ : ℤ => fairBool))
              ((V.toEquiv '' (cylinder (α := fun _ : ℤ => Bool) K H)) ∆
               ((fairBlockAutomorphism K σ).toEquiv ''
                 (cylinder (α := fun _ : ℤ => Bool) K H))) <
                ENNReal.ofReal r :=
  fair_tower_of_finiteClocks
    (finiteClocks_of_balanced (balanced_clocks_of_word h))


lemma hasEdgeLabels_marker : HasEdgeLabels := by
  classical
  intro K τ r hr
  obtain ⟨b, m, hb, hm, hnum⟩ := HalmosSupport.exists_marker_parameters r hr
  let δ : Type := (↥K)
  let t : ℕ := Fintype.card δ + b
  let N : ℕ := m+1
  have ht : 0 < t := by dsimp [t]; omega
  have hN : 0 < N := by dsimp [N]; omega
  let L : Finset ℤ := HalmosSupport.natWindow (N*t)
  let star : (Fin b → Bool) := fun _ => false
  let l : (∀ _j : (↥L), Bool) → (∀ _i : (↥K), Bool) := fun z =>
       HalmosSupport.markerRead τ N hN star
         (HalmosSupport.packetWindow (δ:=δ) b N ((by simpa [L,t] using z)))
  -- exact constancy of the colour fibres
  have hbal : ∀ u v : (∀ _i : (↥K), Bool),
       Nat.card {z : (∀ _j : (↥L), Bool) // l z = u} =
       Nat.card {z : (∀ _j : (↥L), Bool) // l z = v} := by
    intro u v
    simpa [l, HalmosSupport.markerRead_def] using
      (HalmosSupport.card_clockColor_equiv
        (HalmosSupport.packetWindow (δ:=δ) b N) τ
        (HalmosSupport.firstMarker N hN star)
        (fun i : Fin N => N-1-i.val) u v)
  apply edgeData_of_const_fiber K τ r t ht L l hbal
  have hline := marker_line_bad_card (δ:=δ) b m hb hm τ star
  have hform := HalmosSupport.card_markerBad_le_formula
       (α := (δ → Bool)) (β := (Fin b → Bool)) τ m hm star
  have hnat :
      (Finset.univ.filter (fun z : (↥(doubleWindow L t)) → Bool =>
        l (presentWord L t z) ≠ τ (l (previousWord L t z)))).card ≤
        (2^(Fintype.card δ)) *
            ((2^(Fintype.card δ))*(2^b))^(m+1) +
          ((2^(Fintype.card δ))*(2^b)) *
            ((2^(Fintype.card δ))*((2^b)-1))^m *
              ((2^(Fintype.card δ))*(2^b)) := by
    -- the line decoder and the row estimate have the same predicate
    calc
      _ = (Finset.univ.filter
        (HalmosSupport.markerBadRow τ (m+1) (by omega) star)).card := by
          simpa [t, N, L, l] using hline
      _ ≤ _ := by
        simpa [Fintype.card_fun, Fintype.card_coe, pow_add, mul_pow] using hform
  have hcast :
      (( (Finset.univ.filter (fun z : (↥(doubleWindow L t)) → Bool =>
        l (presentWord L t z) ≠ τ (l (previousWord L t z)))).card : ℕ) : ENNReal) ≤
       (( (2^(Fintype.card δ)) *
            ((2^(Fintype.card δ))*(2^b))^(m+1) +
          ((2^(Fintype.card δ))*(2^b)) *
            ((2^(Fintype.card δ))*((2^b)-1))^m *
              ((2^(Fintype.card δ))*(2^b)) : ℕ) : ENNReal) := by
        exact_mod_cast hnat
  have hc : (doubleWindow L t).card = (m+2)*(Fintype.card δ + b) := by
    simpa [L, N, t, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (card_doubleWindow_natWindow t N ht hN)
  have hsmall := hnum (Fintype.card δ)
  have htot :
      ((( (Finset.univ.filter (fun z : (↥(doubleWindow L t)) → Bool =>
        l (presentWord L t z) ≠ τ (l (previousWord L t z)))).card : ℕ) : ENNReal)) *
        ((2:ENNReal)⁻¹)^((doubleWindow L t).card) < ENNReal.ofReal r :=
    lt_of_le_of_lt (mul_le_mul_right' hcast _) (by simpa [hc] using hsmall)
  exact htot

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem generic_weakly_mixing [StandardBorelSpace X]
    (m : Measure X) [IsProbabilityMeasure m] [NoAtoms m] :
    (∃ G : Set (Automorphism m), IsGδ G ∧ Dense G ∧
      ∀ T ∈ G, IsWeaklyMixing m T) ∧
    (∀ T : Automorphism m, IsWeaklyMixing m T →
      Ergodic (T.toEquiv : X → X) m) :=
/-ResultProofBegin-/
by
  refine ⟨?_, ?_⟩
  · classical
    -- The natural Gδ is the countable subsequence set.  Its openness part
    -- is unconditional; the remaining content is exactly density of this
    -- set and the zero-correlation (square-limit) upgrade above.
    refine ⟨HalmosSubseqSet m, isGδ_halmosSubseqSet m, ?_⟩
    refine ⟨?_, ?_⟩
    · -- It suffices to prove actual weak mixers are dense; the
      -- subsequence set contains every one of them.  The change-of-
      -- coordinates reduction above makes the outstanding approximation
      -- a statement on the real line with an arbitrary atom-free law.
      have hd : Dense {T : Automorphism m | IsWeaklyMixing m T} := by
        apply dense_weakMixing_reduce_real m
        intro ν _ _ n R₀ C ε hC hε
        -- At a centre which is already weakly mixing there is no tower to
        -- build--the centre itself is in every one of its balls.  Separating
        -- this harmless case keeps the remaining approximation issue about
        -- genuinely non-mixing centres (where the Rokhlin/conjugacy step is
        -- needed).
        by_cases h₀ : IsWeaklyMixing ν R₀
        · refine ⟨R₀, h₀, ?_⟩
          intro i
          change ν ((R₀.toEquiv '' (C i)) ∆
            (R₀.toEquiv '' (C i))) < ENNReal.ofReal (ε i)
          have hp : (0 : ENNReal) < ENNReal.ofReal (ε i) :=
            ENNReal.ofReal_pos.2 (hε i)
          simpa using hp
        · -- First remove the overlapping tests.  The Boolean-cell criterion
          -- packages the only still-missing construction as a *uniform*
          -- estimate on the cells of a common finite Boolean algebra.  Once
          -- such estimates are available, the finite-intersection argument
          -- (and the factor equal to the number of cells) is completely
          -- formal. This is the shape needed by the block/cylinder lemmas
          -- above.
          have hdν : Dense
              {T : Automorphism ν | IsWeaklyMixing ν T} := by
            apply dense_weakMixing_of_boolean_atom_uniform ν
            intro q S₀ D η hD hηpos
            -- the centre-mixing case of the cell problem is still trivial:
            -- every single Boolean cell has zero error there. Thus the
            -- remaining active problem has one common real radius and only
            -- finite Boolean atoms, rather than overlapping measurable
            -- events with unrelated radii.
            by_cases hm : IsWeaklyMixing ν S₀
            · refine ⟨S₀, hm, ?_⟩
              intro s
              change ν ((S₀.toEquiv ''
                  (HalmosSupport.boolCell D (↑s : Set (Fin q)))) ∆
                  (S₀.toEquiv ''
                    (HalmosSupport.boolCell D (↑s : Set (Fin q))))) <
                    ENNReal.ofReal η
              have hz : (0 : ENNReal) < ENNReal.ofReal η :=
                ENNReal.ofReal_pos.2 hηpos
              simpa using hz
            · classical
              -- There are two occasionally annoying edge cases in the cell
              -- problem.  They really contain no matching information.  On
              -- as soon as any weakly mixing seed is available; if the ball is
              -- wider than the whole probability space, or if there are no
              -- tests, that seed itself suffices.
              -- Discharging them here leaves the Rokhlin step with actual
              -- positive cells and a genuinely small radius.
              by_cases heasy : (∃ W : Automorphism ν, IsWeaklyMixing ν W) ∧
                    ((1 : ℝ) < η ∨ q = 0)
              · rcases heasy with ⟨⟨T, hT⟩, hbig⟩
                refine ⟨T, hT, ?_⟩
                intro s
                cases hbig with
                | inl hb =>
                    have hp : (1 : ENNReal) < ENNReal.ofReal η :=
                      ENNReal.one_lt_ofReal.mpr hb
                    have hh : ν
                        ((T.toEquiv ''
                           (HalmosSupport.boolCell D
                              (↑s : Set (Fin q)))) ∆
                         (S₀.toEquiv ''
                           (HalmosSupport.boolCell D
                              (↑s : Set (Fin q))))) ≤ (1 : ENNReal) :=
                      prob_le_one
                    exact lt_of_le_of_lt hh hp
                | inr hzero =>
                    subst q
                    have hcell (t : Finset (Fin 0)) :
                        HalmosSupport.boolCell D
                              (↑t : Set (Fin 0)) =
                                (Set.univ : Set ℝ) := by
                      ext x
                      constructor
                      · intro _
                        exact Set.mem_univ _
                      · intro _
                        apply (HalmosSupport.mem_boolCell).2
                        intro i
                        exact Fin.elim0 i
                    have hTi : T.toEquiv ''
                        (HalmosSupport.boolCell D (↑s : Set (Fin 0))) =
                          (Set.univ : Set ℝ) := by
                      rw [hcell s]
                      exact Set.image_univ_of_surjective T.toEquiv.surjective
                    have hSi : S₀.toEquiv ''
                        (HalmosSupport.boolCell D (↑s : Set (Fin 0))) =
                          (Set.univ : Set ℝ) := by
                      rw [hcell s]
                      exact Set.image_univ_of_surjective S₀.toEquiv.surjective
                    rw [hTi, hSi]
                    have hp : (0 : ENNReal) < ENNReal.ofReal η :=
                      ENNReal.ofReal_pos.2 hηpos
                    simpa using hp
              · by_cases hthin :
                    (∃ W : Automorphism ν, IsWeaklyMixing ν W) ∧
                      (∀ s : Finset (Fin q),
                        ν (HalmosSupport.boolCell D (↑s : Set (Fin q))) +
                          ν (HalmosSupport.boolCell D (↑s : Set (Fin q))) <
                              ENNReal.ofReal η)
                · -- Another cheap edge case.  If every cell is so small that
                  -- twice its mass is below the requested radius, *any*
                  -- weak mixer already works; no matching is needed.
                  rcases hthin with ⟨⟨W,hW⟩, hsmall⟩
                  refine ⟨W, hW, ?_⟩
                  intro s
                  exact lt_of_le_of_lt
                    (automorphism_symmDiff_images_le_two ν W S₀
                      (HalmosSupport.boolCell D (↑s : Set (Fin q))))
                    (hsmall s)
                · by_cases htriv :
                      (∃ W : Automorphism ν, IsWeaklyMixing ν W) ∧
                        (∀ s : Finset (Fin q),
                          ν (HalmosSupport.boolCell D (↑s : Set (Fin q))) = 0 ∨
                          ν ((HalmosSupport.boolCell D
                            (↑s : Set (Fin q)))ᶜ) = 0)
                  · -- a Boolean partition with no genuinely intermediate
                    -- atom is again invisible to every automorphism
                    rcases htriv with ⟨⟨W,hW⟩, hcells⟩
                    refine ⟨W, hW, ?_⟩
                    intro s
                    have hp : (0 : ENNReal) < ENNReal.ofReal η :=
                      ENNReal.ofReal_pos.2 hηpos
                    cases hcells s with
                    | inl hnull =>
                        have hz := automorphism_null_symmDiff_images ν W S₀
                          (HalmosSupport.boolCell D (↑s : Set (Fin q))) hnull
                        simpa [hz] using hp
                    | inr hfull =>
                        have hz := automorphism_conull_symmDiff_images ν W S₀
                          (HalmosSupport.boolCell D (↑s : Set (Fin q))) hfull
                        simpa [hz] using hp
                  · -- A zero Boolean cell imposes no condition at all: both
                    -- images have measure zero.  Peeling these off is surprisingly
                    -- helpful in the cutting-and-stacking step, where only positive
                    -- cells can contribute a column.  The remaining active datum is
                    -- therefore just a family of *positive* cells.  Notice also the
                    -- edge conditions above: once a seed is available we may henceforth
                    -- assume a nonempty family and a genuinely bounded radius.
                    obtain ⟨T, hTm, hpos⟩ :
                        ∃ T : Automorphism ν, IsWeaklyMixing ν T ∧
                          ∀ s : Finset (Fin q),
                            0 < ν (HalmosSupport.boolCell D
                              (↑s : Set (Fin q))) →
                            ENNReal.ofReal η ≤
                                ν (HalmosSupport.boolCell D (↑s : Set (Fin q))) +
                                ν (HalmosSupport.boolCell D (↑s : Set (Fin q))) →
                            0 < ν ((HalmosSupport.boolCell D
                                   (↑s : Set (Fin q)))ᶜ) →
                            ENNReal.ofReal η ≤
                              ν ((HalmosSupport.boolCell D (↑s : Set (Fin q)))ᶜ) +
                              ν ((HalmosSupport.boolCell D (↑s : Set (Fin q)))ᶜ) →
                            ν ((T.toEquiv ''
                                (HalmosSupport.boolCell D (↑s : Set (Fin q)))) ∆
                               (S₀.toEquiv ''
                                (HalmosSupport.boolCell D (↑s : Set (Fin q))))) <
                                  ENNReal.ofReal η := by
                      -- Apart from genuinely intermediate cells there is a final
                      -- harmless boundary case which is slightly different from
                      -- `hthin` above.  Some cells can be small while one *different*
                      -- cell is almost conull.  Then every individual test is still
                      -- invisible to any automorphism (read it on the smaller of the
                      -- event and its complement), even though it is neither the
                      -- "all cells small" nor the "all cells null or conull" case.
                      --
                      -- Isolating this case here is useful: from now on a seed and
                      -- the failure of the next predicate furnish an honest Boolean
                      -- cell whose two sides each have mass at least half the
                      -- tolerance.  That is the first column on which a later
                      -- Rokhlin matching argument has to work.
                      by_cases hboundary :
                          (∃ W : Automorphism ν, IsWeaklyMixing ν W) ∧
                            (∀ t : Finset (Fin q),
                              ν (HalmosSupport.boolCell D
                                  (↑t : Set (Fin q))) +
                                ν (HalmosSupport.boolCell D
                                  (↑t : Set (Fin q))) < ENNReal.ofReal η ∨
                              ν ((HalmosSupport.boolCell D
                                  (↑t : Set (Fin q)))ᶜ) +
                                ν ((HalmosSupport.boolCell D
                                  (↑t : Set (Fin q)))ᶜ) < ENNReal.ofReal η)
                      · rcases hboundary with ⟨⟨W, hW⟩, hsmallside⟩
                        refine ⟨W, hW, ?_⟩
                        intro t ht hlarge ht' hlarge'
                        cases hsmallside t with
                        | inl hlt =>
                            -- The hypotheses of the active-cell goal cannot
                            -- hold on the small side.  Writing the contradiction
                            -- explicitly keeps all order comparisons in `ENNReal`.
                            exact (False.elim ((not_lt_of_ge hlarge) hlt))
                        | inr hlt =>
                            exact (False.elim ((not_lt_of_ge hlarge') hlt))
                      ·
                        -- With a seed in hand, failure of this mixed boundary
                        -- case actually exhibits a genuinely two-sided atom.  It
                        -- is convenient to leave the outstanding cutting and
                        -- stacking problem with this witness visible, rather than
                        -- allow the quantifiers over a vacuous family to obscure
                        -- it.  If there is no seed, the other alternative says
                        -- exactly that a first atom-free model still has to be
                        -- built.
                        have h_obstacle :
                            (¬ ∃ W : Automorphism ν, IsWeaklyMixing ν W) ∨
                            ((∃ W : Automorphism ν, IsWeaklyMixing ν W) ∧
                            (∃ t : Finset (Fin q),
                              0 < ν (HalmosSupport.boolCell D
                                  (↑t : Set (Fin q))) ∧
                              0 < ν ((HalmosSupport.boolCell D
                                  (↑t : Set (Fin q)))ᶜ) ∧
                              ENNReal.ofReal η ≤
                                ν (HalmosSupport.boolCell D
                                  (↑t : Set (Fin q))) +
                                  ν (HalmosSupport.boolCell D
                                    (↑t : Set (Fin q))) ∧
                              ENNReal.ofReal η ≤
                                ν ((HalmosSupport.boolCell D
                                  (↑t : Set (Fin q)))ᶜ) +
                                  ν ((HalmosSupport.boolCell D
                                    (↑t : Set (Fin q)))ᶜ))) := by
                          classical
                          by_cases hw : ∃ W : Automorphism ν,
                              IsWeaklyMixing ν W
                          · right
                            refine ⟨hw, ?_⟩
                            -- Negating the finite pointwise alternative at a
                            -- seed gives one label for which neither side is
                            -- cheap.  `push_neg` only manipulates Props; no
                            -- order-completion arguments are hidden here.
                            have hn : ¬ (∀ t : Finset (Fin q),
                                ν (HalmosSupport.boolCell D
                                    (↑t : Set (Fin q))) +
                                  ν (HalmosSupport.boolCell D
                                    (↑t : Set (Fin q))) < ENNReal.ofReal η ∨
                                ν ((HalmosSupport.boolCell D
                                    (↑t : Set (Fin q)))ᶜ) +
                                  ν ((HalmosSupport.boolCell D
                                    (↑t : Set (Fin q)))ᶜ) < ENNReal.ofReal η) := by
                              intro hall
                              exact hboundary ⟨hw, hall⟩
                            push_neg at hn
                            rcases hn with ⟨t, ht, ht'⟩
                            have hp0 : (0 : ENNReal) < ENNReal.ofReal η :=
                              ENNReal.ofReal_pos.2 hηpos
                            have ht0 : 0 < ν (HalmosSupport.boolCell D
                                (↑t : Set (Fin q))) := by
                              by_contra hh
                              have hh' : ν (HalmosSupport.boolCell D
                                  (↑t : Set (Fin q))) = 0 :=
                                (not_lt.mp hh).antisymm bot_le
                              have hzero : ENNReal.ofReal η ≤ (0 : ENNReal) := by
                                simpa [hh'] using ht
                              exact (not_le_of_gt hp0) hzero
                            have ht1 : 0 < ν ((HalmosSupport.boolCell D
                                (↑t : Set (Fin q)))ᶜ) := by
                              by_contra hh
                              have hh' : ν ((HalmosSupport.boolCell D
                                  (↑t : Set (Fin q)))ᶜ) = 0 :=
                                (not_lt.mp hh).antisymm bot_le
                              have hzero : ENNReal.ofReal η ≤ (0 : ENNReal) := by
                                simpa [hh'] using ht'
                              exact (not_le_of_gt hp0) hzero
                            exact ⟨t, ht0, ht1, ht, ht'⟩
                          · exact Or.inl hw
                        have h_core :
                            (¬ ∃ W : Automorphism ν, IsWeaklyMixing ν W) ∨
                            ((∃ W : Automorphism ν, IsWeaklyMixing ν W) ∧
                              ¬ (1 : ℝ) < η ∧ q ≠ 0 ∧
                              ∃ t : Finset (Fin q),
                                0 < ν (HalmosSupport.boolCell D
                                    (↑t : Set (Fin q))) ∧
                                0 < ν ((HalmosSupport.boolCell D
                                    (↑t : Set (Fin q)))ᶜ) ∧
                                ENNReal.ofReal η ≤
                                  ν (HalmosSupport.boolCell D
                                    (↑t : Set (Fin q))) +
                                    ν (HalmosSupport.boolCell D
                                      (↑t : Set (Fin q))) ∧
                                ENNReal.ofReal η ≤
                                  ν ((HalmosSupport.boolCell D
                                    (↑t : Set (Fin q)))ᶜ) +
                                    ν ((HalmosSupport.boolCell D
                                      (↑t : Set (Fin q)))ᶜ)) := by
                          rcases h_obstacle with hn | hx
                          · exact Or.inl hn
                          · right
                            rcases hx with ⟨hw, hx⟩
                            have hnbig : ¬ (1 : ℝ) < η := by
                              intro hb
                              exact heasy ⟨hw, Or.inl hb⟩
                            have hnq : q ≠ 0 := by
                              intro h0
                              exact heasy ⟨hw, Or.inr h0⟩
                            exact ⟨hw, hnbig, hnq, hx⟩
                        -- There is one last zero-cost matching case between the
                        -- boundary reductions and a genuine tower argument.  A seed
                        -- may already carry this particular Boolean partition to the
                        -- prescribed one modulo null sets.  This is weaker than
                        -- equality of the images as sets and so wasn't covered by
                        -- the centre-mixing branch above.  In the weak topology it
                        -- is still exact: every active radius is strictly positive.
                        by_cases hexact :
                            ∃ W : Automorphism ν, IsWeaklyMixing ν W ∧
                              ∀ s : Finset (Fin q),
                                ν ((W.toEquiv ''
                                    (HalmosSupport.boolCell D
                                      (↑s : Set (Fin q)))) ∆
                                   (S₀.toEquiv ''
                                    (HalmosSupport.boolCell D
                                      (↑s : Set (Fin q))))) = 0
                        · rcases hexact with ⟨W, hW, hz⟩
                          refine ⟨W, hW, ?_⟩
                          intro s hs hslarge hsc hsclarge
                          have hp : (0 : ENNReal) < ENNReal.ofReal η :=
                            ENNReal.ofReal_pos.2 hηpos
                          simpa [hz s] using hp
                        · -- In the unresolved case even such a mod-null exact
                          -- conjugacy seed is absent. The rounded common-block
                          -- lemmas above reduce finite Bernoulli recodings to bad
                          -- word counts; the still missing step is to realize those
                          -- recodings by a conjugate of the shift (a Rokhlin
                          -- tower), and then transport that model to this real
                          -- law.
                          -- A convenient formulation of the missing tower step is
                          -- asymptotic.  It is enough to realize the centre on
                          -- this finite partition with weak mixers and errors
                          -- `≤ 1/j` for every positive integer `j`.  `≤` is the
                          -- natural output of the bad-word estimate above;
                          -- coercing it to a strict weak ball once and for all
                          -- avoids ever dividing by the atom mass of a block.
                          by_cases hseq :
                              ∀ j : ℕ, 0 < j →
                                ∃ W : Automorphism ν, IsWeaklyMixing ν W ∧
                                  ∀ t : Finset (Fin q),
                                    ν ((W.toEquiv ''
                                        (HalmosSupport.boolCell D
                                          (↑t : Set (Fin q)))) ∆
                                       (S₀.toEquiv ''
                                        (HalmosSupport.boolCell D
                                          (↑t : Set (Fin q))))) ≤
                                      ENNReal.ofReal (1 / (j : ℝ))
                          · obtain ⟨j, hj⟩ := exists_nat_gt (1 / η)
                            have hj0 : 0 < j := by
                              -- `η` is positive; in particular its reciprocal
                              -- is nonnegative.
                              have hn : (0 : ℝ) ≤ 1 / η :=
                                le_of_lt (one_div_pos.mpr hηpos)
                              have hjr : (0 : ℝ) < j :=
                                lt_of_le_of_lt hn hj
                              exact_mod_cast hjr
                            have hjr : (0 : ℝ) < (j : ℝ) := by
                              exact_mod_cast hj0
                            have hr : (1 / (j : ℝ)) < η := by
                              -- this is exactly the Archimedean choice above
                              have hh := hj
                              have hmul : (1 : ℝ) < (j : ℝ) * η := by
                                have hx : (1 / η) * η < (j : ℝ) * η :=
                                  mul_lt_mul_of_pos_right hh hηpos
                                have hne : η ≠ (0 : ℝ) := ne_of_gt hηpos
                                calc
                                  (1 : ℝ) = (1 / η) * η := by field_simp
                                  _ < (j : ℝ) * η := hx
                              exact (div_lt_iff₀ hjr).2 (by
                                simpa [mul_comm] using hmul)
                            have hrad : ENNReal.ofReal (1 / (j : ℝ)) <
                                ENNReal.ofReal η :=
                              (ENNReal.ofReal_lt_ofReal_iff hηpos).2 hr
                            obtain ⟨W, hW, hWt⟩ := hseq j hj0
                            refine ⟨W, hW, ?_⟩
                            intro t ht htlarge ht' htlarge'
                            exact lt_of_le_of_lt (hWt t) hrad
                          ·
                            -- Thus the only still-active case is precisely
                            -- failure of this asymptotic finite-tower
                            -- statement, with an honest two-sided cell
                            -- (`h_core`) and with no already exact seed
                            -- (`hexact`). The common-block and histogram
                            -- surplus lemmas above show that non-mixing finite
                            -- recodings do satisfy the analogous `≤ 1/j`
                            -- estimate; replacing them by conjugates of the
                            -- bilateral shift without increasing it is the
                            -- remaining Rokhlin column.
                            -- The word ``tower'' may now be taken quite
                            -- literally: on the fair product it only has to
                            -- replace a permutation of a finite cube.  All
                            -- rounding and the simultaneous Boolean labels
                            -- have been accounted for above.  If an exact
                            -- measured identification with that model and
                            -- this finite-cube replacement are supplied, the
                            -- present obstruction vanishes immediately.
                            by_cases hmodel :
                              ∃ e : ℝ ≃ᵐ (ℤ → Bool),
                                MeasurePreserving (e : ℝ → (ℤ → Bool)) ν
                                  (Measure.infinitePi (fun _ : ℤ => fairBool)) ∧
                                (∀ (K : Finset ℤ)
                                  (σ : (∀ _j : (↥K), Bool) ≃
                                       (∀ _j : (↥K), Bool))
                                  (r : ℝ), 0 < r →
                                    ∃ V : Automorphism
                                        (Measure.infinitePi
                                          (fun _ : ℤ => fairBool)),
                                      IsWeaklyMixing
                                        (Measure.infinitePi
                                          (fun _ : ℤ => fairBool)) V ∧
                                      ∀ H : Set (∀ _j : (↥K), Bool),
                                       (Measure.infinitePi
                                          (fun _ : ℤ => fairBool))
                                        ((V.toEquiv ''
                                           (cylinder
                                            (α := fun _ : ℤ => Bool) K H)) ∆
                                         ((fairBlockAutomorphism K σ).toEquiv ''
                                           (cylinder
                                            (α := fun _ : ℤ => Bool) K H))) <
                                             ENNReal.ofReal r)
                            · rcases hmodel with ⟨e, he, htower⟩
                              let ι := Finset (Fin q)
                              let N : ℕ := Fintype.card ι
                              let en : ι ≃ Fin N := Fintype.equivFin ι
                              let P : Fin N → Set ℝ := fun j =>
                                HalmosSupport.boolCell D
                                  (↑(en.symm j) : Set (Fin q))
                              have hP (j : Fin N) : MeasurableSet (P j) := by
                                dsimp [P]
                                exact HalmosSupport.measurableSet_boolCell hD _
                              obtain ⟨W, hW, hWP⟩ :=
                                fin_of_equiv_fair_block_tower ν e he htower
                                  N S₀ P hP η hηpos
                              refine ⟨W, hW, ?_⟩
                              intro s hs hs' hsc hsc'
                              have hh := hWP (en s)
                              simpa [P] using hh
                            ·
                              -- Separate the harmless descriptive-set
                              -- issue (an *exact*, not mod-null,
                              -- identification of the laws) from the actual
                              -- column.  This disjunction is often the most
                              -- useful input to the next construction: once
                              -- such an `e` has been built the only missing
                              -- predicate has no reference to the real law.
                              have hmissing :
                                (¬ ∃ e : ℝ ≃ᵐ (ℤ → Bool),
                                  MeasurePreserving
                                    (e : ℝ → (ℤ → Bool)) ν
                                      (Measure.infinitePi
                                       (fun _ : ℤ => fairBool))) ∨
                                (∃ e : ℝ ≃ᵐ (ℤ → Bool),
                                  MeasurePreserving
                                    (e : ℝ → (ℤ → Bool)) ν
                                      (Measure.infinitePi
                                       (fun _ : ℤ => fairBool)) ∧
                                  ¬ (∀ (K : Finset ℤ)
                                    (σ : (∀ _j : (↥K), Bool) ≃
                                         (∀ _j : (↥K), Bool))
                                    (r : ℝ), 0 < r →
                                      ∃ V : Automorphism
                                        (Measure.infinitePi
                                          (fun _ : ℤ => fairBool)),
                                      IsWeaklyMixing
                                        (Measure.infinitePi
                                          (fun _ : ℤ => fairBool)) V ∧
                                      ∀ H : Set (∀ _j : (↥K), Bool),
                                       (Measure.infinitePi
                                          (fun _ : ℤ => fairBool))
                                        ((V.toEquiv '' (cylinder
                                          (α := fun _ : ℤ => Bool) K H)) ∆
                                         ((fairBlockAutomorphism K σ).toEquiv ''
                                          (cylinder
                                           (α := fun _ : ℤ => Bool) K H))) <
                                              ENNReal.ofReal r)) := by
                                classical
                                by_cases heqv : ∃ e : ℝ ≃ᵐ (ℤ → Bool),
                                  MeasurePreserving
                                    (e : ℝ → (ℤ → Bool)) ν
                                    (Measure.infinitePi
                                      (fun _ : ℤ => fairBool))
                                · right
                                  rcases heqv with ⟨e, he⟩
                                  refine ⟨e, he, ?_⟩
                                  intro ht
                                  exact hmodel ⟨e, he, ht⟩
                                · exact Or.inl heqv
                              -- A positive row can now be taken to be an
                              -- entirely finite clock.  Positive translations
                              -- of the fair streams are mixing (rather than
                              -- just aperiodic), as proved above.
                              have hgap :
                                (¬ ∃ e : ℝ ≃ᵐ (ℤ → Bool),
                                  MeasurePreserving
                                    (e : ℝ → (ℤ → Bool)) ν
                                      (Measure.infinitePi
                                       (fun _ : ℤ => fairBool))) ∨
                                (∃ (K : Finset ℤ) (hK : K.Nonempty)
                                   (τ : (∀ _i : (↥K), Bool) ≃ (∀ _i : (↥K), Bool))
                                   (u : ℝ), 0 < u ∧ u ≤ 1 ∧ ¬ EdgeData K τ u) := by
                                classical
                                by_cases he0 : ∃ e : ℝ ≃ᵐ (ℤ → Bool),
                                  MeasurePreserving
                                    (e : ℝ → (ℤ → Bool)) ν
                                      (Measure.infinitePi
                                       (fun _ : ℤ => fairBool))
                                · by_cases hclk : HasEdgeLabels
                                  · exfalso
                                    rcases he0 with ⟨e, he⟩
                                    have ht := tower_of_word_clocks
                                      (word_clocks_of_edge_labels hclk)
                                    exact hmodel ⟨e, he, ht⟩
                                  · exact Or.inr
                                      (nonempty_edge_obstruction hclk)
                                · exact Or.inl he0
                              -- No limiting weak-mixing calculation remains in
                              -- the second arm.  The troublesome witness is now a
                              -- *nonempty finite* block and `0 < u ≤ 1`; its sole
                              -- negated field is `EdgeData`.  An `EdgeData` member is
                              -- just a uniformly balanced colouring of a finite cube
                              -- and a bound for the overlap edges of two translated
                              -- windows (`word_clocks_of_edge_labels`).  Thus neither
                              -- measurable sets nor automorphisms occur in that arm.
                              -- The first arm is the exact, not mod-null, Borel
                              -- identification of the two laws.  Constructing that
                              -- identification, and the complementary small-edge
                              -- colouring, are precisely the two remaining Rokhlin
                              -- inputs.
                              -- At this stage it is useful to isolate the two honest
                              -- non-formal inputs.  Everything after them is now a
                              -- contradiction with `hmodel`; in particular there is
                              -- no additional approximation/limit assertion hidden in
                              -- this branch.  Notice the importance of the *exact*
                              -- equivalence here: a mod-null inverse does not even
                              -- give an `Automorphism` in our bundled definition.
                              by_cases hprimitive :
                                (¬ ∃ e : ℝ ≃ᵐ (ℤ → Bool),
                                    MeasurePreserving
                                      (e : ℝ → (ℤ → Bool)) ν
                                        (Measure.infinitePi
                                          (fun _ : ℤ => fairBool))) ∨
                                  (¬ HasEdgeLabels)
                              ·
                                -- These are now the only two possible obstructions.
                                -- For the second one all probability estimates have
                                -- disappeared: `nonempty_edge_obstruction` is a
                                -- nonempty finite cube and `EdgeData` is a single
                                -- elementary word count. The support lemmas
                                -- `markerBadRow_exception`, `card_markerLeft`,
                                -- `card_markerGap_mid`, and
                                -- `card_markerBad_le_formula` state the first-marker
                                -- bound entirely as cards of finite functions; they
                                -- are often the convenient starting point for the
                                -- as-yet missing encoding of such a row by consecutive
                                -- integer coordinates. The other arm is the exact
                                -- standard-Borel law identification (not just the
                                -- usual completion/mod-null theorem).
                                rcases hprimitive with hnoModel | hnoClock
                                ·
                                  -- The marker construction above removes the finite
                                  -- clock obstruction altogether.  What remains in
                                  -- this arm is only the exact Borel law isomorphism
                                  -- (as opposed to the usual mod-null one).
                                  exfalso
                                  let e₀ : ℝ ≃ᵐ ℝ :=
                                    HalmosRealLaw.cdfBorelEquiv ν bernoulliRealLaw
                                  have hm₀ : MeasurePreserving (e₀ : ℝ → ℝ)
                                      ν bernoulliRealLaw := by
                                    refine ⟨e₀.measurable, ?_⟩
                                    letI : IsFiniteMeasure
                                        (Measure.map (e₀ : ℝ → ℝ) ν) :=
                                      Measure.isFiniteMeasure_map ν (e₀ : ℝ → ℝ)
                                    apply Measure.ext_of_Iic
                                    intro a
                                    rw [Measure.map_apply e₀.measurable
                                      measurableSet_Iic]
                                    simpa [e₀] using
                                      (HalmosRealLaw.cdfBorelEquiv_preimage_Iic
                                        ν bernoulliRealLaw a)
                                  have hmB' : MeasurePreserving
                                      (bernoulliRealEquiv.symm : (ℤ → Bool) → ℝ)
                                      (Measure.infinitePi (fun _ : ℤ => fairBool))
                                      bernoulliRealLaw := by
                                    exact bernoulliRealEquiv.symm.measurable.measurePreserving _
                                  have hmB : MeasurePreserving
                                      (bernoulliRealEquiv : ℝ → (ℤ → Bool))
                                      bernoulliRealLaw
                                      (Measure.infinitePi (fun _ : ℤ => fairBool)) :=
                                    MeasurePreserving.symm bernoulliRealEquiv.symm hmB'
                                  apply hnoModel
                                  refine ⟨e₀.trans bernoulliRealEquiv, ?_⟩
                                  exact hmB.comp hm₀
                                · exact False.elim (hnoClock hasEdgeLabels_marker)
                              ·
                                -- Outside those two primitive inputs the purported
                                -- remaining case is impossible.  Pull the exact model
                                -- out first, then use the word clocks to supply precisely
                                -- the tower that `hmodel` says it has lost.
                                have he0 : ∃ e : ℝ ≃ᵐ (ℤ → Bool),
                                    MeasurePreserving
                                      (e : ℝ → (ℤ → Bool)) ν
                                        (Measure.infinitePi
                                          (fun _ : ℤ => fairBool)) := by
                                  classical
                                  by_contra hn
                                  exact hprimitive (Or.inl hn)
                                have hclock : HasEdgeLabels := by
                                  classical
                                  by_contra hn
                                  exact hprimitive (Or.inr hn)
                                rcases he0 with ⟨e, he⟩
                                have ht : ∀ (K : Finset ℤ)
                                  (σ : (∀ _i : (↥K), Bool) ≃
                                       (∀ _i : (↥K), Bool))
                                  (r : ℝ), 0 < r →
                                    ∃ V : Automorphism
                                        (Measure.infinitePi
                                          (fun _ : ℤ => fairBool)),
                                      IsWeaklyMixing
                                        (Measure.infinitePi
                                          (fun _ : ℤ => fairBool)) V ∧
                                      ∀ H : Set (∀ _i : (↥K), Bool),
                                       (Measure.infinitePi
                                         (fun _ : ℤ => fairBool))
                                        ((V.toEquiv '' (cylinder
                                           (α := fun _ : ℤ => Bool) K H)) ∆
                                         ((fairBlockAutomorphism K σ).toEquiv ''
                                            (cylinder
                                              (α := fun _ : ℤ => Bool) K H))) <
                                            ENNReal.ofReal r :=
                                  tower_of_word_clocks
                                    (word_clocks_of_edge_labels hclock)
                                exact False.elim (hmodel ⟨e, he, ht⟩)
                    refine ⟨T, hTm, ?_⟩
                    intro s
                    by_cases hs : ν (HalmosSupport.boolCell D
                          (↑s : Set (Fin q))) = 0
                    · have hz := automorphism_null_symmDiff_images ν T S₀
                          (HalmosSupport.boolCell D (↑s : Set (Fin q))) hs
                      have hp : (0 : ENNReal) < ENNReal.ofReal η :=
                        ENNReal.ofReal_pos.2 hηpos
                      simpa [hz] using hp
                    · have hs' : 0 < ν (HalmosSupport.boolCell D
                          (↑s : Set (Fin q))) :=
                          (pos_iff_ne_zero.mpr hs)
                      by_cases hfull : ν ((HalmosSupport.boolCell D
                          (↑s : Set (Fin q)))ᶜ) = 0
                      · have hz := automorphism_conull_symmDiff_images ν T S₀
                          (HalmosSupport.boolCell D (↑s : Set (Fin q))) hfull
                        have hp : (0 : ENNReal) < ENNReal.ofReal η :=
                          ENNReal.ofReal_pos.2 hηpos
                        simpa [hz] using hp
                      · have hfull' : 0 < ν ((HalmosSupport.boolCell D
                              (↑s : Set (Fin q)))ᶜ) :=
                            (pos_iff_ne_zero.mpr hfull)
                        by_cases hcolight :
                            ν ((HalmosSupport.boolCell D (↑s : Set (Fin q)))ᶜ) +
                              ν ((HalmosSupport.boolCell D (↑s : Set (Fin q)))ᶜ) <
                                ENNReal.ofReal η
                        · exact lt_of_le_of_lt
                            (automorphism_symmDiff_images_le_two_compl ν T S₀
                              (HalmosSupport.boolCell D (↑s : Set (Fin q))))
                            hcolight
                        · have hcoheavy : ENNReal.ofReal η ≤
                              ν ((HalmosSupport.boolCell D (↑s : Set (Fin q)))ᶜ) +
                                ν ((HalmosSupport.boolCell D (↑s : Set (Fin q)))ᶜ) :=
                              le_of_not_gt hcolight
                          by_cases hlight :
                              ν (HalmosSupport.boolCell D (↑s : Set (Fin q))) +
                                ν (HalmosSupport.boolCell D (↑s : Set (Fin q))) <
                                  ENNReal.ofReal η
                          · -- light cells require no matching.  This is the
                            -- set-level version of the familiar `2 μ(C)` bound.
                            exact lt_of_le_of_lt
                              (automorphism_symmDiff_images_le_two ν T S₀
                                (HalmosSupport.boolCell D
                                  (↑s : Set (Fin q)))) hlight
                          · have hheavy : ENNReal.ofReal η ≤
                                ν (HalmosSupport.boolCell D (↑s : Set (Fin q))) +
                                  ν (HalmosSupport.boolCell D (↑s : Set (Fin q))) :=
                                le_of_not_gt hlight
                            exact hpos s hs' hheavy hfull' hcoheavy
          -- recover the requested unequal radii and overlapping tests by
          -- the already-proved finite-neighbourhood criterion
          exact fin_center_weakMixing_of_dense ν hdν n R₀ C ε hC hε
      refine Dense.mono ?_ hd
      intro T hmix
      exact weakMixing_mem_halmosSubseqSet m T hmix
    · intro T hT
      exact weakMixing_of_halmosSubseq_of_square_limits m T hT
        (fun A B hA hB =>
          automorphism_square_correlation_has_limit m T A B hA hB)
  · intro T hT
    exact weakMixing_ergodic_aux m T hT
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
