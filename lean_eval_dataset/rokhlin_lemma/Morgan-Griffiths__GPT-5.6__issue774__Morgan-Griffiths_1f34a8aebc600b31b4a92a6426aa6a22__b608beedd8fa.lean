import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/rokhlin_lemma_923ee2bc80/Foundation.lean

open MeasureTheory Set Function
open scoped ENNReal NNReal

namespace RokhlinSupport

/-- An image under a measure preserving map has outer measure at least the
measure of a measurable set it contains a copy of.  We state it without a
measurability hypothesis on `s`; this is useful because images of measurable
sets need not be measurable for the (uncompleted) Borel measure. -/
theorem measure_le_image_of_preserving {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β}
    (hf : MeasurePreserving f μ ν) (s : Set α) : μ s ≤ ν (f '' s) := by
  obtain ⟨u, hu, hum, humeq⟩ := exists_measurable_superset ν (f '' s)
  have hsub : s ⊆ f ⁻¹' u := by
    intro x hx
    exact hu ⟨x, hx, rfl⟩
  calc
    μ s ≤ μ (f ⁻¹' u) := measure_mono hsub
    _ = ν u := hf.measure_preimage hum.nullMeasurableSet
    _ = ν (f '' s) := humeq

/-- An aperiodic measure preserving transformation of a standard Borel
probability space has no atoms.  This only uses that points are measurable;
the standard Borel assumption supplies that. -/
theorem measure_singleton_eq_zero_of_aperiodic
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → α)
    (hf : MeasurePreserving f μ μ)
    (ha : μ (Function.periodicPts f) = 0) (x : α) : μ ({x} : Set α) = 0 := by
  -- put `a` for the mass of the original point
  classical
  let a : ENNReal := μ ({x} : Set α)
  by_contra hane
  have a0 : a ≠ 0 := by simpa [a] using hane
  -- positive mass points cannot be periodic
  have notper_of_mass : ∀ y : α, a ≤ μ ({y} : Set α) → y ∉ Function.periodicPts f := by
    intro y hy hper
    have hzero : μ ({y} : Set α) = 0 :=
      measure_mono_null (singleton_subset_iff.mpr hper) ha
    exact a0 (nonpos_iff_eq_zero.mp (hzero ▸ hy))
  let p : ℕ → α := fun k => f^[k] x
  have mass (k : ℕ) : a ≤ μ ({p k} : Set α) := by
    -- apply preservation to the singleton above `f^[k] x`
    have hsub : ({x} : Set α) ⊆ (f^[k]) ⁻¹' ({p k} : Set α) := by
      intro y hy
      have hy' : y = x := (Set.mem_singleton_iff.mp hy)
      subst y
      simp [p]
    calc
      a = μ ({x} : Set α) := rfl
      _ ≤ μ ((f^[k]) ⁻¹' ({p k} : Set α)) := measure_mono hsub
      _ = μ ({p k} : Set α) :=
        (hf.iterate k).measure_preimage (measurableSet_singleton (p k)).nullMeasurableSet
  have p_notper (k : ℕ) : p k ∉ Function.periodicPts f :=
    notper_of_mass (p k) (mass k)
  have pinj : Function.Injective p := by
    intro i j hij
    -- a repeated entry of a forward orbit is periodic (possibly after a tail)
    apply le_antisymm
    · by_contra hnle
      have hji : j < i := Nat.lt_of_not_ge hnle
      have hpos : 0 < i - j := Nat.sub_pos_of_lt hji
      have hfix : Function.IsPeriodicPt f (i-j) (p j) := by
        unfold Function.IsPeriodicPt Function.IsFixedPt
        -- commute the two iterates
        dsimp [p] at hij ⊢
        -- f^[i-j] (f^[j] x) = f^[i] x
        calc
          (f^[i-j]) (f^[j] x) = f^[(i-j)+j] x := (Function.iterate_add_apply f (i-j) j x).symm
          _ = f^[i] x := by rw [Nat.sub_add_cancel hji.le]
          _ = f^[j] x := hij
      exact p_notper j ⟨i-j, hpos, hfix⟩
    · by_contra hnle
      have hij' : i < j := Nat.lt_of_not_ge hnle
      have hpos : 0 < j - i := Nat.sub_pos_of_lt hij'
      have hfix : Function.IsPeriodicPt f (j-i) (p i) := by
        unfold Function.IsPeriodicPt Function.IsFixedPt
        dsimp [p] at hij ⊢
        calc
          (f^[j-i]) (f^[i] x) = f^[(j-i)+i] x := (Function.iterate_add_apply f (j-i) i x).symm
          _ = f^[j] x := by rw [Nat.sub_add_cancel hij'.le]
          _ = f^[i] x := hij.symm
      exact p_notper i ⟨j-i, hpos, hfix⟩
  obtain ⟨m, hm0, hm⟩ := ENNReal.exists_nat_pos_mul_gt a0 (by simp : (1:ENNReal) ≠ ∞)
  let pieces : ℕ → Set α := fun k => ({p k} : Set α)
  have hd : (↑(Finset.range m) : Set ℕ).PairwiseDisjoint pieces := by
    intro i hi j hj hij
    have hne : p i ≠ p j := fun e => hij (pinj e)
    exact Set.disjoint_singleton.mpr hne
  have hmeas (k : ℕ) : MeasurableSet (pieces k) := measurableSet_singleton _
  have hbig : (↑m : ENNReal) * a ≤ μ (⋃ k ∈ Finset.range m, pieces k) := by
    rw [measure_biUnion_finset hd (fun k hk => hmeas k)]
    -- the constant lower bound adds up
    simpa using (Finset.sum_le_sum (fun k (_hk : k ∈ Finset.range m) => mass k))
  have hle : μ (⋃ k ∈ Finset.range m, pieces k) ≤ (1 : ENNReal) := by
    calc
      μ (⋃ k ∈ Finset.range m, pieces k) ≤ μ (Set.univ : Set α) := measure_mono (by intro; simp)
      _ = 1 := measure_univ
  exact (not_lt_of_ge (hbig.trans hle)) hm

theorem noAtoms_of_aperiodic
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → α)
    (hf : MeasurePreserving f μ μ) (ha : μ (Function.periodicPts f) = 0) :
    NoAtoms μ where
  measure_singleton := measure_singleton_eq_zero_of_aperiodic μ f hf ha

end RokhlinSupport

-- END INLINED FILE: Mathlib/Support/rokhlin_lemma_923ee2bc80/Foundation.lean

-- BEGIN INLINED FILE: Mathlib/Support/rokhlin_lemma_923ee2bc80/Levels.lean

open MeasureTheory Set Function

namespace RokhlinSupport

variable {α : Type*}

/-- The exact finite first hitting level of `A`.  Points that never hit `A`
are simply in none of the `hitLevel`s.  Keeping levels as sets avoids choices
of a default value for such points. -/
def hitLevel (f : α → α) (A : Set α) (k : ℕ) : Set α :=
  (f^[k]) ⁻¹' A \ ⋃ j ∈ Finset.range k, (f^[j]) ⁻¹' A

lemma mem_hitLevel_iff {f : α → α} {A : Set α} {k : ℕ} {x : α} :
    x ∈ hitLevel f A k ↔ f^[k] x ∈ A ∧ ∀ j < k, f^[j] x ∉ A := by
  classical
  simp [hitLevel]

lemma measurable_hitLevel [MeasurableSpace α] {f : α → α} (hf : Measurable f)
    {A : Set α} (hA : MeasurableSet A) (k : ℕ) : MeasurableSet (hitLevel f A k) := by
  classical
  refine (hA.preimage (hf.iterate k)).diff ?_
  exact Finset.measurableSet_biUnion _ (fun j hj => hA.preimage (hf.iterate j))

lemma hitLevel_unique {f : α → α} {A : Set α} {k l : ℕ} {x : α}
    (hk : x ∈ hitLevel f A k) (hl : x ∈ hitLevel f A l) : k = l := by
  rcases mem_hitLevel_iff.mp hk with ⟨hk0,hk'⟩
  rcases mem_hitLevel_iff.mp hl with ⟨hl0,hl'⟩
  rcases lt_trichotomy k l with h | h | h
  · exact False.elim ((hl' k h) hk0)
  · exact h
  · exact False.elim ((hk' l h) hl0)

/-- Move forward inside a first hitting string. -/
lemma hitLevel_forward {f : α → α} {A : Set α} {q j : ℕ} {x : α}
    (hx : x ∈ hitLevel f A (q+j)) : f^[j] x ∈ hitLevel f A q := by
  rcases mem_hitLevel_iff.mp hx with ⟨h0,hlt⟩
  apply mem_hitLevel_iff.mpr
  constructor
  · simpa [Function.iterate_add_apply] using h0
  · intro r hr hin
    have : f^[r+j] x ∈ A := by
      simpa [Function.iterate_add_apply] using hin
    exact hlt (r+j) (Nat.add_lt_add_right hr j) this

/-- A residue class of the high first hitting levels.  Only levels at least
`n` are kept; this harmless discard is what later bounds the error near the
roof. -/
def residueBase (f : α → α) (A : Set α) (n i : ℕ) : Set α :=
  ⋃ q : {q : ℕ // n ≤ q ∧ q % n = i}, hitLevel f A (q : ℕ)

lemma mem_residueBase {f : α → α} {A : Set α} {n i : ℕ} {x : α} :
    x ∈ residueBase f A n i ↔
    ∃ q : ℕ, n ≤ q ∧ q % n = i ∧ x ∈ hitLevel f A q := by
  classical
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨q,hq⟩
    exact ⟨q, q.property.1, q.property.2, hq⟩
  · rintro ⟨q,hq,hi,hmem⟩
    exact Set.mem_iUnion.2 ⟨(⟨q,hq,hi⟩ : {q : ℕ // n ≤ q ∧ q % n = i}), hmem⟩

lemma measurable_residueBase [MeasurableSpace α] {f : α → α} (hf : Measurable f)
    {A : Set α} (hA : MeasurableSet A) (n i : ℕ) :
    MeasurableSet (residueBase f A n i) := by
  classical
  exact MeasurableSet.iUnion (fun q => measurable_hitLevel hf hA (q : ℕ))

/-- The first `n` forward images of any one residue class of high first-hit
levels are disjoint.  This assertion is wholly set-theoretic and works for a
non-invertible map. -/
theorem pairwiseDisjoint_images_residueBase {f : α → α} {A : Set α}
    {n i : ℕ} (hn : 0 < n) :
    (↑(Finset.range n) : Set ℕ).PairwiseDisjoint
      (fun j => (f^[j]) '' (residueBase f A n i)) := by
  classical
  intro j hj l hl hjl
  -- We use disjointness by elements so as not to ask measurability of images.
  apply Set.disjoint_left.2
  intro y hyj hyl
  rcases hyj with ⟨x, hx, rfl⟩
  -- `x` lies on a high level `qj`
  rcases mem_residueBase.mp hx with ⟨qj, hqjN, hqji, hxqj⟩
  -- express its level as a head plus `j`
  have hjlt : j < n := Finset.mem_range.mp hj
  have hjq : j ≤ qj := Nat.le_trans (Nat.le_of_lt hjlt) hqjN
  have hxback : f^[j] x ∈ hitLevel f A (qj - j) := by
    have hxe : x ∈ hitLevel f A ((qj-j)+j) := by
      simpa [Nat.sub_add_cancel hjq] using hxqj
    exact hitLevel_forward hxe
  rcases hyl with ⟨z, hz, heq⟩
  rcases mem_residueBase.mp hz with ⟨ql, hqlN, hqli, hzql⟩
  have hllt : l < n := Finset.mem_range.mp hl
  have hlq : l ≤ ql := Nat.le_trans (Nat.le_of_lt hllt) hqlN
  have hzback : f^[l] z ∈ hitLevel f A (ql - l) := by
    have hze : z ∈ hitLevel f A ((ql-l)+l) := by
      simpa [Nat.sub_add_cancel hlq] using hzql
    exact hitLevel_forward hze
  have hb : f^[j] x = f^[l] z := heq.symm
  have hdiff : qj - j = ql - l := by
    apply hitLevel_unique hxback
    simpa [hb] using hzback
  -- cancel the common head modulo n.  Addition on `Fin n` is a permutation.
  have hmodql : Nat.ModEq n qj ql := by
    exact hqji.trans hqli.symm
  have hmodsum : Nat.ModEq n ((qj-j)+j) ((qj-j)+l) := by
    have e1 : (qj-j)+j = qj := Nat.sub_add_cancel hjq
    have e2 : (qj-j)+l = ql := by rw [hdiff, Nat.sub_add_cancel hlq]
    rwa [e1, e2]
  have hmodjl : Nat.ModEq n j l :=
    (Nat.ModEq.add_iff_left (Nat.ModEq.refl (qj-j))).1 hmodsum
  have hjeq : j = l := by
    have := hmodjl
    change j % n = l % n at this
    simpa [Nat.mod_eq_of_lt hjlt, Nat.mod_eq_of_lt hllt] using this
  exact hjl hjeq

end RokhlinSupport

-- END INLINED FILE: Mathlib/Support/rokhlin_lemma_923ee2bc80/Levels.lean

-- BEGIN INLINED FILE: Mathlib/Support/rokhlin_lemma_923ee2bc80/Pieces.lean

open MeasureTheory Set Function
namespace RokhlinSupport

/-- A useful outer-measure version of finite disjoint additivity.  The small
pieces themselves may not be measurable (they will be Borel images).  It is
enough to have pairwise disjoint *measurable* ambient sets for them. -/
theorem sum_measure_le_biUnion_of_containers {α ι : Type*}
    [MeasurableSpace α] (μ : Measure α) (t : Finset ι)
    (E S : ι → Set α)
    (hsub : ∀ i ∈ t, E i ⊆ S i)
    (hS : ∀ i ∈ t, MeasurableSet (S i))
    (hd : (↑t : Set ι).PairwiseDisjoint S) :
    (∑ i ∈ t, μ (E i)) ≤ μ (⋃ i ∈ t, E i) := by
  classical
  obtain ⟨u, hu, hum, humeq⟩ := exists_measurable_superset μ (⋃ i ∈ t, E i)
  have hcontained (i : ι) (hi : i ∈ t) : E i ⊆ u ∩ S i := by
    intro x hx
    refine ⟨hu (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hx⟩⟩), hsub i hi hx⟩
  have hdis : (↑t : Set ι).PairwiseDisjoint (fun i => u ∩ S i) := by
    intro i hi j hj hij
    exact Set.disjoint_of_subset_right inter_subset_right
      (Set.disjoint_of_subset_left inter_subset_right (hd hi hj hij))
  calc
    (∑ i ∈ t, μ (E i)) ≤ (∑ i ∈ t, μ (u ∩ S i)) :=
      Finset.sum_le_sum (fun i hi => measure_mono (hcontained i hi))
    _ = μ (⋃ i ∈ t, (u ∩ S i)) :=
      (measure_biUnion_finset hdis (fun i hi => hum.inter (hS i hi))).symm
    _ ≤ μ u := measure_mono (by
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i,hx⟩
      rcases Set.mem_iUnion.1 hx with ⟨hi,hx⟩
      exact hx.1)
    _ = μ (⋃ i ∈ t, E i) := humeq

/-- Preimages have the stated measure even for iterates; using a measurable
hull gives the companion inequality for (possibly nonmeasurable) images. -/
theorem measure_mono_image_iterate {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → α} (hf : MeasurePreserving f μ μ)
    (s : Set α) (j : ℕ) : μ s ≤ μ ((f^[j]) '' s) :=
  measure_le_image_of_preserving (hf.iterate j) s

end RokhlinSupport

namespace RokhlinSupport
open MeasureTheory Set Function
variable {α : Type*}

/-- Measurable ambient set for the `j`th floor.  We include all head levels
whose sum with `j` has the chosen residue. -/
def floorContainer (f : α → α) (A : Set α) (n i j : ℕ) : Set α :=
  ⋃ q : {q : ℕ // (q+j) % n = i}, hitLevel f A (q : ℕ)

lemma mem_floorContainer {f : α → α} {A : Set α} {n i j : ℕ} {x : α} :
    x ∈ floorContainer f A n i j ↔
    ∃ q : ℕ, (q+j) % n = i ∧ x ∈ hitLevel f A q := by
  classical
  constructor
  · intro hx; rcases Set.mem_iUnion.1 hx with ⟨q,hq⟩
    exact ⟨q, q.property, hq⟩
  · rintro ⟨q,hq,h⟩
    exact Set.mem_iUnion.2 ⟨(⟨q,hq⟩ : {q : ℕ // (q+j)%n=i}), h⟩

lemma measurable_floorContainer [MeasurableSpace α] (f : α → α) (A : Set α)
    (hf : Measurable f) (hA : MeasurableSet A) (n i j : ℕ) :
    MeasurableSet (floorContainer f A n i j) := by
  classical
  exact MeasurableSet.iUnion (fun q => measurable_hitLevel hf hA (q : ℕ))

lemma image_residue_subset_floorContainer {f : α → α} {A : Set α}
    {n i j : ℕ} (hj : j < n) :
    (f^[j]) '' (residueBase f A n i) ⊆ floorContainer f A n i j := by
  rintro y ⟨x,hx,rfl⟩
  rcases mem_residueBase.mp hx with ⟨q,hqn,hqi,hq⟩
  have hjq : j ≤ q := hqn.trans' (Nat.le_of_lt hj)
  have hhead : f^[j] x ∈ hitLevel f A (q-j) := by
    apply hitLevel_forward (q := q-j) (j := j)
    simpa [Nat.sub_add_cancel hjq] using hq
  apply mem_floorContainer.mpr
  refine ⟨q-j, ?_, hhead⟩
  simpa [Nat.sub_add_cancel hjq] using hqi

lemma pairwiseDisjoint_floorContainer {f : α → α} {A : Set α}
    {n i : ℕ} :
    (↑(Finset.range n) : Set ℕ).PairwiseDisjoint
       (floorContainer f A n i) := by
  classical
  intro j hj l hl hjl
  apply Set.disjoint_left.2
  intro x hx hxl
  rcases mem_floorContainer.mp hx with ⟨q,hqi,hq⟩
  rcases mem_floorContainer.mp hxl with ⟨r,hri,hr⟩
  have qr : q = r := hitLevel_unique hq hr
  subst r
  have hm : Nat.ModEq n (q+j) (q+l) := hqi.trans hri.symm
  have hjmodl : Nat.ModEq n j l :=
    (Nat.ModEq.add_iff_left (Nat.ModEq.refl q)).1 hm
  have hjlt : j < n := Finset.mem_range.mp hj
  have hllt : l < n := Finset.mem_range.mp hl
  apply hjl
  change j % n = l % n at hjmodl
  simpa [Nat.mod_eq_of_lt hjlt, Nat.mod_eq_of_lt hllt] using hjmodl

/-- Once the arithmetic base has been chosen, the `n` floors together have
outer measure at least `n` times the measure of the base. -/
theorem nsmul_measure_residueBase_le_floorUnion
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → α} (hf : MeasurePreserving f μ μ)
    {A : Set α} (hA : MeasurableSet A) {n i : ℕ} :
    (n : ENNReal) * μ (residueBase f A n i) ≤
       μ (⋃ j ∈ Finset.range n, (f^[j]) '' residueBase f A n i) := by
  classical
  let E : ℕ → Set α := fun j => (f^[j]) '' residueBase f A n i
  let S : ℕ → Set α := fun j => floorContainer f A n i j
  have hsmall (j : ℕ) (hj : j ∈ Finset.range n) :
      μ (residueBase f A n i) ≤ μ (E j) := by
    exact measure_mono_image_iterate μ hf _ _
  calc
    (n : ENNReal) * μ (residueBase f A n i) =
        ∑ j ∈ Finset.range n, μ (residueBase f A n i) := by simp
    _ ≤ ∑ j ∈ Finset.range n, μ (E j) :=
      Finset.sum_le_sum (fun j hj => hsmall j hj)
    _ ≤ μ (⋃ j ∈ Finset.range n, E j) :=
      sum_measure_le_biUnion_of_containers μ _ E S
        (fun j hj => image_residue_subset_floorContainer (Finset.mem_range.mp hj))
        (fun j hj => measurable_floorContainer f A hf.measurable hA n i j)
        (pairwiseDisjoint_floorContainer)
    _ = μ (⋃ j ∈ Finset.range n, (f^[j]) '' residueBase f A n i) := rfl

end RokhlinSupport

-- END INLINED FILE: Mathlib/Support/rokhlin_lemma_923ee2bc80/Pieces.lean

-- BEGIN INLINED FILE: Mathlib/Support/rokhlin_lemma_923ee2bc80/High.lean
set_option maxHeartbeats 1000000

open MeasureTheory Set Function
namespace RokhlinSupport
variable {α : Type*}

/-- Finite-hit basin. -/
def finiteHit (f : α → α) (A : Set α) : Set α := ⋃ k : ℕ, hitLevel f A k

/-- The level convention still covers exactly the points which hit the section
in finite forward time. -/
lemma finiteHit_eq_iUnion_preimage (f : α → α) (A : Set α) :
    finiteHit f A = ⋃ k : ℕ, (f^[k]) ⁻¹' A := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨k,hk⟩
    exact Set.mem_iUnion.2 ⟨k, (mem_hitLevel_iff.mp hk).1⟩
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨k,hk⟩
    let P : ℕ → Prop := fun j => f^[j] x ∈ A
    have hex : ∃ j, P j := ⟨k,hk⟩
    let r := Nat.find hex
    have hr0 : f^[r] x ∈ A := Nat.find_spec hex
    have hrlt : ∀ j < r, f^[j] x ∉ A := by
      intro j hj hjmem
      exact (Nat.not_le_of_lt hj) (Nat.find_min' hex hjmem)
    exact Set.mem_iUnion.2 ⟨r, mem_hitLevel_iff.mpr ⟨hr0,hrlt⟩⟩

lemma measurable_finiteHit [MeasurableSpace α] {f : α → α} (hf : Measurable f)
    {A : Set α} (hA : MeasurableSet A) : MeasurableSet (finiteHit f A) := by
  exact MeasurableSet.iUnion (measurable_hitLevel hf hA)


def lowHit (f : α → α) (A : Set α) (n : ℕ) : Set α :=
  ⋃ k ∈ Finset.range n, hitLevel f A k

def highHit (f : α → α) (A : Set α) (n : ℕ) : Set α :=
  ⋃ i ∈ Finset.range n, residueBase f A n i

lemma finiteHit_subset_low_union_high {f : α → α} {A : Set α}
    {n : ℕ} (hn : 0 < n) :
    finiteHit f A ⊆ lowHit f A n ∪ highHit f A n := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨k,hk⟩
  by_cases h : k < n
  · left
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨Finset.mem_range.mpr h, hk⟩⟩
  · right
    have hkN : n ≤ k := Nat.le_of_not_gt h
    have hmod : k % n < n := Nat.mod_lt _ hn
    exact Set.mem_iUnion.2 ⟨k % n, Set.mem_iUnion.2
      ⟨Finset.mem_range.mpr hmod, mem_residueBase.mpr ⟨k,hkN,rfl,hk⟩⟩⟩

lemma measure_lowHit_le [MeasurableSpace α]
    (μ : Measure α) {f : α → α} (hf : MeasurePreserving f μ μ)
    {A : Set α} (n : ℕ) :
    μ (lowHit f A n) ≤ (n : ENNReal) * μ A := by
  classical
  calc
    μ (lowHit f A n) ≤ ∑ k ∈ Finset.range n, μ (hitLevel f A k) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range n, μ A := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hsub : hitLevel f A k ⊆ (f^[k]) ⁻¹' A := diff_subset
      calc
        μ (hitLevel f A k) ≤ μ ((f^[k]) ⁻¹' A) := measure_mono hsub
        _ ≤ μ A := by
          obtain ⟨u, hu, hum, hEq⟩ := exists_measurable_superset μ A
          calc
            μ ((f^[k]) ⁻¹' A) ≤ μ ((f^[k]) ⁻¹' u) := measure_mono (preimage_mono hu)
            _ = μ u := (hf.iterate k).measure_preimage hum.nullMeasurableSet
            _ = μ A := hEq
    _ = (n : ENNReal) * μ A := by simp

/-- Pigeonhole a residue with the largest high-level base. -/
lemma exists_residue_large [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → α} (hf : MeasurePreserving f μ μ)
    {A : Set α} {n : ℕ} (hn : 0 < n)
    (hfull : μ (finiteHit f A) = 1) :
    ∃ i < n, 1 - (n : ENNReal) * μ A ≤
        (n : ENNReal) * μ (residueBase f A n i) := by
  classical
  have hall : (1 : ENNReal) ≤ μ (lowHit f A n) + μ (highHit f A n) := by
    calc
      (1 : ENNReal) = μ (finiteHit f A) := hfull.symm
      _ ≤ μ (lowHit f A n ∪ highHit f A n) :=
        measure_mono (finiteHit_subset_low_union_high hn)
      _ ≤ μ (lowHit f A n) + μ (highHit f A n) := measure_union_le _ _
  have hh : (1 : ENNReal) - (n : ENNReal) * μ A ≤ μ (highHit f A n) := by
    apply tsub_le_iff_left.mpr
    calc
      (1 : ENNReal) ≤ μ (lowHit f A n) + μ (highHit f A n) := hall
      _ ≤ (n : ENNReal) * μ A + μ (highHit f A n) := by
        simpa [add_comm] using
          (add_le_add_right (measure_lowHit_le μ (f:=f) hf (A:=A) n) (μ (highHit f A n)))
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image (Finset.range n)
    (fun i => μ (residueBase f A n i))
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn))
  refine ⟨i, Finset.mem_range.mp hi, ?_⟩
  calc
    (1 : ENNReal) - (n : ENNReal) * μ A ≤ μ (highHit f A n) := hh
    _ ≤ ∑ j ∈ Finset.range n, μ (residueBase f A n j) :=
      measure_biUnion_finset_le _ _
    _ ≤ (Finset.range n).card • μ (residueBase f A n i) :=
      Finset.sum_le_card_nsmul _ _ _ himax
    _ = (n : ENNReal) * μ (residueBase f A n i) := by simp [nsmul_eq_mul]

end RokhlinSupport

namespace RokhlinSupport
open Set MeasureTheory Function
variable {α : Type*}

/-- Before invoking a complete-section argument it is convenient to know the
almost invariant piece swept by an arbitrary section. -/
lemma preimage_iUnion_preimage_subset (f : α → α) (A : Set α) :
    f ⁻¹' (⋃ k : ℕ, (f^[k]) ⁻¹' A) ⊆ (⋃ k : ℕ, (f^[k]) ⁻¹' A) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨k,hk⟩
  apply Set.mem_iUnion.2
  refine ⟨k+1, ?_⟩
  simpa [Function.iterate_succ_apply'] using hk


end RokhlinSupport

-- END INLINED FILE: Mathlib/Support/rokhlin_lemma_923ee2bc80/High.lean

-- BEGIN INLINED FILE: Mathlib/Support/rokhlin_lemma_923ee2bc80/Marker.lean

open MeasureTheory Set Function
open scoped ENNReal NNReal Topology

namespace RokhlinSupport
variable {α : Type*}

/-- forward basin of a set -/
def basin (f : α → α) (s : Set α) : Set α := ⋃ k : ℕ, (f^[k]) ⁻¹' s

lemma measurable_basin [MeasurableSpace α] {f : α → α} (hf : Measurable f)
    {s : Set α} (hs : MeasurableSet s) : MeasurableSet (basin f s) := by
  unfold basin
  exact MeasurableSet.iUnion (fun k => hs.preimage (hf.iterate k))

lemma subset_basin (f : α → α) (s : Set α) : s ⊆ basin f s := by
  intro x hx
  unfold basin
  exact Set.mem_iUnion.2 ⟨0, by simpa using hx⟩

lemma preimage_basin_subset (f : α → α) (s : Set α) : f ⁻¹' (basin f s) ⊆ basin f s := by
  intro x hx
  unfold basin at hx ⊢
  rcases Set.mem_iUnion.1 hx with ⟨k, hk⟩
  apply Set.mem_iUnion.2
  refine ⟨k+1, ?_⟩
  -- iterates
  simpa [Function.iterate_succ_apply'] using hk

lemma preimage_iterate_basin_subset (f : α → α) (s : Set α) (k:ℕ) :
    (f^[k]) ⁻¹' (basin f s) ⊆ basin f s := by
  intro x hx
  unfold basin at hx ⊢
  rcases Set.mem_iUnion.1 hx with ⟨j,hj⟩
  refine Set.mem_iUnion.2 ⟨j+k, ?_⟩
  simpa [Function.iterate_add_apply] using hj

lemma basin_mono (f : α → α) {s t : Set α} (h : s ⊆ t) : basin f s ⊆ basin f t := by
  unfold basin
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨k,hk⟩
  refine Set.mem_iUnion.2 ⟨k, h hk⟩

lemma basin_iUnion (f : α → α) (a : ℕ → Set α) :
    basin f (⋃ r, a r) = ⋃ r, basin f (a r) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨k,hk⟩
    rcases Set.mem_iUnion.1 hk with ⟨r,hr⟩
    refine Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨k, hr⟩⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨r,hr⟩
    rcases Set.mem_iUnion.1 hr with ⟨k,hk⟩
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨r, hk⟩⟩

/-- a seed cut from a cylinder; it cannot return to the same cylinder for `m` steps. -/
def spacedSeed (f : α → α) (U : Set α) (m : ℕ) : Set α :=
  U \ ⋃ j ∈ Finset.range m, (f^[j+1]) ⁻¹' U

lemma measurable_spacedSeed [MeasurableSpace α] {f : α → α} (hf : Measurable f)
    {U : Set α} (hU : MeasurableSet U) (m:ℕ) : MeasurableSet (spacedSeed f U m) := by
  classical
  unfold spacedSeed
  refine hU.diff ?_
  exact Finset.measurableSet_biUnion _ (fun j hj => hU.preimage (hf.iterate (j+1)))

lemma mem_spacedSeed {f : α → α} {U : Set α} {m : ℕ} {x : α} :
    x ∈ spacedSeed f U m ↔ x ∈ U ∧ ∀ d, 0 < d → d ≤ m → f^[d] x ∉ U := by
  classical
  constructor
  · intro h
    have hU : x ∈ U := h.1
    have hn := h.2
    refine ⟨hU, ?_⟩
    intro d hd0 hdm hin
    have hd : d-1 < m := by
      have : d ≤ m := hdm
      omega
    have hxun : x ∈ ⋃ j ∈ Finset.range m, (f^[j+1]) ⁻¹' U := by
      apply Set.mem_iUnion.2
      refine ⟨d-1, Set.mem_iUnion.2 ?_⟩
      refine ⟨(Finset.mem_range.mpr hd), ?_⟩
      have : d - 1 + 1 = d := by omega
      simpa [this] using hin
    exact hn hxun
  · rintro ⟨hu, havoid⟩
    refine ⟨hu, ?_⟩
    intro hx
    rcases Set.mem_iUnion.1 hx with ⟨j,hj⟩
    rcases Set.mem_iUnion.1 hj with ⟨hjr,hjx⟩
    have hjlt : j < m := Finset.mem_range.mp hjr
    exact havoid (j+1) (by omega) (by omega) hjx

/-- first `m+1` pullbacks of a seed are pairwise disjoint. -/
lemma spacedSeed_disjoint_preimages {f : α → α} {U : Set α} (m : ℕ) :
    (↑(Finset.range (m+1)) : Set ℕ).PairwiseDisjoint
      (fun j => (f^[j]) ⁻¹' (spacedSeed f U m)) := by
  classical
  intro i hi j hj hne
  have hil : i < m+1 := Finset.mem_range.mp hi
  have hjl : j < m+1 := Finset.mem_range.mp hj
  apply Set.disjoint_left.2
  intro x hxi hxj
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- j? hne : i ≠ j ; so lt gives i < j
    have hiS := (mem_spacedSeed.mp hxi)
    -- wait hxi : x ∈ (f^[i])⁻¹' seed, so iterate
    change f^[i] x ∈ spacedSeed f U m at hxi
    change f^[j] x ∈ spacedSeed f U m at hxj
    rcases mem_spacedSeed.mp hxi with ⟨hiu, hiavoid⟩
    have hju := (mem_spacedSeed.mp hxj).1
    have hpos : 0 < j-i := Nat.sub_pos_of_lt hlt
    have hle : j-i ≤ m := by omega
    have : f^[j-i] (f^[i] x) ∈ U := by
      have heqval : f^[j-i] (f^[i] x) = f^[j] x := by
        calc
          f^[j-i] (f^[i] x) = f^[(j-i)+i] x :=
            (Function.iterate_add_apply f (j-i) i x).symm
          _ = f^[j] x := by rw [Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      rw [heqval]
      exact hju
    exact (hiavoid (j-i) hpos hle this)
  · -- j < i
    have hlt : j < i := hgt
    change f^[i] x ∈ spacedSeed f U m at hxi
    change f^[j] x ∈ spacedSeed f U m at hxj
    rcases mem_spacedSeed.mp hxj with ⟨hju, hjavoid⟩
    have hiu := (mem_spacedSeed.mp hxi).1
    have hpos : 0 < i-j := Nat.sub_pos_of_lt hlt
    have hle : i-j ≤ m := by omega
    have : f^[i-j] (f^[j] x) ∈ U := by
      have heqval : f^[i-j] (f^[j] x) = f^[i] x := by
        calc
          f^[i-j] (f^[j] x) = f^[(i-j)+j] x :=
            (Function.iterate_add_apply f (i-j) j x).symm
          _ = f^[i] x := by rw [Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      rw [heqval]
      exact hiu
    exact (hjavoid (i-j) hpos hle this)

/-- Countably many Borel seeds cover every nonperiodic point. We use a Polish
upgrade and a countable topological basis. -/
theorem exists_spacedSeed_family
    [MeasurableSpace α] [StandardBorelSpace α]
    {f : α → α} (hf : Measurable f) (m : ℕ) :
    ∃ C : ℕ → Set α,
      (∀ r, MeasurableSet (C r)) ∧
      (∀ r, (↑(Finset.range (m+1)) : Set ℕ).PairwiseDisjoint
          (fun j => (f^[j]) ⁻¹' (C r))) ∧
      {x : α | x ∉ Function.periodicPts f} ⊆ ⋃ r, C r := by
  classical
  letI := upgradeStandardBorel α
  let b : ℕ → Set α := (TopologicalSpace.exists_seq_basis α).choose
  have hb : TopologicalSpace.IsTopologicalBasis (Set.range b) :=
    (TopologicalSpace.exists_seq_basis α).choose_spec
  refine ⟨fun r => spacedSeed f (b r) m, ?_, ?_, ?_⟩
  · intro r
    apply measurable_spacedSeed hf
    exact (hb.isOpen (Set.mem_range_self r)).measurableSet
  · intro r
    exact spacedSeed_disjoint_preimages m
  · intro x hx
    -- choose an open neighbourhood of x avoiding the first m other iterates
    have hneq : ∀ d, 0 < d → d ≤ m → f^[d] x ≠ x := by
      intro d hd hdm heq
      exact hx ⟨d, hd, heq⟩
    let bad : Finset (Set α) := (Finset.range m).image (fun j => ({f^[j+1] x} : Set α))
    -- easier use open finite intersection
    let O : Set α := ⋂ j ∈ Finset.range m, ({f^[j+1] x} : Set α)ᶜ
    have hopen : IsOpen O := by
      -- finite intersections of open complements of singleton
      exact isOpen_biInter_finset (fun j hj => isOpen_compl_singleton)
    have hxO : x ∈ O := by
      classical
      refine Set.mem_iInter.2 ?_
      intro j
      refine Set.mem_iInter.2 ?_
      intro hj
      change x ≠ f^[j+1] x
      have hjlt : j < m := Finset.mem_range.mp hj
      have hne := hneq (j+1) (by omega) (by omega)
      exact Ne.symm hne
    obtain ⟨V,hVb,hxV,hVO⟩ := hb.exists_subset_of_mem_open hxO hopen
    rcases hVb with ⟨r, rfl⟩
    apply Set.mem_iUnion.2
    refine ⟨r, (mem_spacedSeed.mpr ?_)⟩
    refine ⟨hxV, ?_⟩
    intro d hd hdm hmem
    have hj : d-1 < m := by omega
    have hxnot : f^[d] x ∉ O := by
      intro ho
      have h1 := Set.mem_iInter.1 ho (d-1)
      have h2 := Set.mem_iInter.1 h1 (Finset.mem_range.mpr hj)
      change f^[d] x ≠ f^[(d-1)+1] x at h2
      have he : d-1+1 = d := by omega
      exact h2 (by rw [he])
    exact hxnot (hVO hmem)

end RokhlinSupport

namespace RokhlinSupport
open MeasureTheory Set Function
variable {α : Type*}

/-- Greedy cover at stage `r`; at the next stage we put the basin of the part
of the `r`-th seed outside the previous cover. -/
def greedyCover (f : α → α) (C : ℕ → Set α) : ℕ → Set α
| 0 => ∅
| r+1 => greedyCover f C r ∪ basin f (C r \ greedyCover f C r)

def greedyPick (f : α → α) (C : ℕ → Set α) (r : ℕ) : Set α :=
  C r \ greedyCover f C r

def greedyGain (f : α → α) (C : ℕ → Set α) (r : ℕ) : Set α :=
  basin f (greedyPick f C r) \ greedyCover f C r

@[simp] lemma greedyCover_zero (f : α → α) (C : ℕ → Set α) :
    greedyCover f C 0 = ∅ := rfl
@[simp] lemma greedyCover_succ (f : α → α) (C : ℕ → Set α) (r:ℕ) :
    greedyCover f C (r+1) = greedyCover f C r ∪ basin f (greedyPick f C r) := rfl

lemma measurable_greedyCover [MeasurableSpace α] {f : α → α} (hf : Measurable f)
    {C : ℕ → Set α} (hC : ∀ r, MeasurableSet (C r)) :
    ∀ r, MeasurableSet (greedyCover f C r) := by
  intro r
  induction r with
  | zero => exact MeasurableSet.empty
  | succ r ih =>
    rw [greedyCover_succ]
    exact ih.union (measurable_basin hf ((hC r).diff ih))

lemma measurable_greedyPick [MeasurableSpace α] {f : α → α} (hf : Measurable f)
    {C : ℕ → Set α} (hC : ∀ r, MeasurableSet (C r)) (r:ℕ) :
    MeasurableSet (greedyPick f C r) :=
  (hC r).diff (measurable_greedyCover hf hC r)

lemma measurable_greedyGain [MeasurableSpace α] {f : α → α} (hf : Measurable f)
    {C : ℕ → Set α} (hC : ∀ r, MeasurableSet (C r)) (r:ℕ) :
    MeasurableSet (greedyGain f C r) :=
  (measurable_basin hf (measurable_greedyPick hf hC r)).diff
     (measurable_greedyCover hf hC r)

lemma preimage_greedyCover_subset (f : α → α) (C : ℕ → Set α) (r:ℕ) :
    f ⁻¹' (greedyCover f C r) ⊆ greedyCover f C r := by
  intro x hx
  induction r with
  | zero => exact False.elim hx
  | succ r ih =>
    -- split which side contains f x
    rcases hx with (hx0 | hx1)
    · exact Or.inl (ih hx0)
    · exact Or.inr (preimage_basin_subset f (greedyPick f C r) hx1)

-- monotonicity in the stage
lemma greedyCover_mono (f : α → α) (C : ℕ → Set α) :
    Monotone (greedyCover f C) := by
  apply monotone_nat_of_le_succ
  intro r
  rw [greedyCover_succ]
  exact Set.subset_union_left

lemma greedyPick_subset_basin_cover (f : α → α) (C : ℕ → Set α) (r:ℕ) :
    greedyPick f C r ⊆ greedyCover f C (r+1) := by
  intro x hx
  -- right summand basin
  exact Or.inr (subset_basin f _ hx)

lemma basin_pick_subset_cover_succ (f : α → α) (C : ℕ → Set α) (r:ℕ) :
    basin f (greedyPick f C r) ⊆ greedyCover f C (r+1) := by
  intro x hx; exact Or.inr hx

lemma greedyCover_subset_all (f : α → α) (C : ℕ → Set α) (r:ℕ) :
    greedyCover f C r ⊆ ⋃ l, basin f (greedyPick f C l) := by
  intro x hx
  induction r with
  | zero => exact False.elim hx
  | succ r ih =>
    rcases hx with hxold | hxnew
    · exact ih hxold
    · exact Set.mem_iUnion.2 ⟨r, hxnew⟩

lemma seeds_subset_all_basin (f : α → α) (C : ℕ → Set α) :
    (⋃ r, C r) ⊆ ⋃ r, basin f (greedyPick f C r) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨r, hr⟩
  by_cases hcov : x ∈ greedyCover f C r
  · exact greedyCover_subset_all f C r hcov
  · apply Set.mem_iUnion.2
    refine ⟨r, subset_basin f _ ?_⟩
    exact ⟨hr, hcov⟩

lemma pairwise_greedyPick (f : α → α) (C : ℕ → Set α) :
    Pairwise (Function.onFun Disjoint (greedyPick f C)) := by
  intro i j hne
  have split := lt_or_gt_of_ne hne
  cases split with
  | inl hlt =>
    apply Set.disjoint_left.2
    intro x hxi hxj
    have hsub : greedyPick f C i ⊆ greedyCover f C j :=
      (greedyPick_subset_basin_cover f C i) |>.trans
        (greedyCover_mono f C (Nat.succ_le_of_lt hlt))
    exact hxj.2 (hsub hxi)
  | inr hgt =>
    apply Set.disjoint_left.2
    intro x hxi hxj
    have hsub : greedyPick f C j ⊆ greedyCover f C i :=
      (greedyPick_subset_basin_cover f C j) |>.trans
        (greedyCover_mono f C (Nat.succ_le_of_lt hgt))
    exact hxi.2 (hsub hxj)

lemma pairwise_greedyGain (f : α → α) (C : ℕ → Set α) :
    Pairwise (Function.onFun Disjoint (greedyGain f C)) := by
  intro i j hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply Set.disjoint_left.2
    intro x hxi hxj
    have hic : basin f (greedyPick f C i) ⊆ greedyCover f C j :=
      (basin_pick_subset_cover_succ f C i) |>.trans
        (greedyCover_mono f C (Nat.succ_le_of_lt hlt))
    exact hxj.2 (hic hxi.1)
  · apply Set.disjoint_left.2
    intro x hxi hxj
    have hjc : basin f (greedyPick f C j) ⊆ greedyCover f C i :=
      (basin_pick_subset_cover_succ f C j) |>.trans
        (greedyCover_mono f C (Nat.succ_le_of_lt hgt))
    exact hxi.2 (hjc hxj.1)

/-- escaping from a measurable backward closed set is a null event in a finite
measure preserving system. -/
lemma measure_escape_iterate_zero [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → α} (hf : MeasurePreserving f μ μ)
    {D : Set α} (hD : MeasurableSet D) (hback : f ⁻¹' D ⊆ D)
    (k : ℕ) : μ (D \ (f^[k]) ⁻¹' D) = 0 := by
  have hiter : ∀ q:ℕ, (f^[q]) ⁻¹' D ⊆ D := by
    intro q
    induction q with
    | zero => intro x hx; simpa using hx
    | succ q ih =>
      intro x hx
      apply hback
      have hx' : f x ∈ (f^[q]) ⁻¹' D := by
        simpa [Function.iterate_succ_apply] using hx
      exact ih hx'
  have hsub : (f^[k]) ⁻¹' D ⊆ D := hiter k
  have hpremeas : MeasurableSet ((f^[k]) ⁻¹' D) := hD.preimage (hf.measurable.iterate k)
  rw [measure_diff hsub hpremeas.nullMeasurableSet (measure_ne_top μ _)]
  have heq : μ ((f^[k]) ⁻¹' D) = μ D :=
    (hf.iterate k).measure_preimage hD.nullMeasurableSet
  rw [heq]
  exact tsub_self _

lemma measure_cover_basin_pick_inter_zero [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → α} (hf : MeasurePreserving f μ μ)
    {C : ℕ → Set α} (hC : ∀ r, MeasurableSet (C r)) (r:ℕ) :
    μ (greedyCover f C r ∩ basin f (greedyPick f C r)) = 0 := by
  let D := greedyCover f C r
  have hD : MeasurableSet D := measurable_greedyCover hf.measurable hC r
  have hback : f ⁻¹' D ⊆ D := preimage_greedyCover_subset f C r
  have hnull (k:ℕ) : μ (D \ (f^[k]) ⁻¹' D) = 0 :=
    measure_escape_iterate_zero μ hf hD hback k
  have hallnull : μ (⋃ k:ℕ, (D \ (f^[k]) ⁻¹' D)) = 0 :=
    measure_iUnion_null hnull
  apply measure_mono_null (t := ⋃ k:ℕ, (D \ (f^[k]) ⁻¹' D)) ?_ hallnull
  intro x hx
  rcases hx with ⟨hxD, hxb⟩
  rcases Set.mem_iUnion.1 hxb with ⟨k,hk⟩
  apply Set.mem_iUnion.2
  refine ⟨k, hxD, ?_⟩
  intro hin
  -- f^k x belongs to pick hence outside D
  exact hk.2 hin

lemma measure_gain_eq_basin [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → α} (hf : MeasurePreserving f μ μ)
    {C : ℕ → Set α} (hC : ∀ r, MeasurableSet (C r)) (r:ℕ) :
    μ (greedyGain f C r) = μ (basin f (greedyPick f C r)) := by
  have hn := measure_cover_basin_pick_inter_zero μ hf hC r
  -- remove the null intersection
  have he := measure_diff_null (μ:=μ) (s:=basin f (greedyPick f C r))
        (t:=greedyCover f C r ∩ basin f (greedyPick f C r)) hn
  -- its difference is precisely cutting out the cover
  have hset : basin f (greedyPick f C r) \
        (greedyCover f C r ∩ basin f (greedyPick f C r)) =
        greedyGain f C r := by
    ext x
    simp [greedyGain]
  rw [hset] at he
  exact he

lemma mul_measure_le_basin_of_disjoint [MeasurableSpace α]
    (μ : Measure α) {f : α → α} (hf : MeasurePreserving f μ μ)
    {s : Set α} (hs : MeasurableSet s) (L : ℕ)
    (hd : (↑(Finset.range L) : Set ℕ).PairwiseDisjoint
      (fun j => (f^[j]) ⁻¹' s)) :
    (L : ENNReal) * μ s ≤ μ (basin f s) := by
  classical
  have hu : (⋃ j ∈ Finset.range L, (f^[j]) ⁻¹' s) ⊆ basin f s := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨j,hj⟩
    rcases Set.mem_iUnion.1 hj with ⟨hjr,hjx⟩
    exact Set.mem_iUnion.2 ⟨j, hjx⟩
  calc
    (L : ENNReal) * μ s = ∑ j ∈ Finset.range L, μ ((f^[j]) ⁻¹' s) := by
      simp [(hf.iterate _).measure_preimage hs.nullMeasurableSet]
    _ = μ (⋃ j ∈ Finset.range L, (f^[j]) ⁻¹' s) :=
      (measure_biUnion_finset hd
        (fun j hj => hs.preimage (hf.measurable.iterate j))).symm
    _ ≤ μ (basin f s) := measure_mono hu

end RokhlinSupport

namespace RokhlinSupport
open MeasureTheory Set Function
open scoped ENNReal NNReal Topology
variable {α : Type*}

lemma pairwise_preimage_of_subset {f : α → α} {s t : Set α}
    {L : ℕ} (hst : s ⊆ t)
    (hd : (↑(Finset.range L) : Set ℕ).PairwiseDisjoint
      (fun j => (f^[j]) ⁻¹' t)) :
    (↑(Finset.range L) : Set ℕ).PairwiseDisjoint
      (fun j => (f^[j]) ⁻¹' s) := by
  intro i hi j hj hne
  exact Set.disjoint_of_subset
    (preimage_mono hst) (preimage_mono hst) (hd hi hj hne)

/-- A cheap complete section.  It is not a marker itself: markers from a
countable separating family are used successively on the uncovered invariant
components.  This formulation avoids Borel images and works for a
(non-invertible) measure preserving map. -/
theorem exists_section_inv_succ
    [MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → α} (hf : MeasurePreserving f μ μ)
    (ha : μ (Function.periodicPts f) = 0) (m : ℕ) :
    ∃ A : Set α, MeasurableSet A ∧
      μ A ≤ ((m+1 : ℕ) : ENNReal)⁻¹ ∧ μ (basin f A) = 1 := by
  classical
  obtain ⟨C,hCm,hCd,hCcover⟩ :=
    exists_spacedSeed_family (α:=α) hf.measurable m
  let P : ℕ → Set α := greedyPick f C
  let G : ℕ → Set α := greedyGain f C
  have hPm (r:ℕ) : MeasurableSet (P r) :=
    measurable_greedyPick hf.measurable hCm r
  have hGm (r:ℕ) : MeasurableSet (G r) :=
    measurable_greedyGain hf.measurable hCm r
  have hPd : Pairwise (Function.onFun Disjoint P) :=
    pairwise_greedyPick f C
  have hGd : Pairwise (Function.onFun Disjoint G) :=
    pairwise_greedyGain f C
  have hr (r:ℕ) : ((m+1:ℕ) : ENNReal) * μ (P r) ≤ μ (G r) := by
    have hsub : P r ⊆ C r := by intro x hx; exact hx.1
    have hpre := pairwise_preimage_of_subset (f:=f) (L:=m+1)
        hsub (hCd r)
    have h0 := mul_measure_le_basin_of_disjoint μ hf (hPm r) (m+1) hpre
    have heq := measure_gain_eq_basin μ hf hCm r
    rw [heq]
    exact h0
  let A : Set α := ⋃ r, P r
  have hAm : MeasurableSet A := MeasurableSet.iUnion hPm
  have hAeq : μ A = ∑' r, μ (P r) :=
    measure_iUnion hPd hPm
  have hGeq : μ (⋃ r, G r) = ∑' r, μ (G r) :=
    measure_iUnion hGd hGm
  have hGle : (∑' r, μ (G r)) ≤ (1 : ENNReal) := by
    rw [← hGeq]
    calc
      μ (⋃ r, G r) ≤ μ (Set.univ : Set α) := measure_mono (by intro x hx; trivial)
      _ = 1 := measure_univ
  have hprod : ((m+1:ℕ) : ENNReal) * μ A ≤ (1 : ENNReal) := by
    rw [hAeq]
    calc
      ((m+1:ℕ) : ENNReal) * (∑' r, μ (P r)) =
          ∑' r, ((m+1:ℕ) : ENNReal) * μ (P r) := by
            rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' r, μ (G r) := ENNReal.tsum_le_tsum hr
      _ ≤ 1 := hGle
  have hsmall : μ A ≤ ((m+1:ℕ) : ENNReal)⁻¹ := by
    apply (ENNReal.le_inv_iff_mul_le).2
    simpa [mul_comm] using hprod
  have hAcov : {x : α | x ∉ Function.periodicPts f} ⊆ basin f A := by
    intro x hx
    have hxC : x ∈ ⋃ r, C r := hCcover hx
    have hxB : x ∈ ⋃ r, basin f (greedyPick f C r) :=
      seeds_subset_all_basin f C hxC
    rw [basin_iUnion]
    exact hxB
  have hfull : μ (basin f A) = 1 := by
    apply le_antisymm
    · -- upper
      have hh : μ (basin f A) ≤ μ (Set.univ : Set α) :=
        measure_mono (by intro x hx; trivial)
      simpa using hh
    · -- the complement is contained in the periodic set, which is null
      have hsub : (Set.univ : Set α) ⊆ Function.periodicPts f ∪ basin f A := by
        intro x hx
        by_cases hp : x ∈ Function.periodicPts f
        · exact Or.inl hp
        · exact Or.inr (hAcov hp)
      have hle : (1:ENNReal) ≤ μ (Function.periodicPts f ∪ basin f A) := by
        have hh : μ (Set.univ : Set α) ≤ μ (Function.periodicPts f ∪ basin f A) :=
          measure_mono hsub
        simpa using hh
      have hu := measure_union_le (μ:=μ)
          (s:=Function.periodicPts f) (t:=basin f A)
      calc
        (1:ENNReal) ≤ μ (Function.periodicPts f ∪ basin f A) := hle
        _ ≤ μ (Function.periodicPts f) + μ (basin f A) := hu
        _ = μ (basin f A) := by simp [ha]
  exact ⟨A, hAm, hsmall, hfull⟩

end RokhlinSupport

namespace RokhlinSupport
open MeasureTheory Set Function
open scoped ENNReal NNReal
variable {α : Type*}

/-- Arbitrarily small measurable section with full forward basin. -/
theorem exists_small_complete_section
    [MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → α} (hf : MeasurePreserving f μ μ)
    (ha : μ (Function.periodicPts f) = 0)
    {δ : ENNReal} (hδ : 0 < δ) :
    ∃ A : Set α, MeasurableSet A ∧ μ A ≤ δ ∧
      μ (⋃ k : ℕ, (f^[k]) ⁻¹' A) = 1 := by
  obtain ⟨N,hNlt⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hδ)
  have hNpos : 0 < N := by
    by_contra h
    have e : N = 0 := Nat.eq_zero_of_not_pos h
    subst N
    simp at hNlt
  let m : ℕ := N-1
  have hm : m+1 = N := by dsimp [m]; omega
  obtain ⟨A,hAm,hAs,hfull⟩ := exists_section_inv_succ μ hf ha m
  refine ⟨A, hAm, ?_, ?_⟩
  · have hle : μ A ≤ ((N:ℕ) : ENNReal)⁻¹ := by simpa [hm] using hAs
    exact hle.trans (le_of_lt hNlt)
  · simpa [basin] using hfull

end RokhlinSupport

-- END INLINED FILE: Mathlib/Support/rokhlin_lemma_923ee2bc80/Marker.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval
namespace Dynamics

/-!
# Rokhlin lemma (Rokhlin 1947; independently Kakutani 1943)

§109 of Knill's *Some Fundamental Theorems in Mathematics*. Every
aperiodic measure-preserving automorphism of a standard Borel
probability space admits, for every height `n` and every `ε > 0`, a
measurable tower base `B` such that `B, T B, …, T^{n−1} B` are pairwise
disjoint and their union has measure at least `1 − ε`.

Mathlib has `MeasurePreserving`, `IsProbabilityMeasure`, periodic-point
infrastructure (`Function.periodicPts`), `Set.PairwiseDisjoint`, and
`StandardBorelSpace`, but no Rokhlin lemma (`grep -ri 'rokhlin'
Mathlib/Dynamics/` finds nothing; the only `tower` hits are
`IsScalarTower`). The Challenge ships four small helper definitions
(`IsAperiodic`, `towerFloor`, `towerUnion`, `IsRokhlinTower`).

The `[StandardBorelSpace Ω]` hypothesis is essential: the
countable-cocountable σ-algebra on `ℝ` with the integer-shift map
`x ↦ x + 1` is aperiodic and measure-preserving (for the 0/1 measure
that sends countable sets to 0 and cocountable sets to 1), but admits
no nontrivial Rokhlin towers — every cocountable base intersects its
own shift, and every countable base has zero-measure tower. The
countable-cocountable σ-algebra has `MeasurableSingletonClass` but is
strictly coarser than the Borel σ-algebra of any Polish topology on
`ℝ`, hence not standard Borel.
-/

open MeasureTheory Set

/-- `T : Ω → Ω` is **aperiodic** w.r.t. `μ` if the set of periodic
points has measure zero, i.e. for a.e. `x`, no positive iterate of `T`
fixes `x`. -/
def IsAperiodic {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → Ω) (μ : Measure Ω) : Prop :=
  μ (Function.periodicPts T) = 0

/-- The level-`k` floor of a Rokhlin tower of base `B`: the image
`T^[k] '' B`. -/
def towerFloor {Ω : Type*} (T : Ω → Ω) (B : Set Ω) (k : ℕ) : Set Ω :=
  T^[k] '' B

/-- The set-theoretic union of a Rokhlin tower of base `B` and height
`n`. -/
def towerUnion {Ω : Type*} (T : Ω → Ω) (B : Set Ω) (n : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range n, towerFloor T B k

/-- The base `B` is a **Rokhlin tower of height `n`** for `T` if the
floors `B, T B, …, T^{n−1} B` are measurable and pairwise disjoint. -/
def IsRokhlinTower {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → Ω) (B : Set Ω) (n : ℕ) : Prop :=
  MeasurableSet B ∧
    (Finset.range n : Set ℕ).PairwiseDisjoint (towerFloor T B)



end Dynamics
end LeanEval

open LeanEval.Dynamics
open MeasureTheory Set
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem rokhlin_lemma {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (_hT : MeasurePreserving T μ μ) (_hap : IsAperiodic T μ)
    (n : ℕ) (_hn : 1 ≤ n) {ε : ENNReal} (_hε : 0 < ε) :
    ∃ B : Set Ω, IsRokhlinTower T B n ∧
      μ (towerUnion T B n) ≥ 1 - ε :=
/-ResultProofBegin-/by
  by_cases hn1 : n = 1
  · subst n
    refine ⟨Set.univ, ?_, ?_⟩
    · refine ⟨MeasurableSet.univ, ?_⟩
      -- singleton range has no distinct indices
      intro i hi j hj hij
      have hi' : i = 0 := by simpa using hi
      have hj' : j = 0 := by simpa using hj
      exact (hij (hi'.trans hj'.symm)).elim
    · simp [towerUnion, towerFloor]
  · by_cases he : (1:ENNReal) ≤ ε
    · refine ⟨∅, ?_, ?_⟩
      · refine ⟨MeasurableSet.empty, ?_⟩
        intro i hi j hj hij
        change Disjoint (Set.image _ (∅ : Set Ω)) (Set.image _ (∅ : Set Ω))
        simp
      · have he' : (1:ENNReal) - ε = 0 := tsub_eq_zero_of_le he
        simp [towerUnion, towerFloor, he']
    · -- the actual marker input: an arbitrarily small sweep-out section
      have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one _hn
      obtain ⟨A, hAm, hAsmall, hApre⟩ : ∃ A : Set Ω, MeasurableSet A ∧
          μ A ≤ ε / (n : ENNReal) ∧
          μ (⋃ k : ℕ, (T^[k]) ⁻¹' A) = 1 := by
        have hδ : 0 < ε / (n : ENNReal) :=
          ENNReal.div_pos (ne_of_gt _hε) (by simp)
        exact RokhlinSupport.exists_small_complete_section μ _hT _hap hδ
      have hAbasin : μ (RokhlinSupport.finiteHit T A) = 1 := by
        simpa [RokhlinSupport.finiteHit_eq_iUnion_preimage] using hApre
      obtain ⟨i, hi, hlarge⟩ :=
        RokhlinSupport.exists_residue_large μ _hT hnpos hAbasin
      let B : Set Ω := RokhlinSupport.residueBase T A n i
      refine ⟨B, ?_, ?_⟩
      · refine ⟨RokhlinSupport.measurable_residueBase _hT.measurable hAm n i, ?_⟩
        exact RokhlinSupport.pairwiseDisjoint_images_residueBase hnpos
      · have hmul : (n : ENNReal) * μ A ≤ ε := by
          have := ENNReal.mul_le_of_le_div hAsmall
          simpa [mul_comm] using this
        have hstep : 1 - ε ≤ (n : ENNReal) * μ B :=
          calc
            1 - ε ≤ 1 - (n : ENNReal) * μ A := tsub_le_tsub_left hmul 1
            _ ≤ (n : ENNReal) * μ B := hlarge
        have htower : (n : ENNReal) * μ B ≤ μ (towerUnion T B n) := by
          simpa [towerUnion, towerFloor, B] using
            (RokhlinSupport.nsmul_measure_residueBase_le_floorUnion μ _hT hAm (n:=n) (i:=i))
        exact hstep.trans htower/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
