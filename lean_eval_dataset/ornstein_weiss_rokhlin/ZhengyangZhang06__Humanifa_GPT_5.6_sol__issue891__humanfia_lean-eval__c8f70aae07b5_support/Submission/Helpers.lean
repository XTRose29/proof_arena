import ChallengeDeps

open LeanEval.Dynamics
open MeasureTheory Set

namespace Submission.Helpers

open MeasurableSpace

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
  (T : (Fin d → ℤ) → Ω → Ω)
  (hid : ∀ x, T 0 x = x)
  (hT : ∀ v, MeasurePreserving (T v) μ μ)
  (hgrp : ∀ u v x, T (u + v) x = T u (T v x))

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
include hid hgrp in
private lemma left_inverse (v : Fin d → ℤ) :
    Function.LeftInverse (T (-v)) (T v) := by
  intro x
  rw [← hgrp]
  simpa using hid x

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
include hid hgrp in
private lemma right_inverse (v : Fin d → ℤ) :
    Function.RightInverse (T (-v)) (T v) := by
  simpa only [Function.RightInverse, neg_neg] using left_inverse T hid hgrp (-v)

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
include hid hgrp in
lemma bijective (v : Fin d → ℤ) : Function.Bijective (T v) :=
  ⟨(left_inverse T hid hgrp v).injective,
    (right_inverse T hid hgrp v).surjective⟩

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
include hid hgrp in
lemma image_eq_preimage_neg (v : Fin d → ℤ) (s : Set Ω) :
    T v '' s = T (-v) ⁻¹' s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_preimage, (left_inverse T hid hgrp v) y] using hy
  · intro hx
    refine ⟨T (-v) x, hx, ?_⟩
    exact (right_inverse T hid hgrp v) x

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
include hid hT hgrp in
lemma measurableSet_image (v : Fin d → ℤ) {s : Set Ω} (hs : MeasurableSet s) :
    MeasurableSet (T v '' s) := by
  rw [image_eq_preimage_neg T hid hgrp]
  exact hs.preimage (hT (-v)).measurable

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
include hid hT hgrp in
lemma measure_image (v : Fin d → ℤ) {s : Set Ω} (hs : MeasurableSet s) :
    μ (T v '' s) = μ s := by
  rw [image_eq_preimage_neg T hid hgrp]
  exact (hT (-v)).measure_preimage hs.nullMeasurableSet

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
include hgrp in
lemma image_image (u v : Fin d → ℤ) (s : Set Ω) :
    T u '' (T v '' s) = T (u + v) '' s := by
  ext x
  simp only [mem_image]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, hgrp u v y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨T v y, ⟨y, hy, rfl⟩, (hgrp u v y).symm⟩

/-- The union of the translates indexed by a finite shape. -/
def tower (S : Finset (Fin d → ℤ)) (B : Set Ω) : Set Ω :=
  ⋃ v ∈ S, T v '' B

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
include hid hT hgrp in
lemma measurableSet_tower (S : Finset (Fin d → ℤ)) {B : Set Ω}
    (hB : MeasurableSet B) : MeasurableSet (tower T S B) := by
  unfold tower
  exact S.measurableSet_biUnion fun v _ =>
    measurableSet_image μ T hid hT hgrp v hB

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
lemma tower_mono_right (S : Finset (Fin d → ℤ)) {A B : Set Ω} (hAB : A ⊆ B) :
    tower T S A ⊆ tower T S B := by
  intro x hx
  simp only [tower, mem_iUnion] at hx ⊢
  obtain ⟨v, hv, y, hy, rfl⟩ := hx
  exact ⟨v, hv, y, hAB hy, rfl⟩

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
lemma tower_subset_tower_of_subset {S R : Finset (Fin d → ℤ)} {B : Set Ω}
    (hSR : S ⊆ R) : tower T S B ⊆ tower T R B := by
  intro x hx
  simp only [tower, mem_iUnion] at hx ⊢
  obtain ⟨v, hv, y, hy, rfl⟩ := hx
  exact ⟨v, hSR hv, y, hy, rfl⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
include hid hT hgrp in
lemma measure_tower_le (S : Finset (Fin d → ℤ)) {B : Set Ω}
    (hB : MeasurableSet B) :
    μ (tower T S B) ≤ S.card * μ B := by
  rw [tower]
  calc
    μ (⋃ v ∈ S, T v '' B) ≤ ∑ v ∈ S, μ (T v '' B) :=
      measure_biUnion_finset_le S _
    _ = S.card * μ B := by
      simp_rw [measure_image μ T hid hT hgrp _ hB]
      simp

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
include hid hT hgrp in
lemma measure_tower_eq (S : Finset (Fin d → ℤ)) {B : Set Ω}
    (hB : MeasurableSet B)
    (hdisj : (S : Set (Fin d → ℤ)).PairwiseDisjoint (fun v => T v '' B)) :
    μ (tower T S B) = S.card * μ B := by
  rw [tower, measure_biUnion_finset hdisj
    (fun v _ => measurableSet_image μ T hid hT hgrp v hB)]
  simp_rw [measure_image μ T hid hT hgrp _ hB]
  simp

omit [StandardBorelSpace Ω] in
include hid hT hgrp in
lemma measureReal_tower_le (S : Finset (Fin d → ℤ)) {B : Set Ω}
    (hB : MeasurableSet B) :
    μ.real (tower T S B) ≤ S.card * μ.real B := by
  simpa [Measure.real] using
    ENNReal.toReal_mono (by finiteness) (measure_tower_le μ T hid hT hgrp S hB)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
include hid hT hgrp in
lemma measureReal_tower_eq (S : Finset (Fin d → ℤ)) {B : Set Ω}
    (hB : MeasurableSet B)
    (hdisj : (S : Set (Fin d → ℤ)).PairwiseDisjoint (fun v => T v '' B)) :
    μ.real (tower T S B) = S.card * μ.real B := by
  have h := congrArg ENNReal.toReal (measure_tower_eq μ T hid hT hgrp S hB hdisj)
  simpa [Measure.real] using h

/-- The conull invariant set on which the action is pointwise free. -/
def freePart (_hfree : IsFreeAction μ T) : Set Ω :=
  {x | ∀ v : Fin d → ℤ, v ≠ 0 → T v x ≠ x}

omit [IsProbabilityMeasure μ] in
include hT in
lemma measurableSet_freePart (hfree : IsFreeAction μ T) :
    MeasurableSet (freePart μ T hfree) := by
  simp only [freePart, setOf_forall]
  exact MeasurableSet.iInter fun v =>
    MeasurableSet.iInter fun _ =>
      (measurableSet_eq_fun (hT v).measurable measurable_id).compl

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
lemma measure_compl_freePart (hfree : IsFreeAction μ T) :
    μ (freePart μ T hfree)ᶜ = 0 := by
  classical
  rw [show (freePart μ T hfree)ᶜ =
      ⋃ v : Fin d → ℤ, ⋃ (_h : v ≠ 0), {x | T v x = x} by
    ext x
    simp [freePart]]
  refine measure_iUnion_null (μ := μ) fun (v : Fin d → ℤ) =>
    measure_iUnion_null (μ := μ) fun (hv : v ≠ 0) => ?_
  exact hfree v hv

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
include hid hgrp in
lemma freePart_invariant (hfree : IsFreeAction μ T) (u : Fin d → ℤ) {x : Ω}
    (hx : x ∈ freePart μ T hfree) : T u x ∈ freePart μ T hfree := by
  intro v hv hfix
  apply hx v hv
  apply (bijective T hid hgrp u).1
  rw [← hgrp]
  rw [← hgrp] at hfix
  simpa [add_comm] using hfix

/-- Finite binary prefixes of a fixed measurable injection form a countable
family of measurable color classes. -/
abbrev PrefixColor := Σ n : ℕ, Fin n → Bool

private noncomputable def binaryPrefix (n : ℕ) (x : Ω) : Fin n → Bool :=
  fun i => mapNatBool Ω x i

private lemma measurable_binaryPrefix (n : ℕ) :
    Measurable (binaryPrefix (Ω := Ω) n) := by
  unfold binaryPrefix
  exact measurable_pi_lambda _ fun _ => (measurable_mapNatBool Ω).eval

private def prefixSet (c : PrefixColor) : Set Ω :=
  {x | binaryPrefix (Ω := Ω) c.1 x = c.2}

private lemma measurableSet_prefixSet (c : PrefixColor) :
    MeasurableSet (prefixSet (Ω := Ω) c) := by
  exact (MeasurableSet.singleton c.2).preimage
    (measurable_binaryPrefix (Ω := Ω) c.1)

/-- A measurable color class made independent for the translations in `D`. -/
private def independentColor (D : Finset (Fin d → ℤ)) (c : PrefixColor) : Set Ω :=
  prefixSet (Ω := Ω) c \
    ⋃ v ∈ D.filter (· ≠ 0), T (-v) ⁻¹' prefixSet (Ω := Ω) c

omit [IsProbabilityMeasure μ] in
include hT in
private lemma measurableSet_independentColor (D : Finset (Fin d → ℤ)) (c : PrefixColor) :
    MeasurableSet (independentColor T D (Ω := Ω) c) := by
  apply (measurableSet_prefixSet (Ω := Ω) c).diff
  exact (D.filter (· ≠ 0)).measurableSet_biUnion fun v _ =>
    (measurableSet_prefixSet (Ω := Ω) c).preimage (hT (-v)).measurable

include hid hgrp in
private lemma independentColor_independent (D : Finset (Fin d → ℤ)) (c : PrefixColor)
    {x y : Ω} (hx : x ∈ independentColor T D (Ω := Ω) c)
    (hy : y ∈ independentColor T D (Ω := Ω) c)
    {v : Fin d → ℤ} (hvD : v ∈ D) (hv0 : v ≠ 0) (hxy : y = T v x) : False := by
  apply hy.2
  simp only [mem_iUnion, mem_preimage]
  refine ⟨v, Finset.mem_filter.2 ⟨hvD, hv0⟩, ?_⟩
  rw [hxy, ← hgrp]
  simpa [hid] using hx.1

omit [IsProbabilityMeasure μ] in
private lemma exists_independentColor (hfree : IsFreeAction μ T)
    (D : Finset (Fin d → ℤ)) {x : Ω} (hx : x ∈ freePart μ T hfree) :
    ∃ c : PrefixColor, x ∈ independentColor T D (Ω := Ω) c := by
  classical
  have hsep (v : Fin d → ℤ) :
      ∃ n : ℕ, v ∈ D.filter (· ≠ 0) →
        mapNatBool Ω x n ≠ mapNatBool Ω (T (-v) x) n := by
    by_cases hv : v ∈ D.filter (· ≠ 0)
    · by_contra h
      push Not at h
      exact hx (-v) (neg_ne_zero.mpr (Finset.mem_filter.1 hv).2)
        (injective_mapNatBool Ω (funext fun n => (h n).2.symm))
    · exact ⟨0, fun hv' => (hv hv').elim⟩
  choose w hw using hsep
  let n := ∑ v ∈ D.filter (· ≠ 0), (w v + 1)
  let c : PrefixColor := ⟨n, binaryPrefix (Ω := Ω) n x⟩
  refine ⟨c, (mem_sdiff x).2 ⟨rfl, ?_⟩⟩
  simp only [mem_iUnion, mem_preimage, not_exists]
  intro v hv
  have hwlt : w v < n := by
    dsimp [n]
    exact (Nat.lt_succ_self (w v)).trans_le
      (Finset.single_le_sum (fun i _ => Nat.zero_le (w i + 1)) hv)
  intro heq
  have := congr_fun heq ⟨w v, hwlt⟩
  exact hw v hv this.symm

private noncomputable def colorSeq : ℕ → PrefixColor :=
  Set.enumerateCountable Set.countable_univ ⟨0, fun i => Fin.elim0 i⟩

private lemma exists_colorSeq_eq (c : PrefixColor) : ∃ n, colorSeq n = c :=
  Set.subset_range_enumerate Set.countable_univ _ (Set.mem_univ c)

/-- The finite difference set `S - S`. -/
def diffShape (S : Finset (Fin d → ℤ)) : Finset (Fin d → ℤ) :=
  S.image₂ (· - ·) S

lemma zero_mem_diffShape {S : Finset (Fin d → ℤ)} (hS : S.Nonempty) :
    0 ∈ diffShape S := by
  obtain ⟨v, hv⟩ := hS
  exact Finset.mem_image₂.2 ⟨v, hv, v, hv, sub_self v⟩

lemma sub_mem_diffShape {S : Finset (Fin d → ℤ)} {u v : Fin d → ℤ}
    (hu : u ∈ S) (hv : v ∈ S) : u - v ∈ diffShape S :=
  Finset.mem_image₂.2 ⟨u, hu, v, hv, rfl⟩

lemma neg_mem_diffShape {S : Finset (Fin d → ℤ)} {v : Fin d → ℤ}
    (hv : v ∈ diffShape S) : -v ∈ diffShape S := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Finset.mem_image₂.1 hv
  exact Finset.mem_image₂.2 ⟨w, hw, u, hu, by simp⟩

private def DIndependent (D : Finset (Fin d → ℤ)) (B : Set Ω) : Prop :=
  ∀ ⦃x⦄, x ∈ B → ∀ ⦃y⦄, y ∈ B → ∀ ⦃v⦄, v ∈ D → v ≠ 0 → y = T v x → False

private noncomputable def greedyAux (A : Set Ω) (D : Finset (Fin d → ℤ)) :
    ℕ → Set Ω
  | 0 => ∅
  | n + 1 =>
      let B := greedyAux A D n
      B ∪ ((A ∩ independentColor T D (colorSeq n)) \ tower T D B)

private lemma greedyAux_mono (A : Set Ω) (D : Finset (Fin d → ℤ)) (n : ℕ) :
    greedyAux T A D n ⊆ greedyAux T A D (n + 1) := by
  intro x hx
  exact Or.inl hx

private lemma greedyAux_mono_nat (A : Set Ω) (D : Finset (Fin d → ℤ))
    {n m : ℕ} (hnm : n ≤ m) :
    greedyAux T A D n ⊆ greedyAux T A D m := by
  induction m, hnm using Nat.le_induction with
  | base => exact Subset.rfl
  | succ m _ ih => exact ih.trans (greedyAux_mono T A D m)

omit [IsProbabilityMeasure μ] in
include hid hT hgrp in
private lemma measurableSet_greedyAux {A : Set Ω} (hA : MeasurableSet A)
    (D : Finset (Fin d → ℤ)) (n : ℕ) :
    MeasurableSet (greedyAux T A D n) := by
  induction n with
  | zero => exact MeasurableSet.empty
  | succ n ih =>
      exact ih.union ((hA.inter (measurableSet_independentColor μ T hT D (colorSeq n))).diff
        (measurableSet_tower μ T hid hT hgrp D ih))

private lemma greedyAux_subset (A : Set Ω) (D : Finset (Fin d → ℤ)) (n : ℕ) :
    greedyAux T A D n ⊆ A := by
  induction n with
  | zero => exact empty_subset A
  | succ n ih =>
      intro x hx
      rcases hx with hx | hx
      · exact ih hx
      · exact hx.1.1

include hid hgrp in
private lemma DIndependent_greedyAux (A : Set Ω) (S : Finset (Fin d → ℤ)) (n : ℕ) :
    DIndependent T (diffShape S) (greedyAux T A (diffShape S) n) := by
  induction n with
  | zero => simp [greedyAux, DIndependent]
  | succ n ih =>
      intro x hx y hy v hvD hv0 hxy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact ih hx hy hvD hv0 hxy
      · apply hy.2
        simp only [tower, mem_iUnion]
        exact ⟨v, hvD, x, hx, hxy.symm⟩
      · apply hx.2
        simp only [tower, mem_iUnion]
        exact ⟨-v, neg_mem_diffShape hvD, y, hy, by
          rw [hxy, ← hgrp]
          simpa using hid x⟩
      · exact independentColor_independent T hid hgrp (diffShape S) (colorSeq n)
          hx.1.2 hy.1.2 hvD hv0 hxy

/-- The measurable maximal packing selected by the countable coloring. -/
noncomputable def packingBase (A : Set Ω) (S : Finset (Fin d → ℤ)) : Set Ω :=
  ⋃ n, greedyAux T A (diffShape S) n

omit [IsProbabilityMeasure μ] in
include hid hT hgrp in
lemma measurableSet_packingBase {A : Set Ω} (hA : MeasurableSet A)
    (S : Finset (Fin d → ℤ)) :
    MeasurableSet (packingBase T A S) :=
  MeasurableSet.iUnion fun n => measurableSet_greedyAux μ T hid hT hgrp hA _ n

lemma packingBase_subset (A : Set Ω) (S : Finset (Fin d → ℤ)) :
    packingBase T A S ⊆ A := by
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.1 hx
  exact greedyAux_subset T A _ n hn

include hid hgrp in
private lemma DIndependent_packingBase (A : Set Ω) (S : Finset (Fin d → ℤ)) :
    DIndependent T (diffShape S) (packingBase T A S) := by
  intro x hx y hy v hvD hv0 hxy
  obtain ⟨n, hxn⟩ := mem_iUnion.1 hx
  obtain ⟨m, hym⟩ := mem_iUnion.1 hy
  let k := max n m
  exact DIndependent_greedyAux T hid hgrp A S k
    (greedyAux_mono_nat T A _ (Nat.le_max_left _ _) hxn)
    (greedyAux_mono_nat T A _ (Nat.le_max_right _ _) hym) hvD hv0 hxy

include hid hgrp in
lemma pairwiseDisjoint_packingBase (A : Set Ω) (S : Finset (Fin d → ℤ)) :
    (S : Set (Fin d → ℤ)).PairwiseDisjoint (fun v => T v '' packingBase T A S) := by
  intro u hu v hv huv
  change Disjoint (T u '' packingBase T A S) (T v '' packingBase T A S)
  rw [Set.disjoint_left]
  intro z hzu hzv
  obtain ⟨x, hx, hzx⟩ := hzu
  obtain ⟨y, hy, hzy⟩ := hzv
  apply DIndependent_packingBase T hid hgrp A S hx hy
    (sub_mem_diffShape hu hv) (sub_ne_zero.2 huv)
  apply (bijective T hid hgrp v).1
  calc
    T v y = z := hzy
    _ = T u x := hzx.symm
    _ = T v (T (u - v) x) := by
      rw [← hgrp]
      congr 1
      simp [sub_eq_add_neg, add_left_comm]

omit [IsProbabilityMeasure μ] in
include hid in
lemma packingBase_maximal (hfree : IsFreeAction μ T) {A : Set Ω}
    (hAfree : A ⊆ freePart μ T hfree) {S : Finset (Fin d → ℤ)} (hS : S.Nonempty) :
    A ⊆ tower T (diffShape S) (packingBase T A S) := by
  intro x hx
  obtain ⟨c, hxc⟩ := exists_independentColor μ T hfree (diffShape S) (hAfree hx)
  obtain ⟨n, hn⟩ := exists_colorSeq_eq c
  have hxcn : x ∈ independentColor T (diffShape S) (colorSeq n) := hn.symm ▸ hxc
  by_cases hconf : x ∈ tower T (diffShape S) (greedyAux T A (diffShape S) n)
  · exact tower_mono_right T _ (fun _ h =>
      mem_iUnion.2 ⟨n, h⟩) hconf
  · have hxnext : x ∈ greedyAux T A (diffShape S) (n + 1) :=
      Or.inr ⟨⟨hx, hxcn⟩, hconf⟩
    simp only [tower, mem_iUnion]
    exact ⟨0, zero_mem_diffShape hS, x, mem_iUnion.2 ⟨n + 1, hxnext⟩, hid x⟩

/-- The symmetric integer cube `[-L,L)ᵈ`. -/
noncomputable def symShape (d L : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Ico (-(L : ℤ)) (L : ℤ)

@[simp] lemma mem_boxShape {L : ℕ} {v : Fin d → ℤ} :
    v ∈ boxShape d L ↔ ∀ i, 0 ≤ v i ∧ v i < L := by
  simp [boxShape, Fintype.mem_piFinset]

@[simp] lemma mem_symShape {L : ℕ} {v : Fin d → ℤ} :
    v ∈ symShape d L ↔ ∀ i, -(L : ℤ) ≤ v i ∧ v i < L := by
  simp [symShape, Fintype.mem_piFinset]

@[simp] lemma card_boxShape (d L : ℕ) : (boxShape d L).card = L ^ d := by
  simp [boxShape, Int.card_Ico]

@[simp] lemma card_symShape (d L : ℕ) : (symShape d L).card = (2 * L) ^ d := by
  have hIco : (Finset.Ico (-(L : ℤ)) (L : ℤ)).card = 2 * L := by
    rw [Int.card_Ico]
    norm_num
    change L + L = 2 * L
    omega
  rw [symShape, Fintype.card_piFinset]
  simp [hIco]

lemma diffShape_box_subset_symShape (L : ℕ) :
    diffShape (boxShape d L) ⊆ symShape d L := by
  intro v hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Finset.mem_image₂.1 hv
  simp only [mem_symShape]
  intro i
  have hui := (mem_boxShape.1 hu i)
  have hwi := (mem_boxShape.1 hw i)
  change -(L : ℤ) ≤ u i - w i ∧ u i - w i < L
  constructor <;> omega

lemma boxShape_nonempty {L : ℕ} (hL : 0 < L) : (boxShape d L).Nonempty := by
  refine ⟨0, mem_boxShape.2 fun i => ?_⟩
  simp [hL]

/-- Points in the free part whose whole `S`-orbit patch lies in `U`. -/
def packingCandidate (hfree : IsFreeAction μ T) (U : Set Ω)
    (S : Finset (Fin d → ℤ)) : Set Ω :=
  freePart μ T hfree ∩ ⋂ v ∈ S, T v ⁻¹' U

omit [IsProbabilityMeasure μ] in
include hT in
lemma measurableSet_packingCandidate (hfree : IsFreeAction μ T) {U : Set Ω}
    (hU : MeasurableSet U) (S : Finset (Fin d → ℤ)) :
    MeasurableSet (packingCandidate μ T hfree U S) := by
  exact (measurableSet_freePart μ T hT hfree).inter
    (S.measurableSet_biInter fun v _ => hU.preimage (hT v).measurable)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] in
lemma packingCandidate_subset_freePart (hfree : IsFreeAction μ T) (U : Set Ω)
    (S : Finset (Fin d → ℤ)) :
    packingCandidate μ T hfree U S ⊆ freePart μ T hfree :=
  inter_subset_left

omit [IsProbabilityMeasure μ] in
lemma tower_packingBase_subset (hfree : IsFreeAction μ T) (U : Set Ω)
    (S : Finset (Fin d → ℤ)) :
    tower T S (packingBase T (packingCandidate μ T hfree U S) S) ⊆ U := by
  intro x hx
  simp only [tower, mem_iUnion] at hx
  obtain ⟨v, hv, y, hy, rfl⟩ := hx
  have hyA := packingBase_subset T _ _ hy
  exact mem_iInter.1 (mem_iInter.1 hyA.2 v) hv

/-- Rapidly separated side lengths. -/
def scale (d M N : ℕ) : ℕ → ℕ
  | 0 => N
  | n + 1 => M * scale d M N n ^ (d + 1)

lemma scale_pos {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (n : ℕ) :
    0 < scale d M N n := by
  induction n with
  | zero => exact hN
  | succ n ih =>
      simp only [scale]
      positivity

lemma scale_dvd_succ (d M N n : ℕ) :
    scale d M N n ∣ scale d M N (n + 1) := by
  rw [scale]
  exact dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _

lemma scale_mono {M N : ℕ} (hM : 0 < M) (_hN : 0 < N) :
    Monotone (scale d M N) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [scale]
  calc
    scale d M N n ≤ scale d M N n ^ (d + 1) := by
      exact Nat.le_pow (by omega)
    _ ≤ M * scale d M N n ^ (d + 1) := by
      exact Nat.le_mul_of_pos_left _ hM

lemma scale_separation {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    {k n j : ℕ} (hj : j < n) (hn : n ≤ k) :
    M * scale d M N (k - n) ^ (d + 1) ≤ scale d M N (k - j) := by
  rw [← scale]
  apply scale_mono (d := d) hM hN
  omega

/-- The union accumulated after the first `n` greedy cube packings. -/
noncomputable def packedUnion (hfree : IsFreeAction μ T) (k M N : ℕ) :
    ℕ → Set Ω
  | 0 => ∅
  | n + 1 =>
      let U := packedUnion hfree k M N n
      let S := boxShape d (scale d M N (k - n))
      let A := packingCandidate μ T hfree Uᶜ S
      U ∪ tower T S (packingBase T A S)

noncomputable def stageShape (k M N n : ℕ) : Finset (Fin d → ℤ) :=
  boxShape d (scale d M N (k - n))

noncomputable def stageCandidate (hfree : IsFreeAction μ T) (k M N n : ℕ) : Set Ω :=
  packingCandidate μ T hfree (packedUnion μ T hfree k M N n)ᶜ
    (stageShape (d := d) k M N n)

noncomputable def stageBase (hfree : IsFreeAction μ T) (k M N n : ℕ) : Set Ω :=
  packingBase T (stageCandidate μ T hfree k M N n) (stageShape (d := d) k M N n)

noncomputable def stageLayer (hfree : IsFreeAction μ T) (k M N n : ℕ) : Set Ω :=
  tower T (stageShape (d := d) k M N n) (stageBase μ T hfree k M N n)

omit [IsProbabilityMeasure μ] in
lemma packedUnion_succ (hfree : IsFreeAction μ T) (k M N n : ℕ) :
    packedUnion μ T hfree k M N (n + 1) =
      packedUnion μ T hfree k M N n ∪ stageLayer μ T hfree k M N n :=
  rfl

omit [IsProbabilityMeasure μ] in
include hid hT hgrp in
lemma measurableSet_packedUnion (hfree : IsFreeAction μ T) (k M N n : ℕ) :
    MeasurableSet (packedUnion μ T hfree k M N n) := by
  induction n with
  | zero => exact MeasurableSet.empty
  | succ n ih =>
      rw [packedUnion_succ]
      apply ih.union
      apply measurableSet_tower μ T hid hT hgrp
      apply measurableSet_packingBase μ T hid hT hgrp
      exact measurableSet_packingCandidate μ T hT hfree ih.compl _

omit [IsProbabilityMeasure μ] in
include hid hT hgrp in
lemma measurableSet_stageCandidate (hfree : IsFreeAction μ T) (k M N n : ℕ) :
    MeasurableSet (stageCandidate μ T hfree k M N n) :=
  measurableSet_packingCandidate μ T hT hfree
    (measurableSet_packedUnion μ T hid hT hgrp hfree k M N n).compl _

omit [IsProbabilityMeasure μ] in
include hid hT hgrp in
lemma measurableSet_stageBase (hfree : IsFreeAction μ T) (k M N n : ℕ) :
    MeasurableSet (stageBase μ T hfree k M N n) :=
  measurableSet_packingBase μ T hid hT hgrp
    (measurableSet_stageCandidate μ T hid hT hgrp hfree k M N n) _

omit [IsProbabilityMeasure μ] in
include hid hT hgrp in
lemma measurableSet_stageLayer (hfree : IsFreeAction μ T) (k M N n : ℕ) :
    MeasurableSet (stageLayer μ T hfree k M N n) :=
  measurableSet_tower μ T hid hT hgrp _
    (measurableSet_stageBase μ T hid hT hgrp hfree k M N n)

omit [IsProbabilityMeasure μ] in
lemma stageLayer_subset_compl (hfree : IsFreeAction μ T) (k M N n : ℕ) :
    stageLayer μ T hfree k M N n ⊆ (packedUnion μ T hfree k M N n)ᶜ :=
  tower_packingBase_subset μ T hfree _ _

omit [IsProbabilityMeasure μ] in
lemma disjoint_packedUnion_stageLayer (hfree : IsFreeAction μ T) (k M N n : ℕ) :
    Disjoint (packedUnion μ T hfree k M N n) (stageLayer μ T hfree k M N n) :=
  Set.disjoint_left.2 fun _ hx hy => stageLayer_subset_compl μ T hfree k M N n hy hx

include hid hT hgrp in
lemma measureReal_packedUnion_succ (hfree : IsFreeAction μ T) (k M N n : ℕ) :
    μ.real (packedUnion μ T hfree k M N (n + 1)) =
      μ.real (packedUnion μ T hfree k M N n) +
        μ.real (stageLayer μ T hfree k M N n) := by
  rw [packedUnion_succ]
  exact measureReal_union (disjoint_packedUnion_stageLayer μ T hfree k M N n)
    (measurableSet_stageLayer μ T hid hT hgrp hfree k M N n)

omit [IsProbabilityMeasure μ] in
lemma packedUnion_mono (hfree : IsFreeAction μ T) (k M N : ℕ) :
    Monotone (packedUnion μ T hfree k M N) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [packedUnion_succ]
  exact subset_union_left

omit [IsProbabilityMeasure μ] in
include hid hgrp in
lemma pairwiseDisjoint_stageBase (hfree : IsFreeAction μ T) (k M N n : ℕ) :
    ((stageShape (d := d) k M N n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)).PairwiseDisjoint
      (fun v => T v '' stageBase μ T hfree k M N n) :=
  pairwiseDisjoint_packingBase T hid hgrp _ _

/-- The lower coordinate boundary of `[0,L)ᵈ` of thickness `l`. -/
noncomputable def lowerBoundary (d l L : ℕ) : Finset (Fin d → ℤ) :=
  (boxShape d L).filter fun v => ∃ i, v i < l

private noncomputable def coordFiber (d L : ℕ) (i : Fin d) (a : ℤ) :
    Finset (Fin d → ℤ) :=
  (boxShape d L).filter fun v => v i = a

private lemma card_coordFiber {L : ℕ} (i : Fin d) {a : ℤ}
    (ha : a ∈ Finset.Ico (0 : ℤ) (L : ℤ)) :
    (coordFiber d L i a).card = L ^ (d - 1) := by
  simpa [coordFiber, boxShape, Int.card_Ico] using
    Fintype.card_filter_piFinset_const_eq_of_mem
      (Finset.Ico (0 : ℤ) (L : ℤ)) i ha

lemma card_lowerBoundary_le {l L : ℕ} (hlL : l ≤ L) :
    (lowerBoundary d l L).card ≤ d * l * L ^ (d - 1) := by
  classical
  let cover : Finset (Fin d → ℤ) :=
    Finset.univ.biUnion fun i =>
      (Finset.Ico (0 : ℤ) (l : ℤ)).biUnion fun a => coordFiber d L i a
  have hsub : lowerBoundary d l L ⊆ cover := by
    intro v hv
    have hvbox := Finset.mem_filter.1 hv
    obtain ⟨i, hi⟩ := hvbox.2
    simp only [cover, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, v i, by
      simpa only [Finset.mem_Ico] using ⟨(mem_boxShape.1 hvbox.1 i).1, hi⟩,
      Finset.mem_filter.2 ⟨hvbox.1, rfl⟩⟩
  calc
    (lowerBoundary d l L).card ≤ cover.card := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin d, ∑ a ∈ Finset.Ico (0 : ℤ) (l : ℤ),
        (coordFiber d L i a).card := by
      unfold cover
      exact Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun i _ => Finset.card_biUnion_le)
    _ = ∑ _i : Fin d, ∑ _a ∈ Finset.Ico (0 : ℤ) (l : ℤ), L ^ (d - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a ha
      apply card_coordFiber
      exact Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 ha).1,
        (Finset.mem_Ico.1 ha).2.trans_le (by exact_mod_cast hlL)⟩
    _ = d * l * L ^ (d - 1) := by
      simp [Int.card_Ico, mul_assoc]

lemma sub_mem_boxShape_or_boundary {l L : ℕ} (_hlL : l ≤ L)
    {q r : Fin d → ℤ} (hq : q ∈ boxShape d l) (hr : r ∈ boxShape d L) :
    r - q ∈ boxShape d L ∨ r ∈ lowerBoundary d l L := by
  by_cases hb : r ∈ lowerBoundary d l L
  · exact Or.inr hb
  · left
    rw [mem_boxShape]
    intro i
    have hqi := mem_boxShape.1 hq i
    have hri := mem_boxShape.1 hr i
    have hli : (l : ℤ) ≤ r i := by
      by_contra h
      apply hb
      exact Finset.mem_filter.2 ⟨hr, ⟨i, by omega⟩⟩
    constructor <;> dsimp <;> omega

/-- Possible translations through which a small positive cube can enter a
larger cube tower from outside. -/
noncomputable def escapeShape (d l L : ℕ) : Finset (Fin d → ℤ) :=
  (lowerBoundary d l L).image₂ (· - ·) (boxShape d l)

lemma card_escapeShape_le {l L : ℕ} (hlL : l ≤ L) :
    (escapeShape d l L).card ≤ d * l ^ (d + 1) * L ^ (d - 1) := by
  calc
    (escapeShape d l L).card
        ≤ (lowerBoundary d l L).card * (boxShape d l).card :=
      Finset.card_image₂_le _ _ _
    _ ≤ (d * l * L ^ (d - 1)) * l ^ d :=
      by simpa using Nat.mul_le_mul_right (l ^ d) (card_lowerBoundary_le (d := d) hlL)
    _ = d * l ^ (d + 1) * L ^ (d - 1) := by ring

omit [StandardBorelSpace Ω] in
include hid hT hgrp in
lemma escape_charge {l L M : ℕ} (hd : 1 ≤ d) (hlL : l ≤ L)
    (hsep : M * l ^ (d + 1) ≤ L) {B : Set Ω} (hB : MeasurableSet B)
    (hdisj : ((boxShape d L : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)).PairwiseDisjoint
      (fun v => T v '' B)) :
    (M : ℝ) * μ.real (tower T (escapeShape d l L) B) ≤
      d * μ.real (tower T (boxShape d L) B) := by
  have hpow : L * L ^ (d - 1) = L ^ d := by
    nth_rewrite 2 [show d = d - 1 + 1 by omega]
    rw [pow_succ]
    ring
  have hcoef :
      M * (d * l ^ (d + 1) * L ^ (d - 1)) ≤ d * L ^ d := by
    calc
      M * (d * l ^ (d + 1) * L ^ (d - 1)) =
          d * (M * l ^ (d + 1)) * L ^ (d - 1) := by ring
      _ ≤ d * L * L ^ (d - 1) := by gcongr
      _ = d * L ^ d := by rw [mul_assoc, hpow]
  have hcard : M * (escapeShape d l L).card ≤ d * L ^ d :=
    (Nat.mul_le_mul_left M (card_escapeShape_le (d := d) hlL)).trans hcoef
  calc
    (M : ℝ) * μ.real (tower T (escapeShape d l L) B)
        ≤ M * ((escapeShape d l L).card * μ.real B) := by
      gcongr
      exact measureReal_tower_le μ T hid hT hgrp _ hB
    _ = (M * (escapeShape d l L).card : ℕ) * μ.real B := by
      push_cast
      ring
    _ ≤ (d * L ^ d : ℕ) * μ.real B := by gcongr
    _ = (d : ℝ) * ((boxShape d L).card * μ.real B) := by
      simp
      ring
    _ = d * μ.real (tower T (boxShape d L) B) := by
      rw [measureReal_tower_eq μ T hid hT hgrp _ hB hdisj]

include hid hT hgrp in
lemma candidate_charge (hfree : IsFreeAction μ T) {U : Set Ω} (hU : MeasurableSet U) {L : ℕ}
    (hL : 0 < L) :
    μ.real (packingCandidate μ T hfree U (boxShape d L)) ≤
      (2 ^ d : ℕ) *
        μ.real
          (tower T (boxShape d L)
            (packingBase T (packingCandidate μ T hfree U (boxShape d L))
              (boxShape d L))) := by
  let A := packingCandidate μ T hfree U (boxShape d L)
  let B := packingBase T A (boxShape d L)
  have hmax : A ⊆ tower T (diffShape (boxShape d L)) B :=
    packingBase_maximal μ T hid hfree
      (packingCandidate_subset_freePart μ T hfree U _) (boxShape_nonempty hL)
  have hdiff :
      tower T (diffShape (boxShape d L)) B ⊆ tower T (symShape d L) B :=
    tower_subset_tower_of_subset T (diffShape_box_subset_symShape (d := d) L)
  have hA : MeasurableSet A :=
    measurableSet_packingCandidate μ T hT hfree hU _
  have hB : MeasurableSet B :=
    measurableSet_packingBase μ T hid hT hgrp hA _
  have hdisj :
      ((boxShape d L : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)).PairwiseDisjoint
        (fun v => T v '' B) :=
    pairwiseDisjoint_packingBase T hid hgrp A _
  change μ.real A ≤ (2 ^ d : ℕ) * μ.real (tower T (boxShape d L) B)
  calc
    μ.real A ≤ μ.real (tower T (diffShape (boxShape d L)) B) :=
      measureReal_mono hmax
    _ ≤ μ.real (tower T (symShape d L) B) :=
      measureReal_mono hdiff
    _ ≤ (symShape d L).card * μ.real B :=
      measureReal_tower_le μ T hid hT hgrp _ hB
    _ = (2 ^ d : ℕ) * ((boxShape d L).card * μ.real B) := by
      simp
      rw [mul_pow]
      ring
    _ = (2 ^ d : ℕ) * μ.real (tower T (boxShape d L) B) := by
      rw [measureReal_tower_eq μ T hid hT hgrp _ hB hdisj]

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
include hid hgrp in
lemma crossing_subset_escape {l L : ℕ} (hlL : l ≤ L) {B : Set Ω} {x : Ω}
    (hx : x ∉ tower T (boxShape d L) B) {q : Fin d → ℤ}
    (hq : q ∈ boxShape d l) (hqx : T q x ∈ tower T (boxShape d L) B) :
    x ∈ tower T (escapeShape d l L) B := by
  simp only [tower, mem_iUnion] at hqx ⊢
  obtain ⟨r, hr, b, hb, hEq⟩ := hqx
  have hrb : r ∈ lowerBoundary d l L := by
    rcases sub_mem_boxShape_or_boundary (d := d) hlL hq hr with hdiff | hboundary
    · apply False.elim
      apply hx
      exact mem_iUnion.2 ⟨r - q, mem_iUnion.2 ⟨hdiff, b, hb, by
        apply (bijective T hid hgrp q).1
        rw [← hEq, ← hgrp]
        congr 1
        simp [sub_eq_add_neg]⟩⟩
    · exact hboundary
  refine ⟨r - q, Finset.mem_image₂.2 ⟨r, hrb, q, hq, rfl⟩, b, hb, ?_⟩
  apply (bijective T hid hgrp q).1
  rw [← hEq, ← hgrp]
  congr 1
  simp [sub_eq_add_neg]

omit [IsProbabilityMeasure μ] in
lemma packedUnion_eq_biUnion_stageLayer (hfree : IsFreeAction μ T) (k M N n : ℕ) :
    packedUnion μ T hfree k M N n =
      ⋃ j ∈ Finset.range n, stageLayer μ T hfree k M N j := by
  induction n with
  | zero => simp [packedUnion]
  | succ n ih =>
      rw [packedUnion_succ, ih, Finset.range_add_one, Finset.set_biUnion_insert,
        union_comm]

include hid hT hgrp in
lemma measureReal_packedUnion_eq_sum (hfree : IsFreeAction μ T) (k M N n : ℕ) :
    μ.real (packedUnion μ T hfree k M N n) =
      ∑ j ∈ Finset.range n, μ.real (stageLayer μ T hfree k M N j) := by
  induction n with
  | zero => simp [packedUnion]
  | succ n ih =>
      rw [measureReal_packedUnion_succ μ T hid hT hgrp hfree k M N n, ih,
        Finset.sum_range_succ]

omit [IsProbabilityMeasure μ] in
include hid hgrp in
lemma complement_candidate_subset (hfree : IsFreeAction μ T) (k M N n : ℕ)
    (hM : 0 < M) (hN : 0 < N) (hnk : n < k) :
    (packedUnion μ T hfree k M N n)ᶜ \
        stageCandidate μ T hfree k M N n ⊆
      (freePart μ T hfree)ᶜ ∪
        ⋃ j ∈ Finset.range n,
          tower T
            (escapeShape d
              (scale d M N (k - n))
              (scale d M N (k - j)))
            (stageBase μ T hfree k M N j) := by
  intro x hx
  rcases hx with ⟨hxU, hxA⟩
  by_cases hxfree : x ∈ freePart μ T hfree
  · right
    have hnotpatch :
        ¬x ∈ ⋂ v ∈ stageShape (d := d) k M N n,
          T v ⁻¹' (packedUnion μ T hfree k M N n)ᶜ := by
      intro hpatch
      exact hxA ⟨hxfree, hpatch⟩
    simp only [mem_iInter, mem_preimage, mem_compl_iff] at hnotpatch
    push Not at hnotpatch
    obtain ⟨q, hqS, hqPacked⟩ := hnotpatch
    have hqPacked' : T q x ∈ packedUnion μ T hfree k M N n := by
      simpa using hqPacked
    rw [packedUnion_eq_biUnion_stageLayer] at hqPacked'
    simp only [mem_iUnion] at hqPacked'
    obtain ⟨j, hjn, hqj⟩ := hqPacked'
    have hjlt : j < n := Finset.mem_range.1 hjn
    have hxj : x ∉ stageLayer μ T hfree k M N j := by
      intro hxj
      apply hxU
      rw [packedUnion_eq_biUnion_stageLayer]
      exact mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hjn, hxj⟩⟩
    have hscale :
        scale d M N (k - n) ≤ scale d M N (k - j) :=
      scale_mono (d := d) hM hN (by omega)
    simp only [mem_iUnion]
    refine ⟨j, hjn, ?_⟩
    exact crossing_subset_escape T hid hgrp hscale hxj hqS hqj
  · exact Or.inl hxfree

include hid hT hgrp in
lemma stageCandidate_charge (hfree : IsFreeAction μ T) (k M N n : ℕ)
    (hM : 0 < M) (hN : 0 < N) :
    μ.real (stageCandidate μ T hfree k M N n) ≤
      (2 ^ d : ℕ) * μ.real (stageLayer μ T hfree k M N n) := by
  simpa [stageCandidate, stageShape, stageLayer, stageBase] using
    candidate_charge μ T hid hT hgrp hfree
      (measurableSet_packedUnion μ T hid hT hgrp hfree k M N n).compl
      (scale_pos (d := d) hM hN (k - n))

include hid hT hgrp in
lemma stageEscape_charge (hfree : IsFreeAction μ T) (hd : 1 ≤ d)
    (k M N : ℕ) (hM : 0 < M) (hN : 0 < N) {j n : ℕ}
    (hj : j < n) (hn : n ≤ k) :
    (M : ℝ) *
        μ.real
          (tower T
            (escapeShape d
              (scale d M N (k - n))
              (scale d M N (k - j)))
            (stageBase μ T hfree k M N j)) ≤
      d * μ.real (stageLayer μ T hfree k M N j) := by
  have hle :
      scale d M N (k - n) ≤ scale d M N (k - j) :=
    scale_mono (d := d) hM hN (by omega)
  apply escape_charge μ T hid hT hgrp hd hle
      (scale_separation (d := d) hM hN hj hn)
      (measurableSet_stageBase μ T hid hT hgrp hfree k M N j)
  simpa [stageShape] using
    pairwiseDisjoint_stageBase μ T hid hgrp hfree k M N j

include hid hT hgrp in
lemma sum_stageEscape_charge (hfree : IsFreeAction μ T) (hd : 1 ≤ d)
    (k M N n : ℕ) (hM : 0 < M) (hN : 0 < N) (hn : n ≤ k) :
    (M : ℝ) *
        ∑ j ∈ Finset.range n,
          μ.real
            (tower T
              (escapeShape d
                (scale d M N (k - n))
                (scale d M N (k - j)))
              (stageBase μ T hfree k M N j)) ≤ d := by
  calc
    (M : ℝ) *
          ∑ j ∈ Finset.range n,
            μ.real
              (tower T
                (escapeShape d
                  (scale d M N (k - n))
                  (scale d M N (k - j)))
                (stageBase μ T hfree k M N j)) =
        ∑ j ∈ Finset.range n,
          (M : ℝ) *
            μ.real
              (tower T
                (escapeShape d
                  (scale d M N (k - n))
                  (scale d M N (k - j)))
                (stageBase μ T hfree k M N j)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range n,
          (d : ℝ) * μ.real (stageLayer μ T hfree k M N j) := by
      exact Finset.sum_le_sum fun j hj =>
        stageEscape_charge μ T hid hT hgrp hfree hd k M N hM hN
          (Finset.mem_range.1 hj) hn
    _ = (d : ℝ) * μ.real (packedUnion μ T hfree k M N n) := by
      rw [measureReal_packedUnion_eq_sum μ T hid hT hgrp hfree k M N n]
      rw [Finset.mul_sum]
    _ ≤ (d : ℝ) * μ.real (Set.univ : Set Ω) := by
      exact mul_le_mul_of_nonneg_left
        (measureReal_mono (μ := μ) (subset_univ _) (by finiteness)) (by positivity)
    _ = d := by simp

include hid hT hgrp in
lemma stageLost_charge (hfree : IsFreeAction μ T) (hd : 1 ≤ d)
    (k M N n : ℕ) (hM : 0 < M) (hN : 0 < N) (hn : n < k) :
    (M : ℝ) *
        μ.real
          ((packedUnion μ T hfree k M N n)ᶜ \
            stageCandidate μ T hfree k M N n) ≤ d := by
  let E : ℕ → Set Ω := fun j =>
    tower T
      (escapeShape d
        (scale d M N (k - n))
        (scale d M N (k - j)))
      (stageBase μ T hfree k M N j)
  have hsubset :
      (packedUnion μ T hfree k M N n)ᶜ \
          stageCandidate μ T hfree k M N n ⊆
        (freePart μ T hfree)ᶜ ∪ ⋃ j ∈ Finset.range n, E j :=
    complement_candidate_subset μ T hid hgrp hfree k M N n hM hN hn
  have hbad : μ.real (freePart μ T hfree)ᶜ = 0 :=
    (measureReal_eq_zero_iff (μ := μ)).2 (measure_compl_freePart μ T hfree)
  have hle :
      μ.real
          ((packedUnion μ T hfree k M N n)ᶜ \
            stageCandidate μ T hfree k M N n) ≤
        ∑ j ∈ Finset.range n, μ.real (E j) := by
    calc
      _ ≤ μ.real ((freePart μ T hfree)ᶜ ∪ ⋃ j ∈ Finset.range n, E j) :=
        measureReal_mono hsubset
      _ ≤ μ.real (freePart μ T hfree)ᶜ +
          μ.real (⋃ j ∈ Finset.range n, E j) :=
        measureReal_union_le _ _
      _ ≤ 0 + ∑ j ∈ Finset.range n, μ.real (E j) := by
        rw [hbad]
        gcongr
        exact measureReal_biUnion_finset_le _ _
      _ = _ := zero_add _
  calc
    (M : ℝ) *
        μ.real
          ((packedUnion μ T hfree k M N n)ᶜ \
            stageCandidate μ T hfree k M N n)
        ≤ M * ∑ j ∈ Finset.range n, μ.real (E j) := by gcongr
    _ ≤ d := by
      exact sum_stageEscape_charge μ T hid hT hgrp hfree hd k M N n hM hN hn.le

include hid hT hgrp in
lemma exists_large_packedUnion (hfree : IsFreeAction μ T) (hd : 1 ≤ d)
    (N : ℕ) (hN : 0 < N) {e : ℝ} (he : 0 < e) :
    ∃ k M : ℕ, 0 < k ∧ 0 < M ∧
      1 - e ≤ μ.real (packedUnion μ T hfree k M N k) := by
  classical
  let K : ℕ := 2 ^ d
  obtain ⟨M, hMbig⟩ := exists_nat_gt ((2 : ℝ) * d / e)
  obtain ⟨k, hkbig⟩ := exists_nat_gt ((2 : ℝ) * K / e)
  have hMprod : (2 : ℝ) * d < e * M := by
    have := (div_lt_iff₀ he).1 hMbig
    nlinarith
  have hkprod : (2 : ℝ) * K < e * k := by
    have := (div_lt_iff₀ he).1 hkbig
    nlinarith
  have hMpos : 0 < M := by
    have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
    have : (0 : ℝ) < M := lt_of_lt_of_le (div_pos (mul_pos zero_lt_two hdreal) he)
      hMbig.le
    exact_mod_cast this
  have hkpos : 0 < k := by
    have hK : (0 : ℝ) < K := by positivity
    have : (0 : ℝ) < k := lt_of_lt_of_le (div_pos (mul_pos zero_lt_two hK) he)
      hkbig.le
    exact_mod_cast this
  refine ⟨k, M, hkpos, hMpos, ?_⟩
  by_contra hgoal
  push Not at hgoal
  have hcompl :
      e < μ.real (packedUnion μ T hfree k M N k)ᶜ := by
    rw [measureReal_compl
      (measurableSet_packedUnion μ T hid hT hgrp hfree k M N k), probReal_univ]
    linarith
  have hstage (n : ℕ) (hn : n < k) :
      e < (2 : ℝ) * K * μ.real (stageLayer μ T hfree k M N n) := by
    have hmono :
        packedUnion μ T hfree k M N n ⊆ packedUnion μ T hfree k M N k :=
      packedUnion_mono μ T hfree k M N hn.le
    have hU :
        e < μ.real (packedUnion μ T hfree k M N n)ᶜ :=
      hcompl.trans_le (measureReal_mono (compl_subset_compl.mpr hmono))
    have hUle :
        μ.real (packedUnion μ T hfree k M N n)ᶜ ≤
          μ.real (stageCandidate μ T hfree k M N n) +
            μ.real
              ((packedUnion μ T hfree k M N n)ᶜ \
                stageCandidate μ T hfree k M N n) := by
      calc
        _ ≤ μ.real
            (stageCandidate μ T hfree k M N n ∪
              ((packedUnion μ T hfree k M N n)ᶜ \
                stageCandidate μ T hfree k M N n)) := by
          apply measureReal_mono (μ := μ) (h₂ := by finiteness)
          intro x hx
          by_cases hA : x ∈ stageCandidate μ T hfree k M N n
          · exact Or.inl hA
          · exact Or.inr ⟨hx, hA⟩
        _ ≤ _ := measureReal_union_le _ _
    have hlost :=
      stageLost_charge μ T hid hT hgrp hfree hd k M N n hMpos hN hn
    have hA :
        e / 2 < μ.real (stageCandidate μ T hfree k M N n) := by
      nlinarith
    have hcharge :=
      stageCandidate_charge μ T hid hT hgrp hfree k M N n hMpos hN
    change μ.real (stageCandidate μ T hfree k M N n) ≤
      (K : ℝ) * μ.real (stageLayer μ T hfree k M N n) at hcharge
    nlinarith
  have hsum :
      ∑ _j ∈ Finset.range k, e <
        ∑ j ∈ Finset.range k,
          (2 : ℝ) * K * μ.real (stageLayer μ T hfree k M N j) := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 hkpos.ne')
    intro j hj
    exact hstage j (Finset.mem_range.1 hj)
  have hpacked :
      μ.real (packedUnion μ T hfree k M N k) =
        ∑ j ∈ Finset.range k, μ.real (stageLayer μ T hfree k M N j) :=
    measureReal_packedUnion_eq_sum μ T hid hT hgrp hfree k M N k
  have hpacked_le :
      μ.real (packedUnion μ T hfree k M N k) ≤ 1 := by
    simpa only [probReal_univ] using
      (measureReal_mono (μ := μ)
        (show packedUnion μ T hfree k M N k ⊆ (Set.univ : Set Ω) from subset_univ _))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [← Finset.mul_sum] at hsum
  rw [← hpacked] at hsum
  nlinarith

/-- The multiplier left after factoring the requested side length `N` out
of a rapidly separated scale. -/
def scaleFactor (d M N : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => M * N ^ d * scaleFactor d M N n ^ (d + 1)

lemma scale_eq_mul_scaleFactor (d M N n : ℕ) :
    scale d M N n = N * scaleFactor d M N n := by
  induction n with
  | zero => simp [scale, scaleFactor]
  | succ n ih =>
      rw [scale, scaleFactor, ih]
      ring

private def dilate (N : ℕ) (v : Fin d → ℤ) : Fin d → ℤ :=
  fun i => N * v i

/-- Lower corners of the `N`-blocks tiling `[0,Nm)ᵈ`. -/
noncomputable def blockOffsets (d N m : ℕ) : Finset (Fin d → ℤ) :=
  (boxShape d m).image (dilate (d := d) N)

lemma mem_blockOffsets {N m : ℕ} {c : Fin d → ℤ} :
    c ∈ blockOffsets d N m ↔
      ∃ u ∈ boxShape d m, dilate (d := d) N u = c := by
  simp [blockOffsets]

lemma card_blockOffsets {N m : ℕ} (hN : 0 < N) :
    (blockOffsets d N m).card = m ^ d := by
  rw [blockOffsets, Finset.card_image_of_injective]
  · exact card_boxShape d m
  · intro u v huv
    funext i
    have hi := congr_fun huv i
    dsimp [dilate] at hi
    exact (mul_left_cancel₀ (by exact_mod_cast hN.ne') hi)

lemma block_add_injective {N m : ℕ} (_hN : 0 < N)
    {c₁ c₂ v₁ v₂ : Fin d → ℤ}
    (hc₁ : c₁ ∈ blockOffsets d N m) (hc₂ : c₂ ∈ blockOffsets d N m)
    (hv₁ : v₁ ∈ boxShape d N) (hv₂ : v₂ ∈ boxShape d N)
    (heq : c₁ + v₁ = c₂ + v₂) :
    c₁ = c₂ ∧ v₁ = v₂ := by
  obtain ⟨u₁, hu₁, rfl⟩ := mem_blockOffsets.1 hc₁
  obtain ⟨u₂, hu₂, rfl⟩ := mem_blockOffsets.1 hc₂
  have hv : v₁ = v₂ := by
    funext i
    have hi := congr_fun heq i
    have hdvd : (N : ℤ) ∣ v₁ i - v₂ i := by
      refine ⟨u₂ i - u₁ i, ?_⟩
      dsimp [dilate] at hi ⊢
      linarith
    have habs : |v₁ i - v₂ i| < (N : ℤ) := by
      rw [abs_lt]
      have h₁ := mem_boxShape.1 hv₁ i
      have h₂ := mem_boxShape.1 hv₂ i
      constructor <;> omega
    exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd habs)
  have hc :
      dilate (d := d) N u₁ + v₂ = dilate (d := d) N u₂ + v₂ := by
    simpa only [hv] using heq
  exact ⟨add_right_cancel hc, hv⟩

lemma block_add_mem_boxShape {N m : ℕ} (hN : 0 < N)
    {c v : Fin d → ℤ} (hc : c ∈ blockOffsets d N m)
    (hv : v ∈ boxShape d N) :
    c + v ∈ boxShape d (N * m) := by
  obtain ⟨u, hu, rfl⟩ := mem_blockOffsets.1 hc
  rw [mem_boxShape]
  intro i
  have hui := mem_boxShape.1 hu i
  have hvi := mem_boxShape.1 hv i
  constructor
  · dsimp [dilate]
    exact add_nonneg (mul_nonneg (by positivity) hui.1) hvi.1
  · have husucc : u i + 1 ≤ (m : ℤ) := by omega
    have hmul : (N : ℤ) * (u i + 1) ≤ N * m :=
      mul_le_mul_of_nonneg_left husucc (by positivity)
    dsimp [dilate]
    calc
      (N : ℤ) * u i + v i < N * u i + N := by omega
      _ = N * (u i + 1) := by ring
      _ ≤ N * m := hmul

lemma block_add_shape_eq {N m : ℕ} (hN : 0 < N) :
    (blockOffsets d N m).image₂ (· + ·) (boxShape d N) =
      boxShape d (N * m) := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    obtain ⟨c, hc, v, hv, rfl⟩ := Finset.mem_image₂.1 hr
    exact block_add_mem_boxShape hN hc hv
  · have hinj :
        ((blockOffsets d N m) ×ˢ (boxShape d N) :
          Set ((Fin d → ℤ) × (Fin d → ℤ))).InjOn
            (fun p => p.1 + p.2) := by
      rintro ⟨c₁, v₁⟩ ⟨hc₁, hv₁⟩ ⟨c₂, v₂⟩ ⟨hc₂, hv₂⟩ heq
      obtain ⟨rfl, rfl⟩ := block_add_injective hN hc₁ hc₂ hv₁ hv₂ heq
      rfl
    rw [(Finset.card_image₂_iff.2 hinj), card_blockOffsets hN]
    simp [mul_pow, mul_comm]

omit [IsProbabilityMeasure μ] in
lemma pairwiseDisjoint_stageLayer (hfree : IsFreeAction μ T) (k M N : ℕ) :
    ((Finset.range k : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (stageLayer μ T hfree k M N) := by
  intro i hi j hj hij
  change Disjoint (stageLayer μ T hfree k M N i)
    (stageLayer μ T hfree k M N j)
  rw [Set.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hsub :
        stageLayer μ T hfree k M N i ⊆ packedUnion μ T hfree k M N j := by
      calc
        stageLayer μ T hfree k M N i
            ⊆ packedUnion μ T hfree k M N (i + 1) := by
          rw [packedUnion_succ]
          exact subset_union_right
        _ ⊆ packedUnion μ T hfree k M N j :=
          packedUnion_mono μ T hfree k M N hijlt
    exact stageLayer_subset_compl μ T hfree k M N j hxj (hsub hxi)
  · have hsub :
        stageLayer μ T hfree k M N j ⊆ packedUnion μ T hfree k M N i := by
      calc
        stageLayer μ T hfree k M N j
            ⊆ packedUnion μ T hfree k M N (j + 1) := by
          rw [packedUnion_succ]
          exact subset_union_right
        _ ⊆ packedUnion μ T hfree k M N i :=
          packedUnion_mono μ T hfree k M N hjilt
    exact stageLayer_subset_compl μ T hfree k M N i hxi (hsub hxj)

noncomputable def stageOffsets (d k M N j : ℕ) : Finset (Fin d → ℤ) :=
  blockOffsets d N (scaleFactor d M N (k - j))

lemma stageOffsets_add_shape_eq {k M N j : ℕ} (hN : 0 < N) :
    (stageOffsets d k M N j).image₂ (· + ·) (boxShape d N) =
      stageShape (d := d) k M N j := by
  rw [stageOffsets, stageShape, block_add_shape_eq hN, ← scale_eq_mul_scaleFactor]

/-- Retile every packed large cube exactly by copies of `[0,N)ᵈ` and
collect all of their lower floors into one base. -/
noncomputable def retiledBase (hfree : IsFreeAction μ T) (k M N : ℕ) : Set Ω :=
  ⋃ j ∈ Finset.range k, ⋃ c ∈ stageOffsets d k M N j,
    T c '' stageBase μ T hfree k M N j

omit [IsProbabilityMeasure μ] in
include hid hT hgrp in
lemma measurableSet_retiledBase (hfree : IsFreeAction μ T) (k M N : ℕ) :
    MeasurableSet (retiledBase μ T hfree k M N) := by
  unfold retiledBase
  apply (Finset.range k).measurableSet_biUnion
  intro j _
  apply (stageOffsets d k M N j).measurableSet_biUnion
  intro c _
  exact measurableSet_image μ T hid hT hgrp c
    (measurableSet_stageBase μ T hid hT hgrp hfree k M N j)

omit [IsProbabilityMeasure μ] in
include hgrp in
lemma tower_retiledBase_eq (hfree : IsFreeAction μ T) (k M N : ℕ) (hN : 0 < N) :
    tower T (boxShape d N) (retiledBase μ T hfree k M N) =
      packedUnion μ T hfree k M N k := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [tower, retiledBase, mem_iUnion, mem_image] at hx
    obtain ⟨v, hv, y, ⟨j, hj, c, hc, b, hb, rfl⟩, rfl⟩ := hx
    have hr : c + v ∈ stageShape (d := d) k M N j := by
      rw [← stageOffsets_add_shape_eq hN]
      exact Finset.mem_image₂.2 ⟨c, hc, v, hv, rfl⟩
    rw [packedUnion_eq_biUnion_stageLayer]
    refine mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hj, ?_⟩⟩
    refine mem_iUnion.2 ⟨c + v, mem_iUnion.2 ⟨hr, ?_⟩⟩
    exact ⟨b, hb, by simpa [add_comm] using hgrp v c b⟩
  · intro x hx
    rw [packedUnion_eq_biUnion_stageLayer] at hx
    simp only [stageLayer, tower, mem_iUnion, mem_image] at hx
    obtain ⟨j, hj, r, hr, b, hb, rfl⟩ := hx
    rw [← stageOffsets_add_shape_eq hN] at hr
    obtain ⟨c, hc, v, hv, hcv⟩ := Finset.mem_image₂.1 hr
    refine mem_iUnion.2 ⟨v, mem_iUnion.2 ⟨hv, T c b, ?_, ?_⟩⟩
    · refine mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hj, ?_⟩⟩
      exact mem_iUnion.2 ⟨c, mem_iUnion.2 ⟨hc, b, hb, rfl⟩⟩
    · rw [← hcv]
      simpa [add_comm] using (hgrp v c b).symm

omit [IsProbabilityMeasure μ] in
include hid hgrp in
lemma pairwiseDisjoint_retiledBase (hfree : IsFreeAction μ T) (k M N : ℕ)
    (hN : 0 < N) :
    ((boxShape d N : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)).PairwiseDisjoint
      (fun v => T v '' retiledBase μ T hfree k M N) := by
  intro u hu v hv huv
  change Disjoint (T u '' retiledBase μ T hfree k M N)
    (T v '' retiledBase μ T hfree k M N)
  rw [Set.disjoint_left]
  intro x hxu hxv
  simp only [retiledBase, mem_iUnion, mem_image] at hxu hxv
  obtain ⟨yu, ⟨ju, hju, cu, hcu, bu, hbu, rfl⟩, rfl⟩ := hxu
  obtain ⟨yv, ⟨jv, hjv, cv, hcv, bv, hbv, hyv⟩, hxvEq⟩ := hxv
  have hru : cu + u ∈ stageShape (d := d) k M N ju := by
    rw [← stageOffsets_add_shape_eq hN]
    exact Finset.mem_image₂.2 ⟨cu, hcu, u, hu, rfl⟩
  have hrv : cv + v ∈ stageShape (d := d) k M N jv := by
    rw [← stageOffsets_add_shape_eq hN]
    exact Finset.mem_image₂.2 ⟨cv, hcv, v, hv, rfl⟩
  have hEqU : T (cu + u) bu = T u (T cu bu) := by
    simpa [add_comm] using hgrp u cu bu
  have hEqV : T (cv + v) bv = T u (T cu bu) := by
    calc
      T (cv + v) bv = T v (T cv bv) := by
        simpa [add_comm] using hgrp v cv bv
      _ = T v yv := congrArg (T v) hyv
      _ = T u (T cu bu) := hxvEq
  have hxLayerU : T u (T cu bu) ∈ stageLayer μ T hfree k M N ju := by
    simp only [stageLayer, tower, mem_iUnion, mem_image]
    exact ⟨cu + u, hru, bu, hbu, hEqU⟩
  have hxLayerV : T u (T cu bu) ∈ stageLayer μ T hfree k M N jv := by
    simp only [stageLayer, tower, mem_iUnion, mem_image]
    exact ⟨cv + v, hrv, bv, hbv, hEqV⟩
  have hjuv : ju = jv := by
    by_contra hne
    exact Set.disjoint_left.1
      (pairwiseDisjoint_stageLayer μ T hfree k M N hju hjv hne)
      hxLayerU hxLayerV
  subst jv
  have hfloorU : T u (T cu bu) ∈ T (cu + u) '' stageBase μ T hfree k M N ju :=
    ⟨bu, hbu, hEqU⟩
  have hfloorV : T u (T cu bu) ∈ T (cv + v) '' stageBase μ T hfree k M N ju := by
    exact ⟨bv, hbv, hEqV⟩
  have hruv : cu + u = cv + v := by
    by_contra hne
    exact Set.disjoint_left.1
      (pairwiseDisjoint_stageBase μ T hid hgrp hfree k M N ju hru hrv hne)
      hfloorU hfloorV
  exact huv (block_add_injective hN hcu hcv hu hv hruv).2

end Submission.Helpers
