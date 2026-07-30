import ChallengeDeps
import Submission.Helpers

namespace Submission

namespace SourceDefinitions
namespace LeanEval
namespace Combinatorics
namespace FangXiaTilingProblem

/-!
# Fang–Xia: tiling of the symmetric group by transpositions

If `T_n = {1} ∪ {all transpositions}` and `(T_n, Y)` is a tiling of the
symmetric group `S_n` (every element of `S_n` has a unique factorisation
`x · y` with `x ∈ T_n`, `y ∈ Y`), then every integer partition `λ` of
`n` whose Young-diagram content sum is nonnegative forces `Y` to be
**λ-transitive** in the Martin–Sagan sense: every pair of ordered set
partitions of shape `λ` is connected by exactly a fixed positive number
of permutations in `Y`. Fang–Xia, *Tiling the symmetric group by
transpositions*, Bull. London Math. Soc. **58**(5) (2026); DOI
`10.1112/blms.70366`; arXiv:2506.00360.
-/

open scoped BigOperators

/-- A factorisation/tiling `(X, Y)` of a group: every element has a
unique representation `x * y` with `x ∈ X` and `y ∈ Y`. -/
def IsTiling {G : Type*} [Group G] (X Y : Set G) : Prop :=
  ∀ g : G, ∃! p : X × Y, (p.1 : G) * (p.2 : G) = g

/-- `T_n` — the identity plus all transpositions in `S_n`. -/
def transpositionsWithOne (n : ℕ) : Set (Equiv.Perm (Fin n)) :=
  {σ | σ = 1 ∨ ∃ i j : Fin n, i ≠ j ∧ σ = Equiv.swap i j}

/-- A weakly-decreasing list of positive row lengths summing to `n`:
the concrete encoding of an integer partition of `n`. -/
structure PartitionShape (n : ℕ) where
  parts : List ℕ
  sorted : parts.Pairwise (· ≥ ·)
  positive : ∀ a ∈ parts, 0 < a
  sum_eq : parts.sum = n

namespace PartitionShape

/-- Auxiliary zero-indexed content sum for a list of row lengths. -/
def contentSumAux : ℕ → List ℕ → ℤ
  | _, [] => 0
  | i, a :: as => (a : ℤ) * ((a : ℤ) - 2 * (i : ℤ) - 1) + contentSumAux (i + 1) as

/-- The paper's content-sum condition, written in the equivalent
row-length formula from the remark after Theorem 1.4. Rows are
zero-indexed here, so the `i`-th term is `aᵢ · (aᵢ − 2i − 1)`,
matching the paper's one-indexed `λ_i · (λ_i − 2i + 1)`. -/
def contentSum {n : ℕ} (lam : PartitionShape n) : ℤ :=
  contentSumAux 0 lam.parts

end PartitionShape

/-- An ordered set partition of `Fin n` with block sizes given by
`lam`. -/
structure OrderedSetPartition {n : ℕ} (lam : PartitionShape n) where
  block : Fin lam.parts.length → Finset (Fin n)
  card_block : ∀ i : Fin lam.parts.length, (block i).card = lam.parts.get i
  pairwise_disjoint :
    Pairwise fun i j : Fin lam.parts.length => Disjoint (block i) (block j)
  union_eq_univ : (Finset.univ.biUnion block) = Finset.univ

/-- A permutation sends an ordered set partition `P` to `Q` blockwise. -/
def SendsPartition {n : ℕ} (σ : Equiv.Perm (Fin n)) {lam : PartitionShape n}
    (P Q : OrderedSetPartition lam) : Prop :=
  ∀ i : Fin lam.parts.length, (P.block i).image σ = Q.block i

/-- λ-transitivity in the Martin–Sagan sense: every pair of ordered
set partitions of shape `λ` is connected by exactly a fixed positive
number of elements of `Y`. -/
def IsPartitionTransitive {n : ℕ} (Y : Set (Equiv.Perm (Fin n)))
    (lam : PartitionShape n) : Prop :=
  ∃ r : ℕ, 0 < r ∧
    ∀ P Q : OrderedSetPartition lam,
      {σ : Equiv.Perm (Fin n) | σ ∈ Y ∧ SendsPartition σ P Q}.ncard = r



end FangXiaTilingProblem
end Combinatorics
end LeanEval
end SourceDefinitions

open LeanEval.Combinatorics.FangXiaTilingProblem
open scoped BigOperators
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

namespace LeanEval.Combinatorics.FangXiaTilingProblem

open scoped BigOperators
open Classical

/- The block data determine an ordered partition. Keeping this small `Finite`
   instance around is convenient; in particular all the `ncard`s below are
   honest finite counts. -/
noncomputable instance orderedSetPartitionFinite {n : ℕ} (a : PartitionShape n) :
    Finite (OrderedSetPartition a) := by
  classical
  refine Finite.of_injective (fun P : OrderedSetPartition a => P.block) ?_
  intro P Q h
  cases P with
  | mk b hb hd hu =>
    cases Q with
    | mk b' hb' hd' hu' =>
      dsimp at h
      subst b'
      rfl

/-- Relabel all the elements of a set partition by a permutation.  Notice that
    permutations act on the *left* here, just as in `t*y` in `IsTiling`. -/
noncomputable def ospAct {n : ℕ} {a : PartitionShape n}
    (s : Equiv.Perm (Fin n)) (P : OrderedSetPartition a) :
    OrderedSetPartition a where
  block i := (P.block i).image s
  card_block i := by simpa using (Finset.card_image_iff.mpr (Set.injOn_of_injective s.injective) :
    ((P.block i).image s).card = (P.block i).card) |>.trans (P.card_block i)
  pairwise_disjoint := by
    classical
    intro i j hij
    have h := P.pairwise_disjoint hij
    exact (Finset.disjoint_image s.injective).2 h
  union_eq_univ := by
    classical
    apply Finset.eq_univ_of_forall
    intro x
    have hx : s.symm x ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    rw [← P.union_eq_univ] at hx
    rcases Finset.mem_biUnion.1 hx with ⟨i, hi, hi'⟩
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
      Finset.mem_image.2 ⟨s.symm x, hi', s.apply_symm_apply x⟩⟩


@[simp] lemma ospAct_block {n : ℕ} {a : PartitionShape n}
    (s : Equiv.Perm (Fin n)) (P : OrderedSetPartition a)
    (i : Fin a.parts.length) :
    (ospAct s P).block i = (P.block i).image s := rfl

@[simp] lemma ospAct_one {n : ℕ} {a : PartitionShape n}
    (P : OrderedSetPartition a) : ospAct (1 : Equiv.Perm (Fin n)) P = P := by
  classical
  cases P
  simp [ospAct]


lemma osp_ext {n : ℕ} {a : PartitionShape n}
    {P Q : OrderedSetPartition a}
    (h : ∀ i, P.block i = Q.block i) : P = Q := by
  cases P with | mk b hb hd hu =>
    cases Q with | mk c hc he hv =>
      cases (funext h)
      rfl

@[simp] lemma ospAct_mul {n : ℕ} {a : PartitionShape n}
    (s t : Equiv.Perm (Fin n)) (P : OrderedSetPartition a) :
    ospAct s (ospAct t P) = ospAct (s * t) P := by
  classical
  apply osp_ext
  intro i
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.1 hx with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.1 hy with ⟨z, hz, rfl⟩
    exact Finset.mem_image.2 ⟨z, hz, rfl⟩
  · intro hx
    rcases Finset.mem_image.1 hx with ⟨z, hz, rfl⟩
    exact Finset.mem_image.2 ⟨t z, Finset.mem_image.2 ⟨z, hz, rfl⟩, rfl⟩

@[simp] lemma ospAct_symm {n : ℕ} {a : PartitionShape n}
    (s : Equiv.Perm (Fin n)) (P : OrderedSetPartition a) :
    ospAct s⁻¹ (ospAct s P) = P := by
  classical
  rw [ospAct_mul]
  simp

lemma sends_iff_act {n : ℕ} {a : PartitionShape n}
    (s : Equiv.Perm (Fin n)) (P Q : OrderedSetPartition a) :
    SendsPartition s P Q ↔ ospAct s P = Q := by
  constructor
  · intro h; exact osp_ext h
  · intro h i
    have := congrArg (fun R : OrderedSetPartition a => R.block i) h
    simpa using this


/-- Every element belongs to one of the blocks. -/
lemma osp_exists_mem {n : ℕ} {a : PartitionShape n}
    (P : OrderedSetPartition a) (x : Fin n) :
    ∃ i : Fin a.parts.length, x ∈ P.block i := by
  have hx : x ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  rw [← P.union_eq_univ] at hx
  rcases Finset.mem_biUnion.1 hx with ⟨i, hi, hx⟩
  exact ⟨i, hx⟩

lemma osp_unique_mem {n : ℕ} {a : PartitionShape n}
    (P : OrderedSetPartition a) {x : Fin n}
    {i j : Fin a.parts.length} (hi : x ∈ P.block i) (hj : x ∈ P.block j) :
    i = j := by
  classical
  by_contra h
  have hd := P.pairwise_disjoint h
  exact (Finset.disjoint_left.1 hd hi hj)

/-- The (ordered) colour of an element in a set partition. -/
noncomputable def ospIndex {n : ℕ} {a : PartitionShape n}
    (P : OrderedSetPartition a) (x : Fin n) : Fin a.parts.length :=
  Classical.choose (osp_exists_mem P x)

@[simp] lemma ospIndex_mem {n : ℕ} {a : PartitionShape n}
    (P : OrderedSetPartition a) (x : Fin n) :
    x ∈ P.block (ospIndex P x) :=
  Classical.choose_spec (osp_exists_mem P x)

lemma mem_block_index_iff {n : ℕ} {a : PartitionShape n}
    (P : OrderedSetPartition a) (x : Fin n) (i : Fin a.parts.length) :
    x ∈ P.block i ↔ ospIndex P x = i := by
  constructor
  · intro h
    exact osp_unique_mem P (ospIndex_mem P x) h
  · intro h; simpa [h] using ospIndex_mem P x

lemma ospIndex_act {n : ℕ} {a : PartitionShape n}
    (s : Equiv.Perm (Fin n)) (P : OrderedSetPartition a) (x : Fin n) :
    ospIndex (ospAct s P) x = ospIndex P (s⁻¹ x) := by
  classical
  apply osp_unique_mem (ospAct s P)
    (ospIndex_mem (ospAct s P) x)
  change x ∈ (P.block _).image s
  exact Finset.mem_image.2 ⟨s⁻¹ x, ospIndex_mem P _, by simp⟩

/-- Partitions are exactly colourings with the prescribed fibre sizes.  It is
    useful to write this down rather than pick representatives of cosets. -/
def Colourings (N k : ℕ) (v : Fin k → ℕ) :=
  {c : Fin N → Fin k // ∀ i, (Finset.univ.filter fun x => c x = i).card = v i}

noncomputable instance colouringsFinite (N k : ℕ) (v : Fin k → ℕ) :
    Finite (Colourings N k v) := by
  classical
  unfold Colourings
  infer_instance

noncomputable def ospColour {n : ℕ} {a : PartitionShape n}
    (P : OrderedSetPartition a) :
    Colourings n a.parts.length (fun i => a.parts.get i) := by
  classical
  refine ⟨ospIndex P, ?_⟩
  intro i
  have h : (Finset.univ.filter fun x : Fin n => ospIndex P x = i) = P.block i := by
    ext x
    simp [mem_block_index_iff]
  simpa [h] using P.card_block i

/-- Turn a colouring back into its fibres. -/
noncomputable def colourPartition {n : ℕ} {a : PartitionShape n}
    (c : Colourings n a.parts.length (fun i => a.parts.get i)) :
    OrderedSetPartition a where
  block i := Finset.univ.filter fun x => c.1 x = i
  card_block i := c.2 i
  pairwise_disjoint := by
    classical
    intro i j h
    refine Finset.disjoint_left.2 ?_
    intro x hx hx'
    have hi : c.1 x = i := (Finset.mem_filter.1 hx).2
    have hj : c.1 x = j := (Finset.mem_filter.1 hx').2
    exact h (hi.symm.trans hj)
  union_eq_univ := by
    classical
    apply Finset.eq_univ_of_forall
    intro x
    exact Finset.mem_biUnion.2 ⟨c.1 x, Finset.mem_univ _,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩

@[simp] lemma colourPartition_ospColour {n : ℕ} {a : PartitionShape n}
    (P : OrderedSetPartition a) :
    colourPartition (ospColour P) = P := by
  classical
  apply osp_ext
  intro i
  ext x
  simp [colourPartition, ospColour, mem_block_index_iff]

@[simp] lemma ospColour_colourPartition {n : ℕ} {a : PartitionShape n}
    (c : Colourings n a.parts.length (fun i => a.parts.get i)) :
    ospColour (colourPartition c) = c := by
  classical
  apply Subtype.ext
  funext x
  -- both values are the unique block containing `x`
  apply (mem_block_index_iff (colourPartition c) x (c.1 x)).1
  change x ∈ Finset.univ.filter (fun y : Fin n => c.1 y = c.1 x)
  simp

noncomputable def ospEquivColour {n : ℕ} {a : PartitionShape n} :
    OrderedSetPartition a ≃
      Colourings n a.parts.length (fun i => a.parts.get i) where
  toFun := ospColour
  invFun := colourPartition
  left_inv := colourPartition_ospColour
  right_inv := ospColour_colourPartition


noncomputable def blockMatch {n : ℕ} {a : PartitionShape n}
    (P Q : OrderedSetPartition a) (i : Fin a.parts.length) :
    {x : Fin n // x ∈ P.block i} ≃ {x : Fin n // x ∈ Q.block i} := by
  classical
  apply Fintype.equivOfCardEq
  simp [P.card_block, Q.card_block]

/-- There is a permutation taking any ordered partition to any other one. -/
noncomputable def partitionTransport {n : ℕ} {a : PartitionShape n}
    (P Q : OrderedSetPartition a) : Equiv.Perm (Fin n) := by
  classical
  let f : Fin n → Fin n := fun x =>
    ((blockMatch P Q (ospIndex P x))
      ⟨x, ospIndex_mem P x⟩).1
  have hfmem (x : Fin n) : f x ∈ Q.block (ospIndex P x) :=
    ((blockMatch P Q (ospIndex P x))
      ⟨x, ospIndex_mem P x⟩).2
  have hf : Function.Injective f := by
    intro x y hxy
    have hi : ospIndex P x = ospIndex P y := by
      exact osp_unique_mem Q (hfmem x)
        (by simpa [hxy] using hfmem y)
    -- use the injectivity of the chosen bijection inside this block
    -- unfolding the name of the map exposes the two block equivalences
    dsimp [f] at hxy
    have hh :
        (blockMatch P Q (ospIndex P x))
            ⟨x, ospIndex_mem P x⟩ =
          (blockMatch P Q (ospIndex P x))
            ⟨y, by simpa [hi] using ospIndex_mem P y⟩ := by
      apply Subtype.ext
      -- rewriting just the right colour is harmless here (all elements of a
      -- `Finset` subtype with the same value have the same proof field).
      convert hxy using 1
      -- a small dependent-index congruence, with variable indices, avoids
      -- rewriting under the proof in the subtype.
      have same (i j : Fin a.parts.length) (h : i = j)
          (z : Fin n) (hz : z ∈ P.block i) (hz' : z ∈ P.block j) :
          ((blockMatch P Q i) ⟨z, hz⟩).1 =
            ((blockMatch P Q j) ⟨z, hz'⟩).1 := by
        subst j
        rfl
      exact same _ _ hi _ _ _
    have :
        (⟨x, ospIndex_mem P x⟩ : {z // z ∈ P.block (ospIndex P x)}) =
          ⟨y, by simpa [hi] using ospIndex_mem P y⟩ :=
      (blockMatch P Q (ospIndex P x)).injective hh
    exact congrArg Subtype.val this
  exact Equiv.ofBijective f ⟨hf,
    (Finite.injective_iff_surjective.mp hf)⟩

@[simp] lemma partitionTransport_apply {n : ℕ} {a : PartitionShape n}
    (P Q : OrderedSetPartition a) (x : Fin n) :
    partitionTransport P Q x =
      ((blockMatch P Q (ospIndex P x))
        ⟨x, ospIndex_mem P x⟩).1 := by
  classical
  rfl

lemma transport_sends {n : ℕ} {a : PartitionShape n}
    (P Q : OrderedSetPartition a) :
    ospAct (partitionTransport P Q) P = Q := by
  classical
  apply osp_ext
  intro i
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rcases Finset.mem_image.1 hy with ⟨x, hx, rfl⟩
    have hi : ospIndex P x = i :=
      (mem_block_index_iff P _ _).1 hx
    have hm :=
      ((blockMatch P Q (ospIndex P x))
        ⟨x, ospIndex_mem P x⟩).2
    simpa [partitionTransport_apply, hi] using hm
  · change (Q.block i).card ≤ ((P.block i).image (partitionTransport P Q)).card
    rw [Q.card_block i,
        Finset.card_image_iff.mpr
          (Set.injOn_of_injective (partitionTransport P Q).injective),
        P.card_block i]

lemma partition_transitive_action {n : ℕ} {a : PartitionShape n}
    (P Q : OrderedSetPartition a) :
    ∃ s : Equiv.Perm (Fin n), ospAct s P = Q :=
  ⟨partitionTransport P Q, transport_sends P Q⟩


/-- The elementary convolution consequence of a tiling.  It is sometimes handy
    to state it without any characters: for a fixed `g` there is exactly one
    left factor in `X`; its right factor has to be `x⁻¹*g`. -/
lemma tiling_unique_left {G : Type*} [Group G]
    {X Y : Set G} (h : IsTiling X Y) (g : G) :
    ∃! x : G, x ∈ X ∧ x⁻¹ * g ∈ Y := by
  rcases h g with ⟨p, hp, hp'⟩
  refine ⟨(p.1 : G), ⟨p.1.property, ?_⟩, ?_⟩
  · have := congrArg (fun z : G => (p.1 : G)⁻¹ * z) hp
    simpa [mul_assoc] using (show (p.1 : G)⁻¹ * g ∈ Y from by
      -- expose the second component of the old pair
      have heq : (p.1 : G)⁻¹ * g = (p.2 : G) := by
        calc
          (p.1 : G)⁻¹ * g = (p.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) := by rw [hp]
          _ = (p.2 : G) := by simp
      exact heq.symm ▸ p.2.property)
  · intro x hx
    have heq : x * (x⁻¹ * g) = g := by simp
    let q : X × Y :=
      (⟨x, hx.1⟩, ⟨x⁻¹ * g, hx.2⟩)
    have hq : (q.1 : G) * (q.2 : G) = g := heq
    have hqp : q = p := hp' q hq
    exact congrArg (fun z : X × Y => (z.1 : G)) hqp

/-- Finite, indicator-function version of `tiling_unique_left`. -/
lemma tiling_indicator_sum {G : Type*} [Group G] [Fintype G]
    {X Y : Set G} (h : IsTiling X Y) (g : G) :
    ∑ x : G, (if x ∈ X ∧ x⁻¹ * g ∈ Y then (1 : ℤ) else 0) = 1 := by
  classical
  rcases tiling_unique_left h g with ⟨u, hu, hu'⟩
  have hf : (Finset.univ.filter fun x : G => x ∈ X ∧ x⁻¹ * g ∈ Y) = {u} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact fun hx => hu' x hx
    · intro hx; simpa [hx] using hu
  calc
    ∑ x : G, (if x ∈ X ∧ x⁻¹ * g ∈ Y then (1 : ℤ) else 0) =
        ((Finset.univ.filter fun x : G => x ∈ X ∧ x⁻¹ * g ∈ Y).card : ℤ) := by
          -- sums of characteristic functions are cards
          classical
          simp
    _ = 1 := by simp [hf]


lemma tiling_Y_nonempty {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    (h : IsTiling (transpositionsWithOne n) Y) : Y.Nonempty := by
  rcases h (1 : Equiv.Perm (Fin n)) with ⟨p, hp, hp'⟩
  exact ⟨p.2, p.2.property⟩

/-- The completely homogeneous (one block, or no blocks) case of the
    conclusion.  It is a useful boundary case because it does not use any
    spectral argument about transpositions. -/
lemma partitionTransitive_of_subsingleton
    {n : ℕ} {Y : Set (Equiv.Perm (Fin n))} {a : PartitionShape n}
    (hY : Y.Nonempty) [Subsingleton (OrderedSetPartition a)] :
    IsPartitionTransitive Y a := by
  classical
  refine ⟨Y.ncard, ?_, ?_⟩
  · have hf : Y.Finite := Set.toFinite _
    exact (Set.ncard_pos hf).2 hY
  · intro P Q
    have hs (s : Equiv.Perm (Fin n)) : SendsPartition s P Q := by
      exact (sends_iff_act s P Q).2 (Subsingleton.elim _ _)
    have he : {s : Equiv.Perm (Fin n) | s ∈ Y ∧ SendsPartition s P Q} = Y := by
      ext s
      simp [hs s]
    rw [he]

lemma osp_subsingleton_of_length_le_one {n : ℕ} {a : PartitionShape n}
    (h : a.parts.length ≤ 1) : Subsingleton (OrderedSetPartition a) := by
  classical
  constructor
  intro P Q
  apply osp_ext
  intro i
  have ilt := i.isLt
  have ilen : a.parts.length = 1 :=
    Nat.le_antisymm h (Nat.succ_le_iff.2 (Nat.pos_of_ne_zero (by
      intro hz
      simpa [hz] using ilt)))
  have ii : i = ⟨0, by simpa [ilen]⟩ := by
    apply Fin.ext
    have iz : i.val = 0 := Nat.eq_zero_of_le_zero (by omega)
    exact iz
  -- both sole blocks are univ by the union condition
  subst i
  have hP (R : OrderedSetPartition a) : R.block ⟨0, by simpa [ilen]⟩ = Finset.univ := by
    have hup := R.union_eq_univ
    apply Finset.eq_univ_of_forall
    intro x
    have hx : x ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    rw [← hup] at hx
    rcases Finset.mem_biUnion.1 hx with ⟨j, hj, hx⟩
    have jeq : j = (⟨0, by simpa [ilen]⟩ : Fin a.parts.length) := by
      apply Fin.ext
      have := j.isLt
      omega
    simpa [jeq] using hx
  rw [hP P, hP Q]


/- A small sum-of-squares estimate that is the useful substitute for the
   missing Specht-module machinery. It is deliberately about ordinary
   colourings, not partitions. -/
abbrev PlainColour (N k : ℕ) := Fin N → Fin k

noncomputable def colUpdate {N k : ℕ} (c : PlainColour N k)
    (x : Fin N) (i : Fin k) : PlainColour N k :=
  Function.update c x i

noncomputable def colTranspose {N k : ℕ} (c : PlainColour N k)
    (x y : Fin N) : PlainColour N k :=
  fun z => c (Equiv.swap x y z)

/-- Swap two particular colours at a single coordinate. -/
noncomputable def colourAtSwap {N k : ℕ} (x : Fin N) (r s : Fin k) :
    PlainColour N k ≃ PlainColour N k where
  toFun c z := if z = x then Equiv.swap r s (c z) else c z
  invFun c z := if z = x then Equiv.swap r s (c z) else c z
  left_inv := by
    classical
    intro c
    funext z
    by_cases hz : z = x
    · subst z
      simp
    · simp [hz]
  right_inv := by
    classical
    intro c
    funext z
    by_cases hz : z = x
    · subst z
      simp
    · simp [hz]

@[simp] lemma colourAtSwap_same {N k : ℕ} (x : Fin N) (r s : Fin k)
    (c : PlainColour N k) :
    colourAtSwap x r s c x = Equiv.swap r s (c x) := by
  classical simp [colourAtSwap]

lemma colourAtSwap_other {N k : ℕ} (x z : Fin N) (r s : Fin k)
    (c : PlainColour N k) (h : z ≠ x) :
    colourAtSwap x r s c z = c z := by
  classical simp [colourAtSwap, h]

@[simp] lemma colUpdate_same {N k : ℕ} (c : PlainColour N k)
    (x : Fin N) (i : Fin k) : colUpdate c x i x = i := by
  classical simp [colUpdate]

lemma colUpdate_other {N k : ℕ} (c : PlainColour N k)
    (x z : Fin N) (i : Fin k) (h : z ≠ x) :
    colUpdate c x i z = c z := by
  classical simp [colUpdate, h]

lemma colourAtSwap_of_value {N k : ℕ} (x : Fin N) {r s : Fin k}
    (hrs : r ≠ s) (c : PlainColour N k) (hx : c x = r) :
    colourAtSwap x r s c = colUpdate c x s := by
  classical
  funext z
  by_cases hz : z = x
  · subst z
    simp [hx, Equiv.swap_apply_def, hrs]
  · simp [colourAtSwap, colUpdate, hz]

lemma transposed_after_one {N k : ℕ} (c : PlainColour N k)
    (x y : Fin N) {r s : Fin k} (hrs : r ≠ s)
    (hx : c x = r) (hy : c y = r) (hxy : y ≠ x) :
    colTranspose (colourAtSwap x r s c) x y = colUpdate c y s := by
  classical
  funext z
  by_cases hz1 : z = x
  · subst z
    -- at `x` the transposed word has the old value at `y`
    have hx' : x ≠ y := Ne.symm hxy
    -- expanding the two changed coordinates is less brittle than rewriting
    -- the ambient functions.
    simp [colTranspose, colourAtSwap, colUpdate, hx', hxy, hy, hx]
  · by_cases hz2 : z = y
    · subst z
      have hx' : x ≠ y := Ne.symm hxy
      simp [colTranspose, Equiv.swap_apply_def, colourAtSwap_same,
        colUpdate, hx', hrs, hx]
    · have hzx : z ≠ x := hz1
      have hzy : z ≠ y := hz2
      -- away from the two coordinates nothing changes
      simp [colTranspose, Equiv.swap_apply_def, hzx, hzy,
        colourAtSwap, colUpdate]


lemma swap_value_eq_right {k : ℕ} {r s v : Fin k} (hrs : r ≠ s) :
    Equiv.swap r s v = s ↔ v = r := by
  classical
  constructor
  · intro h
    have hh := congrArg (Equiv.swap r s) h
    simpa using hh
  · intro h; subst v; simp

/-- one coordinate of the elementary incidence calculation -/
lemma colour_exchange_one {N k : ℕ} (f : PlainColour N k → ℝ)
    {r s : Fin k} (hrs : r ≠ s) (x : Fin N) :
    (∑ c : PlainColour N k,
      if c x = s then
        f c * (f c + ∑ y : Fin N,
          if c y = r then f (colTranspose c x y) else 0)
      else 0) =
    (∑ u : PlainColour N k,
      if u x = r then
        f (colUpdate u x s) *
          (∑ y : Fin N, if u y = r then f (colUpdate u y s) else 0)
      else 0) := by
  classical
  let L : PlainColour N k → ℝ := fun c =>
      if c x = s then
        f c * (f c + ∑ y : Fin N,
          if c y = r then f (colTranspose c x y) else 0)
      else 0
  let R : PlainColour N k → ℝ := fun u =>
      if u x = r then
        f (colUpdate u x s) *
          (∑ y : Fin N, if u y = r then f (colUpdate u y s) else 0)
      else 0
  change (∑ c, L c) = ∑ u, R u
  rw [← Equiv.sum_comp (colourAtSwap x r s) L]
  apply Finset.sum_congr rfl
  intro u hu
  dsimp [L, R]
  by_cases hx : u x = r
  · have hx' : colourAtSwap x r s u = colUpdate u x s :=
      colourAtSwap_of_value x hrs u hx
    have hsx : colourAtSwap x r s u x = s := by simp [hx]
    simp only [hsx, hx, if_true, hx']
    -- split the two inner sums at the distinguished coordinate
    let A : Fin N → ℝ := fun y =>
       if (colourAtSwap x r s u) y = r
       then f (colTranspose (colourAtSwap x r s u) x y) else 0
    let B : Fin N → ℝ := fun y =>
       if u y = r then f (colUpdate u y s) else 0
    have hA0 : A x = 0 := by
      dsimp [A]
      simp [hsx, Ne.symm hrs]
    have hB0 : B x = f (colUpdate u x s) := by
      dsimp [B]
      simp [hx]
    have hrest :
        (∑ y ∈ (Finset.univ.erase x), A y) =
          ∑ y ∈ (Finset.univ.erase x), B y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hne : y ≠ x := Finset.ne_of_mem_erase hy
      have he : colourAtSwap x r s u y = u y :=
        colourAtSwap_other x y r s u hne
      dsimp [A, B]
      rw [he]
      by_cases hyr : u y = r
      · simp [hyr, transposed_after_one u x y hrs hx hyr hne]
      · simp [hyr]
    have hsumA : (∑ y : Fin N, A y) =
        ∑ y ∈ (Finset.univ.erase x), A y := by
      have hh := (Finset.add_sum_erase (Finset.univ : Finset (Fin N))
        A (Finset.mem_univ x))
      -- `hh : A x + rest = total`
      simpa [hA0] using hh.symm
    have hsumB : (∑ y : Fin N, B y) =
        f (colUpdate u x s) + ∑ y ∈ (Finset.univ.erase x), B y := by
      simpa [hB0] using
        (Finset.add_sum_erase (Finset.univ : Finset (Fin N))
          B (Finset.mem_univ x)).symm
    have hinnerA :
        (∑ y : Fin N, if colUpdate u x s y = r
              then f (colTranspose (colUpdate u x s) x y) else 0) =
          ∑ y : Fin N, A y := by
      simp only [A, hx']
    change
      f (colUpdate u x s) *
          (f (colUpdate u x s) +
            ∑ y : Fin N, if colUpdate u x s y = r
              then f (colTranspose (colUpdate u x s) x y) else 0) =
        f (colUpdate u x s) * (∑ y : Fin N, B y)
    rw [hinnerA, hsumA, hsumB, hrest]
  · have hns : colourAtSwap x r s u x ≠ s := by
      intro he
      exact hx ((swap_value_eq_right hrs).1 (by simpa using he))
    rw [if_neg hns, if_neg hx]


/-- The binary exchange graph on two colours has bottom eigenvalue `-#s`.
    In this incidence form it is just a sum of squares.  No representation
    theory is needed. -/
lemma colour_exchange_nonneg {N k : ℕ} (f : PlainColour N k → ℝ)
    {r s : Fin k} (hrs : r ≠ s) :
    0 ≤ ∑ c : PlainColour N k, ∑ x : Fin N,
      (if c x = s then
        f c * (f c + ∑ y : Fin N,
          if c y = r then f (colTranspose c x y) else 0)
       else 0) := by
  classical
  -- change the distinguished word at a single coordinate
  calc
    0 ≤ ∑ u : PlainColour N k,
          (∑ x : Fin N, if u x = r then f (colUpdate u x s) else 0) ^ 2 :=
        Finset.sum_nonneg (fun u hu => sq_nonneg _)
    _ = ∑ x : Fin N, ∑ u : PlainColour N k,
          (if u x = r then
            f (colUpdate u x s) *
              (∑ y : Fin N, if u y = r then f (colUpdate u y s) else 0)
           else 0) := by
        -- every inner sum is its square, expanded before commuting the sums
        have each (u : PlainColour N k) :
            (∑ x : Fin N, if u x = r then f (colUpdate u x s) else 0)^2 =
              ∑ x : Fin N,
                (if u x = r then
                  f (colUpdate u x s) *
                    (∑ y : Fin N,
                       if u y = r then f (colUpdate u y s) else 0)
                 else 0) := by
          let D : ℝ := ∑ y : Fin N,
                       if u y = r then f (colUpdate u y s) else 0
          change D ^ 2 = _
          -- distribute multiplication by the same `D`
          calc
            D ^ 2 = D * D := by ring
            _ = (∑ x : Fin N,
                    if u x = r then f (colUpdate u x s) else 0) * D := rfl
            _ = ∑ x : Fin N,
                    (if u x = r then f (colUpdate u x s) else 0) * D := by
                  rw [Finset.sum_mul]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro x hxmem
              by_cases hx : u x = r <;> simp [D, hx]
        calc
          (∑ u : PlainColour N k,
            (∑ x : Fin N, if u x = r then f (colUpdate u x s) else 0) ^ 2) =
              ∑ u : PlainColour N k, ∑ x : Fin N,
                (if u x = r then
                  f (colUpdate u x s) *
                    (∑ y : Fin N, if u y = r then f (colUpdate u y s) else 0)
                 else 0) := Finset.sum_congr rfl (fun u hu => each u)
          _ = _ := by rw [Finset.sum_comm]
    _ = _ := by
      -- and use the coordinate calculation on every `x`
      calc
        (∑ x : Fin N, ∑ u : PlainColour N k,
          (if u x = r then
            f (colUpdate u x s) *
              (∑ y : Fin N, if u y = r then f (colUpdate u y s) else 0)
           else 0)) =
            ∑ x : Fin N, ∑ c : PlainColour N k,
              (if c x = s then
                f c * (f c + ∑ y : Fin N,
                  if c y = r then f (colTranspose c x y) else 0)
               else 0) := by
                apply Finset.sum_congr rfl
                intro x hx
                symm
                exact colour_exchange_one f hrs x
        _ = _ := by rw [Finset.sum_comm]


def rowInversions : List ℕ → ℕ
  | [] => 0
  | a :: t => a.choose 2 + rowInversions t

def rowDepthAux : ℕ → List ℕ → ℕ
  | i, [] => 0
  | i, a :: t => i * a + rowDepthAux (i+1) t

def rowDepth (l : List ℕ) := rowDepthAux 0 l

lemma choose_two_int (a : ℕ) :
    (2:ℤ) * (a.choose 2 : ℤ) = (a:ℤ) * ((a:ℤ)-1) := by
  have hq : (a.choose 2 : ℚ) = (a:ℚ) * ((a:ℚ)-1) / 2 := by
    simpa using (Nat.cast_choose_two (K := ℚ) a)
  have hq' : (2:ℚ) * (a.choose 2 : ℚ) =
        (a:ℚ) * ((a:ℚ)-1) := by linarith
  exact_mod_cast hq' 


def colGood {N k : ℕ} (v : Fin k → ℕ) (c : PlainColour N k) : Prop :=
  ∀ i, (Finset.univ.filter fun x => c x = i).card = v i

lemma colour_pair_nonneg {N k : ℕ} (v : Fin k → ℕ)
    (f : PlainColour N k → ℝ)
    (fzero : ∀ c, ¬ colGood v c → f c = 0)
    {r s : Fin k} (hrs : r ≠ s) :
    0 ≤ ∑ c : PlainColour N k, f c *
      (((v s : ℕ) : ℝ) * f c +
        ∑ x : Fin N, if c x = s then
          (∑ y : Fin N, if c y = r then
            f (colTranspose c x y) else 0) else 0) := by
  classical
  have h0 := colour_exchange_nonneg f hrs
  -- it remains only to collect the diagonal terms in each word
  refine h0.trans_eq ?_
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hg : colGood v c
  · have card_s := hg s
    let S : Fin N → ℝ := fun x =>
        ∑ y : Fin N, if c y = r then f (colTranspose c x y) else 0
    have count (z : ℝ) :
        (∑ x : Fin N, if c x = s then z else 0) = (v s : ℕ) * z := by
      rw [← card_s]
      rw [← Finset.sum_filter]
      simp
    change
      (∑ x : Fin N, if c x = s then f c * (f c + S x) else 0) =
        f c * ((v s : ℕ) * f c +
          ∑ x : Fin N, if c x = s then S x else 0)
    calc
      (∑ x : Fin N, if c x = s then f c * (f c + S x) else 0) =
        ∑ x : Fin N,
          ((if c x = s then f c * f c else 0) +
           (if c x = s then f c * S x else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hh : c x = s <;> simp [hh, mul_add]
      _ = (∑ x : Fin N, if c x = s then f c * f c else 0) +
          ∑ x : Fin N, (if c x = s then f c * S x else 0) := by
            rw [Finset.sum_add_distrib]
      _ = f c * ((v s : ℕ) * f c +
          ∑ x : Fin N, if c x = s then S x else 0) := by
            have first := count (f c * f c)
            have second :
                (∑ x : Fin N, if c x = s then f c * S x else 0) =
                  f c * ∑ x : Fin N, if c x = s then S x else 0 := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro x hx
                    by_cases hh : c x = s <;> simp [hh]
            rw [first, second]
            push_cast
            ring
  · have hfc := fzero c hg
    simp [hfc]

lemma pair_depth_sum {k : ℕ} (v : Fin k → ℕ) :
    (∑ i : Fin k, ∑ j : Fin k,
       if i < j then (v j : ℝ) else 0) =
       ∑ j : Fin k, (j.val : ℝ) * (v j : ℝ) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_filter]
  have he : (Finset.univ.filter fun i : Fin k => i < j) = Finset.Iio j := by
    ext i
    simp
  rw [he]
  simp

/-- Add the pair inequalities for all rows. -/
lemma all_colour_pairs_nonneg {N k : ℕ} (v : Fin k → ℕ)
    (f : PlainColour N k → ℝ)
    (fzero : ∀ c, ¬ colGood v c → f c = 0) :
    0 ≤ ∑ c : PlainColour N k,
      f c *
        ((∑ j : Fin k, (j.val : ℝ) * (v j : ℝ)) * f c +
          ∑ i : Fin k, ∑ j : Fin k,
            if i < j then
              (∑ x : Fin N, if c x = j then
                (∑ y : Fin N, if c y = i then
                  f (colTranspose c x y) else 0) else 0)
            else 0) := by
  classical
  -- first sum the nonnegative expressions themselves
  have hnon : 0 ≤ ∑ i : Fin k, ∑ j : Fin k,
       if hij : i < j then
         (∑ c : PlainColour N k, f c *
           (((v j : ℕ) : ℝ) * f c +
             ∑ x : Fin N, if c x = j then
               (∑ y : Fin N, if c y = i then
                 f (colTranspose c x y) else 0) else 0))
       else 0 := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split_ifs with hlt
    · exact colour_pair_nonneg v f fzero (ne_of_lt hlt)
    · simp
  refine hnon.trans_eq ?_
  rw [← pair_depth_sum v]
  -- move words out past the two row indices
  have push (i j : Fin k) :
      (if hij : i < j then
         (∑ c : PlainColour N k, f c *
           (((v j : ℕ) : ℝ) * f c +
             ∑ x : Fin N, if c x = j then
               (∑ y : Fin N, if c y = i then
                 f (colTranspose c x y) else 0) else 0))
       else 0) =
       ∑ c : PlainColour N k,
        if i < j then f c *
           (((v j : ℕ) : ℝ) * f c +
             ∑ x : Fin N, if c x = j then
               (∑ y : Fin N, if c y = i then
                 f (colTranspose c x y) else 0) else 0)
        else 0 := by
        split_ifs <;> simp
  simp_rw [push]
  let G : Fin k → Fin k → PlainColour N k → ℝ := fun i j c =>
    if i < j then f c *
       (((v j : ℕ) : ℝ) * f c +
         ∑ x : Fin N, if c x = j then
           (∑ y : Fin N, if c y = i then
             f (colTranspose c x y) else 0) else 0)
    else 0
  change (∑ i, ∑ j, ∑ c, G i j c) = _
  calc
    (∑ i, ∑ j, ∑ c, G i j c) = ∑ i, ∑ c, ∑ j, G i j c := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ i, ∑ j, G i j c := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      -- pull the common factor `f c` outside the two sums
      have pull (i j : Fin k) :
          G i j c = f c *
            (if i < j then
              (((v j : ℕ) : ℝ) * f c +
                ∑ x : Fin N, if c x = j then
                  (∑ y : Fin N, if c y = i then
                     f (colTranspose c x y) else 0) else 0)
             else 0) := by
              dsimp [G]
              by_cases h : i < j <;> simp [h]
      simp_rw [pull]
      simp_rw [← Finset.mul_sum]
      apply congrArg (fun t : ℝ => f c * t)
        (by
          have sep (i j : Fin k) :
              (if i < j then ((v j : ℕ) : ℝ) * f c +
                (∑ x : Fin N, if c x = j then
                  (∑ y : Fin N, if c y = i then f (colTranspose c x y) else 0) else 0) else 0) =
              (if i < j then ((v j : ℕ) : ℝ) else 0) * f c +
                (if i < j then (∑ x : Fin N, if c x = j then
                  (∑ y : Fin N, if c y = i then f (colTranspose c x y) else 0) else 0) else 0) := by
                by_cases h:i<j <;> simp [h]
          simp_rw [sep]
          simp_rw [Finset.sum_add_distrib]
          simp_rw [Finset.sum_mul]
          )

@[simp] lemma ospIndex_swap {n : ℕ} {a : PartitionShape n}
    (P : OrderedSetPartition a) (x y z : Fin n) :
    ospIndex (ospAct (Equiv.swap x y) P) z =
      ospIndex P (Equiv.swap x y z) := by
  classical
  rw [ospIndex_act]
  simp

lemma content_rows (i : ℕ) (l : List ℕ) :
    PartitionShape.contentSumAux i l =
      (2:ℤ) * ((rowInversions l : ℤ) - (rowDepthAux i l : ℤ)) := by
  induction l generalizing i with
  | nil => simp [PartitionShape.contentSumAux, rowInversions, rowDepthAux]
  | cons a t ih =>
    rw [PartitionShape.contentSumAux]
    simp only [rowInversions, rowDepthAux, Nat.cast_add, Nat.cast_mul]
    rw [ih]
    have htwo := choose_two_int a
    -- only casts of a single binomial coefficient remain
    push_cast
    rw [mul_sub]
    nlinarith

lemma depth_le_inversions_of_content {n : ℕ} (a : PartitionShape n)
    (h : 0 ≤ a.contentSum) : rowDepth a.parts ≤ rowInversions a.parts := by
  have hh := content_rows 0 a.parts
  change 0 ≤ PartitionShape.contentSumAux 0 a.parts at h
  rw [hh] at h
  have h' : (rowDepthAux 0 a.parts : ℤ) ≤ (rowInversions a.parts : ℤ) := by
    omega
  exact_mod_cast h'


/-- Sum over all ordered unequal coordinates. The factor of two is useful for
    avoiding any choices of representatives of transpositions. -/
noncomputable def ordSwapSum {N k : ℕ} (f : PlainColour N k → ℝ) (c : PlainColour N k) : ℝ :=
  ∑ x : Fin N, ∑ y : Fin N,
    if x ≠ y then f (colTranspose c x y) else 0

noncomputable def transSwapAve {N k : ℕ} (f : PlainColour N k → ℝ) (c : PlainColour N k) : ℝ :=
  (2:ℝ)⁻¹ * ordSwapSum f c

noncomputable def colourCross {N k : ℕ} (f : PlainColour N k → ℝ)
    (c : PlainColour N k) : ℝ :=
  ∑ i : Fin k, ∑ j : Fin k,
    if i < j then
      (∑ x : Fin N, if c x = j then
          (∑ y : Fin N, if c y = i then f (colTranspose c x y) else 0) else 0)
    else 0

def invCount (k : ℕ) (v : Fin k → ℕ) : ℕ :=
  ∑ i : Fin k, (v i).choose 2

def depthCount (k : ℕ) (v : Fin k → ℕ) : ℕ :=
  ∑ i : Fin k, i.val * v i

-- Splitting an ordinary sum into its fibres does not use any hypotheses on
-- the word. We will apply it repeatedly to two nested coordinate sums.
lemma sum_by_colour {N k : ℕ} (c : PlainColour N k) (F : Fin N → ℝ) :
    (∑ x : Fin N, F x) =
      ∑ i : Fin k, ∑ x : Fin N, if c x = i then F x else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  -- exactly the summand with index `c x` survives
  classical
  simp

lemma colTranspose_eq_self {N k : ℕ} (c : PlainColour N k)
    (x y : Fin N) (h : c x = c y) :
    colTranspose c x y = c := by
  classical
  funext z
  by_cases hx : z = x
  · subst z
    simp [colTranspose, h]
  · by_cases hy : z = y
    · subst z
      simp [colTranspose, hx, h]
    · simp [colTranspose, Equiv.swap_apply_def, hx, hy]

lemma colTranspose_comm {N k : ℕ} (c : PlainColour N k)
    (x y : Fin N) : colTranspose c x y = colTranspose c y x := by
  classical
  funext z
  change c (Equiv.swap x y z) = c (Equiv.swap y x z)
  rw [Equiv.swap_comm x y]

/-- Splitting the ordered sum simultaneously by the two colours. Indices are
    written `(i,j)` with colour `j` at `x` and colour `i` at `y`; this is the
    orientation in `all_colour_pairs_nonneg`. -/
noncomputable def colourPiece {N k : ℕ} (f : PlainColour N k → ℝ) (c : PlainColour N k)
    (i j : Fin k) : ℝ :=
  ∑ x : Fin N, if c x = j then
      (∑ y : Fin N, if c y = i then
         (if x ≠ y then f (colTranspose c x y) else 0) else 0)
    else 0

noncomputable def colourPieceOff {N k : ℕ} (f : PlainColour N k → ℝ) (c : PlainColour N k)
    (i j : Fin k) : ℝ :=
  ∑ x : Fin N, if c x = j then
      (∑ y : Fin N, if c y = i then f (colTranspose c x y) else 0)
    else 0

lemma ordSwap_split {N k : ℕ} (f : PlainColour N k → ℝ)
    (c : PlainColour N k) :
    ordSwapSum f c = ∑ i : Fin k, ∑ j : Fin k, colourPiece f c i j := by
  classical
  -- first partition each of the two coordinate sums.
  unfold ordSwapSum colourPiece
  -- for each fixed pair the singleton fibre of its actual colours remains
  -- commuting sums avoids dependent reindexing.
  calc
    (∑ x : Fin N, ∑ y : Fin N,
      if x ≠ y then f (colTranspose c x y) else 0) =
      ∑ j : Fin k, ∑ x : Fin N, if c x = j then
        (∑ y : Fin N, if x ≠ y then f (colTranspose c x y) else 0)
        else 0 := by
          -- split the outer coordinate
          simpa using
            (sum_by_colour c (fun x : Fin N =>
              ∑ y : Fin N, if x ≠ y then f (colTranspose c x y) else 0))
    _ = ∑ j : Fin k, ∑ x : Fin N, if c x = j then
          (∑ i : Fin k, ∑ y : Fin N, if c y = i then
             (if x ≠ y then f (colTranspose c x y) else 0) else 0)
        else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro x hx
          split_ifs
          · simpa using
              (sum_by_colour c (fun y : Fin N =>
                if x ≠ y then f (colTranspose c x y) else 0))
          · rfl
    _ = ∑ i : Fin k, ∑ j : Fin k, ∑ x : Fin N, if c x = j then
          (∑ y : Fin N, if c y = i then
             (if x ≠ y then f (colTranspose c x y) else 0) else 0)
        else 0 := by
          -- distribute the sum over `i` through the fibre of `x`
          calc
            (∑ j : Fin k, ∑ x : Fin N, if c x = j then
              (∑ i : Fin k, ∑ y : Fin N, if c y = i then
                 (if x ≠ y then f (colTranspose c x y) else 0) else 0)
            else 0) =
              ∑ j : Fin k, ∑ x : Fin N, ∑ i : Fin k,
                if c x = j then
                   (∑ y : Fin N, if c y = i then
                       (if x ≠ y then f (colTranspose c x y) else 0) else 0)
                else 0 := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  apply Finset.sum_congr rfl
                  intro x hx
                  by_cases h : c x = j
                  · simp [h]
                  · simp [h]
            _ = _ := by
              -- now all sums are rectangular: first commute `x` and `i`,
              -- then commute the two colour indices.
              calc
                (∑ j : Fin k, ∑ x : Fin N, ∑ i : Fin k,
                  if c x = j then
                    (∑ y : Fin N, if c y = i then
                      (if x ≠ y then f (colTranspose c x y) else 0) else 0)
                  else 0) =
                    ∑ j : Fin k, ∑ i : Fin k, ∑ x : Fin N,
                      if c x = j then
                        (∑ y : Fin N, if c y = i then
                          (if x ≠ y then f (colTranspose c x y) else 0) else 0)
                      else 0 := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        rw [Finset.sum_comm]
                _ = _ := by rw [Finset.sum_comm]
    _ = _ := rfl



lemma colourPiece_diag {N k : ℕ} (v : Fin k → ℕ)
    (f : PlainColour N k → ℝ) (c : PlainColour N k)
    (hc : colGood v c) (i : Fin k) :
    colourPiece f c i i = ((v i * (v i - 1) : ℕ) : ℝ) * f c := by
  classical
  let S : Finset (Fin N) := (Finset.univ.filter fun z : Fin N => c z = i)
  have hS : S.card = v i := hc i
  have inner (x : Fin N) (hx : c x = i) :
      (∑ y : Fin N, if c y = i then
          (if x ≠ y then f (colTranspose c x y) else 0) else 0) =
        ((v i - 1 : ℕ) : ℝ) * f c := by
    have hxS : x ∈ S := by
      dsimp [S]
      simp [hx]
    calc
      (∑ y : Fin N, if c y = i then
          (if x ≠ y then f (colTranspose c x y) else 0) else 0) =
        ∑ y ∈ S, (if x ≠ y then f (colTranspose c x y) else 0) := by
          unfold S
          exact (Finset.sum_filter _ _).symm
      _ = ∑ y ∈ S.erase x, f (colTranspose c x y) := by
          -- filter out the vanishing term `y=x`
          have hfil := (Finset.sum_filter (s := S)
            (fun y : Fin N => x ≠ y)
            (fun y : Fin N => f (colTranspose c x y)))
          -- orientation of the equation is convenient here
          simpa [Finset.filter_ne] using hfil.symm
      _ = ∑ _y ∈ S.erase x, f c := by
          apply Finset.sum_congr rfl
          intro y hy
          have hyS : y ∈ S := (Finset.mem_of_subset (Finset.erase_subset _ _) hy)
          have hyc : c y = i := (Finset.mem_filter.1 hyS).2
          have hxyc : c x = c y := hx.trans hyc.symm
          rw [colTranspose_eq_self c x y hxyc]
      _ = ((v i - 1 : ℕ) : ℝ) * f c := by
          simp [Finset.sum_const, Finset.card_erase_of_mem hxS, hS]
  unfold colourPiece
  -- there are `v i` choices for `x` as well
  calc
    (∑ x : Fin N, if c x = i then
        (∑ y : Fin N, if c y = i then
          (if x ≠ y then f (colTranspose c x y) else 0) else 0)
      else 0) =
      ∑ x ∈ S, ((v i - 1 : ℕ) : ℝ) * f c := by
        -- first restrict the outer sum to the same fibre
        have hout := (Finset.sum_filter (s := (Finset.univ : Finset (Fin N)))
          (fun x : Fin N => c x = i)
          (fun x : Fin N =>
            (∑ y : Fin N, if c y = i then
              (if x ≠ y then f (colTranspose c x y) else 0) else 0)))
        -- after the restriction replace the inner sum by its value
        rw [← hout]
        apply Finset.sum_congr rfl
        intro x hxmem
        have hxci : c x = i := (Finset.mem_filter.1 hxmem).2
        simpa using (inner x hxci)
    _ = ((v i * (v i - 1) : ℕ) : ℝ) * f c := by
        simp [Finset.sum_const, hS]
        push_cast
        ring



lemma colourPiece_ne {N k : ℕ} (f : PlainColour N k → ℝ)
    (c : PlainColour N k) {i j : Fin k} (hij : i ≠ j) :
    colourPiece f c i j = colourPieceOff f c i j := by
  classical
  unfold colourPiece colourPieceOff
  apply Finset.sum_congr rfl
  intro x hxmem
  by_cases hx : c x = j
  · simp only [hx, if_true]
    apply Finset.sum_congr rfl
    intro y hymem
    by_cases hy : c y = i
    · have hxy : x ≠ y := by
        intro he
        subst y
        exact hij (hy.symm.trans hx)
      simp [hy, hxy]
    · simp [hy]
  · simp [hx]

lemma colourPieceOff_comm {N k : ℕ} (f : PlainColour N k → ℝ)
    (c : PlainColour N k) (i j : Fin k) :
    colourPieceOff f c i j = colourPieceOff f c j i := by
  classical
  unfold colourPieceOff
  calc
    (∑ x : Fin N, if c x = j then
        (∑ y : Fin N, if c y = i then f (colTranspose c x y) else 0) else 0) =
      ∑ x : Fin N, ∑ y : Fin N,
        if c x = j then (if c y = i then f (colTranspose c x y) else 0)
        else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : c x = j <;> simp [h]
    _ = ∑ y : Fin N, ∑ x : Fin N,
        if c y = i then (if c x = j then f (colTranspose c y x) else 0)
        else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y hy
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h1 : c y = i <;>
            by_cases h2 : c x = j <;> simp [h1, h2, colTranspose_comm]
    _ = ∑ y : Fin N, if c y = i then
        (∑ x : Fin N, if c x = j then f (colTranspose c y x) else 0)
        else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases h : c y = i <;> simp [h]
    _ = _ := rfl

lemma two_choose_nat (a : ℕ) :
    2 * a.choose 2 = a * (a - 1) := by
  by_cases h : a = 0
  · simp [h]
  · have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr h
    have hz := choose_two_int a
    -- subtraction commutes with the cast once the argument is positive
    exact_mod_cast hz

lemma sum_except_fin {k : ℕ} (i : Fin k) (F : Fin k → ℝ) :
    (∑ j : Fin k, F j) = F i + ∑ j : Fin k, if i ≠ j then F j else 0 := by
  classical
  calc
    (∑ j : Fin k, F j) = F i + ∑ j ∈ (Finset.univ.erase i), F j := by
      simpa using
        (Finset.add_sum_erase (Finset.univ : Finset (Fin k))
          F (Finset.mem_univ i)).symm
    _ = _ := by
      congr 1
      -- `erase` is precisely the fibre of the predicate `i ≠ _`
      have hfil :=
        (Finset.sum_filter (s := (Finset.univ : Finset (Fin k)))
          (fun j : Fin k => i ≠ j) F)
      simpa [Finset.filter_ne] using hfil

lemma sum_offdiag_symmetric {k : ℕ} (C : Fin k → Fin k → ℝ)
    (hs : ∀ i j, C i j = C j i) :
    (∑ i : Fin k, ∑ j : Fin k, if i ≠ j then C i j else 0) =
       (2:ℝ) * ∑ i : Fin k, ∑ j : Fin k, if i < j then C i j else 0 := by
  classical
  have point (i j : Fin k) :
      (if i ≠ j then C i j else 0) =
        (if i < j then C i j else 0) +
          (if j < i then C i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · have hn : i ≠ j := ne_of_lt h
      have hr : ¬ j < i := not_lt_of_ge (le_of_lt h)
      simp [hn, h, hr]
    · subst j
      simp
    · have hn : i ≠ j := ne_of_gt h
      have hl : ¬ i < j := not_lt_of_ge (le_of_lt h)
      simp [hn, h, hl]
  simp_rw [point]
  -- separate the two triangular halves and identify them by transposing
  simp_rw [Finset.sum_add_distrib]
  have swapHalf :
      (∑ i : Fin k, ∑ j : Fin k, if j < i then C i j else 0) =
        ∑ i : Fin k, ∑ j : Fin k, if i < j then C i j else 0 := by
    -- exchange the two dummy indices
    calc
      (∑ i : Fin k, ∑ j : Fin k, if j < i then C i j else 0) =
          ∑ j : Fin k, ∑ i : Fin k, if j < i then C i j else 0 := by
            rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : i < j
        · simp [h, hs]
        · simp [h]
  rw [swapHalf]
  ring

lemma depthCount_real {k : ℕ} (v : Fin k → ℕ) :
    (∑ j : Fin k, (j.val : ℝ) * (v j : ℝ)) =
      (depthCount k v : ℝ) := by
  classical
  unfold depthCount
  push_cast
  rfl

lemma ordSwap_formula {N k : ℕ} (v : Fin k → ℕ)
    (f : PlainColour N k → ℝ) (c : PlainColour N k)
    (hc : colGood v c) :
    ordSwapSum f c = (2:ℝ) *
       (((invCount k v : ℕ) : ℝ) * f c + colourCross f c) := by
  classical
  rw [ordSwap_split]
  have splitrow (i : Fin k) :
      (∑ j : Fin k, colourPiece f c i j) =
        colourPiece f c i i +
          ∑ j : Fin k,
            if i ≠ j then colourPieceOff f c i j else 0 := by
    rw [sum_except_fin i (fun j => colourPiece f c i j)]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : i = j
    · simp [h]
    · simp [h, colourPiece_ne f c h]
  simp_rw [splitrow]
  rw [Finset.sum_add_distrib]
  have hdiag : (∑ i : Fin k, colourPiece f c i i) =
        (2:ℝ) * (invCount k v : ℝ) * f c := by
    calc
      (∑ i : Fin k, colourPiece f c i i) =
          ∑ i : Fin k, ((v i * (v i - 1) : ℕ) : ℝ) * f c := by
            apply Finset.sum_congr rfl
            intro i hi
            exact colourPiece_diag v f c hc i
      _ = ∑ i : Fin k, (((2 * (v i).choose 2 : ℕ)) : ℝ) * f c := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [two_choose_nat (v i)]
      _ = (2:ℝ) * (invCount k v : ℝ) * f c := by
            unfold invCount
            push_cast
            -- factor first the common `f c`, and then the common `2`
            rw [← Finset.sum_mul]
            rw [← Finset.mul_sum]
  rw [hdiag]
  have hoff :=
    sum_offdiag_symmetric (fun i j : Fin k => colourPieceOff f c i j)
      (fun i j => colourPieceOff_comm f c i j)
  change
    (2:ℝ) * (invCount k v : ℝ) * f c +
      (∑ i : Fin k, ∑ j : Fin k,
        if i ≠ j then colourPieceOff f c i j else 0) = _
  rw [hoff]
  -- the upper half is exactly `colourCross`
  change (2:ℝ) * (invCount k v : ℝ) * f c +
        (2:ℝ) * colourCross f c =
      (2:ℝ) * ((invCount k v : ℝ) * f c + colourCross f c)
  ring

lemma transSwapAve_formula {N k : ℕ} (v : Fin k → ℕ)
    (f : PlainColour N k → ℝ) (c : PlainColour N k)
    (hc : colGood v c) :
    transSwapAve f c = (invCount k v : ℝ) * f c + colourCross f c := by
  classical
  unfold transSwapAve
  rw [ordSwap_formula v f c hc]
  ring



lemma colour_cross_energy_nonneg {N k : ℕ} (v : Fin k → ℕ)
    (f : PlainColour N k → ℝ)
    (fzero : ∀ c, ¬ colGood v c → f c = 0) :
    0 ≤ ∑ c : PlainColour N k,
      f c * ((depthCount k v : ℝ) * f c + colourCross f c) := by
  classical
  have h := all_colour_pairs_nonneg v f fzero
  rw [← depthCount_real v] -- temporary?
  simpa [colourCross] using h

noncomputable def colourOperator {N k : ℕ} (f : PlainColour N k → ℝ)
    (c : PlainColour N k) : ℝ := f c + transSwapAve f c

lemma colour_operator_bound {N k : ℕ} (v : Fin k → ℕ)
    (hnum : depthCount k v ≤ invCount k v)
    (f : PlainColour N k → ℝ)
    (fzero : ∀ c, ¬ colGood v c → f c = 0) :
    (∑ c : PlainColour N k, f c * f c) ≤
      ∑ c : PlainColour N k, f c * colourOperator f c := by
  classical
  have hmain := colour_cross_energy_nonneg v f fzero
  let d : ℝ := (depthCount k v : ℝ)
  let q : ℝ := (invCount k v : ℝ)
  have hdq : d ≤ q := by
    dsimp [d, q]
    exact_mod_cast hnum
  have hcoef : (1:ℝ) ≤ 1 + q - d := by linarith
  have hsquares : 0 ≤ ∑ c : PlainColour N k, f c * f c := by
    apply Finset.sum_nonneg
    intro c hc
    exact mul_self_nonneg _
  have hid :
      (∑ c : PlainColour N k, f c * colourOperator f c) =
        (∑ c : PlainColour N k, f c * (d * f c + colourCross f c)) +
          (1 + q - d) * (∑ c : PlainColour N k, f c * f c) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hg : colGood v c
    · dsimp [colourOperator]
      rw [transSwapAve_formula v f c hg]
      dsimp [q, d]
      ring
    · have hz := fzero c hg
      simp [hz, colourOperator]
  -- the two summands are nonnegative, and the coefficient of the norm is at
  -- least one.
  rw [hid]
  have hmain' : 0 ≤ ∑ c : PlainColour N k,
      f c * (d * f c + colourCross f c) := by
        simpa [d] using hmain
  calc
    (∑ c : PlainColour N k, f c * f c) ≤
        (1 + q - d) * (∑ c : PlainColour N k, f c * f c) := by
          exact (le_mul_of_one_le_left hsquares hcoef)
    _ ≤ (∑ c : PlainColour N k, f c * (d * f c + colourCross f c)) +
          (1 + q - d) * (∑ c : PlainColour N k, f c * f c) := by linarith

lemma colour_operator_kernel {N k : ℕ} (v : Fin k → ℕ)
    (hnum : depthCount k v ≤ invCount k v)
    (f : PlainColour N k → ℝ)
    (fzero : ∀ c, ¬ colGood v c → f c = 0)
    (hz : ∀ c, colGood v c → colourOperator f c = 0) :
    ∀ c, f c = 0 := by
  classical
  have hbound := colour_operator_bound v hnum f fzero
  have hvan : (∑ c : PlainColour N k, f c * colourOperator f c) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    by_cases hg : colGood v c
    · simp [hz c hg]
    · simp [fzero c hg]
  rw [hvan] at hbound
  have hsum : (∑ c : PlainColour N k, f c * f c) = 0 := by
    have hn : 0 ≤ ∑ c : PlainColour N k, f c * f c := by
      apply Finset.sum_nonneg
      intro c hc
      exact mul_self_nonneg _
    linarith
  intro c
  have hle : f c * f c ≤ 0 := by
    have hnone : 0 ≤ f c * f c := mul_self_nonneg _
    -- a single summand of a zero sum of squares
    by_contra hcontra
    have hpos : 0 < f c * f c := lt_of_not_ge hcontra
    have hsumpos : 0 < ∑ z : PlainColour N k, f z * f z := by
      have hrest : 0 ≤ ∑ z ∈ (Finset.univ.erase c), f z * f z := by
        apply Finset.sum_nonneg
        intro z hzmem
        exact mul_self_nonneg _
      have hadd := (Finset.add_sum_erase (Finset.univ : Finset (PlainColour N k))
        (fun z => f z * f z) (Finset.mem_univ c)).symm
      rw [hadd]
      nlinarith
    rw [hsum] at hsumpos
    exact (lt_irrefl 0 hsumpos)
  nlinarith



lemma rowInversions_as_sum (l : List ℕ) :
    rowInversions l = ∑ i : Fin l.length, (l.get i).choose 2 := by
  induction l with
  | nil => simp [rowInversions]
  | cons a t ih =>
    rw [rowInversions]
    change a.choose 2 + rowInversions t =
      ∑ i : Fin (t.length + 1), ((a :: t).get i).choose 2
    rw [Fin.sum_univ_succ]
    simp [ih]

lemma rowDepthAux_as_sum (u : ℕ) (l : List ℕ) :
    rowDepthAux u l =
      ∑ i : Fin l.length, (u + i.val) * l.get i := by
  induction l generalizing u with
  | nil => simp [rowDepthAux]
  | cons a t ih =>
    rw [rowDepthAux]
    change u * a + rowDepthAux (u+1) t =
      ∑ i : Fin (t.length + 1), (u + i.val) * (a::t).get i
    rw [Fin.sum_univ_succ, ih]
    simp
    apply Finset.sum_congr rfl
    intro i hi
    -- `((i.succ).val) = i.val + 1`
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma rowDepth_as_sum (l : List ℕ) :
    rowDepth l = ∑ i : Fin l.length, i.val * l.get i := by
  classical
  simpa [rowDepth] using (rowDepthAux_as_sum 0 l)

lemma shape_depth_inv_counts {n : ℕ} (a : PartitionShape n)
    (hc : 0 ≤ a.contentSum) :
    depthCount a.parts.length (fun i => a.parts.get i) ≤
      invCount a.parts.length (fun i => a.parts.get i) := by
  -- this is only a change of notation from the integer content formula
  simpa [depthCount, invCount, rowDepth_as_sum, rowInversions_as_sum]
    using (depth_le_inversions_of_content a hc)



lemma swap_pair_eq {α : Type*} [DecidableEq α]
    {x y u v : α} (hxy : x ≠ y) (huv : u ≠ v)
    (h : Equiv.swap x y = Equiv.swap u v) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  have ha : (Equiv.swap u v) x = y := by
    rw [← h]
    simp
  rw [Equiv.swap_apply_def] at ha
  split_ifs at ha with hxu hxv
  · left
    exact ⟨hxu, ha.symm⟩
  · right
    exact ⟨hxv, ha.symm⟩
  · exact False.elim (hxy ha)

/-- Replacing the finite class of transpositions by all ordered pairs counts
    every transposition exactly twice. This elementary version is often more
    convenient than making an `Equiv` from unordered pairs. -/
lemma sum_transpositions_ave {N : ℕ} (H : Equiv.Perm (Fin N) → ℝ) :
    (∑ t : Equiv.Perm (Fin N),
       if t ∈ transpositionsWithOne N then H t else 0) =
      H 1 + (2:ℝ)⁻¹ *
        (∑ x : Fin N, ∑ y : Fin N,
          if x ≠ y then H (Equiv.swap x y) else 0) := by
  classical
  let S := (Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p : Fin N × Fin N => p.1 ≠ p.2)
  let U := (Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p : Fin N × Fin N => p.1 < p.2)
  -- unordered representatives are injective
  have hinj : Set.InjOn (fun p : Fin N × Fin N => Equiv.swap p.1 p.2)
      (↑U : Set (Fin N × Fin N)) := by
    intro p hp q hq he
    have hp' : p.1 < p.2 := (Finset.mem_filter.1 hp).2
    have hq' : q.1 < q.2 := (Finset.mem_filter.1 hq).2
    rcases swap_pair_eq (ne_of_lt hp') (ne_of_lt hq') he with hcase | hcase
    · exact Prod.ext hcase.1 hcase.2
    · exfalso
      have bad : p.1 < p.1 := by
        calc p.1 = q.2 := hcase.1
             _ > q.1 := hq'
             _ = p.2 := hcase.2.symm
             _ > p.1 := hp'
      exact (lt_irrefl _ bad)
  -- first describe membership in `T` using these representatives
  have imageU :
      (Finset.univ.filter fun t : Equiv.Perm (Fin N) =>
          t ∈ transpositionsWithOne N) =
        insert (1 : Equiv.Perm (Fin N)) (U.image fun p => Equiv.swap p.1 p.2) := by
    ext t
    constructor
    · intro ht
      have ht0 := (Finset.mem_filter.1 ht).2
      rcases ht0 with he | ⟨x,y,hxy,rfl⟩
      · subst t; simp
      · by_cases hlt : x < y
        · have hp : (x,y) ∈ U := by simp [U, hlt]
          have : Equiv.swap x y ∈ U.image (fun p : Fin N × Fin N => Equiv.swap p.1 p.2) :=
            Finset.mem_image.2 ⟨(x,y), hp, rfl⟩
          simp [this]
        · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hlt) hxy.symm
          have hp : (y,x) ∈ U := by simp [U, hyx]
          have hh : Equiv.swap x y = Equiv.swap y x := Equiv.swap_comm x y
          have : Equiv.swap x y ∈ U.image (fun p : Fin N × Fin N => Equiv.swap p.1 p.2) :=
            Finset.mem_image.2 ⟨(y,x), hp, hh.symm⟩
          simp [this]
    · intro ht
      have hm : t = 1 ∨ t ∈ U.image (fun p : Fin N × Fin N => Equiv.swap p.1 p.2) := by
        simpa using ht
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hm with rfl | hm
      · exact Or.inl rfl
      · rcases Finset.mem_image.1 hm with ⟨p,hp,rfl⟩
        exact Or.inr ⟨p.1,p.2, ne_of_lt ((Finset.mem_filter.1 hp).2), rfl⟩
  have hnot : (1 : Equiv.Perm (Fin N)) ∉
      U.image (fun p : Fin N × Fin N => Equiv.swap p.1 p.2) := by
    intro hm
    rcases Finset.mem_image.1 hm with ⟨p,hp,he⟩
    have hp' : p.1 ≠ p.2 := ne_of_lt ((Finset.mem_filter.1 hp).2)
    have : Equiv.swap p.1 p.2 ≠ (1 : Equiv.Perm (Fin N)) :=
      (not_congr Equiv.swap_eq_one_iff).2 hp'
    exact this he
  -- the ordered list is twice the unordered list
  have hdouble :
      (∑ x : Fin N, ∑ y : Fin N, if x ≠ y then H (Equiv.swap x y) else 0) =
        (2:ℝ) * ∑ p ∈ U, H (Equiv.swap p.1 p.2) := by
    -- split ordered pairs into the two half-planes
    have hx :
      (∑ x : Fin N, ∑ y : Fin N, if x ≠ y then H (Equiv.swap x y) else 0) =
        ∑ p ∈ S, H (Equiv.swap p.1 p.2) := by
      -- turn the double sum into a sum over products and filter
      classical
      calc
        (∑ x : Fin N, ∑ y : Fin N, if x ≠ y then H (Equiv.swap x y) else 0) =
           ∑ p : Fin N × Fin N,
             (if p.1 ≠ p.2 then H (Equiv.swap p.1 p.2) else 0) := by
               rw [Fintype.sum_prod_type]
        _ = _ := by
             unfold S
             exact (Finset.sum_filter _ _).symm
    rw [hx]
    -- the involution reversing a pair exchanges the two halves
    let rev : (Fin N × Fin N) ≃ (Fin N × Fin N) := Equiv.prodComm _ _
    have hsumgt :
        (∑ p ∈ (Finset.univ.filter fun p : Fin N × Fin N => p.2 < p.1),
              H (Equiv.swap p.1 p.2)) =
          ∑ p ∈ U, H (Equiv.swap p.1 p.2) := by
      -- reindex by `rev`
      let e : {p // p ∈ (Finset.univ.filter fun p : Fin N × Fin N => p.2 < p.1)} ≃
          {p // p ∈ U} :=
        { toFun := fun p => ⟨(p.1.2, p.1.1), by
              have hp := (Finset.mem_filter.1 p.2).2
              exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩⟩
          invFun := fun p => ⟨(p.1.2, p.1.1), by
              have hp := (Finset.mem_filter.1 p.2).2
              exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩⟩
          left_inv := by intro p; cases p; rfl
          right_inv := by intro p; cases p; rfl }
      rw [Finset.sum_subtype
            (Finset.univ.filter fun p : Fin N × Fin N => p.2 < p.1)
            (fun x => Iff.rfl)]
      rw [Finset.sum_subtype U (fun x => Iff.rfl)]
      change (∑ p : {p // p ∈ (Finset.univ.filter fun p : Fin N × Fin N => p.2 < p.1)},
           H (Equiv.swap p.1.1 p.1.2)) =
         ∑ p : {p // p ∈ U}, H (Equiv.swap p.1.1 p.1.2)
      refine Fintype.sum_equiv e _ _ ?_
      intro p
      dsimp [e]
      rw [Equiv.swap_comm]
    -- partition S into the two strict half-planes
    have hsplit :
        (∑ p ∈ S, H (Equiv.swap p.1 p.2)) =
          (∑ p ∈ U, H (Equiv.swap p.1 p.2)) +
          (∑ p ∈ (Finset.univ.filter fun p : Fin N × Fin N => p.2 < p.1),
             H (Equiv.swap p.1 p.2)) := by
      -- all summations may be taken over `univ`
      unfold S U
      simp_rw [Finset.sum_filter]
      -- check a pair according to the linear order of its coordinates
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · have hn : p.1 ≠ p.2 := ne_of_lt h
        have hr : ¬ p.2 < p.1 := not_lt_of_ge (le_of_lt h)
        simp [h, hn, hr]
      · simp [h]
      · have hn : p.1 ≠ p.2 := ne_of_gt h
        have hl : ¬ p.1 < p.2 := not_lt_of_ge (le_of_lt h)
        simp [h, hn, hl]
    rw [hsplit, hsumgt]
    ring
  -- finally sum over the image, using injectivity on U
  classical
  calc
    (∑ t : Equiv.Perm (Fin N),
       if t ∈ transpositionsWithOne N then H t else 0) =
        ∑ t ∈ (Finset.univ.filter fun t : Equiv.Perm (Fin N) =>
          t ∈ transpositionsWithOne N), H t := by
            exact (Finset.sum_filter _ _).symm
    _ = H 1 + ∑ t ∈ U.image (fun p : Fin N × Fin N => Equiv.swap p.1 p.2), H t := by
            rw [imageU, Finset.sum_insert hnot]
    _ = H 1 + ∑ p ∈ U, H (Equiv.swap p.1 p.2) := by
            rw [Finset.sum_image]
            intro p hp q hq he
            exact hinj hp hq he
    _ = _ := by rw [hdouble]; ring


noncomputable def partitionOperator {n : ℕ} {a : PartitionShape n}
    (F : OrderedSetPartition a → ℝ) (Q : OrderedSetPartition a) : ℝ :=
  ∑ t : Equiv.Perm (Fin n), if t ∈ transpositionsWithOne n then
       F (ospAct t Q) else 0

lemma partition_operator_kernel {n : ℕ} {a : PartitionShape n}
    (hc : 0 ≤ a.contentSum)
    (F : OrderedSetPartition a → ℝ)
    (hz : ∀ Q, partitionOperator F Q = 0) :
    ∀ Q, F Q = 0 := by
  classical
  let v : Fin a.parts.length → ℕ := fun i => a.parts.get i
  let f : PlainColour n a.parts.length → ℝ := fun c =>
     if h : colGood v c then F (colourPartition ⟨c,h⟩) else 0
  have fbad : ∀ c, ¬ colGood v c → f c = 0 := by
    intro c h; simp [f,h]
  have fgood (c : Colourings n a.parts.length (fun i => a.parts.get i)) :
      f c.1 = F (colourPartition c) := by
    simp [f, v, colGood, c.2]
  have fact (Q : OrderedSetPartition a) (x y : Fin n) :
       f (colTranspose (ospColour Q).1 x y) =
         F (ospAct (Equiv.swap x y) Q) := by
    have heq : (colTranspose (ospColour Q).1 x y) =
          (ospColour (ospAct (Equiv.swap x y) Q)).1 := by
      funext z
      -- both sides record the unique colour after the swap
      symm
      exact ospIndex_swap Q x y z
    rw [heq, fgood]
    simp
  have hnum : depthCount a.parts.length v ≤ invCount a.parts.length v := by
    exact shape_depth_inv_counts a hc
  have zgood : ∀ c, colGood v c → colourOperator f c = 0 := by
    intro c h
    let C : Colourings n a.parts.length (fun i => a.parts.get i) :=
      ⟨c, h⟩
    let Q : OrderedSetPartition a := colourPartition C
    have hCQ : (ospColour Q).1 = c := by
      have hh := ospColour_colourPartition C
      exact congrArg Subtype.val hh
    have hsum := sum_transpositions_ave
       (fun t : Equiv.Perm (Fin n) => F (ospAct t Q))
    have hzQ := hz Q
    unfold partitionOperator at hzQ
    rw [hsum] at hzQ
    change colourOperator f c = 0
    dsimp [colourOperator, transSwapAve, ordSwapSum]
    have hone : f c = F Q := by
      change f C.1 = F (colourPartition C)
      exact fgood C
    -- replace each transposed word by the corresponding action
    have heach (x y : Fin n) :
       f (colTranspose c x y) = F (ospAct (Equiv.swap x y) Q) := by
      rw [← hCQ]
      exact fact Q x y
    rw [hone]
    have :
      (∑ x : Fin n, ∑ y : Fin n,
          if x ≠ y then f (colTranspose c x y) else 0) =
        (∑ x : Fin n, ∑ y : Fin n,
          if x ≠ y then F (ospAct (Equiv.swap x y) Q) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hxy : x ≠ y <;> simp [hxy, heach]
    rw [this]
    simpa using hzQ
  have hall := colour_operator_kernel v hnum f fbad zgood
  intro Q
  have hq := hall (ospColour Q).1
  simpa [fgood] using hq


lemma partition_operator_injective {n:ℕ}{a:PartitionShape n}
    (hc:0 ≤ a.contentSum) (F G : OrderedSetPartition a → ℝ)
    (h : ∀ Q, partitionOperator F Q = partitionOperator G Q) : F = G := by
  classical
  let D : OrderedSetPartition a → ℝ := fun P => F P - G P
  have hzero : ∀ Q, partitionOperator D Q = 0 := by
    intro Q
    change (∑ x : Equiv.Perm (Fin n), if x ∈ transpositionsWithOne n then
       F (ospAct x Q) - G (ospAct x Q) else 0) = 0
    calc
      _ = (∑ x : Equiv.Perm (Fin n), if x ∈ transpositionsWithOne n then
         F (ospAct x Q) else 0) -
          (∑ x : Equiv.Perm (Fin n), if x ∈ transpositionsWithOne n then
         G (ospAct x Q) else 0) := by
           rw [← Finset.sum_sub_distrib]
           apply Finset.sum_congr rfl
           intro x hx
           by_cases hh : x ∈ transpositionsWithOne n <;> simp [hh]
      _ = 0 := sub_eq_zero.mpr (h Q)
  have z := partition_operator_kernel hc D hzero
  funext Q
  have := z Q
  dsimp [D] at this
  exact sub_eq_zero.mp this


/-- Every member of the little ball `1 + transpositions` is its own inverse.
    This is the reason the elementary convolution below uses `t * y` although
    the permutation action on functions is contravariant. -/
lemma transpositionsWithOne_mul_self {n : ℕ}
    {t : Equiv.Perm (Fin n)} (ht : t ∈ transpositionsWithOne n) : t * t = 1 := by
  classical
  rcases ht with h | ⟨i,j,hij,rfl⟩
  · simp [h]
  · simpa using (Equiv.swap_mul_self i j)

/-- The multiplication table of a tiling is literally a bijection. -/
noncomputable def tilingMulEquiv {G : Type*} [Group G]
    (X Y : Set G) (h : IsTiling X Y) : (X × Y) ≃ G := by
  classical
  let m : X × Y → G := fun p => (p.1 : G) * (p.2 : G)
  apply Equiv.ofBijective m
  constructor
  · intro p q hpq
    -- uniqueness in the fibre over `m p`
    have hp : m p = m p := rfl
    have hq : m q = m p := hpq.symm ▸ rfl
    rcases h (m p) with ⟨w, hw, hu⟩
    -- `hu` chooses the same pair for every proof of belonging to this fibre
    exact (hu p hp).trans (hu q hq).symm
  · intro g
    rcases h g with ⟨p,hp,hu⟩
    exact ⟨p, hp⟩

/-- Turning a sum with a `Set` indicator into a sum over the subtype of the
    set. All the subtypes in the sequel are finite. -/
lemma sum_indicator_subtype {ι : Type*} [Fintype ι]
    (S : Set ι) (H : ι → ℝ) :
    (∑ x : ι, if x ∈ S then H x else 0) = ∑ x : S, H x := by
  classical
  -- the finite subtype instance is supplied by the ambient `Fintype`
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter fun x : ι => x ∈ S)
    (by intro x; simp) H

/-- Convolution of the fibre-counting vector with the transposition ball.
    The tiling bijection says that it simply counts *all* permutations taking
    `P` to `Q`. This is the only use of the tiling hypothesis in the linear
    argument. -/
lemma partition_count_operator {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    (a : PartitionShape n) (h : IsTiling (transpositionsWithOne n) Y)
    (P Q : OrderedSetPartition a) :
    partitionOperator
      (fun R : OrderedSetPartition a =>
        ∑ y : {y : Equiv.Perm (Fin n) // y ∈ Y},
          if ospAct (y : Equiv.Perm (Fin n)) P = R then (1:ℝ) else 0) Q
      = ∑ g : Equiv.Perm (Fin n),
          if ospAct g P = Q then (1:ℝ) else 0 := by
  classical
  -- abbreviate the two subtypes. Lean's subtype products are precisely the
  -- pairs occurring in `IsTiling`.
  let X : Set (Equiv.Perm (Fin n)) := transpositionsWithOne n
  let e : (X × Y) ≃ Equiv.Perm (Fin n) := tilingMulEquiv X Y h
  -- first replace the sum over all `t` by the sum over its finite subtype
  change
    (∑ t : Equiv.Perm (Fin n), if t ∈ transpositionsWithOne n then
       (∑ y : {y : Equiv.Perm (Fin n) // y ∈ Y},
          if ospAct (y : Equiv.Perm (Fin n)) P = ospAct t Q then (1:ℝ) else 0)
       else 0) = _
  rw [sum_indicator_subtype (transpositionsWithOne n)
        (fun t : Equiv.Perm (Fin n) =>
          ∑ y : {y : Equiv.Perm (Fin n) // y ∈ Y},
            if ospAct (y : Equiv.Perm (Fin n)) P = ospAct t Q then (1:ℝ) else 0)]
  -- a member of `T` is an involution; hence the displayed equality of
  -- partitions can be multiplied by it on the left.
  have iff_mul (t : {t : Equiv.Perm (Fin n) // t ∈ transpositionsWithOne n})
      (y : {y : Equiv.Perm (Fin n) // y ∈ Y}) :
      ospAct (y : Equiv.Perm (Fin n)) P = ospAct (t : Equiv.Perm (Fin n)) Q ↔
        ospAct ((t : Equiv.Perm (Fin n)) * (y : Equiv.Perm (Fin n))) P = Q := by
    have hi : (t : Equiv.Perm (Fin n)) * (t : Equiv.Perm (Fin n)) = 1 :=
      transpositionsWithOne_mul_self t.property
    constructor
    · intro hp
      calc
        ospAct ((t : Equiv.Perm (Fin n)) * (y : Equiv.Perm (Fin n))) P =
            ospAct (t : Equiv.Perm (Fin n))
              (ospAct (y : Equiv.Perm (Fin n)) P) :=
                (ospAct_mul _ _ _).symm
        _ = ospAct (t : Equiv.Perm (Fin n))
              (ospAct (t : Equiv.Perm (Fin n)) Q) := by rw [hp]
        _ = Q := by rw [ospAct_mul, hi]; simp
    · intro hp
      -- apply the same involution once more
      have hh := congrArg
        (fun R : OrderedSetPartition a => ospAct (t : Equiv.Perm (Fin n)) R) hp
      -- after two copies of `t` nothing remains
      simpa [ospAct_mul, ← mul_assoc, hi] using hh
  -- use `iff_mul` in every summand, then flatten the double sum to the
  -- product subtype and use the tiling bijection.
  calc
    (∑ t : {t : Equiv.Perm (Fin n) // t ∈ transpositionsWithOne n},
       ∑ y : {y : Equiv.Perm (Fin n) // y ∈ Y},
        if ospAct (y : Equiv.Perm (Fin n)) P =
              ospAct (t : Equiv.Perm (Fin n)) Q then (1:ℝ) else 0) =
      ∑ p : ({t : Equiv.Perm (Fin n) // t ∈ transpositionsWithOne n}) ×
              ({y : Equiv.Perm (Fin n) // y ∈ Y}),
         if ospAct ((p.1 : Equiv.Perm (Fin n)) * (p.2 : Equiv.Perm (Fin n))) P = Q
              then (1:ℝ) else 0 := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hh : ospAct (y : Equiv.Perm (Fin n)) P =
              ospAct (t : Equiv.Perm (Fin n)) Q
        · simp [hh, (iff_mul t y).1 hh]
        · have hn : ¬ ospAct ((t : Equiv.Perm (Fin n)) *
                    (y : Equiv.Perm (Fin n))) P = Q := by
                    intro hz; exact hh ((iff_mul t y).2 hz)
          simp [hh, hn]
    _ = ∑ g : Equiv.Perm (Fin n), if ospAct g P = Q then (1:ℝ) else 0 := by
        -- the definition of the equivalence just multiplies the pair
        -- First make the definitional `X` match the displayed subtype.
        change (∑ p : X × Y,
          if ospAct ((p.1 : Equiv.Perm (Fin n)) * (p.2 : Equiv.Perm (Fin n))) P = Q
            then (1:ℝ) else 0) = _
        refine Fintype.sum_equiv e _ _ ?_
        intro p
        rfl

/-- In the transitive permutation action on ordered set partitions, the full
    symmetric group has the same fibre size at every target. -/
lemma full_partition_count_target {n : ℕ} {a : PartitionShape n}
    (P Q R : OrderedSetPartition a) :
    (∑ g : Equiv.Perm (Fin n), if ospAct g P = Q then (1:ℝ) else 0) =
    (∑ g : Equiv.Perm (Fin n), if ospAct g P = R then (1:ℝ) else 0) := by
  classical
  rcases partition_transitive_action Q R with ⟨s, hs⟩
  let B : Equiv.Perm (Fin n) → ℝ := fun g =>
        if ospAct g P = R then (1:ℝ) else 0
  have heach (g : Equiv.Perm (Fin n)) :
      (if ospAct g P = Q then (1:ℝ) else 0) = B (s * g) := by
    have hiff : ospAct g P = Q ↔ ospAct (s * g) P = R := by
      constructor
      · intro hq
        rw [← hs]
        rw [← hq]
        exact (ospAct_mul _ _ _).symm
      · intro hr
        -- cancel the bijection `ospAct s` on partitions
        have hr' : ospAct s (ospAct g P) = ospAct s Q := by
          rw [ospAct_mul]
          rw [hr, hs]
        -- apply the inverse action
        have hh := congrArg
          (fun Z : OrderedSetPartition a => ospAct s⁻¹ Z) hr'
        simpa using hh
    dsimp [B]
    by_cases hg : ospAct g P = Q
    · simp [hg, hiff.1 hg]
    · have hn : ¬ ospAct (s * g) P = R := by
          intro hz; exact hg (hiff.2 hz)
      simp [hg, hn]
  calc
    (∑ g : Equiv.Perm (Fin n), if ospAct g P = Q then (1:ℝ) else 0) =
        ∑ g : Equiv.Perm (Fin n), B ((Equiv.mulLeft s) g) := by
          apply Finset.sum_congr rfl
          intro g hg
          simpa using (heach g)
    _ = ∑ g : Equiv.Perm (Fin n), B g := Equiv.sum_comp (Equiv.mulLeft s) B
    _ = _ := rfl

/-- Moving the source instead of the target is a right multiplication. -/
lemma full_partition_count_source {n : ℕ} {a : PartitionShape n}
    (P P' Q : OrderedSetPartition a) :
    (∑ g : Equiv.Perm (Fin n), if ospAct g P' = Q then (1:ℝ) else 0) =
    (∑ g : Equiv.Perm (Fin n), if ospAct g P = Q then (1:ℝ) else 0) := by
  classical
  rcases partition_transitive_action P P' with ⟨s, hs⟩
  let B : Equiv.Perm (Fin n) → ℝ := fun g =>
      if ospAct g P = Q then (1:ℝ) else 0
  have heach (g : Equiv.Perm (Fin n)) :
      (if ospAct g P' = Q then (1:ℝ) else 0) = B (g * s) := by
    have hh : ospAct g P' = ospAct (g * s) P := by
      rw [← hs]
      exact ospAct_mul _ _ _
    dsimp [B]
    rw [hh]
  calc
    (∑ g : Equiv.Perm (Fin n), if ospAct g P' = Q then (1:ℝ) else 0) =
        ∑ g : Equiv.Perm (Fin n), B ((Equiv.mulRight s) g) := by
          apply Finset.sum_congr rfl
          intro g hg
          simpa using (heach g)
    _ = ∑ g : Equiv.Perm (Fin n), B g := Equiv.sum_comp (Equiv.mulRight s) B
    _ = _ := rfl



noncomputable def yPartitionCount {n : ℕ} (Y : Set (Equiv.Perm (Fin n)))
    {a : PartitionShape n} (P Q : OrderedSetPartition a) : ℝ :=
  ∑ y : {y : Equiv.Perm (Fin n) // y ∈ Y},
       if ospAct (y : Equiv.Perm (Fin n)) P = Q then (1:ℝ) else 0

noncomputable def allPartitionCount {n : ℕ}
    {a : PartitionShape n} (P Q : OrderedSetPartition a) : ℝ :=
  ∑ g : Equiv.Perm (Fin n),
       if ospAct g P = Q then (1:ℝ) else 0

noncomputable def transBallSize (n : ℕ) : ℝ :=
  (Fintype.card {t : Equiv.Perm (Fin n) // t ∈ transpositionsWithOne n} : ℕ)

lemma transBallSize_pos (n : ℕ) : 0 < transBallSize n := by
  classical
  have hmem : (1 : Equiv.Perm (Fin n)) ∈ transpositionsWithOne n := Or.inl rfl
  have hn : 0 < Fintype.card
       {t : Equiv.Perm (Fin n) // t ∈ transpositionsWithOne n} :=
    Fintype.card_pos_iff.mpr ⟨⟨1, hmem⟩⟩
  unfold transBallSize
  exact_mod_cast hn

lemma partition_count_operator' {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    {a : PartitionShape n}
    (h : IsTiling (transpositionsWithOne n) Y) (P Q : OrderedSetPartition a) :
    partitionOperator (fun R : OrderedSetPartition a => yPartitionCount Y P R) Q
      = allPartitionCount P Q := by
  classical
  simpa [yPartitionCount, allPartitionCount] using
    (partition_count_operator a h P Q)

lemma allPartitionCount_target {n : ℕ} {a : PartitionShape n}
    (P Q R : OrderedSetPartition a) :
    allPartitionCount P Q = allPartitionCount P R := by
  classical
  simpa [allPartitionCount] using (full_partition_count_target P Q R)

lemma allPartitionCount_source {n : ℕ} {a : PartitionShape n}
    (P P' Q : OrderedSetPartition a) :
    allPartitionCount P' Q = allPartitionCount P Q := by
  classical
  simpa [allPartitionCount] using (full_partition_count_source P P' Q)

/-- The injective transposition operator forces every `Y`-fibre to be the
    formal quotient of the full-group fibre by the size of the ball. We use
    this real equality only to compare natural counts, not to divide natural
    numbers. -/
lemma yPartitionCount_eq_div {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    {a : PartitionShape n} (hc : 0 ≤ a.contentSum)
    (h : IsTiling (transpositionsWithOne n) Y)
    (P Q : OrderedSetPartition a) :
    yPartitionCount Y P Q = allPartitionCount P Q / transBallSize n := by
  classical
  let A : OrderedSetPartition a → ℝ := fun R => yPartitionCount Y P R
  let b : ℝ := allPartitionCount P Q / transBallSize n
  let B : OrderedSetPartition a → ℝ := fun _ => b
  have hopA (R : OrderedSetPartition a) :
      partitionOperator A R = allPartitionCount P R := by
    dsimp [A]
    exact partition_count_operator' h P R
  have hconst (R : OrderedSetPartition a) :
      allPartitionCount P R = allPartitionCount P Q :=
    allPartitionCount_target P R Q
  have hopB (R : OrderedSetPartition a) :
      partitionOperator B R = allPartitionCount P Q := by
    -- a constant function is multiplied by the cardinality of the ball
    unfold partitionOperator
    change (∑ t : Equiv.Perm (Fin n),
      if t ∈ transpositionsWithOne n then b else 0) = _
    rw [sum_indicator_subtype (transpositionsWithOne n)
          (fun _ : Equiv.Perm (Fin n) => b)]
    -- the remaining finite sum has a constant summand
    simp only [Finset.sum_const, nsmul_eq_mul]
    change (Fintype.card
        {t : Equiv.Perm (Fin n) // t ∈ transpositionsWithOne n} : ℝ) * b = _
    dsimp [b]
    have hp : (transBallSize n) ≠ 0 := ne_of_gt (transBallSize_pos n)
    -- `transBallSize` is just this casted card
    change (transBallSize n) *
        (allPartitionCount P Q / transBallSize n) = allPartitionCount P Q
    field_simp
  have hs : ∀ R : OrderedSetPartition a,
      partitionOperator A R = partitionOperator B R := by
    intro R
    rw [hopA R, hopB R, hconst R]
  have hAB : A = B := partition_operator_injective hc A B hs
  have hval := congrFun hAB Q
  change yPartitionCount Y P Q = b at hval
  simpa [b] using hval

lemma yPartitionCount_all_eq {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    {a : PartitionShape n} (hc : 0 ≤ a.contentSum)
    (h : IsTiling (transpositionsWithOne n) Y)
    (P Q P' Q' : OrderedSetPartition a) :
    yPartitionCount Y P Q = yPartitionCount Y P' Q' := by
  classical
  rw [yPartitionCount_eq_div hc h P Q,
      yPartitionCount_eq_div hc h P' Q']
  -- the full group fibres do not see either the source or the target
  have h1 : allPartitionCount P Q = allPartitionCount P Q' :=
    allPartitionCount_target P Q Q'
  have h2 : allPartitionCount P' Q' = allPartitionCount P Q' :=
    allPartitionCount_source P P' Q'
  rw [h1, h2]


lemma sends_ncard_real {n : ℕ} (Y : Set (Equiv.Perm (Fin n)))
    {a : PartitionShape n} (P Q : OrderedSetPartition a) :
    ({g : Equiv.Perm (Fin n) | g ∈ Y ∧ SendsPartition g P Q}.ncard : ℝ)
       = yPartitionCount Y P Q := by
  classical
  -- express a finite set's card as the sum of its indicator
  have hc :
      ({g : Equiv.Perm (Fin n) | g ∈ Y ∧ SendsPartition g P Q}.ncard : ℝ) =
        ∑ g : Equiv.Perm (Fin n),
          if (g ∈ Y ∧ SendsPartition g P Q) then (1:ℝ) else 0 := by
    rw [Set.ncard_eq_toFinset_card'
          {g : Equiv.Perm (Fin n) | g ∈ Y ∧ SendsPartition g P Q}]
    rw [Set.toFinset_setOf]
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [hc]
  unfold yPartitionCount
  rw [← sum_indicator_subtype Y
        (fun g : Equiv.Perm (Fin n) =>
            if ospAct g P = Q then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro g hg
  by_cases hy : g ∈ Y
  · by_cases he : ospAct g P = Q
    · have hs : SendsPartition g P Q := (sends_iff_act g P Q).2 he
      simp [hy, he, hs]
    · have hs : ¬ SendsPartition g P Q := by
          intro hz
          exact he ((sends_iff_act g P Q).1 hz)
      simp [hy, he, hs]
  · simp [hy]

end LeanEval.Combinatorics.FangXiaTilingProblem
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem fang_xia_partition_transitive_of_tiling {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    (_h : IsTiling (transpositionsWithOne n) Y) :
    ∀ lam : PartitionShape n, 0 ≤ lam.contentSum → IsPartitionTransitive Y lam :=
/-ResultProofBegin-/by
  classical
  intro lam hc
  -- There is no spectral step at all when the shape has one block.  Keeping
  -- this case out also avoids a harmless empty-colour convention later on.
  by_cases hz : lam.parts.length ≤ 1
  · letI : Subsingleton (OrderedSetPartition lam) :=
      LeanEval.Combinatorics.FangXiaTilingProblem.osp_subsingleton_of_length_le_one hz
    exact
      LeanEval.Combinatorics.FangXiaTilingProblem.partitionTransitive_of_subsingleton
        (LeanEval.Combinatorics.FangXiaTilingProblem.tiling_Y_nonempty _h)
  · -- All the remaining work is a finite convolution on the permutation
    -- representation.  We do not need to manufacture a partition to run it:
    -- the (impossible in fact) empty action is vacuous.
    rcases isEmpty_or_nonempty (OrderedSetPartition lam) with hemp | hnon
    · letI : IsEmpty (OrderedSetPartition lam) := hemp
      refine ⟨1, by decide, ?_⟩
      intro P Q
      exact isEmptyElim P
    · -- fix one source and one actually hit target. Its nonempty fibre
      -- supplies the positive integer in the statement.
      let P0 : OrderedSetPartition lam := Classical.choice hnon
      obtain ⟨y0, hy0⟩ :=
        LeanEval.Combinatorics.FangXiaTilingProblem.tiling_Y_nonempty _h
      let Q0 : OrderedSetPartition lam :=
        LeanEval.Combinatorics.FangXiaTilingProblem.ospAct y0 P0
      let r : ℕ :=
        {g : Equiv.Perm (Fin n) |
          g ∈ Y ∧ SendsPartition g P0 Q0}.ncard
      have hs0 : SendsPartition y0 P0 Q0 :=
        (LeanEval.Combinatorics.FangXiaTilingProblem.sends_iff_act y0 P0 Q0).2 (by
          rfl)
      have hrpos : 0 < r := by
        dsimp [r]
        apply (Set.ncard_pos (Set.toFinite _)).2
        exact ⟨y0, hy0, hs0⟩
      refine ⟨r, hrpos, ?_⟩
      intro P Q
      have heq :
          LeanEval.Combinatorics.FangXiaTilingProblem.yPartitionCount Y P Q =
            LeanEval.Combinatorics.FangXiaTilingProblem.yPartitionCount Y P0 Q0 :=
        LeanEval.Combinatorics.FangXiaTilingProblem.yPartitionCount_all_eq
           hc _h P Q P0 Q0
      have hleft :=
        LeanEval.Combinatorics.FangXiaTilingProblem.sends_ncard_real Y P Q
      have hright :=
        LeanEval.Combinatorics.FangXiaTilingProblem.sends_ncard_real Y P0 Q0
      have hcast :
          ({g : Equiv.Perm (Fin n) |
             g ∈ Y ∧ SendsPartition g P Q}.ncard : ℝ) =
          ({g : Equiv.Perm (Fin n) |
             g ∈ Y ∧ SendsPartition g P0 Q0}.ncard : ℝ) :=
        hleft.trans (heq.trans hright.symm)
      have hnat :
          {g : Equiv.Perm (Fin n) |
             g ∈ Y ∧ SendsPartition g P Q}.ncard =
          {g : Equiv.Perm (Fin n) |
             g ∈ Y ∧ SendsPartition g P0 Q0}.ncard :=
        (Nat.cast_inj.mp hcast)
      simpa [r] using hnat/-ResultProofEnd-/
/-ResultEnd-/

end Submission
