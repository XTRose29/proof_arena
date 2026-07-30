import Submission.Connected

namespace Submission.CantorClassification

noncomputable section

open Function Set Topology TopologicalSpace
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [TotallyDisconnectedSpace X] [PerfectSpace X]

lemma exists_nontrivial_clopen_split (C : Clopens X) (hC : (C : Set X).Nonempty) :
    ∃ A B : Clopens X, (A : Set X).Nonempty ∧ (B : Set X).Nonempty ∧
      Disjoint (A : Set X) B ∧ (A : Set X) ∪ B = C ∧
      (A : Set X) ⊆ C ∧ (B : Set X) ⊆ C := by
  obtain ⟨x, hxC⟩ := hC
  have hpre : Preperfect (C : Set X) := C.isOpen.preperfect
  rw [preperfect_iff_nhds] at hpre
  obtain ⟨y, hy, hyx⟩ := hpre x hxC C (C.isOpen.mem_nhds hxC)
  have hyC : y ∈ (C : Set X) := hy.2
  have hxU : x ∈ (C : Set X) \ {y} := ⟨hxC, by simpa [ne_comm] using hyx⟩
  obtain ⟨A, hA, hxA, hAC⟩ := exists_clopen_of_closed_subset_open
    (Z := {x}) (U := (C : Set X) \ {y}) isClosed_singleton
    (C.isOpen.sdiff isClosed_singleton) (by simpa using hxU)
  let A' : Clopens X := ⟨A, hA⟩
  let B' : Clopens X := ⟨(C : Set X) ∩ Aᶜ, C.isClopen.inter hA.compl⟩
  refine ⟨A', B', ⟨x, hxA (Set.mem_singleton x)⟩, ⟨y, hyC, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro hyA
    exact (hAC hyA).2 (Set.mem_singleton y)
  · exact disjoint_compl_right.mono_right Set.inter_subset_right
  · ext z
    constructor
    · rintro (hzA | ⟨hzC, -⟩)
      · exact (hAC hzA).1
      · exact hzC
    · intro hzC
      by_cases hzA : z ∈ A
      · exact Or.inl hzA
      · exact Or.inr ⟨hzC, hzA⟩
  · exact hAC.trans Set.sdiff_subset
  · exact Set.inter_subset_left

structure SplitData (C : Clopens X) (E : Clopens X) where
  left : Clopens X
  right : Clopens X
  left_nonempty : (left : Set X).Nonempty
  right_nonempty : (right : Set X).Nonempty
  disjoint : Disjoint (left : Set X) right
  cover : (left : Set X) ∪ right = C
  left_subset : (left : Set X) ⊆ C
  right_subset : (right : Set X) ⊆ C
  left_decides : (left : Set X) ⊆ E ∨ (left : Set X) ⊆ (E : Set X)ᶜ
  right_decides : (right : Set X) ⊆ E ∨ (right : Set X) ⊆ (E : Set X)ᶜ

lemma splitData_nonempty (C E : Clopens X) (hC : (C : Set X).Nonempty) :
    Nonempty (SplitData C E) := by
  by_cases hCE : ((C : Set X) ∩ E).Nonempty
  · by_cases hCEc : ((C : Set X) ∩ (E : Set X)ᶜ).Nonempty
    · let A : Clopens X := ⟨(C : Set X) ∩ E, C.isClopen.inter E.isClopen⟩
      let B : Clopens X := ⟨(C : Set X) ∩ (E : Set X)ᶜ, C.isClopen.inter E.isClopen.compl⟩
      refine ⟨⟨A, B, hCE, hCEc, ?_, ?_, Set.inter_subset_left, Set.inter_subset_left,
        Or.inl Set.inter_subset_right, Or.inr Set.inter_subset_right⟩⟩
      · exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right disjoint_compl_right
      · simp [A, B]
    · obtain ⟨A, B, hA, hB, hAB, hcover, hAC, hBC⟩ :=
        exists_nontrivial_clopen_split C hC
      have hCsub : (C : Set X) ⊆ E := by
        intro x hxC
        by_contra hxE
        exact hCEc ⟨x, hxC, hxE⟩
      exact ⟨⟨A, B, hA, hB, hAB, hcover, hAC, hBC,
        Or.inl (hAC.trans hCsub), Or.inl (hBC.trans hCsub)⟩⟩
  · obtain ⟨A, B, hA, hB, hAB, hcover, hAC, hBC⟩ :=
      exists_nontrivial_clopen_split C hC
    have hCsub : (C : Set X) ⊆ (E : Set X)ᶜ := by
      intro x hxC hxE
      exact hCE ⟨x, hxC, hxE⟩
    exact ⟨⟨A, B, hA, hB, hAB, hcover, hAC, hBC,
      Or.inr (hAC.trans hCsub), Or.inr (hBC.trans hCsub)⟩⟩

noncomputable def splitData (C E : Clopens X) (hC : (C : Set X).Nonempty) : SplitData C E :=
  Classical.choice (splitData_nonempty C E hC)

structure ClopenNode (X : Type*) [TopologicalSpace X] where
  carrier : Clopens X
  nonempty : (carrier : Set X).Nonempty

noncomputable def clopenEnum (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [TotallyDisconnectedSpace X] [SecondCountableTopology X] :
    ℕ → Clopens X := by
  letI : Countable (Clopens X) :=
    TopologicalSpace.Clopens.countable_iff_secondCountable.mpr inferInstance
  exact Classical.choose (exists_surjective_nat (Clopens X))

lemma clopenEnum_surjective (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [TotallyDisconnectedSpace X] [SecondCountableTopology X] :
    Surjective (clopenEnum X) := by
  letI : Countable (Clopens X) :=
    TopologicalSpace.Clopens.countable_iff_secondCountable.mpr inferInstance
  exact Classical.choose_spec (exists_surjective_nat (Clopens X))

variable [Nonempty X]

noncomputable def nodes (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] [SecondCountableTopology X] :
    List Bool → ClopenNode X
  | [] => ⟨⊤, Set.univ_nonempty⟩
  | b :: l =>
      let parent := nodes X l
      let split := splitData parent.carrier (clopenEnum X l.length) parent.nonempty
      if b then ⟨split.right, split.right_nonempty⟩ else ⟨split.left, split.left_nonempty⟩

def scheme (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] [SecondCountableTopology X]
    (l : List Bool) : Set X :=
  (nodes X l).carrier

lemma scheme_nonempty [SecondCountableTopology X] (l : List Bool) : (scheme X l).Nonempty :=
  (nodes X l).nonempty

lemma scheme_isClopen [SecondCountableTopology X] (l : List Bool) : IsClopen (scheme X l) :=
  (nodes X l).carrier.isClopen

lemma scheme_child_subset [SecondCountableTopology X] (l : List Bool) (b : Bool) :
    scheme X (b :: l) ⊆ scheme X l := by
  cases b
  · simpa [scheme, nodes] using
      (splitData (nodes X l).carrier (clopenEnum X l.length) (nodes X l).nonempty).left_subset
  · simpa [scheme, nodes] using
      (splitData (nodes X l).carrier (clopenEnum X l.length) (nodes X l).nonempty).right_subset

lemma scheme_children_disjoint [SecondCountableTopology X] (l : List Bool) :
    Disjoint (scheme X (false :: l)) (scheme X (true :: l)) := by
  simpa [scheme, nodes] using
    (splitData (nodes X l).carrier (clopenEnum X l.length) (nodes X l).nonempty).disjoint

lemma scheme_children_cover [SecondCountableTopology X] (l : List Bool) :
    scheme X (false :: l) ∪ scheme X (true :: l) = scheme X l := by
  simpa [scheme, nodes] using
    (splitData (nodes X l).carrier (clopenEnum X l.length) (nodes X l).nonempty).cover

lemma scheme_child_decides [SecondCountableTopology X] (l : List Bool) (b : Bool) :
    scheme X (b :: l) ⊆ (clopenEnum X l.length : Set X) ∨
      scheme X (b :: l) ⊆ (clopenEnum X l.length : Set X)ᶜ := by
  cases b <;> simp [scheme, nodes]
  · exact (splitData (nodes X l).carrier (clopenEnum X l.length) (nodes X l).nonempty).left_decides
  · exact (splitData (nodes X l).carrier (clopenEnum X l.length) (nodes X l).nonempty).right_decides

open PiNat

lemma scheme_res_succ_subset [SecondCountableTopology X] (a : ℕ → Bool) (n : ℕ) :
    scheme X (res a (n + 1)) ⊆ scheme X (res a n) := by
  rw [res_succ]
  exact scheme_child_subset (X := X) (res a n) (a n)

lemma branch_nonempty [SecondCountableTopology X] (a : ℕ → Bool) :
    (⋂ n, scheme X (res a n)).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n ↦ scheme X (res a n))
  · exact scheme_res_succ_subset (X := X) a
  · exact fun n ↦ scheme_nonempty (X := X) (res a n)
  · simpa [scheme, nodes] using (isCompact_univ : IsCompact (Set.univ : Set X))
  · exact fun n ↦ (scheme_isClopen (X := X) (res a n)).isClosed

noncomputable def decode (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] [SecondCountableTopology X]
    (a : ℕ → Bool) : X :=
  (branch_nonempty (X := X) a).some

lemma decode_mem [SecondCountableTopology X] (a : ℕ → Bool) (n : ℕ) :
    decode X a ∈ scheme X (res a n) :=
  Set.mem_iInter.mp (branch_nonempty (X := X) a).some_mem n

lemma eq_of_mem_same_branch [SecondCountableTopology X] {a : ℕ → Bool} {x y : X}
    (hx : ∀ n, x ∈ scheme X (res a n)) (hy : ∀ n, y ∈ scheme X (res a n)) : x = y := by
  by_contra hxy
  obtain ⟨U, hU, hxU, hyU⟩ := exists_isClopen_of_totally_separated hxy
  let E : Clopens X := ⟨U, hU⟩
  obtain ⟨k, hk⟩ := clopenEnum_surjective X E
  have hdec : scheme X (res a (k + 1)) ⊆ U ∨ scheme X (res a (k + 1)) ⊆ Uᶜ := by
    simpa [res_succ, res_length, E, hk] using
      (scheme_child_decides (X := X) (res a k) (a k))
  rcases hdec with hsub | hsub
  · exact hyU (hsub (hy (k + 1)))
  · exact (hsub (hx (k + 1))) hxU

lemma decode_injective [SecondCountableTopology X] : Injective (decode X) := by
  intro a b hab
  apply res_injective
  funext n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [res_succ, res_succ, ih]
      congr 1
      by_contra hbit
      have ha := decode_mem (X := X) a (n + 1)
      have hb := decode_mem (X := X) b (n + 1)
      rw [hab] at ha
      rw [res_succ, ih] at ha
      rw [res_succ] at hb
      have hd : Disjoint (scheme X (a n :: res b n)) (scheme X (b n :: res b n)) := by
        cases ha' : a n <;> cases hb' : b n
        · exact (hbit (by simp [ha', hb'])).elim
        · simpa [ha', hb'] using scheme_children_disjoint (X := X) (res b n)
        · simpa [ha', hb'] using (scheme_children_disjoint (X := X) (res b n)).symm
        · exact (hbit (by simp [ha', hb'])).elim
      exact (Set.disjoint_left.mp hd ha hb).elim

noncomputable def nextBit (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] [SecondCountableTopology X]
    (x : X) (l : List Bool) : Bool := by
  classical
  exact if x ∈ scheme X (true :: l) then true else false

noncomputable def prefixes (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] [SecondCountableTopology X]
    (x : X) : ℕ → List Bool := by
  exact fun n ↦ Nat.rec []
    (fun _ l ↦ nextBit X x l :: l) n

lemma prefixes_succ_def [SecondCountableTopology X] (x : X) (n : ℕ) :
    prefixes X x (n + 1) = nextBit X x (prefixes X x n) :: prefixes X x n := by
  simp [prefixes]

lemma mem_prefixes [SecondCountableTopology X] (x : X) (n : ℕ) :
    x ∈ scheme X (prefixes X x n) := by
  induction n with
  | zero => simp [prefixes, scheme, nodes]
  | succ n ih =>
      rw [prefixes_succ_def]
      by_cases htrue : x ∈ scheme X (true :: prefixes X x n)
      · rw [nextBit, if_pos htrue]
        exact htrue
      · have hchildren :
          x ∈ scheme X (false :: prefixes X x n) ∪
            scheme X (true :: prefixes X x n) := by
          rw [scheme_children_cover]
          exact ih
        rcases hchildren with hfalse | htrue'
        · simpa [nextBit, htrue] using hfalse
        · exact (htrue htrue').elim

noncomputable def encode (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] [SecondCountableTopology X]
    (x : X) (n : ℕ) : Bool :=
  (prefixes X x (n + 1)).headD false

lemma prefixes_succ [SecondCountableTopology X] (x : X) (n : ℕ) :
    prefixes X x (n + 1) = encode X x n :: prefixes X x n := by
  rw [prefixes_succ_def]
  unfold encode
  rw [prefixes_succ_def]
  simp

lemma res_encode [SecondCountableTopology X] (x : X) (n : ℕ) :
    res (encode X x) n = prefixes X x n := by
  induction n with
  | zero => simp [prefixes]
  | succ n ih =>
      rw [res_succ, ih, prefixes_succ]

lemma encode_mem [SecondCountableTopology X] (x : X) (n : ℕ) :
    x ∈ scheme X (res (encode X x) n) := by
  rw [res_encode]
  exact mem_prefixes (X := X) x n

lemma decode_encode [SecondCountableTopology X] (x : X) : decode X (encode X x) = x :=
  eq_of_mem_same_branch (decode_mem (X := X) (encode X x)) (encode_mem (X := X) x)

lemma continuous_decode [SecondCountableTopology X] : Continuous (decode X) := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [continuousAt_def]
  intro U hU
  obtain ⟨V, hVU, hVopen, haV⟩ := mem_nhds_iff.mp hU
  obtain ⟨C, hC, haC, hCV⟩ := compact_exists_isClopen_in_isOpen hVopen haV
  let E : Clopens X := ⟨C, hC⟩
  obtain ⟨k, hk⟩ := clopenEnum_surjective X E
  have hdec : scheme X (res a (k + 1)) ⊆ C ∨ scheme X (res a (k + 1)) ⊆ Cᶜ := by
    simpa [res_succ, res_length, E, hk] using
      (scheme_child_decides (X := X) (res a k) (a k))
  have hnode : scheme X (res a (k + 1)) ⊆ C := by
    rcases hdec with hsub | hsub
    · exact hsub
    · exact (hsub (decode_mem (X := X) a (k + 1)) haC).elim
  refine Filter.mem_of_superset
    ((isOpen_cylinder (fun _ : ℕ ↦ Bool) a (k + 1)).mem_nhds
      (self_mem_cylinder a (k + 1))) ?_
  intro b hb
  rw [cylinder_eq_res] at hb
  exact hVU (hCV (hnode (hb ▸ decode_mem (X := X) b (k + 1))))

noncomputable def cantorEquiv (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] [SecondCountableTopology X] :
    (ℕ → Bool) ≃ X where
  toFun := decode X
  invFun := encode X
  left_inv a := decode_injective (X := X) (by rw [decode_encode])
  right_inv := decode_encode (X := X)

noncomputable def homeomorphCantor (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] [SecondCountableTopology X] :
    X ≃ₜ (ℕ → Bool) :=
  (Continuous.homeoOfEquivCompactToT2 (f := cantorEquiv X) (continuous_decode (X := X))).symm

end

end Submission.CantorClassification
