import Submission.OddOrder.PF.Section03.CyclicTIPairingExchange
import Submission.OddOrder.PF.Section03.CyclicTICoefficientSupport

/-!
# Small cyclic-TI coefficient support

This file ports Peterfalvi (3.8.1)--(3.8.3), the combinatorial core of
`small_cycTI_NC`, and its consequence `cycTI_NC_minn`.  The argument is
separated from character theory: an additive rectangle relation forces a
small nonzero matrix support to be a single full row or a single full
column.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u

private theorem odd_matrix_small_support
    {R I J : Type*} [Field R] [Fintype I] [Fintype J]
    (a : I → J → R)
    (hrectangle : ∀ i₁ i₂ j₁ j₂,
      a i₁ j₁ = a i₁ j₂ + a i₂ j₁ - a i₂ j₂)
    (hIodd : Odd (Fintype.card I))
    (hJodd : Odd (Fintype.card J))
    (hIneJ : Fintype.card I ≠ Fintype.card J)
    (hIgt : 2 < Fintype.card I)
    (hJgt : 2 < Fintype.card J)
    (i₀ : I) (j₀ : J)
    (ha₀ : a i₀ j₀ ≠ 0)
    (hsmall :
      (Finset.univ.filter (fun p : I × J ↦ a p.1 p.2 ≠ 0)).card <
        2 * min (Fintype.card I) (Fintype.card J)) :
    (∀ i j, a i j = if j = j₀ then a i₀ j₀ else 0) ∨
      (∀ i j, a i j = if i = i₀ then a i₀ j₀ else 0) := by
  let A : Finset (I × J) :=
    Finset.univ.filter (fun p ↦ a p.1 p.2 ≠ 0)
  let nI := Fintype.card I
  let nJ := Fintype.card J
  have hA_small : A.card < 2 * min nI nJ := by
    simpa [A, nI, nJ] using hsmall

  /- Odd unequal dimensions differ by at least two.  Hence the assumed
  support bound rules out `nJ + nI ≤ #A + 2`; this is the numerical
  estimate used throughout (3.8.1). -/
  have hsum_not_le : ¬ nJ + nI ≤ A.card + 2 := by
    intro hsum
    rcases hIodd with ⟨r, hr⟩
    rcases hJodd with ⟨s, hs⟩
    by_cases hle : nI ≤ nJ
    · have hmin : min nI nJ = nI := Nat.min_eq_left hle
      have hgap : nI + 2 ≤ nJ := by
        dsimp [nI, nJ] at hIneJ hr hs ⊢
        omega
      rw [hmin] at hA_small
      omega
    · have hle' : nJ ≤ nI := Nat.le_of_not_ge hle
      have hmin : min nI nJ = nJ := Nat.min_eq_right hle'
      have hgap : nJ + 2 ≤ nI := by
        dsimp [nI, nJ] at hIneJ hr hs ⊢
        omega
      rw [hmin] at hA_small
      omega

  /- Step (3.8.1).  If the two off-diagonal corners vanish, then the
  remaining corner vanishes.  Otherwise a row-sized set and a column-sized
  set lie in the support and intersect in at most two points. -/
  have zero_corner (i₁ i₂ : I) (j₁ j₂ : J)
      (h₁₂ : a i₁ j₂ = 0) (h₂₁ : a i₂ j₁ = 0) :
      a i₁ j₁ = 0 := by
    by_cases hi : i₁ = i₂
    · subst i₂
      exact h₂₁
    by_contra h₁₁
    let L : Finset (I × J) := Finset.univ.image fun j ↦
      (if a i₁ j = 0 then i₂ else i₁, j)
    let C : Finset (I × J) := Finset.univ.image fun i ↦
      (i, if a i j₁ = 0 then j₂ else j₁)
    let S : Finset (I × J) := {(i₁, j₁), (i₂, j₂)}
    have hLinj : Function.Injective (fun j : J ↦
        (if a i₁ j = 0 then i₂ else i₁, j)) := by
      intro j j' hj
      exact congrArg Prod.snd hj
    have hCinj : Function.Injective (fun i : I ↦
        (i, if a i j₁ = 0 then j₂ else j₁)) := by
      intro i i' hi'
      exact congrArg Prod.fst hi'
    have hLcard : L.card = nJ := by
      change (Finset.univ.image (fun j : J ↦
        (if a i₁ j = 0 then i₂ else i₁, j))).card = nJ
      rw [Finset.card_image_of_injective _ hLinj, Finset.card_univ]
    have hCcard : C.card = nI := by
      change (Finset.univ.image (fun i : I ↦
        (i, if a i j₁ = 0 then j₂ else j₁))).card = nI
      rw [Finset.card_image_of_injective _ hCinj, Finset.card_univ]
    have hUnion : L ∪ C ⊆ A := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_image.mp hp with ⟨j, -, rfl⟩
        by_cases hz : a i₁ j = 0
        · have hnz : a i₂ j ≠ 0 := by
            intro h₂j
            have hr := hrectangle i₁ i₂ j₁ j
            rw [hz, h₂₁, h₂j] at hr
            exact h₁₁ (by simpa using hr)
          simp [A, hz, hnz]
        · simp [A, hz]
      · rcases Finset.mem_image.mp hp with ⟨i, -, rfl⟩
        by_cases hz : a i j₁ = 0
        · have hnz : a i j₂ ≠ 0 := by
            intro hij₂
            have hr := hrectangle i₁ i j₁ j₂
            rw [h₁₂, hz, hij₂] at hr
            exact h₁₁ (by simpa using hr)
          simp [A, hz, hnz]
        · simp [A, hz]
    have hInter : L ∩ C ⊆ S := by
      intro p hp
      rcases Finset.mem_inter.mp hp with ⟨hpL, hpC⟩
      rcases Finset.mem_image.mp hpL with ⟨j, -, rfl⟩
      rcases Finset.mem_image.mp hpC with ⟨i, -, heq⟩
      by_cases hz : a i₁ j = 0
      · simp only [hz, if_pos] at heq
        have hii : i = i₂ := congrArg Prod.fst heq
        subst i
        simp only [h₂₁, if_pos] at heq
        have hjj : j₂ = j := congrArg Prod.snd heq
        subst j
        simp [S, hz]
      · simp only [hz, if_neg] at heq
        have hii : i = i₁ := congrArg Prod.fst heq
        subst i
        simp only [h₁₁, if_neg] at heq
        have hjj : j₁ = j := congrArg Prod.snd heq
        subst j
        simp [S, hz]
    have hpoints : (i₁, j₁) ≠ (i₂, j₂) := by
      intro hp
      exact hi (congrArg Prod.fst hp)
    have hScard : S.card = 2 := by simp [S, hpoints]
    have hUcard : (L ∪ C).card ≤ A.card :=
      Finset.card_le_card hUnion
    have hIntcard : (L ∩ C).card ≤ S.card :=
      Finset.card_le_card hInter
    have hcount := Finset.card_union_add_card_inter L C
    apply hsum_not_le
    omega

  let row (i : I) : Finset (I × J) := A.filter fun p ↦ p.1 = i
  let col (j : J) : Finset (I × J) := A.filter fun p ↦ p.2 = j

  have row_card_ge (i : I) (hi : ∀ j, a i j ≠ 0) :
      nJ ≤ (row i).card := by
    let line : Finset (I × J) := Finset.univ.image fun j : J ↦ (i, j)
    have hline : line.card = nJ := by
      change (Finset.univ.image (fun j : J ↦ (i, j))).card = nJ
      rw [Finset.card_image_of_injective _ (Prod.mk_right_injective i),
        Finset.card_univ]
    have hsub : line ⊆ row i := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨j, -, rfl⟩
      simp [line, row, A, hi j]
    rw [← hline]
    exact Finset.card_le_card hsub

  have col_card_ge (j : J) (hj : ∀ i, a i j ≠ 0) :
      nI ≤ (col j).card := by
    let line : Finset (I × J) := Finset.univ.image fun i : I ↦ (i, j)
    have hline : line.card = nI := by
      change (Finset.univ.image (fun i : I ↦ (i, j))).card = nI
      rw [Finset.card_image_of_injective _ (Prod.mk_left_injective j),
        Finset.card_univ]
    have hsub : line ⊆ col j := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨i, -, rfl⟩
      simp [line, col, A, hj i]
    rw [← hline]
    exact Finset.card_le_card hsub

  have card_add_le_A {B C : Finset (I × J)}
      (hB : B ⊆ A) (hC : C ⊆ A) (hBC : Disjoint B C) :
      B.card + C.card ≤ A.card := by
    rw [← Finset.card_union_of_disjoint hBC]
    exact Finset.card_le_card (Finset.union_subset hB hC)

  have row_subset (i : I) : row i ⊆ A := Finset.filter_subset _ _
  have col_subset (j : J) : col j ⊆ A := Finset.filter_subset _ _

  have rows_disjoint {i i' : I} (hii : i ≠ i') :
      Disjoint (row i) (row i') := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    have hi := (Finset.mem_filter.mp hp).2
    have hi' := (Finset.mem_filter.mp hp').2
    exact hii (hi.symm.trans hi')

  have cols_disjoint {j j' : J} (hjj : j ≠ j') :
      Disjoint (col j) (col j') := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    have hj := (Finset.mem_filter.mp hp).2
    have hj' := (Finset.mem_filter.mp hp').2
    exact hjj (hj.symm.trans hj')

  /- A row and a column meet in at most their common matrix entry. -/
  have row_col_bound (i : I) (j : J) :
      ¬ nJ + nI ≤ (row i).card + (col j).card := by
    intro hlarge
    have hUnion : row i ∪ col j ⊆ A :=
      Finset.union_subset (row_subset i) (col_subset j)
    have hInter : row i ∩ col j ⊆ ({(i, j)} : Finset (I × J)) := by
      intro p hp
      rcases Finset.mem_inter.mp hp with ⟨hpr, hpc⟩
      have hi := (Finset.mem_filter.mp hpr).2
      have hj := (Finset.mem_filter.mp hpc).2
      rw [Finset.mem_singleton]
      exact Prod.ext hi hj
    have hUcard : (row i ∪ col j).card ≤ A.card :=
      Finset.card_le_card hUnion
    have hIntcard : (row i ∩ col j).card ≤ 1 := by
      simpa using Finset.card_le_card hInter
    have hcount := Finset.card_union_add_card_inter (row i) (col j)
    apply hsum_not_le
    omega

  have col_full_of_nonzero_zero (i : I) (j j' : J)
      (hnz : a i j ≠ 0) (hz : a i j' = 0) :
      nI ≤ (col j).card := by
    apply col_card_ge
    intro i'
    intro hi'
    exact hnz (zero_corner i i' j j' hz hi')

  by_cases hrow₀zero : ∃ j, a i₀ j = 0
  · /- Step (3.8.2): a zero in the distinguished row forces the
    distinguished column to be full, and every other column to vanish. -/
    obtain ⟨j₁, hj₁⟩ := hrow₀zero
    have hj₁₀ : j₁ ≠ j₀ := by
      intro h
      subst j₁
      exact ha₀ hj₁
    have hcol₀ : nI ≤ (col j₀).card :=
      col_full_of_nonzero_zero i₀ j₀ j₁ ha₀ hj₁
    have outside (i : I) (j : J) (hj : j ≠ j₀) : a i j = 0 := by
      by_contra hij
      have hall : ∀ j', a i j' ≠ 0 := by
        intro j'
        intro hij'
        have hcolj : nI ≤ (col j).card :=
          col_full_of_nonzero_zero i j j' hij hij'
        have hcols : (col j₀).card + (col j).card ≤ A.card :=
          card_add_le_A (col_subset j₀) (col_subset j)
            (cols_disjoint hj.symm)
        have hmin := Nat.min_le_left nI nJ
        omega
      have hrow : nJ ≤ (row i).card := row_card_ge i hall
      exact row_col_bound i j₀ (by omega)
    left
    intro i j
    by_cases hj : j = j₀
    · subst j
      rw [if_pos rfl]
      have hr := hrectangle i i₀ j₀ j₁
      rw [outside i j₁ hj₁₀, hj₁] at hr
      simpa using hr
    · rw [if_neg hj]
      exact outside i j hj
  · /- Step (3.8.3): if the distinguished row has no zero, it is full;
    every other row must vanish. -/
    have hall₀ : ∀ j, a i₀ j ≠ 0 := by
      intro j hj
      exact hrow₀zero ⟨j, hj⟩
    have hrow₀ : nJ ≤ (row i₀).card := row_card_ge i₀ hall₀
    have outside (i : I) (hi : i ≠ i₀) (j : J) : a i j = 0 := by
      have hsomezero : ∃ j', a i j' = 0 := by
        by_contra hnone
        push_neg at hnone
        have hrowi : nJ ≤ (row i).card := row_card_ge i hnone
        have hrows : (row i₀).card + (row i).card ≤ A.card :=
          card_add_le_A (row_subset i₀) (row_subset i)
            (rows_disjoint hi.symm)
        have hmin := Nat.min_le_right nI nJ
        omega
      obtain ⟨j₁, hj₁⟩ := hsomezero
      by_contra hij
      have hcolj : nI ≤ (col j).card :=
        col_full_of_nonzero_zero i j j₁ hij hj₁
      exact row_col_bound i₀ j (by omega)
    right
    intro i j
    by_cases hi : i = i₀
    · subst i
      rw [if_pos rfl]
      have hcard : 1 < Fintype.card I := by omega
      obtain ⟨i₁, hi₁⟩ := Fintype.exists_ne_of_one_lt_card hcard i₀
      have hr := hrectangle i₀ i₁ j j₀
      rw [outside i₁ hi₁ j, outside i₁ hi₁ j₀] at hr
      simpa using hr
    · rw [if_neg hi]
      exact outside i hi j

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {G W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance cyclicTISmallSupportInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

namespace CyclicTIIsometryData

variable {h : CyclicTIHypothesis G W W₁ W₂ defW}

/-- Peterfalvi (3.8.1)--(3.8.3): below twice the smaller factor size, a
nonempty cyclic-TI coefficient support is a full row or a full column. -/
theorem small_cyclicTINC
    (iso : CyclicTIIsometryData (k := k) h)
    (phi : ClassFunction G k)
    (hzero : Set.EqOn
      (fun w : W ↦ phi ⟨w, h.le_group w.property⟩) 0
      (cyclicTISetInW W W₁ W₂))
    (i₀ : IrreducibleCharacter W₁ k)
    (j₀ : IrreducibleCharacter W₂ k)
    (hsmall : iso.cyclicTINC phi <
      2 * min
        (Fintype.card (IrreducibleCharacter W₁ k))
        (Fintype.card (IrreducibleCharacter W₂ k)))
    (ha₀ : characterPairing phi
      (iso.linearMap
        (IrreducibleCharacter.cyclicTICharacter defW i₀ j₀ :
          ClassFunction W k)) ≠ 0) :
    (∀ i j, characterPairing phi
        (iso.linearMap
          (IrreducibleCharacter.cyclicTICharacter defW i j :
            ClassFunction W k)) =
      if j = j₀ then
        characterPairing phi
          (iso.linearMap
            (IrreducibleCharacter.cyclicTICharacter defW i₀ j₀ :
              ClassFunction W k))
      else 0) ∨
    (∀ i j, characterPairing phi
        (iso.linearMap
          (IrreducibleCharacter.cyclicTICharacter defW i j :
            ClassFunction W k)) =
      if i = i₀ then
        characterPairing phi
          (iso.linearMap
            (IrreducibleCharacter.cyclicTICharacter defW i₀ j₀ :
              ClassFunction W k))
      else 0) := by
  letI : IsCyclic W₁ := h.left_cyclic
  letI : IsCyclic W₂ := h.right_cyclic
  let a (i : IrreducibleCharacter W₁ k)
      (j : IrreducibleCharacter W₂ k) : k :=
    characterPairing phi
      (iso.linearMap
        (IrreducibleCharacter.cyclicTICharacter defW i j :
          ClassFunction W k))
  have hrectangle (i₁ i₂ : IrreducibleCharacter W₁ k)
      (j₁ j₂ : IrreducibleCharacter W₂ k) :
      a i₁ j₁ = a i₁ j₂ + a i₂ j₁ - a i₂ j₂ := by
    have hexchange := iso.pairing_exchange hzero i₁ i₂ j₁ j₂
    dsimp [a] at hexchange ⊢
    linear_combination hexchange
  have hcard₁ :
      Fintype.card (IrreducibleCharacter W₁ k) = Nat.card W₁ :=
    IrreducibleCharacter.card_eq_natCard_of_isCyclic
  have hcard₂ :
      Fintype.card (IrreducibleCharacter W₂ k) = Nat.card W₂ :=
    IrreducibleCharacter.card_eq_natCard_of_isCyclic
  have hodd₁ : Odd (Fintype.card (IrreducibleCharacter W₁ k)) := by
    rw [hcard₁]
    exact h.left_odd_card
  have hodd₂ : Odd (Fintype.card (IrreducibleCharacter W₂ k)) := by
    rw [hcard₂]
    exact h.right_odd_card
  have hne : Fintype.card (IrreducibleCharacter W₁ k) ≠
      Fintype.card (IrreducibleCharacter W₂ k) := by
    rw [hcard₁, hcard₂]
    exact h.factor_card_ne
  have hgt₁ : 2 < Fintype.card (IrreducibleCharacter W₁ k) := by
    rw [hcard₁]
    exact h.two_lt_card_left
  have hgt₂ : 2 < Fintype.card (IrreducibleCharacter W₂ k) := by
    rw [hcard₂]
    exact h.two_lt_card_right
  have hsupport :
      Finset.univ.filter
          (fun p : IrreducibleCharacter W₁ k ×
              IrreducibleCharacter W₂ k ↦ a p.1 p.2 ≠ 0) =
        iso.cyclicTICoefficientSupport phi := by
    ext p
    simp [a, cyclicTIImage, cyclicTISourceIrreducible]
  have hsmall' :
      (Finset.univ.filter
          (fun p : IrreducibleCharacter W₁ k ×
              IrreducibleCharacter W₂ k ↦ a p.1 p.2 ≠ 0)).card <
        2 * min
          (Fintype.card (IrreducibleCharacter W₁ k))
          (Fintype.card (IrreducibleCharacter W₂ k)) := by
    rw [hsupport]
    exact hsmall
  simpa [a] using odd_matrix_small_support a hrectangle hodd₁ hodd₂
    hne hgt₁ hgt₂ i₀ j₀ ha₀ hsmall'

/-- Peterfalvi's `cycTI_NC_minn`: a nonzero coefficient support has at
least the size of the smaller cyclic direct factor. -/
theorem cyclicTINC_min_le
    (iso : CyclicTIIsometryData (k := k) h)
    (phi : ClassFunction G k)
    (hzero : Set.EqOn
      (fun w : W ↦ phi ⟨w, h.le_group w.property⟩) 0
      (cyclicTISetInW W W₁ W₂))
    (hpos : 0 < iso.cyclicTINC phi)
    (hsmall : iso.cyclicTINC phi <
      2 * min
        (Fintype.card (IrreducibleCharacter W₁ k))
        (Fintype.card (IrreducibleCharacter W₂ k))) :
    min
        (Fintype.card (IrreducibleCharacter W₁ k))
        (Fintype.card (IrreducibleCharacter W₂ k)) ≤
      iso.cyclicTINC phi := by
  change 0 < (iso.cyclicTICoefficientSupport phi).card at hpos
  obtain ⟨⟨i₀, j₀⟩, hp⟩ := Finset.card_pos.mp hpos
  let a (i : IrreducibleCharacter W₁ k)
      (j : IrreducibleCharacter W₂ k) : k :=
    characterPairing phi
      (iso.linearMap
        (IrreducibleCharacter.cyclicTICharacter defW i j :
          ClassFunction W k))
  have ha₀ : a i₀ j₀ ≠ 0 := by
    simpa [a, cyclicTIImage, cyclicTISourceIrreducible] using hp
  rcases iso.small_cyclicTINC phi hzero i₀ j₀ hsmall
      (by simpa [a] using ha₀) with hcol | hrow
  · let line : Finset
        (IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :=
      Finset.univ.image fun i ↦ (i, j₀)
    have hlinecard : line.card =
        Fintype.card (IrreducibleCharacter W₁ k) := by
      change (Finset.univ.image (fun i : IrreducibleCharacter W₁ k ↦
        (i, j₀))).card = _
      rw [Finset.card_image_of_injective _ (Prod.mk_left_injective j₀),
        Finset.card_univ]
    have hsub : line ⊆ iso.cyclicTICoefficientSupport phi := by
      intro p hp'
      rcases Finset.mem_image.mp hp' with ⟨i, -, rfl⟩
      have hi := hcol i j₀
      simp only [if_pos rfl] at hi
      have hnz : a i j₀ ≠ 0 := by
        dsimp [a]
        rw [hi]
        exact ha₀
      simpa [a, cyclicTIImage, cyclicTISourceIrreducible] using hnz
    calc
      min
          (Fintype.card (IrreducibleCharacter W₁ k))
          (Fintype.card (IrreducibleCharacter W₂ k)) ≤
          Fintype.card (IrreducibleCharacter W₁ k) := Nat.min_le_left _ _
      _ = line.card := hlinecard.symm
      _ ≤ (iso.cyclicTICoefficientSupport phi).card :=
        Finset.card_le_card hsub
      _ = iso.cyclicTINC phi := rfl
  · let line : Finset
        (IrreducibleCharacter W₁ k × IrreducibleCharacter W₂ k) :=
      Finset.univ.image fun j ↦ (i₀, j)
    have hlinecard : line.card =
        Fintype.card (IrreducibleCharacter W₂ k) := by
      change (Finset.univ.image (fun j : IrreducibleCharacter W₂ k ↦
        (i₀, j))).card = _
      rw [Finset.card_image_of_injective _ (Prod.mk_right_injective i₀),
        Finset.card_univ]
    have hsub : line ⊆ iso.cyclicTICoefficientSupport phi := by
      intro p hp'
      rcases Finset.mem_image.mp hp' with ⟨j, -, rfl⟩
      have hj := hrow i₀ j
      simp only [if_pos rfl] at hj
      have hnz : a i₀ j ≠ 0 := by
        dsimp [a]
        rw [hj]
        exact ha₀
      simpa [a, cyclicTIImage, cyclicTISourceIrreducible] using hnz
    calc
      min
          (Fintype.card (IrreducibleCharacter W₁ k))
          (Fintype.card (IrreducibleCharacter W₂ k)) ≤
          Fintype.card (IrreducibleCharacter W₂ k) := Nat.min_le_right _ _
      _ = line.card := hlinecard.symm
      _ ≤ (iso.cyclicTICoefficientSupport phi).card :=
        Finset.card_le_card hsub
      _ = iso.cyclicTINC phi := rfl

end CyclicTIIsometryData

end

end Submission.OddOrder.PF
