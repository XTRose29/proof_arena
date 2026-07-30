import Submission.Sperner

namespace Submission
namespace SpernerParity

theorem kuhnSimplex_ext {d N : ℕ} {s t : KuhnSimplex d N}
    (hbase : s.base = t.base) (hperm : s.perm = t.perm) : s = t := by
  cases s
  cases t
  cases hbase
  cases hperm
  rfl

/-- Increment the base in the first direction of a Kuhn simplex and rotate that direction
to the end. The old first facet is the new last facet. -/
def forwardNeighbor {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (h : (s.base (s.perm 0)).val + 1 < N) : KuhnSimplex (n + 1) N where
  base := Function.update s.base (s.perm 0) ⟨(s.base (s.perm 0)).val + 1, h⟩
  perm := (finRotate (n + 1)).trans s.perm

/-- Decrement the base in the last direction of a Kuhn simplex and rotate that direction
to the front. The old last facet is the new first facet. -/
def backwardNeighbor {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (h : 0 < (s.base (s.perm (Fin.last n))).val) : KuhnSimplex (n + 1) N where
  base := Function.update s.base (s.perm (Fin.last n))
    ⟨(s.base (s.perm (Fin.last n))).val - 1, by omega⟩
  perm := (finRotate (n + 1)).symm.trans s.perm

/-- Swap the two coordinate directions adjacent to an interior facet. -/
def middleNeighbor {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (k : Fin (n + 2)) (hk0 : 0 < k.val) (hktop : k.val < n + 1) :
    KuhnSimplex (n + 1) N where
  base := s.base
  perm := (Equiv.swap ⟨k.val - 1, by omega⟩ ⟨k.val, hktop⟩).trans s.perm

theorem forwardNeighbor_facet {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (h : (s.base (s.perm 0)).val + 1 < N) (j : Fin (n + 1)) :
    s.vertex ((0 : Fin (n + 2)).succAbove j) =
      (forwardNeighbor s h).vertex ((Fin.last (n + 1)).succAbove j) := by
  ext i
  simp only [KuhnSimplex.vertex_coord]
  by_cases hp : s.perm.symm i = 0
  · have hi : i = s.perm 0 := by
      calc
        i = s.perm (s.perm.symm i) := (s.perm.apply_symm_apply i).symm
        _ = s.perm 0 := congrArg s.perm hp
    subst i
    simp [forwardNeighbor]
    simp [show ¬n < j.val by omega]
  · have hi : i ≠ s.perm 0 := by
      intro hi
      apply hp
      simp [hi]
    simp only [forwardNeighbor, Equiv.symm_trans_apply, Function.update_of_ne hi,
      finRotate_symm_apply, Fin.val_sub_one_of_ne_zero hp, Fin.succAbove_zero,
      Fin.val_succ, Fin.succAbove_last, Fin.val_castSucc]
    have hpval : 0 < (s.perm.symm i).val := Fin.pos_iff_ne_zero.2 hp
    have hcond : (s.perm.symm i).val < j.val + 1 ↔
        (s.perm.symm i).val - 1 < j.val := by omega
    simp only [hcond]

theorem backwardNeighbor_facet {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (h : 0 < (s.base (s.perm (Fin.last n))).val) (j : Fin (n + 1)) :
    s.vertex ((Fin.last (n + 1)).succAbove j) =
      (backwardNeighbor s h).vertex ((0 : Fin (n + 2)).succAbove j) := by
  ext i
  simp only [KuhnSimplex.vertex_coord]
  by_cases hp : s.perm.symm i = Fin.last n
  · have hi : i = s.perm (Fin.last n) := by
      calc
        i = s.perm (s.perm.symm i) := (s.perm.apply_symm_apply i).symm
        _ = s.perm (Fin.last n) := congrArg s.perm hp
    subst i
    simp [backwardNeighbor]
    simp only [if_neg (show ¬n < j.val by omega)]
    change (s.base (s.perm (Fin.last n))).val =
      (s.base (s.perm (Fin.last n))).val - 1 + 1
    omega
  · have hi : i ≠ s.perm (Fin.last n) := by
      intro hi
      apply hp
      simp [hi]
    have hplast : s.perm.symm i < Fin.last n := Fin.lt_last_iff_ne_last.2 hp
    simp only [backwardNeighbor, Equiv.symm_trans_apply, Equiv.symm_symm_apply,
      Function.update_of_ne hi, finRotate_apply, Fin.val_add_one_of_lt hplast,
      Fin.succAbove_last, Fin.val_castSucc, Fin.succAbove_zero, Fin.val_succ]
    split <;> split <;> omega

theorem middleNeighbor_facet {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (k : Fin (n + 2)) (hk0 : 0 < k.val) (hktop : k.val < n + 1)
    (j : Fin (n + 1)) :
    s.vertex (k.succAbove j) = (middleNeighbor s k hk0 hktop).vertex (k.succAbove j) := by
  ext i
  simp only [KuhnSimplex.vertex_coord]
  let a : Fin (n + 1) := ⟨k.val - 1, by omega⟩
  let b : Fin (n + 1) := ⟨k.val, hktop⟩
  have hab : a ≠ b := by
    intro hab
    have := congrArg Fin.val hab
    simp [a, b] at this
    omega
  have hface : k.succAbove j ≠ k := Fin.succAbove_ne _ _
  by_cases ha : s.perm.symm i = a
  · simp [middleNeighbor, a, ha]
    split <;> split <;> omega
  · by_cases hb : s.perm.symm i = b
    · simp [middleNeighbor, b, hb]
      split <;> split <;> omega
    · simp [middleNeighbor, a, b, ha, hb, Equiv.swap_apply_def]

theorem forwardNeighbor_canBackward {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (h : (s.base (s.perm 0)).val + 1 < N) :
    0 < ((forwardNeighbor s h).base
      ((forwardNeighbor s h).perm (Fin.last n))).val := by
  simp [forwardNeighbor]

theorem backwardNeighbor_canForward {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (h : 0 < (s.base (s.perm (Fin.last n))).val) :
    ((backwardNeighbor s h).base ((backwardNeighbor s h).perm 0)).val + 1 < N := by
  have hrotate : (finRotate (n + 1)).symm 0 = Fin.last n := by
    apply (finRotate (n + 1)).injective
    simp
  simp [backwardNeighbor, hrotate]
  omega

theorem backward_forwardNeighbor {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (h : (s.base (s.perm 0)).val + 1 < N) :
    backwardNeighbor (forwardNeighbor s h) (forwardNeighbor_canBackward s h) = s := by
  apply kuhnSimplex_ext
  · funext i
    by_cases hi : i = s.perm 0
    · subst i
      apply Fin.ext
      simp [backwardNeighbor, forwardNeighbor]
    · simp [backwardNeighbor, forwardNeighbor]
  · ext i
    simp [backwardNeighbor, forwardNeighbor]

theorem forward_backwardNeighbor {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (h : 0 < (s.base (s.perm (Fin.last n))).val) :
    forwardNeighbor (backwardNeighbor s h) (backwardNeighbor_canForward s h) = s := by
  have hrotate : (finRotate (n + 1)).symm 0 = Fin.last n := by
    apply (finRotate (n + 1)).injective
    simp
  apply kuhnSimplex_ext
  · funext i
    by_cases hi : i = s.perm (Fin.last n)
    · subst i
      apply Fin.ext
      simp [backwardNeighbor, forwardNeighbor, hrotate]
      omega
    · simp [backwardNeighbor, forwardNeighbor, hrotate]
      rw [Function.update_of_ne hi]
  · ext i
    simp [backwardNeighbor, forwardNeighbor, hrotate]

theorem middleNeighbor_involution {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (k : Fin (n + 2)) (hk0 : 0 < k.val) (hktop : k.val < n + 1) :
    middleNeighbor (middleNeighbor s k hk0 hktop) k hk0 hktop = s := by
  apply kuhnSimplex_ext
  · rfl
  · ext i
    simp [middleNeighbor]

theorem middleNeighbor_ne {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (k : Fin (n + 2)) (hk0 : 0 < k.val) (hktop : k.val < n + 1) :
    middleNeighbor s k hk0 hktop ≠ s := by
  let a : Fin (n + 1) := ⟨k.val - 1, by omega⟩
  let b : Fin (n + 1) := ⟨k.val, hktop⟩
  have hab : a ≠ b := by
    intro hab
    have := congrArg Fin.val hab
    simp [a, b] at this
    omega
  intro hs
  have hp := congrArg (fun t : KuhnSimplex (n + 1) N => t.perm a) hs
  simp [middleNeighbor, a] at hp
  exact hab (Fin.ext hp.symm)

/-- A simplex together with one of its codimension-one facets. -/
structure FacetIncidence (n N : ℕ) where
  simplex : KuhnSimplex (n + 1) N
  face : Fin (n + 2)
deriving DecidableEq, Fintype

/-- Pair an internal facet with its occurrence in the adjacent Kuhn simplex. Boundary facets
are fixed. -/
def incidencePartner {n N : ℕ} (a : FacetIncidence n N) : FacetIncidence n N :=
  if hzero : a.face = 0 then
    if hforward : (a.simplex.base (a.simplex.perm 0)).val + 1 < N then
      ⟨forwardNeighbor a.simplex hforward, Fin.last (n + 1)⟩
    else
      a
  else if hlast : a.face = Fin.last (n + 1) then
    if hbackward : 0 < (a.simplex.base (a.simplex.perm (Fin.last n))).val then
      ⟨backwardNeighbor a.simplex hbackward, 0⟩
    else
      a
  else
    ⟨middleNeighbor a.simplex a.face (Fin.pos_iff_ne_zero.2 hzero)
      (Fin.lt_last_iff_ne_last.2 hlast), a.face⟩

theorem incidencePartner_involution {n N : ℕ} (a : FacetIncidence n N) :
    incidencePartner (incidencePartner a) = a := by
  rcases a with ⟨s, k⟩
  by_cases hzero : k = 0
  · subst k
    by_cases hforward : (s.base (s.perm 0)).val + 1 < N
    · simp [incidencePartner, hforward, forwardNeighbor_canBackward,
        backward_forwardNeighbor]
    · simp [incidencePartner, hforward]
  · by_cases hlast : k = Fin.last (n + 1)
    · subst k
      by_cases hbackward : 0 < (s.base (s.perm (Fin.last n))).val
      · simp [incidencePartner, hbackward, backwardNeighbor_canForward,
          forward_backwardNeighbor]
      · simp [incidencePartner, hbackward]
    · simp [incidencePartner, hzero, hlast, middleNeighbor_involution]

theorem incidencePartner_weight {n N : ℕ} (label : GridVertex (n + 1) N → CubeLabel (n + 1))
    (pivot : Fin (n + 2)) (a : FacetIncidence n N) :
    facetWeightAt label (incidencePartner a).simplex pivot (incidencePartner a).face =
      facetWeightAt label a.simplex pivot a.face := by
  rcases a with ⟨s, k⟩
  by_cases hzero : k = 0
  · subst k
    by_cases hforward : (s.base (s.perm 0)).val + 1 < N
    · simp only [incidencePartner, hforward]
      exact (facetWeightAt_congr label (forwardNeighbor_facet s hforward)).symm
    · simp [incidencePartner, hforward]
  · by_cases hlast : k = Fin.last (n + 1)
    · subst k
      by_cases hbackward : 0 < (s.base (s.perm (Fin.last n))).val
      · have hlast0 : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 :=
          Fin.ne_of_gt (Fin.last_pos)
        simp only [incidencePartner, hbackward, hlast0]
        exact (facetWeightAt_congr label (backwardNeighbor_facet s hbackward)).symm
      · simp [incidencePartner, hbackward]
    · simp only [incidencePartner, hzero, hlast]
      exact (facetWeightAt_congr label
        (middleNeighbor_facet s k (Fin.pos_iff_ne_zero.2 hzero)
          (Fin.lt_last_iff_ne_last.2 hlast))).symm

def incidenceWeight {n N : ℕ} (label : GridVertex (n + 1) N → CubeLabel (n + 1))
    (pivot : Fin (n + 2)) (a : FacetIncidence n N) : ZMod 2 :=
  facetWeightAt label a.simplex pivot a.face

def internalIncidences (n N : ℕ) : Finset (FacetIncidence n N) :=
  Finset.univ.filter fun a => incidencePartner a ≠ a

theorem sum_internalIncidences {n N : ℕ}
    (label : GridVertex (n + 1) N → CubeLabel (n + 1)) (pivot : Fin (n + 2)) :
    ∑ a ∈ internalIncidences n N, incidenceWeight label pivot a = 0 := by
  classical
  apply Finset.sum_involution (fun a _ => incidencePartner a)
  · intro a _
    rw [incidenceWeight, incidenceWeight, incidencePartner_weight]
    exact CharTwo.add_self_eq_zero _
  · intro a ha _
    exact (Finset.mem_filter.1 ha).2
  · intro a ha
    simp only [internalIncidences, Finset.mem_filter, Finset.mem_univ, true_and]
    have hne := (Finset.mem_filter.1 ha).2
    simpa [incidencePartner_involution] using hne.symm
  · intro a _
    exact incidencePartner_involution a

theorem sum_incidenceWeight_eq_sum_fixed {n N : ℕ}
    (label : GridVertex (n + 1) N → CubeLabel (n + 1)) (pivot : Fin (n + 2)) :
    ∑ a, incidenceWeight label pivot a =
      ∑ a ∈ Finset.univ.filter (fun a : FacetIncidence n N => incidencePartner a = a),
        incidenceWeight label pivot a := by
  classical
  calc
    ∑ a, incidenceWeight label pivot a =
        (∑ a ∈ internalIncidences n N, incidenceWeight label pivot a) +
          ∑ a ∈ Finset.univ.filter
            (fun a : FacetIncidence n N => ¬incidencePartner a ≠ a),
            incidenceWeight label pivot a := by
      symm
      exact Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun a : FacetIncidence n N => incidencePartner a ≠ a)
        (incidenceWeight label pivot)
    _ = ∑ a ∈ Finset.univ.filter
          (fun a : FacetIncidence n N => incidencePartner a = a),
          incidenceWeight label pivot a := by
      rw [sum_internalIncidences, zero_add]
      congr 2
      ext a
      simp

def distinguishedIncidence {n N : ℕ} (a : FacetIncidence n N) : Prop :=
  a.face = Fin.last (n + 1) ∧
    a.simplex.perm (Fin.last n) = Fin.last n ∧
      (a.simplex.base (Fin.last n)).val = 0

instance {n N : ℕ} (a : FacetIncidence n N) : Decidable (distinguishedIncidence a) :=
  by
    unfold distinguishedIncidence
    infer_instance

theorem incidencePartner_eq_iff_boundary {n N : ℕ} (a : FacetIncidence n N) :
    incidencePartner a = a ↔
      (a.face = 0 ∧ ¬(a.simplex.base (a.simplex.perm 0)).val + 1 < N) ∨
      (a.face = Fin.last (n + 1) ∧
        ¬0 < (a.simplex.base (a.simplex.perm (Fin.last n))).val) := by
  rcases a with ⟨s, k⟩
  by_cases hzero : k = 0
  · subst k
    by_cases hforward : (s.base (s.perm 0)).val + 1 < N
    · simp [incidencePartner, hforward]
    · simp [incidencePartner, hforward]
  · by_cases hlast : k = Fin.last (n + 1)
    · subst k
      by_cases hbackward : 0 < (s.base (s.perm (Fin.last n))).val
      · simp [incidencePartner, hbackward]
      · simp [incidencePartner, hbackward]
    · constructor
      · intro h
        have hs := congrArg FacetIncidence.simplex h
        simp only [incidencePartner, hzero, hlast] at hs
        exact ((middleNeighbor_ne s k (Fin.pos_iff_ne_zero.2 hzero)
          (Fin.lt_last_iff_ne_last.2 hlast)) hs).elim
      · rintro (h | h)
        · exact (hzero h.1).elim
        · exact (hlast h.1).elim

theorem distinguishedIncidence_partner_eq {n N : ℕ} {a : FacetIncidence n N}
    (ha : distinguishedIncidence a) : incidencePartner a = a := by
  rw [incidencePartner_eq_iff_boundary]
  exact Or.inr ⟨ha.1, by simp [ha.2.1, ha.2.2]⟩

theorem upperFacet_coord {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (hupper : ¬(s.base (s.perm 0)).val + 1 < N) (j : Fin (n + 1)) :
    ((s.vertex ((0 : Fin (n + 2)).succAbove j)).coord (s.perm 0)).val = N := by
  simp [KuhnSimplex.vertex]
  omega

theorem lowerFacet_coord {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (hlower : ¬0 < (s.base (s.perm (Fin.last n))).val) (j : Fin (n + 1)) :
    ((s.vertex ((Fin.last (n + 1)).succAbove j)).coord
      (s.perm (Fin.last n))).val = 0 := by
  have hj : ¬(Fin.last n).val < j.val := not_lt_of_ge (Fin.le_last j)
  simp only [KuhnSimplex.vertex_coord, Equiv.symm_apply_apply,
    Fin.succAbove_last, Fin.val_castSucc, if_neg hj]
  exact Nat.eq_zero_of_not_pos hlower

def inductionPivot (n : ℕ) : Fin (n + 2) :=
  labelIndex (some (Fin.last n))

theorem upperFacet_weight_eq_zero {n N : ℕ}
    (label : GridVertex (n + 1) N → CubeLabel (n + 1))
    (hadm : SpernerAdmissible label) (s : KuhnSimplex (n + 1) N)
    (hupper : ¬(s.base (s.perm 0)).val + 1 < N) :
    facetWeightAt label s (inductionPivot n) 0 = 0 := by
  apply facetWeightAt_eq_zero_of_missing label s (r := labelIndex none)
  · intro hpivot
    have := labelIndex.injective hpivot
    simp at this
  · intro j hlabel
    have hnone : label (s.vertex ((0 : Fin (n + 2)).succAbove j)) = none :=
      labelIndex.injective hlabel
    have hlt := hadm.1 _ hnone (s.perm 0)
    rw [upperFacet_coord s hupper j] at hlt
    omega

theorem lowerFacet_weight_eq_zero {n N : ℕ}
    (label : GridVertex (n + 1) N → CubeLabel (n + 1))
    (hadm : SpernerAdmissible label) (s : KuhnSimplex (n + 1) N)
    (hlower : ¬0 < (s.base (s.perm (Fin.last n))).val)
    (hq : s.perm (Fin.last n) ≠ Fin.last n) :
    facetWeightAt label s (inductionPivot n) (Fin.last (n + 1)) = 0 := by
  let q := s.perm (Fin.last n)
  apply facetWeightAt_eq_zero_of_missing label s (r := labelIndex (some q))
  · simp [inductionPivot, q, hq]
  · intro j hlabel
    have hsome : label (s.vertex ((Fin.last (n + 1)).succAbove j)) = some q :=
      labelIndex.injective hlabel
    have hpos := hadm.2 _ q hsome
    rw [lowerFacet_coord s hlower j] at hpos
    omega

theorem fixed_incidenceWeight_eq_zero_of_not_distinguished {n N : ℕ}
    (label : GridVertex (n + 1) N → CubeLabel (n + 1))
    (hadm : SpernerAdmissible label) (a : FacetIncidence n N)
    (hfixed : incidencePartner a = a) (hnot : ¬distinguishedIncidence a) :
    incidenceWeight label (inductionPivot n) a = 0 := by
  rcases a with ⟨s, k⟩
  rw [incidencePartner_eq_iff_boundary] at hfixed
  rcases hfixed with hupper | hlower
  · have hk : k = 0 := by simpa using hupper.1
    subst k
    exact upperFacet_weight_eq_zero label hadm s hupper.2
  · have hk : k = Fin.last (n + 1) := by simpa using hlower.1
    subst k
    have hq : s.perm (Fin.last n) ≠ Fin.last n := by
      intro hq
      apply hnot
      refine ⟨rfl, hq, ?_⟩
      apply Nat.eq_zero_of_not_pos
      simpa [hq] using hlower.2
    exact lowerFacet_weight_eq_zero label hadm s hlower.2 hq

theorem sum_fixed_eq_sum_distinguished {n N : ℕ}
    (label : GridVertex (n + 1) N → CubeLabel (n + 1))
    (hadm : SpernerAdmissible label) :
    ∑ a ∈ Finset.univ.filter (fun a : FacetIncidence n N => incidencePartner a = a),
        incidenceWeight label (inductionPivot n) a =
      ∑ a ∈ Finset.univ.filter (fun a : FacetIncidence n N => distinguishedIncidence a),
        incidenceWeight label (inductionPivot n) a := by
  classical
  symm
  apply Finset.sum_subset
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact distinguishedIncidence_partner_eq ha
  · intro a hafixed hadist
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hafixed hadist
    exact fixed_incidenceWeight_eq_zero_of_not_distinguished label hadm a hafixed hadist

def castSuccSubtypeEquiv (n : ℕ) :
    Fin n ≃ {i : Fin (n + 1) // i ≠ Fin.last n} where
  toFun i := ⟨i.castSucc, Fin.ne_of_lt (Fin.castSucc_lt_last i)⟩
  invFun i := i.1.castPred i.2
  left_inv i := by simp
  right_inv i := by
    apply Subtype.ext
    simp

def extendLastPerm {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  p.extendDomain (castSuccSubtypeEquiv n)

@[simp]
theorem extendLastPerm_castSucc {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    extendLastPerm p i.castSucc = (p i).castSucc := by
  exact Equiv.Perm.extendDomain_apply_image p (castSuccSubtypeEquiv n) i

@[simp]
theorem extendLastPerm_last {n : ℕ} (p : Equiv.Perm (Fin n)) :
    extendLastPerm p (Fin.last n) = Fin.last n := by
  apply Equiv.Perm.extendDomain_apply_not_subtype
  simp

def restrictLastPerm {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (hfix : p (Fin.last n) = Fin.last n) : Equiv.Perm (Fin n) :=
  (castSuccSubtypeEquiv n).permCongr.symm <|
    p.subtypePerm fun i => by
      constructor
      · intro hpi hi
        subst i
        exact hpi hfix
      · intro hi hpi
        apply hi
        apply p.injective
        rw [hpi, hfix]

theorem extend_restrictLastPerm {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (hfix : p (Fin.last n) = Fin.last n) :
    extendLastPerm (restrictLastPerm p hfix) = p := by
  ext i
  cases i using Fin.lastCases with
  | last => simp [hfix]
  | cast i =>
      rw [extendLastPerm_castSucc]
      have hpi : p i.castSucc ≠ Fin.last n := by
        intro hpi
        have hi : i.castSucc = Fin.last n := p.injective (hpi.trans hfix.symm)
        exact (Fin.ne_of_lt (Fin.castSucc_lt_last i)) hi
      simp [restrictLastPerm, castSuccSubtypeEquiv]

theorem restrict_extendLastPerm {n : ℕ} (p : Equiv.Perm (Fin n)) :
    restrictLastPerm (extendLastPerm p) (extendLastPerm_last p) = p := by
  ext i
  simp [restrictLastPerm, castSuccSubtypeEquiv]

@[simp]
theorem extendLastPerm_symm {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (extendLastPerm p).symm = extendLastPerm p.symm := by
  simp [extendLastPerm]

def embedLowerVertex {n N : ℕ} (v : GridVertex n N) : GridVertex (n + 1) N where
  coord := Fin.lastCases 0 v.coord

@[simp]
theorem embedLowerVertex_castSucc {n N : ℕ} (v : GridVertex n N) (i : Fin n) :
    (embedLowerVertex v).coord i.castSucc = v.coord i := by
  simp [embedLowerVertex]

@[simp]
theorem embedLowerVertex_last {n N : ℕ} (v : GridVertex n N) :
    (embedLowerVertex v).coord (Fin.last n) = 0 := by
  simp [embedLowerVertex]

def embedLowerSimplex {n N : ℕ} (hN : 0 < N) (s : KuhnSimplex n N) :
    KuhnSimplex (n + 1) N where
  base := Fin.lastCases ⟨0, hN⟩ s.base
  perm := extendLastPerm s.perm

@[simp]
theorem embedLowerSimplex_base_castSucc {n N : ℕ} (hN : 0 < N)
    (s : KuhnSimplex n N) (i : Fin n) :
    (embedLowerSimplex hN s).base i.castSucc = s.base i := by
  simp [embedLowerSimplex]

@[simp]
theorem embedLowerSimplex_base_last {n N : ℕ} (hN : 0 < N) (s : KuhnSimplex n N) :
    ((embedLowerSimplex hN s).base (Fin.last n)).val = 0 := by
  simp [embedLowerSimplex]

theorem embedLowerSimplex_vertex {n N : ℕ} (hN : 0 < N) (s : KuhnSimplex n N)
    (k : Fin (n + 1)) :
    (embedLowerSimplex hN s).vertex k.castSucc = embedLowerVertex (s.vertex k) := by
  ext i
  cases i using Fin.lastCases with
  | last =>
      simp [KuhnSimplex.vertex, embedLowerSimplex, embedLowerVertex]
      exact Fin.le_last k
  | cast i =>
      simp [KuhnSimplex.vertex, embedLowerSimplex, embedLowerVertex]
      simp only [Fin.lt_def, Fin.val_castSucc]

def restrictLowerSimplex {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (hfix : s.perm (Fin.last n) = Fin.last n) : KuhnSimplex n N where
  base i := s.base i.castSucc
  perm := restrictLastPerm s.perm hfix

theorem restrict_embedLowerSimplex {n N : ℕ} (hN : 0 < N) (s : KuhnSimplex n N) :
    restrictLowerSimplex (embedLowerSimplex hN s) (extendLastPerm_last s.perm) = s := by
  apply kuhnSimplex_ext
  · funext i
    simp [restrictLowerSimplex]
  · exact restrict_extendLastPerm s.perm

theorem embed_restrictLowerSimplex {n N : ℕ} (s : KuhnSimplex (n + 1) N)
    (hN : 0 < N) (hfix : s.perm (Fin.last n) = Fin.last n)
    (hbase : (s.base (Fin.last n)).val = 0) :
    embedLowerSimplex hN (restrictLowerSimplex s hfix) = s := by
  apply kuhnSimplex_ext
  · funext i
    cases i using Fin.lastCases with
    | last =>
        apply Fin.ext
        simpa [embedLowerSimplex] using hbase.symm
    | cast i => simp [embedLowerSimplex, restrictLowerSimplex]
  · exact extend_restrictLastPerm s.perm hfix

def embedLowerIncidence {n N : ℕ} (hN : 0 < N) (s : KuhnSimplex n N) :
    FacetIncidence n N :=
  ⟨embedLowerSimplex hN s, Fin.last (n + 1)⟩

theorem embedLowerIncidence_distinguished {n N : ℕ} (hN : 0 < N)
    (s : KuhnSimplex n N) :
    distinguishedIncidence (embedLowerIncidence hN s) := by
  simp [distinguishedIncidence, embedLowerIncidence, embedLowerSimplex]

def lowerIncidenceEquiv (n N : ℕ) (hN : 0 < N) :
    KuhnSimplex n N ≃ {a : FacetIncidence n N // distinguishedIncidence a} where
  toFun s := ⟨embedLowerIncidence hN s, embedLowerIncidence_distinguished hN s⟩
  invFun a := restrictLowerSimplex a.1.simplex (by
    have ha := a.2
    change a.1.face = Fin.last (n + 1) ∧
      a.1.simplex.perm (Fin.last n) = Fin.last n ∧
        (a.1.simplex.base (Fin.last n)).val = 0 at ha
    exact ha.2.1)
  left_inv s := restrict_embedLowerSimplex hN s
  right_inv a := by
    apply Subtype.ext
    rcases a with ⟨⟨s, k⟩, hdist⟩
    change k = Fin.last (n + 1) ∧ s.perm (Fin.last n) = Fin.last n ∧
      (s.base (Fin.last n)).val = 0 at hdist
    rcases hdist with ⟨rfl, hfix, hbase⟩
    change (⟨embedLowerSimplex hN (restrictLowerSimplex s _), Fin.last (n + 1)⟩ :
      FacetIncidence n N) = ⟨s, Fin.last (n + 1)⟩
    apply congrArg (fun t : KuhnSimplex (n + 1) N =>
      (⟨t, Fin.last (n + 1)⟩ : FacetIncidence n N))
    exact embed_restrictLowerSimplex s hN hfix hbase

end SpernerParity
end Submission
