import Submission.OddOrder.MathlibSupport.InvariantSubgroupAction
import Submission.OddOrder.MathlibSupport.RepresentationLinearEquivBasic
import Submission.OddOrder.PF.Section09.PTypeFCoreKernel
import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Peterfalvi Section 9: action infrastructure

This module collects the group-action and intertwining-algebra constructions
used by both branches of the Section 9 factor-action argument.  It is kept
independent of the later canonical factor package so that those branches can
share a small, stable interface.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.MathlibSupport

noncomputable section

/-! ## Invariant subgroups -/

/-- A subgroup preserved by an action through automorphisms. -/
def IsInvariantSubgroup
    {A H : Type*} [Group A] [Group H]
    (rho : A →* MulAut H) (L : Subgroup H) : Prop :=
  ∀ a, L.map (rho a).toMonoidHom = L

/-- Membership in an invariant subgroup is preserved by the action. -/
theorem IsInvariantSubgroup.mem
    {A H : Type*} [Group A] [Group H]
    {rho : A →* MulAut H} {L : Subgroup H}
    (hL : IsInvariantSubgroup rho L)
    (a : A) {x : H} (hx : x ∈ L) :
    rho a x ∈ L := by
  rw [← hL a]
  exact ⟨x, hx, rfl⟩

@[simp]
theorem isInvariantSubgroup_bot
    {A H : Type*} [Group A] [Group H]
    (rho : A →* MulAut H) :
    IsInvariantSubgroup rho ⊥ := by
  intro a
  simp

@[simp]
theorem isInvariantSubgroup_top
    {A H : Type*} [Group A] [Group H]
    (rho : A →* MulAut H) :
    IsInvariantSubgroup rho ⊤ := by
  intro a
  exact Subgroup.map_top_of_surjective
    (rho a).toMonoidHom (rho a).surjective

/-- The intersection of two invariant subgroups is invariant. -/
theorem IsInvariantSubgroup.inf
    {A H : Type*} [Group A] [Group H]
    {rho : A →* MulAut H} {L K : Subgroup H}
    (hL : IsInvariantSubgroup rho L)
    (hK : IsInvariantSubgroup rho K) :
    IsInvariantSubgroup rho (L ⊓ K) := by
  intro a
  rw [Subgroup.map_inf _ _ _ (rho a).injective, hL a, hK a]

/-- The supremum of two invariant subgroups is invariant. -/
theorem IsInvariantSubgroup.sup
    {A H : Type*} [Group A] [Group H]
    {rho : A →* MulAut H} {L K : Subgroup H}
    (hL : IsInvariantSubgroup rho L)
    (hK : IsInvariantSubgroup rho K) :
    IsInvariantSubgroup rho (L ⊔ K) := by
  intro a
  rw [Subgroup.map_sup, hL a, hK a]

/-- An arbitrary supremum of invariant subgroups is invariant. -/
theorem IsInvariantSubgroup.iSup
    {A H I : Type*} [Group A] [Group H]
    {rho : A →* MulAut H} {L : I → Subgroup H}
    (hL : ∀ i, IsInvariantSubgroup rho (L i)) :
    IsInvariantSubgroup rho (⨆ i, L i) := by
  intro a
  rw [Subgroup.map_iSup]
  congr 1
  funext i
  exact hL i a

/-- The supremum of a finite family of invariant subgroups is invariant. -/
theorem IsInvariantSubgroup.finsetSup
    {A H I : Type*} [Group A] [Group H]
    {rho : A →* MulAut H} (s : Finset I) {L : I → Subgroup H}
    (hL : ∀ i ∈ s, IsInvariantSubgroup rho (L i)) :
    IsInvariantSubgroup rho (s.sup L) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isInvariantSubgroup_bot rho
  | @insert i s hi ih =>
      rw [Finset.sup_insert]
      exact (hL i (Finset.mem_insert_self i s)).sup
        (ih fun j hj ↦ hL j (Finset.mem_insert_of_mem hj))

/-- A finite family of minimal invariant subgroups has a supremum-independent
subfamily with the same supremum. -/
theorem exists_supIndep_subfamily_of_minimal_invariant
    {A H I : Type*} [Group A] [Group H]
    (rho : A →* MulAut H) (L : I → Subgroup H)
    (hL_ne : ∀ i, L i ≠ ⊥)
    (hL_inv : ∀ i, IsInvariantSubgroup rho (L i))
    (hL_min : ∀ i (K : Subgroup H), K ≤ L i → K ≠ ⊥ →
      IsInvariantSubgroup rho K → K = L i)
    (t : Finset I) :
    ∃ s : Finset I, s ⊆ t ∧ s.SupIndep L ∧ s.sup L = t.sup L := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ s : Finset I, s ⊆ t ∧ s.sup L = t.sup L ∧ s.card = n
  have hP : ∃ n, P n :=
    ⟨t.card, t, Finset.Subset.rfl, rfl, rfl⟩
  obtain ⟨s, hst, hsup, hcard⟩ := Nat.find_spec hP
  refine ⟨s, hst, ?_, hsup⟩
  rw [Finset.supIndep_iff_disjoint_erase]
  intro i his
  rw [disjoint_iff]
  by_contra hmeet
  have hmeet_inv : IsInvariantSubgroup rho (L i ⊓ (s.erase i).sup L) :=
    (hL_inv i).inf
      (IsInvariantSubgroup.finsetSup (s.erase i) fun j _ ↦ hL_inv j)
  have hmeet_eq : L i ⊓ (s.erase i).sup L = L i :=
    hL_min i (L i ⊓ (s.erase i).sup L) inf_le_left hmeet hmeet_inv
  have hi_le : L i ≤ (s.erase i).sup L := by
    rw [← hmeet_eq]
    exact inf_le_right
  have herase_sup : (s.erase i).sup L = t.sup L := by
    have hs_erase : s.sup L = (s.erase i).sup L := by
      calc
        s.sup L = (insert i (s.erase i)).sup L :=
          congrArg (fun u : Finset I ↦ u.sup L)
            (Finset.insert_erase his).symm
        _ = (s.erase i).sup L := by
          rw [Finset.sup_insert, sup_eq_right.mpr hi_le]
    calc
      (s.erase i).sup L = s.sup L := hs_erase.symm
      _ = t.sup L := hsup
  have herase_sub : s.erase i ⊆ t :=
    (Finset.erase_subset i s).trans hst
  have hP_erase : P (s.erase i).card :=
    ⟨s.erase i, herase_sub, herase_sup, rfl⟩
  have hminimal : Nat.find hP ≤ (s.erase i).card :=
    Nat.find_min' hP hP_erase
  have hsmaller : (s.erase i).card < Nat.find hP := by
    rw [← hcard]
    exact Finset.card_erase_lt_of_mem his
  exact (Nat.not_lt_of_ge hminimal) hsmaller

/-! ## Pointwise kernels and conjugate subgroups -/

/-- The subgroup of acting elements fixing every point of `L`. -/
def pointwiseActionKernel
    {A H : Type*} [Group A] [Group H]
    (rho : A →* MulAut H) (L : Subgroup H) : Subgroup A where
  carrier := {a | ∀ x, x ∈ L → rho a x = x}
  one_mem' := by
    intro x hx
    simp
  mul_mem' := by
    intro a b ha hb x hx
    change rho (a * b) x = x
    rw [map_mul]
    change rho a (rho b x) = x
    rw [hb x hx, ha x hx]
  inv_mem' := by
    intro a ha x hx
    change rho a⁻¹ x = x
    apply (rho a).injective
    simp [map_inv, ha x hx]

@[simp]
theorem mem_pointwiseActionKernel_iff
    {A H : Type*} [Group A] [Group H]
    (rho : A →* MulAut H) (L : Subgroup H) (a : A) :
    a ∈ pointwiseActionKernel rho L ↔
      ∀ x, x ∈ L → rho a x = x :=
  Iff.rfl

/-- The pointwise kernel on an invariant subgroup is normal. -/
theorem pointwiseActionKernel_normal
    {A H : Type*} [Group A] [Group H]
    (rho : A →* MulAut H) (L : Subgroup H)
    (hL : IsInvariantSubgroup rho L) :
    (pointwiseActionKernel rho L).Normal := by
  refine ⟨?_⟩
  intro a ha b
  change ∀ x, x ∈ L → rho (b * a * b⁻¹) x = x
  change ∀ x, x ∈ L → rho a x = x at ha
  intro x hx
  simp only [map_mul, map_inv]
  change rho b (rho a ((rho b)⁻¹ x)) = x
  have hx' : (rho b)⁻¹ x ∈ L := by
    simpa [map_inv] using hL.mem b⁻¹ hx
  rw [ha ((rho b)⁻¹ x) hx']
  simp

/-- The restricted action has the pointwise kernel on its invariant domain. -/
theorem restrictMulAutHom_ker_eq_pointwiseActionKernel
    {A H : Type*} [Group A] [Group H]
    (rho : A →* MulAut H) (L : Subgroup H)
    (hL : IsInvariantSubgroup rho L) :
    (restrictMulAutHom L rho hL).ker =
      pointwiseActionKernel rho L := by
  ext a
  rw [MonoidHom.mem_ker, mem_pointwiseActionKernel_iff]
  constructor
  · intro ha x hx
    let xL : L := ⟨x, hx⟩
    have hax := DFunLike.congr_fun ha xL
    exact congrArg Subtype.val hax
  · intro ha
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact ha x x.property

/-- The image of a subgroup under one automorphism from an action. -/
def actionConjugate
    {A H : Type*} [Group A] [Group H]
    (rho : A →* MulAut H) (L : Subgroup H) (a : A) : Subgroup H :=
  L.map (rho a).toMonoidHom

/-- Membership in an action-conjugate subgroup, expressed using the inverse. -/
theorem mem_actionConjugate_iff
    {A H : Type*} [Group A] [Group H]
    (rho : A →* MulAut H) (L : Subgroup H) (a : A) (x : H) :
    x ∈ actionConjugate rho L a ↔ (rho a).symm x ∈ L := by
  exact Subgroup.mem_map_equiv

@[simp]
theorem actionConjugate_one
    {A H : Type*} [Group A] [Group H]
    (rho : A →* MulAut H) (L : Subgroup H) :
    actionConjugate rho L 1 = L := by
  simp only [actionConjugate, map_one]
  change L.map (MulEquiv.refl H).toMonoidHom = L
  change L.map (MonoidHom.id H) = L
  exact L.map_id

/-- Action-conjugating by a product is successive action-conjugation. -/
theorem actionConjugate_mul
    {A H : Type*} [Group A] [Group H]
    (rho : A →* MulAut H) (L : Subgroup H) (a b : A) :
    actionConjugate rho L (a * b) =
      actionConjugate rho (actionConjugate rho L b) a := by
  ext x
  simp only [mem_actionConjugate_iff, map_mul]
  rfl

/-! ## Internal direct-product families -/

/-- An indexed family whose factors generate the ambient group independently
and commute pairwise. -/
def IsInternalDirectProductFamily
    {I H : Type*} [Group H] (A : I → Subgroup H) : Prop :=
  (⨆ i, A i) = ⊤ ∧
    iSupIndep A ∧
    ∀ i j, i ≠ j →
      ∀ x, x ∈ A i → ∀ y, y ∈ A j → Commute x y

/-- The cardinality of a finite internal direct product is the product of the
factor cardinalities. -/
theorem natCard_eq_prod_of_isInternalDirectProductFamily
    {I H : Type*} [Group H] [Finite H] [Finite I]
    (A : I → Subgroup H) (hA : IsInternalDirectProductFamily A) :
    letI := Fintype.ofFinite I
    Nat.card H = ∏ i, Nat.card (A i) := by
  classical
  letI := Fintype.ofFinite I
  have hcomm : Pairwise fun i j : I =>
      ∀ x y : H, x ∈ A i → y ∈ A j → Commute x y := by
    intro i j hij x y hx hy
    exact hA.2.2 i j hij x hx y hy
  let phi : ((i : I) → A i) →* H :=
    Subgroup.noncommPiCoprod hcomm
  have hphi_injective : Function.Injective phi :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep hA.2.1
  have hphi_surjective : Function.Surjective phi := by
    rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range]
    exact hA.1
  let e : ((i : I) → A i) ≃* H :=
    MulEquiv.ofBijective phi ⟨hphi_injective, hphi_surjective⟩
  calc
    Nat.card H = Nat.card ((i : I) → A i) :=
      (Nat.card_congr e.toEquiv).symm
    _ = ∏ i, Nat.card (A i) := Nat.card_pi

/-! ## Conjugating a self-intertwining algebra -/

/-- Conjugation by a compatible represented action preserves self-intertwining
maps. -/
noncomputable def intertwiningConjugate
    {k G A V : Type*} [CommRing k] [Group G] [Group A]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (tau : Representation k A V)
    (alpha : A →* MulAut G)
    (hcompat : ∀ a g v,
      tau a (rho g v) = rho (alpha a g) (tau a v))
    (a : A) (f : Representation.IntertwiningMap rho rho) :
    Representation.IntertwiningMap rho rho where
  toLinearMap :=
    (representationLinearEquiv tau a).conj f.toLinearMap
  isIntertwining' g := by
    ext v
    change tau a (f (tau a⁻¹ (rho g v))) =
      rho g (tau a (f (tau a⁻¹ v)))
    rw [hcompat a⁻¹ g v, f.isIntertwining,
      hcompat a (alpha a⁻¹ g) (f (tau a⁻¹ v))]
    simp

@[simp]
theorem intertwiningConjugate_apply
    {k G A V : Type*} [CommRing k] [Group G] [Group A]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (tau : Representation k A V)
    (alpha : A →* MulAut G)
    (hcompat : ∀ a g v,
      tau a (rho g v) = rho (alpha a g) (tau a v))
    (a : A) (f : Representation.IntertwiningMap rho rho) (v : V) :
    intertwiningConjugate rho tau alpha hcompat a f v =
      tau a (f (tau a⁻¹ v)) :=
  rfl

/-- Conjugation of self-intertwiners as an algebra homomorphism. -/
noncomputable def intertwiningConjugationAlgHom
    {k G A V : Type*} [CommRing k] [Group G] [Group A]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (tau : Representation k A V)
    (alpha : A →* MulAut G)
    (hcompat : ∀ a g v,
      tau a (rho g v) = rho (alpha a g) (tau a v))
    (a : A) :
    Representation.IntertwiningMap rho rho →ₐ[k]
      Representation.IntertwiningMap rho rho where
  toFun := intertwiningConjugate rho tau alpha hcompat a
  map_zero' := by
    ext v
    simp
  map_add' f g := by
    ext v
    simp
  map_one' := by
    ext v
    simp
  map_mul' f g := by
    ext v
    simp
  commutes' c := by
    ext v
    simp [Representation.IntertwiningMap.algebraMap_apply]

@[simp]
theorem intertwiningConjugationAlgHom_apply
    {k G A V : Type*} [CommRing k] [Group G] [Group A]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (tau : Representation k A V)
    (alpha : A →* MulAut G)
    (hcompat : ∀ a g v,
      tau a (rho g v) = rho (alpha a g) (tau a v))
    (a : A) (f : Representation.IntertwiningMap rho rho) (v : V) :
    intertwiningConjugationAlgHom rho tau alpha hcompat a f v =
      tau a (f (tau a⁻¹ v)) :=
  rfl

@[simp]
theorem intertwiningConjugationAlgHom_inv_apply
    {k G A V : Type*} [CommRing k] [Group G] [Group A]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (tau : Representation k A V)
    (alpha : A →* MulAut G)
    (hcompat : ∀ a g v,
      tau a (rho g v) = rho (alpha a g) (tau a v))
    (a : A) (f : Representation.IntertwiningMap rho rho) :
    intertwiningConjugationAlgHom rho tau alpha hcompat a⁻¹
        (intertwiningConjugationAlgHom rho tau alpha hcompat a f) = f := by
  ext v
  simp

/-- Conjugation of self-intertwiners as an algebra equivalence. -/
noncomputable def intertwiningConjugationAlgEquiv
    {k G A V : Type*} [CommRing k] [Group G] [Group A]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (tau : Representation k A V)
    (alpha : A →* MulAut G)
    (hcompat : ∀ a g v,
      tau a (rho g v) = rho (alpha a g) (tau a v))
    (a : A) :
    Representation.IntertwiningMap rho rho ≃ₐ[k]
      Representation.IntertwiningMap rho rho :=
  AlgEquiv.ofBijective
    (intertwiningConjugationAlgHom rho tau alpha hcompat a)
    ⟨fun f g hfg ↦ by
        have h := congrArg
          (intertwiningConjugationAlgHom rho tau alpha hcompat a⁻¹) hfg
        simpa using h,
      fun f ↦ ⟨intertwiningConjugationAlgHom rho tau alpha hcompat a⁻¹ f,
        by
          simpa using
            intertwiningConjugationAlgHom_inv_apply
              rho tau alpha hcompat a⁻¹ f⟩⟩

@[simp]
theorem intertwiningConjugationAlgEquiv_apply
    {k G A V : Type*} [CommRing k] [Group G] [Group A]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (tau : Representation k A V)
    (alpha : A →* MulAut G)
    (hcompat : ∀ a g v,
      tau a (rho g v) = rho (alpha a g) (tau a v))
    (a : A) (f : Representation.IntertwiningMap rho rho) (v : V) :
    intertwiningConjugationAlgEquiv rho tau alpha hcompat a f v =
      tau a (f (tau a⁻¹ v)) :=
  rfl

/-- The compatible conjugations form an action on the self-intertwining
algebra. -/
noncomputable def intertwiningConjugationAlgEquivHom
    {k G A V : Type*} [CommRing k] [Group G] [Group A]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (tau : Representation k A V)
    (alpha : A →* MulAut G)
    (hcompat : ∀ a g v,
      tau a (rho g v) = rho (alpha a g) (tau a v)) :
    A →* (Representation.IntertwiningMap rho rho ≃ₐ[k]
      Representation.IntertwiningMap rho rho) where
  toFun := intertwiningConjugationAlgEquiv rho tau alpha hcompat
  map_one' := by
    ext f v
    simp
  map_mul' a b := by
    ext f v
    simp [mul_assoc]

end

end Submission.OddOrder.PF
