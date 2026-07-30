import Submission.OddOrder.BG.Section15.FittingCoreStructure
import Submission.OddOrder.MathlibSupport.NormalizedTI
import Submission.OddOrder.MathlibSupport.PPrimeCore
import Mathlib.GroupTheory.Exponent

/-!
# Bender--Glauberman Section 16: type and support definitions

This module introduces the Peterfalvi type predicates, the combinatorial
Feit--Thompson type, and its core and Dade support sets.
-/

namespace Submission.OddOrder.BG.Section16

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative commutatorElement

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

def hasElementaryAbelianRankExactlyTwo (H : Subgroup G) : Prop :=
  (exists p : ℕ, p.Prime ∧ HasElementaryAbelianRankAtLeast p 2 H) ∧
    ∀ p : ℕ, p.Prime → ¬ HasElementaryAbelianRankAtLeast p 3 H

def is_typeF_inertia (M U U₁ : Subgroup G) : Prop :=
  U₁ ≤ U ∧
    (U₁.subgroupOf U).Normal ∧
    IsMulCommutative U₁ ∧
    ∀ x ∈ subgroupNonidentity (Fitting_core M),
      elementCentralizerWithin U x ≤ U₁

def is_typeF_complement (M U U₀ : Subgroup G) : Prop :=
  U₀ ≤ U ∧
    Monoid.exponent U₀ = Monoid.exponent U ∧
    IsInternalSemidirectProductIn (Fitting_core M) U₀
      (Fitting_core M ⊔ U₀) ∧
    IsFrobeniusDecomposition
      ((Fitting_core M).subgroupOf (Fitting_core M ⊔ U₀))
      (U₀.subgroupOf (Fitting_core M ⊔ U₀))

def of_typeF (M U : Subgroup G) : Prop :=
  Fitting_core M ≠ ⊥ ∧
    U ≠ ⊥ ∧
    IsInternalSemidirectProductIn (Fitting_core M) U M ∧
    (exists U₁ : Subgroup G, is_typeF_inertia M U U₁) ∧
    exists U₀ : Subgroup G, is_typeF_complement M U U₀

def of_typeI (M U : Subgroup G) : Prop :=
  of_typeF M U ∧
    (IsNormalizedTI (subgroupNonidentity (Fitting_core M)) ⊤ M ∨
      (IsMulCommutative (Fitting_core M) ∧
        hasElementaryAbelianRankExactlyTwo (Fitting_core M)) ∨
      ((∀ p ∈ primeSupport (Nat.card (Fitting_core M)),
          Monoid.exponent U ∣ p - 1) ∧
        ∃ p ∈ primeSupport (Nat.card (Fitting_core M)),
          IsCyclic (pPrimeCore p (Fitting_core M))))

def of_typeP
    (M U W W₁ W₂ : Subgroup G)
    (_defW : IsInternalDirectProductIn W₁ W₂ W) : Prop :=
  (IsCyclic W₁ ∧
      (W₁ ≤ M ∧
        IsHall (primeSupport (Nat.card W₁)) (W₁.subgroupOf M)) ∧
      W₁ ≠ ⊥ ∧
      IsInternalSemidirectProductIn (derivedWithin M) W₁ M) ∧
    (Group.IsNilpotent U ∧
      U ≤ derivedWithin M ∧
      W₁ ≤ Subgroup.normalizer (U : Set G) ∧
      IsInternalSemidirectProductIn (Fitting_core M) U (derivedWithin M)) ∧
    (¬ IsCyclic (Fitting_core M) ∧
      secondDerivedWithin M ≤ fittingWithin M ∧
      Fitting_core M ⊔ centralizerWithin M (Fitting_core M) = fittingWithin M ∧
      fittingWithin M ≤ derivedWithin M) ∧
    (IsCyclic W₂ ∧
      W₂ ≠ ⊥ ∧
      W₂ ≤ Fitting_core M ∧
      W₂ ≤ secondDerivedWithin M ∧
      ∀ x ∈ subgroupNonidentity W₁,
        elementCentralizerWithin (derivedWithin M) x = W₂) ∧
    IsNormalizedTI ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))) ⊤ W

def of_typeII_IV
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop :=
  of_typeP M U W W₁ W₂ defW ∧
    U ≠ ⊥ ∧
    (Nat.card W₁).Prime ∧
    IsNormalizedTI (subgroupNonidentity (fittingWithin M)) ⊤ M

def of_typeII
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop :=
  of_typeII_IV M U W W₁ W₂ defW ∧
    IsMulCommutative U ∧
    ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
    of_typeF (derivedWithin M) U ∧
    Fitting_core (derivedWithin M) = Fitting_core M

def of_typeIII
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop :=
  of_typeII_IV M U W W₁ W₂ defW ∧
    IsMulCommutative U ∧
    Subgroup.normalizer (U : Set G) ≤ M

def of_typeIV
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop :=
  of_typeII_IV M U W W₁ W₂ defW ∧
    ¬ IsMulCommutative U ∧
    Subgroup.normalizer (U : Set G) ≤ M

def of_typeV
    (M U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop :=
  of_typeP M U W W₁ W₂ defW ∧
    U = ⊥ ∧
    (IsNormalizedTI (subgroupNonidentity (Fitting_core M)) ⊤ M ∨
      (∃ p ∈ primeSupport (Nat.card (Fitting_core M)),
        Nat.card W₁ ∣ p - 1 ∧ IsCyclic (pPrimeCore p (Fitting_core M))) ∨
      ∃ p ∈ primeSupport (Nat.card (Fitting_core M)),
        Nat.card (pCore p (Fitting_core M)) = p ^ 3 ∧
          Nat.card W₁ ∣ p + 1 ∧
          IsCyclic (pPrimeCore p (Fitting_core M)))

def exists_typeP
    (spec : ∀ (U W W₁ W₂ : Subgroup G),
      IsInternalDirectProductIn W₁ W₂ W → Prop) : Prop :=
  ∃ U W W₁ W₂ : Subgroup G,
    ∃ defW : IsInternalDirectProductIn W₁ W₂ W,
      spec U W W₁ W₂ defW

def ftTypeSpec (i : ℕ) (M : Subgroup G) : Prop :=
  match i with
  | 1 => ∃ U : Subgroup G, of_typeI M U
  | 2 => exists_typeP (of_typeII M)
  | 3 => exists_typeP (of_typeIII M)
  | 4 => exists_typeP (of_typeIV M)
  | 5 => exists_typeP (of_typeV M)
  | _ => False

abbrev FTtype_spec (i : ℕ) (M : Subgroup G) : Prop := ftTypeSpec i M

def fittingCoreQuotientAbelian (M : Subgroup G) : Prop :=
  derivedWithin (sigmaCore M) ≤ Fitting_core M

noncomputable def ftType (M : Subgroup G) : ℕ := by
  classical
  exact if IsPiNumber (kappaPrimes M)ᶜ (Nat.card M) then 1
    else if sigmaCore M ≠ derivedWithin M then 2
    else if Fitting_core M = sigmaCore M then 5
    else if fittingCoreQuotientAbelian M then 3
    else 4

abbrev FTtype (M : Subgroup G) : ℕ := ftType M

theorem FTtype_range (M : Subgroup G) :
    0 < FTtype M ∧ FTtype M ≤ 5 := by
  classical
  unfold FTtype ftType
  split_ifs <;> omega

def ftCore (M : Subgroup G) : Subgroup G :=
  if 0 < FTtype M ∧ FTtype M ≤ 2 then Fitting_core M
  else derivedWithin M

abbrev FTcore (M : Subgroup G) : Subgroup G := ftCore M

theorem FTcore_is_group (M : Subgroup G) :
    ∃ H : Subgroup G, (H : Set G) = (FTcore M : Set G) :=
  ⟨FTcore M, rfl⟩

abbrev FTcore_group (M : Subgroup G) : Subgroup G := FTcore M

def ftSupport1 (M : Subgroup G) : Set G :=
  subgroupNonidentity (FTcore M)

abbrev FTsupport1 (M : Subgroup G) : Set G := ftSupport1 M

def ftDerived (M : Subgroup G) : Subgroup G :=
  if FTtype M = 1 then M else derivedWithin M

abbrev FTder (M : Subgroup G) : Subgroup G := ftDerived M

def ftSupport (M : Subgroup G) : Set G :=
  ⋃ x ∈ FTsupport1 M,
    subgroupNonidentity (elementCentralizerWithin (FTder M) x)

abbrev FTsupport (M : Subgroup G) : Set G := ftSupport M

def ftSupport0 (M : Subgroup G) : Set G :=
  let pi := primeSupport (Nat.card (FTder M))
  FTsupport M ∪
    {x : G | x ∈ M ∧
      ¬ IsPiNumber pi (orderOf x) ∧
      ¬ IsPiNumber piᶜ (orderOf x)}

abbrev FTsupport0 (M : Subgroup G) : Set G := ftSupport0 M

def subgroupConjugacyStep
    (U : Subgroup G) (M N : Subgroup G) : Prop :=
  ∃ u : G, u ∈ U ∧ N = M.map (MulAut.conj u).toMonoidHom

def AreConjugateSubgroupsWithin
    (U : Subgroup G) (M N : Subgroup G) : Prop :=
  Relation.EqvGen (subgroupConjugacyStep U) M N

def maximalSubgroupConjugacySetoid (U : Subgroup G) :
    Setoid {M : Subgroup G // M ∈ minSimple_max_groups (G := G)} where
  r M N := AreConjugateSubgroupsWithin U M.1 N.1
  iseqv :=
    { refl := by
        intro M
        change Relation.EqvGen (subgroupConjugacyStep U) M.1 M.1
        exact Relation.EqvGen.refl M.1
      symm := by
        intro M N hMN
        change Relation.EqvGen (subgroupConjugacyStep U) M.1 N.1 at hMN
        change Relation.EqvGen (subgroupConjugacyStep U) N.1 M.1
        exact Relation.EqvGen.symm M.1 N.1 hMN
      trans := by
        intro M N P hMN hNP
        change Relation.EqvGen (subgroupConjugacyStep U) M.1 N.1 at hMN
        change Relation.EqvGen (subgroupConjugacyStep U) N.1 P.1 at hNP
        change Relation.EqvGen (subgroupConjugacyStep U) M.1 P.1
        exact Relation.EqvGen.trans M.1 N.1 P.1 hMN hNP }

noncomputable def mmax_transversal (U : Subgroup G) : Set (Subgroup G) :=
  {M | ∃ q : Quotient (maximalSubgroupConjugacySetoid U),
    M = (Quotient.out q).1}

theorem mmax_transversal_subset (U : Subgroup G) :
    mmax_transversal U ⊆ minSimple_max_groups (G := G) := by
  rintro M ⟨q, rfl⟩
  exact (Quotient.out q).2

theorem exists_mem_mmax_transversal_conjugate
    (U M : Subgroup G) (hM : M ∈ minSimple_max_groups (G := G)) :
    ∃ N ∈ mmax_transversal U,
      AreConjugateSubgroupsWithin U M N := by
  let A : {L : Subgroup G // L ∈ minSimple_max_groups (G := G)} := ⟨M, hM⟩
  let S := maximalSubgroupConjugacySetoid U
  let q : Quotient S := Quotient.mk S A
  let R := Quotient.out q
  have hR : Quotient.mk S R = q := Quotient.out_eq q
  have hA : Quotient.mk S A = q := rfl
  have hrel : AreConjugateSubgroupsWithin U M R.1 := by
    have hRA : R ≈ A := Quotient.exact (hR.trans hA.symm)
    change AreConjugateSubgroupsWithin U R.1 A.1 at hRA
    change Relation.EqvGen (subgroupConjugacyStep U) M R.1
    simpa [A] using Relation.EqvGen.symm R.1 A.1 hRA
  exact ⟨R.1, ⟨q, rfl⟩, hrel⟩

theorem mmax_transversal_conjugate_injective
    (U : Subgroup G) {M N : Subgroup G}
    (hM : M ∈ mmax_transversal U)
    (hN : N ∈ mmax_transversal U)
    (hMN : AreConjugateSubgroupsWithin U M N) :
    M = N := by
  rcases hM with ⟨q, rfl⟩
  rcases hN with ⟨r, rfl⟩
  have hMN' :
      (maximalSubgroupConjugacySetoid U).r (Quotient.out q) (Quotient.out r) := by
    change AreConjugateSubgroupsWithin U (Quotient.out q).1 (Quotient.out r).1
    exact hMN
  have hmk :
      Quotient.mk (maximalSubgroupConjugacySetoid U) (Quotient.out q) =
        Quotient.mk (maximalSubgroupConjugacySetoid U) (Quotient.out r) :=
    Quotient.sound hMN'
  have hqr : q = r := by
    rw [← Quotient.out_eq q, ← Quotient.out_eq r]
    exact hmk
  simpa [hqr]

def IsCharacteristicWithin (K M : Subgroup G) : Prop :=
  K ≤ M ∧ (K.subgroupOf M).Characteristic

def IsNormalWithin (K M : Subgroup G) : Prop :=
  K ≤ M ∧ (K.subgroupOf M).Normal

private theorem derivedWithin_le16 (M : Subgroup G) :
    derivedWithin M ≤ M := by
  exact Subgroup.map_subtype_le (_root_.commutator M)

private theorem derivedWithin_subgroupOf_eq16 (M : Subgroup G) :
    (derivedWithin M).subgroupOf M = _root_.commutator M := by
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (derivedWithin_le16 M)]
  rfl

private theorem derivedWithin_characteristicWithin (M : Subgroup G) :
    IsCharacteristicWithin (derivedWithin M) M := by
  refine ⟨derivedWithin_le16 M, ?_⟩
  rw [derivedWithin_subgroupOf_eq16]
  infer_instance

theorem FTcore_char (M : Subgroup G) :
    IsCharacteristicWithin (FTcore M) M := by
  classical
  unfold FTcore ftCore
  split_ifs
  · exact ⟨Fcore_sub M, Fcore_char M⟩
  · exact derivedWithin_characteristicWithin M

theorem FTcore_normal (M : Subgroup G) :
    IsNormalWithin (FTcore M) M := by
  rcases FTcore_char M with ⟨hsub, hchar⟩
  letI : ((FTcore M).subgroupOf M).Characteristic := hchar
  exact ⟨hsub, inferInstance⟩

theorem FTcore_norm (M : Subgroup G) :
    M ≤ Subgroup.normalizer (FTcore M : Set G) := by
  rcases FTcore_normal M with ⟨hsub, hnormal⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hsub).mp hnormal

theorem FTcore_sub (M : Subgroup G) : FTcore M ≤ M :=
  (FTcore_char M).1

theorem FTcore_type1 (M : Subgroup G)
    (hM : FTtype M = 1) :
    FTcore M = Fitting_core M := by
  simp [FTcore, ftCore, hM]

theorem FTcore_type2 (M : Subgroup G)
    (hM : FTtype M = 2) :
    FTcore M = Fitting_core M := by
  simp [FTcore, ftCore, hM]

theorem FTcore_type_gt2 (M : Subgroup G)
    (hM : 2 < FTtype M) :
    FTcore M = derivedWithin M := by
  have hnot : ¬ FTtype M ≤ 2 := Nat.not_le_of_lt hM
  simp [FTcore, ftCore, hnot]

theorem FTsupp1_type1 (M : Subgroup G)
    (hM : FTtype M = 1) :
    FTsupport1 M = subgroupNonidentity (Fitting_core M) := by
  rw [show FTsupport1 M = subgroupNonidentity (FTcore M) by rfl]
  rw [FTcore_type1 M hM]

theorem FTsupp1_type2 (M : Subgroup G)
    (hM : FTtype M = 2) :
    FTsupport1 M = subgroupNonidentity (Fitting_core M) := by
  rw [show FTsupport1 M = subgroupNonidentity (FTcore M) by rfl]
  rw [FTcore_type2 M hM]

theorem FTsupp1_type_gt2 (M : Subgroup G)
    (hM : 2 < FTtype M) :
    FTsupport1 M = subgroupNonidentity (derivedWithin M) := by
  rw [show FTsupport1 M = subgroupNonidentity (FTcore M) by rfl]
  rw [FTcore_type_gt2 M hM]

end

end Submission.OddOrder.BG.Section16
