import Mathlib.Algebra.Group.Subgroup.Finsupp
import Mathlib.Data.Set.Card
import Submission.OddOrder.PF.Section01.BrauerPermutation
import Submission.OddOrder.PF.Section01.RestrictionComplementEquivalence
import Submission.OddOrder.PF.Section04.PrimeTIReducedCharacters
import Submission.OddOrder.PF.Section05.InducedIrreducibles

/-!
# Coherence of families of characters

This file ports the foundational definitions and elementary constructions at
the beginning of Peterfalvi Section 5 (`PFsection5.v`, lines 446--633).

The source uses duplicate-free sequences.  Here a family is represented by a
set of class functions, and its integral span `'Z[S]` is represented by
`AddSubgroup.closure S`.  This agrees with the family produced by
`uniform_prTIred_coherent` in Section 4.  The source permits merely additive
coherence maps; in the Lean development they are complex-linear.  This is the
form used throughout the odd-order proof and makes the pivot extension a
direct rank-one linear construction.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

local instance coherenceBasicsInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

namespace ClassFunction

/-- A class function is a virtual character if it is in the image of the
integral irreducible-character lattice. -/
def IsVirtual {H : Type u} [Group H] (phi : ClassFunction H ℂ) : Prop :=
  ∃ z : VirtualCharacter H ℂ, VirtualCharacter.realize z = phi

namespace IsVirtual

variable {H : Type u} [Group H]

protected theorem zero : IsVirtual (0 : ClassFunction H ℂ) :=
  ⟨0, by simp⟩

protected theorem add {phi psi : ClassFunction H ℂ}
    (hphi : IsVirtual phi) (hpsi : IsVirtual psi) :
    IsVirtual (phi + psi) := by
  obtain ⟨a, rfl⟩ := hphi
  obtain ⟨b, rfl⟩ := hpsi
  exact ⟨a + b, by simp⟩

protected theorem neg {phi : ClassFunction H ℂ}
    (hphi : IsVirtual phi) : IsVirtual (-phi) := by
  obtain ⟨a, rfl⟩ := hphi
  exact ⟨-a, by simp⟩

protected theorem sub {phi psi : ClassFunction H ℂ}
    (hphi : IsVirtual phi) (hpsi : IsVirtual psi) :
    IsVirtual (phi - psi) := by
  rw [sub_eq_add_neg]
  exact hphi.add hpsi.neg

protected theorem zsmul {phi : ClassFunction H ℂ}
    (hphi : IsVirtual phi) (n : ℤ) : IsVirtual (n • phi) := by
  obtain ⟨a, rfl⟩ := hphi
  exact ⟨n • a, by simp⟩

protected theorem nsmul {phi : ClassFunction H ℂ}
    (hphi : IsVirtual phi) (n : ℕ) : IsVirtual (n • phi) := by
  obtain ⟨a, rfl⟩ := hphi
  exact ⟨n • a, by simp⟩

protected theorem natCast_smul {phi : ClassFunction H ℂ}
    (hphi : IsVirtual phi) (n : ℕ) : IsVirtual ((n : ℂ) • phi) := by
  simpa only [Nat.cast_smul_eq_nsmul] using hphi.nsmul n

end IsVirtual

end ClassFunction

/-- Closure of a family under contragredient duality (source `cfConjC_closed`). -/
def cfConjC_closed {H : Type u} [Group H]
    (S : Set (ClassFunction H ℂ)) : Prop :=
  ∀ phi ∈ S,
    ClassFunction.inverseLinear (G := H) (k := ℂ) phi ∈ S

/-- A dual-closed subfamily of another family (source `cfConjC_subset`). -/
def cfConjC_subset {H : Type u} [Group H]
    (S T : Set (ClassFunction H ℂ)) : Prop :=
  S ⊆ T ∧ cfConjC_closed S

variable {L G : Type u} [Group L] [Fintype L] [Group G] [Fintype G]

/-- Peterfalvi Definition 5.1.  The map `nu` is an isometry on the integral
span of `S`, has virtual-character values there, and agrees with `tau` on the
part supported by `A`. -/
structure coherent_with
    (S : Set (ClassFunction L ℂ)) (A : Set L)
    (tau nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ) : Prop where
  isometry : ∀ phi ∈ AddSubgroup.closure S,
    ∀ psi ∈ AddSubgroup.closure S,
      characterPairing (nu phi) (nu psi) = characterPairing phi psi
  mapsToVirtual : ∀ phi ∈ AddSubgroup.closure S,
    ClassFunction.IsVirtual (nu phi)
  agrees : ∀ phi ∈ AddSubgroup.closure S,
    phi ∈ ClassFunction.supportedOn A → nu phi = tau phi

/-- A family is coherent if it admits a coherence isometry. -/
def coherent (S : Set (ClassFunction L ℂ)) (A : Set L)
    (tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ) : Prop :=
  ∃ nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ,
    coherent_with S A tau nu

/-- Peterfalvi Hypothesis 5.2.  Besides the structural properties of the
source family, this packages the partial isometry `tau` and the orthonormal
target pairs `R xi` used in the subsequent subcoherence arguments. -/
structure subcoherent
    (S : Set (ClassFunction L ℂ))
    (tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)) : Prop where
  finite : S.Finite
  source_character : ∀ phi ∈ S,
    ClassFunction.IsOrdinaryCharacter (k := ℂ) phi
  source_virtual : ∀ phi ∈ S, ClassFunction.IsVirtual phi
  zero_not_mem : (0 : ClassFunction L ℂ) ∉ S
  degree_ne_zero : ∀ phi ∈ S, phi 1 ≠ 0
  inverse_ne : ∀ phi ∈ S,
    ClassFunction.inverseLinear (G := L) (k := ℂ) phi ≠ phi
  inverse_mem : cfConjC_closed S
  tau_isometry : ∀ phi ∈ AddSubgroup.closure S,
    phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
    ∀ psi ∈ AddSubgroup.closure S,
      psi ∈ ClassFunction.supportedOn (nonidentitySet L) →
      characterPairing (tau phi) (tau psi) = characterPairing phi psi
  tau_virtual : ∀ phi ∈ AddSubgroup.closure S,
    phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
      ClassFunction.IsVirtual (tau phi)
  tau_supported : ∀ phi ∈ AddSubgroup.closure S,
    phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
      tau phi ∈ ClassFunction.supportedOn (nonidentitySet G)
  pairwise_orthogonal :
    S.Pairwise (fun phi psi ↦ characterPairing phi psi = 0)
  image_virtual : ∀ xi ∈ S, ∀ alpha ∈ R xi,
    ClassFunction.IsVirtual alpha
  image_orthonormal : ∀ xi ∈ S, ∀ alpha ∈ R xi, ∀ beta ∈ R xi,
    characterPairing alpha beta = if alpha = beta then 1 else 0
  tau_inverse_sub : ∀ xi ∈ S,
    tau (xi - ClassFunction.inverseLinear (G := L) (k := ℂ) xi) =
      ∑ alpha ∈ R xi, alpha
  image_orthogonal : ∀ xi ∈ S, ∀ phi ∈ S,
    characterPairing phi xi = 0 →
    characterPairing phi
      (ClassFunction.inverseLinear (G := L) (k := ℂ) xi) = 0 →
    ∀ alpha ∈ R phi, ∀ beta ∈ R xi,
      characterPairing alpha beta = 0

/-- The dual of a coherence isometry: precompose with inversion and negate. -/
def dual_iso
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ) :
    ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  -(nu.comp (ClassFunction.inverseLinear (G := L) (k := ℂ)))

@[simp]
theorem dual_iso_apply
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (phi : ClassFunction L ℂ) :
    dual_iso nu phi =
      -nu (ClassFunction.inverseLinear (G := L) (k := ℂ) phi) :=
  rfl

private theorem closure_mono_of_subset_closure
    {S₁ S₂ : Set (ClassFunction L ℂ)}
    (hS : S₂ ⊆ AddSubgroup.closure S₁) :
    AddSubgroup.closure S₂ ≤ AddSubgroup.closure S₁ :=
  (AddSubgroup.closure_le (AddSubgroup.closure S₁)).2 hS

/-- Coherence passes to any family contained in the integral span. -/
theorem subgen_coherent
    {S₁ S₂ : Set (ClassFunction L ℂ)} {A : Set L}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hS : S₂ ⊆ AddSubgroup.closure S₁)
    (hcoh : coherent S₁ A tau) : coherent S₂ A tau := by
  obtain ⟨nu, hnu⟩ := hcoh
  refine ⟨nu, ?_⟩
  have hspan := closure_mono_of_subset_closure hS
  exact
    { isometry := fun phi hphi psi hpsi ↦
        hnu.isometry phi (hspan hphi) psi (hspan hpsi)
      mapsToVirtual := fun phi hphi ↦
        hnu.mapsToVirtual phi (hspan hphi)
      agrees := fun phi hphi hsupp ↦
        hnu.agrees phi (hspan hphi) hsupp }

/-- Coherence passes to a subfamily. -/
theorem subset_coherent
    {S₁ S₂ : Set (ClassFunction L ℂ)} {A : Set L}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hS : S₂ ⊆ S₁) (hcoh : coherent S₁ A tau) :
    coherent S₂ A tau :=
  subgen_coherent (fun phi hphi ↦ AddSubgroup.subset_closure (hS hphi)) hcoh

/-- A fixed coherence witness for a family also witnesses every subfamily. -/
theorem subset_coherent_with
    {S₁ S₂ : Set (ClassFunction L ℂ)} {A : Set L}
    {tau nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hS : S₁ ⊆ S₂) (hcoh : coherent_with S₂ A tau nu) :
    coherent_with S₁ A tau nu := by
  have hspan : AddSubgroup.closure S₁ ≤ AddSubgroup.closure S₂ :=
    AddSubgroup.closure_mono hS
  exact
    { isometry := fun phi hphi psi hpsi ↦
        hcoh.isometry phi (hspan hphi) psi (hspan hpsi)
      mapsToVirtual := fun phi hphi ↦
        hcoh.mapsToVirtual phi (hspan hphi)
      agrees := fun phi hphi hsupp ↦
        hcoh.agrees phi (hspan hphi) hsupp }

/-- Extensional permutation of the source family preserves coherence. -/
theorem perm_coherent
    {S₁ S₂ : Set (ClassFunction L ℂ)} {A : Set L}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hS : S₁ = S₂) (hcoh : coherent S₁ A tau) :
    coherent S₂ A tau := by
  simpa only [hS] using hcoh

private theorem characterPairing_neg_left
    {H : Type u} [Group H] [Fintype H]
    (phi psi : ClassFunction H ℂ) :
    characterPairing (-phi) psi = -characterPairing phi psi := by
  calc
    characterPairing (-phi) psi =
        characterPairing ((-1 : ℂ) • phi) psi := by
      rw [neg_one_smul ℂ phi]
    _ = (-1 : ℂ) * characterPairing phi psi :=
      characterPairing_smul_left (-1 : ℂ) phi psi
    _ = -characterPairing phi psi := neg_one_mul _

private theorem characterPairing_neg_right
    {H : Type u} [Group H] [Fintype H]
    (phi psi : ClassFunction H ℂ) :
    characterPairing phi (-psi) = -characterPairing phi psi := by
  calc
    characterPairing phi (-psi) =
        characterPairing phi ((-1 : ℂ) • psi) := by
      rw [neg_one_smul ℂ psi]
    _ = (-1 : ℂ) * characterPairing phi psi :=
      characterPairing_smul_right (-1 : ℂ) phi psi
    _ = -characterPairing phi psi := neg_one_mul _

private theorem characterPairing_sub_left
    {H : Type u} [Group H] [Fintype H]
    (phi psi theta : ClassFunction H ℂ) :
    characterPairing (phi - psi) theta =
      characterPairing phi theta - characterPairing psi theta := by
  rw [sub_eq_add_neg, characterPairing_add_left,
    characterPairing_neg_left, sub_eq_add_neg]

private theorem characterPairing_sub_right
    {H : Type u} [Group H] [Fintype H]
    (phi psi theta : ClassFunction H ℂ) :
    characterPairing phi (psi - theta) =
      characterPairing phi psi - characterPairing phi theta := by
  rw [sub_eq_add_neg, characterPairing_add_right,
    characterPairing_neg_right, sub_eq_add_neg]

private theorem inverseLinear_involutive
    {H : Type u} [Group H] (phi : ClassFunction H ℂ) :
    ClassFunction.inverseLinear (G := H) (k := ℂ)
        (ClassFunction.inverseLinear (G := H) (k := ℂ) phi) = phi := by
  ext x
  simp

private theorem characterPairing_inverseLinear
    {H : Type u} [Group H] [Fintype H]
    (phi psi : ClassFunction H ℂ) :
    characterPairing
        (ClassFunction.inverseLinear (G := H) (k := ℂ) phi)
        (ClassFunction.inverseLinear (G := H) (k := ℂ) psi) =
      characterPairing phi psi := by
  unfold characterPairing
  congr 1
  refine Fintype.sum_equiv (Equiv.inv H) _ _ fun x ↦ ?_
  simp only [Equiv.inv_apply, ClassFunction.inverseLinear_apply, inv_inv]

private theorem inverseLinear_mem_closure
    {S : Set (ClassFunction L ℂ)} (hclosed : cfConjC_closed S)
    {phi : ClassFunction L ℂ} (hphi : phi ∈ AddSubgroup.closure S) :
    ClassFunction.inverseLinear (G := L) (k := ℂ) phi ∈
      AddSubgroup.closure S := by
  induction hphi using AddSubgroup.closure_induction with
  | mem phi hphi => exact AddSubgroup.subset_closure (hclosed phi hphi)
  | zero => simpa using (AddSubgroup.closure S).zero_mem
  | add phi psi hphi hpsi ihphi ihpsi =>
      simpa only [map_add] using (AddSubgroup.closure S).add_mem ihphi ihpsi
  | neg phi hphi ihphi =>
      simpa only [map_neg] using (AddSubgroup.closure S).neg_mem ihphi

private theorem inverse_sub_supported
    (phi : ClassFunction L ℂ) :
    phi - ClassFunction.inverseLinear (G := L) (k := ℂ) phi ∈
      ClassFunction.supportedOn (nonidentitySet L) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxone : x = 1 := by simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp

private theorem inverseLinear_eq_neg_of_small_closed_family
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R) (hcard : S.ncard ≤ 2)
    {phi : ClassFunction L ℂ} (hphi : phi ∈ AddSubgroup.closure S)
    (hoff : phi ∈ ClassFunction.supportedOn (nonidentitySet L)) :
    ClassFunction.inverseLinear (G := L) (k := ℂ) phi = -phi := by
  by_cases hS : S = ∅
  · subst S
    have hphi0 : phi = 0 := by
      have : phi ∈ (⊥ : AddSubgroup (ClassFunction L ℂ)) := by
        simpa using hphi
      simpa using this
    subst phi
    simp
  · obtain ⟨eta, heta⟩ := Set.nonempty_iff_ne_empty.mpr hS
    let eta' := ClassFunction.inverseLinear (G := L) (k := ℂ) eta
    have heta'S : eta' ∈ S := hsub.inverse_mem eta heta
    have heta_ne : eta ≠ eta' := by
      exact fun heq ↦ hsub.inverse_ne eta heta heq.symm
    have hpairS : ({eta, eta'} : Set (ClassFunction L ℂ)) ⊆ S :=
      Set.pair_subset heta heta'S
    have htwo_le : 2 ≤ S.ncard := by
      rw [← Set.ncard_pair heta_ne]
      exact Set.ncard_le_ncard hpairS hsub.finite
    have hScard : S.ncard = 2 := Nat.le_antisymm hcard htwo_le
    have hpairEq : ({eta, eta'} : Set (ClassFunction L ℂ)) = S := by
      exact Set.eq_of_subset_of_ncard_le hpairS
        (by simpa [Set.ncard_pair heta_ne, hScard]) hsub.finite
    have hphiPair :
        phi ∈ AddSubgroup.closure
          ({eta, eta'} : Set (ClassFunction L ℂ)) := by
      rw [hpairEq]
      exact hphi
    obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hphiPair
    have hphiOne : phi 1 = 0 :=
      ClassFunction.eq_zero_of_mem_supportedOn hoff (by simp [nonidentitySet])
    have hcoeffMul : (((m + n : ℤ) : ℂ) * eta 1) = 0 := by
      have hrep : phi = m • eta + n • eta' := hmn.symm
      have hvalue := congrArg (fun f : ClassFunction L ℂ ↦ f 1) hrep
      rw [← Int.cast_smul_eq_zsmul ℂ,
        ← Int.cast_smul_eq_zsmul ℂ] at hvalue
      simp only [ClassFunction.add_apply, ClassFunction.smul_apply,
        eta', ClassFunction.inverseLinear_apply, inv_one,
        smul_eq_mul] at hvalue
      rw [Int.cast_add]
      calc
        ((m : ℂ) + (n : ℂ)) * eta 1 =
            (m : ℂ) * eta 1 + (n : ℂ) * eta 1 := by ring
        _ = phi 1 := hvalue.symm
        _ = 0 := hphiOne
    have hcoeffCast : ((m + n : ℤ) : ℂ) = 0 :=
      (mul_eq_zero.mp hcoeffMul).resolve_right
        (hsub.degree_ne_zero eta heta)
    have hcoeff : m + n = 0 := by
      apply Int.cast_injective (α := ℂ)
      simpa only [Int.cast_zero] using hcoeffCast
    have hn : n = -m := by omega
    calc
      ClassFunction.inverseLinear (G := L) (k := ℂ) phi =
          ClassFunction.inverseLinear (G := L) (k := ℂ)
            (m • eta + n • eta') :=
        congrArg (ClassFunction.inverseLinear (G := L) (k := ℂ)) hmn.symm
      _ = m • eta' + n • eta := by
        rw [map_add, map_zsmul, map_zsmul]
        exact congrArg
          (fun x : ClassFunction L ℂ ↦ m • eta' + n • x)
          (inverseLinear_involutive eta)
      _ = -(m • eta + n • eta') := by
        rw [hn]
        module
      _ = -phi := congrArg Neg.neg hmn

/-- If a subcoherent family has at most two members, dualizing any coherence
witness gives another coherence witness.  This is source `dual_coherence`. -/
theorem dual_coherence
    {S : Set (ClassFunction L ℂ)}
    {tau nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    (hnu : coherent_with S (nonidentitySet L) tau nu)
    (hcard : S.ncard ≤ 2) :
    coherent_with S (nonidentitySet L) tau (dual_iso nu) := by
  refine
    { isometry := ?_
      mapsToVirtual := ?_
      agrees := ?_ }
  · intro phi hphi psi hpsi
    have hphiInv := inverseLinear_mem_closure hsub.inverse_mem hphi
    have hpsiInv := inverseLinear_mem_closure hsub.inverse_mem hpsi
    rw [dual_iso_apply, dual_iso_apply,
      characterPairing_neg_left, characterPairing_neg_right, neg_neg]
    exact (hnu.isometry _ hphiInv _ hpsiInv).trans
      (characterPairing_inverseLinear phi psi)
  · intro phi hphi
    have hphiInv := inverseLinear_mem_closure hsub.inverse_mem hphi
    obtain ⟨z, hz⟩ := hnu.mapsToVirtual _ hphiInv
    refine ⟨-z, ?_⟩
    rw [VirtualCharacter.realize_neg, hz, dual_iso_apply]
  · intro phi hphi hoff
    have hinv := inverseLinear_eq_neg_of_small_closed_family
      hsub hcard hphi hoff
    rw [dual_iso_apply, hinv, map_neg, neg_neg]
    exact hnu.agrees phi hphi hoff

private theorem inverseLinear_irreducible
    (chi : IrreducibleCharacter L ℂ) :
    ClassFunction.inverseLinear (G := L) (k := ℂ)
        (chi : ClassFunction L ℂ) =
      (IrreducibleCharacter.dual chi : ClassFunction L ℂ) := by
  ext x
  simp [IrreducibleCharacter.dual_apply]

/-- The two images of an irreducible character and its dual form an
orthonormal virtual-character pair, and their difference has degree zero.
This is the set-based form of source `coherent_seqInd_conjCirr`. -/
theorem coherent_seqInd_conjCirr
    {S : Set (ClassFunction L ℂ)}
    {tau nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    (hnu : coherent_with S (nonidentitySet L) tau nu)
    (chi : IrreducibleCharacter L ℂ)
    (hchi : (chi : ClassFunction L ℂ) ∈ S) :
    ClassFunction.IsVirtual (nu (chi : ClassFunction L ℂ)) ∧
      ClassFunction.IsVirtual
        (nu (IrreducibleCharacter.dual chi : ClassFunction L ℂ)) ∧
      characterPairing (nu (chi : ClassFunction L ℂ))
          (nu (chi : ClassFunction L ℂ)) = 1 ∧
      characterPairing
          (nu (IrreducibleCharacter.dual chi : ClassFunction L ℂ))
          (nu (IrreducibleCharacter.dual chi : ClassFunction L ℂ)) = 1 ∧
      characterPairing (nu (chi : ClassFunction L ℂ))
          (nu (IrreducibleCharacter.dual chi : ClassFunction L ℂ)) = 0 ∧
      (chi : ClassFunction L ℂ) -
          (IrreducibleCharacter.dual chi : ClassFunction L ℂ) ∈
        AddSubgroup.closure S ∧
      (chi : ClassFunction L ℂ) -
          (IrreducibleCharacter.dual chi : ClassFunction L ℂ) ∈
        ClassFunction.supportedOn (nonidentitySet L) ∧
      (nu (chi : ClassFunction L ℂ) -
          nu (IrreducibleCharacter.dual chi : ClassFunction L ℂ)) 1 = 0 := by
  let chiDual : IrreducibleCharacter L ℂ :=
    IrreducibleCharacter.dual chi
  let chi' : ClassFunction L ℂ :=
    (chiDual : ClassFunction L ℂ)
  have hinv : ClassFunction.inverseLinear (G := L) (k := ℂ)
      (chi : ClassFunction L ℂ) = chi' := by
    exact inverseLinear_irreducible chi
  have hchi'S : chi' ∈ S := by
    rw [← hinv]
    exact hsub.inverse_mem (chi : ClassFunction L ℂ) hchi
  have hchiSpan : (chi : ClassFunction L ℂ) ∈ AddSubgroup.closure S :=
    AddSubgroup.subset_closure hchi
  have hchi'Span : chi' ∈ AddSubgroup.closure S :=
    AddSubgroup.subset_closure hchi'S
  have hdiffSpan : (chi : ClassFunction L ℂ) - chi' ∈
      AddSubgroup.closure S :=
    (AddSubgroup.closure S).sub_mem hchiSpan hchi'Span
  have hdiffOff : (chi : ClassFunction L ℂ) - chi' ∈
      ClassFunction.supportedOn (nonidentitySet L) := by
    rw [← hinv]
    exact inverse_sub_supported (chi : ClassFunction L ℂ)
  have hchiNe : chi ≠ chiDual := by
    intro heq
    apply hsub.inverse_ne (chi : ClassFunction L ℂ) hchi
    rw [hinv, heq]
  have hvirtChi := hnu.mapsToVirtual _ hchiSpan
  have hvirtChi' := hnu.mapsToVirtual _ hchi'Span
  have hnormChi : characterPairing
      (nu (chi : ClassFunction L ℂ))
      (nu (chi : ClassFunction L ℂ)) = 1 := by
    rw [hnu.isometry _ hchiSpan _ hchiSpan,
      IrreducibleCharacter.characterPairing_self]
  have hnormChi' : characterPairing (nu chi') (nu chi') = 1 := by
    rw [hnu.isometry _ hchi'Span _ hchi'Span]
    exact IrreducibleCharacter.characterPairing_self
      chiDual
  have hortho : characterPairing
      (nu (chi : ClassFunction L ℂ)) (nu chi') = 0 := by
    rw [hnu.isometry _ hchiSpan _ hchi'Span]
    exact IrreducibleCharacter.characterPairing_eq_zero hchiNe
  have hdegreeZero :
      (nu (chi : ClassFunction L ℂ) - nu chi') 1 = 0 := by
    rw [← map_sub]
    rw [hnu.agrees _ hdiffSpan hdiffOff]
    exact ClassFunction.eq_zero_of_mem_supportedOn
      (hsub.tau_supported _ hdiffSpan hdiffOff) (by simp [nonidentitySet])
  exact ⟨hvirtChi, hvirtChi', hnormChi, hnormChi', hortho,
    hdiffSpan, hdiffOff, hdegreeZero⟩

/-- A pivot whose degree divides all degrees in the family extends the
partial isometry to a coherence isometry.  This is source
`pivot_coherence`. -/
theorem pivot_coherence
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    {eta1 : ClassFunction L ℂ} {zeta1 : ClassFunction G ℂ}
    (hsub : subcoherent S tau R) (heta1 : eta1 ∈ S)
    (hzeta1 : ClassFunction.IsVirtual zeta1)
    (hpivot : ∀ eta ∈ S, eta ≠ eta1 → ∃ a : ℕ,
      eta 1 = (a : ℂ) * eta1 1 ∧
      characterPairing (tau (eta - (a : ℂ) • eta1)) zeta1 =
        -(a : ℂ) * characterPairing eta1 eta1)
    (hnorm : characterPairing zeta1 zeta1 =
      characterPairing eta1 eta1) :
    coherent S (nonidentitySet L) tau := by
  let J := {eta : ClassFunction L ℂ // eta ∈ S}
  letI : Fintype J := hsub.finite.fintype
  let p : J := ⟨eta1, heta1⟩
  let a : J → ℕ := fun eta ↦
    if heta : eta.1 = eta1 then 1
    else Classical.choose (hpivot eta.1 eta.property heta)
  have haSpec (eta : J) (h : eta.1 ≠ eta1) :
      eta.1 1 = (a eta : ℂ) * eta1 1 ∧
      characterPairing
          (tau (eta.1 - (a eta : ℂ) • eta1)) zeta1 =
        -(a eta : ℂ) * characterPairing eta1 eta1 := by
    simpa [a, h] using
      (Classical.choose_spec (hpivot eta.1 eta.property h))
  have haDegree (eta : J) :
      eta.1 1 = (a eta : ℂ) * eta1 1 := by
    by_cases h : eta.1 = eta1
    · have ha : a eta = 1 := by simp [a, h]
      rw [h, ha, Nat.cast_one, one_mul]
    · exact (haSpec eta h).1
  let d : J → ClassFunction L ℂ := fun eta ↦
    eta.1 - (a eta : ℂ) • eta1
  let t : J → ClassFunction G ℂ := fun eta ↦
    tau (d eta) + (a eta : ℂ) • zeta1
  have haCross (eta : J) (h : eta.1 ≠ eta1) :
      characterPairing (tau (d eta)) zeta1 =
        -(a eta : ℂ) * characterPairing eta1 eta1 := by
    simpa [d] using (haSpec eta h).2
  have hdSpan (eta : J) : d eta ∈ AddSubgroup.closure S := by
    apply (AddSubgroup.closure S).sub_mem
      (AddSubgroup.subset_closure eta.property)
    rw [Nat.cast_smul_eq_nsmul]
    exact (AddSubgroup.closure S).nsmul_mem
      (AddSubgroup.subset_closure heta1) _
  have hdOff (eta : J) :
      d eta ∈ ClassFunction.supportedOn (nonidentitySet L) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxone : x = 1 := by
      simpa [nonidentitySet] using not_not.mp hx
    subst x
    simp only [d, ClassFunction.sub_apply, ClassFunction.smul_apply,
      smul_eq_mul]
    rw [haDegree eta, sub_self]
  have htp : t p = zeta1 := by
    simp [t, d, p, a]
  have htVirtual (eta : J) : ClassFunction.IsVirtual (t eta) := by
    by_cases h : eta.1 = eta1
    · have : eta = p := Subtype.ext h
      subst eta
      rw [htp]
      exact hzeta1
    · simpa only [t] using
        (hsub.tau_virtual (d eta) (hdSpan eta) (hdOff eta)).add
          (hzeta1.natCast_smul (a eta))
  have hsourceNorm (eta : J) :
      characterPairing eta.1 eta.1 ≠ 0 := by
    obtain ⟨z, hz⟩ := hsub.source_virtual eta.1 eta.property
    intro hzero
    have hcast : ((normSq z : ℤ) : ℂ) = 0 := by
      calc
        ((normSq z : ℤ) : ℂ) =
            characterPairing (VirtualCharacter.realize z)
              (VirtualCharacter.realize z) := by
          simpa only [normSq] using
            (VirtualCharacter.characterPairing_realize z z).symm
        _ = characterPairing eta.1 eta.1 := by rw [hz]
        _ = 0 := hzero
    have hz0 : z = 0 :=
      (normSq_eq_zero_iff z).mp (by
        apply Int.cast_injective (α := ℂ)
        simpa only [Int.cast_zero] using hcast)
    have heta0 : eta.1 = 0 := by
      calc
        eta.1 = VirtualCharacter.realize z := hz.symm
        _ = 0 := by simp [hz0]
    exact hsub.zero_not_mem (by simpa [heta0] using eta.property)
  have htPair (eta theta : J) :
      characterPairing (t eta) (t theta) =
        characterPairing eta.1 theta.1 := by
    by_cases heta : eta.1 = eta1
    · have hetaP : eta = p := Subtype.ext heta
      subst eta
      rw [htp]
      by_cases htheta : theta.1 = eta1
      · have hthetaP : theta = p := Subtype.ext htheta
        subst theta
        rw [htp]
        exact hnorm
      · have horth : characterPairing eta1 theta.1 = 0 :=
          hsub.pairwise_orthogonal heta1 theta.property (Ne.symm htheta)
        have hcross :
            characterPairing zeta1 (tau (d theta)) =
              -(a theta : ℂ) * characterPairing eta1 eta1 := by
          rw [characterPairing_comm]
          exact haCross theta htheta
        simp only [t, characterPairing_add_right,
          characterPairing_smul_right]
        rw [hcross, hnorm, horth]
        ring
    · by_cases htheta : theta.1 = eta1
      · have hthetaP : theta = p := Subtype.ext htheta
        subst theta
        rw [htp]
        have horth : characterPairing eta.1 eta1 = 0 :=
          hsub.pairwise_orthogonal eta.property heta1 heta
        simp only [t, characterPairing_add_left,
          characterPairing_smul_left]
        rw [haCross eta heta, hnorm, horth]
        ring
      · have hetaOne : characterPairing eta.1 eta1 = 0 :=
          hsub.pairwise_orthogonal eta.property heta1 heta
        have honeTheta : characterPairing eta1 theta.1 = 0 :=
          hsub.pairwise_orthogonal heta1 theta.property (Ne.symm htheta)
        have hmap := hsub.tau_isometry
          (d eta) (hdSpan eta) (hdOff eta)
          (d theta) (hdSpan theta) (hdOff theta)
        have hthetaCross :
            characterPairing zeta1 (tau (d theta)) =
              -(a theta : ℂ) * characterPairing eta1 eta1 := by
          rw [characterPairing_comm]
          exact haCross theta htheta
        have hdPair :
            characterPairing (d eta) (d theta) =
              characterPairing eta.1 theta.1 +
                (a eta : ℂ) * (a theta : ℂ) *
                  characterPairing eta1 eta1 := by
          simp only [d, characterPairing_sub_left,
            characterPairing_sub_right, characterPairing_smul_left,
            characterPairing_smul_right, hetaOne, honeTheta,
            mul_zero, sub_zero, zero_mul]
          ring
        simp only [t, characterPairing_add_left,
          characterPairing_add_right, characterPairing_smul_left,
          characterPairing_smul_right]
        rw [hmap, haCross eta heta, hthetaCross, hnorm, hdPair]
        ring
  let nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ :=
    { toFun := fun phi ↦ ∑ eta : J,
        (characterPairing eta.1 phi /
          characterPairing eta.1 eta.1) • t eta
      map_add' := by
        intro phi psi
        simp only [characterPairing_add_right, add_div, add_smul,
          Finset.sum_add_distrib]
      map_smul' := by
        intro c phi
        simp only [characterPairing_smul_right, smul_smul,
          Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro eta _
        congr 1
        simp only [RingHom.id_apply]
        ring }
  have hnuGenerator (eta : J) : nu eta.1 = t eta := by
    change (∑ theta : J,
      (characterPairing theta.1 eta.1 /
        characterPairing theta.1 theta.1) • t theta) = t eta
    rw [Finset.sum_eq_single eta]
    · rw [div_self (hsourceNorm eta), one_smul]
    · intro theta _ htheta
      have hne : theta.1 ≠ eta.1 := by
        intro h
        exact htheta (Subtype.ext h)
      rw [hsub.pairwise_orthogonal theta.property eta.property hne]
      simp
    · simp
  have hnuVirtual : ∀ phi ∈ AddSubgroup.closure S,
      ClassFunction.IsVirtual (nu phi) := by
    intro phi hphi
    induction hphi using AddSubgroup.closure_induction with
    | mem phi hphi =>
        let eta : J := ⟨phi, hphi⟩
        change ClassFunction.IsVirtual (nu eta.1)
        rw [hnuGenerator eta]
        exact htVirtual eta
    | zero =>
        simpa only [map_zero] using
          (ClassFunction.IsVirtual.zero :
            ClassFunction.IsVirtual (0 : ClassFunction G ℂ))
    | add phi psi hphi hpsi ihphi ihpsi =>
        simpa only [map_add] using ihphi.add ihpsi
    | neg phi hphi ihphi =>
        simpa only [map_neg] using ihphi.neg
  have hnuIsometry : ∀ phi ∈ AddSubgroup.closure S,
      ∀ psi ∈ AddSubgroup.closure S,
        characterPairing (nu phi) (nu psi) =
          characterPairing phi psi := by
    intro phi hphi psi hpsi
    induction hphi, hpsi using AddSubgroup.closure_induction₂ with
    | mem phi psi hphi hpsi =>
        let eta : J := ⟨phi, hphi⟩
        let theta : J := ⟨psi, hpsi⟩
        rw [hnuGenerator eta, hnuGenerator theta]
        exact htPair eta theta
    | zero_left => simp
    | zero_right => simp
    | add_left phi psi theta hphi hpsi htheta ihphi ihpsi =>
        simp only [map_add, characterPairing_add_left, ihphi, ihpsi]
    | add_right phi psi theta hphi hpsi htheta ihphi ihpsi =>
        simp only [map_add, characterPairing_add_right, ihphi, ihpsi]
    | neg_left phi psi hphi hpsi ih =>
        simp only [map_neg, characterPairing_neg_left, ih]
    | neg_right phi psi hphi hpsi ih =>
        simp only [map_neg, characterPairing_neg_right, ih]
  have hdefect : ∀ phi ∈ AddSubgroup.closure S,
      nu phi - tau phi =
        (phi 1 / eta1 1) • (zeta1 - tau eta1) := by
    intro phi hphi
    induction hphi using AddSubgroup.closure_induction with
    | mem phi hphi =>
        let eta : J := ⟨phi, hphi⟩
        have hratio : eta.1 1 / eta1 1 = (a eta : ℂ) := by
          rw [haDegree eta,
            mul_div_cancel_right₀ _ (hsub.degree_ne_zero eta1 heta1)]
        change nu eta.1 - tau eta.1 =
          (eta.1 1 / eta1 1) • (zeta1 - tau eta1)
        rw [hnuGenerator eta, hratio]
        apply ClassFunction.ext
        intro x
        simp only [t, d, map_sub, map_smul,
          ClassFunction.add_apply, ClassFunction.sub_apply,
          ClassFunction.smul_apply, smul_eq_mul]
        ring
    | zero => simp
    | add phi psi hphi hpsi ihphi ihpsi =>
        simp only [map_add, ClassFunction.add_apply, add_div, add_smul]
        rw [← ihphi, ← ihpsi]
        abel
    | neg phi hphi ihphi =>
        calc
          nu (-phi) - tau (-phi) = -(nu phi - tau phi) := by
            simp only [map_neg]
            abel
          _ = -((phi 1 / eta1 1) • (zeta1 - tau eta1)) :=
            congrArg Neg.neg ihphi
          _ = ((-phi) 1 / eta1 1) • (zeta1 - tau eta1) := by
            rw [ClassFunction.neg_apply, neg_div]
            exact (neg_smul _ _).symm
  refine ⟨nu, {
    isometry := hnuIsometry
    mapsToVirtual := hnuVirtual
    agrees := ?_ }⟩
  intro phi hphi hoff
  have hphi1 : phi 1 = 0 :=
    ClassFunction.eq_zero_of_mem_supportedOn hoff
      (by simp [nonidentitySet])
  have h := hdefect phi hphi
  rw [hphi1, zero_div, zero_smul] at h
  exact sub_eq_zero.mp h

end

end Submission.OddOrder.PF
