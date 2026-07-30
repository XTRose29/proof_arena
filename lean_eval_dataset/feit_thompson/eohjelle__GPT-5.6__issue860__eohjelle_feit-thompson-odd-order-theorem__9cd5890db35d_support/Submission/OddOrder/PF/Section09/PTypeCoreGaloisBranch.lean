import Submission.OddOrder.PF.Section09.PTypeCoreContext
import Submission.OddOrder.PF.Section09.PTypeGaloisConclusion

/-!
# Peterfalvi Section 9: the Galois core branch

This module closes the Galois branch of Peterfalvi (9.11).  It also records
the small, representation-independent extension and remainder lemmas shared
by the non-Galois progress step and the final finite closure.

The common lemmas are deliberately stated directly in terms of filters and
linear combinations.  The canonical remainder, degree slice, and Boolean
decomposition are introduced in independent downstream modules, whose callers
can specialize these statements by simplification.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical IsMulCommutative Pointwise

universe u

local instance (priority := 10) pTypeCoreGaloisBranchFintypeOfFinite
    (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace PTypeCoreGaloisBranchInternal

open PTypeCoreContextInternal

private theorem coreFamily_cfConjC_closed
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    cfConjC_closed
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ)) := by
  intro phi hphi
  unfold pTypeCoreFamilyOfContext at hphi ⊢
  exact seqInd_inverse_mem (k := ℂ)
    (pTypeCoreDerived M) (pTypeCoreFitting M)
    (pTypeCoreKernelDerivedComplement ctx) hphi

/-! ## The Galois branch -/

/-- Every member of the canonical core family has the degree prescribed by
the Galois core-character conclusion. -/
private theorem coreFamily_uniform_degree_of_core_induced
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (HC : Subgroup (pTypeCoreDerived M))
    (actionCard : ℕ)
    (hcore : ∀ s ∈ Iirr_kerD (k := ℂ) (pTypeCoreFitting M)
      (pTypeCoreKernelDerivedComplement ctx),
      PTypeCoreInduced HC actionCard s) :
    ∀ chi ∈ pTypeCoreFamilyOfContext ctx,
      chi 1 =
        (((Ptype_factor_action ctx facts).q * actionCard : ℕ) : ℂ) := by
  intro chi hchi
  have hchiRaw : chi ∈ seqIndD (k := ℂ)
      (pTypeCoreDerived M) (pTypeCoreFitting M)
      (pTypeCoreKernelDerivedComplement ctx) := by
    convert hchi using 1
    unfold pTypeCoreFamilyOfContext
    congr 1 <;> apply Subsingleton.elim
  obtain ⟨s, hs, rfl⟩ := seqIndP.mp hchiRaw
  calc
    ClassFunction.induce (pTypeCoreDerived M)
        (s : ClassFunction (pTypeCoreDerived M) ℂ) 1 =
        ((pTypeCoreDerived M).index : ℂ) * s 1 :=
      ClassFunction.induce_one (pTypeCoreDerived M) _
    _ = ((Ptype_factor_action ctx facts).q : ℂ) *
        (actionCard : ℂ) := by
      rw [pTypeCore_index_eq_q ctx facts, (hcore s hs).1]
    _ =
        (((Ptype_factor_action ctx facts).q * actionCard : ℕ) : ℂ) := by
      norm_num

set_option maxHeartbeats 800000 in
/-- The complete Galois branch of Peterfalvi (9.11) for the canonical Type-P
context.  This is the only branch result consumed by the final closure. -/
theorem pTypeCore_galois_branch
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (hmaxM : M ∈ minSimple_max_groups (G := G))
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype5 : FTtype M ≠ 5)
    (hGal :
      typeP_Galois
        (Ptype_factor_action
          (Ptype_Fcore_context hmaxM defW MtypeP notMtype5)
          (Ptype_Fcore_factor_facts
            (Ptype_Fcore_context hmaxM defW MtypeP notMtype5)))) :
    let ctx := Ptype_Fcore_context hmaxM defW MtypeP notMtype5
    coherent
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ))
      (nonidentitySet M)
      (Dade (FT_Dade0_hyp M hmaxM)) := by
  classical
  let ctx := Ptype_Fcore_context hmaxM defW MtypeP notMtype5
  let facts := Ptype_Fcore_factor_facts ctx
  let D := Ptype_factor_action ctx facts
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  let actionCard := pTypeActionFactorCard D
  let pd := FT_prDade_hyp defW hmaxM MtypeP
  let isoM :=
    pd.prDade_prTI.prime_cycTIhyp.cyclicTIIsometryData (k := ℂ)
  let isoG := pd.prDade_cycTI.cyclicTIIsometryData (k := ℂ)
  let R := FTtypeP_coh_base pd isoM isoG (mFT_odd M)
  have hfamilySub :
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ)) ⊆
        FTtypePKernelLayer pd := by
    simpa [FTtypePKernelLayer,
      PrimeDadeHypothesis.signalizerInKernel] using
      (pTypeCoreFamily_sub_kernelLayer
        hmaxM defW MtypeP notMtype5)
  have hfamilyClosed : cfConjC_closed
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ)) :=
    coreFamily_cfConjC_closed ctx
  have hsub : subcoherent
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ))
      (Dade pd.prDade_hyp) R := by
    exact subset_subcoherent
      (FTtypeP_subcoherent pd isoM isoG (mFT_odd M))
      ⟨hfamilySub, hfamilyClosed⟩
  have hchars := typeP_Galois_characters M U W W₁ W₂
    defW hmaxM MtypeP notMtype5 hGal
  have hcore : ∀ s ∈ Iirr_kerD (k := ℂ) (pTypeCoreFitting M)
      (pTypeCoreKernelDerivedComplement ctx),
      PTypeCoreInduced HC actionCard s := by
    convert hchars.1.2 using 1 <;> first | rfl | apply Subsingleton.elim
  have hdegree := coreFamily_uniform_degree_of_core_induced
    ctx facts HC actionCard hcore
  apply uniform_degree_coherence hsub
  intro chi hchi psi hpsi
  exact (hdegree chi hchi).trans (hdegree psi hpsi).symm

/-! ## Common extension input -/

/-- The exact data needed to adjoin a character and its contragredient by
Peterfalvi's coherence-extension theorem. -/
structure PTypeCoreExtensionInput
    {M Q : Type u}
    [Group M] [Fintype M] [Group Q] [Fintype Q]
    (S₀ S₂ : Finset (ClassFunction M ℂ))
    (tau tau₂ : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ) where
  chi : ClassFunction M ℂ
  phi : ClassFunction M ℂ
  scale : ℕ
  target : ClassFunction Q ℂ
  phi_mem : phi ∈ S₂
  chi_mem : chi ∈ S₀
  chi_not_mem : chi ∉ S₂
  degree_balance : chi 1 = (scale : ℂ) * phi 1
  target_orthogonal :
    characterPairing target ((scale : ℂ) • tau₂ phi) = 0
  mapped_balance :
    tau (chi - (scale : ℂ) • phi) =
      target - (scale : ℂ) • tau₂ phi

private theorem bool_eq_false_of_mod_eq_zero
    (b : Bool) (m : ℕ) (hm : 1 < m)
    (hb : b.toNat % m = 0) : b = false := by
  cases b with
  | false => rfl
  | true =>
      simp only [Bool.toNat_true] at hb
      have : 1 % m = 1 := Nat.mod_eq_of_lt hm
      omega

/-- Eliminate the Boolean tail of the final orthogonal decomposition and
package the remaining mapped equality as extension input. -/
def PTypeCoreExtensionInput.of_bool_decomposition
    {M Q : Type u}
    [Group M] [Fintype M] [Group Q] [Fintype Q]
    (S₀ S₂ : Finset (ClassFunction M ℂ))
    (tau tau₂ : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ)
    (chi phi : ClassFunction M ℂ) (scale : ℕ)
    (target tail : ClassFunction Q ℂ) (b : Bool)
    (hphi : phi ∈ S₂) (hchi : chi ∈ S₀) (hchiNot : chi ∉ S₂)
    (hdegree : chi 1 = (scale : ℂ) * phi 1)
    (htarget :
      characterPairing target ((scale : ℂ) • tau₂ phi) = 0)
    (hscale : 1 < scale) (hb : b.toNat % scale = 0)
    (hmapped :
      tau (chi - (scale : ℂ) • phi) =
        target - (scale : ℂ) • tau₂ phi +
          (b.toNat : ℂ) • tail) :
    PTypeCoreExtensionInput S₀ S₂ tau tau₂ := by
  have hbfalse := bool_eq_false_of_mod_eq_zero b scale hscale hb
  subst b
  refine
    { chi := chi
      phi := phi
      scale := scale
      target := target
      phi_mem := hphi
      chi_mem := hchi
      chi_not_mem := hchiNot
      degree_balance := hdegree
      target_orthogonal := htarget
      mapped_balance := ?_ }
  simpa using hmapped

/-- Convert a packaged extension input into the coherent enlarged family. -/
theorem pTypeCore_coherent_insert_of_extensionInput
    {M Q : Type u}
    [Group M] [Fintype M] [Group Q] [Fintype Q]
    (S₀ S₂ : Finset (ClassFunction M ℂ))
    (tau tau₂ : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ)
    (R : ClassFunction M ℂ → Finset (ClassFunction Q ℂ))
    (hsub : subcoherent (↑S₀ : Set (ClassFunction M ℂ)) tau R)
    (hS₂ : cfConjC_subset
      (↑S₂ : Set (ClassFunction M ℂ))
      (↑S₀ : Set (ClassFunction M ℂ)))
    (hcohWith₂ : coherent_with
      (↑S₂ : Set (ClassFunction M ℂ))
      (nonidentitySet M) tau tau₂)
    (e : PTypeCoreExtensionInput S₀ S₂ tau tau₂) :
    coherent
      ({e.chi, ClassFunction.inverseLinear e.chi} ∪
        (↑S₂ : Set (ClassFunction M ℂ)))
      (nonidentitySet M) tau :=
  extend_coherent_with hsub hS₂ hcohWith₂
    e.phi_mem e.chi_mem e.chi_not_mem e.scale e.target
    e.degree_balance e.target_orthogonal e.mapped_balance

/-! ## Representation-independent remainder lemmas -/

/-- Adjoining an element outside the current family strictly decreases the
filtered remainder. -/
theorem pTypeCore_remainder_insert_pair_lt
    {M : Type u} [Group M] [Fintype M]
    (S₀ S₂ : Finset (ClassFunction M ℂ))
    (chi eta : ClassFunction M ℂ)
    (hchi₀ : chi ∈ S₀) (hchi₂ : chi ∉ S₂) :
    (S₀.filter fun z ↦ z ∉ insert chi (insert eta S₂)).card <
      (S₀.filter fun z ↦ z ∉ S₂).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hz₀, hznot⟩
    exact Finset.mem_filter.mpr ⟨hz₀, fun hz₂ ↦ hznot (by simp [hz₂])⟩
  · intro heq
    have hchiR : chi ∈ S₀.filter fun z ↦ z ∉ S₂ :=
      Finset.mem_filter.mpr ⟨hchi₀, hchi₂⟩
    have hchiNext :
        chi ∈ S₀.filter fun z ↦ z ∉ insert chi (insert eta S₂) := by
      rw [heq]
      exact hchiR
    exact (Finset.mem_filter.mp hchiNext).2 (by simp)

/-- The filtered complement of a contragredient-closed subfamily inside a
contragredient-closed ambient family is again a closed subfamily. -/
theorem pTypeCore_remainder_cfConjC_subset
    {M : Type u} [Group M] [Fintype M]
    (S₀ S₂ : Finset (ClassFunction M ℂ))
    (hS₀closed : cfConjC_closed
      (↑S₀ : Set (ClassFunction M ℂ)))
    (hS₂closed : cfConjC_closed
      (↑S₂ : Set (ClassFunction M ℂ))) :
    cfConjC_subset
      (↑(S₀.filter fun z ↦ z ∉ S₂) : Set (ClassFunction M ℂ))
      (↑S₀ : Set (ClassFunction M ℂ)) := by
  constructor
  · intro phi hphi
    exact (Finset.mem_filter.mp hphi).1
  · intro phi hphi
    rcases Finset.mem_filter.mp hphi with ⟨hphi₀, hphiNot⟩
    apply Finset.mem_filter.mpr
    refine ⟨hS₀closed phi hphi₀, ?_⟩
    intro hinv₂
    apply hphiNot
    have hinvInv :
        ClassFunction.inverseLinear (ClassFunction.inverseLinear phi) =
          phi := by
      ext x
      simp
    rw [← hinvInv]
    exact hS₂closed (ClassFunction.inverseLinear phi) hinv₂

/-! ## Generic degree and early-extension adapters -/

/-- A fixed divisor of the core irreducible degrees makes every member of
the full induced family a natural degree multiple of a prescribed
`q * divisor` character. -/
theorem pTypeCore_degree_multiple_of_slice
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (divisor : ℕ)
    (hfixed : ∀ s ∈ Iirr_kerD (k := ℂ)
      (pTypeCoreFitting M) (pTypeCoreKernel ctx),
      divisor ∣ pTypeIrreducibleDegree s)
    {chi psi : ClassFunction M ℂ}
    (hchi : chi ∈ pTypeCoreFamilyOfContext ctx)
    (hpsiDegree :
      psi 1 =
        (((Ptype_factor_action ctx facts).q * divisor : ℕ) : ℂ)) :
    ∃ n : ℕ, chi 1 = (n : ℂ) * psi 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let D := Ptype_factor_action ctx facts
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀ := pTypeCoreKernel ctx
  let H₀CPrime := pTypeCoreKernelDerivedComplement ctx
  have hchiInduced : chi ∈ seqIndD (k := ℂ) HU H H₀CPrime := by
    simpa only [pTypeCoreFamilyOfContext] using hchi
  obtain ⟨s, hs, rfl⟩ := seqIndP.mp hchiInduced
  have hH₀Prime : H₀ ≤ H₀CPrime := by
    dsimp [H₀, H₀CPrime, pTypeCoreKernelDerivedComplement,
      pTypeH0CPrimeInDerived]
    exact le_sup_left
  have hs₀ : s ∈ Iirr_kerD (k := ℂ) H H₀ :=
    Iirr_kerDS (k := ℂ)
      (A₁ := H₀CPrime) (A₂ := H₀)
      (B₁ := H) (B₂ := H) hH₀Prime le_rfl hs
  obtain ⟨n, hn⟩ := hfixed s hs₀
  change Module.finrank ℂ s.representation = divisor * n at hn
  refine ⟨n, ?_⟩
  calc
    ClassFunction.induce HU (s : ClassFunction HU ℂ) 1 =
        (HU.index : ℂ) * s 1 := ClassFunction.induce_one HU _
    _ = (D.q : ℂ) *
        (Module.finrank ℂ s.representation : ℂ) := by
      rw [pTypeCore_index_eq_q ctx facts,
        IrreducibleCharacter.apply_one_eq_finrank]
    _ = (n : ℂ) * (((D.q * divisor : ℕ) : ℂ)) := by
      rw [hn]
      push_cast
      ring
    _ = (n : ℂ) * psi 1 := by rw [hpsiDegree]

/-- The short arm of Peterfalvi (9.11.1), stated independently of the
particular definition of the lower degree slice. -/
theorem pTypeCore_extend_early
    {M Q : Type u}
    [Group M] [Fintype M] [Group Q] [Fintype Q]
    {S₀ S₂ : Finset (ClassFunction M ℂ)}
    {tau : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ}
    {R : ClassFunction M ℂ → Finset (ClassFunction Q ℂ)}
    (hsub : subcoherent (↑S₀ : Set (ClassFunction M ℂ)) tau R)
    (hS₂ : cfConjC_subset
      (↑S₂ : Set (ClassFunction M ℂ))
      (↑S₀ : Set (ClassFunction M ℂ)))
    (hcoh₂ : coherent (↑S₂ : Set (ClassFunction M ℂ))
      (nonidentitySet M) tau)
    {chi phi : ClassFunction M ℂ}
    (hphi : phi ∈ S₂) (hchi : chi ∈ S₀) (hchiNot : chi ∉ S₂)
    (hdiv : ∃ n : ℕ, chi 1 = (n : ℂ) * phi 1)
    (hstrict :
      2 * (chi 1).re * (phi 1).re <
        coherenceDegreeSum (↑S₂ : Set (ClassFunction M ℂ))
          (hsub.finite.subset hS₂.1)) :
    coherent
      ({chi, ClassFunction.inverseLinear chi} ∪
        (↑S₂ : Set (ClassFunction M ℂ)))
      (nonidentitySet M) tau :=
  extend_coherent hsub hS₂ hphi hchi hchiNot hcoh₂ hdiv hstrict

end PTypeCoreGaloisBranchInternal

end

end Submission.OddOrder.PF
