import Submission.OddOrder.PF.Section09.PTypeCoreGaloisBranch
import Submission.OddOrder.PF.Section09.PTypeCoreNonGaloisExtension

/-!
# Peterfalvi Section 9: finite closure of the Type-P core

The preceding modules prove both possible progress steps for a coherent
subfamily of the canonical Type-P core.  Here we iterate those steps over the
finite remainder.  The initial subfamily is the common-degree slice supplied
by the non-Galois index; each iteration adjoins a character together with its
contragredient.  The remainder cardinal strictly decreases, so the iteration
terminates at the full core family.

The only public declaration in this assembly module is Peterfalvi (9.11).
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open PTypeCoreContextInternal
open PTypeCoreGaloisBranchInternal
open PTypeCoreNonGaloisExtensionInternal
open scoped BigOperators Classical IsMulCommutative Pointwise

universe u

local instance (priority := 10) pTypeCoreClosureFintypeOfFinite
    (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace PTypeCoreClosureInternal

/-! ## The initial equal-degree family -/

private theorem coreFamily_closed
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

private theorem degreeSlice_subfamily
    {M Q : Type u}
    [Group M] [Fintype M] [Group Q] [Fintype Q]
    (S : Finset (ClassFunction M ℂ)) (degree : ℕ)
    (tau : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ)
    (R : ClassFunction M ℂ → Finset (ClassFunction Q ℂ))
    (hsub : subcoherent (↑S : Set (ClassFunction M ℂ)) tau R) :
    cfConjC_subset
      (↑(pTypeCoreDegreeSlice S degree) : Set (ClassFunction M ℂ))
      (↑S : Set (ClassFunction M ℂ)) := by
  constructor
  · intro chi hchi
    exact (Finset.mem_filter.mp hchi).1
  · intro chi hchi
    rcases Finset.mem_filter.mp hchi with ⟨hchiS, hdegree⟩
    have hinvS : ClassFunction.inverseLinear chi ∈ S :=
      hsub.inverse_mem chi hchiS
    obtain ⟨n, hn⟩ :=
      (hsub.source_character chi hchiS).exists_nat_degree
    have hrealDegree : star (chi 1) = chi 1 := by
      rw [hn]
      simp
    apply Finset.mem_filter.mpr
    refine ⟨hinvS, ?_⟩
    simpa only [ClassFunction.inverseLinear_apply, inv_one, hrealDegree]
      using hdegree

private theorem degreeSlice_coherent
    {M Q : Type u}
    [Group M] [Fintype M] [Group Q] [Fintype Q]
    (S : Finset (ClassFunction M ℂ)) (degree : ℕ)
    (tau : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ)
    (R : ClassFunction M ℂ → Finset (ClassFunction Q ℂ))
    (hsub : subcoherent (↑S : Set (ClassFunction M ℂ)) tau R) :
    coherent
      (↑(pTypeCoreDegreeSlice S degree) : Set (ClassFunction M ℂ))
      (nonidentitySet M) tau := by
  apply uniform_degree_coherence
    (subset_subcoherent hsub
      (degreeSlice_subfamily S degree tau R hsub))
  intro chi hchi psi hpsi
  exact (Finset.mem_filter.mp hchi).2.trans
    (Finset.mem_filter.mp hpsi).2.symm

/-! ## Finite dual-extension closure -/

/-- Close a finite ambient family from a coherent dual-closed base, provided
every proper intermediate dual-closed family admits a coherent dual-pair
extension.  Termination is measured by the ambient filtered remainder. -/
private theorem closeByDualExtensions
    {M Q : Type u}
    [Group M] [Fintype M] [Group Q] [Fintype Q]
    (ambient base : Finset (ClassFunction M ℂ))
    (tau : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ)
    (R : ClassFunction M ℂ → Finset (ClassFunction Q ℂ))
    (hsub : subcoherent (↑ambient : Set (ClassFunction M ℂ)) tau R)
    (step :
      ∀ current : Finset (ClassFunction M ℂ),
        (↑base : Set (ClassFunction M ℂ)) ⊆
          (↑current : Set (ClassFunction M ℂ)) →
        cfConjC_subset
          (↑current : Set (ClassFunction M ℂ))
          (↑ambient : Set (ClassFunction M ℂ)) →
        ∀ nu : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ,
          coherent_with
            (↑current : Set (ClassFunction M ℂ))
            (nonidentitySet M) tau nu →
          (∃ chi ∈ ambient, chi ∉ current) →
          ∃ chi : ClassFunction M ℂ,
            chi ∈ ambient ∧ chi ∉ current ∧
              coherent
                ({chi, ClassFunction.inverseLinear chi} ∪
                  (↑current : Set (ClassFunction M ℂ)))
                (nonidentitySet M) tau)
    (current : Finset (ClassFunction M ℂ))
    (hbase : (↑base : Set (ClassFunction M ℂ)) ⊆
      (↑current : Set (ClassFunction M ℂ)))
    (hcurrent : cfConjC_subset
      (↑current : Set (ClassFunction M ℂ))
      (↑ambient : Set (ClassFunction M ℂ)))
    (hcoherent : coherent
      (↑current : Set (ClassFunction M ℂ))
      (nonidentitySet M) tau) :
    coherent (↑ambient : Set (ClassFunction M ℂ))
      (nonidentitySet M) tau := by
  classical
  by_cases hcovered :
      (↑ambient : Set (ClassFunction M ℂ)) ⊆
        (↑current : Set (ClassFunction M ℂ))
  · exact subset_coherent hcovered hcoherent
  · obtain ⟨missing, hmissingAmbient, hmissingCurrent⟩ :=
      Set.not_subset.mp hcovered
    obtain ⟨nu, hnu⟩ := hcoherent
    obtain ⟨chi, hchiAmbient, hchiCurrent, hnextCoherent⟩ :=
      step current hbase hcurrent nu hnu
        ⟨missing, hmissingAmbient, hmissingCurrent⟩
    let next : Finset (ClassFunction M ℂ) :=
      insert chi (insert (ClassFunction.inverseLinear chi) current)
    have hnextSet :
        (↑next : Set (ClassFunction M ℂ)) =
          {chi, ClassFunction.inverseLinear chi} ∪
            (↑current : Set (ClassFunction M ℂ)) := by
      ext z
      change z ∈ next ↔
        (z = chi ∨ z = ClassFunction.inverseLinear chi) ∨ z ∈ current
      simp [next, eq_comm]
      tauto
    have hnextCoherent' :
        coherent (↑next : Set (ClassFunction M ℂ))
          (nonidentitySet M) tau := by
      rw [hnextSet]
      exact hnextCoherent
    have hnextSubset :
        (↑next : Set (ClassFunction M ℂ)) ⊆
          (↑ambient : Set (ClassFunction M ℂ)) := by
      intro z hz
      change z ∈ next at hz
      simp only [next, Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact hchiAmbient
      rcases hz with rfl | hz
      · exact hsub.inverse_mem chi hchiAmbient
      · exact hcurrent.1 hz
    have hnextClosed :
        cfConjC_closed (↑next : Set (ClassFunction M ℂ)) := by
      intro z hz
      change z ∈ next at hz
      change ClassFunction.inverseLinear z ∈ next
      simp only [next, Finset.mem_insert] at hz ⊢
      rcases hz with rfl | hz
      · exact Or.inr (Or.inl rfl)
      rcases hz with rfl | hz
      · left
        ext x
        simp
      · exact Or.inr (Or.inr (hcurrent.2 z hz))
    have hbaseNext :
        (↑base : Set (ClassFunction M ℂ)) ⊆
          (↑next : Set (ClassFunction M ℂ)) := by
      intro z hz
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (hbase hz))
    exact closeByDualExtensions ambient base tau R hsub step next
      hbaseNext ⟨hnextSubset, hnextClosed⟩ hnextCoherent'
termination_by (pTypeCoreRemainder ambient current).card
decreasing_by
  simpa only [next, pTypeCoreRemainder] using
    pTypeCore_remainder_insert_pair_lt ambient current chi
      (ClassFunction.inverseLinear chi) hchiAmbient hchiCurrent

end PTypeCoreClosureInternal

open PTypeCoreClosureInternal

/-! ## Peterfalvi (9.11) -/

/-- Peterfalvi (9.11): the canonical Type-P core family is coherent for the
Section 8 Dade isometry. -/
theorem Ptype_core_coherence
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (hmaxM : M ∈ minSimple_max_groups (G := G))
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype5 : FTtype M ≠ 5) :
    let ctx := Ptype_Fcore_context hmaxM defW MtypeP notMtype5
    coherent
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ))
      (nonidentitySet M)
      (Dade (FT_Dade0_hyp M hmaxM)) := by
  classical
  let ctx := Ptype_Fcore_context hmaxM defW MtypeP notMtype5
  let facts := Ptype_Fcore_factor_facts ctx
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
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
  have hsub : subcoherent
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ))
      (Dade (FT_Dade0_hyp M hmaxM)) R := by
    exact subset_subcoherent
      (FTtypeP_subcoherent pd isoM isoG (mFT_odd M))
      ⟨hfamilySub, coreFamily_closed ctx⟩
  by_cases hGal : typeP_Galois D
  · exact pTypeCore_galois_branch
      hmaxM defW MtypeP notMtype5 hGal
  · let index := pTypeNonGaloisIndex hD hGal
    let ambient := pTypeCoreFamilyOfContext ctx
    let base := pTypeCoreDegreeSlice ambient (D.q * index)
    exact closeByDualExtensions ambient base
      (Dade (FT_Dade0_hyp M hmaxM)) R hsub
      (pTypeCore_nonGalois_extension_step
        ctx facts hGal R hsub) base
      Set.Subset.rfl
      (degreeSlice_subfamily ambient _ _ R hsub)
      (degreeSlice_coherent ambient _ _ R hsub)

end

end Submission.OddOrder.PF
