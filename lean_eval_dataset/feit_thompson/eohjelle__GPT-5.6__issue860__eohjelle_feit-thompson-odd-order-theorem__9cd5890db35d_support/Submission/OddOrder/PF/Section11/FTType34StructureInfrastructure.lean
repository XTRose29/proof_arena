import Submission.OddOrder.PF.Section09.PTypeReducibleCoreCases
import Submission.OddOrder.PF.Section11.FTType34Bounds

/-!
# Peterfalvi Section 11: the type-III/IV character rectangle

This file ports the part of `PFsection11.v` following Peterfalvi (11.7).  All
character-theoretic objects used below are the canonical objects attached to
`FTType34Base`; in particular the final Galois assertion concerns the factor
action extracted from `base.ptypeCtx` and not an action supplied by a caller.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open PTypeCoreContextInternal
open scoped BigOperators Classical Pointwise IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {M U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) ftType34StructureFintypeOfFinite
    (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-! ## The complement-action kernel -/

private theorem mem_ptypeFCoreAction_ker_iff34
    (ctx : PTypeFCoreContext M U W W₁ W₂) (u : U) :
    u ∈ (ptypeFCoreAction ctx).ker ↔
      ∀ h : G, h ∈ Fitting_core M →
        ⁅(u : G), h⁆ ∈ Ptype_Fcore_kernel ctx := by
  unfold ptypeFCoreAction
  exact mem_ker_subgroupConjugationFactorHom_iff _ _ _ _ _ u

private theorem ptypeFcompl_kernel_eq_centralizer_of_kernel_eq_bot34
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (hH₀ : Ptype_Fcore_kernel ctx = ⊥) :
    Ptype_Fcompl_kernel ctx = centralizerWithin U (Fitting_core M) := by
  rw [Ptype_Fcompl_kernel]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine mem_centralizerWithin.mpr ⟨u.property, ?_⟩
    intro h hh
    have hcommMem :
        ⁅(u : G), h⁆ ∈ Ptype_Fcore_kernel ctx :=
      (mem_ptypeFCoreAction_ker_iff34 ctx u).mp hu h hh
    have hcommOne : ⁅(u : G), h⁆ = 1 := by
      rw [hH₀] at hcommMem
      exact Subgroup.mem_bot.mp hcommMem
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcommOne).symm
  · intro hx
    have hx' := mem_centralizerWithin.mp hx
    let u : U := ⟨x, hx'.1⟩
    refine ⟨u, ?_, rfl⟩
    apply (mem_ptypeFCoreAction_ker_iff34 ctx u).mpr
    intro h hh
    have hcommOne : ⁅(u : G), h⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hx'.2 h hh).symm
    rw [hH₀]
    exact Subgroup.mem_bot.mpr hcommOne

/-- `PFsection11.v: Ptype_Fcompl_kernel_cent`. -/
theorem Ptype_Fcompl_kernel_cent
    (base : FTType34Base M U W W₁ W₂ defW) :
    Ptype_Fcompl_kernel base.ptypeCtx = base.C := by
  exact ptypeFcompl_kernel_eq_centralizer_of_kernel_eq_bot34 base.ptypeCtx
    (FTtype34_Fcore_kernel_trivial base).H0_eq_bot

namespace FTType34StructureInternal

/-! ## Canonical character data -/

noncomputable abbrev eta34
    (base : FTType34Base M U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) : ClassFunction G ℂ :=
  base.targetMap (base.isoG.cyclicTIImage (i, j))

noncomputable abbrev mu34
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) : ClassFunction M ℂ :=
  base.primeTI.primeTIRed base.isoM j

noncomputable abbrev muZero34
    (base : FTType34Base M U W W₁ W₂ defW) : ClassFunction M ℂ :=
  mu34 base
    (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)

noncomputable def etaColumn34
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) : ClassFunction G ℂ :=
  ∑ i : IrreducibleCharacter W₁ ℂ, eta34 base i j

noncomputable def etaZeroRow34
    (base : FTType34Base M U W W₁ W₂ defW) : ClassFunction G ℂ :=
  ∑ j : IrreducibleCharacter W₂ ℂ,
    eta34 base
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j

def eqProjection34
    (base : FTType34Base M U W W₁ W₂ defW)
    (alpha gamma : ClassFunction G ℂ) : Prop :=
  ∀ (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ),
    characterPairing (alpha - gamma) (eta34 base i j) = 0

noncomputable def dadeBridgeZero34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ) : ClassFunction G ℂ :=
  base.tau (muZero34 base - zeta)

noncomputable abbrev factorFacts34
    (base : FTType34Base M U W W₁ W₂ defW) :
    PTypeFCoreFactorFacts base.ptypeCtx :=
  Ptype_Fcore_factor_facts base.ptypeCtx

noncomputable abbrev factorAction34
    (base : FTType34Base M U W W₁ W₂ defW) :=
  Ptype_factor_action base.ptypeCtx (factorFacts34 base)

private theorem characterPairing_eta34
    (base : FTType34Base M U W W₁ W₂ defW)
    (i k : IrreducibleCharacter W₁ ℂ)
    (j ell : IrreducibleCharacter W₂ ℂ) :
    characterPairing (eta34 base i j) (eta34 base k ell) =
      if (i, j) = (k, ell) then 1 else 0 := by
  rw [base.targetMap_pairing]
  exact base.isoG.characterPairing_cyclicTIImage (i, j) (k, ell)

theorem characterPairing_etaColumn34
    (base : FTType34Base M U W W₁ W₂ defW)
    (j₀ : IrreducibleCharacter W₂ ℂ)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing (etaColumn34 base j₀) (eta34 base i j) =
      if j = j₀ then 1 else 0 := by
  classical
  rw [etaColumn34]
  change characterPairingRight (eta34 base i j)
      (∑ k : IrreducibleCharacter W₁ ℂ, eta34 base k j₀) = _
  rw [map_sum]
  by_cases hj : j = j₀
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single i]
    · change characterPairing (eta34 base i j₀) (eta34 base i j₀) = 1
      rw [characterPairing_eta34, if_pos rfl]
    · intro k _ hki
      change characterPairing (eta34 base k j₀) (eta34 base i j₀) = 0
      rw [characterPairing_eta34, if_neg]
      exact fun h ↦ hki (congrArg Prod.fst h)
    · simp
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro k _
    change characterPairing (eta34 base k j₀) (eta34 base i j) = 0
    rw [characterPairing_eta34, if_neg]
    intro h
    exact hj (congrArg Prod.snd h).symm

theorem characterPairing_etaZeroRow34
    (base : FTType34Base M U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing (etaZeroRow34 base) (eta34 base i j) =
      if i = IrreducibleCharacter.trivial then 1 else 0 := by
  classical
  rw [etaZeroRow34]
  change characterPairingRight (eta34 base i j)
      (∑ ell : IrreducibleCharacter W₂ ℂ,
        eta34 base
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
          ell) = _
  rw [map_sum]
  by_cases hi : i = IrreducibleCharacter.trivial
  · subst i
    rw [if_pos rfl, Finset.sum_eq_single j]
    · change characterPairing
          (eta34 base
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j)
          (eta34 base
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j) = 1
      rw [characterPairing_eta34, if_pos rfl]
    · intro ell _ hell
      change characterPairing
          (eta34 base
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) ell)
          (eta34 base
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j) = 0
      rw [characterPairing_eta34, if_neg]
      exact fun h ↦ hell (congrArg Prod.snd h)
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro ell _
    change characterPairing
        (eta34 base
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) ell)
        (eta34 base i j) = 0
    rw [characterPairing_eta34, if_neg]
    intro h
    exact hi (congrArg Prod.fst h).symm

theorem eqProjection34_iff
    (base : FTType34Base M U W W₁ W₂ defW)
    (alpha gamma : ClassFunction G ℂ) :
    eqProjection34 base alpha gamma ↔
      ∀ (i : IrreducibleCharacter W₁ ℂ)
        (j : IrreducibleCharacter W₂ ℂ),
          characterPairing alpha (eta34 base i j) =
            characterPairing gamma (eta34 base i j) := by
  constructor
  · intro h i j
    have hij := h i j
    have hsub : characterPairing (alpha - gamma) (eta34 base i j) =
        characterPairing alpha (eta34 base i j) -
          characterPairing gamma (eta34 base i j) := by
      change characterPairingRight (eta34 base i j) (alpha - gamma) = _
      exact map_sub (characterPairingRight (eta34 base i j)) alpha gamma
    rw [hsub] at hij
    exact sub_eq_zero.mp hij
  · intro h i j
    have hsub : characterPairing (alpha - gamma) (eta34 base i j) =
        characterPairing alpha (eta34 base i j) -
          characterPairing gamma (eta34 base i j) := by
      change characterPairingRight (eta34 base i j) (alpha - gamma) = _
      exact map_sub (characterPairingRight (eta34 base i j)) alpha gamma
    rw [hsub, h i j, sub_self]

/-! ## Section 11 layer infrastructure -/

private theorem ftType34_kernelLayer_subcoherent11
    (base : FTType34Base M U W W₁ W₂ defW) :
    subcoherent (FTtypePKernelLayer base.primeDade) base.tau base.R := by
  let R₀ := FTtypeP_coh_base base.primeDade base.isoM base.isoG (mFT_odd M)
  have hsub := FTtypeP_subcoherent
    base.primeDade base.isoM base.isoG (mFT_odd M)
  exact
    { finite := hsub.finite
      source_character := hsub.source_character
      source_virtual := hsub.source_virtual
      zero_not_mem := hsub.zero_not_mem
      degree_ne_zero := hsub.degree_ne_zero
      inverse_ne := hsub.inverse_ne
      inverse_mem := hsub.inverse_mem
      tau_isometry := by
        intro phi hphi hphiOff psi hpsi hpsiOff
        change characterPairing
            (base.targetMap (Dade base.primeDade.prDade_hyp phi))
            (base.targetMap (Dade base.primeDade.prDade_hyp psi)) = _
        rw [base.targetMap_pairing]
        exact hsub.tau_isometry phi hphi hphiOff psi hpsi hpsiOff
      tau_virtual := by
        intro phi hphi hphiOff
        exact base.targetMap_virtual (hsub.tau_virtual phi hphi hphiOff)
      tau_supported := by
        intro phi hphi hphiOff
        exact base.targetMap_supported (hsub.tau_supported phi hphi hphiOff)
      pairwise_orthogonal := hsub.pairwise_orthogonal
      image_virtual := by
        intro xi hxi alpha halpha
        rw [FTType34Base.R] at halpha
        rcases Finset.mem_map.mp halpha with ⟨beta, hbeta, rfl⟩
        exact base.targetMap_virtual (hsub.image_virtual xi hxi beta hbeta)
      image_orthonormal := by
        intro xi hxi alpha halpha beta hbeta
        rw [FTType34Base.R] at halpha hbeta
        rcases Finset.mem_map.mp halpha with ⟨alpha₀, halpha₀, rfl⟩
        rcases Finset.mem_map.mp hbeta with ⟨beta₀, hbeta₀, rfl⟩
        change characterPairing (base.targetMap alpha₀)
          (base.targetMap beta₀) = _
        rw [base.targetMap_pairing]
        simpa only [EmbeddingLike.apply_eq_iff_eq] using
          hsub.image_orthonormal xi hxi alpha₀ halpha₀ beta₀ hbeta₀
      tau_inverse_sub := by
        intro xi hxi
        change base.targetMap
            (Dade base.primeDade.prDade_hyp
              (xi - ClassFunction.inverseLinear xi)) = _
        rw [hsub.tau_inverse_sub xi hxi]
        simp [FTType34Base.R, R₀, Finset.sum_map]
      image_orthogonal := by
        intro xi hxi phi hphi hpair hpairInv alpha halpha beta hbeta
        rw [FTType34Base.R] at halpha hbeta
        rcases Finset.mem_map.mp halpha with ⟨alpha₀, halpha₀, rfl⟩
        rcases Finset.mem_map.mp hbeta with ⟨beta₀, hbeta₀, rfl⟩
        change characterPairing (base.targetMap alpha₀)
          (base.targetMap beta₀) = 0
        rw [base.targetMap_pairing]
        exact hsub.image_orthogonal xi hxi phi hphi hpair hpairInv
          alpha₀ halpha₀ beta₀ hbeta₀ }

theorem ftType34_bottom_subcoherent34
    (base : FTType34Base M U W W₁ W₂ defW) :
    subcoherent
      (↑(ftType34Layer base ⊥) : Set (ClassFunction M ℂ))
      base.tau base.R := by
  simpa [FTtypePKernelLayer, PrimeDadeHypothesis.signalizerInKernel,
    ftType34Layer, base.FTcore_eq_HU] using
      ftType34_kernelLayer_subcoherent11 base

theorem ftType34S1_cfConjC_subset34
    (base : FTType34Base M U W W₁ W₂ defW) :
    cfConjC_subset
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (↑(ftType34Layer base ⊥) : Set (ClassFunction M ℂ)) := by
  change
    ((↑(seqIndD (k := ℂ) base.HUInM
        (⊤ : Subgroup base.HUInM) base.HCInHU) :
          Set (ClassFunction M ℂ)) ⊆
      (↑(seqIndD (k := ℂ) base.HUInM
        (⊤ : Subgroup base.HUInM) (⊥ : Subgroup base.HUInM)) :
          Set (ClassFunction M ℂ))) ∧
      ∀ phi ∈ seqIndD (k := ℂ) base.HUInM
          (⊤ : Subgroup base.HUInM) base.HCInHU,
        ClassFunction.inverseLinear phi ∈
          seqIndD (k := ℂ) base.HUInM
            (⊤ : Subgroup base.HUInM) base.HCInHU
  exact seqInd_conjC_subset1 (k := ℂ) base.HUInM
    (⊤ : Subgroup base.HUInM) (⊤ : Subgroup base.HUInM)
    base.HCInHU le_rfl

theorem ftType34S1_subset_kernelLayer34
    (base : FTType34Base M U W W₁ W₂ defW) :
    (↑(ftType34S1 base) : Set (ClassFunction M ℂ)) ⊆
      FTtypePKernelLayer base.primeDade := by
  intro zeta hzeta
  have hbottom := (ftType34S1_cfConjC_subset34 base).1 hzeta
  simpa [FTtypePKernelLayer, PrimeDadeHypothesis.signalizerInKernel,
    ftType34Layer, base.FTcore_eq_HU] using hbottom

theorem ftType34S2_cfConjC_subset34
    (base : FTType34Base M U W W₁ W₂ defW) :
    cfConjC_subset
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ))
      (↑(ftType34Layer base ⊥) : Set (ClassFunction M ℂ)) := by
  change
    ((↑(seqIndD (k := ℂ) base.HUInM
        base.HCInHU base.CInHU) : Set (ClassFunction M ℂ)) ⊆
      (↑(seqIndD (k := ℂ) base.HUInM
        (⊤ : Subgroup base.HUInM) (⊥ : Subgroup base.HUInM)) :
          Set (ClassFunction M ℂ))) ∧
      ∀ phi ∈ seqIndD (k := ℂ) base.HUInM
          base.HCInHU base.CInHU,
        ClassFunction.inverseLinear phi ∈
          seqIndD (k := ℂ) base.HUInM base.HCInHU base.CInHU
  exact seqInd_conjC_subset1 (k := ℂ) base.HUInM
    (⊤ : Subgroup base.HUInM) base.HCInHU base.CInHU le_top

theorem ftType34S1_subcoherent34
    (base : FTType34Base M U W W₁ W₂ defW) :
    subcoherent
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      base.tau base.R :=
  subset_subcoherent (ftType34_bottom_subcoherent34 base)
    (ftType34S1_cfConjC_subset34 base)

private theorem ftType34S2_subcoherent34
    (base : FTType34Base M U W W₁ W₂ defW) :
    subcoherent
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ))
      base.tau base.R :=
  subset_subcoherent (ftType34_bottom_subcoherent34 base)
    (ftType34S2_cfConjC_subset34 base)

/-! ## Degree and coherence of `S₁` -/

theorem secondDerivedInM_eq_commutator_map11
    (M : Subgroup G) :
    (secondDerivedWithin M).subgroupOf M =
      (_root_.commutator ((derivedWithin M).subgroupOf M)).map
        ((derivedWithin M).subgroupOf M).subtype := by
  have hderM : derivedWithin M ≤ M :=
    TypeSpecInternal.derivedWithin_le16_final M
  change (derivedWithin (derivedWithin M)).subgroupOf M =
    (_root_.commutator ((derivedWithin M).subgroupOf M)).map
      ((derivedWithin M).subgroupOf M).subtype
  rw [show derivedWithin (derivedWithin M) =
      ⁅derivedWithin M, derivedWithin M⁆ by
    exact (derivedWithin M).map_subtype_commutator]
  rw [subgroupOf_commutator_eq hderM hderM]
  exact ((derivedWithin M).subgroupOf M).map_subtype_commutator.symm

/-! The Section 10 quotient-Frobenius induction argument is private there.
The following local copy keeps the Section 11 irreducibility adapter private
as well, without adding a support-module interface. -/

private theorem representation_irreducible_comp_surjective34
    {A B k V : Type} [Group A] [Group B] [Field k]
    [AddCommGroup V] [Module k V]
    (rho : Representation k B V) [Representation.IsIrreducible rho]
    (f : A →* B) (hf : Function.Surjective f) :
    Representation.IsIrreducible (rho.comp f) := by
  let sigma : Representation k A V := rho.comp f
  have hbot_ne_top : (⊥ : Subrepresentation sigma) ≠ ⊤ := by
    intro h
    apply IsSimpleOrder.bot_ne_top (α := Subrepresentation rho)
    apply SetLike.ext
    intro v
    have hv := congrArg (fun U : Subrepresentation sigma ↦ v ∈ U) h
    change (v ∈ (⊥ : Submodule k V)) =
      (v ∈ (⊤ : Submodule k V)) at hv
    exact iff_of_eq hv
  letI : Nontrivial (Subrepresentation sigma) :=
    ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
  refine IsSimpleOrder.of_forall_eq_top fun U hU ↦ ?_
  let U' : Subrepresentation rho :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule b v hv := by
        obtain ⟨a, rfl⟩ := hf b
        exact U.apply_mem_toSubmodule a hv }
  have hU' : U' ≠ ⊥ := by
    intro hbot
    apply hU
    apply SetLike.ext
    intro v
    have hv := congrArg (fun W : Subrepresentation rho ↦ v ∈ W) hbot
    change (v ∈ U.toSubmodule) =
      (v ∈ (⊥ : Submodule k V)) at hv
    exact iff_of_eq hv
  have htop : U' = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'
  apply SetLike.ext
  intro v
  have hv := congrArg (fun W : Subrepresentation rho ↦ v ∈ W) htop
  change (v ∈ U.toSubmodule) =
    (v ∈ (⊤ : Submodule k V)) at hv
  exact iff_of_eq hv

private noncomputable def IrreducibleCharacter.comapSurjective34
    {A B : Type} [Group A] [Fintype A] [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) :
    IrreducibleCharacter A ℂ := by
  let rho : Representation ℂ A chi.representation :=
    chi.representation.ρ.comp f
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  letI : Representation.IsIrreducible rho :=
    representation_irreducible_comp_surjective34
      chi.representation.ρ f hf
  letI : CategoryTheory.Simple (FDRep.of rho) :=
    simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep (FDRep.of rho)

@[simp]
private theorem IrreducibleCharacter.comapSurjective34_apply
    {A B : Type} [Group A] [Fintype A] [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) (a : A) :
    IrreducibleCharacter.comapSurjective34 f hf chi a = chi (f a) := by
  simp only [IrreducibleCharacter.comapSurjective34,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character (f a) = chi (f a)
  exact chi.representation_character (f a)

private noncomputable def IrreducibleCharacter.quotientDescend34
    {A : Type} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal]
    (chi : IrreducibleCharacter A ℂ)
    (hN : N ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) :
    IrreducibleCharacter (A ⧸ N) ℂ := by
  have hNrho : N ≤ chi.representation.ρ.ker := by
    rw [← ClassFunction.translationKernel_irreducibleCharacter chi]
    exact hN
  let rhoQ : Representation ℂ (A ⧸ N) chi.representation :=
    QuotientGroup.lift N chi.representation.ρ hNrho
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  have hrhoQcomp : rhoQ.comp q = chi.representation.ρ := by
    ext a v
    rfl
  letI : Representation.IsIrreducible (rhoQ.comp q) := by
    rw [hrhoQcomp]
    infer_instance
  letI : Representation.IsIrreducible rhoQ :=
    representation_isIrreducible_of_comp rhoQ q
  letI : CategoryTheory.Simple (FDRep.of rhoQ) :=
    simple_fdRep_of_isIrreducible rhoQ
  exact IrreducibleCharacter.ofFDRep (FDRep.of rhoQ)

@[simp]
private theorem IrreducibleCharacter.quotientDescend34_mk_apply
    {A : Type} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal]
    (chi : IrreducibleCharacter A ℂ)
    (hN : N ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) (a : A) :
    IrreducibleCharacter.quotientDescend34 N chi hN
        (QuotientGroup.mk' N a) = chi a := by
  simp only [IrreducibleCharacter.quotientDescend34,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character a = chi a
  exact chi.representation_character a

private theorem irreducible_induce_of_derived_quotient_frobenius34
    {A : Type} [Group A] [Fintype A]
    (K N : Subgroup A) [K.Normal] [N.Normal]
    (hNK : N ≤ K)
    {E : Subgroup (A ⧸ N)}
    (hFrob : IsFrobeniusDecomposition
      (K.map (QuotientGroup.mk' N)) E)
    (theta : IrreducibleCharacter K ℂ)
    (hNtheta : N.subgroupOf K ≤
      ClassFunction.translationKernel (theta : ClassFunction K ℂ))
    (htheta : ¬(⊤ : Subgroup K) ≤
      ClassFunction.translationKernel (theta : ClassFunction K ℂ)) :
    IsIrreducibleCharacter A ℂ
      (ClassFunction.induce K (theta : ClassFunction K ℂ)) := by
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  let Kq : Subgroup (A ⧸ N) := K.map q
  let eK : (K ⧸ N.subgroupOf K) ≃* Kq :=
    ClassFunction.subgroupQuotientEquivImage N K hNK
  let thetaQ : IrreducibleCharacter (K ⧸ N.subgroupOf K) ℂ :=
    IrreducibleCharacter.quotientDescend34
      (N.subgroupOf K) theta hNtheta
  let thetaBar : IrreducibleCharacter Kq ℂ :=
    IrreducibleCharacter.comapSurjective34
      eK.symm.toMonoidHom eK.symm.surjective thetaQ
  have hthetaBar : thetaBar ≠ IrreducibleCharacter.trivial := by
    intro htriv
    have hthetaTriv : theta = IrreducibleCharacter.trivial := by
      ext x
      calc
        theta x = thetaQ (QuotientGroup.mk' (N.subgroupOf K) x) := by
          rw [IrreducibleCharacter.quotientDescend34_mk_apply]
        _ = thetaBar (eK (QuotientGroup.mk' (N.subgroupOf K) x)) := by
          rw [IrreducibleCharacter.comapSurjective34_apply]
          exact congrArg (fun y ↦ thetaQ y)
            (eK.symm_apply_apply _).symm
        _ = IrreducibleCharacter.trivial
            (eK (QuotientGroup.mk' (N.subgroupOf K) x)) := by rw [htriv]
        _ = IrreducibleCharacter.trivial x := by simp
    apply htheta
    rw [hthetaTriv]
    intro x _ g
    simp
  let chiQ : IrreducibleCharacter (A ⧸ N) ℂ :=
    ⟨ClassFunction.induce Kq (thetaBar : ClassFunction Kq ℂ),
      irr_induced_Frobenius_ker hFrob thetaBar hthetaBar⟩
  let chi : IrreducibleCharacter A ℂ :=
    IrreducibleCharacter.comapSurjective34 q
      (QuotientGroup.mk'_surjective N) chiQ
  refine ⟨chi.representation, chi.representation_simple, ?_⟩
  have hthetaInflate :
      ClassFunction.inflate (N.subgroupOf K)
          (thetaQ : ClassFunction (K ⧸ N.subgroupOf K) ℂ) =
        (theta : ClassFunction K ℂ) := by
    ext x
    exact IrreducibleCharacter.quotientDescend34_mk_apply
      (N.subgroupOf K) theta hNtheta x
  have hthetaBarClass :
      (thetaBar : ClassFunction Kq ℂ) =
        ClassFunction.subgroupQuotientToImage N K hNK
          (thetaQ : ClassFunction _ ℂ) := by
    ext y
    simp only [thetaBar,
      IrreducibleCharacter.comapSurjective34_apply,
      ClassFunction.subgroupQuotientToImage_apply, eK]
    rfl
  have hIndMod := ClassFunction.cfIndMod
    (k := ℂ) N K hNK
      (thetaQ : ClassFunction (K ⧸ N.subgroupOf K) ℂ)
  calc
    ClassFunction.ofRepresentation chi.representation.ρ =
        (chi : ClassFunction A ℂ) := chi.ofRepresentation_representation
    _ = ClassFunction.inflate N (chiQ : ClassFunction (A ⧸ N) ℂ) := by
      ext x
      simp only [chi, ClassFunction.inflate_apply,
        IrreducibleCharacter.comapSurjective34_apply]
      rfl
    _ = ClassFunction.inflate N
        (ClassFunction.induce Kq (thetaBar : ClassFunction Kq ℂ)) := rfl
    _ = ClassFunction.inflate N
        (ClassFunction.induce Kq
          (ClassFunction.subgroupQuotientToImage N K hNK
            (thetaQ : ClassFunction _ ℂ))) := by rw [hthetaBarClass]
    _ = ClassFunction.induce K
        (ClassFunction.inflate (N.subgroupOf K)
          (thetaQ : ClassFunction (K ⧸ N.subgroupOf K) ℂ)) := by
      exact hIndMod.symm
    _ = ClassFunction.induce K (theta : ClassFunction K ℂ) := by
      rw [hthetaInflate]

private instance ftType34DerivedInM_normal11
    (M : Subgroup G) : ((derivedWithin M).subgroupOf M).Normal :=
  TypeSpecInternal.derivedWithin_normal16 M

private instance ftType34SecondDerivedInM_normal11
    (M : Subgroup G) :
    ((secondDerivedWithin M).subgroupOf M).Normal := by
  let K : Subgroup M := (derivedWithin M).subgroupOf M
  letI : K.Normal := ftType34DerivedInM_normal11 M
  rw [secondDerivedInM_eq_commutator_map11 M]
  infer_instance

theorem ftType34_secondDerived_subgroup_eq_HCInHU11
    (base : FTType34Base M U W W₁ W₂ defW) :
    ((secondDerivedWithin M).subgroupOf M).subgroupOf base.HUInM =
      base.HCInHU := by
  change ((secondDerivedWithin M).subgroupOf M).subgroupOf base.HUInM =
    (base.HC.subgroupOf M).subgroupOf base.HUInM
  rw [FTtype34_der2 base]

theorem ftType34S1_irreducible34
    (base : FTType34Base M U W W₁ W₂ defW) :
    ∀ zeta ∈ ftType34S1 base,
      IsIrreducibleCharacter M ℂ zeta := by
  intro zeta hzeta
  change zeta ∈ seqIndD (k := ℂ) base.HUInM ⊤ base.HCInHU at hzeta
  obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp hzeta
  let K : Subgroup M := base.HUInM
  let N : Subgroup M := (secondDerivedWithin M).subgroupOf M
  letI : K.Normal := ftType34DerivedInM_normal11 M
  letI : N.Normal := ftType34SecondDerivedInM_normal11 M
  have hNK : N ≤ K := by
    intro x hx
    change (x : G) ∈ derivedWithin M
    exact Subgroup.map_subtype_le (_root_.commutator (derivedWithin M)) hx
  have hNtheta : N.subgroupOf K ≤
      ClassFunction.translationKernel (theta : ClassFunction K ℂ) := by
    rw [show N.subgroupOf K = base.HCInHU by
      exact ftType34_secondDerived_subgroup_eq_HCInHU11 base]
    exact (mem_Iirr_kerD.mp htheta).1
  have hthetaTop : ¬(⊤ : Subgroup K) ≤
      ClassFunction.translationKernel (theta : ClassFunction K ℂ) :=
    (mem_Iirr_kerD.mp htheta).2
  have hFrob : IsFrobeniusDecomposition
      (K.map (QuotientGroup.mk' N))
      ((W₁.subgroupOf M).map (QuotientGroup.mk' N)) := by
    simpa only [K, N] using
      (FTType345ConstantsInternal.ftType345_derived_quotient_frobenius
        base.MtypeP)
  exact irreducible_induce_of_derived_quotient_frobenius34
    K N hNK hFrob theta hNtheta hthetaTop

theorem ftType34_HUInM_index_eq_q11
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.HUInM.index = base.q := by
  calc
    base.HUInM.index = Nat.card (W₁.subgroupOf M) :=
      base.derived_complement_decomposition.2.2.2.symm.index_eq_card
    _ = Nat.card W₁ := MathlibSupport.natCard_subgroupOf_eq
      base.derived_complement_decomposition.2.1
    _ = base.q := rfl

private theorem ftType34_commutator_HU_le_HC11
    (base : FTType34Base M U W W₁ W₂ defW) :
    _root_.commutator base.HUInM ≤ base.HCInHU := by
  intro x hx
  change (x : M) ∈ base.HC.subgroupOf M
  rw [← FTtype34_der2 base]
  rw [secondDerivedInM_eq_commutator_map11 M]
  exact ⟨x, hx, rfl⟩

theorem ftType34S1_degree34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ) (hzeta : zeta ∈ ftType34S1 base) :
    zeta 1 = (base.q : ℂ) := by
  change zeta ∈ seqIndD (k := ℂ) base.HUInM ⊤ base.HCInHU at hzeta
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hzeta
  have hchiDer : _root_.commutator base.HUInM ≤
      ClassFunction.translationKernel
        (chi : ClassFunction base.HUInM ℂ) :=
    (ftType34_commutator_HU_le_HC11 base).trans
      (mem_Iirr_kerD.mp hchi).1
  have hchiLinear : pTypeIsLinearCharacter chi :=
    pTypeCore_linear_of_commutator_le_kernel chi hchiDer
  rw [ClassFunction.induce_one,
    internal.pTypeLinear_apply_one chi hchiLinear,
    ftType34_HUInM_index_eq_q11 base, mul_one]

theorem ftType34S1_coherent34
    (base : FTType34Base M U W W₁ W₂ defW) :
    coherent
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (nonidentitySet M) base.tau := by
  apply uniform_degree_coherence (ftType34S1_subcoherent34 base)
  intro chi hchi psi hpsi
  exact (ftType34S1_degree34 base chi hchi).trans
    (ftType34S1_degree34 base psi hpsi).symm

private theorem ftType34_muZero_degree34
    (base : FTType34Base M U W W₁ W₂ defW) :
    (muZero34 base) 1 = (base.q : ℂ) := by
  rw [base.primeTI.prTIred_1 base.isoM,
    base.primeTI.prTIirr0_1 base.isoM, mul_one]

theorem ftType34_bridgeZero_virtual34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ) (hzeta : zeta ∈ ftType34S1 base) :
    ClassFunction.IsVirtual (ftType34Bridge0 (muZero34 base) zeta) := by
  exact
    (base.primeTI.prTIred_char base.isoM
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)).isVirtual.sub
      ((ftType34S1_subcoherent34 base).source_virtual zeta hzeta)

theorem ftType34_bridgeZero_supported34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ) (hzeta : zeta ∈ ftType34S1 base) :
    ftType34Bridge0 (muZero34 base) zeta ∈
      ClassFunction.supportedOn (nonidentitySet M) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxOne : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  change (muZero34 base) 1 - zeta 1 = 0
  rw [ftType34_muZero_degree34 base,
    ftType34S1_degree34 base zeta hzeta, sub_self]

/-! ## Canonical action subgroups and coherence of `S₂` -/

private theorem ftType34_actionKernel_map_eq_C11
    (base : FTType34Base M U W W₁ W₂ defW) :
    (factorAction34 base).C.map U.subtype = base.C := by
  change (ptypeFCoreAction base.ptypeCtx).ker.map U.subtype = base.C
  exact Ptype_Fcompl_kernel_cent base

theorem ftType34_actionKernel_eq_CInU11
    (base : FTType34Base M U W W₁ W₂ defW) :
    (factorAction34 base).C = base.CInU := by
  apply Subgroup.map_injective U.subtype_injective
  rw [ftType34_actionKernel_map_eq_C11 base]
  exact (Subgroup.map_subgroupOf_eq_of_le base.C_le_U).symm

private theorem ftType34_H0InHU_eq_bot11
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.H0InHU = ⊥ := by
  have hH₀ : base.H0 = ⊥ :=
    (FTtype34_Fcore_kernel_trivial base).H0_eq_bot
  change ((base.H0.subgroupOf M).subgroupOf base.HUInM) = ⊥
  rw [hH₀]
  simp

private theorem ftType34_actionH0C_eq_CInHU11
    (base : FTType34Base M U W W₁ W₂ defW) :
    pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel base.ptypeCtx) U W₁
      (factorAction34 base) = base.CInHU := by
  unfold pTypeH0CInDerived
  rw [ftType34_actionKernel_map_eq_C11 base]
  change base.H0InHU ⊔ base.CInHU = base.CInHU
  simpa only [ftType34_H0InHU_eq_bot11 base, bot_sup_eq]

private theorem ftType34_actionHC_eq_HCInM11
    (base : FTType34Base M U W W₁ W₂ defW) :
    pTypeHCInMaximal M (Fitting_core M) U W₁
      (factorAction34 base) = base.HC.subgroupOf M := by
  unfold pTypeHCInMaximal
  rw [ftType34_actionKernel_map_eq_C11 base]
  change base.H.subgroupOf M ⊔ base.C.subgroupOf M =
    (base.H ⊔ base.C).subgroupOf M
  exact (Subgroup.subgroupOf_sup
    (base.H_le_HU.trans base.HU_le_M)
    (base.C_le_HU.trans base.HU_le_M)).symm

private theorem ftType34_HCInHU_eq_sup11
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.HCInHU = base.HInHU ⊔ base.CInHU := by
  change ((base.H ⊔ base.C).subgroupOf M).subgroupOf base.HUInM =
    (base.H.subgroupOf M).subgroupOf base.HUInM ⊔
      (base.C.subgroupOf M).subgroupOf base.HUInM
  rw [Subgroup.subgroupOf_sup
    (base.H_le_HU.trans base.HU_le_M)
    (base.C_le_HU.trans base.HU_le_M)]
  rw [Subgroup.subgroupOf_sup
    (Subgroup.subgroupOf_mono M base.H_le_HU)
    (Subgroup.subgroupOf_mono M base.C_le_HU)]

theorem ftType34S2_eq_H_C11
    (base : FTType34Base M U W W₁ W₂ defW) :
    ftType34S2 base =
      seqIndD (k := ℂ) base.HUInM base.HInHU base.CInHU := by
  calc
    ftType34S2 base =
        seqIndD (k := ℂ) base.HUInM base.HCInHU base.CInHU := rfl
    _ = seqIndD (k := ℂ) base.HUInM
        (base.CInHU ⊔ base.HInHU) base.CInHU := by
      rw [ftType34_HCInHU_eq_sup11 base, sup_comm]
    _ = seqIndD (k := ℂ) base.HUInM base.HInHU base.CInHU :=
      seqIndDY base.HUInM base.HInHU base.CInHU

private theorem ftType34_coreKernelDerivedComplement_le_C11
    (base : FTType34Base M U W W₁ W₂ defW) :
    pTypeCoreKernelDerivedComplement base.ptypeCtx ≤ base.CInHU := by
  have hle := pTypeCoreKernelDerivedComplement_le_H0C
    base.ptypeCtx (factorFacts34 base)
  rw [ftType34_actionH0C_eq_CInHU11 base] at hle
  exact hle

theorem ftType34S2_subset_core11
    (base : FTType34Base M U W W₁ W₂ defW) :
    (↑(ftType34S2 base) : Set (ClassFunction M ℂ)) ⊆
      ↑(pTypeCoreFamilyOfContext base.ptypeCtx) := by
  intro phi hphi
  rw [ftType34S2_eq_H_C11 base] at hphi
  change phi ∈ seqIndD (k := ℂ) base.HUInM base.HInHU
    (pTypeCoreKernelDerivedComplement base.ptypeCtx)
  exact seqIndS base.HUInM
    (Iirr_kerDS (k := ℂ)
      (A₁ := base.CInHU)
      (A₂ := pTypeCoreKernelDerivedComplement base.ptypeCtx)
      (B₁ := base.HInHU) (B₂ := base.HInHU)
      (ftType34_coreKernelDerivedComplement_le_C11 base) le_rfl) hphi

theorem ftType34S2_coherent34
    (base : FTType34Base M U W W₁ W₂ defW) :
    coherent
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ))
      (nonidentitySet M) base.tau := by
  have hcore := Ptype_core_coherence
    base.maxM defW base.MtypeP base.notMtype5
  dsimp only at hcore
  have hctx :
      Ptype_Fcore_context base.maxM defW base.MtypeP base.notMtype5 =
        base.ptypeCtx := Subsingleton.elim _ _
  rw [hctx] at hcore
  have hS2Dade := subset_coherent (ftType34S2_subset_core11 base) hcore
  change coherent
    (↑(ftType34S2 base) : Set (ClassFunction M ℂ))
    (nonidentitySet M)
    (base.targetMap.comp (Dade (FT_Dade0_hyp M base.maxM)))
  exact (base.coherent_targetMap_iff
    (S := (↑(ftType34S2 base) : Set (ClassFunction M ℂ)))
    (A := nonidentitySet M)
    (sigma := Dade (FT_Dade0_hyp M base.maxM))).2 hS2Dade

/-! ## Reducible columns -/

private def ftType34ReducibleCore11
    (base : FTType34Base M U W W₁ W₂ defW) :
    Finset (ClassFunction M ℂ) :=
  pTypeReducibleLayer base.HUInM base.HInHU base.H0InHU

private def ftType34NontrivialReducedColumns11
    (base : FTType34Base M U W W₁ W₂ defW) :
    Finset (ClassFunction M ℂ) :=
  Finset.image (mu34 base)
    (Finset.univ.erase
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))

private theorem ftType34_reducibleCore_data11
    (base : FTType34Base M U W W₁ W₂ defW) :
    let D := factorAction34 base
    (ftType34ReducibleCore11 base).card = base.p - 1 ∧
      (ftType34ReducibleCore11 base).Nonempty ∧
      ftType34ReducibleCore11 base ⊆
        ftType34NontrivialReducedColumns11 base ∧
      ∀ zeta ∈ ftType34ReducibleCore11 base,
        pTypeIsIndHC base.HUInM base.HInHU
          (pTypeH0CInDerived M (derivedWithin M)
            (Ptype_Fcore_kernel base.ptypeCtx) U W₁ D)
          (pTypeHCInMaximal M (Fitting_core M) U W₁ D)
          base.q (pTypeActionFactorCard D) zeta := by
  have hraw := typeP_reducible_core_Ind
    M U W W₁ W₂ defW base.maxM base.MtypeP base.notMtype5
  dsimp only at hraw
  have hctx :
      Ptype_Fcore_context base.maxM defW base.MtypeP base.notMtype5 =
        base.ptypeCtx := Subsingleton.elim _ _
  rw [hctx] at hraw
  simpa only [ftType34ReducibleCore11,
    ftType34NontrivialReducedColumns11,
    factorAction34, factorFacts34,
    Ptype_factor_action_p, Ptype_factor_action_q,
    typeIII_IV_core_prime base.ptypeCtx base.notMtype2] using hraw

private theorem ftType34_reducibleCore_eq_columns11
    (base : FTType34Base M U W W₁ W₂ defW) :
    ftType34ReducibleCore11 base =
      ftType34NontrivialReducedColumns11 base := by
  letI : IsCyclic W₂ := base.primeTI.fixed_cyclic
  have hdata := ftType34_reducibleCore_data11 base
  dsimp only at hdata
  apply Finset.eq_of_subset_of_card_le hdata.2.2.1
  have hcolumns :
      (ftType34NontrivialReducedColumns11 base).card = base.p - 1 := by
    rw [ftType34NontrivialReducedColumns11,
      Finset.card_image_of_injective _
        (base.primeTI.prTIred_inj base.isoM)]
    simp [IrreducibleCharacter.card_eq_natCard_of_isCyclic,
      FTType34Base.p]
  rw [hcolumns, hdata.1]

private theorem ftType34_mu_mem_reducibleCore11
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    (mu34 base) j ∈ ftType34ReducibleCore11 base := by
  rw [ftType34_reducibleCore_eq_columns11 base,
    ftType34NontrivialReducedColumns11]
  exact Finset.mem_image.mpr
    ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩, rfl⟩

theorem ftType34_actionFactorCard_eq_u11
    (base : FTType34Base M U W W₁ W₂ defW) :
    pTypeActionFactorCard (factorAction34 base) = base.u := by
  rw [PTypeCoreActionKernelInternal.pTypeCore_actionFactorCard_eq_C_index,
    ftType34_actionKernel_eq_CInU11 base]

theorem ftType34_mu_degree11
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    (mu34 base) j 1 = ((base.q * base.u : ℕ) : ℂ) := by
  have hdata := ftType34_reducibleCore_data11 base
  dsimp only at hdata
  have hind := hdata.2.2.2 ((mu34 base) j)
    (ftType34_mu_mem_reducibleCore11 base j hj)
  rw [ftType34_actionFactorCard_eq_u11 base] at hind
  exact hind.1

theorem ftType34_mu_mem_S2_reducible11
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    (mu34 base) j ∈ ftType34S2 base ∧
      ¬ IsIrreducibleCharacter M ℂ ((mu34 base) j) := by
  have hdata := ftType34_reducibleCore_data11 base
  dsimp only at hdata
  have hind := hdata.2.2.2 ((mu34 base) j)
    (ftType34_mu_mem_reducibleCore11 base j hj)
  have hmem : (mu34 base) j ∈
      seqIndD (k := ℂ) base.HUInM base.HInHU base.CInHU := by
    rw [← ftType34_actionH0C_eq_CInHU11 base]
    exact hind.2.1
  refine ⟨?_, base.primeTI.prTIred_not_irr base.isoM j⟩
  rw [ftType34S2_eq_H_C11 base]
  exact hmem

end FTType34StructureInternal

end

end Submission.OddOrder.PF
