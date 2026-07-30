import Submission.OddOrder.PF.Section09.PTypeCoreCoherence
import Submission.OddOrder.MathlibSupport.ComplexCyclotomicPowerAutomorphism

/-!
# Peterfalvi Section 10: reference character and type-III--V constants

This module contains the canonical Section 10 objects and the proofs of
Peterfalvi (10.2)--(10.3).  Later Section 10 phases import the internal
aliases below rather than reconstructing the Prime-TI and Dade data.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise IsMulCommutative commutatorElement

variable {Gamma : Type} [Group Gamma] [Fintype Gamma]
variable [IsMinSimpleOddGroup Gamma]
variable {M U W W₁ W₂ : Subgroup Gamma}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

namespace FTType345ConstantsInternal

/-! ## Canonical Section 10 objects -/

/-- Source `M'`, regarded as a subgroup of the group type `M`. -/
abbrev ftType345DerivedInM (M : Subgroup Gamma) : Subgroup M :=
  (derivedWithin M).subgroupOf M

/-- Source `calS = seqIndD M' M M' 1`. -/
def ftType345InducedFamily10 (M : Subgroup Gamma) :
    Finset (ClassFunction M ℂ) :=
  seqIndD (k := ℂ) (ftType345DerivedInM M)
    (⊤ : Subgroup (ftType345DerivedInM M)) ⊥

/-- Pull source `'A0(M)` back to the group type `M`. -/
def ftType345Support0InM (M : Subgroup Gamma) : Set M :=
  {x | (x : Gamma) ∈ FTsupport0 M}

/-- Pull the ambient cyclic-TI set back to the top subgroup. -/
def ftType345CyclicSupport
    (W W₁ W₂ : Subgroup Gamma) : Set (⊤ : Subgroup Gamma) :=
  {x | (x : Gamma) ∈ cyclicTISet W W₁ W₂}

/-- The canonical prime-TI hypothesis attached to a type-P witness. -/
abbrev ftType345PrimeTI
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    PrimeTIHypothesis M (derivedWithin M) W W₁ W₂ defW :=
  FT_primeTI_hyp defW MtypeP

/-- The canonical prime-TI cyclic isometry on `M`. -/
noncomputable abbrev ftType345IsoM
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    CyclicTIIsometryData (k := ℂ)
      (ftType345PrimeTI MtypeP).prime_cycTIhyp :=
  (ftType345PrimeTI MtypeP).prime_cycTIhyp.cyclicTIIsometryData

/-- The canonical prime-Dade hypothesis attached to a maximal type-P
subgroup. -/
noncomputable abbrev ftType345PrimeDade
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    PrimeDadeHypothesis (⊤ : Subgroup Gamma) M (derivedWithin M)
      (FTcore M) (FTsupport M) (FTsupport0 M) W W₁ W₂ defW :=
  FT_prDade_hyp defW hmaxM MtypeP

/-- The canonical cyclic-TI isometry on the ambient group. -/
noncomputable abbrev ftType345IsoG
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    CyclicTIIsometryData (k := ℂ)
      (ftType345PrimeDade hmaxM MtypeP).prDade_cycTI :=
  (ftType345PrimeDade hmaxM MtypeP).prDade_cycTI.cyclicTIIsometryData

/-- The source prime-TI rectangle character `mu2_ i j`. -/
noncomputable abbrev ftType345Mu2
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) : ClassFunction M ℂ :=
  (ftType345PrimeTI MtypeP).primeTICharacter
    (ftType345IsoM MtypeP) i j

/-- The sign of a column in the source prime-TI rectangle. -/
noncomputable abbrev ftType345Sign
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) : ℤ :=
  (ftType345PrimeTI MtypeP).primeTISign
    (ftType345IsoM MtypeP) j

/-- The ambient cyclic-TI image of a rectangle entry. -/
noncomputable abbrev ftType345Eta
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction (⊤ : Subgroup Gamma) ℂ :=
  (ftType345IsoG hmaxM MtypeP).cyclicTIImage (i, j)

/-- The canonical Dade map used throughout Section 10. -/
noncomputable abbrev ftType345Tau
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma)) :
    ClassFunction M ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup Gamma) ℂ :=
  Dade (FT_Dade0_hyp M hmaxM)

/-- The Lean representative of source index `#1`. -/
noncomputable def FTtype345_jOne
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    IrreducibleCharacter W₂ ℂ := by
  let pti := ftType345PrimeTI MtypeP
  letI : IsCyclic W₂ := pti.fixed_cyclic
  exact Classical.choose
    (IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := ℂ) pti.prime_cycTIhyp.one_lt_card_right)

theorem FTtype345_jOne_ne_trivial
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    FTtype345_jOne MtypeP ≠
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) := by
  let pti := ftType345PrimeTI MtypeP
  letI : IsCyclic W₂ := pti.fixed_cyclic
  exact Classical.choose_spec
    (IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := ℂ) pti.prime_cycTIhyp.one_lt_card_right)

private theorem secondDerivedInM_eq_commutator_map10
    (M : Subgroup Gamma) :
    (secondDerivedWithin M).subgroupOf M =
      (_root_.commutator (ftType345DerivedInM M)).map
        (ftType345DerivedInM M).subtype := by
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

private instance ftType345DerivedInM_normal10
    (M : Subgroup Gamma) : (ftType345DerivedInM M).Normal :=
  TypeSpecInternal.derivedWithin_normal16 M

private instance ftType345SecondDerivedInM_normal10
    (M : Subgroup Gamma) :
    ((secondDerivedWithin M).subgroupOf M).Normal := by
  let K : Subgroup M := ftType345DerivedInM M
  letI : K.Normal := ftType345DerivedInM_normal10 M
  rw [secondDerivedInM_eq_commutator_map10 M]
  infer_instance

/-! ## The derived quotient is Frobenius -/

private theorem primeTI_centralizerWithin_subgroupOf_zpowers10
    {L K W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (h : PrimeTIHypothesis L K W W₁ W₂ defW)
    (x : L) (hxW₁ : x ∈ W₁.subgroupOf L) (hx : x ≠ 1) :
    centralizerWithin (K.subgroupOf L) (Subgroup.zpowers x) =
      W₂.subgroupOf L := by
  let x₁ : W₁ := ⟨(x : Gamma), hxW₁⟩
  have hx₁ : x₁ ≠ 1 := by
    intro hx₁one
    apply hx
    apply Subtype.ext
    simpa only [x₁, Subgroup.coe_one] using
      congrArg Subtype.val hx₁one
  have hcent := h.centralizer_kernel x₁ hx₁
  ext z
  constructor
  · intro hz
    have hzGamma :
        (z : Gamma) ∈
          centralizerWithin K (Subgroup.zpowers (x : Gamma)) := by
      refine ⟨hz.1, ?_⟩
      intro y hy
      have hyMap : y ∈ (Subgroup.zpowers x).map L.subtype := by
        rwa [MonoidHom.map_zpowers]
      rcases hyMap with ⟨yL, hyL, rfl⟩
      exact congrArg Subtype.val (hz.2 yL hyL)
    rw [hcent] at hzGamma
    exact hzGamma
  · intro hz
    have hzGamma :
        (z : Gamma) ∈
          centralizerWithin K (Subgroup.zpowers (x : Gamma)) := by
      rw [hcent]
      exact hz
    refine ⟨hzGamma.1, ?_⟩
    intro y hy
    apply Subtype.ext
    apply hzGamma.2 (y : Gamma)
    change (y : Gamma) ∈ Subgroup.zpowers (L.subtype x)
    rw [← MonoidHom.map_zpowers]
    exact Subgroup.mem_map_of_mem L.subtype hy

private theorem primeTI_frobenius_quotient_of_fixed_le10
    {L K W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (h : PrimeTIHypothesis L K W W₁ W₂ defW)
    (D : Subgroup L) [D.Normal]
    (hDK : D < K.subgroupOf L)
    (hW₂D : W₂.subgroupOf L ≤ D) :
    IsFrobeniusDecomposition
      ((K.subgroupOf L).map (QuotientGroup.mk' D))
      ((W₁.subgroupOf L).map (QuotientGroup.mk' D)) := by
  classical
  let KL : Subgroup L := K.subgroupOf L
  let RL : Subgroup L := W₁.subgroupOf L
  let q : L →* L ⧸ D := QuotientGroup.mk' D
  let Kq : Subgroup (L ⧸ D) := KL.map q
  let Rq : Subgroup (L ⧸ D) := RL.map q
  letI : KL.Normal := h.kernel_normal
  letI : Kq.Normal :=
    Subgroup.Normal.map (inferInstance : KL.Normal) q
      (QuotientGroup.mk'_surjective D)
  have hDleK : D ≤ KL := hDK.le
  have hcomp : Kq.IsComplement' Rq := by
    simpa only [Kq, Rq, KL, RL, q] using
      h.semidirect_complement.quotient_isComplement hDleK
  have hKqne : Kq ≠ ⊥ := by
    simpa only [Kq, KL, q] using
      (IsFrobeniusDecomposition.quotient_kernel_ne_bot hDK)
  have hRLne : RL ≠ ⊥ := by
    intro hbot
    apply h.complement_ne_bot
    apply le_bot_iff.mp
    intro r hr
    let rL : L := ⟨r, h.complement_le_group hr⟩
    have hrL : rL ∈ RL := hr
    rw [hbot] at hrL
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subgroup.mem_bot.mp hrL))
  have hRqne : Rq ≠ ⊥ := by
    simpa only [Rq, RL, q] using
      h.semidirect_complement.quotient_right_ne_bot hDleK hRLne
  have hfixed : ∀ r : Rq, r ≠ 1 → ∀ k : Kq,
      (r : L ⧸ D) * (k : L ⧸ D) * (r : L ⧸ D)⁻¹ =
        (k : L ⧸ D) → k = 1 := by
    intro r hr k hk
    rcases r.property with ⟨r₀, hr₀, hrEq⟩
    let rL : RL := ⟨r₀, hr₀⟩
    have hrLne : rL ≠ 1 := by
      intro hrOne
      apply hr
      apply Subtype.ext
      rw [← hrEq]
      have hr₀one : r₀ = 1 := congrArg Subtype.val hrOne
      rw [hr₀one, map_one]
      rfl
    have hcentL :
        centralizerWithin KL (Subgroup.zpowers (rL : L)) =
          W₂.subgroupOf L := by
      have hrLne' : (rL : L) ≠ 1 := by
        intro hrOne
        exact hrLne (Subtype.ext hrOne)
      simpa only [KL, RL] using
        primeTI_centralizerWithin_subgroupOf_zpowers10 h
          (rL : L) rL.property hrLne'
    let Rr : Subgroup L := Subgroup.zpowers (rL : L)
    letI : IsSolvable Rr := inferInstance
    have hRrRL : Rr ≤ RL := by
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact RL.zpow_mem rL.property n
    have hcopKL : Nat.Coprime (Nat.card KL) (Nat.card RL) := by
      simpa only [KL, RL,
        MathlibSupport.natCard_subgroupOf_eq h.kernel_le_group,
        MathlibSupport.natCard_subgroupOf_eq h.complement_le_group] using
          h.kernel_complement_card_coprime
    have hcopDRr : Nat.Coprime (Nat.card D) (Nat.card Rr) :=
      (hcopKL.coprime_dvd_left
          (Subgroup.card_dvd_of_le hDleK)).coprime_dvd_right
        (Subgroup.card_dvd_of_le hRrRL)
    have hcentMap :=
      map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
        (N := D) (Y := KL) (R := Rr) hDleK hcopDRr
    have hcentBot :
        centralizerWithin Kq (Subgroup.zpowers (r : L ⧸ D)) = ⊥ := by
      calc
        centralizerWithin Kq (Subgroup.zpowers (r : L ⧸ D)) =
            centralizerWithin Kq (Rr.map q) := by
          dsimp only [Rr]
          rw [MonoidHom.map_zpowers, hrEq]
        _ = (centralizerWithin KL Rr).map q := hcentMap.symm
        _ = (W₂.subgroupOf L).map q := by rw [hcentL]
        _ = ⊥ := by
          apply (Subgroup.map_eq_bot_iff _).mpr
          simpa only [q, QuotientGroup.ker_mk'] using hW₂D
    have hrk : Commute (r : L ⧸ D) (k : L ⧸ D) := by
      rw [commute_iff_eq]
      calc
        (r : L ⧸ D) * (k : L ⧸ D) =
            ((r : L ⧸ D) * (k : L ⧸ D) *
                (r : L ⧸ D)⁻¹) * (r : L ⧸ D) := by group
        _ = (k : L ⧸ D) * (r : L ⧸ D) := by rw [hk]
    have hkcent :
        (k : L ⧸ D) ∈ centralizerWithin Kq
          (Subgroup.zpowers (r : L ⧸ D)) := by
      refine ⟨k.property, ?_⟩
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hrk.zpow_left n).eq
    rw [hcentBot] at hkcent
    exact Subtype.ext (Subgroup.mem_bot.mp hkcent)
  exact
    { isComplement := hcomp
      kernel_normal := inferInstance
      kernel_ne_bot := hKqne
      complement_ne_bot := hRqne
      fixedPointFree := hfixed }

/-- The type-P quotient `M' / M''`, with the image of `W₁` as
complement, is a Frobenius group. -/
theorem ftType345_derived_quotient_frobenius
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    let D := (secondDerivedWithin M).subgroupOf M
    IsFrobeniusDecomposition
      ((ftType345DerivedInM M).map (QuotientGroup.mk' D))
      ((W₁.subgroupOf M).map (QuotientGroup.mk' D)) := by
  classical
  let K : Subgroup M := ftType345DerivedInM M
  let D : Subgroup M := (secondDerivedWithin M).subgroupOf M
  let pti := ftType345PrimeTI MtypeP
  letI : K.Normal := ftType345DerivedInM_normal10 M
  have hKne : K ≠ ⊥ := by
    intro hKbot
    apply pti.fixed_ne_bot
    apply le_bot_iff.mp
    intro x hx
    let xM : M := ⟨x, pti.kernel_le_group (pti.fixed_le_kernel hx)⟩
    have hxK : xM ∈ K := pti.fixed_le_kernel hx
    rw [hKbot] at hxK
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subgroup.mem_bot.mp hxK))
  letI : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hKne
  letI : IsSolvable M := of_typeP_sol M U W W₁ W₂ defW MtypeP
  letI : IsSolvable K := inferInstance
  have hDeq : D = (_root_.commutator K).map K.subtype := by
    simpa only [D, K] using secondDerivedInM_eq_commutator_map10 M
  have hDK : D < K := by
    rw [hDeq]
    have hcomm : _root_.commutator K < (⊤ : Subgroup K) :=
      IsSolvable.commutator_lt_top_of_nontrivial K
    have hmap :=
      (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).2 hcomm
    simpa only [← MonoidHom.range_eq_map, K.range_subtype] using hmap
  letI : D.Normal := ftType345SecondDerivedInM_normal10 M
  have hW₂D : W₂.subgroupOf M ≤ D := by
    intro x hx
    change (x : Gamma) ∈ secondDerivedWithin M
    exact MtypeP.2.2.2.1.2.2.2.1 hx
  exact primeTI_frobenius_quotient_of_fixed_le10 pti D hDK hW₂D

/-! ## Irreducible characters through quotient maps -/

private theorem representation_irreducible_comp_surjective10
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

private noncomputable def IrreducibleCharacter.comapSurjective10
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
    representation_irreducible_comp_surjective10
      chi.representation.ρ f hf
  letI : CategoryTheory.Simple (FDRep.of rho) :=
    simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep (FDRep.of rho)

@[simp]
private theorem IrreducibleCharacter.comapSurjective10_apply
    {A B : Type} [Group A] [Fintype A] [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) (a : A) :
    IrreducibleCharacter.comapSurjective10 f hf chi a = chi (f a) := by
  simp only [IrreducibleCharacter.comapSurjective10,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character (f a) = chi (f a)
  exact chi.representation_character (f a)

private noncomputable def IrreducibleCharacter.quotientDescend10
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
private theorem IrreducibleCharacter.quotientDescend10_mk_apply
    {A : Type} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal]
    (chi : IrreducibleCharacter A ℂ)
    (hN : N ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) (a : A) :
    IrreducibleCharacter.quotientDescend10 N chi hN
        (QuotientGroup.mk' N a) = chi a := by
  simp only [IrreducibleCharacter.quotientDescend10,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character a = chi a
  exact chi.representation_character a

private theorem commutator_le_translationKernel_of_isLinear10
    {A : Type} [Group A] [Fintype A]
    (chi : IrreducibleCharacter A ℂ)
    (hlinear : pTypeIsLinearCharacter chi) :
    _root_.commutator A ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ) := by
  let rho : Representation ℂ A chi.representation :=
    chi.representation.ρ
  have hfinrank : Module.finrank ℂ chi.representation = 1 := hlinear
  let f : A →* chi.representation ≃ₗ[ℂ] chi.representation :=
    representationLinearEquivHom rho
  have hcomm : _root_.commutator A ≤ f.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro z ⟨x, y, rfl⟩
    change f ⁅x, y⁆ = 1
    rw [map_commutatorElement,
      commutatorElement_eq_one_iff_commute, commute_iff_eq]
    apply LinearEquiv.toLinearMap_injective
    exact (endomorphisms_commute_of_finrank_eq_one hfinrank
      (rho x) (rho y)).eq
  rw [ClassFunction.translationKernel_irreducibleCharacter]
  intro a ha
  rw [MonoidHom.mem_ker]
  have haOne := MonoidHom.mem_ker.mp (hcomm ha)
  apply LinearMap.ext
  intro v
  exact DFunLike.congr_fun haOne v

private theorem irreducible_induce_of_derived_quotient_frobenius
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
    IrreducibleCharacter.quotientDescend10
      (N.subgroupOf K) theta hNtheta
  let thetaBar : IrreducibleCharacter Kq ℂ :=
    IrreducibleCharacter.comapSurjective10
      eK.symm.toMonoidHom eK.symm.surjective thetaQ
  have hthetaBar : thetaBar ≠ IrreducibleCharacter.trivial := by
    intro htriv
    have hthetaTriv : theta = IrreducibleCharacter.trivial := by
      ext x
      calc
        theta x = thetaQ (QuotientGroup.mk' (N.subgroupOf K) x) := by
          rw [IrreducibleCharacter.quotientDescend10_mk_apply]
        _ = thetaBar (eK (QuotientGroup.mk' (N.subgroupOf K) x)) := by
          rw [IrreducibleCharacter.comapSurjective10_apply]
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
    IrreducibleCharacter.comapSurjective10 q
      (QuotientGroup.mk'_surjective N) chiQ
  refine ⟨chi.representation, chi.representation_simple, ?_⟩
  have hthetaInflate :
      ClassFunction.inflate (N.subgroupOf K)
          (thetaQ : ClassFunction (K ⧸ N.subgroupOf K) ℂ) =
        (theta : ClassFunction K ℂ) := by
    ext x
    exact IrreducibleCharacter.quotientDescend10_mk_apply
      (N.subgroupOf K) theta hNtheta x
  have hthetaBarClass :
      (thetaBar : ClassFunction Kq ℂ) =
        ClassFunction.subgroupQuotientToImage N K hNK
          (thetaQ : ClassFunction _ ℂ) := by
    ext y
    simp only [thetaBar,
      IrreducibleCharacter.comapSurjective10_apply,
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
        IrreducibleCharacter.comapSurjective10_apply]
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

end FTType345ConstantsInternal

open FTType345ConstantsInternal

/-! ## The three constants -/

/-- Coq `FTtype345_TIirr_degree`. -/
def FTtype345_TIirr_degree
    (MtypeP : of_typeP M U W W₁ W₂ defW) : ℕ :=
  Module.finrank ℂ
    ((ftType345PrimeTI MtypeP).primeTIIndex
      (ftType345IsoM MtypeP)
      ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ),
        FTtype345_jOne MtypeP)).representation

/-- Coq `FTtype345_TIsign`. -/
def FTtype345_TIsign
    (MtypeP : of_typeP M U W W₁ W₂ defW) : ℤ :=
  ftType345Sign MtypeP (FTtype345_jOne MtypeP)

/-- Coq `FTtype345_ratio = (d - delta) / |W₁|`. -/
def FTtype345_ratio
    (MtypeP : of_typeP M U W W₁ W₂ defW) : ℂ :=
  ((FTtype345_TIirr_degree MtypeP : ℂ) -
      (FTtype345_TIsign MtypeP : ℂ)) /
    (Nat.card W₁ : ℂ)

/-- The three clauses of the reference-character conclusion (10.2). -/
structure FTType345ReferenceChoice
    (M W₁ : Subgroup Gamma) (zeta : ClassFunction M ℂ) : Prop where
  irreducible : IsIrreducibleCharacter M ℂ zeta
  mem_calS : zeta ∈ ftType345InducedFamily10 M
  degree : zeta 1 = (Nat.card W₁ : ℂ)

/-- The four clauses in Peterfalvi (10.3). -/
structure FTType345Constants
    (MtypeP : of_typeP M U W W₁ W₂ defW) : Prop where
  degree_constant :
    ∀ (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ),
      j ≠ IrreducibleCharacter.trivial →
        ftType345Mu2 MtypeP i j 1 =
          (FTtype345_TIirr_degree MtypeP : ℂ)
  sign_constant :
    ∀ j : IrreducibleCharacter W₂ ℂ,
      j ≠ IrreducibleCharacter.trivial →
        ftType345Sign MtypeP j = FTtype345_TIsign MtypeP
  degree_gt_one : 1 < FTtype345_TIirr_degree MtypeP
  ratio_natural : ∃ n : ℕ, FTtype345_ratio MtypeP = (n : ℂ)

/-! ## Peterfalvi (10.2)--(10.3) -/

/-- `PFsection10.v: FTtypeP_ref_irr`, Peterfalvi (10.2). -/
theorem FTtypeP_ref_irr
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    ∃ zeta : ClassFunction M ℂ,
      FTType345ReferenceChoice M W₁ zeta := by
  classical
  let K : Subgroup M := ftType345DerivedInM M
  let D : Subgroup M := (secondDerivedWithin M).subgroupOf M
  letI : K.Normal := ftType345DerivedInM_normal10 M
  letI : D.Normal := ftType345SecondDerivedInM_normal10 M
  letI : IsSolvable M := of_typeP_sol M U W W₁ W₂ defW MtypeP
  letI : IsSolvable K := inferInstance
  let pti := ftType345PrimeTI MtypeP
  have hKne : K ≠ ⊥ := by
    intro hKbot
    apply pti.fixed_ne_bot
    apply le_bot_iff.mp
    intro x hx
    let xM : M := ⟨x, pti.kernel_le_group (pti.fixed_le_kernel hx)⟩
    have hxK : xM ∈ K := pti.fixed_le_kernel hx
    rw [hKbot] at hxK
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subgroup.mem_bot.mp hxK))
  letI : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hKne
  have hDltK : D < K := by
    have hDeq : D = (_root_.commutator K).map K.subtype := by
      simpa only [D, K] using secondDerivedInM_eq_commutator_map10 M
    rw [hDeq]
    have hcomm : _root_.commutator K < (⊤ : Subgroup K) :=
      IsSolvable.commutator_lt_top_of_nontrivial K
    have hmap :=
      (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).2 hcomm
    simpa only [← MonoidHom.range_eq_map, K.range_subtype] using hmap
  obtain ⟨phi, hphiMem, hphiDegree⟩ :=
    exists_linInd K (⊥ : Subgroup K) (bot_lt_iff_ne_bot.mpr top_ne_bot)
  obtain ⟨theta, hthetaNe, hphiInd⟩ :=
    (seqIndC1P (k := ℂ) K).mp hphiMem
  have hthetaOne : theta 1 = 1 := by
    have hindexNe : (K.index : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr K.index_ne_zero_of_finite
    apply mul_left_cancel₀ hindexNe
    calc
      (K.index : ℂ) * theta 1 =
          (ClassFunction.induce K (theta : ClassFunction K ℂ)) 1 := by
        rw [ClassFunction.induce_one]
      _ = phi 1 := congrArg (fun f : ClassFunction M ℂ ↦ f 1) hphiInd.symm
      _ = (K.index : ℂ) := hphiDegree
      _ = (K.index : ℂ) * 1 := by simp
  have hlinear : pTypeIsLinearCharacter theta := by
    change Module.finrank ℂ theta.representation = 1
    apply Nat.cast_injective (R := ℂ)
    simpa only [Nat.cast_one, IrreducibleCharacter.apply_one_eq_finrank]
      using hthetaOne
  have hDsubK : D.subgroupOf K = _root_.commutator K := by
    have hDeq : D = (_root_.commutator K).map K.subtype := by
      simpa only [D, K] using secondDerivedInM_eq_commutator_map10 M
    rw [hDeq]
    exact Subgroup.comap_map_eq_self_of_injective
      K.subtype_injective (_root_.commutator K)
  have hDtheta : D.subgroupOf K ≤
      ClassFunction.translationKernel (theta : ClassFunction K ℂ) := by
    rw [hDsubK]
    exact commutator_le_translationKernel_of_isLinear10 theta hlinear
  have hthetaTop : ¬(⊤ : Subgroup K) ≤
      ClassFunction.translationKernel (theta : ClassFunction K ℂ) :=
    (mem_Iirr_kerD.mp ((mem_Iirr_ker1 theta).mpr hthetaNe)).2
  have hFrob := ftType345_derived_quotient_frobenius MtypeP
  have hphiIrr : IsIrreducibleCharacter M ℂ phi := by
    rw [hphiInd]
    exact irreducible_induce_of_derived_quotient_frobenius
      K D hDltK.le hFrob theta hDtheta hthetaTop
  have hindex : K.index = Nat.card W₁ := by
    have houter : IsInternalSemidirectProductIn
        (derivedWithin M) W₁ M := MtypeP.1.2.2.2
    calc
      K.index = Nat.card (W₁.subgroupOf M) :=
        houter.2.2.2.symm.index_eq_card
      _ = Nat.card W₁ := MathlibSupport.natCard_subgroupOf_eq houter.2.1
  refine ⟨phi, hphiIrr, hphiMem, ?_⟩
  rw [hphiDegree, hindex]

/-- `PFsection10.v: FTtype345_core_prime`, the first assertion of (10.3). -/
theorem FTtype345_core_prime
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2) :
    (Nat.card W₂).Prime := by
  obtain ⟨S, pairMS, xdefW, V, StypeP⟩ :=
    FTtypeP_pair_witness defW hmaxM MtypeP
  have hStype2 : FTtype S = 2 := by
    rcases pairMS.one_type_two with hM2 | hS2
    · exact (notMtype2 hM2).elim
    · exact hS2
  exact (compl_of_typeII S V W W₂ W₁ xdefW
    pairMS.T_maximal StypeP hStype2).1.2.2.1

private theorem ftType345_nontrivial_column_invariant
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    ftType345Mu2 MtypeP
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j 1 =
        (FTtype345_TIirr_degree MtypeP : ℂ) ∧
      ftType345Sign MtypeP j = FTtype345_TIsign MtypeP := by
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  have hp := FTtype345_core_prime hmaxM MtypeP notMtype2
  obtain ⟨nu, hnu⟩ :=
    exists_prime_cyclic_irreducible_algEquiv
      hp pti.fixed_cyclic
      (FTtype345_jOne MtypeP) (FTtype345_jOne_ne_trivial MtypeP)
      j hj
  have hindex := pti.primeTIIndex_mapRingEquiv isoM nu.toRingEquiv
    (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
    (FTtype345_jOne MtypeP)
  have hsign := pti.primeTISign_mapRingEquiv isoM nu.toRingEquiv
    (FTtype345_jOne MtypeP)
  rw [IrreducibleCharacter.mapRingEquiv_trivial] at hindex
  rw [hnu] at hindex hsign
  constructor
  · have hvalue := congrArg
        (fun chi : IrreducibleCharacter M ℂ ↦ chi 1) hindex
    change pti.primeTIIndex isoM
        ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ), j) 1 =
      (Module.finrank ℂ
        (pti.primeTIIndex isoM
          ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ),
            FTtype345_jOne MtypeP)).representation : ℂ)
    simpa only [IrreducibleCharacter.mapRingEquiv_apply,
      IrreducibleCharacter.apply_one_eq_finrank, map_natCast] using hvalue
  · exact hsign

private theorem irreducibleCharacter_finrank_pos10
    {A : Type} [Group A] [Fintype A]
    (chi : IrreducibleCharacter A ℂ) :
    0 < Module.finrank ℂ chi.representation := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero chi.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  exact Module.finrank_pos

private theorem ratio_natural_of_integral_mod_sign10
    {m d : ℕ} {delta : ℤ}
    (hm : 0 < m) (hd : 1 < d) (hsign : IsSign delta)
    (hmod : IsIntegralModEq (m : ℂ) (d : ℂ) (delta : ℂ)) :
    ∃ n : ℕ, (((d : ℂ) - (delta : ℂ)) / (m : ℂ)) = (n : ℂ) := by
  obtain ⟨z, hzInt, hz⟩ := hmod
  let q : ℚ := ((d : ℚ) - (delta : ℚ)) / (m : ℚ)
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hqz : (q : ℂ) = z := by
    apply mul_right_cancel₀ hmC
    change (q : ℂ) * (m : ℂ) = z * (m : ℂ)
    have hz' : (d : ℂ) - (delta : ℂ) = (m : ℂ) * z := hz
    have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have hqmulQ : q * (m : ℚ) = (d : ℚ) - (delta : ℚ) := by
      dsimp only [q]
      exact div_mul_cancel₀ _ hmQ
    calc
      (q : ℂ) * (m : ℂ) =
          (((d : ℚ) - (delta : ℚ) : ℚ) : ℂ) := by
        exact_mod_cast hqmulQ
      _ = (d : ℂ) - (delta : ℂ) := by norm_num
      _ = z * (m : ℂ) := by rw [hz', mul_comm]
  have hqIntC : IsIntegral ℤ (q : ℂ) := hqz ▸ hzInt
  have hqInt : IsIntegral ℤ q := IsIntegral.ratCast_iff.mp hqIntC
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqInt
  have hqNonneg : 0 ≤ q := by
    dsimp only [q]
    have hdQ : (1 : ℚ) < (d : ℚ) := by exact_mod_cast hd
    have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
    rcases hsign with hdelta | hdelta
    · rw [hdelta]
      apply div_nonneg
      · simpa using (sub_nonneg.mpr hdQ.le)
      · exact hmQ.le
    · rw [hdelta]
      apply div_nonneg
      · have hdNonneg : (0 : ℚ) ≤ (d : ℚ) := by positivity
        simpa using add_nonneg hdNonneg (zero_le_one : (0 : ℚ) ≤ 1)
      · exact hmQ.le
  have haNonneg : 0 ≤ a := by
    have ha' : (a : ℚ) = q := ha
    have haQ : (0 : ℚ) ≤ (a : ℚ) := by
      rw [ha']
      exact hqNonneg
    exact_mod_cast haQ
  refine ⟨a.toNat, ?_⟩
  have hqa : q = (a : ℚ) := ha.symm
  calc
    ((d : ℂ) - (delta : ℂ)) / (m : ℂ) = (q : ℂ) := by
      norm_num [q]
    _ = (a : ℂ) := by rw [hqa]; rfl
    _ = (a.toNat : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg haNonneg).symm

/-- `PFsection10.v: FTtype345_constants`, the remainder of (10.3). -/
theorem FTtype345_constants
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2) :
    FTType345Constants MtypeP := by
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  have hdist := FTtype345_jOne_ne_trivial MtypeP
  have hinv (j : IrreducibleCharacter W₂ ℂ)
      (hj : j ≠ IrreducibleCharacter.trivial) :=
    ftType345_nontrivial_column_invariant
      hmaxM MtypeP notMtype2 j hj
  have hdgt : 1 < FTtype345_TIirr_degree MtypeP := by
    by_contra hnot
    have hle : FTtype345_TIirr_degree MtypeP ≤ 1 := Nat.not_lt.mp hnot
    have hpos : 0 < FTtype345_TIirr_degree MtypeP := by
      exact irreducibleCharacter_finrank_pos10
        (pti.primeTIIndex isoM
          (IrreducibleCharacter.trivial, FTtype345_jOne MtypeP))
    have hone : FTtype345_TIirr_degree MtypeP = 1 := by omega
    let chi := pti.primeTIIndex isoM
      ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ),
        FTtype345_jOne MtypeP)
    have hlinear : pTypeIsLinearCharacter chi := by
      simpa only [pTypeIsLinearCharacter, pTypeIrreducibleDegree,
        chi, FTtype345_TIirr_degree] using hone
    have hker : (derivedWithin M).subgroupOf M ≤
        ClassFunction.translationKernel (chi : ClassFunction M ℂ) := by
      have hcomm :=
        commutator_le_translationKernel_of_isLinear10 chi hlinear
      have hderived :
          (derivedWithin M).subgroupOf M = _root_.commutator M := by
        change ((_root_.commutator M).map M.subtype).comap M.subtype =
          _root_.commutator M
        exact Subgroup.comap_map_eq_self_of_injective
          M.subtype_injective (_root_.commutator M)
      rw [hderived]
      exact hcomm
    obtain ⟨i, hi⟩ := (pti.prTIirr0P isoM chi).2 hker
    have hpair :
        (i, (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) =
          ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ),
            FTtype345_jOne MtypeP) := by
      apply (pti.primeTIirr_spec isoM).1
      exact hi.symm
    exact hdist (congrArg Prod.snd hpair).symm
  have hdegreeConstant :
      ∀ (i : IrreducibleCharacter W₁ ℂ)
        (j : IrreducibleCharacter W₂ ℂ),
        j ≠ IrreducibleCharacter.trivial →
          ftType345Mu2 MtypeP i j 1 =
            (FTtype345_TIirr_degree MtypeP : ℂ) := by
    intro i j hj
    calc
      ftType345Mu2 MtypeP i j 1 =
          ftType345Mu2 MtypeP IrreducibleCharacter.trivial j 1 :=
        pti.prTIirr_1 isoM i j
      _ = (FTtype345_TIirr_degree MtypeP : ℂ) := (hinv j hj).1
  have hsignConstant :
      ∀ j : IrreducibleCharacter W₂ ℂ,
        j ≠ IrreducibleCharacter.trivial →
          ftType345Sign MtypeP j = FTtype345_TIsign MtypeP := by
    intro j hj
    exact (hinv j hj).2
  have hratioNatural :
      ∃ n : ℕ, FTtype345_ratio MtypeP = (n : ℂ) := by
    have hmod := pti.primeTICharacter_one_mod_card_left isoM
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
      (FTtype345_jOne MtypeP)
    have hdegree :
        pti.primeTICharacter isoM
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
            (FTtype345_jOne MtypeP) 1 =
          (FTtype345_TIirr_degree MtypeP : ℂ) := by
      rw [pti.primeTICharacter_apply,
        IrreducibleCharacter.apply_one_eq_finrank]
      rfl
    have hmod' : IsIntegralModEq (Nat.card W₁ : ℂ)
        (FTtype345_TIirr_degree MtypeP : ℂ)
        (FTtype345_TIsign MtypeP : ℂ) := by
      change IsIntegralModEq (Nat.card W₁ : ℂ)
        (FTtype345_TIirr_degree MtypeP : ℂ)
        (pti.primeTISign isoM (FTtype345_jOne MtypeP) : ℂ)
      rw [← hdegree]
      exact hmod
    have hm : 0 < Nat.card W₁ := Nat.card_pos
    simpa only [FTtype345_ratio, FTtype345_TIsign, ftType345Sign] using
      ratio_natural_of_integral_mod_sign10 hm hdgt
        (pti.primeTISign_isSign isoM (FTtype345_jOne MtypeP)) hmod'
  exact
    { degree_constant := hdegreeConstant
      sign_constant := hsignConstant
      degree_gt_one := hdgt
      ratio_natural := hratioNatural }

end

end Submission.OddOrder.PF
