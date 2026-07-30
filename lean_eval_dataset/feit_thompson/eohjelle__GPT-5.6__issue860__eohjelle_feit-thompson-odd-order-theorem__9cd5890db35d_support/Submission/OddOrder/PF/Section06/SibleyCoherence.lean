import Submission.OddOrder.BG.Section03.FrobeniusQuotient
import Submission.OddOrder.BG.Section03.FrobeniusSolvableKernel
import Submission.OddOrder.PF.Section01.CharacterCompleteness
import Submission.OddOrder.PF.Section01.IrreducibleCharacterTransport
import Submission.OddOrder.PF.Section01.QuotientSubgroupAdapter
import Submission.OddOrder.PF.Section01.VirtualCharacterInduction
import Submission.OddOrder.PF.Section01.VirtualCharacterPullback
import Submission.OddOrder.PF.Section02.DadeRestriction
import Submission.OddOrder.PF.Section03.NormalizedTICharacterPairing
import Submission.OddOrder.PF.Section04.PrimeTIQuotient
import Submission.OddOrder.PF.Section05.CoherenceExtension
import Submission.OddOrder.PF.Section05.DadeAutomorphismCoherence
import Submission.OddOrder.PF.Section05.SubcoherentConstruction
import Submission.OddOrder.PF.Section06.BoundedSeqIndCoherence
import Submission.OddOrder.PF.Section06.CaseAAlignment
import Submission.OddOrder.PF.Section06.CaseBPivot
import Submission.OddOrder.PF.Section06.CentralRestrictionClifford
import Submission.OddOrder.PF.Section06.ConstantIrrModTISylow
import Submission.OddOrder.PF.Section06.FrobeniusKernelInduction
import Submission.OddOrder.PF.Section06.NormalizedTISylowAdapters
import Submission.OddOrder.PF.Section06.OddFrobeniusIndexBound
import Submission.OddOrder.PF.Section06.OddFrobeniusQuotient

/-!
# Sibley's coherence theorem

This file ports Peterfalvi's Theorem (6.8), `Sibley_coherence`, from
`PFsection6.v`, lines 570--1346.  The two alternatives in the source are
kept explicit: either `L` is Frobenius with kernel `H` and complement `W₁`,
or the same semidirect product occurs in a prime-Dade configuration with a
prime-order subgroup `W₂` in the ambient derived subgroup of `H`.

MathComp's induction map `'Ind[G,L]` is represented by induction through
`L.subgroupOf G`, preceded by the canonical transport of class functions
from `L`.  Similarly, the source family `seqIndD H L H 1` is the Lean family
`seqIndD (H.subgroupOf L) ⊤ ⊥`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical IsMulCommutative Pointwise

universe u

local instance sibleyCoherenceInvertibleCard
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## Source-side notation -/

/-- The ambient copy of the derived subgroup of `H`.

MathComp writes this subgroup as `H^`(1)%G`; Lean's commutator subgroup is a
subgroup of the type `H`, so it is mapped back to the common ambient group.
-/
def ambientCommutator
    {Γ : Type u} [Group Γ] (H : Subgroup Γ) : Subgroup Γ :=
  (_root_.commutator H).map H.subtype

/-- Canonical induction from the ambient subgroup `L` to `G`.

The proof `hLG` identifies the copy `L.subgroupOf G` with `L` before
applying ordinary class-function induction.
-/
def sibleyInduce
    {Γ : Type u} [Group Γ] [Fintype Γ]
    (G L : Subgroup Γ) (hLG : L ≤ G) :
    ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  (ClassFunction.induce (L.subgroupOf G)).comp
    (ClassFunction.toSubgroupOf L G hLG)

/-- Frobenius reciprocity for `sibleyInduce`, with restriction written as
pullback along the literal embedding of `L` in `G`. -/
private theorem sibleyInduce_frobeniusReciprocity
    {Γ : Type u} [Group Γ] [Fintype Γ]
    (G L : Subgroup Γ) (hLG : L ≤ G)
    (f : ClassFunction L ℂ) (g : ClassFunction G ℂ) :
    let LG : Subgroup G := L.subgroupOf G
    let eLG : LG ≃* L := Subgroup.subgroupOfEquivOfLe hLG
    let embed : L →* G :=
      LG.subtype.comp eLG.symm.toMonoidHom
    characterPairing (sibleyInduce G L hLG f) g =
      characterPairing f (ClassFunction.comap embed g) := by
  let LG : Subgroup G := L.subgroupOf G
  let eLG : LG ≃* L := Subgroup.subgroupOfEquivOfLe hLG
  let embed : L →* G :=
    LG.subtype.comp eLG.symm.toMonoidHom
  rw [sibleyInduce, LinearMap.comp_apply,
    ClassFunction.frobeniusReciprocity]
  unfold characterPairing
  rw [MathlibSupport.natCard_subgroupOf_eq hLG]
  congr 1
  rw [← eLG.toEquiv.sum_comp (fun x : L ↦
    f x * ClassFunction.comap embed g x⁻¹)]
  apply Finset.sum_congr rfl
  intro x _
  have hembed :
      embed (eLG x) = (x : G) := by
    change ((eLG.symm (eLG x) : LG) : G) = (x : G)
    exact congrArg (fun y : LG ↦ (y : G))
      (eLG.symm_apply_apply x)
  simp only [ClassFunction.toSubgroupOf_apply,
    ClassFunction.restrict_apply, ClassFunction.comap_apply,
    map_inv]
  change f (eLG x) * g (x : G)⁻¹ =
    f (eLG x) * g (embed (eLG x))⁻¹
  rw [hembed]

/-- The family denoted `seqIndD H L H 1` in the source. -/
def sibleyFamily
    {Γ : Type u} [Group Γ] [Fintype Γ]
    (L H : Subgroup Γ) : Finset (ClassFunction L ℂ) :=
  seqIndD (H.subgroupOf L) (⊤ : Subgroup (H.subgroupOf L)) ⊥

/-- The two structural alternatives in Peterfalvi (6.8)(c).

In the second branch the existential proof of the internal direct product
is kept under the same binder as the dependent prime-Dade hypothesis, just
as `exists defW : W1 \x W2 = W` is in the Coq statement.
-/
def SibleyStructuralAlternative
    {Γ : Type u} [Group Γ] [Fintype Γ]
    (G L H W₁ : Subgroup Γ) : Prop :=
  IsFrobeniusDecomposition (H.subgroupOf L) (W₁.subgroupOf L) ∨
    ∃ W₂ : Subgroup Γ,
      Nat.Prime (Nat.card W₂) ∧ W₂ ≤ ambientCommutator H ∧
        ∃ (A₀ : Set Γ) (W : Subgroup Γ)
            (defW : IsInternalDirectProductIn W₁ W₂ W),
          PrimeDadeHypothesis G L H H (subgroupNonidentity H)
            A₀ W W₁ W₂ defW

/-- On the smaller normalized-TI set in a prime-Dade package, the packaged
Dade map is ordinary induction.  The source uses Dade induction after
restricting the Dade hypothesis to this subset. -/
private theorem PrimeDadeHypothesis.Dade_Ind_on_smallSet
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {G L K H W W₁ W₂ : Subgroup Gamma}
    {A A₀ : Set Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (hTI : IsNormalizedTI A G L)
    (phi : ClassFunction L ℂ)
    (hphi : phi ∈
      ClassFunction.supportedOn {x : L | (x : Gamma) ∈ A}) :
    Dade pd.prDade_hyp phi =
      ClassFunction.induce (L.subgroupOf G)
        (ClassFunction.toSubgroupOf L G pd.prDade_hyp.2.1 phi) := by
  let hAnorm : L ≤ Subgroup.normalizer A :=
    fun x hx ↦ (hTI.2.1 hx).2
  calc
    Dade pd.prDade_hyp phi =
        restr_Dade pd.prDade_hyp pd.set_subset_dadeSet hAnorm phi :=
      (restr_DadeE pd.prDade_hyp pd.set_subset_dadeSet
        hAnorm phi hphi).symm
    _ = ClassFunction.induce (L.subgroupOf G)
          (ClassFunction.toSubgroupOf L G
            pd.prDade_hyp.2.1 phi) := by
      simpa only [restr_Dade] using
        Dade_Ind
          (restr_Dade_hyp pd.prDade_hyp
            pd.set_subset_dadeSet hAnorm)
          hTI phi hphi

/-! ## Reusable coherence infrastructure -/

/-- Replace the partial map in a subcoherent structure by a map which agrees
with it on the integral source span supported away from the identity.  This
is the structure-level form of the map replacement used in the prime-Dade
branch of the source proof. -/
private theorem subcoherent_congr
    {L₀ G₀ : Type u} [Group L₀] [Fintype L₀]
    [Group G₀] [Fintype G₀]
    {S : Set (ClassFunction L₀ ℂ)}
    {sigma tau : ClassFunction L₀ ℂ →ₗ[ℂ] ClassFunction G₀ ℂ}
    {R : ClassFunction L₀ ℂ → Finset (ClassFunction G₀ ℂ)}
    (hsub : subcoherent S sigma R)
    (heq : ∀ phi ∈ AddSubgroup.closure S,
      phi ∈ ClassFunction.supportedOn (nonidentitySet L₀) →
        sigma phi = tau phi) :
    subcoherent S tau R := by
  have hinverseOff (phi : ClassFunction L₀ ℂ) :
      phi - ClassFunction.inverseLinear phi ∈
        ClassFunction.supportedOn (nonidentitySet L₀) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxone : x = 1 := by
      simpa [nonidentitySet] using not_not.mp hx
    subst x
    simp
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
        rw [← heq phi hphi hphiOff, ← heq psi hpsi hpsiOff]
        exact hsub.tau_isometry phi hphi hphiOff psi hpsi hpsiOff
      tau_virtual := by
        intro phi hphi hphiOff
        rw [← heq phi hphi hphiOff]
        exact hsub.tau_virtual phi hphi hphiOff
      tau_supported := by
        intro phi hphi hphiOff
        rw [← heq phi hphi hphiOff]
        exact hsub.tau_supported phi hphi hphiOff
      pairwise_orthogonal := hsub.pairwise_orthogonal
      image_virtual := hsub.image_virtual
      image_orthonormal := hsub.image_orthonormal
      tau_inverse_sub := by
        intro xi hxi
        let d := xi - ClassFunction.inverseLinear xi
        have hdSpan : d ∈ AddSubgroup.closure S :=
          (AddSubgroup.closure S).sub_mem
            (AddSubgroup.subset_closure hxi)
            (AddSubgroup.subset_closure (hsub.inverse_mem xi hxi))
        have hdOff : d ∈
            ClassFunction.supportedOn (nonidentitySet L₀) :=
          hinverseOff xi
        rw [← heq d hdSpan hdOff]
        exact hsub.tau_inverse_sub xi hxi
      image_orthogonal := hsub.image_orthogonal }

/-- A finite orthogonal projection, in the exact form used twice in the
Sibley calculation.  The residual is orthogonal to the given orthonormal
family. -/
private theorem orthogonal_projection_split
    {Q : Type u} [Group Q] [Fintype Q]
    (T : Finset (ClassFunction Q ℂ))
    (hT : ∀ alpha ∈ T, ∀ beta ∈ T,
      characterPairing alpha beta = if alpha = beta then 1 else 0)
    (phi : ClassFunction Q ℂ) :
    let proj := ∑ alpha ∈ T,
      characterPairing phi alpha • alpha
    ∀ beta ∈ T, characterPairing (phi - proj) beta = 0 := by
  dsimp only
  intro beta hbeta
  rw [show characterPairing
        (phi - ∑ alpha ∈ T, characterPairing phi alpha • alpha) beta =
          characterPairing phi beta -
            characterPairing
              (∑ alpha ∈ T, characterPairing phi alpha • alpha) beta by
        change characterPairingRight beta
            (phi - ∑ alpha ∈ T,
              characterPairing phi alpha • alpha) = _
        exact map_sub (characterPairingRight beta) _ _]
  have hsum :
      characterPairing
          (∑ alpha ∈ T, characterPairing phi alpha • alpha) beta =
        ∑ alpha ∈ T,
          characterPairing
            (characterPairing phi alpha • alpha) beta := by
    change characterPairingRight beta
        (∑ alpha ∈ T, characterPairing phi alpha • alpha) = _
    exact map_sum (characterPairingRight beta)
      (fun alpha ↦ characterPairing phi alpha • alpha) T
  rw [hsum]
  simp_rw [characterPairing_smul_left]
  rw [Finset.sum_eq_single beta]
  · rw [hT beta hbeta beta hbeta, if_pos rfl, mul_one, sub_self]
  · intro alpha halpha hne
    rw [hT alpha halpha beta hbeta, if_neg hne, mul_zero]
  · exact fun h ↦ (h hbeta).elim

/-- The internal centralizer appearing in the prime-TI hypothesis, viewed
inside the subgroup type `L`.  This is the local form needed before passing
to the derived quotient of the kernel. -/
private theorem primeTI_centralizerWithin_subgroupOf_zpowers
    {Gamma : Type u} [Group Gamma]
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
      have hyMap :
          y ∈ (Subgroup.zpowers x).map L.subtype := by
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

/-- In a prime-TI semidirect product, killing a normal subgroup which
contains every complement fixed point makes the quotient a Frobenius
group.  Sibley's application takes that normal subgroup to be the derived
subgroup of the kernel. -/
private theorem primeTI_frobenius_quotient_of_fixed_le
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
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
        primeTI_centralizerWithin_subgroupOf_zpowers h
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
        _ = (W₂.subgroupOf L).map q := by
          rw [hcentL]
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

/-! ## Irreducible characters through quotient maps -/

/-- Irreducibility is unchanged when a representation is pulled back along
a surjective homomorphism. -/
private theorem representation_irreducible_comp_surjective
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

/-- Pull an irreducible character back along a surjective homomorphism. -/
private noncomputable def IrreducibleCharacter.comapSurjective
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
    representation_irreducible_comp_surjective
      chi.representation.ρ f hf
  letI : CategoryTheory.Simple (FDRep.of rho) :=
    simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep (FDRep.of rho)

@[simp]
private theorem IrreducibleCharacter.comapSurjective_apply
    {A B : Type} [Group A] [Fintype A] [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) (a : A) :
    IrreducibleCharacter.comapSurjective f hf chi a = chi (f a) := by
  simp only [IrreducibleCharacter.comapSurjective,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character (f a) = chi (f a)
  exact chi.representation_character (f a)

/-- Induction is unchanged when its subgroup is transported across an
equality. -/
private theorem induce_comapMulEquiv_subgroupCongr
    {A : Type} [Group A] [Fintype A]
    (H K : Subgroup A) (hHK : H = K)
    (chi : IrreducibleCharacter K ℂ) :
    ClassFunction.induce H
        (IrreducibleCharacter.comapMulEquiv
          (MulEquiv.subgroupCongr hHK) chi : ClassFunction H ℂ) =
      ClassFunction.induce K (chi : ClassFunction K ℂ) := by
  subst K
  apply congrArg (ClassFunction.induce H)
  ext x
  rw [IrreducibleCharacter.comapMulEquiv_apply]
  apply congrArg (fun y : H ↦ chi y)
  apply Subtype.ext
  rfl

/-- Descend an irreducible character through a normal subgroup contained in
its translation kernel. -/
private noncomputable def IrreducibleCharacter.quotientDescend
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
private theorem IrreducibleCharacter.quotientDescend_mk_apply
    {A : Type} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal]
    (chi : IrreducibleCharacter A ℂ)
    (hN : N ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) (a : A) :
    IrreducibleCharacter.quotientDescend N chi hN
        (QuotientGroup.mk' N a) = chi a := by
  simp only [IrreducibleCharacter.quotientDescend,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character a = chi a
  exact chi.representation_character a

/-- Pullback along a surjection also reflects irreducibility.  This is the
Lean replacement for the source rewrite `cfMod_irr`: descend the pulled-back
irreducible through the homomorphism kernel, then transport it across the
first-isomorphism equivalence. -/
private theorem irreducible_of_comap_surjective
    {A B : Type} [Group A] [Fintype A] [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (phi : ClassFunction B ℂ)
    (hirr : IsIrreducibleCharacter A ℂ
      (ClassFunction.comap f phi)) :
    IsIrreducibleCharacter B ℂ phi := by
  let chiA : IrreducibleCharacter A ℂ :=
    ⟨ClassFunction.comap f phi, hirr⟩
  let hker : f.ker ≤ ClassFunction.translationKernel
      (chiA : ClassFunction A ℂ) :=
    ClassFunction.ker_le_translationKernel_comap f phi
  let chiQ : IrreducibleCharacter (A ⧸ f.ker) ℂ :=
    IrreducibleCharacter.quotientDescend f.ker chiA hker
  let e : (A ⧸ f.ker) ≃* B :=
    QuotientGroup.quotientKerEquivOfSurjective f hf
  let chiB : IrreducibleCharacter B ℂ :=
    IrreducibleCharacter.comapSurjective
      e.symm.toMonoidHom e.symm.surjective chiQ
  have hchiB : (chiB : ClassFunction B ℂ) = phi := by
    ext b
    obtain ⟨a, rfl⟩ := hf b
    calc
      chiB (f a) = chiQ (e.symm (f a)) := by
        exact IrreducibleCharacter.comapSurjective_apply
          e.symm.toMonoidHom e.symm.surjective chiQ (f a)
      _ = chiQ (QuotientGroup.mk' f.ker a) := by
        have he : e (QuotientGroup.mk' f.ker a) = f a := rfl
        rw [← he, e.symm_apply_apply]
      _ = chiA a := by
        exact IrreducibleCharacter.quotientDescend_mk_apply
          f.ker chiA hker a
      _ = phi (f a) := rfl
  rw [← hchiB]
  exact chiB.property

/-- If an irreducible of `K` factors through a Frobenius quotient of `L`,
then its induction to `L` is irreducible. -/
private theorem irr_induced_of_Frobenius_quotient
    {A : Type} [Group A] [Fintype A]
    (K N : Subgroup A) [K.Normal] [N.Normal]
    (hNK : N ≤ K)
    {E : Subgroup (A ⧸ N)}
    (hFrob : IsFrobeniusDecomposition
      (K.map (QuotientGroup.mk' N)) E)
    (theta : IrreducibleCharacter K ℂ)
    (hNtheta : N.subgroupOf K ≤
      ClassFunction.translationKernel
        (theta : ClassFunction K ℂ))
    (htheta : ¬(⊤ : Subgroup K) ≤
      ClassFunction.translationKernel
        (theta : ClassFunction K ℂ)) :
    IsIrreducibleCharacter A ℂ
      (ClassFunction.induce K (theta : ClassFunction K ℂ)) := by
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  let Kq : Subgroup (A ⧸ N) := K.map q
  let eK : (K ⧸ N.subgroupOf K) ≃* Kq :=
    ClassFunction.subgroupQuotientEquivImage N K hNK
  let thetaQ : IrreducibleCharacter (K ⧸ N.subgroupOf K) ℂ :=
    IrreducibleCharacter.quotientDescend
      (N.subgroupOf K) theta hNtheta
  let thetaBar : IrreducibleCharacter Kq ℂ :=
    IrreducibleCharacter.comapSurjective
      eK.symm.toMonoidHom eK.symm.surjective thetaQ
  have hthetaBar :
      thetaBar ≠ IrreducibleCharacter.trivial := by
    intro htriv
    have hthetaTriv : theta = IrreducibleCharacter.trivial := by
      ext x
      calc
        theta x = thetaQ (QuotientGroup.mk' (N.subgroupOf K) x) := by
          rw [IrreducibleCharacter.quotientDescend_mk_apply]
        _ = thetaBar (eK (QuotientGroup.mk' (N.subgroupOf K) x)) := by
          rw [IrreducibleCharacter.comapSurjective_apply]
          exact congrArg (fun y ↦ thetaQ y)
            (eK.symm_apply_apply _).symm
        _ = IrreducibleCharacter.trivial
            (eK (QuotientGroup.mk' (N.subgroupOf K) x)) := by
          rw [htriv]
        _ = IrreducibleCharacter.trivial x := by simp
    apply htheta
    rw [hthetaTriv]
    intro x _ g
    simp
  let chiQ : IrreducibleCharacter (A ⧸ N) ℂ :=
    ⟨ClassFunction.induce Kq (thetaBar : ClassFunction Kq ℂ),
      irr_induced_Frobenius_ker hFrob thetaBar hthetaBar⟩
  let chi : IrreducibleCharacter A ℂ :=
    IrreducibleCharacter.comapSurjective q
      (QuotientGroup.mk'_surjective N) chiQ
  refine ⟨chi.representation, chi.representation_simple, ?_⟩
  have hthetaInflate :
      ClassFunction.inflate (N.subgroupOf K)
          (thetaQ : ClassFunction (K ⧸ N.subgroupOf K) ℂ) =
        (theta : ClassFunction K ℂ) := by
    ext x
    exact IrreducibleCharacter.quotientDescend_mk_apply
      (N.subgroupOf K) theta hNtheta x
  have hthetaBarClass :
      (thetaBar : ClassFunction Kq ℂ) =
        ClassFunction.subgroupQuotientToImage N K hNK
          (thetaQ : ClassFunction _ ℂ) := by
    ext y
    simp only [thetaBar,
      IrreducibleCharacter.comapSurjective_apply,
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
        IrreducibleCharacter.comapSurjective_apply]
      rfl
    _ = ClassFunction.inflate N
        (ClassFunction.induce Kq
          (thetaBar : ClassFunction Kq ℂ)) := rfl
    _ = ClassFunction.inflate N
        (ClassFunction.induce Kq
          (ClassFunction.subgroupQuotientToImage N K hNK
            (thetaQ : ClassFunction _ ℂ))) := by
      rw [hthetaBarClass]
    _ = ClassFunction.induce K
        (ClassFunction.inflate (N.subgroupOf K)
          (thetaQ : ClassFunction (K ⧸ N.subgroupOf K) ℂ)) := by
      exact hIndMod.symm
    _ = ClassFunction.induce K (theta : ClassFunction K ℂ) := by
      rw [hthetaInflate]

/-- An irreducible character which kills the derived subgroup has degree
one. -/
private theorem irreducible_degree_one_of_commutator_le_kernel
    {A : Type} [Group A] [Fintype A]
    (chi : IrreducibleCharacter A ℂ)
    (hder : _root_.commutator A ≤
      ClassFunction.translationKernel
        (chi : ClassFunction A ℂ)) :
    chi 1 = 1 := by
  let rho := chi.representation.ρ
  have hder' : _root_.commutator A ≤ rho.ker := by
    rw [← ClassFunction.translationKernel_irreducibleCharacter chi]
    exact hder
  let Q := A ⧸ rho.ker
  let sigmaQ : Representation ℂ Q chi.representation :=
    quotientKerRepresentation rho
  let q : A →* Q := QuotientGroup.mk' rho.ker
  letI : IsMulCommutative Q :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hder'
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  letI : Representation.IsIrreducible (sigmaQ.comp q) := by
    change Representation.IsIrreducible rho
    infer_instance
  letI : Representation.IsIrreducible sigmaQ :=
    representation_isIrreducible_of_comp sigmaQ q
  rw [IrreducibleCharacter.apply_one_eq_finrank,
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative sigmaQ]
  norm_num

/-- The quotient image of `H` has the relative index of `N` in `H`.

This elementary cardinality bridge is repeated here because the version
used in the proof of (6.5) is private to `OddFrobeniusQuotient`.  Sibley's
last estimate needs the same identity for the second Frobenius quotient. -/
private theorem relIndex_eq_card_map_quotient_sibley
    {A : Type u} [Group A] [Finite A]
    {N H : Subgroup A} (hNnormal : N.Normal) (hNH : N ≤ H) :
    N.relIndex H = Nat.card (H.map (QuotientGroup.mk' N)) := by
  letI : N.Normal := hNnormal
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  let f : H →* A ⧸ N := q.comp H.subtype
  have hker : f.ker = N.subgroupOf H := by
    ext x
    change q (x : A) = 1 ↔ (x : A) ∈ N
    exact QuotientGroup.eq_one_iff (x : A)
  have hrange : f.range = H.map q := by
    dsimp [f]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  calc
    N.relIndex H = (N.subgroupOf H).index := rfl
    _ = f.ker.index := congrArg Subgroup.index hker.symm
    _ = Nat.card f.range := Subgroup.index_ker f
    _ = Nat.card (H.map q) :=
      Nat.card_congr (MulEquiv.subgroupCongr hrange).toEquiv

/-- Restrict a Frobenius kernel to an ambient-normal nontrivial subgroup,
and restrict the ambient type to the subgroup generated with the original
complement. -/
private theorem frobenius_subkernel_sibley
    {Q : Type u} [Group Q] [Finite Q]
    {K R A : Subgroup Q}
    (hfrob : IsFrobeniusDecomposition K R)
    (hAK : A ≤ K) (hAnormal : A.Normal) (hAne : A ≠ ⊥) :
    IsFrobeniusDecomposition
      (A.subgroupOf (R ⊔ A))
      (R.subgroupOf (R ⊔ A)) := by
  let J : Subgroup Q := R ⊔ A
  let AJ : Subgroup J := A.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  letI : A.Normal := hAnormal
  have hRnormA : R ≤ Subgroup.normalizer (A : Set Q) := by
    rw [A.normalizer_eq_top]
    exact le_top
  have hcomp : AJ.IsComplement' RJ := by
    simpa only [J, AJ, RJ] using
      properKernel_subgroupOf_isComplement
        hfrob.isComplement hAK hRnormA
  have hAJnormal : AJ.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : A.Normal) J
  have hAJne : AJ ≠ ⊥ := by
    intro hbot
    apply hAne
    apply le_antisymm _ bot_le
    intro a ha
    let aJ : J :=
      ⟨a, (show A ≤ J from le_sup_right) ha⟩
    have haAJ : aJ ∈ AJ := ha
    rw [hbot] at haAJ
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subgroup.mem_bot.mp haAJ))
  have hRJne : RJ ≠ ⊥ := by
    intro hbot
    apply hfrob.complement_ne_bot
    apply le_antisymm _ bot_le
    intro r hr
    let rJ : J :=
      ⟨r, (show R ≤ J from le_sup_left) hr⟩
    have hrRJ : rJ ∈ RJ := hr
    rw [hbot] at hrRJ
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subgroup.mem_bot.mp hrRJ))
  refine
    { isComplement := hcomp
      kernel_normal := hAJnormal
      kernel_ne_bot := hAJne
      complement_ne_bot := hRJne
      fixedPointFree := ?_ }
  intro r hr k hk
  let rQ : R := ⟨((r : J) : Q), r.property⟩
  let kQ : K := ⟨((k : J) : Q), hAK k.property⟩
  have hrQ : rQ ≠ 1 := by
    intro hrOne
    apply hr
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun x : R ↦ (x : Q)) hrOne)
  have hkQ :
      (rQ : Q) * (kQ : Q) * (rQ : Q)⁻¹ = (kQ : Q) := by
    exact congrArg (fun x : J ↦ (x : Q)) hk
  have hkOne := hfrob.fixedPointFree rQ hrQ kQ hkQ
  apply Subtype.ext
  exact Subtype.ext (congrArg (fun x : K ↦ (x : Q)) hkOne)

/-- Numerical form of the odd Frobenius estimate after restricting the
kernel to a normal subkernel. -/
private theorem two_complement_card_le_subkernel_card_sub_one
    {Q : Type u} [Group Q] [Fintype Q]
    {K R A : Subgroup Q}
    (hoddQ : Odd (Nat.card Q))
    (hfrob : IsFrobeniusDecomposition K R)
    (hAK : A ≤ K) (hAnormal : A.Normal) (hAne : A ≠ ⊥) :
    2 * Nat.card R ≤ Nat.card A - 1 := by
  let J : Subgroup Q := R ⊔ A
  let AJ : Subgroup J := A.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  have hfrobA : IsFrobeniusDecomposition AJ RJ := by
    simpa only [J, AJ, RJ] using
      frobenius_subkernel_sibley hfrob hAK hAnormal hAne
  have hoddJ : Odd (Nat.card J) :=
    Odd.of_dvd_nat hoddQ
      (by
        simpa only [Subgroup.card_top] using
          Subgroup.card_dvd_of_le
            (show J ≤ (⊤ : Subgroup Q) from le_top))
  have hbound := odd_Frobenius_index_ler AJ RJ hoddJ hfrobA
  have hindex : AJ.index = Nat.card R := by
    calc
      AJ.index = Nat.card RJ :=
        hfrobA.isComplement.symm.index_eq_card
      _ = Nat.card R :=
        MathlibSupport.natCard_subgroupOf_eq
          (show R ≤ J from le_sup_left)
  have hcardA : Nat.card AJ = Nat.card A :=
    MathlibSupport.natCard_subgroupOf_eq
      (show A ≤ J from le_sup_right)
  rw [hindex, hcardA] at hbound
  have hreal :
      (2 * Nat.card R : ℝ) ≤ ((Nat.card A - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.card_pos (α := A))]
    have htwice :
        (2 : ℝ) * (Nat.card R : ℝ) ≤
          (Nat.card A : ℝ) - 1 := by
      nlinarith [hbound]
    norm_num [Nat.cast_mul] at htwice ⊢
    exact htwice
  exact_mod_cast hreal

/-- Odd semiregular conjugation has at least two nonidentity acted-on
elements for every actor element. -/
private theorem two_actor_card_le_acted_card_sub_one
    {Q : Type u} [Group Q] [Fintype Q]
    {A R : Subgroup Q}
    (hoddQ : Odd (Nat.card Q))
    (hreg : IsSemiregularConjugation A R)
    (hnorm : R ≤ Subgroup.normalizer (A : Set Q))
    (hAne : A ≠ ⊥) (hRne : R ≠ ⊥) :
    2 * Nat.card R ≤ Nat.card A - 1 := by
  let J : Subgroup Q := R ⊔ A
  let AJ : Subgroup J := A.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  have hfrob : IsFrobeniusDecomposition AJ RJ := by
    simpa only [J, AJ, RJ] using
      hreg.isFrobeniusDecomposition_sup hnorm hAne hRne
  have hoddJ : Odd (Nat.card J) :=
    Odd.of_dvd_nat hoddQ
      (by
        simpa only [Subgroup.card_top] using
          Subgroup.card_dvd_of_le
            (show J ≤ (⊤ : Subgroup Q) from le_top))
  have hbound := odd_Frobenius_index_ler AJ RJ hoddJ hfrob
  have hindex : AJ.index = Nat.card R := by
    calc
      AJ.index = Nat.card RJ :=
        hfrob.isComplement.symm.index_eq_card
      _ = Nat.card R :=
        MathlibSupport.natCard_subgroupOf_eq
          (show R ≤ J from le_sup_left)
  have hcardA : Nat.card AJ = Nat.card A :=
    MathlibSupport.natCard_subgroupOf_eq
      (show A ≤ J from le_sup_right)
  rw [hindex, hcardA] at hbound
  have hreal :
      (2 * Nat.card R : ℝ) ≤ ((Nat.card A - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.card_pos (α := A))]
    have htwice :
        (2 : ℝ) * (Nat.card R : ℝ) ≤
          (Nat.card A : ℝ) - 1 := by
      nlinarith [hbound]
    norm_num [Nat.cast_mul] at htwice ⊢
    exact htwice
  exact_mod_cast hreal

/-- Once the two exceptional kernel layers form a coherent base and the
Peterfalvi degree estimate holds outside that base, repeated use of (5.6)
extends coherence to the entire nontrivial induced family.  Keeping this
finite induction separate makes the two structural branches of Sibley's
argument share the same tail. -/
private theorem extend_coherent_from_sibley_base
    {L₀ G₀ : Type u} [Group L₀] [Fintype L₀]
    [Group G₀] [Fintype G₀]
    (K₀ : Subgroup L₀) [K₀.Normal]
    (tau₀ : ClassFunction L₀ ℂ →ₗ[ℂ] ClassFunction G₀ ℂ)
    (R₀ : ClassFunction L₀ ℂ → Finset (ClassFunction G₀ ℂ))
    (calS₀ X₀ Y₀ : Finset (ClassFunction L₀ ℂ))
    (hcalS₀ : calS₀ =
      seqIndD K₀ (⊤ : Subgroup K₀) ⊥)
    (hsub₀ : subcoherent
      (↑calS₀ : Set (ClassFunction L₀ ℂ)) tau₀ R₀)
    (eta₀ : ClassFunction L₀ ℂ) (heta₀Y : eta₀ ∈ Y₀)
    (heta₀Degree : eta₀ 1 = (K₀.index : ℂ))
    (hXYcal : cfConjC_subset
      (↑(X₀ ∪ Y₀) : Set (ClassFunction L₀ ℂ))
      (↑calS₀ : Set (ClassFunction L₀ ℂ)))
    (hXYcoh : coherent
      (↑(X₀ ∪ Y₀) : Set (ClassFunction L₀ ℂ))
      (nonidentitySet L₀) tau₀)
    (hpsiXbound : ∀ psi ∈
        (↑calS₀ : Set (ClassFunction L₀ ℂ)),
      psi ∉ (↑(X₀ ∪ Y₀) : Set (ClassFunction L₀ ℂ)) →
        2 * (psi 1).re * (eta₀ 1).re <
          coherenceDegreeSum
            (↑(X₀ ∪ Y₀) : Set (ClassFunction L₀ ℂ))
            (hsub₀.finite.subset hXYcal.1)) :
    coherent
      (↑calS₀ : Set (ClassFunction L₀ ℂ))
      (nonidentitySet L₀) tau₀ := by
  classical
  have hbaseFinite :
      (↑(X₀ ∪ Y₀) : Set (ClassFunction L₀ ℂ)).Finite :=
    hsub₀.finite.subset hXYcal.1
  have hEtaBase : eta₀ ∈ X₀ ∪ Y₀ :=
    Finset.mem_union_right X₀ heta₀Y
  have hdegreeDiv
      {psi : ClassFunction L₀ ℂ}
      (hpsiCal : psi ∈
        (↑calS₀ : Set (ClassFunction L₀ ℂ))) :
      ∃ a : ℕ, psi 1 = (a : ℂ) * eta₀ 1 := by
    have hpsiSeq :
        psi ∈ seqIndD K₀ (⊤ : Subgroup K₀) ⊥ := by
      simpa only [hcalS₀] using
        (Finset.mem_coe.mp hpsiCal)
    obtain ⟨chi, _, hpsiInd⟩ :=
      (seqIndC1P (k := ℂ) K₀).mp hpsiSeq
    refine ⟨Module.finrank ℂ chi.representation, ?_⟩
    rw [hpsiInd, ClassFunction.induce_one,
      IrreducibleCharacter.apply_one_eq_finrank, heta₀Degree]
    push_cast
    ring
  have hweightNonneg
      {xi : ClassFunction L₀ ℂ}
      (hxi : xi ∈
        (↑calS₀ : Set (ClassFunction L₀ ℂ))) :
      0 ≤ coherenceDegreeWeight xi := by
    obtain ⟨d, hd⟩ :=
      (hsub₀.source_character xi hxi).exists_nat_degree
    obtain ⟨n, hn⟩ :=
      (hsub₀.source_character xi hxi).isVirtual.exists_nat_norm
    have hxiSeq :
        xi ∈ seqIndD K₀ (⊤ : Subgroup K₀) ⊥ := by
      simpa only [hcalS₀] using
        (Finset.mem_coe.mp hxi)
    have hn0 : n ≠ 0 := by
      intro hnzero
      have hzero : characterPairing xi xi = 0 := by
        rw [hn, hnzero]
        simp
      exact (cfnorm_seqInd_neq0 K₀ hxiSeq) hzero
    rw [coherenceDegreeWeight, hd, hn]
    norm_num
    exact div_nonneg (sq_nonneg (d : ℝ)) (Nat.cast_nonneg n)
  have hsumMono
      {S₁ : Set (ClassFunction L₀ ℂ)}
      (hS₁cf : cfConjC_subset S₁
        (↑calS₀ : Set (ClassFunction L₀ ℂ)))
      (hbaseS₁ :
        (↑(X₀ ∪ Y₀) : Set (ClassFunction L₀ ℂ)) ⊆ S₁) :
      coherenceDegreeSum
          (↑(X₀ ∪ Y₀) : Set (ClassFunction L₀ ℂ)) hbaseFinite ≤
        coherenceDegreeSum S₁
          (hsub₀.finite.subset hS₁cf.1) := by
    unfold coherenceDegreeSum
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (hbaseFinite.toFinset_mono hbaseS₁)
    intro xi hxi _
    apply hweightNonneg
    exact hS₁cf.1
      ((hsub₀.finite.subset hS₁cf.1).mem_toFinset.mp hxi)
  have hbuild :
      ∀ T : Finset (ClassFunction L₀ ℂ),
        T ⊆ calS₀ →
        ∃ S₁ : Set (ClassFunction L₀ ℂ),
          cfConjC_subset S₁
              (↑calS₀ : Set (ClassFunction L₀ ℂ)) ∧
            (↑(X₀ ∪ Y₀) : Set (ClassFunction L₀ ℂ)) ⊆ S₁ ∧
            (↑T : Set (ClassFunction L₀ ℂ)) ⊆ S₁ ∧
            coherent S₁ (nonidentitySet L₀) tau₀ := by
    intro T hTcal
    induction T using Finset.induction_on with
    | empty =>
        exact ⟨
          (↑(X₀ ∪ Y₀) : Set (ClassFunction L₀ ℂ)),
          hXYcal, Set.Subset.rfl, by simp, hXYcoh⟩
    | @insert psi T hpsiT ih =>
        have hpsiCal :
            psi ∈ (↑calS₀ : Set (ClassFunction L₀ ℂ)) :=
          hTcal (Finset.mem_insert_self psi T)
        have hTcal' : T ⊆ calS₀ := by
          intro xi hxi
          exact hTcal (Finset.mem_insert_of_mem hxi)
        obtain ⟨S₁, hS₁cf, hbaseS₁, hTS₁, hcoh₁⟩ :=
          ih hTcal'
        by_cases hpsi₁ : psi ∈ S₁
        · refine ⟨S₁, hS₁cf, hbaseS₁, ?_, hcoh₁⟩
          intro xi hxi
          rcases Finset.mem_insert.mp hxi with rfl | hxi
          · exact hpsi₁
          · exact hTS₁ hxi
        · let S₂ : Set (ClassFunction L₀ ℂ) :=
            {psi, ClassFunction.inverseLinear psi} ∪ S₁
          have hS₂sub :
              S₂ ⊆ (↑calS₀ : Set (ClassFunction L₀ ℂ)) := by
            intro xi hxi
            rcases hxi with hxi | hxi
            · rcases hxi with rfl | rfl
              · exact hpsiCal
              · exact hsub₀.inverse_mem psi hpsiCal
            · exact hS₁cf.1 hxi
          have hS₂closed : cfConjC_closed S₂ := by
            intro xi hxi
            rcases hxi with hxi | hxi
            · rcases hxi with rfl | rfl
              · exact Or.inl (Or.inr rfl)
              · left
                left
                ext x
                simp
            · exact Or.inr (hS₁cf.2 xi hxi)
          have hS₂cf : cfConjC_subset S₂
              (↑calS₀ : Set (ClassFunction L₀ ℂ)) :=
            ⟨hS₂sub, hS₂closed⟩
          have hpsiNotBase :
              psi ∉
                (↑(X₀ ∪ Y₀) : Set (ClassFunction L₀ ℂ)) := by
            intro hpsiBase
            exact hpsi₁ (hbaseS₁ hpsiBase)
          have hextBound :
              2 * (psi 1).re * (eta₀ 1).re <
                coherenceDegreeSum S₁
                  (hsub₀.finite.subset hS₁cf.1) :=
            (hpsiXbound psi hpsiCal hpsiNotBase).trans_le
              (hsumMono hS₁cf hbaseS₁)
          have hcoh₂ : coherent S₂ (nonidentitySet L₀) tau₀ := by
            exact extend_coherent hsub₀ hS₁cf
              (hbaseS₁ hEtaBase) hpsiCal hpsi₁ hcoh₁
              (hdegreeDiv hpsiCal) hextBound
          refine ⟨S₂, hS₂cf, ?_, ?_, hcoh₂⟩
          · intro xi hxi
            exact Or.inr (hbaseS₁ hxi)
          · intro xi hxi
            rcases Finset.mem_insert.mp hxi with rfl | hxi
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr (hTS₁ hxi)
  obtain ⟨S₁, _, _, hcalS₁, hcoh₁⟩ :=
    hbuild calS₀ (fun _ h ↦ h)
  exact subset_coherent hcalS₁ hcoh₁

/-- Glue the two exceptional kernel layers once the single balancing
difference in Sibley's calculation has been identified. -/
private theorem coherent_union_of_sibley_bridge
    {L₀ G₀ : Type u} [Group L₀] [Fintype L₀]
    [Group G₀] [Fintype G₀]
    {S₀ X₀ Y₀ : Set (ClassFunction L₀ ℂ)}
    {tau₀ : ClassFunction L₀ ℂ →ₗ[ℂ] ClassFunction G₀ ℂ}
    {R₀ : ClassFunction L₀ ℂ → Finset (ClassFunction G₀ ℂ)}
    (hsub₀ : subcoherent S₀ tau₀ R₀)
    (hX₀ : cfConjC_subset X₀ S₀)
    (hY₀ : cfConjC_subset Y₀ S₀)
    (hYX₀ : Y₀ ⊆ X₀ᶜ)
    (hbridgeData :
      ∃ (tauX tauY :
          ClassFunction L₀ ℂ →ₗ[ℂ] ClassFunction G₀ ℂ)
        (xi₁ eta₁ : ClassFunction L₀ ℂ) (a : ℕ),
        coherent_with X₀ (nonidentitySet L₀) tau₀ tauX ∧
        coherent_with Y₀ (nonidentitySet L₀) tau₀ tauY ∧
        xi₁ ∈ X₀ ∧ eta₁ ∈ Y₀ ∧
        xi₁ 1 = (a : ℂ) * eta₁ 1 ∧
        tau₀ (xi₁ - (a : ℂ) • eta₁) =
          tauX xi₁ - (a : ℂ) • tauY eta₁) :
    coherent (X₀ ∪ Y₀) (nonidentitySet L₀) tau₀ := by
  obtain ⟨tauX, tauY, xi₁, eta₁, a,
      hcohX, hcohY, hxi₁, heta₁, hdegree, hbridge⟩ :=
    hbridgeData
  have haeta :
      (a : ℂ) • eta₁ ∈ AddSubgroup.closure Y₀ := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      (AddSubgroup.closure Y₀).nsmul_mem
        (AddSubgroup.subset_closure heta₁) a
  have hdiffOff :
      xi₁ - (a : ℂ) • eta₁ ∈
        ClassFunction.supportedOn (nonidentitySet L₀) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hx₁ : x = 1 := by
      simpa [nonidentitySet] using not_not.mp hx
    subst x
    simp only [ClassFunction.sub_apply, ClassFunction.smul_apply,
      smul_eq_mul, hdegree, sub_self]
  have hbridge' :
      tau₀ (xi₁ - (a : ℂ) • eta₁) =
        tauX xi₁ - tauY ((a : ℂ) • eta₁) := by
    simpa only [map_smul] using hbridge
  exact bridge_coherent hsub₀ hX₀ hcohX hY₀ hcohY hYX₀
    (chi := xi₁) (phi := (a : ℂ) • eta₁)
    hxi₁ haeta hdiffOff hbridge'

/-- The final pivot step in Sibley's prime-Dade branch.  The preceding
character calculation only has to supply a universal pivot and the
orthogonal decompositions recorded in `hXbridge`. -/
private theorem coherent_union_of_sibley_pivot
    {L₀ G₀ : Type u} [Group L₀] [Fintype L₀]
    [Group G₀] [Fintype G₀]
    {S₀ : Set (ClassFunction L₀ ℂ)}
    {X₀ Y₀ : Finset (ClassFunction L₀ ℂ)}
    {tau₀ : ClassFunction L₀ ℂ →ₗ[ℂ] ClassFunction G₀ ℂ}
    {R₀ : ClassFunction L₀ ℂ → Finset (ClassFunction G₀ ℂ)}
    {eta₁ : ClassFunction L₀ ℂ}
    {Y₁ : ClassFunction G₀ ℂ}
    (hsub₀ : subcoherent S₀ tau₀ R₀)
    (hX₀ : cfConjC_subset
      (↑X₀ : Set (ClassFunction L₀ ℂ)) S₀)
    (hY₀ : cfConjC_subset
      (↑Y₀ : Set (ClassFunction L₀ ℂ)) S₀)
    (heta₁ : eta₁ ∈ Y₀)
    (hY₁Virtual : ClassFunction.IsVirtual Y₁)
    (hY₁Norm : characterPairing Y₁ Y₁ =
      characterPairing eta₁ eta₁)
    (hYdegree₁ : ∀ eta ∈ Y₀, eta 1 = eta₁ 1)
    (hXbridge : ∀ xi ∈ X₀,
      ∃ (a : ℕ) (X₁ : ClassFunction G₀ ℂ),
        xi 1 = (a : ℂ) * eta₁ 1 ∧
        characterPairing X₁ Y₁ = 0 ∧
        tau₀ (xi - (a : ℂ) • eta₁) =
          X₁ - (a : ℂ) • Y₁)
    (hYpivot : ∀ eta ∈ Y₀, eta ≠ eta₁ →
      characterPairing (tau₀ (eta - eta₁)) Y₁ =
        -characterPairing eta₁ eta₁) :
    coherent
      ((↑X₀ : Set (ClassFunction L₀ ℂ)) ∪
        (↑Y₀ : Set (ClassFunction L₀ ℂ)))
      (nonidentitySet L₀) tau₀ := by
  let XY : Set (ClassFunction L₀ ℂ) :=
    (↑X₀ : Set (ClassFunction L₀ ℂ)) ∪
      (↑Y₀ : Set (ClassFunction L₀ ℂ))
  have hXY : cfConjC_subset XY S₀ := by
    refine ⟨Set.union_subset hX₀.1 hY₀.1, ?_⟩
    intro phi hphi
    rcases hphi with hphi | hphi
    · exact Or.inl (hX₀.2 phi hphi)
    · exact Or.inr (hY₀.2 phi hphi)
  have hsubXY : subcoherent XY tau₀ R₀ :=
    subset_subcoherent hsub₀ hXY
  have pairing_sub_left_local
      (f g h : ClassFunction G₀ ℂ) :
      characterPairing (f - g) h =
        characterPairing f h - characterPairing g h := by
    rw [sub_eq_add_neg, characterPairing_add_left,
      ← neg_one_smul ℂ g, characterPairing_smul_left]
    ring
  refine pivot_coherence hsubXY (Or.inr heta₁)
    hY₁Virtual ?_ hY₁Norm
  intro xi hxi hne
  rcases hxi with hxiX | hxiY
  · obtain ⟨a, X₁, hdegree, horth, hdecomp⟩ :=
      hXbridge xi hxiX
    refine ⟨a, hdegree, ?_⟩
    rw [hdecomp, pairing_sub_left_local,
      characterPairing_smul_left, horth, hY₁Norm]
    ring
  · refine ⟨1, ?_, ?_⟩
    · simpa using hYdegree₁ xi hxiY
    · simpa using hYpivot xi hxiY hne

/-! ## Peterfalvi (6.8) -/

set_option maxHeartbeats 800000

/-- Peterfalvi (6.8), `PFsection6.v: Sibley_coherence`.

The family induced from the nonprincipal irreducibles of the nilpotent TI
subgroup is coherent for ordinary induction to `G`. -/
theorem Sibley_coherence
    {Gamma : Type} [Group Gamma] [Fintype Gamma]
    (G L H W₁ : Subgroup Gamma)
    (hLG : L ≤ G) (hHL : H ≤ L) (hW₁L : W₁ ≤ L)
    (hoddL : Odd (Nat.card L))
    (hnilH : Group.IsNilpotent H)
    (hTI : IsNormalizedTI (subgroupNonidentity H) G L)
    (hstruct : SibleyStructuralAlternative G L H W₁) :
    coherent
      (↑(sibleyFamily L H) : Set (ClassFunction L ℂ))
      (nonidentitySet L)
      (sibleyInduce G L hLG) := by
  classical
  let K : Subgroup L := H.subgroupOf L
  let W₁L' : Subgroup L := W₁.subgroupOf L
  let tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ :=
    sibleyInduce G L hLG
  let calS : Finset (ClassFunction L ℂ) :=
    seqIndD K (⊤ : Subgroup K) ⊥
  let case_c1 : Prop := IsFrobeniusDecomposition K W₁L'
  let case_c2 : Prop := ¬case_c1

  have hstruct' :
      case_c1 ∨
        ∃ W₂ : Subgroup Gamma,
          Nat.Prime (Nat.card W₂) ∧
            W₂ ≤ ambientCommutator H ∧
              ∃ (A₀ : Set Gamma) (W : Subgroup Gamma)
                  (defW : IsInternalDirectProductIn W₁ W₂ W),
                PrimeDadeHypothesis G L H H
                  (subgroupNonidentity H) A₀ W W₁ W₂ defW := by
    simpa only [SibleyStructuralAlternative, case_c1, K, W₁L'] using
      hstruct
  obtain ⟨W₂, hW₂c1, hW₂c2⟩ :
      ∃ W₂ : Subgroup Gamma,
        (case_c1 → W₂ = ⊥) ∧
          (case_c2 →
            Nat.Prime (Nat.card W₂) ∧
              W₂ ≤ ambientCommutator H ∧
                ∃ (A₀ : Set Gamma) (W : Subgroup Gamma)
                    (defW : IsInternalDirectProductIn W₁ W₂ W),
                  PrimeDadeHypothesis G L H H
                    (subgroupNonidentity H) A₀ W W₁ W₂ defW) := by
    by_cases hc1 : case_c1
    · exact ⟨⊥, fun _ ↦ rfl, fun hc2 ↦ (hc2 hc1).elim⟩
    · rcases hstruct' with hc1' | ⟨W₂, hp, hder, A₀, W, defW, pd⟩
      · exact (hc1 hc1').elim
      · exact ⟨W₂, fun hc1' ↦ (hc1 hc1').elim,
          fun _ ↦ ⟨hp, hder, A₀, W, defW, pd⟩⟩

  have hW₂H : W₂ ≤ H := by
    by_cases hc1 : case_c1
    · rw [hW₂c1 hc1]
      exact bot_le
    · rcases hW₂c2 hc1 with ⟨_, _, A₀, W, defW, pd⟩
      exact pd.prDade_prTI.fixed_le_kernel
  have hW₂L : W₂ ≤ L := hW₂H.trans hHL
  have hKnormal : K.Normal := by
    by_cases hc1 : case_c1
    · exact hc1.kernel_normal
    · rcases hW₂c2 hc1 with ⟨_, _, A₀, W, defW, pd⟩
      exact pd.prDade_prTI.kernel_normal
  letI : K.Normal := hKnormal
  have hKW₁ : K.IsComplement' W₁L' := by
    by_cases hc1 : case_c1
    · exact hc1.isComplement
    · rcases hW₂c2 hc1 with ⟨_, _, A₀, W, defW, pd⟩
      exact pd.prDade_prTI.semidirect_complement
  have hKne : K ≠ ⊥ := by
    obtain ⟨x, hxH, hxne⟩ := hTI.1
    intro hbot
    let xL : L := ⟨x, hHL hxH⟩
    have hxK : xL ∈ K := hxH
    rw [hbot] at hxK
    exact hxne (congrArg Subtype.val (Subgroup.mem_bot.mp hxK))
  have hW₁ne : W₁L' ≠ ⊥ := by
    by_cases hc1 : case_c1
    · exact hc1.complement_ne_bot
    · rcases hW₂c2 hc1 with ⟨_, _, A₀, W, defW, pd⟩
      intro hbot
      apply pd.prDade_prTI.complement_ne_bot
      apply le_antisymm _ bot_le
      intro w hw
      let wL : L := ⟨w, hW₁L hw⟩
      have hwSub : wL ∈ W₁L' := hw
      rw [hbot] at hwSub
      exact Subgroup.mem_bot.mpr
        (congrArg Subtype.val (Subgroup.mem_bot.mp hwSub))
  let eKH : K ≃* H := Subgroup.subgroupOfEquivOfLe hHL
  letI : Group.IsNilpotent K :=
    (Group.isNilpotent_congr eKH).mpr hnilH
  letI : IsSolvable K := inferInstance

  have hAG1 :
      subgroupNonidentity H ⊆ (G : Set Gamma) \ {(1 : Gamma)} := by
    intro x hx
    exact ⟨hLG (hHL hx.1), by simpa using hx.2⟩
  have hAinv : IsInvStable (subgroupNonidentity H) := by
    intro x
    constructor
    · rintro ⟨hxH, hxne⟩
      exact ⟨by simpa using H.inv_mem hxH,
        by simpa using hxne⟩
    · rintro ⟨hxH, hxne⟩
      exact ⟨H.inv_mem hxH, inv_ne_one.mpr hxne⟩
  have hcalClosed :
      cfConjC_closed
        (↑calS : Set (ClassFunction L ℂ)) := by
    intro phi hphi
    exact seqInd_inverse_mem K (⊤ : Subgroup K) ⊥ hphi
  have hcalNonreal : ∀ phi ∈ calS,
      ClassFunction.inverseLinear phi ≠ phi := by
    intro phi hphi
    exact seqInd_conjC_neq K hoddL (⊤ : Subgroup K) ⊥ hphi
  have hspanK {phi : ClassFunction L ℂ}
      (hphi : phi ∈
        AddSubgroup.closure
          (↑calS : Set (ClassFunction L ℂ))) :
      phi ∈ ClassFunction.supportedOn (K : Set L) := by
    induction hphi using AddSubgroup.closure_induction with
    | mem phi hphi => exact seqInd_on K hphi
    | zero => exact (ClassFunction.supportedOn (R := ℂ) (K : Set L)).zero_mem
    | add phi psi _ _ ihphi ihpsi =>
        exact (ClassFunction.supportedOn (R := ℂ) (K : Set L)).add_mem
          ihphi ihpsi
    | neg phi _ ihphi =>
        exact (ClassFunction.supportedOn (R := ℂ) (K : Set L)).neg_mem
          ihphi
  have hspanA {phi : ClassFunction L ℂ}
      (hphi : phi ∈
        AddSubgroup.closure
          (↑calS : Set (ClassFunction L ℂ)))
      (hoff : phi ∈ ClassFunction.supportedOn (nonidentitySet L)) :
      phi ∈ ClassFunction.supportedOn
        {x : L | (x : Gamma) ∈ subgroupNonidentity H} := by
    have hphiK := hspanK hphi
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hxA
    by_cases hx1 : x = 1
    · subst x
      exact ClassFunction.eq_zero_of_mem_supportedOn hoff
        (by simp [nonidentitySet])
    · apply ClassFunction.eq_zero_of_mem_supportedOn hphiK
      intro hxK
      apply hxA
      exact ⟨hxK, fun hx ↦ hx1 (Subtype.ext hx)⟩
  have hspanVirtual {phi : ClassFunction L ℂ}
      (hphi : phi ∈
        AddSubgroup.closure
          (↑calS : Set (ClassFunction L ℂ))) :
      ClassFunction.IsVirtual phi := by
    induction hphi using AddSubgroup.closure_induction with
    | mem phi hphi => exact seqInd_vcharW K hphi
    | zero => exact ClassFunction.IsVirtual.zero
    | add phi psi _ _ ihphi ihpsi => exact ihphi.add ihpsi
    | neg phi _ ihphi => exact ihphi.neg
  have htauIsometry : ∀ phi ∈
      AddSubgroup.closure
        (↑calS : Set (ClassFunction L ℂ)),
      phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
      ∀ psi ∈ AddSubgroup.closure
        (↑calS : Set (ClassFunction L ℂ)),
      psi ∈ ClassFunction.supportedOn (nonidentitySet L) →
        characterPairing (tau phi) (tau psi) =
          characterPairing phi psi := by
    intro phi hphi hphiOff psi hpsi hpsiOff
    simpa only [tau, sibleyInduce, LinearMap.comp_apply] using
      normedTI_induce_characterPairing hTI hAG1 hAinv phi psi
        (hspanA hphi hphiOff) (hspanA hpsi hpsiOff)
  have htauVirtual : ∀ phi ∈
      AddSubgroup.closure
        (↑calS : Set (ClassFunction L ℂ)),
      phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
        ClassFunction.IsVirtual (tau phi) := by
    intro phi hphi _hoff
    obtain ⟨z, hz⟩ := hspanVirtual hphi
    let e : L.subgroupOf G ≃* L :=
      Subgroup.subgroupOfEquivOfLe hLG
    let zL : VirtualCharacter (L.subgroupOf G) ℂ :=
      VirtualCharacter.comap e.toMonoidHom z
    let zG : VirtualCharacter G ℂ :=
      VirtualCharacter.induce (L.subgroupOf G) zL
    refine ⟨zG, ?_⟩
    calc
      VirtualCharacter.realize zG =
          ClassFunction.induce (L.subgroupOf G)
            (VirtualCharacter.realize zL) := by
        exact VirtualCharacter.realize_induce (L.subgroupOf G) zL
      _ = ClassFunction.induce (L.subgroupOf G)
          (ClassFunction.toSubgroupOf L G hLG phi) := by
        apply congrArg (ClassFunction.induce (L.subgroupOf G))
        calc
          VirtualCharacter.realize zL =
              ClassFunction.comap e.toMonoidHom
                (VirtualCharacter.realize z) :=
            VirtualCharacter.realize_comap e.toMonoidHom z
          _ = ClassFunction.toSubgroupOf L G hLG phi := by
            rw [hz]
            rfl
      _ = tau phi := rfl
  have htauSupported : ∀ phi ∈
      AddSubgroup.closure
        (↑calS : Set (ClassFunction L ℂ)),
      phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
        tau phi ∈ ClassFunction.supportedOn (nonidentitySet G) := by
    intro phi _hphi hoff
    rw [ClassFunction.mem_supportedOn_iff]
    intro g hg
    have hg1 : g = 1 := by
      simpa [nonidentitySet] using not_not.mp hg
    subst g
    have hphi1 : phi 1 = 0 :=
      ClassFunction.eq_zero_of_mem_supportedOn hoff (by simp [nonidentitySet])
    simp only [tau, sibleyInduce, LinearMap.comp_apply,
      ClassFunction.induce_one, ClassFunction.toSubgroupOf_apply,
      map_one, hphi1, mul_zero]

  obtain ⟨R, hsub⟩ :
      ∃ R : ClassFunction L ℂ → Finset (ClassFunction G ℂ),
        subcoherent
          (↑calS : Set (ClassFunction L ℂ)) tau R := by
    by_cases hc1 : case_c1
    · have hcalIrr :
          (↑calS : Set (ClassFunction L ℂ)) ⊆
            Set.range (fun chi : IrreducibleCharacter L ℂ ↦
              (chi : ClassFunction L ℂ)) := by
        intro phi hphi
        obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp hphi
        have hthetaNe : theta ≠ IrreducibleCharacter.trivial := by
          intro htriv
          subst theta
          have hnot := (mem_Iirr_kerD.mp htheta).2
          apply hnot
          intro x _ y
          simp
        let chi : IrreducibleCharacter L ℂ :=
          ⟨ClassFunction.induce K (theta : ClassFunction K ℂ),
            irr_induced_Frobenius_ker hc1 theta hthetaNe⟩
        exact ⟨chi, rfl⟩
      exact irr_subcoherent
        (↑calS : Set (ClassFunction L ℂ)) tau
        ⟨hcalIrr, hcalClosed⟩ hcalNonreal
        htauIsometry htauVirtual htauSupported
    · rcases hW₂c2 hc1 with ⟨_, _, A₀, W, defW, pd⟩
      let isoL : CyclicTIIsometryData (k := ℂ)
          pd.prDade_prTI.prime_cycTIhyp :=
        pd.prDade_prTI.prime_cycTIhyp.cyclicTIIsometryData
      let isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI :=
        pd.prDade_cycTI.cyclicTIIsometryData
      have hsignal : pd.signalizerInKernel = (⊤ : Subgroup K) := by
        ext x
        simp [PrimeDadeHypothesis.signalizerInKernel, K]
      have hcalDade : cfConjC_subset
          (↑calS : Set (ClassFunction L ℂ))
          (↑(seqIndD (k := ℂ) K pd.signalizerInKernel ⊥) :
            Set (ClassFunction L ℂ)) := by
        rw [hsignal]
        exact ⟨Set.Subset.rfl, hcalClosed⟩
      obtain ⟨R, hsubDade, _, _⟩ :=
        pd.prDade_subcoherent isoL isoG
          (↑calS : Set (ClassFunction L ℂ))
          hcalDade hcalNonreal
      refine ⟨R, subcoherent_congr hsubDade ?_⟩
      intro phi hphi hoff
      have hphiA := hspanA hphi hoff
      calc
        Dade pd.prDade_hyp phi =
            ClassFunction.induce (L.subgroupOf G)
              (ClassFunction.toSubgroupOf L G
                pd.prDade_hyp.2.1 phi) :=
          pd.Dade_Ind_on_smallSet hTI phi hphiA
        _ = tau phi := by rfl

  letI : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hKne
  let D : Subgroup K := _root_.commutator K
  let DL : Subgroup L := D.map K.subtype
  have hDtop : D < (⊤ : Subgroup K) := by
    simpa only [D] using
      (IsSolvable.commutator_lt_top_of_nontrivial K)
  have hDLproper : DL < K := by
    have hmap :=
      (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).2 hDtop
    simpa only [DL, ← MonoidHom.range_eq_map, K.range_subtype] using hmap
  have hDLnormal : DL.Normal := by
    dsimp only [DL, D]
    infer_instance
  letI : DL.Normal := hDLnormal
  have hDerEquiv :
      D.map eKH.toMonoidHom = _root_.commutator H := by
    dsimp only [D]
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr eKH.surjective]
    rfl
  have hcompSubtype :
      L.subtype.comp K.subtype =
        H.subtype.comp eKH.toMonoidHom := by
    ext x
    rfl
  have hDambient :
      DL.map L.subtype = ambientCommutator H := by
    calc
      DL.map L.subtype =
          D.map (L.subtype.comp K.subtype) := by
            simp only [DL, Subgroup.map_map]
      _ = D.map (H.subtype.comp eKH.toMonoidHom) := by
            rw [hcompSubtype]
      _ = (D.map eKH.toMonoidHom).map H.subtype := by
            rw [Subgroup.map_map]
      _ = (_root_.commutator H).map H.subtype := by
            rw [hDerEquiv]
      _ = ambientCommutator H := rfl
  have hW₂DL (hc2 : case_c2) : W₂.subgroupOf L ≤ DL := by
    rcases hW₂c2 hc2 with ⟨_, hW₂der, A₀, W, defW, pd⟩
    intro w hw
    have hwMap : L.subtype w ∈ DL.map L.subtype := by
      rw [hDambient]
      exact hW₂der hw
    rcases hwMap with ⟨d, hd, hdw⟩
    have hdw' : d = w := L.subtype_injective hdw
    rwa [← hdw']
  have hfrobDerived :
      IsFrobeniusDecomposition
        (K.map (QuotientGroup.mk' DL))
        (W₁L'.map (QuotientGroup.mk' DL)) := by
    by_cases hc1 : case_c1
    · exact hc1.quotient hDLproper
    · rcases hW₂c2 hc1 with ⟨_, _, A₀, W, defW, pd⟩
      simpa only [K, W₁L'] using
        primeTI_frobenius_quotient_of_fixed_le
          pd.prDade_prTI DL hDLproper (hW₂DL hc1)
  have hnilBot :
      Group.IsNilpotent (K ⧸ (⊥ : Subgroup K)) := by
    exact Group.nilpotent_of_surjective
      (QuotientGroup.mk' (⊥ : Subgroup K))
      (QuotientGroup.mk'_surjective (⊥ : Subgroup K))
  have hfq : odd_Frobenius_quotient K (⊥ : Subgroup K) := by
    dsimp [odd_Frobenius_quotient]
    refine ⟨hoddL, hnilBot, ?_⟩
    let H₁ : Subgroup L :=
      (_root_.commutator K ⊔ (⊥ : Subgroup K)).map K.subtype
    have hH₁proper : H₁ < K := by
      simpa only [H₁, sup_bot_eq, DL, D] using hDLproper
    have hW₂H₁ (hc2 : case_c2) : W₂.subgroupOf L ≤ H₁ := by
      simpa only [H₁, sup_bot_eq, DL, D] using hW₂DL hc2
    letI : H₁.Normal := by
      simpa only [H₁, sup_bot_eq, DL, D] using hDLnormal
    change ∃ E : Subgroup (L ⧸ H₁),
      IsFrobeniusDecomposition
        (K.map (QuotientGroup.mk' H₁)) E
    refine ⟨W₁L'.map (QuotientGroup.mk' H₁), ?_⟩
    by_cases hc1 : case_c1
    · exact hc1.quotient hH₁proper
    · rcases hW₂c2 hc1 with ⟨_, _, A₀, W, defW, pd⟩
      simpa only [K, W₁L'] using
        primeTI_frobenius_quotient_of_fixed_le
          pd.prDade_prTI H₁ hH₁proper (hW₂H₁ hc1)

  rcases non_coherent_chief K tau R hsub ⊥ hfq with
      hcoh | hexception
  · simpa only [sibleyFamily, calS, K, tau] using hcoh
  · rcases hexception with
      ⟨hchief, hindexBound, p, hp, hKbotP, hKbotNonabelian,
        hindexNotDvd⟩
    letI : Fact p.Prime := ⟨hp⟩
    have hKp : IsPGroup p K :=
      hKbotP.of_equiv QuotientGroup.quotientBot
    have hKnonabelian : ¬ IsMulCommutative K := by
      intro hcomm
      letI : IsMulCommutative K := hcomm
      apply hKbotNonabelian
      rw [isMulCommutative_iff]
      intro x y
      apply QuotientGroup.quotientBot.injective
      simp only [map_mul]
      exact mul_comm _ _
    have hKW₁cop :
        Nat.Coprime (Nat.card K) (Nat.card W₁L') := by
      by_cases hc1 : case_c1
      · exact hc1.natCard_coprime
      · rcases hW₂c2 hc1 with ⟨_, _, A₀, W, defW, pd⟩
        simpa only [K, W₁L',
          MathlibSupport.natCard_subgroupOf_eq hHL,
          MathlibSupport.natCard_subgroupOf_eq hW₁L] using
            pd.prDade_prTI.kernel_complement_card_coprime
    have hpKcard : p ∣ Nat.card K :=
      hKp.card_eq_or_dvd.resolve_left
        (fun hcard ↦ hKne (Subgroup.card_eq_one.mp hcard))
    have hpKindex : ¬ p ∣ K.index := by
      rw [hKW₁.symm.index_eq_card]
      exact hp.coprime_iff_not_dvd.mp
        (hKW₁cop.coprime_dvd_left hpKcard)
    let PL : Sylow p L := hKp.toSylow hpKindex
    have hPLcoe : (PL : Subgroup L) = K := rfl
    have hpW₁card : ¬ p ∣ Nat.card W₁L' := by
      rw [← hKW₁.symm.index_eq_card]
      exact hpKindex
    obtain ⟨PG, hPG⟩ :=
      exists_sylow_subgroupOf_eq_of_normalizedTI_isComplement
        hLG hHL W₁L'
        (by simpa only [K] using hKp) hTI
        (by simpa only [K] using hKW₁) hpW₁card
    have hTIG : IsNormalizedTI
        (subgroupNonidentity (PG : Subgroup G))
        (⊤ : Subgroup G) (L.subgroupOf G) := by
      have hTIG₀ := normalizedTI_subgroupOf
        (hHL.trans hLG) hLG hTI
      simpa only [hPG] using hTIG₀
    have hPGcard : Nat.card PG = Nat.card K := by
      calc
        Nat.card PG = Nat.card (H.subgroupOf G) :=
          Nat.card_congr (MulEquiv.subgroupCongr hPG).toEquiv
        _ = Nat.card H :=
          MathlibSupport.natCard_subgroupOf_eq (hHL.trans hLG)
        _ = Nat.card K := by
          simpa only [K] using
            (MathlibSupport.natCard_subgroupOf_eq hHL).symm

    let W₂L' : Subgroup L := W₂.subgroupOf L
    have hW₂LK : W₂L' ≤ K := by
      intro w hw
      exact hW₂H hw
    let W₂K : Subgroup K := W₂L'.subgroupOf K
    have hW₂Kcard : Nat.card W₂K = Nat.card W₂ := by
      calc
        Nat.card W₂K = Nat.card W₂L' := by
          simpa only [W₂K] using
            MathlibSupport.natCard_subgroupOf_eq hW₂LK
        _ = Nat.card W₂ := by
          simpa only [W₂L'] using
            MathlibSupport.natCard_subgroupOf_eq hW₂L
    have hDLsubK : DL.subgroupOf K = D := by
      dsimp only [DL]
      exact Subgroup.comap_map_eq_self_of_injective
        K.subtype_injective D

    let caseA : Prop := Subgroup.center K ⊓ W₂K ≤ ⊥
    let caseB : Prop := ¬caseA
    have hcaseB_c2 (hcaseB : caseB) : case_c2 := by
      intro hc1
      apply hcaseB
      simpa only [caseA, W₂K, W₂L', hW₂c1 hc1, Subgroup.bot_subgroupOf,
        inf_bot_eq] using (bot_le : (⊥ : Subgroup K) ≤ ⊥)
    have hcaseB_W₂center (hcaseB : caseB) :
        W₂K ≤ Subgroup.center K := by
      have hc2 := hcaseB_c2 hcaseB
      rcases hW₂c2 hc2 with ⟨hW₂prime, _, A₀, W, defW, pd⟩
      have hprimeK : Nat.Prime (Nat.card W₂K) := by
        simpa only [hW₂Kcard] using hW₂prime
      have hdiv : Nat.card ↥(Subgroup.center K ⊓ W₂K) ∣
          Nat.card W₂K :=
        Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime hprimeK).mp hdiv with hcardOne | hcardFull
      · have hbot : Subgroup.center K ⊓ W₂K = ⊥ :=
          Subgroup.eq_bot_of_card_eq _ hcardOne
        apply (hcaseB ?_).elim
        dsimp only [caseA]
        rw [hbot]
      · have hfull : Subgroup.center K ⊓ W₂K = W₂K := by
          apply Subgroup.eq_of_le_of_card_ge inf_le_right
          rw [hcardFull]
        intro w hw
        have : w ∈ Subgroup.center K ⊓ W₂K := by
          rw [hfull]
          exact hw
        exact this.1
    have hcaseB_W₂D (hcaseB : caseB) : W₂K ≤ D := by
      have hc2 := hcaseB_c2 hcaseB
      intro w hw
      rw [← hDLsubK]
      exact hW₂DL hc2 hw
    have hcaseB_W₂prime (hcaseB : caseB) :
        Nat.Prime (Nat.card W₂K) := by
      have hc₂ := hcaseB_c2 hcaseB
      rcases hW₂c2 hc₂ with ⟨hprime, _, A₀, W, defW, pd⟩
      simpa only [hW₂Kcard] using hprime

    let Z : Subgroup K :=
      if caseA then Subgroup.center K ⊓ D else W₂K
    have hZcenter : Z ≤ Subgroup.center K := by
      by_cases hcaseA : caseA
      · simpa only [Z, if_pos hcaseA] using
          (inf_le_left : Subgroup.center K ⊓ D ≤ Subgroup.center K)
      · simpa only [Z, if_neg hcaseA] using
          hcaseB_W₂center hcaseA
    have hZD : Z ≤ D := by
      by_cases hcaseA : caseA
      · simpa only [Z, if_pos hcaseA] using
          (inf_le_right : Subgroup.center K ⊓ D ≤ D)
      · simpa only [Z, if_neg hcaseA] using
          hcaseB_W₂D hcaseA
    have hDne : D ≠ ⊥ := by
      intro hDbot
      apply hKnonabelian
      exact (_root_.commutator_eq_bot_iff K).mp
        (by simpa only [D] using hDbot)
    have hZne : Z ≠ ⊥ := by
      by_cases hcaseA : caseA
      · have hmeet := nilpotent_normal_inf_center_ne_bot D hDne
        simpa only [Z, if_pos hcaseA, inf_comm] using hmeet
      · have hc2 := hcaseB_c2 hcaseA
        rcases hW₂c2 hc2 with ⟨hW₂prime, _, A₀, W, defW, pd⟩
        have hprimeK : Nat.Prime (Nat.card W₂K) := by
          simpa only [hW₂Kcard] using hW₂prime
        simpa only [Z, if_neg hcaseA] using
          W₂K.one_lt_card_iff_ne_bot.mp hprimeK.one_lt
    have hcaseB_Zprime (hcaseB : caseB) :
        Nat.Prime (Nat.card Z) := by
      simpa only [Z, if_neg hcaseB] using
        hcaseB_W₂prime hcaseB

    have hcaseB_ZcenterL (hcaseB : caseB) :
        Z.map K.subtype ≤ Subgroup.center L := by
      have hc2 := hcaseB_c2 hcaseB
      rcases hW₂c2 hc2 with ⟨_, _, A₀, W, defW, pd⟩
      rintro z ⟨zK, hzK, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro l
      rcases hKW₁.2 l with ⟨⟨k, r⟩, hkr⟩
      change ((k : K) : L) * ((r : W₁L') : L) = l at hkr
      have hzW₂ : (((zK : K) : L) : Gamma) ∈ W₂ := by
        have hzW₂K : zK ∈ W₂K := by
          change zK ∈ Z at hzK
          rw [show Z = W₂K by
            simp only [Z, if_neg hcaseB]] at hzK
          exact hzK
        exact hzW₂K
      let rW₁ : W₁ := ⟨((r : W₁L') : L), r.property⟩
      let zW₂ : W₂ := ⟨(((zK : K) : L) : Gamma), hzW₂⟩
      have hzk :
          ((zK : K) : L) * ((k : K) : L) =
            ((k : K) : L) * ((zK : K) : L) := by
        have hzKcenter := hZcenter hzK
        rw [Subgroup.mem_center_iff] at hzKcenter
        exact (congrArg (fun x : K ↦ (x : L))
          (hzKcenter k)).symm
      have hzr :
          ((zK : K) : L) * ((r : W₁L') : L) =
            ((r : W₁L') : L) * ((zK : K) : L) := by
        apply Subtype.ext
        exact (defW.commute rW₁ zW₂).symm.eq
      have hcommProduct :
        ((zK : K) : L) *
              (((k : K) : L) * ((r : W₁L') : L)) =
            (((k : K) : L) * ((r : W₁L') : L)) *
              ((zK : K) : L) := by
        calc
          ((zK : K) : L) *
                (((k : K) : L) * ((r : W₁L') : L)) =
              (((zK : K) : L) * ((k : K) : L)) *
                ((r : W₁L') : L) := by rw [mul_assoc]
          _ = (((k : K) : L) * ((zK : K) : L)) *
                ((r : W₁L') : L) := by rw [hzk]
          _ = ((k : K) : L) *
                (((zK : K) : L) * ((r : W₁L') : L)) := by
                  rw [mul_assoc]
          _ = ((k : K) : L) *
                (((r : W₁L') : L) * ((zK : K) : L)) := by rw [hzr]
          _ = (((k : K) : L) * ((r : W₁L') : L)) *
                ((zK : K) : L) := by rw [mul_assoc]
      calc
        l * ((zK : K) : L) =
            (((k : K) : L) * ((r : W₁L') : L)) *
              ((zK : K) : L) := by rw [hkr]
        _ = ((zK : K) : L) *
              (((k : K) : L) * ((r : W₁L') : L)) :=
          hcommProduct.symm
        _ = ((zK : K) : L) * l := by rw [hkr]
    have hZmapNormal : (Z.map K.subtype : Subgroup L).Normal := by
      by_cases hcaseA : caseA
      · dsimp only [Z]
        rw [if_pos hcaseA]
        haveI : (Subgroup.center K ⊓ D).Characteristic := by
          rw [Subgroup.characteristic_iff_map_eq]
          intro e
          rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective,
            Subgroup.characteristic_iff_map_eq.mp
              (show (Subgroup.center K).Characteristic from
                inferInstance) e,
            Subgroup.characteristic_iff_map_eq.mp
              (show D.Characteristic by
                dsimp only [D]
                infer_instance) e]
        infer_instance
      · refine { conj_mem := ?_ }
        intro z hz g
        have hzCenter := hcaseB_ZcenterL hcaseA hz
        rw [Subgroup.mem_center_iff] at hzCenter
        have hconj : g * z * g⁻¹ = z := by
          calc
            g * z * g⁻¹ = z * g * g⁻¹ := by
              rw [hzCenter g]
            _ = z := by simp
        rwa [hconj]
    letI : (Z.map K.subtype : Subgroup L).Normal := hZmapNormal
    letI : Z.Normal := Subgroup.Normal.of_map_subtype hZmapNormal

    let LG : Subgroup G := L.subgroupOf G
    let eLG : LG ≃* L := Subgroup.subgroupOfEquivOfLe hLG
    let ZLG : Subgroup LG :=
      (Z.map K.subtype).map eLG.symm.toMonoidHom
    have hZLGnormal : ZLG.Normal :=
      Subgroup.Normal.map hZmapNormal eLG.symm.toMonoidHom
        eLG.symm.surjective
    let ZG : Subgroup G := ZLG.map LG.subtype
    let embedLtoG : L →* G :=
      LG.subtype.comp eLG.symm.toMonoidHom
    have hembedLtoG : Function.Injective embedLtoG :=
      LG.subtype_injective.comp eLG.symm.injective
    have hZmapEmbed :
        (Z.map K.subtype).map embedLtoG = ZG := by
      simp only [embedLtoG, ZG, ZLG, Subgroup.map_map]
    let zToG : Z →* G :=
      embedLtoG.comp (K.subtype.comp Z.subtype)
    have hzToGInjective : Function.Injective zToG :=
      hembedLtoG.comp
        (K.subtype_injective.comp Z.subtype_injective)
    have hzToGRange : zToG.range = ZG := by
      dsimp only [zToG]
      rw [MonoidHom.range_comp, MonoidHom.range_comp,
        Subgroup.range_subtype, hZmapEmbed]
    have hZGcard : Nat.card ZG = Nat.card Z := by
      calc
        Nat.card ZG = Nat.card ZLG := by
          exact Subgroup.card_map_of_injective
            LG.subtype_injective
        _ = Nat.card (Z.map K.subtype) := by
          exact Subgroup.card_map_of_injective
            eLG.symm.injective
        _ = Nat.card Z := by
          exact Subgroup.card_map_of_injective
            K.subtype_injective
    have hcaseB_ZGprime (hcaseB : caseB) :
        Nat.Prime (Nat.card ZG) := by
      rw [hZGcard]
      exact hcaseB_Zprime hcaseB
    have hcaseB_Zcyclic (hcaseB : caseB) : IsCyclic Z := by
      letI : Fact (Nat.Prime (Nat.card Z)) :=
        ⟨hcaseB_Zprime hcaseB⟩
      exact isCyclic_of_prime_card (p := Nat.card Z) rfl
    have hcaseB_ZGcyclic (hcaseB : caseB) : IsCyclic ZG := by
      letI : Fact (Nat.Prime (Nat.card ZG)) :=
        ⟨hcaseB_ZGprime hcaseB⟩
      exact isCyclic_of_prime_card (p := Nat.card ZG) rfl
    have hZGLG : ZG ≤ LG := Subgroup.map_subtype_le ZLG
    have hZGsubLG : ZG.subgroupOf LG = ZLG := by
      change ZG.comap LG.subtype = ZLG
      simpa only [ZG] using
        Subgroup.comap_map_eq_self_of_injective
          LG.subtype_injective ZLG
    have hZGnormal : (ZG.subgroupOf LG).Normal := by
      rw [hZGsubLG]
      exact hZLGnormal
    have hZGne : ZG ≠ ⊥ := by
      intro hbot
      apply hZne
      have hZLGbot : ZLG = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective
          ZLG LG.subtype_injective).mp hbot
      have hZLbot : Z.map K.subtype = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective
          (Z.map K.subtype) eLG.symm.injective).mp hZLGbot
      exact (Subgroup.map_eq_bot_iff_of_injective
        Z K.subtype_injective).mp hZLbot
    have hZGcenterPG : ZG ≤ centerWithin (PG : Subgroup G) := by
      intro z hz
      rcases hz with ⟨zLG, hzLG, rfl⟩
      rcases hzLG with ⟨zL, hzL, rfl⟩
      rcases hzL with ⟨zK, hzK, rfl⟩
      have hzCenter := hZcenter hzK
      rw [Subgroup.mem_center_iff] at hzCenter
      refine ⟨?_, ?_⟩
      · rw [hPG]
        exact zK.property
      · intro x hx
        have hxH : ((x : G) : Gamma) ∈ H := by
          change (x : G) ∈ H.subgroupOf G
          rw [← hPG]
          exact hx
        let xL : L := ⟨((x : G) : Gamma), hHL hxH⟩
        let xK : K := ⟨xL, hxH⟩
        apply Subtype.ext
        change (((xK * zK : K) : L) : Gamma) =
          (((zK * xK : K) : L) : Gamma)
        exact congrArg
          (fun y : K ↦ (((y : K) : L) : Gamma))
          (hzCenter xK)
    have hcaseA_ZGcentralizer
        (hcaseA : caseA) {z : G}
        (hz : z ∈ ZG) (hzOne : z ≠ 1) :
        centralizerWithin LG (Subgroup.zpowers z) =
          H.subgroupOf G := by
      by_cases hc₁ : case_c1
      · simpa only [LG] using
          centralizerWithin_subgroupOf_zpowers_eq_frobeniusKernel
            hLG hHL hc₁
              (by simpa only [hPG] using hZGcenterPG hz) hzOne
      · rcases hW₂c2 hc₁ with
          ⟨_, _, A₀, W, defW, pd⟩
        rcases hz with ⟨zLG, hzLG, rfl⟩
        rcases hzLG with ⟨zL, hzL, rfl⟩
        rcases hzL with ⟨zK, hzK, rfl⟩
        apply le_antisymm
        · intro x hx
          let xL : L := ⟨(x : Gamma), hx.1⟩
          rcases hKW₁.2 xL with ⟨⟨k, r⟩, hkr⟩
          change ((k : K) : L) * ((r : W₁L') : L) = xL at hkr
          have hzk : Commute (zK : K) k := by
            have hzKcenter := hZcenter hzK
            rw [Subgroup.mem_center_iff] at hzKcenter
            rw [commute_iff_eq]
            exact (hzKcenter k).symm
          have hzkL :
              ((zK : K) : L) * ((k : K) : L) =
                ((k : K) : L) * ((zK : K) : L) :=
            congrArg (fun y : K ↦ (y : L)) hzk.eq
          have hxz :
              (xL : L) * ((zK : K) : L) =
                ((zK : K) : L) * (xL : L) := by
            apply Subtype.ext
            exact congrArg (fun y : G ↦ (y : Gamma))
              (hx.2 _ (Subgroup.mem_zpowers _)).symm
          have hrz : Commute (r : L) ((zK : K) : L) := by
            rw [commute_iff_eq]
            apply mul_left_cancel (a := ((k : K) : L))
            calc
              ((k : K) : L) *
                    (((r : W₁L') : L) * ((zK : K) : L)) =
                  ((((k : K) : L) * ((r : W₁L') : L)) *
                    ((zK : K) : L)) := by rw [mul_assoc]
              _ = (xL : L) * ((zK : K) : L) := by rw [hkr]
              _ = ((zK : K) : L) * (xL : L) := hxz
              _ = ((zK : K) : L) *
                    (((k : K) : L) * ((r : W₁L') : L)) := by
                  rw [hkr]
              _ = (((zK : K) : L) * ((k : K) : L)) *
                    ((r : W₁L') : L) := by rw [mul_assoc]
              _ = (((k : K) : L) * ((zK : K) : L)) *
                    ((r : W₁L') : L) := by
                  rw [hzkL]
              _ = ((k : K) : L) *
                    (((zK : K) : L) * ((r : W₁L') : L)) := by
                  rw [mul_assoc]
          have hrOne : r = 1 := by
            by_contra hr
            have hrL : (r : L) ≠ 1 := by
              intro hrOne
              apply hr
              apply Subtype.ext
              exact hrOne
            have hcent :=
              primeTI_centralizerWithin_subgroupOf_zpowers
                pd.prDade_prTI (r : L) r.property hrL
            have hzcent : ((zK : K) : L) ∈ centralizerWithin K
                (Subgroup.zpowers (r : L)) := by
              refine ⟨zK.property, ?_⟩
              intro y hy
              obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
              exact (hrz.zpow_left n).eq
            rw [hcent] at hzcent
            have hzW₂K : zK ∈ W₂K := by
              change (((zK : K) : L) : Gamma) ∈ W₂
              change (((zK : K) : L) : Gamma) ∈ W₂ at hzcent
              exact hzcent
            have hzBot : zK ∈ (⊥ : Subgroup K) :=
              hcaseA ⟨hZcenter hzK, hzW₂K⟩
            apply hzOne
            apply Subtype.ext
            exact congrArg
              (fun y : K ↦ (((y : K) : L) : Gamma))
              (Subgroup.mem_bot.mp hzBot)
          have hkx : (((k : K) : L) : Gamma) = (x : Gamma) := by
            have := congrArg (fun y : L ↦ (y : Gamma)) hkr
            simpa only [hrOne, Subgroup.coe_one, mul_one, xL] using this
          change (x : Gamma) ∈ H
          rw [← hkx]
          exact k.property
        · intro x hxH
          have hxHG : (x : Gamma) ∈ H := by
            change x ∈ H.subgroupOf G at hxH
            exact hxH
          refine ⟨?_, ?_⟩
          · exact hHL hxHG
          · intro y hy
            obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
            have hzComm := (hZGcenterPG
              (Subgroup.mem_map_of_mem LG.subtype
                (Subgroup.mem_map_of_mem eLG.symm.toMonoidHom
                  (Subgroup.mem_map_of_mem K.subtype hzK)))).2 x
            have hxPG : x ∈ (PG : Subgroup G) := by
              rw [hPG]
              exact hxHG
            have hxzComm : Commute x
                (LG.subtype
                  (eLG.symm.toMonoidHom (K.subtype zK))) :=
              hzComm hxPG
            exact (hxzComm.zpow_right n).symm.eq
    have hcaseA_ZGcentralizerCard (hcaseA : caseA) :
        ∀ ⦃x y : G⦄,
          x ∈ ZG → x ≠ 1 → y ∈ ZG → y ≠ 1 →
            Nat.card
                (centralizerWithin LG (Subgroup.zpowers x)) =
              Nat.card
                (centralizerWithin LG (Subgroup.zpowers y)) := by
      intro x y hx hxOne hy hyOne
      rw [hcaseA_ZGcentralizer hcaseA hx hxOne,
        hcaseA_ZGcentralizer hcaseA hy hyOne]
    have hirrZmodH_caseA
        (hcaseA : caseA) (phi : IrreducibleCharacter G ℂ)
        (hconstant : ∀ ⦃x y : G⦄,
          x ∈ ZG → x ≠ 1 → y ∈ ZG → y ≠ 1 →
            phi x = phi y) :
        ∀ ⦃x : G⦄, x ∈ ZG → x ≠ 1 →
          (∃ n : ℤ, phi x = (n : ℂ)) ∧
            IsIntegralModEq (Nat.card PG : ℂ) (phi x) (phi 1) := by
      have hoddLG : Odd (Nat.card LG) := by
        simpa only [LG,
          MathlibSupport.natCard_subgroupOf_eq hLG] using hoddL
      exact constant_irr_mod_TI_Sylow
        PG LG ZG hoddLG
        (by simpa only [LG] using hTIG)
        hZGLG hZGnormal hZGne hZGcenterPG
        (hcaseA_ZGcentralizerCard hcaseA) phi hconstant
    have hirrZmodK_caseA
        (hcaseA : caseA) (phi : IrreducibleCharacter G ℂ)
        (hconstant : ∀ ⦃x y : G⦄,
          x ∈ ZG → x ≠ 1 → y ∈ ZG → y ≠ 1 →
            phi x = phi y) :
        ∀ ⦃x : G⦄, x ∈ ZG → x ≠ 1 →
          (∃ n : ℤ, phi x = (n : ℂ)) ∧
            IsIntegralModEq (Nat.card K : ℂ) (phi x) (phi 1) := by
      simpa only [hPGcard] using
        hirrZmodH_caseA hcaseA phi hconstant
    have hcaseB_ZGcenterLG (hcaseB : caseB) :
        ZG ≤ centerWithin LG := by
      intro z hz
      rcases hz with ⟨zLG, hzLG, rfl⟩
      rcases hzLG with ⟨zL, hzL, rfl⟩
      have hzCenter := hcaseB_ZcenterL hcaseB hzL
      rw [Subgroup.mem_center_iff] at hzCenter
      refine ⟨(eLG.symm zL).property, ?_⟩
      intro x hx
      let xLG : LG := ⟨x, hx⟩
      apply Subtype.ext
      exact congrArg (fun y : L ↦ (y : Gamma))
        (hzCenter (eLG xLG))
    have hcaseB_ZGcentralizer
        (hcaseB : caseB) {z : G} (hz : z ∈ ZG) :
        centralizerWithin LG (Subgroup.zpowers z) = LG := by
      apply le_antisymm
      · exact fun _ hx ↦ hx.1
      · intro x hxLG
        refine ⟨hxLG, ?_⟩
        intro y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hxzComm : Commute x z :=
          (hcaseB_ZGcenterLG hcaseB hz).2 x hxLG
        exact (hxzComm.zpow_right n).symm.eq
    have hirrZmodH_caseB
        (hcaseB : caseB) (phi : IrreducibleCharacter G ℂ)
        (hconstant : ∀ ⦃x y : G⦄,
          x ∈ ZG → x ≠ 1 → y ∈ ZG → y ≠ 1 →
            phi x = phi y) :
        ∀ ⦃x : G⦄, x ∈ ZG → x ≠ 1 →
          (∃ n : ℤ, phi x = (n : ℂ)) ∧
            IsIntegralModEq (Nat.card PG : ℂ) (phi x) (phi 1) := by
      have hoddLG : Odd (Nat.card LG) := by
        simpa only [LG,
          MathlibSupport.natCard_subgroupOf_eq hLG] using hoddL
      apply constant_irr_mod_TI_Sylow
        PG LG ZG hoddLG
        (by simpa only [LG] using hTIG)
        hZGLG hZGnormal hZGne hZGcenterPG
      · intro x y hx hxOne hy hyOne
        rw [hcaseB_ZGcentralizer hcaseB hx,
          hcaseB_ZGcentralizer hcaseB hy]
      · exact hconstant
    have hirrZmodK_caseB
        (hcaseB : caseB) (phi : IrreducibleCharacter G ℂ)
        (hconstant : ∀ ⦃x y : G⦄,
          x ∈ ZG → x ≠ 1 → y ∈ ZG → y ≠ 1 →
            phi x = phi y) :
        ∀ ⦃x : G⦄, x ∈ ZG → x ≠ 1 →
          (∃ n : ℤ, phi x = (n : ℂ)) ∧
            IsIntegralModEq (Nat.card K : ℂ) (phi x) (phi 1) := by
      simpa only [hPGcard] using
        hirrZmodH_caseB hcaseB phi hconstant

    let X : Finset (ClassFunction L ℂ) :=
      seqIndD K Z (⊥ : Subgroup K)
    let Y : Finset (ClassFunction L ℂ) :=
      seqIndD K (⊤ : Subgroup K) D
    have hXcal : cfConjC_subset
        (↑X : Set (ClassFunction L ℂ))
        (↑calS : Set (ClassFunction L ℂ)) := by
      have h := seqInd_conjC_subset1 (k := ℂ) K
        (⊤ : Subgroup K) Z ⊥ le_top
      refine ⟨?_, ?_⟩
      · simpa only [X, calS] using h.1
      · intro phi hphi
        rw [Finset.mem_coe] at hphi ⊢
        have hphi' : phi ∈ seqIndD (k := ℂ) K Z ⊥ := by
          simpa only [X] using hphi
        simpa only [X] using h.2 phi hphi'
    have hYcal : cfConjC_subset
        (↑Y : Set (ClassFunction L ℂ))
        (↑calS : Set (ClassFunction L ℂ)) := by
      have h := seqInd_conjC_subset1 (k := ℂ) K
        (⊤ : Subgroup K) (⊤ : Subgroup K) D le_rfl
      refine ⟨?_, ?_⟩
      · simpa only [Y, calS] using h.1
      · intro phi hphi
        rw [Finset.mem_coe] at hphi ⊢
        have hphi' : phi ∈ seqIndD (k := ℂ) K ⊤ D := by
          simpa only [Y] using hphi
        simpa only [Y] using h.2 phi hphi'
    have hXYcal : cfConjC_subset
        (↑(X ∪ Y) : Set (ClassFunction L ℂ))
        (↑calS : Set (ClassFunction L ℂ)) := by
      constructor
      · intro phi hphi
        rw [Finset.mem_coe, Finset.mem_union] at hphi
        exact hphi.elim
          (fun hphiX ↦ hXcal.1 hphiX)
          (fun hphiY ↦ hYcal.1 hphiY)
      · intro phi hphi
        rw [Finset.mem_coe, Finset.mem_union] at hphi ⊢
        exact hphi.elim
          (fun hphiX ↦ Or.inl (hXcal.2 phi hphiX))
          (fun hphiY ↦ Or.inr (hYcal.2 phi hphiY))
    have hYX : ∀ eta ∈ Y, eta ∉ X := by
      intro eta hetaY hetaX
      obtain ⟨theta, htheta, heta⟩ := seqIndP.mp hetaY
      have hetaX' :
          ClassFunction.induce K (theta : ClassFunction K ℂ) ∈ X := by
        rw [heta] at hetaX
        exact hetaX
      have hthetaX :=
        (mem_seqInd (k := ℂ) K Z ⊥ theta).mp hetaX'
      exact (mem_Iirr_kerD.mp hthetaX).2
        (hZD.trans (mem_Iirr_kerD.mp htheta).1)
    have hXYorth : ∀ xi ∈ X, ∀ eta ∈ Y,
        characterPairing xi eta = 0 := by
      intro xi hxi eta heta
      exact subset_ortho_subcoherent hsub hXcal.1
        (hYcal.1 heta) (hYX eta heta) xi hxi
    have hYirr : ∀ eta ∈ Y,
        IsIrreducibleCharacter L ℂ eta := by
      intro eta heta
      obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp heta
      exact irr_induced_of_Frobenius_quotient K DL hDLproper.le
        hfrobDerived theta
        (by simpa only [hDLsubK] using
          (mem_Iirr_kerD.mp htheta).1)
        (mem_Iirr_kerD.mp htheta).2
    have hYdegree : ∀ eta ∈ Y, eta 1 = (K.index : ℂ) := by
      intro eta heta
      obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp heta
      rw [ClassFunction.induce_one,
        irreducible_degree_one_of_commutator_le_kernel theta
          (mem_Iirr_kerD.mp htheta).1]
      simp
    have hYorthonormal : ∀ eta ∈ Y, ∀ zeta ∈ Y,
        characterPairing eta zeta = if eta = zeta then 1 else 0 := by
      intro eta heta zeta hzeta
      let etaI : IrreducibleCharacter L ℂ := ⟨eta, hYirr eta heta⟩
      let zetaI : IrreducibleCharacter L ℂ := ⟨zeta, hYirr zeta hzeta⟩
      by_cases heq : eta = zeta
      · subst zeta
        simpa only [if_pos rfl] using
          IrreducibleCharacter.characterPairing_eq_ite etaI etaI
      · have hI : etaI ≠ zetaI := by
          intro hEq
          exact heq (congrArg Subtype.val hEq)
        rw [show characterPairing eta zeta = 0 by
          simpa only [etaI, zetaI, if_neg hI] using
            IrreducibleCharacter.characterPairing_eq_ite etaI zetaI,
          if_neg heq]
    have hsubY : subcoherent
        (↑Y : Set (ClassFunction L ℂ)) tau R :=
      subset_subcoherent hsub hYcal
    obtain ⟨tau₁, hcohY⟩ :=
      uniform_degree_coherence hsubY (by
        intro eta heta zeta hzeta
        rw [hYdegree eta heta, hYdegree zeta hzeta])
    obtain ⟨eta₁, heta₁Y⟩ : Y.Nonempty := by
      simpa only [Y] using
        (seqIndD_nonempty (k := ℂ) K
          (⊤ : Subgroup K) D hDtop)
    have heta₁Norm : characterPairing eta₁ eta₁ = 1 := by
      exact hYorthonormal eta₁ heta₁Y eta₁ heta₁Y |>.trans
        (if_pos rfl)
    have hYcardTwo : 2 ≤ Y.card := by
      simpa only [Y] using
        (seqInd_nontrivial (k := ℂ) K hoddL
          (⊤ : Subgroup K) D heta₁Y)
    have hcohYisometry : ∀ phi ∈ AddSubgroup.closure
        (↑Y : Set (ClassFunction L ℂ)),
        ∀ psi ∈ AddSubgroup.closure
          (↑Y : Set (ClassFunction L ℂ)),
          characterPairing (tau₁ phi) (tau₁ psi) =
            characterPairing phi psi :=
      hcohY.isometry
    have hcohYvirtual : ∀ phi ∈ AddSubgroup.closure
        (↑Y : Set (ClassFunction L ℂ)),
        ClassFunction.IsVirtual (tau₁ phi) :=
      hcohY.mapsToVirtual
    have hcohYagree : ∀ phi ∈ AddSubgroup.closure
        (↑Y : Set (ClassFunction L ℂ)),
        phi ∈ ClassFunction.supportedOn (nonidentitySet L) →
          tau₁ phi = tau phi :=
      hcohY.agrees
    have hYtauOrthonormal : ∀ eta ∈ Y, ∀ zeta ∈ Y,
        characterPairing (tau₁ eta) (tau₁ zeta) =
          if eta = zeta then 1 else 0 := by
      intro eta heta zeta hzeta
      rw [hcohYisometry eta (AddSubgroup.subset_closure heta)
        zeta (AddSubgroup.subset_closure hzeta)]
      exact hYorthonormal eta heta zeta hzeta
    have heta₁TauVirtual : ClassFunction.IsVirtual (tau₁ eta₁) :=
      hcohYvirtual eta₁ (AddSubgroup.subset_closure heta₁Y)
    have heta₁TauNorm :
        characterPairing (tau₁ eta₁) (tau₁ eta₁) = 1 := by
      simpa using hYtauOrthonormal eta₁ heta₁Y eta₁ heta₁Y

    have hYcoefficientClosed
        (sigma : ℂ ≃+* ℂ) (eta : ClassFunction L ℂ)
        (heta : eta ∈ Y) :
        ClassFunction.mapRingHom sigma.toRingHom eta ∈ Y := by
      simpa only [Y] using
        cfAut_seqInd (k := ℂ) sigma K
          (⊤ : Subgroup K) D heta

    /- In Case B the coherence on `Y` is also a coherence for the Dade
    isometry.  This is the exact input of `cfAut_Dade_coherent` in source
    lines 969--975; the agreement follows from `Dade_Ind` on the common
    source span. -/
    have hcaseB_coefficient_commutes
        (hcaseB : caseB) (sigma : ℂ ≃+* ℂ)
        (eta : ClassFunction L ℂ) (heta : eta ∈ Y) :
        ClassFunction.mapRingHom sigma.toRingHom (tau₁ eta) =
          tau₁ (ClassFunction.mapRingHom sigma.toRingHom eta) := by
      have hc₂ := hcaseB_c2 hcaseB
      rcases hW₂c2 hc₂ with
          ⟨_, _, A₀, W, defW, pd⟩
      have hcohYDade :
          coherent_with
            (↑Y : Set (ClassFunction L ℂ))
            (nonidentitySet L)
            (Dade pd.prDade_hyp) tau₁ := by
        refine
          { isometry := hcohY.isometry
            mapsToVirtual := hcohY.mapsToVirtual
            agrees := ?_ }
        intro phi hphi hoff
        have hphiCal :
            phi ∈ AddSubgroup.closure
              (↑calS : Set (ClassFunction L ℂ)) :=
          (AddSubgroup.closure_mono hYcal.1) hphi
        have hphiA := hspanA hphiCal hoff
        calc
          tau₁ phi = tau phi := hcohY.agrees phi hphi hoff
          _ = Dade pd.prDade_hyp phi := by
            symm
            calc
              Dade pd.prDade_hyp phi =
                  ClassFunction.induce (L.subgroupOf G)
                    (ClassFunction.toSubgroupOf L G
                      pd.prDade_hyp.2.1 phi) :=
                pd.Dade_Ind_on_smallSet hTI phi hphiA
              _ = tau phi := by rfl
      have hetaInvY :
          ClassFunction.inverseLinear eta ∈ Y := by
        simpa only [Y] using
          (seqInd_inverse_mem (k := ℂ) K
            (⊤ : Subgroup K) D heta)
      have hetaInvNe :
          ClassFunction.inverseLinear eta ≠ eta := by
        apply seqInd_conjC_neq (k := ℂ) K hoddL
          (⊤ : Subgroup K) D
        simpa only [Y] using heta
      let etaI : IrreducibleCharacter L ℂ :=
        ⟨eta, hYirr eta heta⟩
      let etaInvI : IrreducibleCharacter L ℂ :=
        ⟨ClassFunction.inverseLinear eta,
          hYirr (ClassFunction.inverseLinear eta) hetaInvY⟩
      have hetaIY :
          (etaI : ClassFunction L ℂ) ∈
            (↑Y : Set (ClassFunction L ℂ)) := by
        change eta ∈ Y
        exact heta
      have hetaInvIY :
          (etaInvI : ClassFunction L ℂ) ∈
            (↑Y : Set (ClassFunction L ℂ)) := by
        change ClassFunction.inverseLinear eta ∈ Y
        exact hetaInvY
      have hetaInvINe : etaInvI ≠ etaI := by
        intro heq
        apply hetaInvNe
        exact congrArg Subtype.val heq
      have hcomm :=
        cfAut_Dade_coherent pd.prDade_hyp hcohYDade
          sigma etaI hetaIY
          ⟨etaInvI, hetaInvIY, hetaInvINe⟩
          (by
            intro phi hphi
            exact hYcoefficientClosed sigma phi hphi)
      calc
        ClassFunction.mapRingHom sigma.toRingHom (tau₁ eta) =
            tau₁
              (IrreducibleCharacter.mapRingEquiv sigma etaI :
                ClassFunction L ℂ) := by
          simpa only [etaI] using hcomm
        _ = tau₁ (ClassFunction.mapRingHom sigma.toRingHom eta) := by
          apply congrArg tau₁
          exact
            (ClassFunction.mapRingHom_irreducible sigma etaI).symm

    /- The second input to the Case-B automorphism calculation is the
    pointwise Dade identity on the central prime section.  The element of
    `Z` lies in the smaller Dade set because it is a nonidentity element of
    `H` commuting with itself. -/
    have hcaseB_dade_twist_vanishes
        (hcaseB : caseB) (sigma : ℂ ≃+* ℂ)
        (eta : ClassFunction L ℂ) (heta : eta ∈ Y) :
        ∀ z : Z, z ≠ 1 →
          tau₁
              (eta -
                ClassFunction.mapRingHom sigma.toRingHom eta)
              (zToG z) = 0 := by
      intro z hz
      have hc₂ := hcaseB_c2 hcaseB
      rcases hW₂c2 hc₂ with
          ⟨_, _, A₀, W, defW, pd⟩
      obtain ⟨theta, htheta, hetaInd⟩ :=
        seqIndP.mp heta
      let ZL : Subgroup L := Z.map K.subtype
      have hZLsubK : ZL ≤ K := by
        simpa only [ZL] using Subgroup.map_subtype_le Z
      have hZLsubgroup : ZL.subgroupOf K = Z := by
        change (Z.map K.subtype).comap K.subtype = Z
        exact Subgroup.comap_map_eq_self_of_injective
          K.subtype_injective Z
      letI : ZL.Normal := by
        simpa only [ZL] using hZmapNormal
      have hthetaZ :
          Z ≤ ClassFunction.translationKernel
            (theta : ClassFunction K ℂ) :=
        hZD.trans (mem_Iirr_kerD.mp htheta).1
      have hthetaZL :
          ZL.subgroupOf K ≤
            ClassFunction.translationKernel
              (theta : ClassFunction K ℂ) := by
        rw [hZLsubgroup]
        exact hthetaZ
      have hetaKernel :
          ZL ≤ ClassFunction.translationKernel
            (ClassFunction.induce K
              (theta : ClassFunction K ℂ) :
                ClassFunction L ℂ) :=
        ClassFunction.le_translationKernel_induce
          ZL K hZLsubK (theta : ClassFunction K ℂ)
            hthetaZL
      have hzZL : (((z : Z) : K) : L) ∈ ZL := by
        exact ⟨(z : K), z.property, rfl⟩
      have hetaZ : eta (((z : Z) : K) : L) = eta 1 := by
        rw [hetaInd]
        simpa using hetaKernel hzZL (1 : L)
      let diff : ClassFunction L ℂ :=
        eta - ClassFunction.mapRingHom sigma.toRingHom eta
      have hdiffSpan :
          diff ∈ AddSubgroup.closure
            (↑Y : Set (ClassFunction L ℂ)) := by
        exact
          (AddSubgroup.closure
            (↑Y : Set (ClassFunction L ℂ))).sub_mem
              (AddSubgroup.subset_closure heta)
              (AddSubgroup.subset_closure
                (hYcoefficientClosed sigma eta heta))
      have hdiffOff :
          diff ∈ ClassFunction.supportedOn
            (nonidentitySet L) := by
        rw [ClassFunction.mem_supportedOn_iff]
        intro x hx
        have hxOne : x = 1 := by
          simpa [nonidentitySet] using not_not.mp hx
        subst x
        simp only [diff, ClassFunction.sub_apply,
          ClassFunction.mapRingHom_apply]
        rw [hYdegree eta heta, map_natCast, sub_self]
      have hdiffCal :
          diff ∈ AddSubgroup.closure
            (↑calS : Set (ClassFunction L ℂ)) :=
        (AddSubgroup.closure_mono hYcal.1) hdiffSpan
      have hdiffA := hspanA hdiffCal hdiffOff
      have htauDade :
          tau₁ diff = Dade pd.prDade_hyp diff := by
        calc
          tau₁ diff = tau diff :=
            hcohY.agrees diff hdiffSpan hdiffOff
          _ = Dade pd.prDade_hyp diff := by
            symm
            calc
              Dade pd.prDade_hyp diff =
                  ClassFunction.induce (L.subgroupOf G)
                    (ClassFunction.toSubgroupOf L G
                      pd.prDade_hyp.2.1 diff) :=
                pd.Dade_Ind_on_smallSet hTI diff hdiffA
              _ = tau diff := by rfl
      let zGamma : Gamma := (((z : Z) : K) : L)
      have hzH : zGamma ∈ H := by
        exact (z : K).property
      have hzGammaNe : zGamma ≠ 1 := by
        intro hzOne
        apply hz
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact hzOne
      have hzCentralizerSupport :
          zGamma ∈ primeDadeCentralizerSupport H H := by
        exact ⟨hzH, hzGammaNe, zGamma, hzH,
          hzGammaNe, Commute.refl zGamma⟩
      have hzA₀ : zGamma ∈ A₀ :=
        pd.set_subset_dadeSet
          (pd.prDade_def.centralizerSupport_le
            hzCentralizerSupport)
      have hDadeAt := Dade_id pd.prDade_hyp diff hzA₀
      let zG : G := ⟨zGamma, hLG (hHL hzH)⟩
      let zL : L := ⟨zGamma, hHL hzH⟩
      have hzToGEq : zToG z = zG := by
        apply Subtype.ext
        rfl
      have hzSourceEq : (((z : Z) : K) : L) = zL := by
        apply Subtype.ext
        rfl
      have hsourceZero : diff (((z : Z) : K) : L) = 0 := by
        simp only [diff, ClassFunction.sub_apply,
          ClassFunction.mapRingHom_apply]
        rw [hetaZ, hYdegree eta heta, map_natCast, sub_self]
      rw [show
        tau₁
            (eta - ClassFunction.mapRingHom sigma.toRingHom eta) =
          tau₁ diff by rfl, htauDade]
      calc
        Dade pd.prDade_hyp diff (zToG z) =
            Dade pd.prDade_hyp diff zG := by rw [hzToGEq]
        _ = diff zL := by
          simpa only [zG, zL] using hDadeAt
        _ = diff (((z : Z) : K) : L) := by rw [hzSourceEq]
        _ = 0 := hsourceZero

    have hcaseB_ZpowerTransitive (hcaseB : caseB) :
        ∀ (x y : Z), x ≠ 1 → y ≠ 1 →
          ∃ k : ℕ,
            k.Coprime (Nat.card Z) ∧ y = x ^ k := by
      intro x y hx hy
      have hxOrderDvd : orderOf x ∣ Nat.card Z :=
        orderOf_dvd_natCard x
      have hxOrder : orderOf x = Nat.card Z := by
        rcases (Nat.dvd_prime
          (hcaseB_Zprime hcaseB)).mp hxOrderDvd with
          hxOne | hxFull
        · exact (hx (orderOf_eq_one_iff.mp hxOne)).elim
        · exact hxFull
      have hxPowersTop : Subgroup.zpowers x = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [Nat.card_zpowers, hxOrder]
      have hyPower :
          y ∈ (Finset.range (orderOf x)).image (x ^ ·) := by
        rw [← mem_zpowers_iff_mem_range_orderOf,
          hxPowersTop]
        exact Subgroup.mem_top y
      rcases Finset.mem_image.mp hyPower with
          ⟨k, hkRange, hky⟩
      have hkLt : k < Nat.card Z := by
        rw [Finset.mem_range, hxOrder] at hkRange
        exact hkRange
      have hkPos : 0 < k := by
        by_contra hk
        have hkZero : k = 0 := Nat.eq_zero_of_not_pos hk
        apply hy
        rw [← hky, hkZero, pow_zero]
      have hkNotDvd : ¬Nat.card Z ∣ k :=
        Nat.not_dvd_of_pos_of_lt hkPos hkLt
      have hkCoprime : (Nat.card Z).Coprime k :=
        (hcaseB_Zprime hcaseB).coprime_iff_not_dvd.mpr
          hkNotDvd
      exact ⟨k, hkCoprime.symm, hky.symm⟩

    have hXcharacterizationSource
        (theta : IrreducibleCharacter K ℂ) :
        (ClassFunction.induce K
              (theta : ClassFunction K ℂ) ∈ X ↔
          ¬ Z ≤ ClassFunction.translationKernel
            (theta : ClassFunction K ℂ)) := by
      simpa only [X, mem_Iirr_kerD, bot_le, true_and] using
        (mem_seqInd (k := ℂ) K Z
          (⊥ : Subgroup K) theta)

    /- The integral span assertion needed in Case B is obtained before any
    target calculation.  Induction of the basis character of `Z` is an
    integral combination of irreducibles of `K`; every nonzero coefficient
    lies outside the `Z`-kernel layer by Frobenius reciprocity. -/
    have hinduceVirtual_mem_X_span
        (v : VirtualCharacter K ℂ)
        (hv : ∀ theta : IrreducibleCharacter K ℂ,
          v theta ≠ 0 →
            ClassFunction.induce K
                (theta : ClassFunction K ℂ) ∈ X) :
        ClassFunction.induce K (VirtualCharacter.realize v) ∈
          AddSubgroup.closure
            (↑X : Set (ClassFunction L ℂ)) := by
      induction v using Finsupp.induction with
      | zero => simp
      | @single_add theta n v htheta hn ih =>
          have hvtheta : v theta = 0 :=
            Finsupp.notMem_support_iff.mp htheta
          have hthetaX :
              ClassFunction.induce K
                  (theta : ClassFunction K ℂ) ∈ X := by
            apply hv theta
            simp only [Finsupp.add_apply,
              Finsupp.single_eq_same, hvtheta, add_zero]
            exact hn
          have hvTail : ∀ psi : IrreducibleCharacter K ℂ,
              v psi ≠ 0 →
                ClassFunction.induce K
                    (psi : ClassFunction K ℂ) ∈ X := by
            intro psi hpsi
            apply hv psi
            by_cases hpsiTheta : psi = theta
            · subst psi
              exact (hpsi hvtheta).elim
            · simpa only [Finsupp.add_apply,
                Finsupp.single_eq_of_ne hpsiTheta, zero_add] using hpsi
          rw [VirtualCharacter.realize_add, map_add]
          apply (AddSubgroup.closure
            (↑X : Set (ClassFunction L ℂ))).add_mem
          · rw [VirtualCharacter.realize_single, map_smul]
            have hnmem := (AddSubgroup.closure
              (↑X : Set (ClassFunction L ℂ))).zsmul_mem
                (AddSubgroup.subset_closure hthetaX) n
            rwa [← Int.cast_smul_eq_zsmul ℂ] at hnmem
          · exact ih hvTail

    let centralInduce :
        IrreducibleCharacter Z ℂ → ClassFunction L ℂ :=
      fun i ↦ ClassFunction.induce K
        (ClassFunction.induce Z (i : ClassFunction Z ℂ))
    have hcentralInduceVirtual
        (i : IrreducibleCharacter Z ℂ) :
        ClassFunction.IsVirtual (centralInduce i) := by
      let vZ : VirtualCharacter Z ℂ := Finsupp.single i 1
      let vK : VirtualCharacter K ℂ :=
        VirtualCharacter.induce Z vZ
      let vL : VirtualCharacter L ℂ :=
        VirtualCharacter.induce K vK
      refine ⟨vL, ?_⟩
      rw [VirtualCharacter.realize_induce,
        VirtualCharacter.realize_induce,
        VirtualCharacter.realize_single]
      simp only [Int.cast_one, one_smul, centralInduce, vL, vK, vZ]
    have hcentralInduceMemXSpan
        (i : IrreducibleCharacter Z ℂ)
        (hi : i ≠ IrreducibleCharacter.trivial) :
        centralInduce i ∈
          AddSubgroup.closure
            (↑X : Set (ClassFunction L ℂ)) := by
      let vZ : VirtualCharacter Z ℂ := Finsupp.single i 1
      let vK : VirtualCharacter K ℂ :=
        VirtualCharacter.induce Z vZ
      have hrealizeK :
          VirtualCharacter.realize vK =
            ClassFunction.induce Z
              (i : ClassFunction Z ℂ) := by
        rw [show vK = VirtualCharacter.induce Z vZ by rfl,
          VirtualCharacter.realize_induce]
        simp only [vZ, VirtualCharacter.realize_single,
          Int.cast_one, one_smul]
      have hvSupport
          (theta : IrreducibleCharacter K ℂ)
          (htheta : vK theta ≠ 0) :
          ClassFunction.induce K
              (theta : ClassFunction K ℂ) ∈ X := by
        apply (hXcharacterizationSource theta).2
        intro hZtheta
        have hpairTheta :
            characterPairing
                (theta : ClassFunction K ℂ)
                (ClassFunction.induce Z
                  (i : ClassFunction Z ℂ)) ≠ 0 := by
          intro hzero
          apply htheta
          apply Int.cast_injective (α := ℂ)
          rw [← VirtualCharacter.characterPairing_irreducible_realize
            theta vK, hrealizeK, hzero, Int.cast_zero]
        have hpair :
            characterPairing
                (ClassFunction.induce Z
                  (i : ClassFunction Z ℂ))
                (theta : ClassFunction K ℂ) ≠ 0 := by
          rw [characterPairing_comm]
          exact hpairTheta
        have hrestrict :
            ClassFunction.restrict Z
                (theta : ClassFunction K ℂ) =
              theta 1 •
                ((IrreducibleCharacter.trivial :
                    IrreducibleCharacter Z ℂ) :
                  ClassFunction Z ℂ) := by
          ext z
          simp only [ClassFunction.restrict_apply,
            ClassFunction.smul_apply,
            IrreducibleCharacter.trivial_apply, mul_one]
          have hz := hZtheta z.property (1 : K)
          simpa using hz
        apply hpair
        rw [ClassFunction.frobeniusReciprocity, hrestrict,
          characterPairing_smul_right,
          IrreducibleCharacter.characterPairing_eq_ite,
          if_neg hi, mul_zero]
      have hspan := hinduceVirtual_mem_X_span vK hvSupport
      rw [hrealizeK] at hspan
      simpa only [centralInduce] using hspan
    have hcaseB_centralInduceOne
        (hcaseB : caseB) (i : IrreducibleCharacter Z ℂ) :
        centralInduce i 1 =
          ((K.index * Z.index : ℕ) : ℂ) := by
      letI : IsCyclic Z := hcaseB_Zcyclic hcaseB
      dsimp only [centralInduce]
      rw [ClassFunction.induce_one,
        ClassFunction.induce_one,
        IrreducibleCharacter.apply_one_eq_one_of_isCyclic]
      push_cast
      ring
    have hcaseB_centralInduceSelf
        (hcaseB : caseB) (i : IrreducibleCharacter Z ℂ) :
        characterPairing (centralInduce i) (centralInduce i) =
          ((K.index * Z.index : ℕ) : ℂ) := by
      let ZL : Subgroup L := Z.map K.subtype
      have hZLsubK : ZL ≤ K := by
        simpa only [ZL] using Subgroup.map_subtype_le Z
      have hZLsubgroup : ZL.subgroupOf K = Z := by
        change (Z.map K.subtype).comap K.subtype = Z
        exact Subgroup.comap_map_eq_self_of_injective
          K.subtype_injective Z
      let eJZ : ZL.subgroupOf K ≃* Z :=
        MulEquiv.subgroupCongr hZLsubgroup
      let iK : IrreducibleCharacter (ZL.subgroupOf K) ℂ :=
        IrreducibleCharacter.comapMulEquiv eJZ i
      let eZL : ZL.subgroupOf K ≃* ZL :=
        Subgroup.subgroupOfEquivOfLe hZLsubK
      let iL : IrreducibleCharacter ZL ℂ :=
        IrreducibleCharacter.comapMulEquiv eZL.symm iK
      have hiTransport :
          ClassFunction.toSubgroupOf ZL K hZLsubK
              (iL : ClassFunction ZL ℂ) =
            (iK : ClassFunction (ZL.subgroupOf K) ℂ) := by
        ext z
        simp only [ClassFunction.toSubgroupOf_apply, iL,
          IrreducibleCharacter.comapMulEquiv_apply, eZL,
          MulEquiv.symm_apply_apply]
      have hinner :
          ClassFunction.induce (ZL.subgroupOf K)
              (iK : ClassFunction (ZL.subgroupOf K) ℂ) =
            ClassFunction.induce Z
              (i : ClassFunction Z ℂ) := by
        simpa only [iK, eJZ] using
          induce_comapMulEquiv_subgroupCongr
            (ZL.subgroupOf K) Z hZLsubgroup i
      have hdirect :
          centralInduce i =
            ClassFunction.induce ZL
              (iL : ClassFunction ZL ℂ) := by
        calc
          centralInduce i =
              ClassFunction.induce K
                (ClassFunction.induce Z
                  (i : ClassFunction Z ℂ)) := rfl
          _ = ClassFunction.induce K
                (ClassFunction.induce (ZL.subgroupOf K)
                  (iK : ClassFunction (ZL.subgroupOf K) ℂ)) :=
            congrArg (ClassFunction.induce K) hinner.symm
          _ = ClassFunction.induce K
                (ClassFunction.induce (ZL.subgroupOf K)
                  (ClassFunction.toSubgroupOf ZL K hZLsubK
                    (iL : ClassFunction ZL ℂ))) := by
            apply congrArg (ClassFunction.induce K)
            apply congrArg
              (ClassFunction.induce (ZL.subgroupOf K))
            exact hiTransport.symm
          _ = ClassFunction.induce ZL
                (iL : ClassFunction ZL ℂ) :=
            ClassFunction.induce_trans ZL K hZLsubK
              (iL : ClassFunction ZL ℂ)
      letI : ZL.Normal := by
        simpa only [ZL] using hZmapNormal
      have hinertia :
          ClassFunction.inertia ZL
              (iL : ClassFunction ZL ℂ) = ⊤ := by
        apply top_unique
        intro x _hx
        rw [ClassFunction.mem_inertia_iff]
        ext z
        simp only [ClassFunction.normalConjugate_apply]
        apply congrArg iL
        apply Subtype.ext
        rw [MulAut.conjNormal_symm_apply]
        have hzCentral := hcaseB_ZcenterL hcaseB z.property
        rw [Subgroup.mem_center_iff] at hzCentral
        calc
          x⁻¹ * (z : L) * x =
              x⁻¹ * ((z : L) * x) := by rw [mul_assoc]
          _ = x⁻¹ * (x * (z : L)) := by
            rw [hzCentral x]
          _ = (z : L) := by simp
      have hinertiaIndex :
          ClassFunction.inertiaIndex ZL
              (iL : ClassFunction ZL ℂ) = ZL.index := by
        rw [ClassFunction.inertiaIndex, hinertia]
        rw [Subgroup.card_top, ← ZL.index_mul_card]
        rw [Nat.mul_comm ZL.index (Nat.card ZL)]
        exact Nat.mul_div_right _ Nat.card_pos
      rw [hdirect]
      calc
        characterPairing
              (ClassFunction.induce ZL
                (iL : ClassFunction ZL ℂ))
              (ClassFunction.induce ZL
                (iL : ClassFunction ZL ℂ)) =
            (ZL.index : ℂ) := by
          rw [ClassFunction.cfnorm_Ind_irr, hinertiaIndex]
        _ = ((K.index * Z.index : ℕ) : ℂ) := by
          congr 1
          simpa only [ZL, Subgroup.index_map_subtype,
            mul_comm]
    have hcentralInducePairing
        (i : IrreducibleCharacter Z ℂ)
        (g : ClassFunction G ℂ) :
        characterPairing (tau (centralInduce i)) g =
          characterPairing (i : ClassFunction Z ℂ)
            (ClassFunction.comap zToG g) := by
      calc
        characterPairing (tau (centralInduce i)) g =
            characterPairing (centralInduce i)
              (ClassFunction.comap embedLtoG g) := by
          simpa only [tau, embedLtoG, LG, eLG] using
            sibleyInduce_frobeniusReciprocity G L hLG
              (centralInduce i) g
        _ = characterPairing (i : ClassFunction Z ℂ)
              (ClassFunction.comap zToG g) := by
          dsimp only [centralInduce]
          rw [ClassFunction.frobeniusReciprocity,
            ClassFunction.frobeniusReciprocity]
          apply congrArg
            (characterPairing (i : ClassFunction Z ℂ))
          ext z
          simp only [ClassFunction.restrict_apply,
            ClassFunction.comap_apply, zToG,
            MonoidHom.comp_apply]
          rfl

    have hXirr_c1 (hc1 : case_c1) : ∀ xi ∈ X,
        IsIrreducibleCharacter L ℂ xi := by
      intro xi hxi
      obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp hxi
      have hthetaNe :
          theta ≠ IrreducibleCharacter.trivial := by
        intro htriv
        apply (mem_Iirr_kerD.mp htheta).2
        rw [htriv]
        intro x _ g
        simp
      exact irr_induced_Frobenius_ker hc1 theta hthetaNe

    have hXirr_caseA (hcaseA : caseA) : ∀ xi ∈ X,
        IsIrreducibleCharacter L ℂ xi := by
      by_cases hc1 : case_c1
      · exact hXirr_c1 hc1
      rcases hW₂c2 hc1 with
        ⟨hW₂prime, _, A₀, W, defW, pd⟩
      let pti := pd.prDade_prTI
      let iso : CyclicTIIsometryData (k := ℂ)
          pti.prime_cycTIhyp :=
        pti.prime_cycTIhyp.cyclicTIIsometryData
      have hW₂Kne : W₂K ≠ ⊥ := by
        have hprimeK : Nat.Prime (Nat.card W₂K) := by
          simpa only [hW₂Kcard] using hW₂prime
        exact W₂K.one_lt_card_iff_ne_bot.mp hprimeK.one_lt
      have hW₂KnotZ : ¬ W₂K ≤ Z := by
        intro hW₂Z
        apply hW₂Kne
        apply le_antisymm _ bot_le
        intro w hw
        exact hcaseA ⟨hZcenter (hW₂Z hw), hw⟩
      have hZLsubK :
          (Z.map K.subtype).subgroupOf K = Z := by
        change (Z.map K.subtype).comap K.subtype = Z
        exact Subgroup.comap_map_eq_self_of_injective
          K.subtype_injective Z
      let ZL : Subgroup L := Z.map K.subtype
      let ZΓ : Subgroup Gamma := ZL.map L.subtype
      have hZΓL : ZΓ ≤ L := by
        exact Subgroup.map_subtype_le ZL
      have hZΓsubL : ZΓ.subgroupOf L = ZL := by
        apply Subgroup.map_injective L.subtype_injective
        rw [Subgroup.map_subgroupOf_eq_of_le hZΓL]
      letI : (ZΓ.subgroupOf L).Normal := by
        rw [hZΓsubL]
        exact hZmapNormal
      have hZΓH : ZΓ ≤ H := by
        rintro z ⟨zL, hzL, rfl⟩
        rcases hzL with ⟨zK, hzK, rfl⟩
        exact zK.property
      let Q := primeTIQuotientGroup L ZΓ
      let q : L →* Q := QuotientGroup.mk' (ZΓ.subgroupOf L)
      let W₂q : Subgroup Q := primeTIQuotientImage L ZΓ W₂
      have hW₂qne : W₂q ≠ ⊥ := by
        intro hbot
        have hW₂LZL : W₂.subgroupOf L ≤ ZL := by
          have hle :=
            (Subgroup.map_eq_bot_iff
              (W₂.subgroupOf L)).mp (by
              simpa only [W₂q, primeTIQuotientImage, q] using hbot)
          simpa only [q, QuotientGroup.ker_mk', hZΓsubL] using hle
        apply hW₂KnotZ
        intro w hw
        rw [← hZLsubK]
        exact hW₂LZL hw
      obtain ⟨defWq, ptiq⟩ :=
        PrimeTIHypothesis.quotient pti ZΓ hZΓH hW₂qne
      let isoq : CyclicTIIsometryData (k := ℂ)
          ptiq.prime_cycTIhyp :=
        ptiq.prime_cycTIhyp.cyclicTIIsometryData
      let Kq : Subgroup Q := primeTIQuotientImage L ZΓ H
      let KqT : Subgroup (⊤ : Subgroup Q) :=
        Kq.subgroupOf (⊤ : Subgroup Q)
      let qT : L →* (⊤ : Subgroup Q) :=
        { toFun := fun x ↦ ⟨q x, Subgroup.mem_top _⟩
          map_one' := by
            apply Subtype.ext
            exact q.map_one
          map_mul' := by
            intro x y
            apply Subtype.ext
            exact q.map_mul x y }
      have hqTsurj : Function.Surjective qT := by
        intro y
        obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
          (ZΓ.subgroupOf L) (y : Q)
        exact ⟨x, Subtype.ext hx⟩
      have hqTkerK : qT.ker ≤ K := by
        intro x hx
        have hxq : q x = 1 := congrArg Subtype.val
          (MonoidHom.mem_ker.mp hx)
        have hxZ : x ∈ ZΓ.subgroupOf L :=
          (QuotientGroup.eq_one_iff x).mp hxq
        rw [hZΓsubL] at hxZ
        exact Subgroup.map_subtype_le Z hxZ
      have hKT : K.map qT = KqT := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, hxy⟩
          exact ⟨x, hx, Subtype.ext hxy⟩
      let eKT : K.map qT ≃* KqT :=
        MulEquiv.subgroupCongr hKT
      let qK : K →* K.map qT := qT.subgroupMap K
      have hqKsurj : Function.Surjective qK :=
        qT.subgroupMap_surjective K
      let thetaQ (j : IrreducibleCharacter W₂q ℂ) :
          IrreducibleCharacter KqT ℂ :=
        ptiq.primeTI_Ires isoq j
      let thetaMap (j : IrreducibleCharacter W₂q ℂ) :
          IrreducibleCharacter (K.map qT) ℂ :=
        IrreducibleCharacter.comapMulEquiv eKT (thetaQ j)
      let thetaLift (j : IrreducibleCharacter W₂q ℂ) :
          IrreducibleCharacter K ℂ :=
        IrreducibleCharacter.comapSurjective qK hqKsurj (thetaMap j)
      have hthetaLiftClass
          (j : IrreducibleCharacter W₂q ℂ) :
          ClassFunction.comap qK
              (thetaMap j : ClassFunction (K.map qT) ℂ) =
            (thetaLift j : ClassFunction K ℂ) := by
        ext x
        exact (IrreducibleCharacter.comapSurjective_apply
          qK hqKsurj (thetaMap j) x).symm
      have hliftSelected
          (j : IrreducibleCharacter W₂q ℂ) :
          ∃ r : IrreducibleCharacter W₂ ℂ,
            thetaLift j = pti.primeTI_Ires iso r := by
        rcases pti.prTIres_irr_cases iso (thetaLift j) with
          hselected | hind
        · exact hselected
        exfalso
        have hcomapIrr : IsIrreducibleCharacter
            L ℂ
            (ClassFunction.comap qT
              (ClassFunction.induce (K.map qT)
                (thetaMap j : ClassFunction (K.map qT) ℂ))) := by
          rw [ClassFunction.comap_induce_surjective qT hqTsurj K
            hqTkerK, hthetaLiftClass]
          exact hind.1
        have hmapIrr : IsIrreducibleCharacter
            (⊤ : Subgroup Q) ℂ
            (ClassFunction.induce (K.map qT)
              (thetaMap j : ClassFunction (K.map qT) ℂ)) :=
          irreducible_of_comap_surjective qT hqTsurj _ hcomapIrr
        have hredIrr : IsIrreducibleCharacter
            (⊤ : Subgroup Q) ℂ (ptiq.primeTIRed isoq j) := by
          rw [← ptiq.cfInd_prTIres isoq j]
          have hindTransport :
              ClassFunction.induce (K.map qT)
                  (thetaMap j : ClassFunction (K.map qT) ℂ) =
                ClassFunction.induce KqT
                  (thetaQ j : ClassFunction KqT ℂ) := by
            simpa only [thetaMap, eKT] using
              induce_comapMulEquiv_subgroupCongr
                (K.map qT) KqT hKT (thetaQ j)
          rw [← hindTransport]
          exact hmapIrr
        exact ptiq.prTIred_not_irr isoq j hredIrr
      let selectedMap : IrreducibleCharacter W₂q ℂ →
          IrreducibleCharacter W₂ ℂ := fun j ↦
        Classical.choose (hliftSelected j)
      have hselectedMap
          (j : IrreducibleCharacter W₂q ℂ) :
          thetaLift j = pti.primeTI_Ires iso (selectedMap j) :=
        Classical.choose_spec (hliftSelected j)
      have hselectedMapInj : Function.Injective selectedMap := by
        intro i j hij
        have hlift : thetaLift i = thetaLift j := by
          rw [hselectedMap i, hselectedMap j, hij]
        have hmap : thetaMap i = thetaMap j := by
          apply IrreducibleCharacter.ext
          intro y
          obtain ⟨x, rfl⟩ := hqKsurj y
          have hvalue := congrArg
            (fun chi : IrreducibleCharacter K ℂ ↦ chi x) hlift
          simpa only [thetaLift,
            IrreducibleCharacter.comapSurjective_apply] using hvalue
        have hQ : thetaQ i = thetaQ j := by
          apply IrreducibleCharacter.ext
          intro y
          have hvalue := congrArg
            (fun chi : IrreducibleCharacter (K.map qT) ℂ ↦
              chi (eKT.symm y)) hmap
          simpa only [thetaMap,
            IrreducibleCharacter.comapMulEquiv_apply,
            eKT.apply_symm_apply] using hvalue
        exact ptiq.prTIres_inj isoq hQ
      have hW₂qcard : Nat.card W₂q = Nat.card W₂ := by
        have hdiv : Nat.card W₂q ∣ Nat.card W₂ := by
          simpa only [W₂q, primeTIQuotientImage,
            MathlibSupport.natCard_subgroupOf_eq hW₂L] using
              Subgroup.card_map_dvd (W₂.subgroupOf L) q
        exact ((Nat.dvd_prime hW₂prime).mp hdiv).resolve_left
          (fun hcard ↦ hW₂qne (Subgroup.card_eq_one.mp hcard))
      letI : IsCyclic W₂ := pti.fixed_cyclic
      letI : IsCyclic W₂q := ptiq.fixed_cyclic
      have hselectedCard :
          Fintype.card (IrreducibleCharacter W₂q ℂ) =
            Fintype.card (IrreducibleCharacter W₂ ℂ) := by
        rw [IrreducibleCharacter.card_eq_natCard_of_isCyclic,
          IrreducibleCharacter.card_eq_natCard_of_isCyclic,
          hW₂qcard]
      have hselectedMapSurj : Function.Surjective selectedMap :=
        ((Fintype.bijective_iff_injective_and_card selectedMap).mpr
          ⟨hselectedMapInj, hselectedCard⟩).2
      have hselectedZ (r : IrreducibleCharacter W₂ ℂ) :
          Z ≤ ClassFunction.translationKernel
            (pti.primeTI_Ires iso r : ClassFunction K ℂ) := by
        obtain ⟨j, hj⟩ := hselectedMapSurj r
        have hliftZ : Z ≤ ClassFunction.translationKernel
            (thetaLift j : ClassFunction K ℂ) := by
          intro z hz x
          have hzqK : qK z = 1 := by
            apply Subtype.ext
            apply Subtype.ext
            apply (QuotientGroup.eq_one_iff (z : L)).mpr
            rw [hZΓsubL]
            exact ⟨z, hz, rfl⟩
          simp only [thetaLift,
            IrreducibleCharacter.comapSurjective_apply, map_mul,
            hzqK, one_mul]
        rw [hselectedMap j, hj] at hliftZ
        exact hliftZ
      intro xi hxi
      obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp hxi
      rcases pti.prTIres_irr_cases iso theta with
        ⟨j, hj⟩ | hind
      · exact ((mem_Iirr_kerD.mp htheta).2
          (hj.symm ▸ hselectedZ j)).elim
      · exact hind.1
    have hcaseA_Xdata (hcaseA : caseA) :
        (↑X : Set (ClassFunction L ℂ)) =
            {phi | ∃ chi : IrreducibleCharacter L ℂ,
              phi = (chi : ClassFunction L ℂ) ∧
                ¬ Z.map K.subtype ≤
                  ClassFunction.translationKernel phi} ∧
          coherent (↑X : Set (ClassFunction L ℂ))
            (nonidentitySet L) tau := by
      simpa only [X] using
        seqIndD_irr_coherence K tau R hsub hfq Z
          hZne hZcenter (hXirr_caseA hcaseA)
    have hcohX_caseA (hcaseA : caseA) :
        coherent (↑X : Set (ClassFunction L ℂ))
          (nonidentitySet L) tau :=
      (hcaseA_Xdata hcaseA).2

    have hcaseA_alignment
        (hcaseA : caseA) :
        ∀ (tau₂ :
              ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
            (_ : coherent_with
              (↑X : Set (ClassFunction L ℂ))
              (nonidentitySet L) tau tau₂)
            (xi₁ : ClassFunction L ℂ) (_ : xi₁ ∈ X)
            (_ : ∀ xi ∈ X, ∃ b : ℕ,
              xi 1 = (b : ℂ) * xi₁ 1)
            (a : ℕ)
            (_ : xi₁ 1 = (a : ℂ) * eta₁ 1),
          ∃ (tauX tauY :
              ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ),
            (tauX = tau₂ ∨
              (X.card ≤ 2 ∧ tauX = dual_iso tau₂)) ∧
            (tauY = tau₁ ∨
              (Y.card ≤ 2 ∧ tauY = dual_iso tau₁)) ∧
            tau (xi₁ - (a : ℂ) • eta₁) =
              tauX xi₁ - (a : ℂ) • tauY eta₁ := by
      intro tau₂ hcohX xi₁ hxi₁X hdiv a hdegree
      let ZL : Subgroup L := Z.map K.subtype
      have hZLnormal : ZL.Normal := by
        simpa only [ZL] using hZmapNormal
      have hZLne : ZL ≠ ⊥ := by
        intro hbot
        apply hZne
        exact (Subgroup.map_eq_bot_iff_of_injective Z
          K.subtype_injective).mp (by simpa only [ZL] using hbot)
      have hZLcenter : ZL ≤ centerWithin K := by
        rintro z ⟨zK, hzK, rfl⟩
        have hzCenter := hZcenter hzK
        rw [Subgroup.mem_center_iff] at hzCenter
        refine ⟨zK.property, ?_⟩
        intro x hxK
        let xK : K := ⟨x, hxK⟩
        exact congrArg (fun y : K ↦ (y : L)) (hzCenter xK)
      have hZLcommutator :
          ZL ≤ (_root_.commutator K).map K.subtype := by
        rintro z ⟨zK, hzK, rfl⟩
        refine ⟨zK, ?_, rfl⟩
        exact hZD hzK
      have hXinduced : ∀ xi ∈ X,
          ∃ theta : IrreducibleCharacter K ℂ,
            xi = ClassFunction.induce K
              (theta : ClassFunction K ℂ) := by
        intro xi hxi
        obtain ⟨theta, _htheta, htheta⟩ := seqIndP.mp hxi
        exact ⟨theta, htheta⟩
      have hXcharacterization :
          ∀ chi : IrreducibleCharacter L ℂ,
            ((chi : ClassFunction L ℂ) ∈ X ↔
              ¬ ZL ≤ ClassFunction.translationKernel
                (chi : ClassFunction L ℂ)) := by
        intro chi
        have hdescription := (hcaseA_Xdata hcaseA).1
        change (chi : ClassFunction L ℂ) ∈
            (↑X : Set (ClassFunction L ℂ)) ↔ _
        rw [hdescription]
        constructor
        · rintro ⟨rho, hrho, hnot⟩
          have hrhoEq : rho = chi := by
            apply Subtype.ext
            exact hrho.symm
          subst rho
          simpa only [ZL] using hnot
        · intro hnot
          exact ⟨chi, rfl, by simpa only [ZL] using hnot⟩
      have hXorthonormal : ∀ xi ∈ X, ∀ zeta ∈ X,
          characterPairing xi zeta =
            if xi = zeta then 1 else 0 := by
        intro xi hxi zeta hzeta
        let xiI : IrreducibleCharacter L ℂ :=
          ⟨xi, hXirr_caseA hcaseA xi hxi⟩
        let zetaI : IrreducibleCharacter L ℂ :=
          ⟨zeta, hXirr_caseA hcaseA zeta hzeta⟩
        by_cases heq : xi = zeta
        · subst zeta
          simpa only [if_pos rfl] using
            IrreducibleCharacter.characterPairing_eq_ite xiI xiI
        · have hI : xiI ≠ zetaI := by
            intro hEq
            exact heq (congrArg Subtype.val hEq)
          rw [show characterPairing xi zeta = 0 by
            simpa only [xiI, zetaI, if_neg hI] using
              IrreducibleCharacter.characterPairing_eq_ite xiI zetaI,
            if_neg heq]
      let restriction :
          ClassFunction G ℂ →ₗ[ℂ] ClassFunction L ℂ :=
        ClassFunction.comap embedLtoG
      have hrestrictionVirtual : ∀ f : ClassFunction G ℂ,
          ClassFunction.IsVirtual f →
            ClassFunction.IsVirtual (restriction f) := by
        intro f hf
        obtain ⟨v, hv⟩ := hf
        refine ⟨VirtualCharacter.comap embedLtoG v, ?_⟩
        calc
          VirtualCharacter.realize
                (VirtualCharacter.comap embedLtoG v) =
              ClassFunction.comap embedLtoG
                (VirtualCharacter.realize v) :=
            VirtualCharacter.realize_comap embedLtoG v
          _ = restriction f := by rw [hv]
      have hreciprocity : ∀ (f : ClassFunction L ℂ)
          (g : ClassFunction G ℂ),
          characterPairing (tau f) g =
            characterPairing f (restriction g) := by
        intro f g
        simpa only [tau, restriction, embedLtoG, LG, eLG] using
          sibleyInduce_frobeniusReciprocity G L hLG f g
      let ctx : CaseAAlignmentContext
          K ZL (↑calS : Set (ClassFunction L ℂ))
          X Y tau tau₁ R eta₁ :=
        { kernel_normal := hKnormal
          central_le_kernel := by
            simpa only [ZL] using Subgroup.map_subtype_le Z
          central_normal := hZLnormal
          central_ne_bot := hZLne
          central_le_center := hZLcenter
          central_le_commutator := hZLcommutator
          subcoherent_data := hsub
          x_family := hXcal
          y_family := hYcal
          y_disjoint_x := by
            intro eta heta
            exact hYX eta heta
          x_irreducible := hXirr_caseA hcaseA
          x_induced := hXinduced
          x_characterization := hXcharacterization
          x_orthonormal := hXorthonormal
          y_orthonormal := hYorthonormal
          xy_orthogonal := hXYorth
          y_coherence := hcohY
          eta_mem := heta₁Y
          y_degree := hYdegree
          y_card_two := hYcardTwo
          restriction := restriction
          restriction_virtual := hrestrictionVirtual
          frobenius_reciprocity := hreciprocity
          embed := embedLtoG
          embed_injective := hembedLtoG
          restriction_apply := by
            intro f x
            rfl
          targetCentral := ZG
          targetCentral_eq_map := by
            simpa only [ZL] using hZmapEmbed
          constant_mod := hirrZmodK_caseA hcaseA }
      exact caseA_alignment K ZL
        (↑calS : Set (ClassFunction L ℂ)) X Y
        tau tau₁ R eta₁ ctx tau₂ hcohX
        xi₁ hxi₁X hdiv a hdegree

    /- The long character calculation in Case A ends by aligning one of
    the two possible coherence isometries on `X` with the fixed isometry on
    `Y`.  The rest of the branch is independent of that calculation: choose
    a member of minimal p-power degree and feed the aligned difference into
    the bridge lemma from Section 5. -/
    have hcaseAcohXY_of_alignment
        (hcaseA : caseA)
        (hcaseAAlignment :
          ∀ (tau₂ :
              ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
            (_ : coherent_with
              (↑X : Set (ClassFunction L ℂ))
              (nonidentitySet L) tau tau₂)
            (xi₁ : ClassFunction L ℂ) (_ : xi₁ ∈ X)
            (_ : ∀ xi ∈ X, ∃ b : ℕ,
              xi 1 = (b : ℂ) * xi₁ 1)
            (a : ℕ)
            (_ : xi₁ 1 = (a : ℂ) * eta₁ 1),
            ∃ (tauX tauY :
                ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ),
              (tauX = tau₂ ∨
                (X.card ≤ 2 ∧ tauX = dual_iso tau₂)) ∧
              (tauY = tau₁ ∨
                (Y.card ≤ 2 ∧ tauY = dual_iso tau₁)) ∧
              tau (xi₁ - (a : ℂ) • eta₁) =
                tauX xi₁ - (a : ℂ) • tauY eta₁) :
        coherent
          ((↑X : Set (ClassFunction L ℂ)) ∪
            (↑Y : Set (ClassFunction L ℂ)))
          (nonidentitySet L) tau := by
      have hbotZ : (⊥ : Subgroup K) < Z :=
        bot_lt_iff_ne_bot.mpr hZne
      have hXnonempty : X.Nonempty := by
        simpa only [X] using
          (seqIndD_nonempty (k := ℂ) K Z
            (⊥ : Subgroup K) hbotZ)
      have hXdegreeExponent
          (xi : ClassFunction L ℂ) (hxi : xi ∈ X) :
          ∃ e : ℕ,
            xi 1 = ((K.index * p ^ e : ℕ) : ℂ) := by
        obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp hxi
        obtain ⟨n, hn⟩ := hKp.exists_card_eq
        obtain ⟨e, _, he⟩ :=
          (Nat.dvd_prime_pow hp).mp
            (hn ▸ theta.finrank_representation_dvd_natCard)
        refine ⟨e, ?_⟩
        rw [ClassFunction.induce_one,
          IrreducibleCharacter.apply_one_eq_finrank,
          he, Nat.cast_mul]
      let exponentX : ClassFunction L ℂ → ℕ :=
        fun xi ↦
          if hxi : xi ∈ X then
            Classical.choose (hXdegreeExponent xi hxi)
          else 0
      have hexponentX
          (xi : ClassFunction L ℂ) (hxi : xi ∈ X) :
          xi 1 =
            ((K.index * p ^ exponentX xi : ℕ) : ℂ) := by
        simpa only [exponentX, dif_pos hxi] using
          Classical.choose_spec (hXdegreeExponent xi hxi)
      obtain ⟨xi₁, hxi₁X, hxi₁Min⟩ :=
        Finset.exists_min_image X exponentX hXnonempty
      have hxi₁Divides :
          ∀ xi ∈ X, ∃ b : ℕ,
            xi 1 = (b : ℂ) * xi₁ 1 := by
        intro xi hxi
        have hpowDvd :
            p ^ exponentX xi₁ ∣ p ^ exponentX xi :=
          pow_dvd_pow p (hxi₁Min xi hxi)
        obtain ⟨b, hb⟩ := hpowDvd
        refine ⟨b, ?_⟩
        rw [hexponentX xi hxi, hexponentX xi₁ hxi₁X, hb]
        simp only [Nat.cast_mul]
        ring
      let a : ℕ := p ^ exponentX xi₁
      have hxi₁Degree :
          xi₁ 1 = (a : ℂ) * eta₁ 1 := by
        rw [hexponentX xi₁ hxi₁X,
          hYdegree eta₁ heta₁Y]
        simp only [a, Nat.cast_mul]
        ring
      obtain ⟨tau₂, hcohX⟩ := hcohX_caseA hcaseA
      obtain ⟨tauX, tauY, htauX, htauY, hbridge⟩ :=
        hcaseAAlignment tau₂ hcohX xi₁ hxi₁X
          hxi₁Divides a hxi₁Degree
      have hsubX :
          subcoherent
            (↑X : Set (ClassFunction L ℂ)) tau R :=
        subset_subcoherent hsub hXcal
      have hcohX' :
          coherent_with
            (↑X : Set (ClassFunction L ℂ))
            (nonidentitySet L) tau tauX := by
        rcases htauX with htauX | ⟨hXcard, htauX⟩
        · simpa only [htauX] using hcohX
        · have hXncard :
              (↑X : Set (ClassFunction L ℂ)).ncard ≤ 2 := by
            simpa using hXcard
          simpa only [htauX] using
            (dual_coherence hsubX hcohX hXncard)
      have hcohY' :
          coherent_with
            (↑Y : Set (ClassFunction L ℂ))
            (nonidentitySet L) tau tauY := by
        rcases htauY with htauY | ⟨hYcard, htauY⟩
        · simpa only [htauY] using hcohY
        · have hYncard :
              (↑Y : Set (ClassFunction L ℂ)).ncard ≤ 2 := by
            simpa using hYcard
          simpa only [htauY] using
            (dual_coherence hsubY hcohY hYncard)
      have hYXset :
          (↑Y : Set (ClassFunction L ℂ)) ⊆
            (↑X : Set (ClassFunction L ℂ))ᶜ := by
        intro eta heta
        exact hYX eta heta
      exact coherent_union_of_sibley_bridge
        hsub hXcal hYcal hYXset
        ⟨tauX, tauY, xi₁, eta₁, a,
          hcohX', hcohY', hxi₁X, heta₁Y,
          hxi₁Degree, hbridge⟩

    /- In Case B all source-specific Clifford and Dade calculations are
    concentrated in the construction of a single signed pivot `Y₁` and
    the decompositions in `hXbridge`.  Once those have been obtained, the
    two-element exceptional possibility for `Y` is handled uniformly by
    dual coherence. -/
    have hcaseBcohXY_of_pivot
        (Y₁ : ClassFunction G ℂ)
        (hY₁alt :
          Y₁ = tau₁ eta₁ ∨
            Y.card = 2 ∧ Y₁ = dual_iso tau₁ eta₁)
        (hXbridge : ∀ xi ∈ X,
          ∃ (a : ℕ) (X₁ : ClassFunction G ℂ),
            xi 1 = (a : ℂ) * eta₁ 1 ∧
            characterPairing X₁ Y₁ = 0 ∧
            tau (xi - (a : ℂ) • eta₁) =
              X₁ - (a : ℂ) • Y₁) :
        coherent
          ((↑X : Set (ClassFunction L ℂ)) ∪
            (↑Y : Set (ClassFunction L ℂ)))
          (nonidentitySet L) tau := by
      have heta₁InvY :
          ClassFunction.inverseLinear eta₁ ∈ Y := by
        simpa only [Y] using
          (seqInd_inverse_mem (k := ℂ) K
            (⊤ : Subgroup K) D heta₁Y)
      have heta₁InvNe :
          ClassFunction.inverseLinear eta₁ ≠ eta₁ := by
        apply seqInd_conjC_neq (k := ℂ) K hoddL
          (⊤ : Subgroup K) D
        simpa only [Y] using heta₁Y
      have pairing_sub_left_local
          (f g h : ClassFunction G ℂ) :
          characterPairing (f - g) h =
            characterPairing f h - characterPairing g h := by
        rw [sub_eq_add_neg, characterPairing_add_left,
          ← neg_one_smul ℂ g, characterPairing_smul_left]
        ring
      have pairing_neg_left_local
          (f g : ClassFunction G ℂ) :
          characterPairing (-f) g =
            -characterPairing f g := by
        rw [← neg_one_smul ℂ f, characterPairing_smul_left]
        ring
      have pairing_neg_right_local
          (f g : ClassFunction G ℂ) :
          characterPairing f (-g) =
            -characterPairing f g := by
        rw [← neg_one_smul ℂ g, characterPairing_smul_right]
        ring
      have hY₁Virtual : ClassFunction.IsVirtual Y₁ := by
        rcases hY₁alt with hY₁ | ⟨_, hY₁⟩
        · rw [hY₁]
          exact heta₁TauVirtual
        · rw [hY₁, dual_iso_apply]
          exact
            (hcohYvirtual
              (ClassFunction.inverseLinear eta₁)
              (AddSubgroup.subset_closure heta₁InvY)).neg
      have hY₁Norm :
          characterPairing Y₁ Y₁ =
            characterPairing eta₁ eta₁ := by
        rcases hY₁alt with hY₁ | ⟨_, hY₁⟩
        · rw [hY₁, heta₁TauNorm, heta₁Norm]
        · rw [hY₁, dual_iso_apply]
          calc
            characterPairing
                (-tau₁ (ClassFunction.inverseLinear eta₁))
                (-tau₁ (ClassFunction.inverseLinear eta₁)) =
                characterPairing
                  (tau₁ (ClassFunction.inverseLinear eta₁))
                  (tau₁ (ClassFunction.inverseLinear eta₁)) := by
              rw [pairing_neg_left_local,
                pairing_neg_right_local, neg_neg]
            _ = 1 := by
              rw [hYtauOrthonormal
                (ClassFunction.inverseLinear eta₁) heta₁InvY
                (ClassFunction.inverseLinear eta₁) heta₁InvY,
                if_pos rfl]
            _ = characterPairing eta₁ eta₁ := heta₁Norm.symm
      have hYdegree₁ : ∀ eta ∈ Y, eta 1 = eta₁ 1 := by
        intro eta heta
        exact (hYdegree eta heta).trans
          (hYdegree eta₁ heta₁Y).symm
      have hYpivot : ∀ eta ∈ Y, eta ≠ eta₁ →
          characterPairing (tau (eta - eta₁)) Y₁ =
            -characterPairing eta₁ eta₁ := by
        intro eta heta hne
        have hspan :
            eta - eta₁ ∈ AddSubgroup.closure
              (↑Y : Set (ClassFunction L ℂ)) :=
          (AddSubgroup.closure
            (↑Y : Set (ClassFunction L ℂ))).sub_mem
              (AddSubgroup.subset_closure heta)
              (AddSubgroup.subset_closure heta₁Y)
        have hoff :
            eta - eta₁ ∈
              ClassFunction.supportedOn
                (nonidentitySet L) := by
          rw [ClassFunction.mem_supportedOn_iff]
          intro x hx
          have hxone : x = 1 := by
            simpa [nonidentitySet] using not_not.mp hx
          subst x
          simp only [ClassFunction.sub_apply]
          rw [hYdegree₁ eta heta, sub_self]
        have hagree :
            tau₁ (eta - eta₁) = tau (eta - eta₁) :=
          hcohYagree (eta - eta₁) hspan hoff
        rcases hY₁alt with hY₁ | ⟨hYcard, hY₁⟩
        · rw [hY₁, ← hagree, map_sub,
            pairing_sub_left_local,
            hYtauOrthonormal eta heta eta₁ heta₁Y,
            hYtauOrthonormal eta₁ heta₁Y eta₁ heta₁Y,
            if_neg hne, if_pos rfl, heta₁Norm]
          ring
        · have hetaInv :
              eta = ClassFunction.inverseLinear eta₁ := by
            by_contra hneInv
            let T : Finset (ClassFunction L ℂ) :=
              {eta₁, ClassFunction.inverseLinear eta₁, eta}
            have hTsub : T ⊆ Y := by
              intro phi hphi
              simp only [T, Finset.mem_insert,
                Finset.mem_singleton] at hphi
              rcases hphi with rfl | hphi
              · exact heta₁Y
              · rcases hphi with rfl | rfl
                · exact heta₁InvY
                · exact heta
            have hTcard : T.card = 3 := by
              simp [T, hne, Ne.symm hne, heta₁InvNe,
                Ne.symm heta₁InvNe, hneInv, Ne.symm hneInv]
            have hcardLe := Finset.card_le_card hTsub
            rw [hTcard, hYcard] at hcardLe
            omega
          subst eta
          rw [hY₁, dual_iso_apply, ← hagree, map_sub]
          rw [pairing_neg_right_local, pairing_sub_left_local,
            hYtauOrthonormal
              (ClassFunction.inverseLinear eta₁) heta₁InvY
              (ClassFunction.inverseLinear eta₁) heta₁InvY,
            hYtauOrthonormal eta₁ heta₁Y
              (ClassFunction.inverseLinear eta₁) heta₁InvY,
            if_pos rfl, if_neg heta₁InvNe.symm, heta₁Norm]
          ring
      exact coherent_union_of_sibley_pivot
        hsub hXcal hYcal heta₁Y
        hY₁Virtual hY₁Norm hYdegree₁ hXbridge hYpivot

    /- The last induction is common to Cases A and B.  Its only numerical
    input is the square estimate proved from the appropriate odd Frobenius
    decomposition in each branch. -/
    have hfinish_of_base_and_numerical
        (hcohXY : coherent
          ((↑X : Set (ClassFunction L ℂ)) ∪
            (↑Y : Set (ClassFunction L ℂ)))
          (nonidentitySet L) tau)
        (hubW₁ : Z < D →
          (2 * K.index) ^ 2 ≤
            Z.index * (Nat.card Z - 1) ^ 2) :
        coherent
          (↑calS : Set (ClassFunction L ℂ))
          (nonidentitySet L) tau := by
      have hXfinite :
          (↑X : Set (ClassFunction L ℂ)).Finite :=
        hsub.finite.subset hXcal.1
      have hXYfinite :
          (↑(X ∪ Y) : Set (ClassFunction L ℂ)).Finite :=
        hsub.finite.subset hXYcal.1
      have hweightRe
          {xi : ClassFunction L ℂ}
          (hxi : xi ∈
            (↑calS : Set (ClassFunction L ℂ))) :
          coherenceDegreeWeight xi =
            Complex.re (xi 1 ^ 2 / characterPairing xi xi) := by
        obtain ⟨d, hd⟩ := Cnat_seqInd1 K (by
          simpa only [calS, seqIndD, Finset.mem_coe] using hxi)
        obtain ⟨n, hn⟩ :=
          (hsub.source_character xi hxi).isVirtual.exists_nat_norm
        rw [coherenceDegreeWeight, hd, hn]
        norm_num [pow_two, Complex.mul_re]
      have hXto : hXfinite.toFinset = X := by
        ext xi
        simp [hXfinite]
      have hsumXraw :
          (∑ xi ∈ X, coherenceDegreeWeight xi) =
            (K.index : ℝ) *
              ((Z.index : ℝ) * ((Nat.card Z : ℝ) - 1)) := by
        letI : (((⊥ : Subgroup K).map K.subtype :
            Subgroup L)).Normal := by
          rw [Subgroup.map_bot]
          infer_instance
        have hsumComplex :=
          sum_seqIndD_square (k := ℂ) K Z
            (⊥ : Subgroup K) bot_le
        have hsumReal := congrArg Complex.re hsumComplex
        rw [Complex.re_sum] at hsumReal
        simp only [Complex.mul_re, Complex.natCast_re,
          Complex.natCast_im, Complex.sub_re, Complex.one_re,
          mul_zero, zero_mul, sub_zero] at hsumReal
        calc
          (∑ xi ∈ X, coherenceDegreeWeight xi) =
              ∑ xi ∈ X,
                Complex.re (xi 1 ^ 2 / characterPairing xi xi) := by
            apply Finset.sum_congr rfl
            intro xi hxi
            exact hweightRe (hXcal.1 hxi)
          _ = (K.index : ℝ) *
              ((Z.index : ℝ) * ((Nat.card Z : ℝ) - 1)) := by
            simpa only [X, Subgroup.relIndex_bot_left] using hsumReal
      have hYweight
          (eta : ClassFunction L ℂ) (heta : eta ∈ Y) :
          coherenceDegreeWeight eta = (K.index : ℝ) ^ 2 := by
        rw [coherenceDegreeWeight, hYdegree eta heta,
          hYorthonormal eta heta eta heta, if_pos rfl]
        norm_num
      have hYsumPos :
          0 < ∑ eta ∈ Y, coherenceDegreeWeight eta := by
        have hKindexPos : (0 : ℝ) < K.index := by
          exact_mod_cast
            Nat.pos_of_ne_zero K.index_ne_zero_of_finite
        exact Finset.sum_pos'
          (fun eta heta ↦ by
            rw [hYweight eta heta]
            exact (pow_pos hKindexPos 2).le)
          ⟨eta₁, heta₁Y, by
            rw [hYweight eta₁ heta₁Y]
            exact pow_pos hKindexPos 2⟩
      have hXYdisjoint : Disjoint X Y := by
        rw [Finset.disjoint_left]
        intro xi hxiX hxiY
        exact hYX xi hxiY hxiX
      have hXYto : hXYfinite.toFinset = X ∪ Y := by
        ext xi
        simp [hXYfinite]
      have hsumXY :
          coherenceDegreeSum
              (↑(X ∪ Y) : Set (ClassFunction L ℂ)) hXYfinite =
            (K.index : ℝ) *
                ((Z.index : ℝ) * ((Nat.card Z : ℝ) - 1)) +
              ∑ eta ∈ Y, coherenceDegreeWeight eta := by
        rw [coherenceDegreeSum, hXYto,
          Finset.sum_union hXYdisjoint, hsumXraw]
      have hpsiXbound : ∀ psi ∈
          (↑calS : Set (ClassFunction L ℂ)),
          psi ∉ (↑(X ∪ Y) : Set (ClassFunction L ℂ)) →
            2 * (psi 1).re * (eta₁ 1).re <
              coherenceDegreeSum
                (↑(X ∪ Y) : Set (ClassFunction L ℂ)) hXYfinite := by
        intro psi hpsiCal hpsiXY
        have hpsiSeq :
            psi ∈ seqIndD K (⊤ : Subgroup K) ⊥ := by
          simpa only [calS, Finset.mem_coe] using hpsiCal
        obtain ⟨theta, htheta, hpsi⟩ := seqIndP.mp hpsiSeq
        subst psi
        have hZtheta : Z ≤ ClassFunction.translationKernel
            (theta : ClassFunction K ℂ) := by
          by_contra hnot
          apply hpsiXY
          rw [Finset.mem_coe, Finset.mem_union]
          left
          apply (mem_seqInd (k := ℂ) K Z ⊥ theta).mpr
          exact (mem_Iirr_kerD.mpr ⟨bot_le, hnot⟩)
        have hDtheta : ¬D ≤ ClassFunction.translationKernel
            (theta : ClassFunction K ℂ) := by
          intro hDker
          apply hpsiXY
          rw [Finset.mem_coe, Finset.mem_union]
          right
          apply (mem_seqInd (k := ℂ) K
            (⊤ : Subgroup K) D theta).mpr
          exact (mem_Iirr_kerD.mpr
            ⟨hDker, (mem_Iirr_kerD.mp htheta).2⟩)
        have hZDproper : Z < D := by
          refine lt_of_le_of_ne hZD ?_
          intro hDZ
          apply hDtheta
          exact hDZ.symm.le.trans hZtheta
        letI : CategoryTheory.Simple theta.representation :=
          theta.representation_simple
        letI : Representation.IsIrreducible theta.representation.ρ :=
          representation_isIrreducible_of_simple_fdRep
            theta.representation
        have hscalar : ∀ z : Z, ∃ c : ℂ,
            theta.representation.ρ (z : K) =
              c • (1 : Module.End ℂ theta.representation) := by
          intro z
          let zc : Subgroup.center K := ⟨z, hZcenter z.property⟩
          refine ⟨
            (schurCenterScalarCharacter
              theta.representation.ρ zc : ℂ), ?_⟩
          ext v
          exact schurCenterScalarCharacter_smul
            theta.representation.ρ zc v
        have hthetaSq :
            Module.finrank ℂ theta.representation ^ 2 ≤ Z.index :=
          Representation.IsIrreducible.finrank_sq_le_index_of_scalar_subgroup
            theta.representation.ρ Z hscalar
        let n : ℕ := Module.finrank ℂ theta.representation
        have htargetSq :
            (2 * K.index * n) ^ 2 ≤
              (Z.index * (Nat.card Z - 1)) ^ 2 := by
          calc
            (2 * K.index * n) ^ 2 =
                (2 * K.index) ^ 2 * n ^ 2 := by ring
            _ ≤ (Z.index * (Nat.card Z - 1) ^ 2) * Z.index :=
              Nat.mul_le_mul (hubW₁ hZDproper) hthetaSq
            _ = (Z.index * (Nat.card Z - 1)) ^ 2 := by ring
        have htargetSqReal :
            ((2 * K.index * n : ℕ) : ℝ) ^ 2 ≤
              ((Z.index * (Nat.card Z - 1) : ℕ) : ℝ) ^ 2 := by
          exact_mod_cast htargetSq
        have htargetReal :
            ((2 * K.index * n : ℕ) : ℝ) ≤
              ((Z.index * (Nat.card Z - 1) : ℕ) : ℝ) :=
          le_of_sq_le_sq htargetSqReal (by positivity)
        have htarget :
            2 * K.index * n ≤ Z.index * (Nat.card Z - 1) := by
          exact_mod_cast htargetReal
        have hmulTarget := Nat.mul_le_mul_left K.index htarget
        have hdegreeRe :
            (ClassFunction.induce K
                (theta : ClassFunction K ℂ) 1).re =
              ((K.index * n : ℕ) : ℝ) := by
          rw [ClassFunction.induce_one,
            IrreducibleCharacter.apply_one_eq_finrank]
          norm_num [n]
        have heta₁Re : (eta₁ 1).re = (K.index : ℝ) := by
          rw [hYdegree eta₁ heta₁Y]
          norm_num
        have hbaseBound :
            2 *
                (ClassFunction.induce K
                  (theta : ClassFunction K ℂ) 1).re *
                (eta₁ 1).re ≤
              (K.index : ℝ) *
                ((Z.index : ℝ) * ((Nat.card Z : ℝ) - 1)) := by
          rw [hdegreeRe, heta₁Re]
          have hcast :
              ((K.index * (2 * K.index * n) : ℕ) : ℝ) ≤
                ((K.index *
                    (Z.index * (Nat.card Z - 1)) : ℕ) : ℝ) := by
            exact_mod_cast hmulTarget
          simp only [Nat.cast_mul] at hcast
          rw [Nat.cast_sub (Nat.card_pos (α := Z))] at hcast
          norm_num only [Nat.cast_ofNat] at hcast
          convert hcast using 1 <;>
            simp only [Nat.cast_mul] <;> ring
        calc
          2 *
                (ClassFunction.induce K
                  (theta : ClassFunction K ℂ) 1).re *
                (eta₁ 1).re ≤
              (K.index : ℝ) *
                ((Z.index : ℝ) * ((Nat.card Z : ℝ) - 1)) :=
            hbaseBound
          _ < (K.index : ℝ) *
                  ((Z.index : ℝ) * ((Nat.card Z : ℝ) - 1)) +
                ∑ eta ∈ Y, coherenceDegreeWeight eta :=
            lt_add_of_pos_right _ hYsumPos
          _ = coherenceDegreeSum
                (↑(X ∪ Y) : Set (ClassFunction L ℂ)) hXYfinite :=
            hsumXY.symm
      have hcohXY' : coherent
          (↑(X ∪ Y) : Set (ClassFunction L ℂ))
          (nonidentitySet L) tau := by
        simpa only [Finset.coe_union] using hcohXY
      exact extend_coherent_from_sibley_base
        K tau R calS X Y rfl hsub eta₁ heta₁Y
        (hYdegree eta₁ heta₁Y) hXYcal hcohXY' hpsiXbound

    have hubW₁_of_caseA_bound
        (hbound : 2 * K.index ≤ Nat.card Z - 1) :
        (2 * K.index) ^ 2 ≤
          Z.index * (Nat.card Z - 1) ^ 2 := by
      have hsq :
          (2 * K.index) ^ 2 ≤ (Nat.card Z - 1) ^ 2 :=
        Nat.pow_le_pow_left hbound 2
      have hindexPos : 1 ≤ Z.index :=
        Nat.one_le_iff_ne_zero.mpr Subgroup.index_ne_zero_of_finite
      calc
        (2 * K.index) ^ 2 ≤ (Nat.card Z - 1) ^ 2 := hsq
        _ = 1 * (Nat.card Z - 1) ^ 2 := by simp
        _ ≤ Z.index * (Nat.card Z - 1) ^ 2 :=
          Nat.mul_le_mul_right _ hindexPos
    have hubW₁_of_caseB_bounds
        (hboundD : 2 * K.index ≤ D.index - 1)
        (hboundZD : 2 * K.index ≤ Z.relIndex D - 1) :
        (2 * K.index) ^ 2 ≤
          Z.index * (Nat.card Z - 1) ^ 2 := by
      have hboundD' : 2 * K.index ≤ D.index :=
        hboundD.trans (Nat.sub_le _ _)
      have hboundZD' : 2 * K.index ≤ Z.relIndex D :=
        hboundZD.trans (Nat.sub_le _ _)
      have hsqIndex :
          (2 * K.index) ^ 2 ≤ Z.relIndex D * D.index := by
        simpa only [pow_two] using Nat.mul_le_mul hboundZD' hboundD'
      have hindexProduct : Z.relIndex D * D.index = Z.index :=
        Z.relIndex_mul_index hZD
      have hZcardTwo : 2 ≤ Nat.card Z :=
        Z.one_lt_card_iff_ne_bot.mpr hZne
      have hcardFactor : 1 ≤ (Nat.card Z - 1) ^ 2 := by
        have : 1 ≤ Nat.card Z - 1 := by omega
        exact Nat.one_le_pow 2 (Nat.card Z - 1) this
      calc
        (2 * K.index) ^ 2 ≤ Z.relIndex D * D.index := hsqIndex
        _ = Z.index := hindexProduct
        _ = Z.index * 1 := by simp
        _ ≤ Z.index * (Nat.card Z - 1) ^ 2 :=
          Nat.mul_le_mul_left _ hcardFactor

    have hcaseA_bound (hcaseA : caseA) :
        2 * K.index ≤ Nat.card Z - 1 := by
      let ZL : Subgroup L := Z.map K.subtype
      have hZLne : ZL ≠ ⊥ := by
        intro hbot
        apply hZne
        exact (Subgroup.map_eq_bot_iff_of_injective Z
          K.subtype_injective).mp hbot
      have hZLnormal : ZL.Normal := hZmapNormal
      letI : ZL.Normal := hZLnormal
      have hZLsubK : ZL ≤ K :=
        Subgroup.map_subtype_le Z
      have hZLsubgroup : ZL.subgroupOf K = Z := by
        change (Z.map K.subtype).comap K.subtype = Z
        exact Subgroup.comap_map_eq_self_of_injective
          K.subtype_injective Z
      have hreg : IsSemiregularConjugation ZL W₁L' := by
        intro r hr z hz
        let zK : K := ⟨(z : L), hZLsubK z.property⟩
        have hzZ : zK ∈ Z := by
          rw [← hZLsubgroup]
          exact z.property
        by_cases hc1 : case_c1
        · have hzOne := hc1.fixedPointFree r hr zK (by
            simpa only [zK] using hz)
          apply Subtype.ext
          exact congrArg (fun x : K ↦ (x : L)) hzOne
        · rcases hW₂c2 hc1 with
          ⟨_, _, A₀, W, defW, pd⟩
          have hrL : (r : L) ≠ 1 := by
            intro hrOne
            apply hr
            apply Subtype.ext
            exact hrOne
          have hcent :=
            primeTI_centralizerWithin_subgroupOf_zpowers
              pd.prDade_prTI (r : L) r.property hrL
          have hrz : Commute (r : L) (zK : L) := by
            rw [commute_iff_eq]
            calc
              (r : L) * (zK : L) =
                  ((r : L) * (zK : L) * (r : L)⁻¹) * (r : L) := by
                group
              _ = (zK : L) * (r : L) := by
                rw [show
                  (r : L) * (zK : L) * (r : L)⁻¹ = (zK : L) by
                    simpa only [zK] using hz]
          have hzcent :
              (zK : L) ∈ centralizerWithin K
                (Subgroup.zpowers (r : L)) := by
            refine ⟨zK.property, ?_⟩
            intro y hy
            obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
            exact (hrz.zpow_left n).eq
          rw [hcent] at hzcent
          have hzW₂K : zK ∈ W₂K := by
            change (((zK : K) : L) : Gamma) ∈ W₂
            change (((zK : K) : L) : Gamma) ∈ W₂ at hzcent
            exact hzcent
          have hzbot : zK ∈ (⊥ : Subgroup K) :=
            hcaseA ⟨hZcenter hzZ, hzW₂K⟩
          apply Subtype.ext
          have hzKone : zK = (1 : K) := Subgroup.mem_bot.mp hzbot
          exact congrArg (fun x : K ↦ (x : L)) hzKone
      have hnorm : W₁L' ≤ Subgroup.normalizer (ZL : Set L) := by
        rw [ZL.normalizer_eq_top]
        exact le_top
      have hcardW₁ : Nat.card W₁L' = K.index :=
        hKW₁.symm.index_eq_card.symm
      have hZLcard : Nat.card ZL = Nat.card Z := by
        calc
          Nat.card ZL = Nat.card (ZL.subgroupOf K) :=
            (MathlibSupport.natCard_subgroupOf_eq hZLsubK).symm
          _ = Nat.card Z := by rw [hZLsubgroup]
      rw [← hcardW₁]
      simpa only [hZLcard] using
        two_actor_card_le_acted_card_sub_one
          hoddL hreg hnorm hZLne hW₁ne

    have hcaseB_index_lt (hcaseB : caseB) :
        K.index < Z.index := by
      have hc₂ := hcaseB_c2 hcaseB
      rcases hW₂c2 hc₂ with
          ⟨_, _, A₀, W, defW, pd⟩
      let ZL : Subgroup L := Z.map K.subtype
      have hZLsubK : ZL ≤ K := by
        simpa only [ZL] using Subgroup.map_subtype_le Z
      have hZLsubgroup : ZL.subgroupOf K = Z := by
        change (Z.map K.subtype).comap K.subtype = Z
        exact Subgroup.comap_map_eq_self_of_injective
          K.subtype_injective Z
      have hZLltK : ZL < K := by
        refine lt_of_le_of_ne hZLsubK ?_
        intro hZLK
        apply hKnonabelian
        rw [isMulCommutative_iff]
        intro x y
        apply Subtype.ext
        have hxZL : (x : L) ∈ ZL := by
          rw [hZLK]
          exact x.property
        have hxCenter := hcaseB_ZcenterL hcaseB hxZL
        rw [Subgroup.mem_center_iff] at hxCenter
        exact (hxCenter (y : L)).symm
      have hW₂ZL : W₂.subgroupOf L ≤ ZL := by
        intro w hw
        let wK : K := ⟨(w : L), hW₂LK hw⟩
        refine ⟨wK, ?_, rfl⟩
        rw [show Z = W₂K by simp only [Z, if_neg hcaseB]]
        change (((wK : K) : L) : Gamma) ∈ W₂
        exact hw
      letI : ZL.Normal := by
        simpa only [ZL] using hZmapNormal
      let qZ : L →* L ⧸ ZL := QuotientGroup.mk' ZL
      let KZ : Subgroup (L ⧸ ZL) := K.map qZ
      let RZ : Subgroup (L ⧸ ZL) := W₁L'.map qZ
      have hfrobZ : IsFrobeniusDecomposition KZ RZ := by
        simpa only [KZ, RZ, qZ] using
          primeTI_frobenius_quotient_of_fixed_le
            pd.prDade_prTI ZL hZLltK hW₂ZL
      have hoddQZ : Odd (Nat.card (L ⧸ ZL)) :=
        odd_natCard_quotient ZL hoddL
      have hRZcard : Nat.card RZ = K.index := by
        let fZ : W₁L' → RZ := qZ.subgroupMap W₁L'
        have hfZ : Function.Bijective fZ :=
          ⟨hKW₁.quotientRight_subgroupMap_injective hZLltK.le,
            qZ.subgroupMap_surjective W₁L'⟩
        calc
          Nat.card RZ = Nat.card W₁L' :=
            (Nat.card_congr (Equiv.ofBijective fZ hfZ)).symm
          _ = K.index := hKW₁.symm.index_eq_card.symm
      have hKZcard : Nat.card KZ = Z.index := by
        calc
          Nat.card KZ = ZL.relIndex K :=
            (relIndex_eq_card_map_quotient_sibley
              (show ZL.Normal from inferInstance) hZLsubK).symm
          _ = (ZL.subgroupOf K).index := rfl
          _ = Z.index := congrArg Subgroup.index hZLsubgroup
      have hbound :
          2 * Nat.card RZ ≤ Nat.card KZ - 1 :=
        two_complement_card_le_subkernel_card_sub_one
          hoddQZ hfrobZ le_rfl hfrobZ.kernel_normal
            hfrobZ.kernel_ne_bot
      rw [hRZcard, hKZcard] at hbound
      have hKindexPos : 0 < K.index :=
        Nat.pos_of_ne_zero K.index_ne_zero_of_finite
      omega

    have hcaseB_bounds (hcaseB : caseB) (hZDproper : Z < D) :
        2 * K.index ≤ D.index - 1 ∧
          2 * K.index ≤ Z.relIndex D - 1 := by
      have hc2 := hcaseB_c2 hcaseB
      rcases hW₂c2 hc2 with
          ⟨_, _, A₀, W, defW, pd⟩
      let qD : L →* L ⧸ DL := QuotientGroup.mk' DL
      let KD : Subgroup (L ⧸ DL) := K.map qD
      let RD : Subgroup (L ⧸ DL) := W₁L'.map qD
      have hoddQD : Odd (Nat.card (L ⧸ DL)) :=
        odd_natCard_quotient DL hoddL
      have hRDcard : Nat.card RD = K.index := by
        let fD : W₁L' → RD := qD.subgroupMap W₁L'
        have hfD : Function.Bijective fD :=
          ⟨hKW₁.quotientRight_subgroupMap_injective hDLproper.le,
            qD.subgroupMap_surjective W₁L'⟩
        calc
          Nat.card RD = Nat.card W₁L' :=
            (Nat.card_congr (Equiv.ofBijective fD hfD)).symm
          _ = K.index := hKW₁.symm.index_eq_card.symm
      have hKDcard : Nat.card KD = D.index := by
        calc
          Nat.card KD = DL.relIndex K :=
            (relIndex_eq_card_map_quotient_sibley
              hDLnormal hDLproper.le).symm
          _ = (DL.subgroupOf K).index := rfl
          _ = D.index := congrArg Subgroup.index hDLsubK
      have hboundD₀ :
          2 * Nat.card RD ≤ Nat.card KD - 1 :=
        two_complement_card_le_subkernel_card_sub_one
          hoddQD hfrobDerived (A := KD) le_rfl
          hfrobDerived.kernel_normal hfrobDerived.kernel_ne_bot
      have hboundD : 2 * K.index ≤ D.index - 1 := by
        simpa only [hRDcard, hKDcard] using hboundD₀

      let ZL : Subgroup L := Z.map K.subtype
      have hZLltDL : ZL < DL := by
        simpa only [ZL, DL] using
          ((Subgroup.map_lt_map_iff_of_injective
            K.subtype_injective).2 hZDproper)
      have hZLltK : ZL < K := hZLltDL.trans hDLproper
      have hW₂ZL : W₂.subgroupOf L ≤ ZL := by
        intro w hw
        let wK : K := ⟨(w : L), hW₂LK hw⟩
        refine ⟨wK, ?_, rfl⟩
        rw [show Z = W₂K by simp only [Z, if_neg hcaseB]]
        change (((wK : K) : L) : Gamma) ∈ W₂
        exact hw
      letI : ZL.Normal := hZmapNormal
      let qZ : L →* L ⧸ ZL := QuotientGroup.mk' ZL
      let KZ : Subgroup (L ⧸ ZL) := K.map qZ
      let RZ : Subgroup (L ⧸ ZL) := W₁L'.map qZ
      let DZ : Subgroup (L ⧸ ZL) := DL.map qZ
      have hfrobZ : IsFrobeniusDecomposition KZ RZ := by
        simpa only [KZ, RZ, qZ] using
          primeTI_frobenius_quotient_of_fixed_le
            pd.prDade_prTI ZL hZLltK hW₂ZL
      have hoddQZ : Odd (Nat.card (L ⧸ ZL)) :=
        odd_natCard_quotient ZL hoddL
      have hRZcard : Nat.card RZ = K.index := by
        let fZ : W₁L' → RZ := qZ.subgroupMap W₁L'
        have hfZ : Function.Bijective fZ :=
          ⟨hKW₁.quotientRight_subgroupMap_injective hZLltK.le,
            qZ.subgroupMap_surjective W₁L'⟩
        calc
          Nat.card RZ = Nat.card W₁L' :=
            (Nat.card_congr (Equiv.ofBijective fZ hfZ)).symm
          _ = K.index := hKW₁.symm.index_eq_card.symm
      have hDZKZ : DZ ≤ KZ :=
        Subgroup.map_mono hDLproper.le
      have hDZnormal : DZ.Normal :=
        Subgroup.Normal.map hDLnormal qZ
          (QuotientGroup.mk'_surjective ZL)
      have hDZne : DZ ≠ ⊥ := by
        intro hbot
        have hle : DL ≤ qZ.ker :=
          (Subgroup.map_eq_bot_iff DL).mp hbot
        have hDLZL : DL ≤ ZL := by
          simpa only [qZ, QuotientGroup.ker_mk'] using hle
        exact (not_le_of_gt hZLltDL) hDLZL
      have hDZcard : Nat.card DZ = Z.relIndex D := by
        calc
          Nat.card DZ = ZL.relIndex DL :=
            (relIndex_eq_card_map_quotient_sibley
              hZmapNormal hZLltDL.le).symm
          _ = Z.relIndex D := by
            simpa only [ZL, DL] using
              Subgroup.relIndex_map_map_of_injective
                Z D K.subtype_injective
      have hboundZD₀ :
          2 * Nat.card RZ ≤ Nat.card DZ - 1 :=
        two_complement_card_le_subkernel_card_sub_one
          hoddQZ hfrobZ hDZKZ hDZnormal hDZne
      have hboundZD :
          2 * K.index ≤ Z.relIndex D - 1 := by
        simpa only [hRZcard, hDZcard] using hboundZD₀
      exact ⟨hboundD, hboundZD⟩

    have hubW₁ : Z < D →
        (2 * K.index) ^ 2 ≤
          Z.index * (Nat.card Z - 1) ^ 2 := by
      intro hZDproper
      by_cases hcaseA : caseA
      · exact hubW₁_of_caseA_bound (hcaseA_bound hcaseA)
      · obtain ⟨hboundD, hboundZD⟩ :=
          hcaseB_bounds hcaseA hZDproper
        exact hubW₁_of_caseB_bounds hboundD hboundZD

    have hcohXY :
        coherent
          ((↑X : Set (ClassFunction L ℂ)) ∪
            (↑Y : Set (ClassFunction L ℂ)))
          (nonidentitySet L) tau := by
      by_cases hcaseA : caseA
      · exact hcaseAcohXY_of_alignment hcaseA
          (hcaseA_alignment hcaseA)
      · have hXinduced : ∀ xi ∈ X,
            ∃ theta : IrreducibleCharacter K ℂ,
              xi = ClassFunction.induce K
                (theta : ClassFunction K ℂ) := by
          intro xi hxi
          obtain ⟨theta, _htheta, htheta⟩ := seqIndP.mp hxi
          exact ⟨theta, htheta⟩
        let ctx : SibleyCaseBContext
            K Z X Y tau tau₁ eta₁ :=
          { sourceFamily :=
              (↑calS : Set (ClassFunction L ℂ))
            targetColumns := R
            source_subcoherent := hsub
            X_family := hXcal
            Y_family := hYcal
            eta₁_mem := heta₁Y
            Y_closed := hYcal.2
            Y_coherent := hcohY
            Y_orthonormal := hYorthonormal
            Y_degree := hYdegree
            two_le_card_Y := hYcardTwo
            X_Y_disjoint := by
              intro xi hxi eta heta heq
              apply hYX eta heta
              rw [heq]
              exact hxi
            Z_nontrivial := hZne
            Z_prime := hcaseB_Zprime hcaseA
            Z_cyclic := hcaseB_Zcyclic hcaseA
            Z_central := hZcenter
            Z_central_in_L := hcaseB_ZcenterL hcaseA
            X_induced := hXinduced
            X_characterization := hXcharacterizationSource
            centralInduce := centralInduce
            centralInduce_eq_induce := by
              intro i
              rfl
            centralInduce_virtual := hcentralInduceVirtual
            centralInduce_mem_X_span := hcentralInduceMemXSpan
            centralInduce_one :=
              hcaseB_centralInduceOne hcaseA
            centralInduce_self :=
              hcaseB_centralInduceSelf hcaseA
            embedLtoG := embedLtoG
            embedLtoG_injective := hembedLtoG
            zToG := zToG
            zToG_injective := hzToGInjective
            zToG_eq := by rfl
            frobenius_reciprocity := by
              intro f g
              simpa only [tau, embedLtoG, LG, eLG] using
                sibleyInduce_frobeniusReciprocity
                  G L hLG f g
            centralInduce_pairing := hcentralInducePairing
            ZG := ZG
            ZG_nontrivial := hZGne
            ZG_prime := hcaseB_ZGprime hcaseA
            ZG_cyclic := hcaseB_ZGcyclic hcaseA
            zToG_range := hzToGRange
            Z_power_transitive :=
              hcaseB_ZpowerTransitive hcaseA
            Y_coefficient_closed := hYcoefficientClosed
            coefficient_automorphism_commutes :=
              hcaseB_coefficient_commutes hcaseA
            dade_twist_vanishes_on_Z :=
              hcaseB_dade_twist_vanishes hcaseA
            constant_irreducible_mod :=
              hirrZmodK_caseB hcaseA
            kernel_index_lt_central_index :=
              hcaseB_index_lt hcaseA }
        obtain ⟨Y₁, hY₁alt, hXbridge⟩ :=
          sibley_caseB_pivot K Z X Y tau tau₁ eta₁ ctx
        exact hcaseBcohXY_of_pivot Y₁ hY₁alt hXbridge

    have hcohAll :=
      hfinish_of_base_and_numerical hcohXY hubW₁
    simpa only [sibleyFamily, calS, K, tau] using hcohAll

end

end Submission.OddOrder.PF
