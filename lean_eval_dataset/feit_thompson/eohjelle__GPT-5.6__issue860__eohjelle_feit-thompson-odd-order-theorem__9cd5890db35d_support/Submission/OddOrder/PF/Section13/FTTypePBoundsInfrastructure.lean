import Submission.OddOrder.BG.AppendixC.NormEquationCharacterBranch
import Submission.OddOrder.MathlibSupport.CharacterGeneratorNorm
import Submission.OddOrder.MathlibSupport.ComplexCyclotomicPowerAutomorphism
import Submission.OddOrder.PF.Section13.FTTypePSetupAndCoherence

/-!
# Peterfalvi Section 13: infrastructure for the analytic bounds

This module collects the finite-set notation, the fitting-family layer, the
coherence calculation for reciprocal Dade coefficients, and fixed
nonprincipal indices for the two cyclic factors.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open scoped BigOperators Classical Pointwise

universe u

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {S U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) ftTypePBoundsFintypeOfFinite
    (Q : Type) [Finite Q] : Fintype Q :=
  Fintype.ofFinite Q

namespace FTTypePBoundsInfrastructureInternal

/-- A set viewed as a finset when its ambient type is finite. -/
def finiteSet {Q : Type u} [Fintype Q] (A : Set Q) : Finset Q :=
  Finset.univ.filter (· ∈ A)

end FTTypePBoundsInfrastructureInternal

/-- The unnormalized squared mass of a class function on a set. -/
def ftTypePSumNormSq (A : Set G) (chi : ClassFunction G ℂ) : ℝ :=
  ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet A,
    Complex.normSq (chi x)

/-- The cardinality notation used by the Section 13 estimates. -/
def ftTypePSetCard (A : Set G) : ℕ :=
  (FTTypePBoundsInfrastructureInternal.finiteSet A).card

namespace FTTypePBoundsInfrastructureInternal

/-! ### The fitting-family layer -/

def fittingCoreFamily
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Finset (ClassFunction S ℂ) :=
  let H := ctx.H.subgroupOf S
  let P := (ctx.P.subgroupOf S).subgroupOf H
  seqIndD (k := ℂ) H P ⊥

theorem seqIndD_mem_seqIndT
    {Q : Type u} [Group Q] [Fintype Q]
    (H : Subgroup Q) [H.Normal] (K M : Subgroup H)
    {phi : ClassFunction Q ℂ}
    (hphi : phi ∈ seqIndD (k := ℂ) H K M) :
    phi ∈ seqIndT (k := ℂ) H :=
  seqInd_subT (k := ℂ) H (Iirr_kerD (k := ℂ) K M) hphi

theorem fittingCoreFamily_subset
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    fittingCoreFamily ctx ⊆ ftTypePFittingFamily S := by
  intro phi hphi
  let H := ctx.H.subgroupOf S
  let P := (ctx.P.subgroupOf S).subgroupOf H
  change phi ∈ seqIndD (k := ℂ) H P ⊥ at hphi
  change phi ∈ seqIndT (k := ℂ) H
  exact seqIndD_mem_seqIndT H P ⊥ hphi

/-! ### Coherence and reciprocal-Dade coefficients -/

private theorem starPairing_eq_pairing_of_virtual
    {Q : Type u} [Group Q] [Fintype Q]
    {phi psi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hpsi : ClassFunction.IsVirtual psi) :
    starCharacterPairing phi psi = characterPairing phi psi :=
  PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
    hphi hpsi

private theorem starPairing_sub_left
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    starCharacterPairing (phi - psi) theta =
      starCharacterPairing phi theta - starCharacterPairing psi theta := by
  simp [sub_eq_add_neg, starCharacterPairing, twistedCharacterPairing,
    add_mul, Finset.sum_add_distrib]
  ring

private theorem adjusted_agrees
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (K M : Subgroup H)
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction J ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu)
    {xi0 xi : ClassFunction L ℂ}
    (hxi0 : xi0 ∈ seqIndD (k := ℂ) H K M)
    (hxi : xi ∈ seqIndD (k := ℂ) H K M) :
    Dade ddA (invDadeSeqIndAdjusted xi0 xi) =
      nu (invDadeSeqIndAdjusted xi0 xi) := by
  let weighted : ClassFunction L ℂ :=
    (xi0 1) • xi - (xi 1) • xi0
  have hweightedClosure :
      weighted ∈ AddSubgroup.closure
        (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ)) := by
    obtain ⟨m, hm⟩ := Cnat_seqInd1 H hxi0
    obtain ⟨n, hn⟩ := Cnat_seqInd1 H hxi
    unfold weighted
    rw [hm, hn]
    have hmMem :=
      (AddSubgroup.closure
          (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))).nsmul_mem
        (AddSubgroup.subset_closure hxi) m
    have hnMem :=
      (AddSubgroup.closure
          (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))).nsmul_mem
        (AddSubgroup.subset_closure hxi0) n
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ) m xi] at hmMem
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ) n xi0] at hnMem
    exact
      (AddSubgroup.closure
          (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))).sub_mem
        hmMem hnMem
  have hweightedSupport :
      weighted ∈ ClassFunction.supportedOn (nonidentitySet L) := by
    have hsupp := sub_seqInd_on H hxi hxi0
    rw [ClassFunction.mem_supportedOn_iff] at hsupp ⊢
    intro x hx
    apply hsupp
    intro hxH
    apply hx
    simpa [nonidentitySet] using hxH.2
  have hagree := hcoh.agrees weighted hweightedClosure hweightedSupport
  have hdegree : xi0 1 ≠ 0 :=
    seqInd1_neq0 H (seqIndD_mem_seqIndT H K M hxi0)
  have hadjusted :
      invDadeSeqIndAdjusted xi0 xi = (xi0 1)⁻¹ • weighted := by
    unfold invDadeSeqIndAdjusted weighted
    apply ClassFunction.ext
    intro x
    simp only [ClassFunction.sub_apply, ClassFunction.smul_apply,
      smul_eq_mul]
    field_simp [hdegree]
  rw [hadjusted, map_smul, map_smul, hagree]

theorem coherentCoefficient
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (K M : Subgroup H)
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction J ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu)
    {xi0 xi zeta : ClassFunction L ℂ}
    (hxi0 : xi0 ∈ seqIndD (k := ℂ) H K M)
    (hxi : xi ∈ seqIndD (k := ℂ) H K M)
    (hzeta : zeta ∈ seqIndD (k := ℂ) H K M)
    (horth : characterPairing xi0 zeta = 0) :
    invDadeSeqIndCoefficient ddA xi0 (nu zeta) xi =
      characterPairing xi zeta := by
  have hxiClosure := AddSubgroup.subset_closure hxi
  have hxi0Closure := AddSubgroup.subset_closure hxi0
  have hzetaClosure := AddSubgroup.subset_closure hzeta
  have hnuXi := hcoh.mapsToVirtual xi hxiClosure
  have hnuXi0 := hcoh.mapsToVirtual xi0 hxi0Closure
  have hnuZeta := hcoh.mapsToVirtual zeta hzetaClosure
  unfold invDadeSeqIndCoefficient
  rw [adjusted_agrees H K M ddA nu hcoh hxi0 hxi]
  unfold invDadeSeqIndAdjusted
  rw [map_sub, map_smul, starPairing_sub_left,
    starCharacterPairing_smul_left,
    starPairing_eq_pairing_of_virtual hnuXi hnuZeta,
    starPairing_eq_pairing_of_virtual hnuXi0 hnuZeta,
    hcoh.isometry xi hxiClosure zeta hzetaClosure,
    hcoh.isometry xi0 hxi0Closure zeta hzetaClosure,
    horth, mul_zero, sub_zero]

theorem coherentCoefficient_eq_zero
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (K M : Subgroup H)
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction J ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu)
    {xi0 xi zeta : ClassFunction L ℂ}
    (hxi0 : xi0 ∈ seqIndD (k := ℂ) H K M)
    (hxi : xi ∈ seqIndD (k := ℂ) H K M)
    (hzeta : zeta ∈ seqIndD (k := ℂ) H K M)
    (hxi0zeta : characterPairing xi0 zeta = 0)
    (hxizeta : characterPairing xi zeta = 0) :
    invDadeSeqIndCoefficient ddA xi0 (nu zeta) xi = 0 := by
  rw [coherentCoefficient H K M ddA nu hcoh
    hxi0 hxi hzeta hxi0zeta, hxizeta]

theorem coherentCoefficient_eq_one
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (K M : Subgroup H)
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction J ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu)
    {xi0 zeta : ClassFunction L ℂ}
    (hxi0 : xi0 ∈ seqIndD (k := ℂ) H K M)
    (hzeta : zeta ∈ seqIndD (k := ℂ) H K M)
    (hxi0zeta : characterPairing xi0 zeta = 0)
    (hzetaSelf : characterPairing zeta zeta = 1) :
    invDadeSeqIndCoefficient ddA xi0 (nu zeta) zeta = 1 := by
  rw [coherentCoefficient H K M ddA nu hcoh
    hxi0 hzeta hzeta hxi0zeta, hzetaSelf]

private theorem residualKernel_zero_of_left
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L)
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (xi0 : ClassFunction L ℂ) (chi : ClassFunction J ℂ)
    (xi mu : ClassFunction L ℂ)
    (hzero : invDadeSeqIndCoefficient ddA xi0 chi xi = 0) :
    invDadeSeqIndU H ddA xi0 chi xi mu = 0 := by
  dsimp only [invDadeSeqIndU]
  rw [hzero]
  simp

private theorem residualKernel_zero_of_right
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L)
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (xi0 : ClassFunction L ℂ) (chi : ClassFunction J ℂ)
    (xi mu : ClassFunction L ℂ)
    (hzero : invDadeSeqIndCoefficient ddA xi0 chi mu = 0) :
    invDadeSeqIndU H ddA xi0 chi xi mu = 0 := by
  dsimp only [invDadeSeqIndU]
  rw [hzero]
  simp

theorem coherentResidualKernel
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (K M : Subgroup H)
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction J ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu)
    {xi0 xi mu zeta : ClassFunction L ℂ}
    (hxi0 : xi0 ∈ seqIndD (k := ℂ) H K M)
    (hxi : xi ∈ seqIndD (k := ℂ) H K M)
    (hmu : mu ∈ seqIndD (k := ℂ) H K M)
    (hzeta : zeta ∈ seqIndD (k := ℂ) H K M)
    (hxi0zeta : characterPairing xi0 zeta = 0)
    (hne : xi ≠ zeta ∨ mu ≠ zeta) :
    invDadeSeqIndU H ddA xi0 (nu zeta) xi mu = 0 := by
  rcases hne with hxiNe | hmuNe
  · apply residualKernel_zero_of_left
    exact coherentCoefficient_eq_zero H K M ddA nu hcoh
      hxi0 hxi hzeta hxi0zeta
      (seqInd_ortho H
        (seqIndD_mem_seqIndT H K M hxi)
        (seqIndD_mem_seqIndT H K M hzeta) hxiNe)
  · apply residualKernel_zero_of_right
    exact coherentCoefficient_eq_zero H K M ddA nu hcoh
      hxi0 hmu hzeta hxi0zeta
      (seqInd_ortho H
        (seqIndD_mem_seqIndT H K M hmu)
        (seqIndD_mem_seqIndT H K M hzeta) hmuNe)

/-! ### Reducing reciprocal-Dade sums to one term -/

theorem invDade_split_erase
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (xi0 : ClassFunction L ℂ) (chi : ClassFunction J ℂ)
    (hxi0 : xi0 ∈ seqIndT (k := ℂ) H) :
    IsInvDadeSeqIndSum H ddA xi0
      ((seqIndT (k := ℂ) H).erase xi0) chi := by
  apply invDade_seqInd_sum H ddA xi0
    ((seqIndT (k := ℂ) H).erase xi0) chi
  · exact (Finset.insert_erase hxi0).symm
  · simp

theorem invDade_value_eq_single
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (xi0 : ClassFunction L ℂ) (T : Finset (ClassFunction L ℂ))
    (chi : ClassFunction J ℂ)
    (hsplit : IsInvDadeSeqIndSum H ddA xi0 T chi)
    (xi : ClassFunction L ℂ) (hxi : xi ∈ T)
    (hcoeff : ∀ mu ∈ T, mu ≠ xi →
      invDadeSeqIndCoefficient ddA xi0 chi mu = 0)
    (a : L)
    (ha : (a : Gamma) ∈ subgroupNonidentity (H.map L.subtype)) :
    invDade ddA chi a =
      (star (invDadeSeqIndCoefficient ddA xi0 chi xi) /
          starCharacterPairing xi xi) * xi a := by
  rw [hsplit.value_on_support a ha]
  rw [Finset.sum_eq_single xi]
  · intro mu hmu hne
    rw [hcoeff mu hmu hne]
    simp
  · exact fun hxiNotMem ↦ (hxiNotMem hxi).elim

theorem invDade_pairing_eq_single
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (xi0 : ClassFunction L ℂ) (T : Finset (ClassFunction L ℂ))
    (chi : ClassFunction J ℂ)
    (hsplit : IsInvDadeSeqIndSum H ddA xi0 T chi)
    (xi : ClassFunction L ℂ) (hxi : xi ∈ T)
    (hU : ∀ mu ∈ T, ∀ nu ∈ T,
      mu ≠ xi ∨ nu ≠ xi →
        invDadeSeqIndU H ddA xi0 chi mu nu = 0) :
    starCharacterPairing (invDade ddA chi) (invDade ddA chi) =
      invDadeSeqIndU H ddA xi0 chi xi xi := by
  rw [hsplit.pairing_norm]
  rw [Finset.sum_eq_single xi]
  · rw [Finset.sum_eq_single xi]
    · intro nu hnu hne
      exact hU xi hxi nu hnu (Or.inr hne)
    · exact fun hxiNotMem ↦ (hxiNotMem hxi).elim
  · intro mu hmu hne
    apply Finset.sum_eq_zero
    intro nu hnu
    exact hU mu hmu nu hnu (Or.inl hne)
  · exact fun hxiNotMem ↦ (hxiNotMem hxi).elim

theorem invDade_normSq_eq_single
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (xi0 : ClassFunction L ℂ) (T : Finset (ClassFunction L ℂ))
    (chi : ClassFunction J ℂ)
    (hsplit : IsInvDadeSeqIndSum H ddA xi0 T chi)
    (xi : ClassFunction L ℂ) (hxi : xi ∈ T)
    (hU : ∀ mu ∈ T, ∀ nu ∈ T,
      mu ≠ xi ∨ nu ≠ xi →
        invDadeSeqIndU H ddA xi0 chi mu nu = 0) :
    classFunctionNormSq (invDade ddA chi) =
      (invDadeSeqIndU H ddA xi0 chi xi xi).re := by
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    invDade_pairing_eq_single H ddA xi0 T chi hsplit xi hxi hU]

theorem coherentNormSq_eq_single
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {J L : Subgroup Gamma} (H : Subgroup L) [H.Normal]
    (K M : Subgroup H)
    (ddA : DadeHypothesis J L
      (subgroupNonidentity (H.map L.subtype)))
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction J ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H K M) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu)
    (xi0 zeta : ClassFunction L ℂ)
    (hxi0 : xi0 ∈ seqIndD (k := ℂ) H K M)
    (hzeta : zeta ∈ seqIndD (k := ℂ) H K M)
    (T : Finset (ClassFunction L ℂ))
    (hT : ∀ xi ∈ T, xi ∈ seqIndD (k := ℂ) H K M)
    (hzetaT : zeta ∈ T)
    (hsplit : IsInvDadeSeqIndSum H ddA xi0 T (nu zeta))
    (hxi0zeta : characterPairing xi0 zeta = 0) :
    classFunctionNormSq (invDade ddA (nu zeta)) =
      (invDadeSeqIndU H ddA xi0 (nu zeta) zeta zeta).re := by
  apply invDade_normSq_eq_single H ddA xi0 T (nu zeta)
    hsplit zeta hzetaT
  intro xi hxi mu hmu hne
  exact coherentResidualKernel H K M ddA nu hcoh hxi0
    (hT xi hxi) (hT mu hmu) hzeta hxi0zeta hne

end FTTypePBoundsInfrastructureInternal

/-! ### Fixed nonprincipal cyclic-factor indices -/

noncomputable def ftTypePLeftIndex
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    IrreducibleCharacter W₁ ℂ := by
  letI : IsCyclic W₁ := ctx.primeTI.prime_cycTIhyp.left_cyclic
  exact Classical.choose
    (IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := ℂ) ctx.primeTI.prime_cycTIhyp.one_lt_card_left)

noncomputable def ftTypePRightIndex
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    IrreducibleCharacter W₂ ℂ := by
  letI : IsCyclic W₂ := ctx.primeTI.prime_cycTIhyp.right_cyclic
  exact Classical.choose
    (IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := ℂ) ctx.primeTI.prime_cycTIhyp.one_lt_card_right)

namespace FTTypePBoundsInfrastructureInternal

theorem leftIndex_ne_trivial
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ftTypePLeftIndex ctx ≠ IrreducibleCharacter.trivial := by
  letI : IsCyclic W₁ := ctx.primeTI.prime_cycTIhyp.left_cyclic
  exact Classical.choose_spec
    (IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := ℂ) ctx.primeTI.prime_cycTIhyp.one_lt_card_left)

theorem rightIndex_ne_trivial
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ftTypePRightIndex ctx ≠ IrreducibleCharacter.trivial := by
  letI : IsCyclic W₂ := ctx.primeTI.prime_cycTIhyp.right_cyclic
  exact Classical.choose_spec
    (IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := ℂ) ctx.primeTI.prime_cycTIhyp.one_lt_card_right)

end FTTypePBoundsInfrastructureInternal

end

end Submission.OddOrder.PF
