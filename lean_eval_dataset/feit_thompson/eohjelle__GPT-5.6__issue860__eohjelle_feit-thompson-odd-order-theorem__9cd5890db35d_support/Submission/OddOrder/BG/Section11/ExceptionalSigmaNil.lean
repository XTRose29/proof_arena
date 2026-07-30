import Submission.OddOrder.BG.Section03.FrobeniusNilpotentKernel
import Submission.OddOrder.BG.Section03.SemidirectProperKernel
import Submission.OddOrder.BG.Section10.SigmaDisjoint
import Submission.OddOrder.BG.Section11.ExceptionalTI

/-!
# Bender--Glauberman Section 11: nilpotence of the exceptional sigma core

This file ports `BGsection11.v: exceptional_sigma_nil` and
`exceptional_sigma_uniq` (Theorem 11.3 and Corollary 11.4).
-/

namespace Submission.OddOrder.BG.Section11

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport

universe u

/-- A normalized disjoint pair is complementary inside the subgroup it
generates. -/
private theorem subgroupOf_sup_isComplement
    {G : Type u} [Group G] {H R : Subgroup G}
    (hnorm : R ≤ Subgroup.normalizer (H : Set G))
    (hdis : Disjoint H R) :
    (H.subgroupOf (R ⊔ H)).IsComplement'
      (R.subgroupOf (R ⊔ H)) := by
  let J : Subgroup G := R ⊔ H
  let HJ : Subgroup J := H.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  letI : HJ.Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
  have hdisJ : Disjoint HJ RJ := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hxbot : ((x : J) : G) ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hdis]
      exact ⟨hx.1, hx.2⟩
    exact Subgroup.mem_bot.mp hxbot
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisJ
  have hnormJ : RJ ≤ Subgroup.normalizer (HJ : Set J) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : HJ.Normal)]
    exact le_top
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left HJ RJ hnormJ]
  have hsup : HJ ⊔ RJ = ⊤ := by
    change H.subgroupOf J ⊔ R.subgroupOf J = ⊤
    rw [← Subgroup.subgroupOf_sup (show H ≤ J from le_sup_right)
      (show R ≤ J from le_sup_left)]
    simp [J, sup_comm]
  rw [hsup]
  rfl

/-- `BGsection11.v: exceptional_sigma_nil` (Bender--Glauberman
Theorem 11.3).  The sigma core of an exceptional maximal subgroup is
nilpotent. -/
theorem exceptional_sigma_nil
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} {M A₀ A : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hExc : exceptional_FTmaximal p M A₀ A)
    (P : Sylow p M) (hAP : A ≤ ambientSylow M P) :
    Group.IsNilpotent (sigmaCore M) := by
  classical
  letI : Fact p.Prime := ⟨hExc.prime⟩
  let PG : Subgroup G := ambientSylow M P
  have hnotNormalizer :
      ¬ Subgroup.normalizer (PG : Set G) ≤ M := by
    simpa [PG] using
      sigma'_Sylow_contra hExc.prime P hExc.sigma_compl
  obtain ⟨g, hgNormalizer, hgM⟩ :=
    Set.not_subset.mp hnotNormalizer
  let e : G ≃* G := MulAut.conj g⁻¹
  have hPGM : PG ≤ M := by
    exact Subgroup.map_subtype_le (P : Subgroup M)
  have hPGmap : PG.map e.toMonoidHom = PG := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    exact (Subgroup.normalizer (PG : Set G)).inv_mem hgNormalizer
  have hAMg : A ≤ M.map e.toMonoidHom := by
    calc
      A ≤ PG := hAP
      _ = PG.map e.toMonoidHom := hPGmap.symm
      _ ≤ M.map e.toMonoidHom := Subgroup.map_mono hPGM
  let S : Subgroup G := sigmaCore M
  let R : Subgroup G := A₀.map e.toMonoidHom
  have hRM : R ≤ M := by
    calc
      R ≤ PG.map e.toMonoidHom :=
        Subgroup.map_mono (hExc.A₀_le.trans hAP)
      _ = PG := hPGmap
      _ ≤ M := hPGM
  have hMnormS : M ≤ Subgroup.normalizer (S : Set G) := by
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (sigmaCore_le M)).mp (sigmaCore_normal M)
  have hRnormS : R ≤ Subgroup.normalizer (S : Set G) :=
    hRM.trans hMnormS
  have hcardR : Nat.card R = Nat.card A₀ := by
    simpa [R] using
      (Subgroup.card_map_of_injective
        (K := A₀) (f := e.toMonoidHom) e.injective)
  have hcopSA₀ : (Nat.card S).Coprime (Nat.card A₀) := by
    apply Nat.coprime_of_dvd
    intro q hq hqS hqA₀
    have hqSigma : q ∈ sigmaPrimes M :=
      sigmaCore_isPiNumber M hq hqS
    have hqpow : q ∣ p ^ 1 := by
      simpa only [hExc.A₀_rank_one.card_eq] using hqA₀
    have hqp : q = p :=
      Nat.prime_eq_prime_of_dvd_pow hq hExc.prime hqpow
    rw [hqp] at hqSigma
    exact hExc.sigma_compl hqSigma
  have hcopSR : (Nat.card S).Coprime (Nat.card R) := by
    rwa [hcardR]
  have hdisSR : Disjoint S R :=
    Subgroup.disjoint_of_coprime_natCard hcopSR
  let F : Subgroup G := R ⊔ S
  let K : Subgroup F := S.subgroupOf F
  let T : Subgroup F := R.subgroupOf F
  have hFM : F ≤ M := by
    exact sup_le hRM (sigmaCore_le M)
  have hKnormal : K.Normal := by
    dsimp only [K, F]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hRnormS
  have hcomp : K.IsComplement' T := by
    simpa only [K, T, F] using
      subgroupOf_sup_isComplement hRnormS hdisSR
  have hTprime : (Nat.card T).Prime := by
    have hcardT : Nat.card T = Nat.card R :=
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        (show R ≤ F from le_sup_left)
    rw [hcardT, hcardR, hExc.A₀_rank_one.card_eq, pow_one]
    exact hExc.prime
  have hsolF : IsSolvable F :=
    mFT_sol (sub_mmax_proper hM hFM)
  have hcentAmbient :
      S ⊓ Subgroup.centralizer (R : Set G) = ⊥ := by
    simpa only [S, R, e] using
      (exceptional_TI_MsigmaJ hM hExc P hAP g hgM hAMg).2
  have hcentK : centralizerWithin K T = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hxAmbient :
        ((x : F) : G) ∈
          S ⊓ Subgroup.centralizer (R : Set G) := by
      refine ⟨(mem_centralizerWithin.mp hx).1, ?_⟩
      change ∀ r : G, r ∈ R →
        r * ((x : F) : G) = ((x : F) : G) * r
      intro r hr
      let rF : F := ⟨r, (show R ≤ F from le_sup_left) hr⟩
      have hrT : rF ∈ T := hr
      exact congrArg Subtype.val
        ((mem_centralizerWithin.mp hx).2 rF hrT)
    have hxbot : ((x : F) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hcentAmbient]
      exact hxAmbient
    exact Subgroup.mem_bot.mp hxbot
  have hnilK : Group.IsNilpotent K :=
    prime_Frobenius_sol_kernel_nil
      hcomp hKnormal hsolF hTprime hcentK
  let eKS : K ≃* S :=
    Subgroup.subgroupOfEquivOfLe
      (show S ≤ F from le_sup_right)
  exact (Group.isNilpotent_congr eKS).mp hnilK

/-- `BGsection11.v: exceptional_sigma_uniq` (Bender--Glauberman
Corollary 11.4).  An exceptional maximal subgroup is the unique maximal
overgroup of `A` whose sigma core meets its sigma core nontrivially. -/
theorem exceptional_sigma_uniq
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} {M A₀ A : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hExc : exceptional_FTmaximal p M A₀ A)
    (P : Sylow p M) (hAP : A ≤ ambientSylow M P)
    (H : Subgroup G)
    (hH : H ∈ minSimple_max_groups_of (G := G) (A : Set G))
    (hcore : sigmaCore H ⊓ sigmaCore M ≠ ⊥) :
    H = M := by
  classical
  have hnil : Group.IsNilpotent (sigmaCore M) :=
    exceptional_sigma_nil hM hExc P hAP
  have hcore' : sigmaCore M ⊓ sigmaCore H ≠ ⊥ := by
    simpa only [inf_comm] using hcore
  have hconj :
      ∃ g : G, H = M.map (MulAut.conj g).toMonoidHom := by
    by_contra hnone
    push Not at hnone
    exact hcore'
      (sigmaCore_inf_sigmaCore_eq_bot_of_nilpotent
        hM hH.1 hnone hnil)
  obtain ⟨g, hHg⟩ := hconj
  by_contra hHM
  have hgM : g ∉ M := by
    intro hgM
    have hmap : M.map (MulAut.conj g).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer hgM)
    exact hHM (hHg.trans hmap)
  have hginvM : g⁻¹ ∉ M := by
    intro hginvM
    apply hgM
    simpa using M.inv_mem hginvM
  have hAMg : A ≤ M.map (MulAut.conj g).toMonoidHom := by
    rw [← hHg]
    exact hH.2
  have hti :=
    (exceptional_TI_MsigmaJ hM hExc P hAP g⁻¹ hginvM
      (by simpa only [inv_inv] using hAMg)).1
  have htiH : sigmaCore M ⊓ H = ⊥ := by
    simpa only [inv_inv, ← hHg] using hti
  have hcoreBot : sigmaCore M ⊓ sigmaCore H = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← htiH]
    exact inf_le_inf le_rfl (sigmaCore_le H)
  exact hcore' hcoreBot

end Submission.OddOrder.BG.Section11
