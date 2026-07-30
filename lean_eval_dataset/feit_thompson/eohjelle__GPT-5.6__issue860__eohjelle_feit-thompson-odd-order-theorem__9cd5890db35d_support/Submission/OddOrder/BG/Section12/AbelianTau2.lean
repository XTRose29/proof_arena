import Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect
import Submission.OddOrder.BG.Section12.NonabelianTau2

/-!
# Bender--Glauberman Section 12: the abelian `tau2` case

This file ports `BGsection12.v`, lines 1003--1315.  It contains the
abelian-Sylow half of Theorem 12.8 and Corollary 12.9.  As in the preceding
Section 12 files, MathComp membership in a family of elementary-abelian
subgroups is represented by a containment and an
`IsElementaryAbelianOfRank` proof.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport
open scoped commutatorElement IsMulCommutative Pointwise

noncomputable section

universe u

/-- The five conclusions of `BGsection12.v: abelian_tau2_sub_Fitting`.

All subgroups are kept in the common ambient group.  Thus the derived
subgroup of a normalizer is expressed by the ambient subgroup commutator,
and the two Fitting subgroups by `fittingWithin`. -/
structure AbelianTau2SubFittingConclusion
    {G : Type u} [Group G] (E A S : Subgroup G) : Prop where
  sylow_le_normalizer_commutator :
    S ≤ ⁅Subgroup.normalizer (S : Set G),
      Subgroup.normalizer (S : Set G)⁆
  normalizer_commutator_le_fitting :
    ⁅Subgroup.normalizer (S : Set G),
      Subgroup.normalizer (S : Set G)⁆ ≤ fittingWithin E
  fitting_le_centralizer :
    fittingWithin E ≤ Subgroup.centralizer (S : Set G)
  centralizer_le_complement :
    Subgroup.centralizer (S : Set G) ≤ E
  fitting_normalizer_eq :
    fittingWithin (Subgroup.normalizer (A : Set G)) = fittingWithin E

/-- The conclusions of Theorem 12.8(a), (b), (d), and (e). -/
structure AbelianTau2Conclusion
    {G : Type u} [Group G] [Finite G]
    (M E E₁ E₂ E₃ A S : Subgroup G) : Prop where
  E₂_normal : (E₂.subgroupOf E).Normal
  E₂_abelian : IsMulCommutative E₂
  E₂_hall : IsHall (tau2Primes M) E₂
  normalizer_A_eq_S :
    Subgroup.normalizer (A : Set G) = Subgroup.normalizer (S : Set G)
  normalizer_S_eq_E₂ :
    Subgroup.normalizer (S : Set G) = Subgroup.normalizer (E₂ : Set G)
  normalizer_E₂_eq_E₃_join_E₂ :
    Subgroup.normalizer (E₂ : Set G) =
      Subgroup.normalizer ((E₃ ⊔ E₂ : Subgroup G) : Set G)
  normalizer_E₃_join_E₂_eq_fitting :
    Subgroup.normalizer ((E₃ ⊔ E₂ : Subgroup G) : Set G) =
      Subgroup.normalizer (fittingWithin E : Set G)
  regular_rank_one_central :
    ∀ {q : ℕ} [Fact q.Prime] {X : Subgroup G},
      RankOneLineIn q E₁ X →
      centralizerWithin (sigmaCore M) X = ⊥ →
      X ≤ centerWithin E

/-- The two subgroups in Corollary 12.9. -/
def tau1ActionCommutator
    {G : Type u} [Group G] (A Q : Subgroup G) : Subgroup G :=
  ⁅A, Q⁆

/-- The fixed line in the rank-two elementary-abelian group in Corollary
12.9. -/
def tau1ActionFixedLine
    {G : Type u} [Group G] (A Q : Subgroup G) : Subgroup G :=
  centralizerWithin A Q

/-- The three conclusions of `BGsection12.v: tau1_act_tau2`. -/
structure Tau1ActTau2Conclusion
    {G : Type u} [Group G]
    (M A Q : Subgroup G) (p : ℕ) : Prop where
  A0_rank_one : RankOneLineIn p A (tau1ActionCommutator A Q)
  A0_sigma_centralizer :
    centralizerWithin A (sigmaCore M) = tau1ActionCommutator A Q
  A0_normal : ((tau1ActionCommutator A Q).subgroupOf M).Normal
  A0_not_conjugate_to_A1 :
    ∀ g : G, tau1ActionCommutator A Q ≠
      (tau1ActionFixedLine A Q).map (MulAut.conj g).toMonoidHom
  A1_rank_one : RankOneLineIn p A (tau1ActionFixedLine A Q)
  A1_centralizer_not_le :
    ¬ Subgroup.centralizer (tau1ActionFixedLine A Q : Set G) ≤ M

private theorem isMulCommutative_of_le
    {G : Type u} [Group G] {B C : Subgroup G}
    (hB : IsMulCommutative B) (hCB : C ≤ B) :
    IsMulCommutative C := by
  letI : IsMulCommutative B := hB
  apply isMulCommutative_iff.mpr
  intro x y
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  exact congrArg (fun z : B => (z : G))
    (mul_comm (⟨x, hCB x.2⟩ : B) (⟨y, hCB y.2⟩ : B))

private theorem isMulCommutative_of_mulEquiv
    {G K : Type u} [Group G] [Group K]
    (hG : IsMulCommutative G) (e : G ≃* K) :
    IsMulCommutative K := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply e.symm.injective
  simpa only [map_mul] using
    (isMulCommutative_iff.mp hG (e.symm x) (e.symm y))

/-- The ambient image of a characteristic subgroup is normalized by the
ambient normalizer. -/
private theorem characteristic_map_subtype_le_normalizer
    {G : Type u} [Group G] (H : Subgroup G)
    (R : Subgroup H) [R.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (R.map H.subtype : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact characteristic_map_subtype_invariant_under_normalizer
      H (Subgroup.normalizer (H : Set G)) R le_rfl g hg r hr
  · intro hr
    have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).inv_mem hg
    have hback := characteristic_map_subtype_invariant_under_normalizer
      H (Subgroup.normalizer (H : Set G)) R le_rfl
      g⁻¹ hginv (g * r * g⁻¹) hr
    have hcancel : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by
      group
    simpa only [hcancel] using hback

/-- Ambient form of the maximality property defining the Fitting subgroup. -/
private theorem nilpotent_normal_le_fittingWithin
    {G : Type u} [Group G] [Finite G]
    {K H : Subgroup G} (hKH : K ≤ H)
    (hKnormal : (K.subgroupOf H).Normal)
    (hKnil : Group.IsNilpotent K) :
    K ≤ fittingWithin H := by
  let KH : Subgroup H := K.subgroupOf H
  let eKH : KH ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  letI : Group.IsNilpotent K := hKnil
  letI : KH.Normal := hKnormal
  letI : Group.IsNilpotent KH :=
    Group.nilpotent_of_mulEquiv eKH.symm
  have hcore : KH ≤ fittingCore H :=
    nilpotent_normal_le_fittingCore (by infer_instance) (by infer_instance)
  rw [← Subgroup.map_subgroupOf_eq_of_le hKH]
  exact Subgroup.map_mono hcore

/-- In a finite nilpotent subgroup, the `p`-core is abelian whenever one
ambient Sylow `p`-subgroup is abelian. -/
private theorem pCore_isMulCommutative_of_ambient_sylow
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (F : Subgroup G) [Group.IsNilpotent F]
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    IsMulCommutative (pCore p F) := by
  let P : Sylow p F := Classical.choice Sylow.nonempty
  let PG : Subgroup G := (P : Subgroup F).map F.subtype
  have hPGp : IsPGroup p PG := P.isPGroup'.map F.subtype
  obtain ⟨T, hPGT⟩ := hPGp.exists_le_sylow
  have hTcomm : IsMulCommutative (T : Subgroup G) := by
    exact isMulCommutative_of_mulEquiv hScomm (Sylow.equiv S T)
  have hPGcomm : IsMulCommutative PG :=
    isMulCommutative_of_le hTcomm hPGT
  let ePG : (P : Subgroup F) ≃* PG :=
    (P : Subgroup F).equivMapOfInjective F.subtype F.subtype_injective
  have hPcomm : IsMulCommutative (P : Subgroup F) :=
    isMulCommutative_of_mulEquiv hPGcomm ePG.symm
  rw [pCore_eq_sylow_of_isNilpotent P]
  exact hPcomm

/-- An abelian ambient Sylow subgroup lying in a finite nilpotent subgroup
is central there. -/
private theorem ambient_sylow_le_centerWithin_of_isNilpotent
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {F : Subgroup G} [Group.IsNilpotent F]
    (hSF : (S : Subgroup G) ≤ F)
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    (S : Subgroup G) ≤ centerWithin F := by
  let SF : Sylow p F := S.subtype hSF
  have hSFcomm : IsMulCommutative (SF : Subgroup F) := by
    let e :=
      (SF : Subgroup F).equivMapOfInjective F.subtype
        F.subtype_injective
    have hmap : (SF : Subgroup F).map F.subtype =
        (S : Subgroup G) := by
      change ((S : Subgroup G).subgroupOf F).map F.subtype =
        (S : Subgroup G)
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hSF hx⟩, hx, rfl⟩
    have hmapComm :
        IsMulCommutative ((SF : Subgroup F).map F.subtype) := by
      rw [hmap]
      exact hScomm
    exact isMulCommutative_of_mulEquiv hmapComm e.symm
  have hcore : pCore p F = (SF : Subgroup F) :=
    pCore_eq_sylow_of_isNilpotent SF
  have hcoreComm : IsMulCommutative (pCore p F) := by
    rw [hcore]
    exact hSFcomm
  have hcoreCentCore :
      pCore p F ≤ Subgroup.centralizer (pCore p F : Set F) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hcoreComm
  have hcoreCentPrime :
      pCore p F ≤ Subgroup.centralizer (pPrimeCore p F : Set F) :=
    pCore_le_centralizer_pPrimeCore p
  have hprimeCentCore :
      pPrimeCore p F ≤ Subgroup.centralizer (pCore p F : Set F) :=
    Subgroup.le_centralizer_iff.mp hcoreCentPrime
  have htopCentCore :
      (⊤ : Subgroup F) ≤ Subgroup.centralizer (pCore p F : Set F) := by
    rw [← sup_pCore_pPrimeCore_eq_top_of_isNilpotent (G := F) p]
    exact sup_le hcoreCentCore hprimeCentCore
  intro s hs
  refine mem_centerWithin.mpr ⟨hSF hs, ?_⟩
  intro f hf
  let sF : F := ⟨s, hSF hs⟩
  let fF : F := ⟨f, hf⟩
  have hsCore : sF ∈ pCore p F := by
    rw [hcore]
    exact hs
  have hfCent : fF ∈ Subgroup.centralizer (pCore p F : Set F) :=
    htopCentCore (by simp)
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp hfCent sF hsCore).symm

/-- The Fitting subgroup of a group and of the centralizer of a normal
`p`-subgroup agree when that subgroup lies in an abelian ambient Sylow
subgroup.  This is the local identity `eqFC` in the Coq proof. -/
private theorem fittingWithin_eq_fittingWithin_centralizer
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {A H : Subgroup G}
    (hAH : A ≤ H) (hAnormal : (A.subgroupOf H).Normal)
    (hcentH : Subgroup.centralizer (A : Set G) ≤ H)
    (hAp : IsPGroup p A)
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    fittingWithin H =
      fittingWithin (Subgroup.centralizer (A : Set G)) := by
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  let F : Subgroup G := fittingWithin H
  have hHnormA : H ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hAnormal
  have hNAnormC :
      Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer (C : Set G) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (A : Set G))).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer (A : Set G))
  have hHnormC : H ≤ Subgroup.normalizer (C : Set G) :=
    hHnormA.trans hNAnormC
  have hFCAH : fittingWithin C ≤ H :=
    (fittingWithin_le C).trans hcentH
  have hHnormFC : H ≤ Subgroup.normalizer (fittingWithin C : Set G) :=
    le_normalizer_fittingWithin_of_le_normalizer hHnormC
  have hFCnormalH : ((fittingWithin C).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFCAH).mpr hHnormFC
  have hFCF : fittingWithin C ≤ F :=
    nilpotent_normal_le_fittingWithin hFCAH hFCnormalH
      (by infer_instance)
  have hAF : A ≤ F :=
    nilpotent_normal_le_fittingWithin hAH hAnormal hAp.isNilpotent
  let AF : Subgroup F := A.subgroupOf F
  letI : Group.IsNilpotent F := fittingWithin_isNilpotent H
  have hAFp : IsPGroup p AF := by
    let eAF : AF ≃* A := Subgroup.subgroupOfEquivOfLe hAF
    exact hAp.of_equiv eAF.symm
  have hAFcore : AF ≤ pCore p F :=
    hAFp.le_pCore_of_isNilpotent
  have hcoreComm : IsMulCommutative (pCore p F) :=
    pCore_isMulCommutative_of_ambient_sylow S F hScomm
  have hcoreCentCore :
      pCore p F ≤ Subgroup.centralizer (pCore p F : Set F) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hcoreComm
  have hcoreCentPrime :
      pCore p F ≤ Subgroup.centralizer (pPrimeCore p F : Set F) :=
    pCore_le_centralizer_pPrimeCore p
  have hprimeCentCore :
      pPrimeCore p F ≤ Subgroup.centralizer (pCore p F : Set F) :=
    Subgroup.le_centralizer_iff.mp hcoreCentPrime
  have hcoreCentAF :
      pCore p F ≤ Subgroup.centralizer (AF : Set F) :=
    hcoreCentCore.trans (Subgroup.centralizer_le hAFcore)
  have hprimeCentAF :
      pPrimeCore p F ≤ Subgroup.centralizer (AF : Set F) :=
    hprimeCentCore.trans (Subgroup.centralizer_le hAFcore)
  have htopCentAF :
      (⊤ : Subgroup F) ≤ Subgroup.centralizer (AF : Set F) := by
    rw [← sup_pCore_pPrimeCore_eq_top_of_isNilpotent (G := F) p]
    exact sup_le hcoreCentAF hprimeCentAF
  have hFC : F ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    let xF : F := ⟨x, hx⟩
    let aF : F := ⟨a, hAF ha⟩
    have hxCent : xF ∈ Subgroup.centralizer (AF : Set F) :=
      htopCentAF (by simp)
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hxCent aF ha)
  have hFnormC : C ≤ Subgroup.normalizer (F : Set G) :=
    hcentH.trans (fittingWithin_le_normalizer H)
  have hFnormalC : (F.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFC).mpr hFnormC
  have hFFC : F ≤ fittingWithin C :=
    nilpotent_normal_le_fittingWithin hFC hFnormalC (by infer_instance)
  exact le_antisymm hFFC hFCF

/-- `BGsection12.v: abelian_tau2_sub_Fitting`, Theorem 12.8(c). -/
theorem abelian_tau2_sub_Fitting
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E A : Subgroup G} {p : ℕ} (S : Sylow p G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    AbelianTau2SubFittingConclusion E A (S : Subgroup G) := by
  classical
  letI : Fact p.Prime := ⟨hpTau.1⟩
  let NA : Subgroup G := Subgroup.normalizer (A : Set G)
  let NS : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G)
  have hAM : A ≤ M := hAE.trans hEM
  have hctx := tau2_compl_context hM hEM hHall hpTau hAE hA
  have hScentA : (S : Subgroup G) ≤ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact hAS.trans
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr hScomm)
  have hSE : (S : Subgroup G) ≤ E :=
    hScentA.trans hctx.centralizer_le_E
  have hSM : (S : Subgroup G) ≤ M := hSE.trans hEM
  have hFEqC :
      fittingWithin E = fittingWithin (Subgroup.centralizer (A : Set G)) :=
    fittingWithin_eq_fittingWithin_centralizer S hAE hctx.A_normal
      hctx.centralizer_le_E hA.isPGroup hScomm
  have hNAEqC :
      fittingWithin NA = fittingWithin (Subgroup.centralizer (A : Set G)) := by
    apply fittingWithin_eq_fittingWithin_centralizer S
    · exact Subgroup.le_normalizer
    · infer_instance
    · exact Subgroup.centralizer_le_normalizer (A : Set G)
    · exact hA.isPGroup
    · exact hScomm
  have hFNAFE : fittingWithin NA = fittingWithin E :=
    hNAEqC.trans hFEqC.symm
  have hNAproper : NA < ⊤ :=
    mFT_norm_proper A hA.ne_bot (mFT_pgroup_proper A hA.isPGroup)
  have hNAsol : IsSolvable NA := mFT_sol hNAproper
  have hNArank :
      ∀ q : ℕ, q.Prime →
        ¬ ∃ B : Subgroup (fittingCore NA),
          IsElementaryAbelianOfRank q 3 B := by
    intro q hq
    rintro ⟨B, hB⟩
    letI : Fact q.Prime := ⟨hq⟩
    let BNA : Subgroup NA := B.map (fittingCore NA).subtype
    let BG : Subgroup G := BNA.map NA.subtype
    have hBG : IsElementaryAbelianOfRank q 3 BG := by
      exact (hB.map_of_injective (fittingCore NA).subtype
        (fittingCore NA).subtype_injective).map_of_injective
          NA.subtype NA.subtype_injective
    have hBGFNA : BG ≤ fittingWithin NA := by
      dsimp [BG, BNA, fittingWithin]
      exact Subgroup.map_mono (Subgroup.map_subtype_le B)
    have hBGE : BG ≤ E := by
      rw [hFNAFE] at hBGFNA
      exact hBGFNA.trans (fittingWithin_le E)
    have hBGM : BG ≤ M := hBGE.trans hEM
    have hqBG : q ∣ Nat.card BG := by
      rw [hBG.card_eq]
      exact dvd_pow_self q (by omega)
    have hqE : q ∣ Nat.card E :=
      hqBG.trans (Subgroup.card_dvd_of_le hBGE)
    have hqEM : q ∣ Nat.card (E.subgroupOf M) := by
      rwa [natCard_subgroupOf_eq hEM]
    have hqNotSigma : q ∉ sigmaPrimes M :=
      hHall.isPiNumber_card hq hqEM
    exact hqNotSigma (alpha_sub_sigma hM ⟨hq, BG, hBGM, hBG⟩)
  have hNAderCore : _root_.commutator NA ≤ fittingCore NA :=
    rank2_der1_sub_Fitting (mFT_odd NA) hNAsol hNArank
  have hNAderFNA : ⁅NA, NA⁆ ≤ fittingWithin NA := by
    rw [← NA.map_subtype_commutator]
    exact Subgroup.map_mono hNAderCore
  have hTauCtx := tau2_context hM hpTau hAM hA
  let SM : Sylow p M := S.subtype hSM
  have hAmbientSM : ambientSylow M SM = (S : Subgroup G) := by
    change ((S : Subgroup G).subgroupOf M).map M.subtype =
      (S : Subgroup G)
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hSM hx⟩, hx, rfl⟩
  have hOmega :
      (omegaOne p (S : Subgroup G)).map (S : Subgroup G).subtype = A := by
    calc
      (omegaOne p (S : Subgroup G)).map (S : Subgroup G).subtype =
          (omegaOne p (ambientSylow M SM)).map
            (ambientSylow M SM).subtype :=
        congrArg
          (fun P : Subgroup G => (omegaOne p P).map P.subtype)
          hAmbientSM.symm
      _ = A := hTauCtx.omegaOne_eq SM (hAS.trans hAmbientSM.ge)
  have hNSNA : NS ≤ NA := by
    dsimp [NS, NA]
    rw [← hOmega]
    exact characteristic_map_subtype_le_normalizer
      (S : Subgroup G) (omegaOne p (S : Subgroup G))
  have hNSderNAder : ⁅NS, NS⁆ ≤ ⁅NA, NA⁆ :=
    Subgroup.commutator_mono hNSNA hNSNA
  have hNSderFE : ⁅NS, NS⁆ ≤ fittingWithin E :=
    hNSderNAder.trans (hNAderFNA.trans_eq hFNAFE)
  have hSNSder : (S : Subgroup G) ≤ ⁅NS, NS⁆ := by
    calc
      (S : Subgroup G) ≤
          (_root_.commutator NS).map NS.subtype := by
        simpa [NS] using mFT_Sylow_der1 S
      _ = ⁅NS, NS⁆ := NS.map_subtype_commutator
  have hSFE : (S : Subgroup G) ≤ fittingWithin E :=
    hSNSder.trans hNSderFE
  letI : Group.IsNilpotent (fittingWithin E) :=
    fittingWithin_isNilpotent E
  have hSZF : (S : Subgroup G) ≤ centerWithin (fittingWithin E) :=
    ambient_sylow_le_centerWithin_of_isNilpotent S hSFE hScomm
  have hFECentS : fittingWithin E ≤ Subgroup.centralizer (S : Set G) :=
    Subgroup.le_centralizer_iff.mp (hSZF.trans inf_le_right)
  have hCentSE : Subgroup.centralizer (S : Set G) ≤ E := by
    exact (Subgroup.centralizer_le hAS).trans hctx.centralizer_le_E
  exact
    { sylow_le_normalizer_commutator := hSNSder
      normalizer_commutator_le_fitting := hNSderFE
      fitting_le_centralizer := hFECentS
      centralizer_le_complement := hCentSE
      fitting_normalizer_eq := hFNAFE }

private theorem isHall_subgroupOf_of_le
    {G : Type u} [Group G] [Finite G]
    {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    {pi : Set ℕ} (hA : IsHall pi (A.subgroupOf C)) :
    IsHall pi (A.subgroupOf B) := by
  constructor
  · rw [natCard_subgroupOf_eq hAB]
    have hcard := hA.isPiNumber_card
    rwa [natCard_subgroupOf_eq (hAB.trans hBC)] at hcard
  · have hdvd : A.relIndex B ∣ A.relIndex C := by
      refine ⟨B.relIndex C, ?_⟩
      exact (A.relIndex_mul_relIndex B C hAB hBC).symm
    exact hA.isPiNumber_index.of_dvd hdvd

private theorem isHall_of_isHall_subgroupOf
    {G : Type u} [Group G] [Finite G]
    {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    {pi rho : Set ℕ} (hpi : pi ⊆ rho)
    (hA : IsHall pi (A.subgroupOf B))
    (hB : IsHall rho (B.subgroupOf C)) :
    IsHall pi (A.subgroupOf C) := by
  constructor
  · rw [natCard_subgroupOf_eq (hAB.trans hBC)]
    have hcard := hA.isPiNumber_card
    rwa [natCard_subgroupOf_eq hAB] at hcard
  · have hBindex : IsPiNumber piᶜ (B.relIndex C) := by
      apply hB.isPiNumber_index.mono
      intro r hrNotRho hrPi
      exact hrNotRho (hpi hrPi)
    change IsPiNumber piᶜ (A.relIndex C)
    rw [← A.relIndex_mul_relIndex B C hAB hBC]
    exact hA.isPiNumber_index.mul hBindex

private theorem sylow_isHall_singleton
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    IsHall ({p} : Set ℕ) (P : Subgroup G) := by
  constructor
  · exact P.isPGroup'.isPiNumber_natCard (Set.mem_singleton p)
  · intro q hq hqIndex hqp
    have : q = p := Set.mem_singleton_iff.mp hqp
    subst q
    exact P.not_dvd_index hqIndex

/-- The Sylow calculation at the start of the proof of Theorem 12.8(a,b,d,e).
Every nontrivial Sylow subgroup of `E₂` is already ambient Sylow and is
central in the Fitting subgroup of the complement. -/
private theorem tau2_sylow_central_of_abelian_tau2
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₂ : Subgroup G} {p q : ℕ}
    (S : Sylow p G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hE₂E : E₂ ≤ E)
    (hHallE₂ : IsHall (tau2Primes M) (E₂.subgroupOf E))
    (hpTau : p ∈ tau2Primes M)
    (hqTau : q ∈ tau2Primes M)
    (hScomm : IsMulCommutative (S : Subgroup G))
    (Q : Sylow q E₂) :
    let QG := (Q : Subgroup E₂).map E₂.subtype
    ∃ T : Sylow q G,
      (T : Subgroup G) = QG ∧ QG ≤ centerWithin (fittingWithin E) := by
  classical
  dsimp only
  letI : Fact q.Prime := ⟨hqTau.1⟩
  let QG : Subgroup G := (Q : Subgroup E₂).map E₂.subtype
  have hQGE₂ : QG ≤ E₂ := Subgroup.map_subtype_le _
  have hQGE : QG ≤ E := hQGE₂.trans hE₂E
  have hQHallE₂ : IsHall ({q} : Set ℕ) (QG.subgroupOf E₂) := by
    have hmap : QG.subgroupOf E₂ = (Q : Subgroup E₂) := by
      change ((Q : Subgroup E₂).map E₂.subtype).comap E₂.subtype =
        (Q : Subgroup E₂)
      exact Subgroup.comap_map_eq_self_of_injective
        E₂.subtype_injective (Q : Subgroup E₂)
    rw [hmap]
    exact sylow_isHall_singleton Q
  have hQHallE : IsHall ({q} : Set ℕ) (QG.subgroupOf E) :=
    isHall_of_isHall_subgroupOf hQGE₂ hE₂E
      (by simpa only [Set.singleton_subset_iff] using hqTau)
      hQHallE₂ hHallE₂
  have hQEp : IsPGroup q (QG.subgroupOf E) := by
    let e : QG.subgroupOf E ≃* QG :=
      Subgroup.subgroupOfEquivOfLe hQGE
    have hQGp : IsPGroup q QG := Q.isPGroup'.map E₂.subtype
    exact hQGp.of_equiv e.symm
  have hqNotIndexE : ¬ q ∣ (QG.subgroupOf E).index := by
    intro hqIndex
    exact hQHallE.isPiNumber_index Fact.out hqIndex
      (Set.mem_singleton q)
  let QE : Sylow q E := hQEp.toSylow hqNotIndexE
  have hQEAmbient :
      (QE : Subgroup E).map E.subtype = QG := by
    change (QG.subgroupOf E).map E.subtype = QG
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hQGE hx⟩, hx, rfl⟩
  obtain ⟨B, hBE, _hBM, hB⟩ := ex_tau2Elem hEM hHall hqTau
  obtain ⟨e, heB⟩ := exists_conjugate_le_sylow_map QE hBE hB.isPGroup
  let B' : Subgroup G := B.map (MulAut.conj (e : G)).toMonoidHom
  have hB'Q : B' ≤ QG := by
    rw [← hQEAmbient]
    rintro _ ⟨b, hb, rfl⟩
    exact heB b hb
  have hB'E : B' ≤ E := hB'Q.trans hQGE
  have hB' : IsElementaryAbelianOfRank q 2 B' :=
    hB.map_of_injective (MulAut.conj (e : G)).toMonoidHom
      (MulAut.conj (e : G)).injective
  have hQGp : IsPGroup q QG := Q.isPGroup'.map E₂.subtype
  obtain ⟨T, hQGT⟩ := hQGp.exists_le_sylow
  have hTcomm : IsMulCommutative (T : Subgroup G) := by
    by_contra hTnoncomm
    have hnon := nonabelian_tau2 hM hEM hHall hqTau hB'E hB'
      T.isPGroup' hTnoncomm
    have hpq : p = q := by
      exact Set.mem_singleton_iff.mp (hnon.tau2_eq ▸ hpTau)
    subst q
    exact hTnoncomm
      (isMulCommutative_of_mulEquiv hScomm (Sylow.equiv S T))
  have hB'T : B' ≤ (T : Subgroup G) := hB'Q.trans hQGT
  have hfit := abelian_tau2_sub_Fitting T hM hEM hHall hqTau
    hB'E hB' hB'T hTcomm
  have hTF : (T : Subgroup G) ≤ fittingWithin E :=
    hfit.sylow_le_normalizer_commutator.trans
      hfit.normalizer_commutator_le_fitting
  have hTE : (T : Subgroup G) ≤ E :=
    hTF.trans (fittingWithin_le E)
  let TE : Sylow q E := T.subtype hTE
  have hQEleTE : (QE : Subgroup E) ≤ (TE : Subgroup E) := by
    intro x hx
    have hxG : (x : G) ∈ QG := by
      rw [← hQEAmbient]
      exact Subgroup.mem_map_of_mem E.subtype hx
    exact hQGT hxG
  have hQETEEq : (QE : Subgroup E) = (TE : Subgroup E) :=
    (QE.3 TE.isPGroup' hQEleTE).symm
  have hTEAmbient :
      (TE : Subgroup E).map E.subtype = (T : Subgroup G) := by
    change ((T : Subgroup G).subgroupOf E).map E.subtype =
      (T : Subgroup G)
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hTE hx⟩, hx, rfl⟩
  have hTQG : (T : Subgroup G) = QG := by
    calc
      (T : Subgroup G) = (TE : Subgroup E).map E.subtype :=
        hTEAmbient.symm
      _ = (QE : Subgroup E).map E.subtype :=
        congrArg (fun U : Subgroup E => U.map E.subtype) hQETEEq.symm
      _ = QG := hQEAmbient
  letI : Group.IsNilpotent (fittingWithin E) :=
    fittingWithin_isNilpotent E
  have hTZ : (T : Subgroup G) ≤ centerWithin (fittingWithin E) :=
    ambient_sylow_le_centerWithin_of_isNilpotent T hTF hTcomm
  exact ⟨T, hTQG, hTQG.ge.trans hTZ⟩

/-! ## Nilpotent Hall and normalizer adapters -/

/-- A Hall subgroup of a finite nilpotent group is contained in the
corresponding prime-set core. -/
private theorem hall_le_piCore_of_isNilpotent_12_8
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    {pi : Set ℕ} {H : Subgroup K} (hH : IsHall pi H) :
    H ≤ piCore pi K := by
  calc
    H = (sylowSup H).map H.subtype := by
      rw [sylowSup_eq_top]
      exact H.range_subtype.symm.trans
        (MonoidHom.range_eq_map H.subtype)
    _ = ⨆ r : {r : ℕ // r.Prime},
        ((Classical.choice
          (Sylow.nonempty (p := (r : ℕ)) (G := H)) : Sylow r H) :
          Subgroup H).map H.subtype := by
      rw [sylowSup, Subgroup.map_iSup]
    _ ≤ piCore pi K := by
      apply iSup_le
      intro r
      letI : Fact (r : ℕ).Prime := ⟨r.property⟩
      let R : Sylow (r : ℕ) H := Classical.choice Sylow.nonempty
      by_cases hRbot : (R : Subgroup H) = ⊥
      · simp [R, hRbot]
      have hrR : (r : ℕ) ∣ Nat.card R :=
        R.isPGroup'.card_eq_or_dvd.resolve_left
          (fun hcard => hRbot (Subgroup.card_eq_one.mp hcard))
      have hrPi : (r : ℕ) ∈ pi :=
        hH.isPiNumber_card r.property
          (hrR.trans (R : Subgroup H).card_subgroup_dvd_card)
      have hmapR : IsPGroup (r : ℕ)
          ((R : Subgroup H).map H.subtype) := R.isPGroup'.map H.subtype
      exact (hmapR.le_pCore_of_isNilpotent).trans
        (le_piCore (by infer_instance)
          (pCore_isPGroup.isPiNumber_natCard hrPi))

/-- Hall subgroups are unique in a finite nilpotent group. -/
private theorem hall_eq_piCore_of_isNilpotent_12_8
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    {pi : Set ℕ} {H : Subgroup K} (hH : IsHall pi H) :
    H = piCore pi K := by
  have hle : H ≤ piCore pi K :=
    hall_le_piCore_of_isNilpotent_12_8 hH
  have hrelPi : IsPiNumber pi (H.relIndex (piCore pi K)) :=
    (piCore_isPiNumber pi).of_dvd
      (Subgroup.relIndex_dvd_card H (piCore pi K))
  have hrelCompl : IsPiNumber piᶜ (H.relIndex (piCore pi K)) :=
    hH.isPiNumber_index.of_dvd
      (Subgroup.relIndex_dvd_index_of_le hle)
  have hcop : (H.relIndex (piCore pi K)).Coprime
      (H.relIndex (piCore pi K)) := hrelPi.coprime_compl hrelCompl
  have hone : H.relIndex (piCore pi K) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hone)

/-- An ambient `pi`-subgroup lies in a normal ambiently represented
`pi`-Hall subgroup. -/
private theorem isPiNumber_le_normal_isHall_ambient_12_8
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {C H L : Subgroup G}
    (hHnormal : (H.subgroupOf C).Normal)
    (hHHall : IsHall pi (H.subgroupOf C))
    (hLC : L ≤ C) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ H := by
  let HC : Subgroup C := H.subgroupOf C
  letI : HC.Normal := by simpa [HC] using hHnormal
  have hcop : (Nat.card L).Coprime HC.index := by
    apply Nat.coprime_of_dvd
    intro r hr hrL hrIndex
    exact hHHall.isPiNumber_index hr hrIndex (hLpi hr hrL)
  intro x hx
  let xC : C := ⟨x, hLC hx⟩
  let quotientC : C →* C ⧸ HC := QuotientGroup.mk' HC
  have horderL : orderOf (quotientC xC) ∣ Nat.card L :=
    (orderOf_map_dvd quotientC xC).trans (by
      simpa [xC] using L.orderOf_dvd_natCard hx)
  have horderIndex : orderOf (quotientC xC) ∣ HC.index := by
    simpa only [HC.index_eq_card] using
      orderOf_dvd_natCard (quotientC xC)
  have horderOne : orderOf (quotientC xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  have hquotientOne : quotientC xC = 1 :=
    orderOf_eq_one_iff.mp horderOne
  have hxHC : xC ∈ HC :=
    (QuotientGroup.eq_one_iff xC).mp
      (by simpa [quotientC] using hquotientOne)
  exact hxHC

/-- The join of two commuting abelian subgroups is abelian. -/
private theorem isMulCommutative_sup_of_commute_12_8
    {G : Type u} [Group G] {H K : Subgroup G}
    (hH : IsMulCommutative H) (hK : IsMulCommutative K)
    (hHK : ∀ h ∈ H, ∀ k ∈ K, Commute h k) :
    IsMulCommutative (H ⊔ K : Subgroup G) := by
  letI : IsMulCommutative H := hH
  letI : IsMulCommutative K := hK
  apply isMulCommutative_iff.mpr
  intro x y
  have hnorm : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    apply Subgroup.centralizer_le_normalizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hHK h hh k hk).eq.symm
  have hxprod : (x : G) ∈ (H : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H K hnorm]
    exact x.2
  have hyprod : (y : G) ∈ (H : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H K hnorm]
    exact y.2
  rcases hxprod with ⟨h₁, hh₁, k₁, hk₁, hx⟩
  rcases hyprod with ⟨h₂, hh₂, k₂, hk₂, hy⟩
  apply Subtype.ext
  change (x : G) * y = (y : G) * x
  rw [← hx, ← hy]
  have hh : Commute h₁ h₂ :=
    congrArg Subtype.val
      (mul_comm (⟨h₁, hh₁⟩ : H) ⟨h₂, hh₂⟩)
  have hkk : Commute k₁ k₂ :=
    congrArg Subtype.val
      (mul_comm (⟨k₁, hk₁⟩ : K) ⟨k₂, hk₂⟩)
  have hh₁k₂ := hHK h₁ hh₁ k₂ hk₂
  have hh₂k₁ := hHK h₂ hh₂ k₁ hk₁
  calc
    (h₁ * k₁) * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
    _ = h₁ * (h₂ * k₁) * k₂ := by rw [hh₂k₁.eq.symm]
    _ = (h₂ * k₂) * (h₁ * k₁) := by
      calc
        h₁ * (h₂ * k₁) * k₂ = (h₁ * h₂) * (k₁ * k₂) := by group
        _ = (h₂ * h₁) * (k₁ * k₂) := by rw [hh.eq]
        _ = (h₂ * h₁) * (k₂ * k₁) := by rw [hkk.eq]
        _ = h₂ * (h₁ * k₂) * k₁ := by group
        _ = h₂ * (k₂ * h₁) * k₁ := by rw [hh₁k₂.eq]
        _ = (h₂ * k₂) * (h₁ * k₁) := by group

/-- An abelian Hall subgroup of a finite nilpotent ambient subgroup is
central in that subgroup. -/
private theorem abelian_hall_le_centerWithin_of_isNilpotent
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {H K : Subgroup G} [Group.IsNilpotent K]
    (hHK : H ≤ K) (hHall : IsHall pi (H.subgroupOf K))
    (hHcomm : IsMulCommutative H) : H ≤ centerWithin K := by
  let HK : Subgroup K := H.subgroupOf K
  have hHKcomm : IsMulCommutative HK := by
    exact isMulCommutative_of_mulEquiv hHcomm
      (Subgroup.subgroupOfEquivOfLe hHK).symm
  have hcore : HK = piCore pi K :=
    hall_eq_piCore_of_isNilpotent_12_8 hHall
  have hHKnormal : HK.Normal := by
    rw [hcore]
    infer_instance
  have htopCent : (⊤ : Subgroup K) ≤
      Subgroup.centralizer (HK : Set K) := by
    rw [← sylowSup_eq_top]
    dsimp [sylowSup]
    apply iSup_le
    intro r
    letI : Fact (r : ℕ).Prime := ⟨r.property⟩
    let R : Sylow (r : ℕ) K := Classical.choice Sylow.nonempty
    by_cases hrPi : (r : ℕ) ∈ pi
    · have hRHK : (R : Subgroup K) ≤ HK := by
        rw [hcore]
        exact le_piCore (by infer_instance)
          (R.isPGroup'.isPiNumber_natCard hrPi)
      exact hRHK.trans
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr hHKcomm)
    · have hRcompl : IsPiNumber piᶜ (Nat.card R) :=
        R.isPGroup'.isPiNumber_natCard hrPi
      have hdis : Disjoint (R : Subgroup K) HK :=
        Subgroup.disjoint_of_coprime_natCard
          ((hHall.isPiNumber_card.coprime_compl hRcompl).symm)
      have hcomm := Subgroup.commute_of_normal_of_disjoint
        (R : Subgroup K) HK (by infer_instance) hHKnormal hdis
      intro r₀ hr₀
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hcomm r₀ h hr₀ hh).eq.symm
  intro h hh
  refine mem_centerWithin.mpr ⟨hHK hh, ?_⟩
  intro k hk
  let hK : K := ⟨h, hHK hh⟩
  let kK : K := ⟨k, hk⟩
  have hkCent : kK ∈ Subgroup.centralizer (HK : Set K) :=
    htopCent (by simp)
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp hkCent hK hh).symm

/-- If the derived subgroup of a normalizer centralizes the normalized
subgroup, then it normalizes every mixed commutator with a subgroup of the
normalizer. -/
private theorem normalizer_le_normalizer_commutator_of_derived_central
    {G : Type u} [Group G] {K X N : Subgroup G}
    (hNnormK : N ≤ Subgroup.normalizer (K : Set G))
    (hXN : X ≤ N)
    (hder : ⁅N, N⁆ ≤ Subgroup.centralizer (K : Set G)) :
    N ≤ Subgroup.normalizer (((⁅K, X⁆ : Subgroup G) : Set G)) := by
  rw [Subgroup.commutator_def]
  apply Subgroup.le_normalizer_closure_iff.mpr
  rintro n hn _ ⟨k, hk, x, hx, rfl⟩
  have hxN : x ∈ N := hXN hx
  have hXnormK : X ≤ Subgroup.normalizer (K : Set G) :=
    hXN.trans hNnormK
  let k' : G := n * k * n⁻¹
  let c : G := ⁅n, x⁆
  have hk' : k' ∈ K :=
    Subgroup.le_normalizer_iff.mp hNnormK n hn k hk
  have hc : c ∈ Subgroup.centralizer (K : Set G) :=
    hder (Subgroup.commutator_mem_commutator hn hxN)
  have hcommKX : ⁅k', x⁆ ∈ ⁅K, X⁆ :=
    Subgroup.commutator_mem_commutator hk' hx
  have hcommKXK : ⁅k', x⁆ ∈ K :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hXnormK) hcommKX
  have hkc : Commute k' c :=
    Subgroup.mem_centralizer_iff.mp hc k' hk'
  have hcd : Commute c ⁅k', x⁆ :=
    (Subgroup.mem_centralizer_iff.mp hc ⁅k', x⁆ hcommKXK).symm
  have hconjx : n * x * n⁻¹ = c * x := by
    simpa [c] using
      (conj_eq_commutatorElement_mul (g₁ := n) (g₂ := x))
  have hconjugate : n * ⁅k, x⁆ * n⁻¹ = ⁅k', x⁆ := by
    calc
      n * ⁅k, x⁆ * n⁻¹ = ⁅k', n * x * n⁻¹⁆ := by
        simpa [k'] using
          (conjugate_commutatorElement (g₁ := k) (g₂ := x) (g₃ := n))
      _ = ⁅k', c * x⁆ := by rw [hconjx]
      _ = ⁅k', c⁆ * c * ⁅k', x⁆ * c⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj k' c x
      _ = ⁅k', x⁆ := by
        rw [hkc.commutator_eq, one_mul, hcd.eq]
        simp
  rw [hconjugate]
  exact hcommKX

/-- Fixed points in `K` under a subgroup of a normalizer are normal when
the normalizer has abelian conjugation image on `K`. -/
private theorem centralizerWithin_normal_of_derived_central
    {G : Type u} [Group G]
    {K X N : Subgroup G} (hKN : K ≤ N)
    (hNnormK : N ≤ Subgroup.normalizer (K : Set G))
    (hXN : X ≤ N)
    (hder : ⁅N, N⁆ ≤ Subgroup.centralizer (K : Set G)) :
    ((centralizerWithin K X).subgroupOf N).Normal := by
  have hCN : centralizerWithin K X ≤ N :=
    (centralizerWithin_le_left K X).trans hKN
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCN]
  rw [Subgroup.le_normalizer_iff]
  intro n hn s hs
  have hnsK : n * s * n⁻¹ ∈ K :=
    Subgroup.le_normalizer_iff.mp hNnormK n hn s hs.1
  refine ⟨hnsK, ?_⟩
  intro x hx
  let nN : Subgroup.normalizer (K : Set G) := ⟨n, hNnormK hn⟩
  let xN : Subgroup.normalizer (K : Set G) :=
    ⟨x, hNnormK (hXN hx)⟩
  let sK : K := ⟨s, hs.1⟩
  let rho := K.normalizerMonoidHom
  have hcommAut : Commute (rho xN) (rho nN) := by
    rw [← commutatorElement_eq_one_iff_commute,
      ← map_commutatorElement]
    apply MonoidHom.mem_ker.mp
    rw [Subgroup.normalizerMonoidHom_ker]
    exact hder (Subgroup.commutator_mem_commutator
      (hXN hx) hn)
  have hfix : rho xN sK = sK := by
    apply Subtype.ext
    change x * s * x⁻¹ = s
    exact mul_inv_eq_iff_eq_mul.mpr (hs.2 x hx)
  have hfixedConj : rho xN (rho nN sK) = rho nN sK := by
    calc
      rho xN (rho nN sK) = (rho xN * rho nN) sK := rfl
      _ = (rho nN * rho xN) sK := by rw [hcommAut.eq]
      _ = rho nN (rho xN sK) := rfl
      _ = rho nN sK := by rw [hfix]
  have hfixedConjVal := congrArg Subtype.val hfixedConj
  change x * (n * s * n⁻¹) * x⁻¹ = n * s * n⁻¹ at hfixedConjVal
  exact mul_inv_eq_iff_eq_mul.mp hfixedConjVal

/-! ## Rank-one and coprime-action adapters -/

/-- Distinct lines in an elementary-abelian plane are complementary. -/
private theorem rankTwo_distinct_lines_12_8
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A X Z : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hX : RankOneLineIn p A X) (hZ : RankOneLineIn p A Z)
    (hne : X ≠ Z) :
    Disjoint X Z ∧ X ⊔ Z = A := by
  have hdis : Disjoint X Z := by
    rw [disjoint_iff]
    by_contra hneBot
    have hdiv : Nat.card (X ⊓ Z : Subgroup G) ∣ p := by
      have hdivX : Nat.card (X ⊓ Z : Subgroup G) ∣ Nat.card X :=
        Subgroup.card_dvd_of_le inf_le_left
      simpa only [hX.2.card_eq, pow_one] using hdivX
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv with
      hcardOne | hcardP
    · exact hneBot (Subgroup.eq_bot_of_card_eq (X ⊓ Z) hcardOne)
    · have hInfX : X ⊓ Z = X := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_left
        rw [hcardP, hX.2.card_eq, pow_one]
      have hXZ : X ≤ Z := by
        intro x hx
        have hxInf : x ∈ X ⊓ Z := by rw [hInfX]; exact hx
        exact hxInf.2
      have hcardEq : Nat.card X = Nat.card Z := by
        rw [hX.2.card_eq, hZ.2.card_eq]
      exact hne (Subgroup.eq_of_le_of_card_ge hXZ hcardEq.ge)
  refine ⟨hdis, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge (sup_le hX.1 hZ.1)
  rw [natCard_sup_eq_mul_of_disjoint_of_commute hdis,
    hX.2.card_eq, hZ.2.card_eq, hA.card_eq, pow_one, pow_two]
  intro x hx y hy
  letI : IsMulCommutative A := hA.commutative
  exact congrArg Subtype.val
    (mul_comm (⟨x, hX.1 hx⟩ : A) ⟨y, hZ.1 hy⟩)

/-- A nontrivial cyclic subgroup of an elementary-abelian `p`-group is a
rank-one line. -/
private theorem rankOne_of_nontrivial_cyclic_le_elementary
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A X : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hXA : X ≤ A) (hXcyclic : IsCyclic X) (hXne : X ≠ ⊥) :
    IsElementaryAbelianOfRank p 1 X := by
  letI : IsCyclic X := hXcyclic
  have hXp : IsPGroup p X := hA.isPGroup.to_le hXA
  have hXcardNe : Nat.card X ≠ 1 := by
    intro hcard
    exact hXne (Subgroup.card_eq_one.mp hcard)
  have hOmegaCard : Nat.card (omegaOne p X) = p :=
    card_omegaOne_of_isCyclic_isPGroup Fact.out hXp hXcardNe
  have hOmegaTop : omegaOne p X = ⊤ := by
    apply top_unique
    intro x _
    apply mem_omegaOne_of_pow_eq_one
    have hxG : (x : G) ^ p = 1 :=
      congrArg (fun z : A => (z : G))
        (hA.pow_eq_one ⟨(x : G), hXA x.2⟩)
    apply Subtype.ext
    exact hxG
  have hXcard : Nat.card X = p := by
    rw [hOmegaTop, Subgroup.card_top] at hOmegaCard
    exact hOmegaCard
  exact isElementaryAbelianOfRank_one_of_card_eq_prime hXcard

/-- A nonidentity element of an elementary-abelian plane spans a line. -/
private theorem rankOneLineIn_zpowers_of_mem_12_9
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    {a : G} (ha : a ∈ A) (hane : a ≠ 1) :
    RankOneLineIn p A (Subgroup.zpowers a) := by
  have hapow : a ^ p = 1 :=
    congrArg Subtype.val (hA.pow_eq_one ⟨a, ha⟩)
  have haorder : orderOf a = p :=
    ((Nat.dvd_prime (Fact.out : p.Prime)).mp
      (orderOf_dvd_of_pow_eq_one hapow)).resolve_left
        (by simpa [orderOf_eq_one_iff] using hane)
  have hcard : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers, haorder]
  exact ⟨Subgroup.zpowers_le.mpr ha,
    isElementaryAbelianOfRank_one_of_card_eq_prime hcard⟩

/-- Conjugating a subgroup after regarding it inside an overgroup has the
same ambient carrier as conjugating by the coerced overgroup element. -/
private theorem map_subgroupOf_conj_lift_12_9
    {G : Type u} [Group G] {M X : Subgroup G}
    (hXM : X ≤ M) (m : M) :
    ((X.subgroupOf M).map (MulAut.conj m).toMonoidHom).map M.subtype =
      X.map (MulAut.conj (m : G)).toMonoidHom := by
  calc
    ((X.subgroupOf M).map (MulAut.conj m).toMonoidHom).map M.subtype =
        (X.subgroupOf M).map
          (M.subtype.comp (MulAut.conj m).toMonoidHom) :=
      Subgroup.map_map (X.subgroupOf M) M.subtype
        (MulAut.conj m).toMonoidHom
    _ = (X.subgroupOf M).map
        ((MulAut.conj (m : G)).toMonoidHom.comp M.subtype) := by
      rfl
    _ = ((X.subgroupOf M).map M.subtype).map
        (MulAut.conj (m : G)).toMonoidHom := by
      rw [Subgroup.map_map]
    _ = X.map (MulAut.conj (m : G)).toMonoidHom := by
      rw [Subgroup.map_subgroupOf_eq_of_le hXM]

/-- The fixed-point subgroup inside a coprime abelian commutator is
trivial. -/
private theorem centralizerWithin_commutator_eq_bot_of_coprime_abelian_12_8
    {G : Type u} [Group G] [Finite G] {K P : Subgroup G}
    (hPnormK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card P))
    (hKab : IsMulCommutative K) :
    centralizerWithin ⁅K, P⁆ P = ⊥ := by
  classical
  let T : Subgroup G := ⁅K, P⁆
  have hTK : T ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hPnormK
  have hPnormT : P ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.normalizer_commutator_ge_right K P
  have hTcop : Nat.Coprime (Nat.card T) (Nat.card P) :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hTK)
  letI : IsMulCommutative K := hKab
  letI : IsSolvable K :=
    Submission.OddOrder.MathlibSupport.isSolvable_of_comm
      (fun a b : K => mul_comm a b)
  have hidem : ⁅P, ⁅P, K⁆⁆ = ⁅P, K⁆ :=
    commutator_commutator_eq_of_coprime
      (K := K) (R := P) hPnormK hcop
  have hperfect : ⁅P, T⁆ = T := by
    dsimp [T]
    rw [Subgroup.commutator_comm K P]
    exact hidem
  letI : IsMulCommutative T :=
    isMulCommutative_of_le hKab hTK
  apply le_antisymm _ bot_le
  intro x hx
  let xt : T := ⟨x, hx.1⟩
  have hfix : ∀ a : P,
      (a : G) * (xt : G) * (a : G)⁻¹ = (xt : G) := by
    intro a
    calc
      (a : G) * (xt : G) * (a : G)⁻¹ =
          (xt : G) * (a : G) * (a : G)⁻¹ := by
            rw [hx.2 (a : G) a.2]
      _ = (xt : G) := by simp
  have hxt : xt = 1 :=
    Submission.OddOrder.BG.Section06.fixed_eq_one_of_abelian_perfect_coprime_conjugation
        hPnormT hTcop hperfect xt hfix
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxt)

/-- Full centralizers commute with ambient equivalences. -/
private theorem map_centralizer_equiv_12_8
    {G : Type u} [Group G] (X : Subgroup G) (e : G ≃* G) :
    (Subgroup.centralizer (X : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (X.map e.toMonoidHom : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy z hz
    have hz' : e.symm z ∈ X := Subgroup.mem_map_equiv.mp hz
    have hcomm := hy (e.symm z) hz'
    simpa using congrArg e hcomm
  · intro hy z hz
    have hzMap : e z ∈ X.map e.toMonoidHom :=
      (Subgroup.mem_map_iff_mem e.injective).mpr hz
    have hcomm := hy (e z) hzMap
    simpa using congrArg e.symm hcomm

/-- In an odd finite group with elementary-abelian `q`-rank one, all
rank-one elementary-abelian `q`-subgroups are conjugate. -/
private theorem rankOne_subgroups_conjugate_of_no_rankTwo
    {K : Type u} [Group K] [Finite K]
    {q : ℕ} [Fact q.Prime] {X Y : Subgroup K}
    (hodd : Odd (Nat.card K))
    (hX : IsElementaryAbelianOfRank q 1 X)
    (hY : IsElementaryAbelianOfRank q 1 Y)
    (hNoRankTwo : ¬ ∃ B : Subgroup K,
      IsElementaryAbelianOfRank q 2 B) :
    ∃ k : K,
      X.map (MulAut.conj k).toMonoidHom = Y := by
  classical
  obtain ⟨P, hXP⟩ := hX.isPGroup.exists_le_sylow
  obtain ⟨Q, hYQ⟩ := hY.isPGroup.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P Q
  have hQcyclic : IsCyclic (Q : Subgroup K) := by
    apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
      Q.isPGroup'
      (hodd.of_dvd_nat (Q : Subgroup K).card_subgroup_dvd_card)).mpr
    rintro ⟨B, hB⟩
    let BK : Subgroup K := B.map (Q : Subgroup K).subtype
    exact hNoRankTwo ⟨BK,
      hB.map_of_injective (Q : Subgroup K).subtype
        (Q : Subgroup K).subtype_injective⟩
  letI : IsCyclic (Q : Subgroup K) := hQcyclic
  have hQne : Nat.card (Q : Subgroup K) ≠ 1 := by
    intro hcard
    have hYdivQ : Nat.card Y ∣ Nat.card (Q : Subgroup K) :=
      Subgroup.card_dvd_of_le hYQ
    have hqQ : q ∣ Nat.card (Q : Subgroup K) := by
      simpa only [hY.card_eq, pow_one] using hYdivQ
    apply (Fact.out : q.Prime).not_dvd_one
    simpa only [hcard] using hqQ
  let O : Subgroup K :=
    (omegaOne q (Q : Subgroup K)).map (Q : Subgroup K).subtype
  have hOcard : Nat.card O = q := by
    dsimp [O]
    rw [Subgroup.card_map_of_injective
      (Q : Subgroup K).subtype_injective]
    exact card_omegaOne_of_isCyclic_isPGroup Fact.out
      Q.isPGroup' hQne
  have hPmap : (P : Subgroup K).map
      (MulAut.conj k).toMonoidHom = (Q : Subgroup K) := by
    change MulAut.conj k • (P : Subgroup K) = (Q : Subgroup K)
    rw [← Sylow.coe_subgroup_smul, hk]
  let Xk : Subgroup K := X.map (MulAut.conj k).toMonoidHom
  have hXk : IsElementaryAbelianOfRank q 1 Xk :=
    hX.map_of_injective (MulAut.conj k).toMonoidHom
      (MulAut.conj k).injective
  have hXkQ : Xk ≤ (Q : Subgroup K) :=
    (Subgroup.map_mono hXP).trans_eq hPmap
  have line_eq_O : ∀ {L : Subgroup K},
      IsElementaryAbelianOfRank q 1 L →
      L ≤ (Q : Subgroup K) → L = O := by
    intro L hL hLQ
    have hLO : L ≤ O := by
      intro x hx
      let xQ : Q := ⟨x, hLQ hx⟩
      refine ⟨xQ, mem_omegaOne_of_pow_eq_one q ?_, rfl⟩
      have hxK : (x : K) ^ q = 1 :=
        congrArg (fun z : L => (z : K))
          (hL.pow_eq_one ⟨x, hx⟩)
      apply Subtype.ext
      exact hxK
    apply Subgroup.eq_of_le_of_card_ge hLO
    rw [hOcard, hL.card_eq, pow_one]
  have hXkO : Xk = O := line_eq_O hXk hXkQ
  have hYO : Y = O := line_eq_O hY hYQ
  exact ⟨k, hXkO.trans hYO.symm⟩

/-! ## The abelian `tau2` case -/

/-- `BGsection12.v: abelian_tau2`, Theorem 12.8(a), (b), (d), and (e). -/
theorem abelian_tau2
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₁ E₂ E₃ A : Subgroup G} {p : ℕ}
    (S : Sylow p G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    AbelianTau2Conclusion M E E₁ E₂ E₃ A (S : Subgroup G) := by
  classical
  letI : Fact p.Prime := ⟨hpTau.1⟩
  let F : Subgroup G := fittingWithin E
  let K : Subgroup G := E₃ ⊔ E₂
  have hEM : E ≤ M := hCompl.E_le_M
  have hE₁E : E₁ ≤ E := hCompl.E₁_le_E
  have hE₂E : E₂ ≤ E := hCompl.E₂_le_E
  have hE₃E : E₃ ≤ E := hCompl.E₃_le_E
  have hSigma := sigma_compl_context hM hCompl
  letI : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance

  have hE₂pi : IsPiNumber (tau2Primes M) (Nat.card E₂) := by
    rw [← natCard_subgroupOf_eq hE₂E]
    exact hCompl.hall_E₂.isPiNumber_card
  have hE₂HallG : IsHall (tau2Primes M) E₂ := by
    refine ⟨hE₂pi, ?_⟩
    intro q hq hqIndex
    intro hqTau
    letI : Fact q.Prime := ⟨hq⟩
    let Q : Sylow q E₂ := Classical.choice Sylow.nonempty
    obtain ⟨T, hTQ, _hQZ⟩ :=
      tau2_sylow_central_of_abelian_tau2 S hM hEM
        hCompl.hall_E hE₂E hCompl.hall_E₂ hpTau hqTau hScomm Q
    have hTE₂ : (T : Subgroup G) ≤ E₂ := by
      rw [hTQ]
      exact Subgroup.map_subtype_le _
    exact T.not_dvd_index
      (hqIndex.trans (Subgroup.index_dvd_of_le hTE₂))

  have hE₂ZF : E₂ ≤ centerWithin F := by
    calc
      E₂ = (sylowSup E₂).map E₂.subtype := by
        rw [sylowSup_eq_top]
        exact E₂.range_subtype.symm.trans
          (MonoidHom.range_eq_map E₂.subtype)
      _ = ⨆ q : {q : ℕ // q.Prime},
          ((Classical.choice
            (Sylow.nonempty (p := (q : ℕ)) (G := E₂)) : Sylow q E₂) :
            Subgroup E₂).map E₂.subtype := by
        rw [sylowSup, Subgroup.map_iSup]
      _ ≤ centerWithin F := by
        apply iSup_le
        intro q
        letI : Fact (q : ℕ).Prime := ⟨q.property⟩
        let Q : Sylow (q : ℕ) E₂ := Classical.choice Sylow.nonempty
        by_cases hQbot : (Q : Subgroup E₂) = ⊥
        · simp [Q, hQbot]
        have hqQ : (q : ℕ) ∣ Nat.card Q :=
          Q.isPGroup'.card_eq_or_dvd.resolve_left
            (fun hcard => hQbot (Subgroup.card_eq_one.mp hcard))
        have hqE₂ : (q : ℕ) ∣ Nat.card E₂ :=
          hqQ.trans (Q : Subgroup E₂).card_subgroup_dvd_card
        have hqTau : (q : ℕ) ∈ tau2Primes M :=
          hE₂pi q.property hqE₂
        obtain ⟨T, hTQ, hQZ⟩ :=
          tau2_sylow_central_of_abelian_tau2 S hM hEM
            hCompl.hall_E hE₂E hCompl.hall_E₂ hpTau hqTau
              hScomm Q
        simpa only [hTQ] using hQZ
  have hE₂F : E₂ ≤ F :=
    hE₂ZF.trans (centralizerWithin_le_left F F)
  have hE₂comm : IsMulCommutative E₂ := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    exact ((mem_centerWithin.mp (hE₂ZF x.2)).2 y (hE₂F y.2)).symm
  letI : IsMulCommutative E₂ := hE₂comm
  have hHallE₂F : IsHall (tau2Primes M) (E₂.subgroupOf F) :=
    isHall_subgroupOf_of_le hE₂F (fittingWithin_le E)
      hCompl.hall_E₂
  have hE₂charF : (E₂.subgroupOf F).Characteristic := by
    rw [hall_eq_piCore_of_isNilpotent_12_8 hHallE₂F]
    infer_instance
  letI : (E₂.subgroupOf F).Characteristic := hE₂charF
  have hNFNE₂ : Subgroup.normalizer (F : Set G) ≤
      Subgroup.normalizer (E₂ : Set G) := by
    simpa only [Subgroup.map_subgroupOf_eq_of_le hE₂F] using
      characteristic_map_subtype_le_normalizer F (E₂.subgroupOf F)
  have hENE₂ : E ≤ Subgroup.normalizer (E₂ : Set G) :=
    (fittingWithin_le_normalizer E).trans hNFNE₂
  have hE₂normal : (E₂.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE₂E).mpr hENE₂

  let E₃E : Subgroup E := E₃.subgroupOf E
  let E₂E : Subgroup E := E₂.subgroupOf E
  letI : E₃E.Normal := by simpa [E₃E] using hSigma.E₃_normal
  letI : E₂E.Normal := by simpa [E₂E] using hE₂normal
  have hE₃tau1Compl : IsPiNumber (tau1Primes M)ᶜ (Nat.card E₃E) := by
    apply hCompl.hall_E₃.isPiNumber_card.mono
    intro q hqTau3 hqTau1
    exact (tau3'1 M hqTau1) hqTau3
  have hE₂tau1Compl : IsPiNumber (tau1Primes M)ᶜ (Nat.card E₂E) := by
    apply hCompl.hall_E₂.isPiNumber_card.mono
    intro q hqTau2 hqTau1
    exact (tau2'1 M hqTau1) hqTau2
  have hdisE₃E₂ : Disjoint E₃E E₂E := by
    apply Subgroup.disjoint_of_coprime_natCard
    exact (hCompl.hall_E₃.isPiNumber_card.coprime_compl
      (hCompl.hall_E₂.isPiNumber_card.mono (tau3'2 M)))
  have hcommE₃E₂ := Subgroup.commute_of_normal_of_disjoint
    E₃E E₂E (by infer_instance) (by infer_instance) hdisE₃E₂
  have hcommE₃E₂G : ∀ x ∈ E₃, ∀ y ∈ E₂, Commute x y := by
    intro x hx y hy
    let xE : E := ⟨x, hE₃E hx⟩
    let yE : E := ⟨y, hE₂E hy⟩
    exact congrArg Subtype.val (hcommE₃E₂ xE yE hx hy).eq
  have hE₃comm : IsMulCommutative E₃ := by
    letI : IsCyclic E₃ := hSigma.E₃_cyclic
    infer_instance
  have hKcomm : IsMulCommutative K := by
    dsimp [K]
    exact isMulCommutative_sup_of_commute_12_8
      hE₃comm hE₂comm hcommE₃E₂G
  have hKE : K ≤ E := sup_le hE₃E hE₂E
  have hKnormal : (K.subgroupOf E).Normal := by
    dsimp [K]
    rw [Subgroup.subgroupOf_sup hE₃E hE₂E]
    infer_instance
  letI : IsMulCommutative K := hKcomm
  letI : Group.IsNilpotent K := by infer_instance
  have hKtau1Compl : IsPiNumber (tau1Primes M)ᶜ (Nat.card K) := by
    have hrel := isPiNumber_card_sup_of_normal_left
      (K := E) (A := E₃E) (B := E₂E)
      (by infer_instance) hE₃tau1Compl hE₂tau1Compl
    rw [← Subgroup.subgroupOf_sup hE₃E hE₂E,
      natCard_subgroupOf_eq hKE] at hrel
    exact hrel
  have hE₁tau1 : IsPiNumber (tau1Primes M) (Nat.card E₁) := by
    rw [← natCard_subgroupOf_eq hE₁E]
    exact hCompl.hall_E₁.isPiNumber_card
  have hcopKE₁ : (Nat.card K).Coprime (Nat.card E₁) :=
    (hE₁tau1.coprime_compl hKtau1Compl).symm
  have hHallKE : IsHall (primeSupport (Nat.card K)) (K.subgroupOf E) := by
    rw [← natCard_subgroupOf_eq hKE]
    apply isHall_primeSupport
    rw [hSigma.E₃₂_E₁_sdprod.2.2.2.symm.index_eq_card,
      natCard_subgroupOf_eq hKE, natCard_subgroupOf_eq hE₁E]
    exact hcopKE₁
  have hKF : K ≤ F :=
    nilpotent_normal_le_fittingWithin hKE hKnormal (by infer_instance)
  have hHallKF : IsHall (primeSupport (Nat.card K)) (K.subgroupOf F) :=
    isHall_subgroupOf_of_le hKF (fittingWithin_le E) hHallKE
  have hKZF : K ≤ centerWithin F :=
    abelian_hall_le_centerWithin_of_isNilpotent hKF hHallKF hKcomm
  have hKcharF : (K.subgroupOf F).Characteristic := by
    rw [hall_eq_piCore_of_isNilpotent_12_8 hHallKF]
    infer_instance
  letI : (K.subgroupOf F).Characteristic := hKcharF
  have hNFNK : Subgroup.normalizer (F : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
    simpa only [Subgroup.map_subgroupOf_eq_of_le hKF] using
      characteristic_map_subtype_le_normalizer F (K.subgroupOf F)

  have hE₂K : E₂ ≤ K := le_sup_right
  have hHallE₂K : IsHall (tau2Primes M) (E₂.subgroupOf K) :=
    isHall_subgroupOf_of_le hE₂K hKE hCompl.hall_E₂
  have hE₂charK : (E₂.subgroupOf K).Characteristic := by
    rw [hall_eq_piCore_of_isNilpotent_12_8 hHallE₂K]
    infer_instance
  letI : (E₂.subgroupOf K).Characteristic := hE₂charK
  have hNKNE₂ : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (E₂ : Set G) := by
    simpa only [Subgroup.map_subgroupOf_eq_of_le hE₂K] using
      characteristic_map_subtype_le_normalizer K (E₂.subgroupOf K)

  have hfit := abelian_tau2_sub_Fitting S hM hEM hCompl.hall_E
    hpTau hAE hA hAS hScomm
  have hSE : (S : Subgroup G) ≤ E :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hScomm).trans
      hfit.centralizer_le_complement
  have hSpi : IsPiNumber (tau2Primes M) (Nat.card S) :=
    S.isPGroup'.isPiNumber_natCard hpTau
  have hSE₂ : (S : Subgroup G) ≤ E₂ :=
    isPiNumber_le_normal_isHall_ambient_12_8 hE₂normal
      hCompl.hall_E₂ hSE hSpi
  let SE₂ : Sylow p E₂ := S.subtype hSE₂
  have hScore : (S : Subgroup G).subgroupOf E₂ = pCore p E₂ := by
    simpa only [SE₂, Sylow.coe_subtype] using
      (pCore_eq_sylow_of_isNilpotent SE₂).symm
  have hScharE₂ : ((S : Subgroup G).subgroupOf E₂).Characteristic := by
    rw [hScore]
    infer_instance
  letI : ((S : Subgroup G).subgroupOf E₂).Characteristic := hScharE₂
  have hNE₂NS : Subgroup.normalizer (E₂ : Set G) ≤
      Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    simpa only [Subgroup.map_subgroupOf_eq_of_le hSE₂] using
      characteristic_map_subtype_le_normalizer E₂
        ((S : Subgroup G).subgroupOf E₂)

  have hAM : A ≤ M := hAE.trans hEM
  have hTau := tau2_context hM hpTau hAM hA
  let SM : Sylow p M := S.subtype (hSE.trans hEM)
  have hAmbientSM : ambientSylow M SM = (S : Subgroup G) := by
    change ((S : Subgroup G).subgroupOf M).map M.subtype =
      (S : Subgroup G)
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hSE.trans hEM hx⟩, hx, rfl⟩
  have hOmegaA :
      (omegaOne p (S : Subgroup G)).map (S : Subgroup G).subtype = A := by
    calc
      (omegaOne p (S : Subgroup G)).map (S : Subgroup G).subtype =
          (omegaOne p (ambientSylow M SM)).map
            (ambientSylow M SM).subtype :=
        congrArg
          (fun P : Subgroup G => (omegaOne p P).map P.subtype)
          hAmbientSM.symm
      _ = A := hTau.omegaOne_eq SM (hAS.trans hAmbientSM.ge)
  have hAcharS : (A.subgroupOf (S : Subgroup G)).Characteristic := by
    have hsubgroup : A.subgroupOf (S : Subgroup G) =
        omegaOne p (S : Subgroup G) := by
      change A.comap (S : Subgroup G).subtype = omegaOne p (S : Subgroup G)
      rw [← hOmegaA]
      exact Subgroup.comap_map_eq_self_of_injective
        (S : Subgroup G).subtype_injective _
    rw [hsubgroup]
    infer_instance
  letI : (A.subgroupOf (S : Subgroup G)).Characteristic := hAcharS
  have hNSNA : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
      Subgroup.normalizer (A : Set G) := by
    simpa only [Subgroup.map_subgroupOf_eq_of_le hAS] using
      characteristic_map_subtype_le_normalizer (S : Subgroup G)
        (A.subgroupOf (S : Subgroup G))
  have hNANF : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (F : Set G) := by
    dsimp only [F]
    rw [← hfit.fitting_normalizer_eq]
    exact fittingWithin_le_normalizer (Subgroup.normalizer (A : Set G))

  have hNAeqNS : Subgroup.normalizer (A : Set G) =
      Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    apply le_antisymm
    · exact hNANF.trans (hNFNK.trans
        (hNKNE₂.trans hNE₂NS))
    · exact hNSNA
  have hNSeqNE₂ : Subgroup.normalizer ((S : Subgroup G) : Set G) =
      Subgroup.normalizer (E₂ : Set G) := by
    apply le_antisymm
    · exact hNSNA.trans (hNANF.trans (hNFNK.trans hNKNE₂))
    · exact hNE₂NS
  have hNE₂eqNK : Subgroup.normalizer (E₂ : Set G) =
      Subgroup.normalizer (K : Set G) := by
    apply le_antisymm
    · exact hNE₂NS.trans
        (hNSNA.trans (hNANF.trans hNFNK))
    · exact hNKNE₂
  have hNKeqNF : Subgroup.normalizer (K : Set G) =
      Subgroup.normalizer (F : Set G) := by
    apply le_antisymm
    · exact hNKNE₂.trans (hNE₂NS.trans
        (hNSNA.trans hNANF))
    · exact hNFNK

  refine
    { E₂_normal := hE₂normal
      E₂_abelian := hE₂comm
      E₂_hall := hE₂HallG
      normalizer_A_eq_S := hNAeqNS
      normalizer_S_eq_E₂ := hNSeqNE₂
      normalizer_E₂_eq_E₃_join_E₂ := by simpa only [K] using hNE₂eqNK
      normalizer_E₃_join_E₂_eq_fitting := by simpa only [K, F] using hNKeqNF
      regular_rank_one_central := ?_ }
  intro q _ X hX hregX
  have hqX : q ∣ Nat.card X := by
    rw [hX.2.card_eq, pow_one]
  have hqE₁ : q ∣ Nat.card E₁ :=
    hqX.trans (Subgroup.card_dvd_of_le hX.1)
  have hqTau1 : q ∈ tau1Primes M := by
    have hcard := hCompl.hall_E₁.isPiNumber_card
    rw [natCard_subgroupOf_eq hE₁E] at hcard
    exact hcard Fact.out hqE₁
  have hXE : X ≤ E := hX.1.trans hE₁E
  have hXnormK : X ≤ Subgroup.normalizer (K : Set G) := by
    exact hXE.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKE).mp hKnormal)
  have hFcentK : F ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.le_centralizer_iff.mp (hKZF.trans inf_le_right)
  have hNKderCentK : ⁅Subgroup.normalizer (K : Set G),
      Subgroup.normalizer (K : Set G)⁆ ≤
      Subgroup.centralizer (K : Set G) := by
    rw [← hNE₂eqNK, ← hNSeqNE₂]
    exact hfit.normalizer_commutator_le_fitting.trans hFcentK
  let H : Subgroup G := ⁅K, X⁆
  have hNKNH : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (H : Set G) := by
    dsimp [H]
    exact normalizer_le_normalizer_commutator_of_derived_central
      le_rfl hXnormK hNKderCentK
  have hNSnotM : ¬ Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M := by
    have hnot := hTau.normalizer_sylow_not_le SM
      (hAS.trans hAmbientSM.ge)
    change ¬ Subgroup.normalizer (ambientSylow M SM : Set G) ≤ M at hnot
    rw [hAmbientSM] at hnot
    exact hnot
  have hNHnotM : ¬ Subgroup.normalizer (H : Set G) ≤ M := by
    intro hNHM
    apply hNSnotM
    rw [hNSeqNE₂, hNE₂eqNK]
    exact hNKNH.trans hNHM
  have hKM : K ≤ M := hKE.trans hEM
  have hKsigmaCompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K) := by
    have hEcompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card E) := by
      rw [← natCard_subgroupOf_eq hEM]
      exact hCompl.hall_E.isPiNumber_card
    exact hEcompl.of_dvd (Subgroup.card_dvd_of_le hKE)
  have hKqCompl : IsPiNumber ({q} : Set ℕ)ᶜ (Nat.card K) := by
    apply hKtau1Compl.mono
    intro r hr hrq
    exact hr (Set.mem_singleton_iff.mp hrq ▸ hqTau1)
  have hXMN : X ≤ M ⊓ Subgroup.normalizer (K : Set G) :=
    le_inf (hXE.trans hEM) hXnormK
  have hKcentX : K ≤ Subgroup.centralizer (X : Set G) := by
    by_contra hKnotCentX
    have hHne : H ≠ ⊥ := by
      intro hHbot
      apply hKnotCentX
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by simpa only [H] using hHbot)
    have hcommConclusion := commG_sigma'_1Elem_cyclic hM hKM
      hKsigmaCompl hqTau1.2.1 hX.2 hXMN hregX hKqCompl hKcomm
    have hHK : H ≤ K :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hXnormK
    have hHM : H ≤ M := hHK.trans hKM
    have hHnormalM : (H.subgroupOf M).Normal := by
      simpa only [H] using hcommConclusion.2.2
    have hNHM : Subgroup.normalizer (H : Set G) = M :=
      mmax_normal hM hHM hHnormalM hHne
    exact hNHnotM (by rw [hNHM])
  have hE₁comm : IsMulCommutative E₁ := by
    letI : IsCyclic E₁ := hSigma.E₁_cyclic
    infer_instance
  have hE₁centX : E₁ ≤ Subgroup.centralizer (X : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (hX.1.trans
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr hE₁comm))
  have hsupKE₁ : K ⊔ E₁ = E := by
    have htop : K.subgroupOf E ⊔ E₁.subgroupOf E = ⊤ := by
      simpa only [K] using hSigma.E₃₂_E₁_sdprod.2.2.2.sup_eq_top
    calc
      K ⊔ E₁ =
          (K.subgroupOf E).map E.subtype ⊔
            (E₁.subgroupOf E).map E.subtype := by
        rw [Subgroup.map_subgroupOf_eq_of_le hKE,
          Subgroup.map_subgroupOf_eq_of_le hE₁E]
      _ = (K.subgroupOf E ⊔ E₁.subgroupOf E).map E.subtype := by
        rw [Subgroup.map_sup]
      _ = (⊤ : Subgroup E).map E.subtype :=
        congrArg (Subgroup.map E.subtype) htop
      _ = E := by
        rw [← MonoidHom.range_eq_map, E.range_subtype]
  have hEcentX : E ≤ Subgroup.centralizer (X : Set G) := by
    rw [← hsupKE₁]
    exact sup_le hKcentX hE₁centX
  intro x hx
  refine mem_centerWithin.mpr ⟨hXE hx, ?_⟩
  intro e he
  exact (Subgroup.mem_centralizer_iff.mp (hEcentX he) x hx).symm

/-- `BGsection12.v: abelian_tau2_norm_Sylow`, Theorem 12.8(f). -/
theorem abelian_tau2_norm_Sylow
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E A : Subgroup G} {p : ℕ} (S : Sylow p G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G))
    (X : Subgroup G)
    (hXNS : X ≤ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    ((centralizerWithin (S : Subgroup G) X).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).Normal ∧
    ((⁅(S : Subgroup G), X⁆).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).Normal := by
  let NS : Subgroup G :=
    Subgroup.normalizer ((S : Subgroup G) : Set G)
  have hfit := abelian_tau2_sub_Fitting S hM hEM hHall hpTau
    hAE hA hAS hScomm
  have hder : ⁅NS, NS⁆ ≤
      Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    dsimp [NS]
    exact hfit.normalizer_commutator_le_fitting.trans
      hfit.fitting_le_centralizer
  have hSNS : (S : Subgroup G) ≤ NS := by
    dsimp [NS]
    exact Subgroup.le_normalizer
  have hXNS' : X ≤ NS := by simpa only [NS] using hXNS
  constructor
  · exact centralizerWithin_normal_of_derived_central
      hSNS le_rfl hXNS' hder
  · have hcommS : ⁅(S : Subgroup G), X⁆ ≤ (S : Subgroup G) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hXNS
    have hcommNS : ⁅(S : Subgroup G), X⁆ ≤ NS :=
      hcommS.trans hSNS
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hcommNS).mpr
    exact normalizer_le_normalizer_commutator_of_derived_central
      le_rfl hXNS' hder

/-- `BGsection12.v: tau1_act_tau2`, Corollary 12.9. -/
theorem tau1_act_tau2
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E A Q : Subgroup G} {p q : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hqTau : q ∈ tau1Primes M)
    (hQE : Q ≤ E)
    (hQ : IsElementaryAbelianOfRank q 1 Q)
    (hregQ : centralizerWithin (sigmaCore M) Q = ⊥)
    (hcomm_ne : tau1ActionCommutator A Q ≠ ⊥) :
    Tau1ActTau2Conclusion M A Q p := by
  classical
  letI : Fact p.Prime := ⟨hpTau.1⟩
  letI : Fact q.Prime := ⟨hqTau.1⟩
  let A₀ : Subgroup G := tau1ActionCommutator A Q
  let A₁ : Subgroup G := tau1ActionFixedLine A Q
  have hAM : A ≤ M := hAE.trans hEM
  have hQM : Q ≤ M := hQE.trans hEM
  have hAcomm : IsMulCommutative A := hA.commutative
  have hComplCtx := tau2_compl_context hM hEM hHall hpTau hAE hA
  have hTauCtx := tau2_context hM hpTau hAM hA
  have hEnormA : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).mp
      hComplCtx.A_normal
  have hQnormA : Q ≤ Subgroup.normalizer (A : Set G) :=
    hQE.trans hEnormA
  have hpneQ : p ≠ q := by
    intro hpq
    subst q
    exact (tau2'1 M hqTau) hpTau
  have hAsigmaCompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card A) :=
    hA.isPGroup.isPiNumber_natCard hpTau.2.1
  have hAqCompl : IsPiNumber ({q} : Set ℕ)ᶜ (Nat.card A) := by
    apply hA.isPGroup.isPiNumber_natCard
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hpneQ
  have hQnotTau2 : IsPiNumber (tau2Primes M)ᶜ (Nat.card Q) :=
    (hQ.isPGroup.isPiNumber_natCard hqTau).mono (tau2'1 M)
  have hcopAQ : Nat.Coprime (Nat.card A) (Nat.card Q) :=
    (hA.isPGroup.isPiNumber_natCard hpTau).coprime_compl hQnotTau2
  have hQMN : Q ≤ M ⊓ Subgroup.normalizer (A : Set G) :=
    le_inf hQM hQnormA
  have hcommConclusion := commG_sigma'_1Elem_cyclic hM hAM
    hAsigmaCompl hqTau.2.1 hQ hQMN hregQ hAqCompl hAcomm
  have hA₀A : A₀ ≤ A := by
    dsimp [A₀, tau1ActionCommutator]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hQnormA
  letI : IsCyclic (⁅A, Q⁆ : Subgroup G) := hcommConclusion.2.1
  have hA₀cyclic : IsCyclic A₀ := by
    exact Subgroup.isCyclic_of_le (H' := (⁅A, Q⁆ : Subgroup G)) (by
      intro x hx
      simpa only [A₀, tau1ActionCommutator] using hx)
  have hA₀ne : A₀ ≠ ⊥ := by
    simpa only [A₀] using hcomm_ne
  have hA₀elementary : IsElementaryAbelianOfRank p 1 A₀ :=
    rankOne_of_nontrivial_cyclic_le_elementary (X := A₀)
      hA hA₀A hA₀cyclic hA₀ne
  have hA₀line : RankOneLineIn p A A₀ :=
    ⟨hA₀A, hA₀elementary⟩
  have hA₀normal : (A₀.subgroupOf M).Normal := by
    simpa only [A₀, tau1ActionCommutator] using
      hcommConclusion.2.2
  have hA₁A : A₁ ≤ A := by
    dsimp [A₁, tau1ActionFixedLine]
    exact centralizerWithin_le_left A Q
  have hA₀fixed : centralizerWithin A₀ Q = ⊥ := by
    simpa only [A₀, tau1ActionCommutator] using
      centralizerWithin_commutator_eq_bot_of_coprime_abelian_12_8
        hQnormA hcopAQ hAcomm
  have hdisA₀A₁ : Disjoint A₀ A₁ := by
    rw [disjoint_iff]
    apply le_antisymm
    · calc
        A₀ ⊓ A₁ ≤ centralizerWithin A₀ Q := by
          intro x hx
          exact ⟨hx.1, hx.2.2⟩
        _ = ⊥ := hA₀fixed
    · exact bot_le
  have hcommA₀A₁ : ∀ x ∈ A₀, ∀ y ∈ A₁, Commute x y := by
    intro x hx y hy
    exact congrArg Subtype.val
      (mul_comm (⟨x, hA₀A hx⟩ : A) ⟨y, hA₁A hy⟩)
  letI : IsMulCommutative A := hAcomm
  letI : IsSolvable A :=
    Submission.OddOrder.MathlibSupport.isSolvable_of_comm
      (fun a b : A => mul_comm a b)
  have hsupA₀A₁ : A₀ ⊔ A₁ = A := by
    apply le_antisymm (sup_le hA₀A hA₁A)
    have hdecomp :=
      le_commutator_sup_centralizerWithin_of_coprime
        (K := A) (R := Q) hQnormA hcopAQ
    rw [Subgroup.commutator_comm Q A] at hdecomp
    simpa only [A₀, A₁, tau1ActionCommutator,
      tau1ActionFixedLine] using hdecomp
  have hA₁card : Nat.card A₁ = p := by
    have hcard : Nat.card A = Nat.card A₀ * Nat.card A₁ := by
      rw [← hsupA₀A₁]
      exact natCard_sup_eq_mul_of_disjoint_of_commute
        hdisA₀A₁ hcommA₀A₁
    rw [hA.card_eq, hA₀line.2.card_eq, pow_two, pow_one] at hcard
    exact (Nat.eq_of_mul_eq_mul_left hpTau.1.pos hcard).symm
  have hA₁line : RankOneLineIn p A A₁ :=
    ⟨hA₁A, isElementaryAbelianOfRank_one_of_card_eq_prime
      hA₁card⟩

  have hA₀leSigmaCent :
      A₀ ≤ Subgroup.centralizer (sigmaCore M : Set G) := by
    simpa only [A₀, tau1ActionCommutator] using hcommConclusion.1
  have hA₀leFixedSigma :
      A₀ ≤ centralizerWithin A (sigmaCore M) :=
    le_inf hA₀A hA₀leSigmaCent
  have hFixedSigmaLeA₀ :
      centralizerWithin A (sigmaCore M) ≤ A₀ := by
    intro x hx
    by_contra hxA₀
    have hxne : x ≠ 1 := by
      intro hxone
      exact hxA₀ (hxone ▸ A₀.one_mem)
    let X : Subgroup G := Subgroup.zpowers x
    have hXline : RankOneLineIn p A X :=
      rankOneLineIn_zpowers_of_mem_12_9 hA hx.1 hxne
    have hXneA₀ : X ≠ A₀ := by
      intro hEq
      exact hxA₀ (hEq ▸ Subgroup.mem_zpowers x)
    have hXC : X ≤ centralizerWithin A (sigmaCore M) :=
      Subgroup.zpowers_le.mpr hx
    have hplane :=
      (rankTwo_distinct_lines_12_8 hA hA₀line hXline
        hXneA₀.symm).2
    have hAC : A ≤ centralizerWithin A (sigmaCore M) := by
      calc
        A ≤ A₀ ⊔ X := hplane.ge
        _ ≤ centralizerWithin A (sigmaCore M) :=
          sup_le hA₀leFixedSigma hXC
    have hSigmaCentA :
        sigmaCore M ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.le_centralizer_iff.mp (hAC.trans inf_le_right)
    have hfixedAll : centralizerWithin (sigmaCore M) A = sigmaCore M :=
      inf_eq_left.mpr hSigmaCentA
    exact Msigma_neq1 hM
      (hfixedAll.symm.trans hTauCtx.centralizerWithin_eq_bot)
  have hFixedSigma :
      centralizerWithin A (sigmaCore M) = A₀ :=
    le_antisymm hFixedSigmaLeA₀ hA₀leFixedSigma
  have hA₁neA₀ : A₁ ≠ A₀ := by
    intro hEq
    apply hA₀ne
    apply le_antisymm _ bot_le
    rw [← disjoint_iff.mp hdisA₀A₁]
    exact le_inf le_rfl (le_of_eq hEq.symm)

  have hA₀M : A₀ ≤ M := hA₀A.trans hAM
  have hNA₀ : Subgroup.normalizer (A₀ : Set G) = M :=
    mmax_normal hM hA₀M hA₀normal hA₀ne
  have hMnormA₀ : M ≤ Subgroup.normalizer (A₀ : Set G) :=
    le_of_eq hNA₀.symm
  have hnotConjugate : ∀ g : G,
      A₀ ≠ A₁.map (MulAut.conj g).toMonoidHom := by
    intro g hEq
    let Qg : Subgroup G := Q.map (MulAut.conj g).toMonoidHom
    let A₁g : Subgroup G := A₁.map (MulAut.conj g).toMonoidHom
    have hA₁gEq : A₁g = A₀ := by
      simpa only [A₁g] using hEq.symm
    have hA₁centQ : A₁ ≤ Subgroup.centralizer (Q : Set G) := by
      dsimp only [A₁, tau1ActionFixedLine]
      exact inf_le_right
    have hQcentA₁ : Q ≤ Subgroup.centralizer (A₁ : Set G) :=
      Subgroup.le_centralizer_iff.mp hA₁centQ
    have hQgcentA₀ : Qg ≤ Subgroup.centralizer (A₀ : Set G) := by
      have hmapped := Subgroup.map_mono
        (f := (MulAut.conj g).toMonoidHom) hQcentA₁
      rw [map_centralizer_equiv_12_8 A₁ (MulAut.conj g)] at hmapped
      change Qg ≤ Subgroup.centralizer (A₁g : Set G) at hmapped
      rw [hA₁gEq] at hmapped
      exact hmapped
    have hQgM : Qg ≤ M :=
      hQgcentA₀.trans
        ((Subgroup.centralizer_le_normalizer (A₀ : Set G)).trans
          (le_of_eq hNA₀))
    have hQg : IsElementaryAbelianOfRank q 1 Qg := by
      dsimp [Qg]
      exact hQ.map_of_injective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective
    have hNoRankTwoM : ¬ ∃ B : Subgroup M,
        IsElementaryAbelianOfRank q 2 B := by
      rintro ⟨B, hB⟩
      apply hqTau.2.2.2.1
      exact ⟨B.map M.subtype, Subgroup.map_subtype_le B,
        hB.map_of_injective M.subtype M.subtype_injective⟩
    obtain ⟨m, hm⟩ := rankOne_subgroups_conjugate_of_no_rankTwo
      (K := M) (X := Qg.subgroupOf M) (Y := Q.subgroupOf M)
      (mFT_odd M) (hQg.subgroupOf hQgM) (hQ.subgroupOf hQM)
      hNoRankTwoM
    have hQgconjQ :
        Qg.map (MulAut.conj (m : G)).toMonoidHom = Q := by
      have hmapped := congrArg (Subgroup.map M.subtype) hm
      rw [map_subgroupOf_conj_lift_12_9 hQgM m,
        Subgroup.map_subgroupOf_eq_of_le hQM] at hmapped
      exact hmapped
    have hA₀map :
        A₀.map (MulAut.conj (m : G)).toMonoidHom = A₀ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMnormA₀ m.2)
    have hQcentA₀ : Q ≤ Subgroup.centralizer (A₀ : Set G) := by
      have hmapped := Subgroup.map_mono
        (f := (MulAut.conj (m : G)).toMonoidHom) hQgcentA₀
      rw [map_centralizer_equiv_12_8 A₀ (MulAut.conj (m : G)),
        hQgconjQ, hA₀map] at hmapped
      exact hmapped
    have hA₀centQ : A₀ ≤ centralizerWithin A₀ Q :=
      le_inf le_rfl (Subgroup.le_centralizer_iff.mp hQcentA₀)
    apply hA₀ne
    rw [hA₀fixed] at hA₀centQ
    exact le_antisymm hA₀centQ bot_le

  have hCentA₁NotLe :
      ¬ Subgroup.centralizer (A₁ : Set G) ≤ M := by
    obtain ⟨S, hAS⟩ := hA.isPGroup.exists_le_sylow
    by_cases hScomm : IsMulCommutative (S : Subgroup G)
    · intro _hCentA₁M
      have hQpi : IsPiNumber (tau1Primes M) (Nat.card Q) :=
        hQ.isPGroup.isPiNumber_natCard hqTau
      obtain ⟨E₁, hQE₁, hE₁E, hHallE₁⟩ :=
        exists_ambient_isHall_ge_of_isSolvable hQE
          (sigma_compl_sol hEM hHall) (tau1Primes M) hQpi
      obtain ⟨E₃, hE₃E, hHallE₃⟩ := (ex_tau13_compl hEM hHall).2
      obtain ⟨E₂, _hE₂E, _hHallE₂, hCompl⟩ :=
        ex_tau2_compl hEM hHall hE₁E hHallE₁ hE₃E hHallE₃
      have habel := abelian_tau2 S hM hCompl hpTau hAE hA hAS hScomm
      have hQlineE₁ : RankOneLineIn q E₁ Q := ⟨hQE₁, hQ⟩
      have hQZE : Q ≤ centerWithin E :=
        habel.regular_rank_one_central hQlineE₁ hregQ
      have hA₀centQ : A₀ ≤ centralizerWithin A₀ Q := by
        intro a ha
        refine ⟨ha, ?_⟩
        intro x hx
        exact ((mem_centerWithin.mp (hQZE hx)).2 a
          (hA₀A.trans hAE ha)).symm
      apply hA₀ne
      rw [hA₀fixed] at hA₀centQ
      exact le_antisymm hA₀centQ bot_le
    · have hnon := nonabelian_tau2 hM hEM hHall hpTau hAE hA
        S.isPGroup' hScomm
      have hA₁lineE : RankOneLineIn p E A₁ :=
        ⟨hA₁A.trans hAE, hA₁line.2⟩
      have hA₁neDist : A₁ ≠ centralizerWithin A (sigmaCore M) := by
        intro hEq
        exact hA₁neA₀ (hEq.trans hFixedSigma)
      exact (hnon.rankOne_control A₁ hA₁lineE hA₁neDist).2

  exact
    { A0_rank_one := by simpa only [A₀] using hA₀line
      A0_sigma_centralizer := by simpa only [A₀] using hFixedSigma
      A0_normal := by simpa only [A₀] using hA₀normal
      A0_not_conjugate_to_A1 := by
        simpa only [A₀, A₁] using hnotConjugate
      A1_rank_one := by simpa only [A₁] using hA₁line
      A1_centralizer_not_le := by
        simpa only [A₁] using hCentA₁NotLe }

end

end Submission.OddOrder.BG.Section12
