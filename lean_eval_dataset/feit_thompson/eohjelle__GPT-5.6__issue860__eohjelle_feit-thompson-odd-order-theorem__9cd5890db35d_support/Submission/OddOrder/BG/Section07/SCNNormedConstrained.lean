import Submission.OddOrder.BG.Section07.NormedSubgroups
import Submission.OddOrder.MathlibSupport.PGroupPrimeSupport
import Submission.OddOrder.MathlibSupport.CoprimeSolvableCentralProduct
import Submission.OddOrder.MathlibSupport.PrimeIndex
import Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGenerationSolvable
import Submission.OddOrder.MathlibSupport.PPrimeCoreCentralizer
import Submission.OddOrder.MathlibSupport.RankTwoCentralizerIndex
import Submission.OddOrder.BG.Section07.SCNRankTwoSubgroup
import Submission.OddOrder.BG.Section07.SCNPrimeCore

/-!
# Bender--Glauberman Proposition 7.5(b)

An SCN subgroup of rank at least two satisfies Hypothesis 7.1.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport

universe u

/-- `BGsection7.SCN_normed_constrained`, Proposition 7.5(b). -/
theorem SCN_normed_constrained
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (A : Subgroup G)
    (hSCN : IsSCN (P : Subgroup G) A) (hRank : 2 ≤ Group.rank A) :
    NormedConstrained A := by
  classical
  have hAne : A ≠ ⊥ := by
    intro hAbot
    subst A
    have hzero : Group.rank (⊥ : Subgroup G) = 0 :=
      Group.rank_eq_zero _
    omega
  have hAproper : A < ⊤ :=
    lt_of_le_of_lt hSCN.le_sylow
      (mFT_pgroup_proper (P : Subgroup G) P.isPGroup')
  letI : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hAne
  have hAp : IsPGroup p A :=
    IsPGroup.to_le P.isPGroup' hSCN.le_sylow
  have hsupport : primeSupport (Nat.card A) = {p} :=
    hAp.primeSupport_natCard_eq_singleton
  have hAncyc : ¬ IsCyclic A := by
    intro hcyc
    obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
    have hclosure : Subgroup.closure ({a} : Set A) = ⊤ := by
      rw [← Subgroup.zpowers_eq_closure]
      exact ha
    have hrankLe : Group.rank A ≤ ({a} : Finset A).card := by
      apply Group.rank_le
      simpa only [Finset.coe_singleton] using hclosure
    simp only [Finset.card_singleton] at hrankLe
    omega
  have hAnormal : (A.subgroupOf (P : Subgroup G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSCN.le_sylow).mpr
      hSCN.le_normalizer
  let Z : Subgroup G := omegaOneCenterAmbient p (P : Subgroup G)
  have hZcenter : Z ≤ centerWithin (P : Subgroup G) := by
    simpa [Z] using
      omegaOneCenterAmbient_le_centerWithin p (P : Subgroup G)
  have hZA : Z ≤ A := by
    calc
      Z ≤ centerWithin (P : Subgroup G) := hZcenter
      _ ≤ centralizerWithin (P : Subgroup G) A :=
        centerWithin_le_centralizerWithin hSCN.le_sylow
      _ = A := hSCN.centralizerWithin_eq
  obtain ⟨B, hBA, hBnormal, hB, hBZ⟩ :=
    exists_normal_rankTwo_with_omegaOneCenter_dichotomy
      P.isPGroup' (mFT_odd (P : Subgroup G)) hSCN.le_sylow
        hAnormal hAncyc hZA

  refine
    { nontrivial := hAne
      proper := hAproper
      constrained := ?_ }
  intro X Y hAX hXproper hY
  rcases hY with ⟨hYX, hYpi, hAnormY⟩
  letI : IsSolvable X := mFT_sol hXproper
  have hYsol : IsSolvable Y :=
    solvable_of_solvable_injective
      (f := Subgroup.inclusion hYX) (Subgroup.inclusion_injective hYX)
  have hYprime : IsPPrimeSubgroup p Y := by
    rw [IsPPrimeSubgroup]
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hpY
    have hpNotSupport : p ∈ (primeSupport (Nat.card A))ᶜ :=
      hYpi (Fact.out : p.Prime) hpY
    rw [hsupport] at hpNotSupport
    exact hpNotSupport (by simp)

  /- Intersect the full-centralizer core with an internal centralizer, then
  use the solvable centralizer-core theorem to ascend to the ambient core. -/
  have centralizerCore_le_ambientCore
      (X₀ R W : Subgroup G) (hRX : R ≤ X₀) (hRp : IsPGroup p R)
      (hXsol : IsSolvable X₀)
      (hWD : W ≤ centralizerWithin X₀ R)
      (hWC : W ≤
        (pPrimeCore p (Subgroup.centralizer (R : Set G))).map
          (Subgroup.centralizer (R : Set G)).subtype) :
      W ≤ (pPrimeCore p X₀).map X₀.subtype := by
    let C : Subgroup G := Subgroup.centralizer (R : Set G)
    let D : Subgroup G := centralizerWithin X₀ R
    let KC : Subgroup G := (pPrimeCore p C).map C.subtype
    let L : Subgroup G := KC ⊓ D
    have hDC : D ≤ C := by
      exact inf_le_right
    have hLnormal : (L.subgroupOf D).Normal := by
      letI : (KC.subgroupOf C).Normal := by
        change (((pPrimeCore p C).map C.subtype).comap C.subtype).Normal
        rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
        infer_instance
      have hn :=
        Subgroup.inf_subgroupOf_inf_normal_of_left
          (A' := KC) (A := C) D
      change ((KC ⊓ D).subgroupOf D).Normal
      rw [inf_eq_right.mpr hDC] at hn
      exact hn
    have hKCcard : Nat.card KC = Nat.card (pPrimeCore p C) := by
      dsimp [KC]
      exact Subgroup.card_map_of_injective C.subtype_injective
    have hLprime : IsPPrimeSubgroup p L := by
      rw [IsPPrimeSubgroup]
      have hKCprime : Nat.Coprime p (Nat.card KC) := by
        rw [hKCcard]
        exact pPrimeCore_coprime_card
      exact hKCprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le inf_le_left)
    have hLsubprime : IsPPrimeSubgroup p (L.subgroupOf D) := by
      rw [IsPPrimeSubgroup, natCard_subgroupOf_eq
        (show L ≤ D from inf_le_right)]
      exact hLprime
    have hLcore : L.subgroupOf D ≤ pPrimeCore p D :=
      le_pPrimeCore hLsubprime hLnormal
    have hWcoreD : W ≤ (pPrimeCore p D).map D.subtype := by
      intro w hw
      have hwKC : w ∈ KC := by
        simpa [KC, C] using hWC hw
      have hwD : w ∈ D := hWD hw
      let wD : D := ⟨w, hwD⟩
      have hwL : wD ∈ L.subgroupOf D := ⟨hwKC, hwD⟩
      exact ⟨wD, hLcore hwL, rfl⟩
    have hcoreMap :=
      map_pPrimeCore_centralizerWithin_le_map_pPrimeCore
        (p := p) (X := X₀) (R := R) hRX hRp hXsol
    exact hWcoreD.trans (by simpa [D] using hcoreMap)

  /- If `z` lies in the omega subgroup of the center, the entire Sylow
  subgroup lies in its centralizer; restrict the SCN data and use the
  prime-core SCN leaf there. -/
  have omegaCentralizerCore
      (z : G) (hzZ : z ∈ Z) (hz1 : z ≠ 1) (W : Subgroup G)
      (hWC : W ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G))
      (hWprime : IsPPrimeSubgroup p W)
      (hAnormW : A ≤ Subgroup.normalizer (W : Set G)) :
      W ≤
        (pPrimeCore p
          (Subgroup.centralizer (Subgroup.zpowers z : Set G))).map
            (Subgroup.centralizer (Subgroup.zpowers z : Set G)).subtype := by
    let C : Subgroup G :=
      Subgroup.centralizer (Subgroup.zpowers z : Set G)
    have hzCenter : z ∈ centerWithin (P : Subgroup G) := hZcenter hzZ
    have hPC : (P : Subgroup G) ≤ C := by
      dsimp [C]
      rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
      exact hzCenter.2
    have hCproper : C < ⊤ := by
      dsimp [C]
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact mFT_cent1_proper hz1
    letI : IsSolvable C := mFT_sol hCproper
    let PC : Sylow p C := P.subtype hPC
    have hSCNC : IsSCN (PC : Subgroup C) (A.subgroupOf C) := by
      simpa [PC] using IsSCN.subgroupOf hSCN hPC
    have hWprimeC : IsPPrimeSubgroup p (W.subgroupOf C) := by
      rw [IsPPrimeSubgroup, natCard_subgroupOf_eq hWC]
      exact hWprime
    have hAnormWC :
        A.subgroupOf C ≤
          Subgroup.normalizer (W.subgroupOf C : Set C) := by
      have hsub : A.subgroupOf C ≤
          (Subgroup.normalizer (W : Set G)).subgroupOf C :=
        Subgroup.subgroupOf_mono C hAnormW
      rwa [Subgroup.subgroupOf_normalizer_eq hWC] at hsub
    have hWcoreC : W.subgroupOf C ≤ pPrimeCore p C :=
      le_pPrimeCore_of_isSCN_normalizes
        (G := C) (p := p) (mFT_odd C) PC hSCNC hWprimeC hAnormWC
    calc
      W = (W.subgroupOf C).map C.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hWC).symm
      _ ≤ (pPrimeCore p C).map C.subtype :=
        Subgroup.map_mono hWcoreC

  have hYBcop : (Nat.card Y).Coprime (Nat.card B) := by
    rw [hB.card_eq]
    exact hYprime.symm.pow_right 2
  have hYcore : Y ≤ (pPrimeCore p X).map X.subtype := by
    apply le_of_centralizerWithin_zpowers_le_of_coprime_abelian_solvable
      hB.commutative (hB.not_isCyclic (Fact.out : p.Prime))
      (hBA.trans hAnormY) hYBcop hYsol
    intro b hbB hb1
    let R : Subgroup G := Subgroup.zpowers b
    let C : Subgroup G := Subgroup.centralizer (R : Set G)
    let V : Subgroup G := centralizerWithin Y R
    have hbA : b ∈ A := hBA hbB
    have hAC : A ≤ C := by
      dsimp [C, R]
      rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
      exact
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr hSCN.commutative)
          hbA
    have hVC : V ≤ C := by
      exact inf_le_right
    have hVX : V ≤ X :=
      (centralizerWithin_le_left Y R).trans hYX
    have hVD : V ≤ centralizerWithin X R :=
      le_inf hVX hVC
    have hRX : R ≤ X := by
      dsimp [R]
      exact Subgroup.zpowers_le.mpr (hAX hbA)
    have hRp : IsPGroup p R :=
      IsPGroup.to_le P.isPGroup'
        (Subgroup.zpowers_le.mpr (hSCN.le_sylow hbA))
    have hVprime : IsPPrimeSubgroup p V := by
      rw [IsPPrimeSubgroup]
      exact hYprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le (centralizerWithin_le_left Y R))
    have hAnormC : A ≤ Subgroup.normalizer (C : Set G) :=
      hAC.trans Subgroup.le_normalizer
    have hAnormV : A ≤ Subgroup.normalizer (V : Set G) := by
      exact (le_inf hAnormY hAnormC).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    by_cases hbZ : b ∈ Z
    · have hVfull : V ≤ (pPrimeCore p C).map C.subtype := by
        simpa [C, R] using
          omegaCentralizerCore b hbZ hb1 V (by simpa [C]) hVprime hAnormV
      exact centralizerCore_le_ambientCore X R V hRX hRp
        (mFT_sol hXproper) hVD (by simpa [C] using hVfull)
    · have hZdata : Nat.card Z = p ∧ Z ≤ B := by
        rcases hBZ with hBZ | hZdata
        · exact (hbZ (hBZ hbB)).elim
        · exact hZdata
      rcases hZdata with ⟨hZcard, hZB⟩
      have hCproper : C < ⊤ := by
        dsimp [C, R]
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        exact mFT_cent1_proper hb1
      letI : IsSolvable C := mFT_sol hCproper
      let P₁ : Subgroup G := centralizerWithin (P : Subgroup G) B
      have hP₁P : P₁ ≤ (P : Subgroup G) := centralizerWithin_le_left _ _
      have hRPB : R ≤ B := by
        dsimp [R]
        exact Subgroup.zpowers_le.mpr hbB
      have hP₁C : P₁ ≤ C := by
        dsimp [P₁, C]
        exact inf_le_right.trans (Subgroup.centralizer_le hRPB)
      let P₁C : Subgroup C := P₁.subgroupOf C
      have hP₁p : IsPGroup p P₁ :=
        IsPGroup.to_le P.isPGroup' hP₁P
      have hP₁Cp : IsPGroup p P₁C :=
        hP₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₁C).symm
      obtain ⟨P₂, hP₁P₂⟩ := hP₁Cp.exists_le_sylow
      have hindexP : P₁.relIndex (P : Subgroup G) ≤ p :=
        centralizerWithin_relIndex_le_prime_of_normal_rank_two
          P.isPGroup' (hBA.trans hSCN.le_sylow) hBnormal hB
      have hcardP₁C : Nat.card P₁C = Nat.card P₁ :=
        natCard_subgroupOf_eq hP₁C
      let P₂G : Subgroup G := (P₂ : Subgroup C).map C.subtype
      have hP₂Gp : IsPGroup p P₂G := P₂.isPGroup'.map C.subtype
      obtain ⟨Q, hP₂Q⟩ := hP₂Gp.exists_le_sylow
      have hcardP₂G : Nat.card P₂G = Nat.card P₂ := by
        dsimp [P₂G]
        exact Subgroup.card_map_of_injective C.subtype_injective
      have hcardP₂P : Nat.card P₂ ≤ Nat.card P := by
        calc
          Nat.card P₂ = Nat.card P₂G := hcardP₂G.symm
          _ ≤ Nat.card Q := Subgroup.card_le_of_le hP₂Q
          _ = Nat.card P :=
            Q.card_eq_multiplicity.trans P.card_eq_multiplicity.symm
      have hmulC :
          Nat.card P₁C * P₁C.relIndex (P₂ : Subgroup C) =
            Nat.card P₂ := by
        change Nat.card P₁C *
          (P₁C.subgroupOf (P₂ : Subgroup C)).index = Nat.card P₂
        rw [← natCard_subgroupOf_eq hP₁P₂]
        exact (P₁C.subgroupOf (P₂ : Subgroup C)).card_mul_index
      have hmulP :
          Nat.card P₁ * P₁.relIndex (P : Subgroup G) = Nat.card P := by
        change Nat.card P₁ *
          (P₁.subgroupOf (P : Subgroup G)).index = Nat.card P
        rw [← natCard_subgroupOf_eq hP₁P]
        exact (P₁.subgroupOf (P : Subgroup G)).card_mul_index
      have hindexP₂ : P₁C.relIndex (P₂ : Subgroup C) ≤ p := by
        have hrelLe :
            P₁C.relIndex (P₂ : Subgroup C) ≤
              P₁.relIndex (P : Subgroup G) := by
          refine Nat.le_of_mul_le_mul_left ?_
            (Nat.card_pos (α := P₁C))
          calc
            Nat.card P₁C * P₁C.relIndex (P₂ : Subgroup C) =
                Nat.card P₂ := hmulC
            _ ≤ Nat.card P := hcardP₂P
            _ = Nat.card P₁ * P₁.relIndex (P : Subgroup G) := hmulP.symm
            _ = Nat.card P₁C * P₁.relIndex (P : Subgroup G) := by
              rw [hcardP₁C]
        exact hrelLe.trans hindexP
      let H : Subgroup P₂ := P₁C.subgroupOf (P₂ : Subgroup C)
      have hHnormal : H.Normal := by
        by_cases hindexOne : P₁C.relIndex (P₂ : Subgroup C) = 1
        · have hHtop : H = ⊤ := Subgroup.index_eq_one.mp hindexOne
          rw [hHtop]
          infer_instance
        · obtain ⟨n, hP₂card⟩ := IsPGroup.iff_card.mp P₂.isPGroup'
          have hindexDvd : P₁C.relIndex (P₂ : Subgroup C) ∣ p ^ n := by
            rw [← hP₂card]
            exact P₁C.relIndex_dvd_card (P₂ : Subgroup C)
          obtain ⟨k, -, hk⟩ :=
            (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hindexDvd
          have hk0 : k ≠ 0 := by
            intro hkzero
            apply hindexOne
            simp [hk, hkzero]
          have hpDvd : p ∣ P₁C.relIndex (P₂ : Subgroup C) := by
            rw [hk]
            exact dvd_pow_self p hk0
          have hindexPos : 0 < P₁C.relIndex (P₂ : Subgroup C) := by
            apply Nat.pos_of_ne_zero
            intro hzero
            have hP₂cardPos : 0 < Nat.card P₂ := Nat.card_pos
            rw [← hmulC, hzero, mul_zero] at hP₂cardPos
            exact (Nat.lt_irrefl 0 hP₂cardPos)
          have hpLe : p ≤ P₁C.relIndex (P₂ : Subgroup C) :=
            Nat.le_of_dvd hindexPos hpDvd
          have hindexPrime : P₁C.relIndex (P₂ : Subgroup C) = p :=
            le_antisymm hindexP₂ hpLe
          exact normal_of_index_eq_prime
            (Fact.out : p.Prime) P₂.isPGroup' hindexPrime
      letI : H.Normal := hHnormal
      let HC : Subgroup P₂ := (Subgroup.center H).map H.subtype
      letI : HC.Normal := by
        dsimp [HC]
        infer_instance
      let E : Subgroup C := HC.map (P₂ : Subgroup C).subtype
      have hEP₂ : E ≤ (P₂ : Subgroup C) := Subgroup.map_subtype_le _
      have hEnormal : (E.subgroupOf (P₂ : Subgroup C)).Normal := by
        change ((HC.map (P₂ : Subgroup C).subtype).comap
          (P₂ : Subgroup C).subtype).Normal
        rw [Subgroup.comap_map_eq_self_of_injective
          (P₂ : Subgroup C).subtype_injective]
        infer_instance
      have hEcomm : IsMulCommutative E := by
        dsimp [E, HC]
        infer_instance
      have hEcore : E ≤ pPrimePCore p C :=
        (Submission.OddOrder.BG.Section06.odd_p_abelian_constrained
          (G := C) (p := p) (mFT_odd C)) P₂ E hEcomm hEP₂ hEnormal
      have hZC : Z ≤ C := by
        intro z hz
        have hzCenter := hZcenter hz
        dsimp [C, R]
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        rcases hr with ⟨n, rfl⟩
        exact (Commute.zpow_left
          (hzCenter.2 b (hSCN.le_sylow hbA)) n)
      have hZK₂ : Z.subgroupOf C ≤ pPrimePCore p C := by
        intro z hz
        have hzCenter : (z : G) ∈ centerWithin (P : Subgroup G) :=
          hZcenter hz
        have hzP₁ : (z : G) ∈ P₁ := by
          refine ⟨hzCenter.1, ?_⟩
          intro x hx
          exact hzCenter.2 x (hSCN.le_sylow (hBA hx))
        let zC : C := ⟨(z : G), hP₁C hzP₁⟩
        have hzP₁C : zC ∈ P₁C := hzP₁
        let z₂ : P₂ := ⟨zC, hP₁P₂ hzP₁C⟩
        let zH : H := ⟨z₂, hzP₁C⟩
        have hzCenterH : zH ∈ Subgroup.center H := by
          rw [Subgroup.mem_center_iff]
          intro x
          apply Subtype.ext
          apply Subtype.ext
          apply Subtype.ext
          exact hzCenter.2 (x : G) (hP₁P x.2)
        have hzHC : z₂ ∈ HC := ⟨zH, hzCenterH, rfl⟩
        have hzE : zC ∈ E := ⟨z₂, hzHC, rfl⟩
        exact hEcore hzE

      /- Modulo the `p'`-core, `Z` lies in the `p`-core while `V` remains
      a `p'`-group, so their commutator vanishes in the quotient. -/
      let K : Subgroup C := pPrimeCore p C
      let q : C →* C ⧸ K := QuotientGroup.mk' K
      let ZC : Subgroup C := Z.subgroupOf C
      let VC : Subgroup C := V.subgroupOf C
      let Zq : Subgroup (C ⧸ K) := ZC.map q
      let Vq : Subgroup (C ⧸ K) := VC.map q
      have hVCsub : V ≤ C := hVC
      have hVCprime : IsPPrimeSubgroup p VC := by
        rw [IsPPrimeSubgroup, natCard_subgroupOf_eq hVCsub]
        exact hVprime
      have hVqprime : IsPPrimeSubgroup p Vq := by
        rw [IsPPrimeSubgroup]
        exact hVCprime.coprime_dvd_right (Subgroup.card_map_dvd VC q)
      have hZqPcore : Zq ≤ pCore p (C ⧸ K) := by
        have hmapped : ZC.map q ≤ (pPrimePCore p C).map q :=
          Subgroup.map_mono hZK₂
        simpa [Zq, q, K, pPrimePCore_map_quotient_eq] using hmapped
      have hZCnormVC : ZC ≤ Subgroup.normalizer (VC : Set C) := by
        have hsub : Z.subgroupOf C ≤
            (Subgroup.normalizer (V : Set G)).subgroupOf C :=
          Subgroup.subgroupOf_mono C (hZB.trans (hBA.trans hAnormV))
        rwa [Subgroup.subgroupOf_normalizer_eq hVCsub] at hsub
      have hZqnormVq : Zq ≤ Subgroup.normalizer (Vq : Set (C ⧸ K)) :=
        (Subgroup.map_mono hZCnormVC).trans (VC.le_normalizer_map q)
      have hcommVq : ⁅Zq, Vq⁆ ≤ Vq :=
        Subgroup.le_normalizer_iff_commutator_le_right.mp hZqnormVq
      have hcommPq : ⁅Zq, Vq⁆ ≤ pCore p (C ⧸ K) :=
        (Subgroup.commutator_mono hZqPcore le_top).trans
          (Subgroup.commutator_le_left (pCore p (C ⧸ K)) ⊤)
      have hPqVqDisjoint : Disjoint (pCore p (C ⧸ K)) Vq := by
        apply Subgroup.disjoint_of_coprime_natCard
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp
          (pCore_isPGroup (G := C ⧸ K) (p := p))
        rw [hn]
        exact hVqprime.pow_left n
      have hcommqBot : ⁅Zq, Vq⁆ = ⊥ := by
        apply le_bot_iff.mp
        exact (le_inf hcommPq hcommVq).trans
          (disjoint_iff.mp hPqVqDisjoint).le
      have hcommZCVC : ⁅ZC, VC⁆ ≤ K := by
        rw [← QuotientGroup.ker_mk' K]
        apply (Subgroup.map_eq_bot_iff ⁅ZC, VC⁆).mp
        rw [Subgroup.map_commutator]
        exact hcommqBot
      have hmapZC : ZC.map C.subtype = Z :=
        Subgroup.map_subgroupOf_eq_of_le hZC
      have hmapVC : VC.map C.subtype = V :=
        Subgroup.map_subgroupOf_eq_of_le hVCsub
      have hcommCore : ⁅Z, V⁆ ≤ (pPrimeCore p C).map C.subtype := by
        have hmapped : (⁅ZC, VC⁆ : Subgroup C).map C.subtype ≤
            K.map C.subtype :=
          Subgroup.map_mono hcommZCVC
        simpa [K, Subgroup.map_commutator, hmapZC, hmapVC] using hmapped

      have hZne : Z ≠ ⊥ := by
        intro hZbot
        rw [hZbot, Subgroup.card_bot] at hZcard
        exact (Fact.out : p.Prime).ne_one hZcard.symm
      have hZcyc : IsCyclic Z := isCyclic_of_prime_card hZcard
      obtain ⟨z, hzgen⟩ :=
        (Z.isCyclic_iff_exists_zpowers_eq_top).mp hZcyc
      have hzZ : z ∈ Z := by
        rw [← hzgen]
        exact Subgroup.mem_zpowers z
      have hz1 : z ≠ 1 := by
        rw [← Subgroup.zpowers_ne_bot, hzgen]
        exact hZne
      let W : Subgroup G := centralizerWithin V Z
      have hWprime : IsPPrimeSubgroup p W := by
        rw [IsPPrimeSubgroup]
        exact hVprime.coprime_dvd_right
          (Subgroup.card_dvd_of_le (centralizerWithin_le_left V Z))
      have hAW : A ≤ Subgroup.normalizer (W : Set G) := by
        have hAZcent : A ≤ Subgroup.centralizer (Z : Set G) := by
          rw [Subgroup.le_centralizer_iff]
          exact hZA.trans
            (Subgroup.le_centralizer_iff_isMulCommutative.mpr
              hSCN.commutative)
        have hAnormCZ : A ≤
            Subgroup.normalizer (Subgroup.centralizer (Z : Set G) : Set G) :=
          hAZcent.trans Subgroup.le_normalizer
        simpa [W, centralizerWithin] using
          ((le_inf hAnormV hAnormCZ).trans
            Subgroup.inf_normalizer_le_normalizer_inf)
      have hWfull : W ≤
          (pPrimeCore p
            (Subgroup.centralizer (Subgroup.zpowers z : Set G))).map
              (Subgroup.centralizer (Subgroup.zpowers z : Set G)).subtype := by
        apply omegaCentralizerCore z hzZ hz1 W
        · simpa [W, hzgen] using
            (show W ≤ Subgroup.centralizer (Z : Set G) from inf_le_right)
        · exact hWprime
        · exact hAW
      have hRzC : Subgroup.zpowers z ≤ C := by
        rw [hzgen]
        exact hZC
      have hRzp : IsPGroup p (Subgroup.zpowers z) :=
        IsPGroup.to_le P.isPGroup'
          (Subgroup.zpowers_le.mpr (hZcenter hzZ).1)
      have hWD : W ≤ centralizerWithin C (Subgroup.zpowers z) := by
        apply le_inf
        · exact (centralizerWithin_le_left V Z).trans hVC
        · simpa [W, hzgen] using
            (show W ≤ Subgroup.centralizer (Z : Set G) from inf_le_right)
      have hWcore : W ≤ (pPrimeCore p C).map C.subtype :=
        centralizerCore_le_ambientCore C (Subgroup.zpowers z) W
          hRzC hRzp (mFT_sol hCproper) hWD hWfull
      have hVsol : IsSolvable V :=
        solvable_of_solvable_injective
          (f := Subgroup.inclusion hVC) (Subgroup.inclusion_injective hVC)
      letI : IsSolvable V := hVsol
      have hVZcop : (Nat.card V).Coprime (Nat.card Z) := by
        rw [hZcard]
        exact hVprime.symm
      have hVcoreC : V ≤ (pPrimeCore p C).map C.subtype := by
        apply (le_commutator_sup_centralizerWithin_of_coprime
          (K := V) (R := Z) (hZB.trans (hBA.trans hAnormV)) hVZcop).trans
        exact sup_le hcommCore hWcore
      exact centralizerCore_le_ambientCore X R V hRX hRp
        (mFT_sol hXproper) hVD (by simpa [C] using hVcoreC)

  let K : Subgroup G := (pPrimeCore p X).map X.subtype
  have hYK : Y ≤ K := by
    simpa [K] using hYcore
  have hKX : K ≤ X := by
    dsimp [K]
    exact Subgroup.map_subtype_le _
  have hKnormal : (K.subgroupOf X).Normal := by
    change (((pPrimeCore p X).map X.subtype).comap X.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    infer_instance
  have hKcard : Nat.card K = Nat.card (pPrimeCore p X) := by
    dsimp [K]
    exact Subgroup.card_map_of_injective X.subtype_injective
  have hKcop : Nat.Coprime p (Nat.card K) := by
    rw [hKcard]
    exact pPrimeCore_coprime_card
  have hKpi :
      IsPiNumber (primeSupport (Nat.card A))ᶜ (Nat.card K) := by
    intro q hq hqK
    rw [hsupport]
    intro hqp
    have hqpEq : q = p := Set.mem_singleton_iff.mp hqp
    subst q
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hKcop) hqK
  have hKcore : K ≤ primeSetCore (primeSupport (Nat.card A))ᶜ X := by
    rw [primeSetCore]
    exact le_sSup ⟨hKX, hKnormal, hKpi⟩
  exact hYK.trans hKcore

end Submission.OddOrder.BG.Section07
