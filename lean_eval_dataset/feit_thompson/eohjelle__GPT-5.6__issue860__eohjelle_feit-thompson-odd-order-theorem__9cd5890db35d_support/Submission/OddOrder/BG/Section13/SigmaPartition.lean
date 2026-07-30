import Submission.OddOrder.BG.Section12.SigmaComplementContext
import Submission.OddOrder.BG.Section12.NonabelianUniqueness
import Submission.OddOrder.BG.Section12.SigmaEmbedding
import Submission.OddOrder.BG.Section13.MsigmaCentrality
import Submission.OddOrder.MathlibSupport.BetaQuotientCommutator
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowConjugacy
import Submission.OddOrder.MathlibSupport.AmbientFitting
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Submission.OddOrder.MathlibSupport.PGroupCenter
import Submission.OddOrder.MathlibSupport.PPrimeCoreDerivedHall
import Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow
import Submission.OddOrder.MathlibSupport.SolvableHallConjugacyTransport
import Submission.OddOrder.MathlibSupport.SylowIntersectionNormalizer
import Submission.OddOrder.MathlibSupport.Tau1PrimeComplementInvariantSylow

/-!
# Bender--Glauberman Section 13: the sigma partition

This file ports `BGsection13.v`, lines 576--821: Lemma 13.8 and
Theorem 13.9.  The source's ambient notation `q.-Sylow(K) Q` is represented
by `IsSylowSubgroupOf q Q K`.
-/

namespace Submission.OddOrder.BG.Section13

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.MathlibSupport
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

private theorem map_conj_map_conj
    {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_one
    {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj 1).toMonoidHom = H := by
  convert H.map_id using 1
  ext x
  simp

private theorem map_conj_inv_map_conj
    {G : Type*} [Group G] (H : Subgroup G) (a : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj a⁻¹).toMonoidHom = H := by
  rw [map_conj_map_conj]
  simpa only [inv_mul_cancel] using map_conj_one H

/-- A Sylow subgroup of a Hall subgroup is Sylow in the ambient group. -/
private theorem exists_sylow_eq_map_of_sylow_hall
    {H : Type u} [Group H] [Finite H]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {A : Subgroup H} (hA : IsHall pi A) (hpPi : p ∈ pi)
    (P : Sylow p A) :
    ∃ Q : Sylow p H,
      (Q : Subgroup H) = (P : Subgroup A).map A.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup H := (P : Subgroup A).map A.subtype
  have hSp : IsPGroup p S := P.isPGroup'.map A.subtype
  have hpAindex : ¬ p ∣ A.index := by
    intro hpIndex
    exact hA.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpAindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

/-- Extend an ambient Sylow subgroup of an intersection across the factor
whose normalizer already contains it. -/
private theorem isSylowSubgroupOf_left_of_inf_of_normalizer_le
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H M Q : Subgroup G}
    (hQ : IsSylowSubgroupOf p Q (H ⊓ M))
    (hNQM : Subgroup.normalizer (Q : Set G) ≤ M) :
    IsSylowSubgroupOf p Q H := by
  obtain ⟨R, rfl⟩ := hQ
  obtain ⟨S, hS⟩ :=
    exists_sylow_map_eq_of_sylow_inf_of_normalizer_le H M R hNQM
  exact ⟨S, hS.symm⟩

/-- The ambient image in `IsSylowSubgroupOf` lies in its ambient group. -/
private theorem IsSylowSubgroupOf.le_sigmaPartition
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Q K : Subgroup G}
  (hQ : IsSylowSubgroupOf p Q K) : Q ≤ K := by
  obtain ⟨R, rfl⟩ := hQ
  exact Subgroup.map_subtype_le (R : Subgroup K)

/-- A subgroup whose full normalizer lies in a proper subgroup cannot be
trivial. -/
private theorem ne_bot_of_normalizer_le_mmax
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {Q M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hNQM : Subgroup.normalizer (Q : Set G) ≤ M) : Q ≠ ⊥ := by
  intro hQ
  have hnormalizerBot :
      Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top (⊥ : Subgroup G)
  have htop : (⊤ : Subgroup G) ≤ M := by
    rw [hQ, hnormalizerBot] at hNQM
    exact hNQM
  exact (not_le_of_gt (mmax_proper hM)) htop

/-- Restrict an ambient Sylow subgroup to an intermediate intersection
which still contains it. -/
private theorem isSylowSubgroupOf_inf_of_le
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {S M L : Subgroup G}
    (hS : IsSylowSubgroupOf p S M) (hSL : S ≤ L) :
    IsSylowSubgroupOf p S (M ⊓ L) := by
  have hSI : S ≤ M ⊓ L :=
    le_inf (IsSylowSubgroupOf.le_sigmaPartition hS) hSL
  have hSp : IsPGroup p S := hS.isPGroup
  obtain ⟨P, hP⟩ := hS
  let I : Subgroup G := M ⊓ L
  change S ≤ I at hSI
  let SI : Subgroup I := S.subgroupOf I
  have hSIp : IsPGroup p SI :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSI).symm
  obtain ⟨T, hSIT⟩ := hSIp.exists_le_sylow
  let TG : Subgroup G := (T : Subgroup I).map I.subtype
  have hTGp : IsPGroup p TG := T.isPGroup'.map I.subtype
  have hTGM : TG ≤ M :=
    (Subgroup.map_subtype_le (T : Subgroup I)).trans inf_le_left
  let TM : Subgroup M := TG.subgroupOf M
  have hTMp : IsPGroup p TM :=
    hTGp.of_equiv (Subgroup.subgroupOfEquivOfLe hTGM).symm
  have hPTM : (P : Subgroup M) ≤ TM := by
    intro x hx
    change (x : G) ∈ TG
    have hxS : (x : G) ∈ S := by
      rw [hP]
      exact Subgroup.mem_map_of_mem M.subtype hx
    let xI : I := ⟨x, hSI hxS⟩
    have hxSI : xI ∈ SI := hxS
    exact Subgroup.mem_map_of_mem I.subtype (hSIT hxSI)
  have hTMP : TM = (P : Subgroup M) := P.is_maximal' hTMp hPTM
  have hTGS : TG = S := by
    calc
      TG = TM.map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hTGM).symm
      _ = (P : Subgroup M).map M.subtype := by rw [hTMP]
      _ = S := hP.symm
  exact ⟨T, by
    change S = TG
    exact hTGS.symm⟩

/-- Cauchy's theorem, packaged as a rank-one elementary-abelian ambient
subgroup. -/
private theorem exists_rankOne_le_of_prime_dvd_natCard
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hpK : p ∣ Nat.card K) :
    ∃ P : Subgroup G, P ≤ K ∧ IsElementaryAbelianOfRank p 1 P := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpK
  let P : Subgroup G := (Subgroup.zpowers x).map K.subtype
  have hcardZ : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hx]
  have hcardP : Nat.card P = p := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hcardZ]
  exact ⟨P, Subgroup.map_subtype_le _,
    isElementaryAbelianOfRank_one_of_card_eq_prime hcardP⟩

/-- A group of the same prime characteristic cannot act fixed-point freely
on a nontrivial normalized subgroup. -/
private theorem prime_ne_of_centralizerWithin_eq_bot
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {P Q : Subgroup G}
    (hP : IsElementaryAbelianOfRank p 1 P)
    (hQ : IsPGroup q Q) (hQne : Q ≠ ⊥)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hcent : centralizerWithin Q P = ⊥) : q ≠ p := by
  intro hqp
  subst q
  let J : Subgroup G := P ⊔ Q
  have hJp : IsPGroup p J :=
    hP.isPGroup.to_sup_of_normal_right' hQ hPQ
  have hQJ : Q ≤ J := le_sup_right
  let QJ : Subgroup J := Q.subgroupOf J
  letI : QJ.Normal := by
    dsimp [QJ, J]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hPQ
  have hQJne : QJ ≠ ⊥ := by
    intro hbot
    change Q.subgroupOf J = ⊥ at hbot
    apply hQne
    rw [← Subgroup.map_subgroupOf_eq_of_le hQJ, hbot,
      Subgroup.map_bot]
  have hmeet : QJ ⊓ Subgroup.center J ≠ ⊥ :=
    normal_inf_center_ne_bot hJp QJ hQJne
  let Z : Subgroup G :=
    (QJ ⊓ Subgroup.center J).map J.subtype
  have hZne : Z ≠ ⊥ := by
    intro hZ
    apply hmeet
    exact (Subgroup.map_eq_bot_iff_of_injective
      (QJ ⊓ Subgroup.center J) J.subtype_injective).mp hZ
  have hZcent : Z ≤ centralizerWithin Q P := by
    rintro z ⟨zJ, hzJ, rfl⟩
    exact mem_centralizerWithin.mpr ⟨hzJ.1, by
      intro x hx
      have hxJ : x ∈ J := (le_sup_left : P ≤ P ⊔ Q) hx
      simpa using congrArg J.subtype
        (Subgroup.mem_center_iff.mp hzJ.2 ⟨x, hxJ⟩)⟩
  exact hZne (le_bot_iff.mp (hZcent.trans_eq hcent))

/-- A `pi`-subgroup lies in a normal `pi`-Hall subgroup. -/
private theorem isPiNumber_le_normal_isHall
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {A H : Subgroup K}
    (hHnormal : H.Normal) (hHHall : IsHall pi H)
    (hApi : IsPiNumber pi (Nat.card A)) : A ≤ H := by
  letI : H.Normal := hHnormal
  have hcop : (Nat.card A).Coprime H.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpA hpIndex
    exact hHHall.isPiNumber_index hp hpIndex (hApi hp hpA)
  intro x hx
  let q : K →* K ⧸ H := QuotientGroup.mk' H
  have horderA : orderOf (q x) ∣ Nat.card A :=
    (orderOf_map_dvd q x).trans (A.orderOf_dvd_natCard hx)
  have horderIndex : orderOf (q x) ∣ H.index := by
    simpa only [H.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderA horderIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (orderOf_eq_one_iff.mp horderOne)

/-- The prime-set core is a Hall subgroup of a finite nilpotent group. -/
private theorem piCore_isHall_of_isNilpotent
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    (pi : Set ℕ) : IsHall pi (piCore pi K) := by
  exact ⟨piCore_isPiNumber pi, by
    intro p hp hpIndex hpPi
    letI : Fact p.Prime := ⟨hp⟩
    let P : Sylow p K := Classical.choice Sylow.nonempty
    have hPnormal : (P : Subgroup K).Normal := by infer_instance
    have hPle : (P : Subgroup K) ≤ piCore pi K :=
      le_piCore hPnormal (P.isPGroup'.isPiNumber_natCard hpPi)
    exact P.not_dvd_index (hpIndex.trans (Subgroup.index_dvd_of_le hPle))⟩

/-- Subgroups supported on complementary sets of primes commute in a
finite nilpotent group. -/
private theorem nilpotent_subgroups_commute_of_coprime_pi
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    {pi : Set ℕ} {A B : Subgroup K}
    (hA : IsPiNumber pi (Nat.card A))
    (hB : IsPiNumber piᶜ (Nat.card B)) :
    A ≤ Subgroup.centralizer (B : Set K) := by
  let O : Subgroup K := piCore pi K
  let O' : Subgroup K := piCore piᶜ K
  have hAO : A ≤ O :=
    isPiNumber_le_normal_isHall (by infer_instance)
      (piCore_isHall_of_isNilpotent pi) hA
  have hBO' : B ≤ O' :=
    isPiNumber_le_normal_isHall (by infer_instance)
      (piCore_isHall_of_isNilpotent piᶜ) hB
  have hdis : Disjoint O O' :=
    Subgroup.disjoint_of_coprime_natCard
      ((piCore_isPiNumber pi).coprime_compl
        (by simpa only [compl_compl] using
          (piCore_isPiNumber (G := K) piᶜ)))
  have hcomm := Subgroup.commute_of_normal_of_disjoint
    O O' (by infer_instance) (by infer_instance) hdis
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (hcomm a b (hAO ha) (hBO' hb)).eq.symm

/-- A fitting prime gives a nontrivial ambient prime core. -/
private theorem ambient_pCore_ne_bot_of_dvd_fittingWithin
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hpF : p ∣ Nat.card (fittingWithin H)) :
    (pCore p H).map H.subtype ≠ ⊥ := by
  have hcoreF : pCore p (fittingWithin H) ≠ ⊥ :=
    (pCore_ne_bot_iff_dvd_card_of_isNilpotent
      (G := fittingWithin H) p).2 hpF
  intro hmap
  have hmapF :
      (pCore p (fittingWithin H)).map
          (fittingWithin H).subtype = ⊥ := by
    rw [map_pCore_fittingWithin_eq_map_pCore H p]
    exact hmap
  exact hcoreF
    ((Subgroup.map_eq_bot_iff_of_injective
      (pCore p (fittingWithin H))
      (fittingWithin H).subtype_injective).mp hmapF)

/-- The quotient of a subgroup by the restricted ambient normal subgroup
is canonically its image in the ambient quotient. -/
private def subgroupQuotientEquivImage13_8
    {K : Type u} [Group K] (B D : Subgroup K) [B.Normal] :
    (D ⧸ B.subgroupOf D) ≃* D.map (QuotientGroup.mk' B) := by
  letI : (B.subgroupOf D).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : B.Normal) D
  exact QuotientGroup.liftEquiv (B.subgroupOf D)
    ((QuotientGroup.mk' B).subgroupMap_surjective D) (by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])

/-- If a Sylow subgroup of a normal subgroup has Sylow image in a
nilpotent quotient, adjoining the quotient kernel makes it normal in the
ambient group.  This is the local Frattini input in Lemma 13.8. -/
private theorem normal_sup_of_sylow_quotient_nilpotent_13_8
    {K : Type u} [Group K] [Finite K]
    {q : ℕ} [Fact q.Prime]
    {B D X : Subgroup K} [B.Normal] [D.Normal]
    (hBD : B ≤ D) (_hXD : X ≤ D)
    (hX : IsSylowSubgroupOf q X D)
    (hnil : Group.IsNilpotent (D ⧸ B.subgroupOf D)) :
    (B ⊔ X).Normal := by
  let pi : K →* K ⧸ B := QuotientGroup.mk' B
  let Dbar : Subgroup (K ⧸ B) := D.map pi
  letI : Dbar.Normal := by
    dsimp [Dbar, pi]
    exact Subgroup.Normal.map (inferInstance : D.Normal)
      (QuotientGroup.mk' B) (QuotientGroup.mk'_surjective B)
  letI : Group.IsNilpotent Dbar := by
    letI : Group.IsNilpotent (D ⧸ B.subgroupOf D) := hnil
    simpa [Dbar, pi] using
      Group.nilpotent_of_mulEquiv
        (subgroupQuotientEquivImage13_8 B D)
  obtain ⟨P, hXP⟩ := hX
  let Q : Sylow q Dbar :=
    P.mapSurjective (pi.subgroupMap_surjective D)
  have hXmap :
      X.map pi = (Q : Subgroup Dbar).map Dbar.subtype := by
    rw [hXP]
    change
      ((P : Subgroup D).map D.subtype).map pi =
        ((P.mapSurjective (pi.subgroupMap_surjective D) :
          Sylow q Dbar) : Subgroup Dbar).map Dbar.subtype
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    apply congrArg
      (fun f : D →* K ⧸ B ↦ (P : Subgroup D).map f)
    ext d
    rfl
  have hQcore : (Q : Subgroup Dbar) = pCore q Dbar :=
    (pCore_eq_sylow_of_isNilpotent Q).symm
  have hXmapNormal : (X.map pi).Normal := by
    rw [hXmap, hQcore]
    infer_instance
  have hcomapNormal : ((X.map pi).comap pi).Normal :=
    hXmapNormal.comap pi
  simpa [pi, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm] using
    hcomapNormal

/-! ## Local data for Lemma 13.8 -/

/-- The five conclusions extracted from the source predicate `Qprops` in
the proof of Lemma 13.8.  Keeping this predicate named makes the symmetry
between `(M,q,Q)` and `(L,q_star,U)` explicit. -/
def Tau1AsymmetrySylowData
    {G : Type u} [Group G] [Finite G]
    (p q : ℕ) (M P Q : Subgroup G) : Prop :=
  IsSylowSubgroupOf q Q M ∧
    q ≠ p ∧
    q ∉ betaPrimes M ∧
    centralizerWithin (betaCore M) P ≠ ⊥ ∧
    centralizerWithin (betaCore M) (P ⊔ Q) = ⊥

/-- The oriented local data left after the Hall/Fitting reduction in
Lemma 13.8.

The base maximal subgroup is `M`; `L` is the other maximal subgroup.
The existential `H` is allowed to be the Hall conjugate selected after
orienting the two beta sets; `X` is its nontrivial fitting prime core inside
`C_{beta(M)}(P)`.  The opposite beta prime `r` and the beta-normalizer
factorization are precisely the inputs consumed by
`exists_rankOne_le_centralizerWithin_inf_normalizer_of_tau1`. -/
def Tau1AsymmetryFittingData
    {G : Type u} [Group G] [Finite G]
    (M L P Q : Subgroup G) : Prop :=
  ∃ (H X : Subgroup G) (r : ℕ),
    X ≠ ⊥ ∧
      X ≤ H ∧
      X ≤ betaCore M ∧
      H ≤ M ∧
      H ≤ Subgroup.centralizer (P : Set G) ∧
      r ∈ betaPrimes L ∧
      r ∣ Nat.card H ∧
      betaCore M ⊔
        (M ⊓ Subgroup.normalizer (Q : Set G)) = M

/-- Construct the oriented Hall/Fitting data in Lemma 13.8.

This is the direct port of `BGsection13.v`, lines 626--710.  The selected
fitting prime core first forces the Hall subgroup into `M` by beta
normalizer control and sigma transitivity.  A prime from the opposite beta
centralizer gives `r ∣ |H|`, and the nilpotent beta quotient plus the
Frattini argument supplies the final normalizer factorization. -/
private theorem tau1_asymmetry_fitting_data
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M L P Q H : Subgroup G} {p q s : ℕ}
    [Fact p.Prime] [Fact q.Prime] [Fact s.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hPM : P ≤ M)
    (hP : IsElementaryAbelianOfRank p 1 P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : centralizerWithin Q P = ⊥)
    (hQprops : Tau1AsymmetrySylowData p q M P Q)
    (hOppCent : centralizerWithin (betaCore L) P ≠ ⊥)
    (hHC : H ≤ Subgroup.centralizer (P : Set G))
    (hHall : IsHall (betaPrimes M ∪ betaPrimes L)
      (H.subgroupOf (Subgroup.centralizer (P : Set G))))
    (hAH : centralizerWithin (betaCore M) P ≤ H)
    (hsF : s ∣ Nat.card (fittingWithin H))
    (hsBetaM : s ∈ betaPrimes M) :
    Tau1AsymmetryFittingData M L P Q := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let A : Subgroup G := centralizerWithin (betaCore M) P
  change H ≤ C at hHC
  change IsHall (betaPrimes M ∪ betaPrimes L)
    (H.subgroupOf C) at hHall
  change A ≤ H at hAH
  let X : Subgroup G := (pCore s H).map H.subtype
  have hXne : X ≠ ⊥ := by
    simpa only [X] using
      (ambient_pCore_ne_bot_of_dvd_fittingWithin hsF)
  have hXH : X ≤ H := by
    dsimp only [X]
    exact Subgroup.map_subtype_le _
  have hXs : IsPGroup s X := by
    dsimp only [X]
    exact pCore_isPGroup.map H.subtype
  have hXsub : X.subgroupOf H = pCore s H := by
    change ((pCore s H).map H.subtype).comap H.subtype = pCore s H
    exact Subgroup.comap_map_eq_self_of_injective
      H.subtype_injective (pCore s H)
  have hXnormalH : (X.subgroupOf H).Normal := by
    rw [hXsub]
    infer_instance
  have hHnormX : H ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mp hXnormalH

  /- Conjugate `X` into `betaCore M`; its normalizer then puts all of `H`
  in the same conjugate of `M`. -/
  let SB : Sylow s (betaCore M) := Classical.choice Sylow.nonempty
  obtain ⟨S, hS⟩ :=
    exists_sylow_eq_map_of_sylow_hall
      (Fact.out : s.Prime) (Mbeta_Hall_G hM) hsBetaM SB
  obtain ⟨T, hXT⟩ := hXs.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hST :
      (S : Subgroup G).map (MulAut.conj g).toMonoidHom =
        (T : Subgroup G) := by
    change MulAut.conj g • (S : Subgroup G) = (T : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hg]
  have hSbeta : (S : Subgroup G) ≤ betaCore M := by
    rw [hS]
    exact Subgroup.map_subtype_le (SB : Subgroup (betaCore M))
  let Mg : Subgroup G := M.map (MulAut.conj g).toMonoidHom
  have hXMg : X ≤ Mg := by
    calc
      X ≤ (T : Subgroup G) := hXT
      _ = (S : Subgroup G).map (MulAut.conj g).toMonoidHom := hST.symm
      _ ≤ (betaCore M).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hSbeta
      _ ≤ Mg := Subgroup.map_mono (betaCore_le M)
  have hMg : Mg ∈ minSimple_max_groups (G := G) := by
    dsimp only [Mg]
    exact (mmaxJ M (MulAut.conj g)).mpr hM
  have hsBetaMg : s ∈ betaPrimes Mg := by
    dsimp only [Mg]
    rw [betaPrimes_conj]
    exact hsBetaM
  have hNormXMg : Subgroup.normalizer (X : Set G) ≤ Mg :=
    beta_norm_sub_mmax hMg hXMg
      (hXs.isPiNumber_natCard hsBetaMg) hXne
  have hHMg : H ≤ Mg := hHnormX.trans hNormXMg

  /- A nontrivial prime core in the Fitting subgroup of
  `C_{beta(M)}(P)` fixes the conjugate of `M` selected above. -/
  have hAC : A ≤ C := by
    dsimp only [A, C]
    exact inf_le_right
  have hCsol : IsSolvable C := by
    dsimp only [C]
    exact mFT_sol (mFT_cent_proper P hP.ne_bot)
  have hAsol : IsSolvable A := by
    letI : IsSolvable C := hCsol
    exact isSolvable_of_injective (Subgroup.inclusion hAC)
      (Subgroup.inclusion_injective hAC)
  have hAne : A ≠ ⊥ := by
    simpa only [A] using hQprops.2.2.2.1
  have hFAne : fittingWithin A ≠ ⊥ := by
    intro hFbot
    exact hAne
      (Section08.eq_bot_of_fittingWithin_eq_bot_of_isSolvable
        A hAsol hFbot)
  have hFAcard : Nat.card (fittingWithin A) ≠ 1 :=
    fun hc ↦ hFAne (Subgroup.card_eq_one.mp hc)
  obtain ⟨t, htPrime, htFA⟩ := Nat.exists_prime_and_dvd hFAcard
  letI : Fact t.Prime := ⟨htPrime⟩
  let Y : Subgroup G := (pCore t A).map A.subtype
  have hYne : Y ≠ ⊥ := by
    simpa only [Y] using
      (ambient_pCore_ne_bot_of_dvd_fittingWithin htFA)
  have hYA : Y ≤ A := by
    dsimp only [Y]
    exact Subgroup.map_subtype_le _
  have hYt : IsPGroup t Y := by
    dsimp only [Y]
    exact pCore_isPGroup.map A.subtype
  have htY : t ∣ Nat.card Y :=
    hYt.card_eq_or_dvd.resolve_left
      (fun hc ↦ hYne (Subgroup.card_eq_one.mp hc))
  have hYbeta : Y ≤ betaCore M :=
    hYA.trans (centralizerWithin_le_left (betaCore M) P)
  have htBetaM : t ∈ betaPrimes M :=
    (betaCore_isPiNumber M) htPrime
      (htY.trans (Subgroup.card_dvd_of_le hYbeta))
  have hYM : Y ≤ M := hYbeta.trans (betaCore_le M)
  have hNYM : Subgroup.normalizer (Y : Set G) ≤ M :=
    beta_norm_sub_mmax hM hYM
      (hYt.isPiNumber_natCard htBetaM) hYne
  have hYH : Y ≤ H := hYA.trans hAH
  have hYMg : Y ≤ Mg := hYH.trans hHMg
  have hMover :
      ((∃ a : G, M = M.map (MulAut.conj a).toMonoidHom) ∧ Y ≤ M) :=
    ⟨⟨1, (map_conj_one M).symm⟩, hYM⟩
  have hMgover :
      ((∃ a : G, Mg = M.map (MulAut.conj a).toMonoidHom) ∧ Y ≤ Mg) :=
    ⟨⟨g, rfl⟩, hYMg⟩
  obtain ⟨c, hcY, hMgMap⟩ :=
    (sigma_group_trans hM (beta_sub_sigma hM htBetaM) hYt).2.1
      hMover hMgover
  have hcM : c ∈ M :=
    hNYM (Subgroup.centralizer_le_normalizer (Y : Set G) hcY)
  have hMmapc : M.map (MulAut.conj c).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer hcM)
  have hMgM : Mg = M := hMgMap.trans hMmapc
  have hHM : H ≤ M := hHMg.trans_eq hMgM

  /- The oriented fitting core is now inside the beta Hall subgroup of
  `M`. -/
  have hXM : X ≤ M := hXH.trans hHM
  let XM : Subgroup M := X.subgroupOf M
  let BM : Subgroup M := (betaCore M).subgroupOf M
  have hXMpi : IsPiNumber (betaPrimes M) (Nat.card XM) := by
    rw [MathlibSupport.natCard_subgroupOf_eq hXM]
    exact hXs.isPiNumber_natCard hsBetaM
  have hBMnormal : BM.Normal := by
    simpa only [BM] using betaCore_normal M
  have hXMB : XM ≤ BM :=
    isPiNumber_le_normal_isHall hBMnormal
      (by simpa only [BM] using Mbeta_Hall hM) hXMpi
  have hXbeta : X ≤ betaCore M := by
    calc
      X = XM.map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hXM).symm
      _ ≤ BM.map M.subtype := Subgroup.map_mono hXMB
      _ = betaCore M := by
        dsimp only [BM]
        rw [Subgroup.map_subgroupOf_eq_of_le (betaCore_le M)]

  /- A prime in the opposite beta centralizer also divides the Hall
  subgroup. -/
  let AL : Subgroup G := centralizerWithin (betaCore L) P
  have hALne : AL ≠ ⊥ := by
    simpa only [AL] using hOppCent
  have hALcard : Nat.card AL ≠ 1 :=
    fun hc ↦ hALne (Subgroup.card_eq_one.mp hc)
  obtain ⟨r, hrPrime, hrAL⟩ := Nat.exists_prime_and_dvd hALcard
  have hrBetaL : r ∈ betaPrimes L :=
    (betaCore_isPiNumber L) hrPrime
      (hrAL.trans (Subgroup.card_dvd_of_le
        (centralizerWithin_le_left (betaCore L) P)))
  have hALC : AL ≤ C := by
    dsimp only [AL, C]
    exact inf_le_right
  have hrC : r ∣ Nat.card C :=
    hrAL.trans (Subgroup.card_dvd_of_le hALC)
  have hrUnion : r ∈ betaPrimes M ∪ betaPrimes L :=
    Or.inr hrBetaL
  have hrProduct :
      r ∣ Nat.card (H.subgroupOf C) * (H.subgroupOf C).index := by
    rw [(H.subgroupOf C).card_mul_index]
    exact hrC
  have hrNotIndex : ¬ r ∣ (H.subgroupOf C).index := by
    intro hrIndex
    exact hHall.isPiNumber_index hrPrime hrIndex hrUnion
  have hrHsub : r ∣ Nat.card (H.subgroupOf C) :=
    (hrPrime.dvd_mul.mp hrProduct).resolve_right hrNotIndex
  have hrH : r ∣ Nat.card H := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hHC] using hrHsub

  /- Fixed-point-free coprime action puts the Sylow subgroup in `M'`.
  Its image in the nilpotent beta quotient is normal, so the Frattini
  argument yields `betaCore M ⊔ N_M(Q) = M`. -/
  have hQM : Q ≤ M :=
    IsSylowSubgroupOf.le_sigmaPartition hQprops.1
  have hQq : IsPGroup q Q := hQprops.1.isPGroup
  have hcopQP : (Nat.card Q).Coprime (Nat.card P) :=
    IsPGroup.coprime_card_of_ne q p hQprops.2.1 Q P
      hQq hP.isPGroup
  letI : Group.IsNilpotent Q := hQq.isNilpotent
  have hQcomm : Q ≤ ⁅P, Q⁆ := by
    have hdecomp : Q ≤ ⁅P, Q⁆ ⊔ centralizerWithin Q P :=
      le_commutator_sup_centralizerWithin_of_coprime hPQ hcopQP
    simpa [hCQ] using hdecomp
  have hQderG : Q ≤ ⁅M, M⁆ :=
    hQcomm.trans (Subgroup.commutator_mono hPM hQM)
  let B0 : Subgroup M := (betaCore M).subgroupOf M
  let D : Subgroup M := _root_.commutator M
  have hB0D : B0 ≤ D := by
    intro x hx
    change (x : G) ∈ betaCore M at hx
    change x ∈ D
    obtain ⟨y, hy, hyx⟩ := Mbeta_der1 hM hx
    have hyx' : y = x := M.subtype_injective hyx
    simpa [hyx'] using hy
  have hB0normal : B0.Normal := by
    simpa only [B0] using betaCore_normal M
  letI : B0.Normal := hB0normal
  have hDnormal : D.Normal := by
    dsimp only [D]
    infer_instance
  letI : D.Normal := hDnormal
  obtain ⟨SM, hQeq⟩ := hQprops.1
  have hSMder : (SM : Subgroup M) ≤ D := by
    apply (Subgroup.map_le_map_iff_of_injective
      M.subtype_injective).mp
    rw [show D.map M.subtype = ⁅M, M⁆ by
      exact M.map_subtype_commutator]
    rw [← hQeq]
    exact hQderG
  let SD : Sylow q D := SM.subtype hSMder
  have hSDmap : (SD : Subgroup D).map D.subtype =
      (SM : Subgroup M) := by
    dsimp only [SD]
    rw [Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le hSMder]
  have hSMsylD : IsSylowSubgroupOf q (SM : Subgroup M) D :=
    ⟨SD, hSDmap.symm⟩
  let N : Subgroup M := B0 ⊔ (SM : Subgroup M)
  have hNnormal : N.Normal := by
    dsimp only [N]
    exact normal_sup_of_sylow_quotient_nilpotent_13_8
      (B := B0) (D := D) (X := (SM : Subgroup M))
      hB0D hSMder hSMsylD (by
        simpa [B0, D] using Mbeta_quo_nil hM)
  letI : N.Normal := hNnormal
  have hSMN : (SM : Subgroup M) ≤ N := by
    dsimp only [N]
    exact le_sup_right
  let SN : Sylow q N := SM.subtype hSMN
  have hSNmap : (SN : Subgroup N).map N.subtype =
      (SM : Subgroup M) := by
    dsimp only [SN]
    rw [Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le hSMN]
  let U : Subgroup M :=
    Subgroup.normalizer ((SM : Subgroup M) : Set M)
  have hUN : U ⊔ N = ⊤ := by
    simpa [U, hSNmap] using SN.normalizer_sup_eq_top
  have hSMU : (SM : Subgroup M) ≤ U := by
    dsimp only [U]
    exact Subgroup.le_normalizer
  have hBU : B0 ⊔ U = ⊤ := by
    apply top_unique
    rw [← hUN]
    apply sup_le
    · exact le_sup_right
    · dsimp only [N]
      exact sup_le le_sup_left (hSMU.trans le_sup_right)
  have hQMsub : Q.subgroupOf M = (SM : Subgroup M) := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hQM, hQeq]
  have hUsub : U =
      (Subgroup.normalizer (Q : Set G)).subgroupOf M := by
    dsimp only [U]
    rw [← hQMsub]
    exact (Subgroup.subgroupOf_normalizer_eq hQM).symm
  have hBmap : B0.map M.subtype = betaCore M := by
    dsimp only [B0]
    exact Subgroup.map_subgroupOf_eq_of_le (betaCore_le M)
  have hUmap : U.map M.subtype =
      M ⊓ Subgroup.normalizer (Q : Set G) := by
    calc
      U.map M.subtype =
          ((Subgroup.normalizer (Q : Set G)).subgroupOf M).map
            M.subtype := by rw [hUsub]
      _ = Subgroup.normalizer (Q : Set G) ⊓ M :=
        Subgroup.subgroupOf_map_subtype
          (Subgroup.normalizer (Q : Set G)) M
      _ = M ⊓ Subgroup.normalizer (Q : Set G) := inf_comm _ _
  have htopMap : (⊤ : Subgroup M).map M.subtype = M := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfactor :
      betaCore M ⊔
          (M ⊓ Subgroup.normalizer (Q : Set G)) = M := by
    calc
      betaCore M ⊔
          (M ⊓ Subgroup.normalizer (Q : Set G)) =
        B0.map M.subtype ⊔ U.map M.subtype := by
          rw [hBmap, hUmap]
      _ = (B0 ⊔ U).map M.subtype :=
        (Subgroup.map_sup B0 U M.subtype).symm
      _ = (⊤ : Subgroup M).map M.subtype := by rw [hBU]
      _ = M := htopMap

  exact ⟨H, X, r, hXne, hXH, hXbeta, hHM, hHC,
    hrBetaL, hrH, hfactor⟩

/-- Close one orientation of the contradiction in Lemma 13.8.

The direct Hall/Fitting reduction above supplies
`Tau1AsymmetryFittingData`.  The corrected invariant-Sylow transfer
constructs the opposite-beta line in `N_M(Q)`; Theorem 13.4 puts its
normalizer in `L`; and the actual beta-quotient commutator theorem finishes
the coprime quotient step. -/
private theorem tau1_asymmetry_oriented_contradiction
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M L P Q : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hL : L ∈ minSimple_max_groups (G := G))
    (hnotLM : ∀ g : G,
      M ≠ L.map (MulAut.conj g).toMonoidHom)
    (hpM : p ∈ tau1Primes M)
    (hpL : p ∈ tau1Primes L)
    (hPM : P ≤ M) (hPL : P ≤ L)
    (hP : IsElementaryAbelianOfRank p 1 P)
    (hQML : Q ≤ M ⊓ L)
    (hNQL : Subgroup.normalizer (Q : Set G) ≤ L)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : centralizerWithin Q P = ⊥)
    (hQprops : Tau1AsymmetrySylowData p q M P Q)
    (hdata : Tau1AsymmetryFittingData M L P Q) :
    False := by
  rcases hdata with
    ⟨H, X, r, hXne, hXH, hXbeta, hHM, hHC,
      hrBetaL, hrH, hfactor⟩
  have hXcentP : X ≤ Subgroup.centralizer (P : Set G) :=
    hXH.trans hHC
  letI : Fact r.Prime := ⟨hrBetaL.1⟩
  have hrNotSigmaM : r ∉ sigmaPrimes M := by
    intro hrSigmaM
    exact Set.disjoint_left.mp
      (sigma_disjoint hL hM hnotLM).2.1
        (beta_sub_alpha L hrBetaL) hrSigmaM
  obtain ⟨R, hRrank, hRle⟩ :=
    exists_rankOne_le_centralizerWithin_inf_normalizer_of_tau1
      hM hL hpM hpL hPM hP hPQ hrBetaL hrNotSigmaM
        hHM hHC hrH hfactor
  have hRcentM : R ≤ centralizerWithin M P :=
    hRle.trans inf_le_left
  have hRNQ : R ≤ Subgroup.normalizer (Q : Set G) :=
    hRle.trans inf_le_right
  have hRM : R ≤ M :=
    hRcentM.trans (centralizerWithin_le_left M P)
  have hRcentP : R ≤ Subgroup.centralizer (P : Set G) :=
    hRcentM.trans inf_le_right
  have hRL : R ≤ L := hRNQ.trans hNQL
  have hNRL : Subgroup.normalizer (R : Set G) ≤ L :=
    beta_norm_sub_mmax hL hRL
      (hRrank.isPGroup.isPiNumber_natCard hrBetaL) hRrank.ne_bot

  have hrp : r ≠ p := by
    intro hrp
    apply hpL.2.1
    rw [← hrp]
    exact beta_sub_sigma hL hrBetaL
  have hdisPR : Disjoint P R :=
    IsPGroup.disjoint_of_ne p r hrp.symm P R
      hP.isPGroup hRrank.isPGroup
  have hPcentR : P ≤ Subgroup.centralizer (R : Set G) :=
    Subgroup.le_centralizer_iff.mp hRcentP
  have hPnormR : P ≤ Subgroup.normalizer (R : Set G) :=
    hPcentR.trans (Subgroup.centralizer_le_normalizer (R : Set G))
  have hPRM : P ⊔ R ≤ M := sup_le hPM hRM
  have hPpi :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card P) :=
    hP.isPGroup.isPiNumber_natCard hpM.2.1
  have hRpi :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card R) :=
    hRrank.isPGroup.isPiNumber_natCard hrNotSigmaM
  have hPRpi :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card (P ⊔ R : Subgroup G)) := by
    rw [natCard_sup_eq_mul_of_disjoint_of_le_normalizer
      hdisPR hPnormR]
    exact hPpi.mul hRpi
  obtain ⟨E, hPRE, hEM, hHallE⟩ :=
    MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
      hPRM (mmax_sol hM) (sigmaPrimes M)ᶜ hPRpi
  have hPE : P ≤ E := le_sup_left.trans hPRE
  have hRE : R ≤ E := le_sup_right.trans hPRE
  have hPline : RankOneLineIn p E P := ⟨hPE, hP⟩
  have hRline : RankOneLineIn r (centralizerWithin E P) R :=
    ⟨le_inf hRE hRcentP, hRrank⟩
  have hcentPR :
      centralizerWithin (sigmaCore M) P ≤
        centralizerWithin (sigmaCore M) R :=
    cent_tau1Elem_Msigma hM hEM hHallE hpM hrBetaL.1
      hPline hRline
  have hXcentSigmaP : X ≤ centralizerWithin (sigmaCore M) P :=
    le_inf (hXbeta.trans (Mbeta_sub_Msigma hM)) hXcentP
  have hXcentR : X ≤ Subgroup.centralizer (R : Set G) :=
    (hXcentSigmaP.trans hcentPR).trans inf_le_right
  have hXL : X ≤ L :=
    (hXcentR.trans
      (Subgroup.centralizer_le_normalizer (R : Set G))).trans hNRL

  have hcommBetaL : ⁅X, Q⁆ ≤ betaCore L :=
    commutator_le_betaCore_of_coprime_regular_action
      hM hL hQprops.2.1.symm hP.isPGroup
        hQprops.1.isPGroup hXbeta hXL hQML hPL hPQ hCQ
          hQprops.2.2.1
  have hMnormBeta :
      M ≤ Subgroup.normalizer (betaCore M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (betaCore_le M)).mp (betaCore_normal M)
  have hQnormBeta :
      Q ≤ Subgroup.normalizer (betaCore M : Set G) :=
    (hQML.trans inf_le_left).trans hMnormBeta
  have hcommBetaM : ⁅X, Q⁆ ≤ betaCore M :=
    (Subgroup.commutator_mono hXbeta le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hQnormBeta)
  have hcommInf :
      ⁅X, Q⁆ ≤ alphaCore L ⊓ sigmaCore M :=
    le_inf
      (hcommBetaL.trans (Mbeta_sub_Malpha L))
      (hcommBetaM.trans (Mbeta_sub_Msigma hM))
  have hcommBot : ⁅X, Q⁆ = ⊥ :=
    le_bot_iff.mp
      (hcommInf.trans_eq (sigma_disjoint hL hM hnotLM).1)
  have hXcentQ : X ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
  have hXcentSup :
      X ≤ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    exact sup_le
      (Subgroup.le_centralizer_iff.mp hXcentP)
      (Subgroup.le_centralizer_iff.mp hXcentQ)
  have hXbad : X ≤ centralizerWithin (betaCore M) (P ⊔ Q) :=
    le_inf hXbeta hXcentSup
  apply hXne
  exact le_bot_iff.mp
    (hXbad.trans_eq hQprops.2.2.2.2)

/-- `BGsection13.v: tau1_mmaxI_asymmetry`, Lemma 13.8.

Two nonconjugate maximal subgroups cannot support the symmetric pair of
fixed-point-free rank-one actions described in the statement. -/
theorem tau1_mmaxI_asymmetry
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M L P Q U : Subgroup G} {p q q_star : ℕ}
    (hq : q.Prime) (hq_star : q_star.Prime)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hL : L ∈ minSimple_max_groups (G := G))
    (hnotconj : ∀ g : G,
      L ≠ M.map (MulAut.conj g).toMonoidHom)
    (hpM : p ∈ tau1Primes M)
    (hpL : p ∈ tau1Primes L)
    (hPML : P ≤ M ⊓ L)
    (hP : IsElementaryAbelianOfRank p 1 P)
    (hQsyl : IsSylowSubgroupOf q Q (M ⊓ L))
    (hUsyl : IsSylowSubgroupOf q_star U (M ⊓ L))
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hCQ : centralizerWithin Q P = ⊥)
    (hCU : centralizerWithin U P = ⊥)
    (hNQL : Subgroup.normalizer (Q : Set G) ≤ L)
    (hNUM : Subgroup.normalizer (U : Set G) ≤ M) :
    False := by
  classical
  letI : Fact p.Prime := ⟨hpM.1⟩
  letI : Fact q.Prime := ⟨hq⟩
  letI : Fact q_star.Prime := ⟨hq_star⟩
  have hPM : P ≤ M := hPML.trans inf_le_left
  have hPL : P ≤ L := hPML.trans inf_le_right
  have hPne : P ≠ ⊥ := hP.ne_bot
  have hQne : Q ≠ ⊥ := ne_bot_of_normalizer_le_mmax hL hNQL
  have hUne : U ≠ ⊥ := ne_bot_of_normalizer_le_mmax hM hNUM
  have hQsylM : IsSylowSubgroupOf q Q M :=
    isSylowSubgroupOf_left_of_inf_of_normalizer_le hQsyl hNQL
  have hUsylL : IsSylowSubgroupOf q_star U L :=
    isSylowSubgroupOf_left_of_inf_of_normalizer_le
      (by simpa [inf_comm] using hUsyl) hNUM
  have hnotconj_symm : ∀ g : G,
      M ≠ L.map (MulAut.conj g).toMonoidHom := by
    intro g hEq
    apply hnotconj g⁻¹
    have hh := congrArg
      (fun K : Subgroup G ↦
        K.map (MulAut.conj g⁻¹).toMonoidHom) hEq
    rw [map_conj_inv_map_conj] at hh
    exact hh.symm
  have hNQnonuniq :
      minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (Q : Set G) : Set G) ≠ {M} := by
    intro huniq
    have hLM : L = M := eq_uniq_mmax huniq hL hNQL
    exact hnotconj 1 (hLM.trans (map_conj_one M).symm)
  have hNUnonuniq :
      minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (U : Set G) : Set G) ≠ {L} := by
    intro huniq
    have hML : M = L := eq_uniq_mmax huniq hM hNUM
    exact hnotconj_symm 1 (hML.trans (map_conj_one L).symm)

  have hqp : q ≠ p :=
    prime_ne_of_centralizerWithin_eq_bot
      hP hQsylM.isPGroup hQne hPQ hCQ
  have hqStarp : q_star ≠ p :=
    prime_ne_of_centralizerWithin_eq_bot
      hP hUsylL.isPGroup hUne hPU hCU
  have hQprops : Tau1AsymmetrySylowData p q M P Q := by
    rcases (cent_Malpha_reg_tau1
      hM hpM hq hqp hPM hP hQne hPQ hCQ hNQnonuniq).2 hQsylM with
      ⟨hAlphaBeta, _hAlphaNe, hqNotAlpha,
        hCentP, hCentQP⟩
    exact ⟨hQsylM, hqp,
      by
        rw [← hAlphaBeta]
        exact hqNotAlpha,
      by simpa [alphaCore, betaCore, hAlphaBeta] using hCentP,
      by simpa [alphaCore, betaCore, hAlphaBeta, sup_comm] using hCentQP⟩
  have hUprops : Tau1AsymmetrySylowData p q_star L P U := by
    rcases (cent_Malpha_reg_tau1
      hL hpL hq_star hqStarp hPL hP hUne hPU hCU hNUnonuniq).2
        hUsylL with
      ⟨hAlphaBeta, _hAlphaNe, hqNotAlpha,
        hCentP, hCentUP⟩
    exact ⟨hUsylL, hqStarp,
      by
        rw [← hAlphaBeta]
        exact hqNotAlpha,
      by simpa [alphaCore, betaCore, hAlphaBeta] using hCentP,
      by simpa [alphaCore, betaCore, hAlphaBeta, sup_comm] using hCentUP⟩

  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let A : Subgroup G := centralizerWithin (betaCore M) P
  have hAC : A ≤ C := inf_le_right
  have hApiM : IsPiNumber (betaPrimes M) (Nat.card A) :=
    (betaCore_isPiNumber M).of_dvd
      (Subgroup.card_dvd_of_le (centralizerWithin_le_left _ _))
  have hApi : IsPiNumber (betaPrimes M ∪ betaPrimes L) (Nat.card A) :=
    hApiM.mono Set.subset_union_left
  have hCsol : IsSolvable C := mFT_sol (mFT_cent_proper P hPne)
  obtain ⟨H, hAH, hHC, hHall⟩ :=
    MathlibSupport.exists_ambient_isHall_ge_of_isSolvable hAC hCsol
      (betaPrimes M ∪ betaPrimes L) hApi
  have hAne : A ≠ ⊥ := hQprops.2.2.2.1
  have hHne : H ≠ ⊥ := fun hHbot ↦
    hAne (le_bot_iff.mp (hAH.trans_eq hHbot))
  have hHsol : IsSolvable H := by
    letI : IsSolvable C := hCsol
    exact isSolvable_of_injective (Subgroup.inclusion hHC)
      (Subgroup.inclusion_injective hHC)
  have hFne : fittingWithin H ≠ ⊥ := by
    intro hFbot
    exact hHne
      (Section08.eq_bot_of_fittingWithin_eq_bot_of_isSolvable
        H hHsol hFbot)
  have hFcard : Nat.card (fittingWithin H) ≠ 1 :=
    fun hc ↦ hFne (Subgroup.card_eq_one.mp hc)
  obtain ⟨s, hsPrime, hsF⟩ := Nat.exists_prime_and_dvd hFcard
  letI : Fact s.Prime := ⟨hsPrime⟩
  have hsH : s ∣ Nat.card H :=
    hsF.trans (Subgroup.card_dvd_of_le (fittingWithin_le H))
  have hsSub : s ∣ Nat.card (H.subgroupOf C) := by
    simpa [MathlibSupport.natCard_subgroupOf_eq hHC] using hsH
  have hsUnion : s ∈ betaPrimes M ∪ betaPrimes L :=
    hHall.isPiNumber_card hsPrime hsSub
  rcases hsUnion with hsBetaM | hsBetaL
  · have hdata : Tau1AsymmetryFittingData M L P Q :=
      tau1_asymmetry_fitting_data
        hM hPM hP hPQ hCQ hQprops hUprops.2.2.2.1
          hHC hHall hAH hsF hsBetaM
    exact tau1_asymmetry_oriented_contradiction
      hM hL hnotconj_symm hpM hpL hPM hPL hP
        (IsSylowSubgroupOf.le_sigmaPartition hQsyl)
          hNQL hPQ hCQ hQprops hdata
  · let AL : Subgroup G := centralizerWithin (betaCore L) P
    have hALC : AL ≤ C := by
      dsimp only [AL, C]
      exact inf_le_right
    have hALpiL : IsPiNumber (betaPrimes L) (Nat.card AL) :=
      (betaCore_isPiNumber L).of_dvd
        (Subgroup.card_dvd_of_le
          (centralizerWithin_le_left (betaCore L) P))
    have hALpi :
        IsPiNumber (betaPrimes M ∪ betaPrimes L) (Nat.card AL) :=
      hALpiL.mono Set.subset_union_right
    obtain ⟨x, hALH', hH'C, hHall', _hfit, hdiv, _htransport⟩ :=
      exists_ambient_isHall_map_conj_ge_of_isSolvable
        (K := C) (A := AL) (H := H)
        hALC hHC hCsol hALpi hHall
    let H' : Subgroup G :=
      H.map (MulAut.conj (x : G)).toMonoidHom
    change AL ≤ H' at hALH'
    change H' ≤ C at hH'C
    change IsHall (betaPrimes M ∪ betaPrimes L)
      (H'.subgroupOf C) at hHall'
    change ∀ n : ℕ,
      n ∣ Nat.card (fittingWithin H') ↔
        n ∣ Nat.card (fittingWithin H) at hdiv
    have hHallSwap :
        IsHall (betaPrimes L ∪ betaPrimes M) (H'.subgroupOf C) := by
      simpa only [Set.union_comm] using hHall'
    have hsF' : s ∣ Nat.card (fittingWithin H') :=
      (hdiv s).2 hsF
    have hdata : Tau1AsymmetryFittingData L M P U :=
      tau1_asymmetry_fitting_data
        hL hPL hP hPU hCU hUprops hQprops.2.2.2.1
          hH'C hHallSwap hALH' hsF' hsBetaL
    exact tau1_asymmetry_oriented_contradiction
      hL hM hnotconj hpL hpM hPL hPM hP
        (by simpa [inf_comm] using
          (IsSylowSubgroupOf.le_sigmaPartition hUsyl))
          hNUM hPU hCU
          hUprops hdata

/-- `BGsection13.v: sigma_partition`, Theorem 13.9. -/
theorem sigma_partition
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M L : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hL : L ∈ minSimple_max_groups (G := G))
    (hnotconj : ∀ g : G,
      L ≠ M.map (MulAut.conj g).toMonoidHom) :
    Disjoint (sigmaPrimes M) (sigmaPrimes L) := by
  classical
  rw [Set.disjoint_left]
  intro q hqM hqL
  letI : Fact q.Prime := ⟨hqM.1⟩

  obtain ⟨E, hEM, hHallE⟩ := ex_sigma_compl hM
  have hEnormSigma :
      E ≤ Subgroup.normalizer (sigmaCore M : Set G) := by
    apply hEM.trans
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (sigmaCore_le M)).mp (sigmaCore_normal M)
  have hsolSigma : IsSolvable (sigmaCore M) := by
    letI : IsSolvable M := mmax_sol hM
    exact isSolvable_of_injective
      (Subgroup.inclusion (sigmaCore_le M))
      (Subgroup.inclusion_injective (sigmaCore_le M))
  obtain ⟨Sσ, hESσ⟩ :=
    exists_sylow_normalized_of_coprime_of_isSolvable
      (p := q) hEnormSigma
      (coprime_sigma_compl hEM hHallE) hsolSigma
  obtain ⟨S, hS⟩ :=
    exists_sylow_eq_map_of_sylow_hall hqM.1
      (Msigma_Hall_G hM) hqM Sσ
  have hSsigma : (S : Subgroup G) ≤ sigmaCore M := by
    rw [hS]
    exact Subgroup.map_subtype_le (Sσ : Subgroup (sigmaCore M))
  have hES :
      E ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    rw [hS]
    exact hESσ

  let TL : Sylow q L := Classical.choice Sylow.nonempty
  obtain ⟨T, hT⟩ := sigma_Sylow_G hL hqL TL
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hTS :
      (T : Subgroup G).map (MulAut.conj g).toMonoidHom =
        (S : Subgroup G) := by
    change MulAut.conj g • (T : Subgroup G) = (S : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hg]
  have hTL : (T : Subgroup G) ≤ L := by
    rw [hT]
    exact Subgroup.map_subtype_le (TL : Subgroup L)
  let K : Subgroup G := L.map (MulAut.conj g).toMonoidHom
  have hSK : (S : Subgroup G) ≤ K := by
    have hmapped := Subgroup.map_mono hTL
      (f := (MulAut.conj g).toMonoidHom)
    rwa [hTS] at hmapped
  have hK : K ∈ minSimple_max_groups (G := G) :=
    (mmaxJ L (MulAut.conj g)).mpr hL
  have hqK : q ∈ sigmaPrimes K := by
    change q ∈ sigmaPrimes
      (L.map (MulAut.conj g).toMonoidHom)
    rw [sigmaPrimes_conj L g]
    exact hqL
  have hnotK : ∀ z : G,
      K ≠ M.map (MulAut.conj z).toMonoidHom := by
    intro z hEq
    apply hnotconj (g⁻¹ * z)
    have hback := congrArg
      (fun H : Subgroup G ↦
        H.map (MulAut.conj g⁻¹).toMonoidHom) hEq
    change
      (L.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj g⁻¹).toMonoidHom =
        (M.map (MulAut.conj z).toMonoidHom).map
          (MulAut.conj g⁻¹).toMonoidHom at hback
    rw [map_conj_inv_map_conj, map_conj_map_conj] at hback
    exact hback

  have hSM : (S : Subgroup G) ≤ M :=
    hSsigma.trans (sigmaCore_le M)
  let SM : Sylow q M := S.subtype hSM
  let SK : Sylow q K := S.subtype hSK
  have hSMambient : ambientSylow M SM = (S : Subgroup G) := by
    change ((S : Subgroup G).subgroupOf M).map M.subtype =
      (S : Subgroup G)
    exact Subgroup.map_subgroupOf_eq_of_le hSM
  have hSKambient : ambientSylow K SK = (S : Subgroup G) := by
    change ((S : Subgroup G).subgroupOf K).map K.subtype =
      (S : Subgroup G)
    exact Subgroup.map_subgroupOf_eq_of_le hSK
  have hNSM :
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M := by
    have h := norm_sigma_Sylow hqM SM
    rwa [hSMambient] at h
  have hNSK :
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ K := by
    have h := norm_sigma_Sylow hqK SK
    rwa [hSKambient] at h
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    have h := sigma_Sylow_neq_bot hM hqM SM
    rwa [hSMambient] at h

  obtain ⟨⟨E₁, hE₁E, hHallE₁⟩,
      ⟨E₃, hE₃E, hHallE₃⟩⟩ :=
    ex_tau13_compl hEM hHallE
  obtain ⟨E₂, hE₂E, hHallE₂, hcompl⟩ :=
    ex_tau2_compl hEM hHallE
      hE₁E hHallE₁ hE₃E hHallE₃
  have hE₂bot : E₂ = ⊥ := by
    by_contra hE₂ne
    have hcardNe : Nat.card E₂ ≠ 1 :=
      fun hc ↦ hE₂ne (Subgroup.card_eq_one.mp hc)
    obtain ⟨r, hr, hrE₂⟩ := Nat.exists_prime_and_dvd hcardNe
    letI : Fact r.Prime := ⟨hr⟩
    have hrSub : r ∣ Nat.card (E₂.subgroupOf E) := by
      rw [MathlibSupport.natCard_subgroupOf_eq hE₂E]
      exact hrE₂
    have hrTau : r ∈ tau2Primes M :=
      hHallE₂.isPiNumber_card hr hrSub
    obtain ⟨A₂, hA₂E, _, hA₂⟩ :=
      ex_tau2Elem hEM hHallE hrTau
    have hA₂K : A₂ ≤ K :=
      (hA₂E.trans hES).trans hNSK
    have hKneM : K ≠ M := by
      intro hKM
      exact hnotK 1 (hKM.trans (map_conj_one M).symm)
    have hIntBot : sigmaCore M ⊓ K = ⊥ :=
      (tau2_context hM hrTau (hA₂E.trans hEM) hA₂).maximal_intersection_eq_bot
        ⟨hK, hA₂K⟩ hKneM
    apply hSne
    apply le_bot_iff.mp
    rw [← hIntBot]
    exact le_inf hSsigma hSK
  have hE₁ne : E₁ ≠ ⊥ :=
    (sigma_compl_context hM hcompl).E₂_eq_bot_imp_E₁_ne_bot hE₂bot
  have hE₁cardNe : Nat.card E₁ ≠ 1 :=
    fun hc ↦ hE₁ne (Subgroup.card_eq_one.mp hc)
  obtain ⟨p, hp, hpE₁⟩ := Nat.exists_prime_and_dvd hE₁cardNe
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPE₁, hP⟩ :=
    exists_rankOne_le_of_prime_dvd_natCard hpE₁
  have hpTauM : p ∈ tau1Primes M := by
    apply hHallE₁.isPiNumber_card hp
    rw [MathlibSupport.natCard_subgroupOf_eq hE₁E]
    exact hpE₁
  have hPne : P ≠ ⊥ := hP.ne_bot
  have hPE : P ≤ E := hPE₁.trans hE₁E
  have hPM : P ≤ M := hPE.trans hEM
  have hPS :
      P ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    hPE.trans hES
  have hPK : P ≤ K := hPS.trans hNSK
  have hPMK : P ≤ M ⊓ K := le_inf hPM hPK
  have hSMK : (S : Subgroup G) ≤ M ⊓ K := le_inf hSM hSK
  have hSsyl :
      IsSylowSubgroupOf q (S : Subgroup G) (M ⊓ K) := by
    exact ⟨S.subtype hSMK, by
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSMK]⟩

  have hreg : centralizerWithin (S : Subgroup G) P = ⊥ := by
    by_contra hCne
    let C₀ : Subgroup G := centralizerWithin (S : Subgroup G) P
    have hCq : IsPGroup q C₀ :=
      S.isPGroup'.to_le
        (centralizerWithin_le_left (S : Subgroup G) P)
    have hCcardNe : Nat.card C₀ ≠ 1 :=
      fun hc ↦ hCne (Subgroup.card_eq_one.mp hc)
    have hqC : q ∣ Nat.card C₀ :=
      hCq.card_eq_or_dvd.resolve_left hCcardNe
    obtain ⟨X, hXC, hX⟩ :=
      exists_rankOne_le_of_prime_dvd_natCard hqC
    have hXcent : X ≤ centralizerWithin (sigmaCore M) P :=
      hXC.trans (centralizerWithin_mono_left hSsigma)
    have huniq := cent_cent_Msigma_tau1_uniq
      hM hEM hHallE hE₁E hHallE₁
        hPE₁ hPne hXcent hX
    let Cσ : Subgroup M := (sigmaCore M).subgroupOf M
    let eσ : sigmaCore M ≃* Cσ :=
      (Subgroup.subgroupOfEquivOfLe (sigmaCore_le M)).symm
    let SσM : Sylow q Cσ :=
      Sσ.mapSurjective (f := eσ.toMonoidHom) eσ.surjective
    have hSσMambient :
        (((SσM : Subgroup Cσ).map Cσ.subtype).map M.subtype :
          Subgroup G) =
        (Sσ : Subgroup (sigmaCore M)).map (sigmaCore M).subtype := by
      change
        ((((Sσ.mapSurjective (f := eσ.toMonoidHom) eσ.surjective :
            Sylow q Cσ) : Subgroup Cσ).map Cσ.subtype).map
              M.subtype : Subgroup G) =
          (Sσ : Subgroup (sigmaCore M)).map (sigmaCore M).subtype
      rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
      apply congrArg
        (fun f : sigmaCore M →* G ↦
          (Sσ : Subgroup (sigmaCore M)).map f)
      ext x
      rfl
    have huniqRestricted := huniq.2 SσM
    have huniqS :
        minSimple_max_groups_of (G := G)
          ((S : Subgroup G) : Set G) = {M} := by
      rw [hSσMambient, ← hS] at huniqRestricted
      exact huniqRestricted
    have hKM : K = M := eq_uniq_mmax huniqS hK hSK
    exact hnotK 1 (hKM.trans (map_conj_one M).symm)

  have hPnotcent :
      ¬ P ≤ Subgroup.centralizer
        ((sigmaCore M ⊓ K : Subgroup G) : Set G) := by
    intro hPcent
    have hSint : (S : Subgroup G) ≤ sigmaCore M ⊓ K :=
      le_inf hSsigma hSK
    have hcentEq :
        centralizerWithin (S : Subgroup G) P = (S : Subgroup G) := by
      apply le_antisymm
        (centralizerWithin_le_left (S : Subgroup G) P)
      intro s hs
      exact ⟨hs, by
        intro x hx
        exact (Subgroup.mem_centralizer_iff.mp
          (hPcent hx) s (hSint hs)).symm⟩
    exact hSne (hcentEq.symm.trans hreg)

  have hpTauK : p ∈ tau1Primes K := by
    by_contra hpNotTauK
    have hpP : p ∣ Nat.card P := by
      rw [hP.card_eq, pow_one]
    have hpE : p ∈ primeSupport (Nat.card E) :=
      ⟨hp, hpP.trans (Subgroup.card_dvd_of_le hPE)⟩
    have hpK : p ∈ primeSupport (Nat.card K) :=
      ⟨hp, hpP.trans (Subgroup.card_dvd_of_le hPK)⟩
    have hcomm : ⁅sigmaCore M ⊓ K, M ⊓ K⁆ ≠ ⊥ := by
      intro hcommBot
      apply hPnotcent
      have hswap : ⁅M ⊓ K, sigmaCore M ⊓ K⁆ = ⊥ := by
        calc
          ⁅M ⊓ K, sigmaCore M ⊓ K⁆ =
              ⁅sigmaCore M ⊓ K, M ⊓ K⁆ :=
            Subgroup.commutator_comm _ _
          _ = ⊥ := hcommBot
      exact hPMK.trans
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hswap)
    have hcentral :=
      (Msigma_setI_mmax_central
        hM hEM hHallE hK hpE hpK hpNotTauK hcomm hnotK).1
          P hPMK hP.isPGroup
    exact hPnotcent hcentral

  exact tau1_mmaxI_asymmetry
    hqM.1 hqM.1 hM hK hnotK
    hpTauM hpTauK hPMK hP
    hSsyl hSsyl hPS hPS hreg hreg hNSK hNSM

end

end Submission.OddOrder.BG.Section13
