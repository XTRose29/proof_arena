import Submission.OddOrder.BG.Section03.SemiregularConjugation
import Submission.OddOrder.BG.Section12.AbelianTau2
import Submission.OddOrder.BG.Section12.SigmaComplementContext
import Submission.OddOrder.BG.Section12.NonabelianUniqueness
import Submission.OddOrder.BG.Section12.SigmaEmbedding
import Submission.OddOrder.BG.Section12.Tau2CoprimeCyclicSplit
import Submission.OddOrder.MathlibSupport.CoprimeSolvableCentralProduct
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowConjugacy
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension
import Submission.OddOrder.MathlibSupport.PPrimeFactorIntersection
import Submission.OddOrder.MathlibSupport.SolvableHallConjugacyTransport

/-!
# Bender--Glauberman Section 13: prime actions on the sigma core

This file ports `BGsection13.v`, lines 1--575: Lemma 13.1,
Corollaries 13.2 and 13.3, Theorems 13.4 and 13.5, and Lemmas 13.6
and 13.7.

MathComp's `semiprime K A` says that all nontrivial subgroups of the actor
`A` have the same centralizer in `K`.  This is a prime action, and is
strictly weaker than the fixed-point-free property called `semiregular` in
the source.  We record that predicate explicitly below because both notions
are used later in Section 13.

The Coq development includes containment in its Hall predicate.  Lean's
`IsHall` is applied to `subgroupOf`, so the ambient containments are recorded
separately.  The local adapters below are proposition-free translations of
the generic quotient, Sylow, and coprime-commutator steps used by the source;
the eight public results therefore have exactly their mathematical
hypotheses, with no Section-13 proof records in their interfaces.
-/

namespace Submission.OddOrder.BG.Section13

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

/-- MathComp's `semiprime K A`: every nontrivial subgroup of the actor
has the same centralizer in the acted-on subgroup. -/
def IsPrimeAction
    {G : Type u} [Group G] (K A : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ A → X ≠ ⊥ →
    centralizerWithin K X = centralizerWithin K A

namespace IsPrimeAction

/-- Source lemma `cent_semiprime`. -/
theorem centralizer_eq
    {G : Type u} [Group G] {K A X : Subgroup G}
    (h : IsPrimeAction K A) (hXA : X ≤ A) (hX : X ≠ ⊥) :
    centralizerWithin K X = centralizerWithin K A :=
  h X hXA hX

/-- A prime action restricts on the acted-on subgroup. -/
theorem mono_left
    {G : Type u} [Group G] {K L A : Subgroup G}
    (hLK : L ≤ K) (h : IsPrimeAction K A) :
    IsPrimeAction L A := by
  intro X hXA hX
  have hK := h.centralizer_eq hXA hX
  change L ⊓ Subgroup.centralizer (X : Set G) =
    L ⊓ Subgroup.centralizer (A : Set G)
  have hcent : Subgroup.centralizer (X : Set G) ⊓ K =
      Subgroup.centralizer (A : Set G) ⊓ K := by
    simpa [centralizerWithin, inf_comm] using hK
  apply le_antisymm
  · intro x hx
    have hxK : x ∈ K := hLK hx.1
    have hx' : x ∈ Subgroup.centralizer (X : Set G) ⊓ K :=
      ⟨hx.2, hxK⟩
    have hxA := hcent.le hx'
    exact ⟨hx.1, hxA.1⟩
  · intro x hx
    have hxK : x ∈ K := hLK hx.1
    have hx' : x ∈ Subgroup.centralizer (A : Set G) ⊓ K :=
      ⟨hx.2, hxK⟩
    have hxX := hcent.ge hx'
    exact ⟨hx.1, hxX.1⟩

end IsPrimeAction

/-- Source-name alias for the centralizer characterization of a prime
action. -/
theorem cent_semiprime
    {G : Type u} [Group G] {K A X : Subgroup G}
    (h : IsPrimeAction K A) (hXA : X ≤ A) (hX : X ≠ ⊥) :
    centralizerWithin K X = centralizerWithin K A :=
  h.centralizer_eq hXA hX

/-! ## Local finite-group adapters -/

/-- The quotient of a subgroup by the restriction of an ambient normal
subgroup is its image in the ambient quotient. -/
private def subgroupQuotientEquivImage13
    {K : Type u} [Group K] (B D : Subgroup K) [B.Normal] :
    (D ⧸ B.subgroupOf D) ≃* D.map (QuotientGroup.mk' B) := by
  letI : (B.subgroupOf D).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : B.Normal) D
  exact QuotientGroup.liftEquiv (B.subgroupOf D)
    ((QuotientGroup.mk' B).subgroupMap_surjective D) (by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])

/-- Frattini's argument in the nilpotent quotient: adjoining a Sylow
subgroup to the quotient kernel gives a normal subgroup. -/
private theorem normal_sup_of_sylow_quotient_nilpotent13
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
      Group.nilpotent_of_mulEquiv (subgroupQuotientEquivImage13 B D)
  obtain ⟨Q, hXQ⟩ := hX
  let Qbar : Sylow q Dbar :=
    Q.mapSurjective (pi.subgroupMap_surjective D)
  have hXmap :
      X.map pi = (Qbar : Subgroup Dbar).map Dbar.subtype := by
    rw [hXQ]
    change
      ((Q : Subgroup D).map D.subtype).map pi =
        ((Q.mapSurjective (pi.subgroupMap_surjective D) :
          Sylow q Dbar) : Subgroup Dbar).map Dbar.subtype
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    apply congrArg (fun f : D →* K ⧸ B ↦ (Q : Subgroup D).map f)
    ext d
    rfl
  have hQcore : (Qbar : Subgroup Dbar) = pCore q Dbar :=
    (pCore_eq_sylow_of_isNilpotent Qbar).symm
  have hmapNormal : (X.map pi).Normal := by
    rw [hXmap, hQcore]
    infer_instance
  have hcomapNormal : ((X.map pi).comap pi).Normal :=
    hmapNormal.comap pi
  simpa [pi, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
    using hcomapNormal

/-- Quotient form of MathComp's `coprime_TIg`: modulo `S`, the normal
subgroup `S ⊔ B` is a `p`-group, so a normalized `p'`-subgroup meets it
inside `S`. -/
private theorem commutator_le_inf_of_normal_sup_of_coprime13
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {H S A B K : Subgroup G}
    (hSH : S ≤ H) (_hAH : A ≤ H) (hBH : B ≤ H)
    (hAB : A ≤ B) (hKH : K ≤ H)
    (hSnormal : (S.subgroupOf H).Normal)
    (hSBnormal : ((S ⊔ B).subgroupOf H).Normal)
    (hAnormK : A ≤ Subgroup.normalizer (K : Set G))
    (hBp : IsPGroup p B) (hKp' : IsPPrimeSubgroup p K) :
    ⁅K, A⁆ ≤ K ⊓ S := by
  let SH : Subgroup H := S.subgroupOf H
  let BH : Subgroup H := B.subgroupOf H
  let KH : Subgroup H := K.subgroupOf H
  let U : Subgroup H := (S ⊔ B).subgroupOf H
  letI : SH.Normal := by simpa [SH] using hSnormal
  let pi : H →* H ⧸ SH := QuotientGroup.mk' SH
  have hBHp : IsPGroup p BH := by
    let eBH : BH ≃* B := Subgroup.subgroupOfEquivOfLe hBH
    exact hBp.of_equiv eBH.symm
  have hUeq : U = SH ⊔ BH := by
    dsimp [U, SH, BH]
    exact Subgroup.subgroupOf_sup hSH hBH
  have hSHmap : SH.map pi = ⊥ := by
    apply (Subgroup.map_eq_bot_iff SH).mpr
    simp [pi, QuotientGroup.ker_mk']
  have hfactor : IsPGroup p (U.map pi) := by
    rw [hUeq, Subgroup.map_sup, hSHmap, bot_sup_eq]
    exact hBHp.map pi
  have hKHp' : IsPPrimeSubgroup p KH := by
    change Nat.Coprime p (Nat.card KH)
    rw [MathlibSupport.natCard_subgroupOf_eq hKH]
    exact hKp'
  have hinf : KH ⊓ U ≤ SH :=
    inf_le_of_isPPrimeSubgroup_of_factor_isPGroup hKHp' hfactor
  have hcommK : ⁅K, A⁆ ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hAnormK
  have hHnormSB : H ≤ Subgroup.normalizer ((S ⊔ B : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hSH hBH)).mp
      hSBnormal
  have hcommSB : ⁅K, A⁆ ≤ S ⊔ B :=
    (Subgroup.commutator_mono le_rfl (hAB.trans le_sup_right)).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hKH.trans hHnormSB))
  intro x hx
  have hxH : x ∈ H := hKH (hcommK hx)
  let xH : H := ⟨x, hxH⟩
  have hxinf : xH ∈ KH ⊓ U := ⟨hcommK hx, hcommSB hx⟩
  exact ⟨hcommK hx, hinf hxinf⟩

/-- Move an elementary-abelian rank witness into a prescribed ambient
Sylow subgroup. -/
private theorem exists_elementaryAbelian_le_ambientSylow13
    {G : Type u} [Group G] [Finite G]
    {H Q : Subgroup G} {p n : ℕ} [Fact p.Prime]
    (hQH : IsSylowSubgroupOf p Q H)
    (hRank : HasElementaryAbelianRankAtLeast p n H) :
    ∃ A : Subgroup G, A ≤ Q ∧
      IsElementaryAbelianOfRank p n A := by
  classical
  rcases hQH with ⟨P, hQP⟩
  rcases hRank with ⟨A, hAH, hA⟩
  let AH : Subgroup H := A.subgroupOf H
  have hAHrank : IsElementaryAbelianOfRank p n AH := hA.subgroupOf hAH
  obtain ⟨R, hAHR⟩ := hAHrank.isPGroup.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H R P
  let B : Subgroup H := AH.map (MulAut.conj h).toMonoidHom
  have hRB :
      (R : Subgroup H).map (MulAut.conj h).toMonoidHom =
        (P : Subgroup H) := by
    change MulAut.conj h • (R : Subgroup H) = (P : Subgroup H)
    rw [← Sylow.coe_subgroup_smul, hh]
  have hBP : B ≤ (P : Subgroup H) :=
    (Subgroup.map_mono hAHR).trans_eq hRB
  let BG : Subgroup G := B.map H.subtype
  exact ⟨BG, by
    rw [hQP]
    exact Subgroup.map_mono hBP, by
    exact
      (hAHrank.map_of_injective (MulAut.conj h).toMonoidHom
        (MulAut.conj h).injective).map_of_injective
          H.subtype H.subtype_injective⟩

/-- A Sylow subgroup of the second factor in a normal product is still
Sylow in the whole group at primes absent from the normal factor. -/
private theorem isSylowSubgroupOf_map_of_normal_sup13
    {G : Type u} [Group G] [Finite G]
    {H N I : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hNH : N ≤ H) (hIH : I ≤ H)
    (hNnormal : (N.subgroupOf H).Normal)
    (hsup : N ⊔ I = H)
    (hpN : ¬ p ∣ Nat.card N) (R : Sylow p I) :
    IsSylowSubgroupOf p
      ((R : Subgroup I).map I.subtype) H := by
  let NH : Subgroup H := N.subgroupOf H
  let IH : Subgroup H := I.subgroupOf H
  let Q : Subgroup G := (R : Subgroup I).map I.subtype
  have hQI : Q ≤ I :=
    Subgroup.map_subtype_le (R : Subgroup I)
  have hQH : Q ≤ H := hQI.trans hIH
  have hsupH : NH ⊔ IH = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hNH,
      Subgroup.map_subgroupOf_eq_of_le hIH, hsup,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hpIHindex : ¬ p ∣ IH.index := by
    intro hpIndex
    apply hpN
    have hindexDvd : IH.index ∣ Nat.card NH := by
      letI : NH.Normal := hNnormal
      let J : Subgroup IH := (NH ⊓ IH).subgroupOf IH
      have hNindex : NH.index = J.index := by
        calc
          NH.index = NH.relIndex (⊤ : Subgroup H) :=
            NH.relIndex_top_right.symm
          _ = NH.relIndex (IH ⊔ NH) := by rw [sup_comm, hsupH]
          _ = NH.relIndex IH := Subgroup.relIndex_sup_right IH NH
          _ = (NH ⊓ IH).relIndex IH :=
            (Subgroup.inf_relIndex_right NH IH).symm
          _ = J.index := by rfl
      have hNcard : Nat.card NH * J.index = Nat.card H := by
        rw [← hNindex]
        exact NH.card_mul_index
      have hIcard : Nat.card IH * IH.index = Nat.card H :=
        IH.card_mul_index
      have hJcard : Nat.card J * J.index = Nat.card IH :=
        J.card_mul_index
      have hcancel :
          Nat.card NH * J.index =
            (Nat.card J * IH.index) * J.index := by
        calc
          Nat.card NH * J.index = Nat.card H := hNcard
          _ = Nat.card IH * IH.index := hIcard.symm
          _ = (Nat.card J * J.index) * IH.index := by rw [hJcard]
          _ = (Nat.card J * IH.index) * J.index := by ac_rfl
      have hcard : Nat.card NH = Nat.card J * IH.index :=
        Nat.mul_right_cancel
          (Nat.pos_of_ne_zero J.index_ne_zero_of_finite) hcancel
      exact ⟨Nat.card J, by simpa [mul_comm] using hcard⟩
    have hpNH : p ∣ Nat.card NH := hpIndex.trans hindexDvd
    rw [MathlibSupport.natCard_subgroupOf_eq hNH] at hpNH
    exact hpNH
  let QH : Subgroup H := Q.subgroupOf H
  let QI : Subgroup I := Q.subgroupOf I
  have hQIeq : QI = (R : Subgroup I) := by
    dsimp [QI, Q]
    exact Subgroup.comap_map_eq_self_of_injective I.subtype_injective R
  have hQHp : IsPGroup p QH :=
    (R.isPGroup'.map I.subtype).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hpQHindex : ¬ p ∣ QH.index := by
    have hfactor : QH.index = QI.index * IH.index := by
      change Q.relIndex H = Q.relIndex I * I.relIndex H
      exact (Q.relIndex_mul_relIndex I H hQI hIH).symm
    rw [hfactor, hQIeq]
    exact (Fact.out : p.Prime).not_dvd_mul R.not_dvd_index hpIHindex
  exact ⟨hQHp.toSylow hpQHindex,
    (Subgroup.map_subgroupOf_eq_of_le hQH).symm⟩

/-- MathComp's `Sylow_gen`, in the eliminator form used below. -/
private theorem le_of_sylow_le13
    {G : Type u} [Group G] [Finite G] {X K : Subgroup G}
    (h : ∀ {q : ℕ}, q ∈ primeSupport (Nat.card X) →
      ∀ Q : Sylow q X,
        ((Q : Subgroup X).map X.subtype : Subgroup G) ≤ K) :
    X ≤ K := by
  let L : Subgroup X := K.comap X.subtype
  have hLtop : L = ⊤ := by
    apply Subgroup.index_eq_one.mp
    by_contra hindex
    have hindexGt : 1 < L.index :=
      (Nat.one_lt_iff_ne_zero_and_ne_one.mpr
        ⟨L.index_ne_zero_of_finite, hindex⟩)
    obtain ⟨q, hq, hqIndex⟩ :=
      Nat.exists_prime_and_dvd hindexGt.ne'
    letI : Fact q.Prime := ⟨hq⟩
    let Q : Sylow q X := default
    have hqX : q ∈ primeSupport (Nat.card X) :=
      ⟨hq, hqIndex.trans L.index_dvd_card⟩
    have hQK := h hqX Q
    have hQL : (Q : Subgroup X) ≤ L := by
      intro x hx
      exact hQK (Subgroup.mem_map_of_mem X.subtype hx)
    have hfactor : (Q : Subgroup X).index =
        (Q : Subgroup X).relIndex L * L.index :=
      ((Q : Subgroup X).relIndex_mul_index hQL).symm
    exact Q.not_dvd_index (hfactor ▸ dvd_mul_of_dvd_right hqIndex _)
  intro x hx
  let xX : X := ⟨x, hx⟩
  have hxL : xX ∈ L := by rw [hLtop]; trivial
  exact hxL

/-- MathComp's `Sylow_transversal_gen`, in the eliminator form needed in
Theorem 13.4: a solvable group acted on coprimely is generated by its
actor-invariant Sylow subgroups. -/
private theorem le_of_normalized_sylow_le13
    {G : Type u} [Group G] [Finite G] {A L K : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hcop : (Nat.card L).Coprime (Nat.card A))
    (hsol : IsSolvable L)
    (h : ∀ {p : ℕ}, p ∈ primeSupport (Nat.card L) →
      ∀ P : Sylow p L,
        A ≤ Subgroup.normalizer
          (((P : Subgroup L).map L.subtype : Subgroup G) : Set G) →
        ((P : Subgroup L).map L.subtype : Subgroup G) ≤ K) :
    L ≤ K := by
  classical
  let H : Subgroup L := K.comap L.subtype
  have hHtop : H = ⊤ := by
    apply Subgroup.index_eq_one.mp
    by_contra hindex
    have hindexGt : 1 < H.index :=
      Nat.one_lt_iff_ne_zero_and_ne_one.mpr
        ⟨H.index_ne_zero_of_finite, hindex⟩
    obtain ⟨p, hp, hpIndex⟩ :=
      Nat.exists_prime_and_dvd hindexGt.ne'
    letI : Fact p.Prime := ⟨hp⟩
    have hpL : p ∈ primeSupport (Nat.card L) :=
      ⟨hp, hpIndex.trans H.index_dvd_card⟩
    obtain ⟨P, hAP⟩ :=
      exists_sylow_normalized_of_coprime_of_isSolvable
        (p := p) hAL hcop hsol
    have hPK :
        ((P : Subgroup L).map L.subtype : Subgroup G) ≤ K :=
      h hpL P hAP
    have hPH : (P : Subgroup L) ≤ H := by
      intro x hx
      exact hPK (Subgroup.mem_map_of_mem L.subtype hx)
    exact P.not_dvd_index
      (hpIndex.trans (Subgroup.index_dvd_of_le hPH))
  intro x hx
  let xL : L := ⟨x, hx⟩
  have hxH : xL ∈ H := by
    rw [hHtop]
    trivial
  exact hxH

/-- Centralization is symmetric, in subgroup-containment form. -/
private theorem centralizer_le_symm13
    {G : Type u} [Group G] {A B : Subgroup G}
    (h : A ≤ Subgroup.centralizer (B : Set G)) :
    B ≤ Subgroup.centralizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (h ha) b hb).symm

/-- An elementwise centralizer of both factors centralizes their join. -/
private theorem le_centralizer_sup13
    {G : Type u} [Group G] {X A B : Subgroup G}
    (hA : X ≤ Subgroup.centralizer (A : Set G))
    (hB : X ≤ Subgroup.centralizer (B : Set G)) :
    X ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Subgroup.sup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with hy | hy
      · exact Subgroup.mem_centralizer_iff.mp (hA hx) y hy
      · exact Subgroup.mem_centralizer_iff.mp (hB hx) y hy
  | one => simp
  | mul a b _ _ ha hb =>
      calc
        (a * b) * x = a * (b * x) := by simp [mul_assoc]
        _ = a * (x * b) := by rw [hb]
        _ = (a * x) * b := by simp [mul_assoc]
        _ = (x * a) * b := by rw [ha]
        _ = x * (a * b) := by simp [mul_assoc]
  | inv a _ ha =>
      exact (show Commute a⁻¹ x from
        (show Commute a x from ha).inv_left).eq

/-- Restrict a Hall subgroup to an intermediate subgroup containing it. -/
private theorem isHall_subgroupOf_intermediate13
    {G : Type u} [Group G] [Finite G]
    {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    {pi : Set ℕ} (hA : IsHall pi (A.subgroupOf C)) :
    IsHall pi (A.subgroupOf B) := by
  constructor
  · rw [MathlibSupport.natCard_subgroupOf_eq hAB]
    have hcard := hA.isPiNumber_card
    rwa [MathlibSupport.natCard_subgroupOf_eq (hAB.trans hBC)] at hcard
  · have hdvd : A.relIndex B ∣ A.relIndex C := by
      exact ⟨B.relIndex C,
        (A.relIndex_mul_relIndex B C hAB hBC).symm⟩
    exact hA.isPiNumber_index.of_dvd hdvd

/-- A pi-subgroup lies in a normal pi-Hall subgroup. -/
private theorem le_normal_isHall_of_isPiNumber13
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {C K L : Subgroup G}
    (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall pi (K.subgroupOf C))
    (hLC : L ≤ C) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa only [KC] using hKnormal
  have hcop : (Nat.card L).Coprime KC.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    exact hKHall.isPiNumber_index hp hpIndex (hLpi hp hpL)
  intro x hxL
  let xC : C := ⟨x, hLC hxL⟩
  let qC : C →* C ⧸ KC := QuotientGroup.mk' KC
  have horderL : orderOf (qC xC) ∣ Nat.card L :=
    (orderOf_map_dvd qC xC).trans (by
      simpa [xC] using L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (qC xC) ∣ KC.index := by
    simpa only [KC.index_eq_card] using orderOf_dvd_natCard (qC xC)
  have horderOne : orderOf (qC xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  have hqOne : qC xC = 1 := orderOf_eq_one_iff.mp horderOne
  have hxKC : xC ∈ KC :=
    (QuotientGroup.eq_one_iff xC).mp
      (by simpa [qC] using hqOne)
  exact hxKC

/-- Semiregularity gives a trivial fixed-point subgroup. -/
private theorem centralizerWithin_eq_bot_of_semiregular13
    {G : Type u} [Group G]
    {K A X : Subgroup G}
    (hreg : IsSemiregularConjugation K A)
    (hXA : X ≤ A) (hX : X ≠ ⊥) :
    centralizerWithin K X = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  letI : Nontrivial X := X.nontrivial_iff_ne_bot.mpr hX
  obtain ⟨a, ha⟩ := exists_ne (1 : X)
  let aA : A := ⟨a, hXA a.property⟩
  let xK : K := ⟨x, hx.1⟩
  have hcomm : (a : G) * x = x * (a : G) := hx.2 a a.property
  have hconj :
      (aA : G) * (xK : G) * (aA : G)⁻¹ = (xK : G) := by
    simpa [aA, xK, mul_assoc] using
      congrArg (fun z : G ↦ z * (a : G)⁻¹) hcomm
  have haA : aA ≠ 1 := by
    intro haAone
    apply ha
    apply Subtype.ext
    exact congrArg (fun z : A ↦ (z : G)) haAone
  have hxone : xK = 1 :=
    hreg aA haA xK hconj
  apply Subgroup.mem_bot.mpr
  simpa only [xK, Subgroup.coe_one] using congrArg Subtype.val hxone

private theorem map_conj_map_conj13
    {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_one13
    {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj 1).toMonoidHom = H := by
  convert H.map_id using 1
  ext x
  simp

private theorem map_conj_inv_map_conj13
    {G : Type*} [Group G] (H : Subgroup G) (a : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj a⁻¹).toMonoidHom = H := by
  rw [map_conj_map_conj13]
  simpa only [inv_mul_cancel] using map_conj_one13 H

/-- Nonconjugacy of maximal subgroups is symmetric. -/
private theorem not_conjugate_symm13
    {G : Type u} [Group G] {M H : Subgroup G}
    (h : ∀ g : G, H ≠ M.map (MulAut.conj g).toMonoidHom) :
    ∀ g : G, M ≠ H.map (MulAut.conj g).toMonoidHom := by
  intro g hEq
  apply h g⁻¹
  have hh := congrArg
    (fun K : Subgroup G ↦
      K.map (MulAut.conj g⁻¹).toMonoidHom) hEq
  rw [map_conj_inv_map_conj13] at hh
  exact hh.symm

/-- Restrict an ambient Sylow statement to a common overgroup. -/
private theorem isSylowSubgroupOf_subgroupOf13
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {X D H : Subgroup G}
    (hXH : X ≤ H) (hDH : D ≤ H) (_hXD : X ≤ D)
    (hX : IsSylowSubgroupOf p X D) :
    IsSylowSubgroupOf p (X.subgroupOf H) (D.subgroupOf H) := by
  let DH : Subgroup H := D.subgroupOf H
  obtain ⟨S, hXS⟩ := hX
  let eDH : DH ≃* D := Subgroup.subgroupOfEquivOfLe hDH
  let SH : Sylow p DH :=
    S.mapSurjective (f := eDH.symm.toMonoidHom) eDH.symm.surjective
  have hSHcoe :
      (SH : Subgroup DH) =
        (S : Subgroup D).map eDH.symm.toMonoidHom := by
    change
      ((S.mapSurjective (f := eDH.symm.toMonoidHom)
          eDH.symm.surjective : Sylow p DH) : Subgroup DH) = _
    rw [Sylow.coe_mapSurjective]
  refine ⟨SH, by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hXH]
    rw [hSHcoe, Subgroup.map_map, Subgroup.map_map, hXS]
    apply congrArg (fun f : D →* G ↦ (S : Subgroup D).map f)
    ext d
    rfl⟩

/-- The intrinsic normalizer of a subgroup of `H` maps to the expected
ambient intersection. -/
private theorem map_normalizer_subgroupOf13
    {G : Type u} [Group G] {H Y : Subgroup G} (hYH : Y ≤ H) :
    (Subgroup.normalizer ((Y.subgroupOf H : Subgroup H) : Set H)).map
        H.subtype = H ⊓ Subgroup.normalizer (Y : Set G) := by
  calc
    (Subgroup.normalizer ((Y.subgroupOf H : Subgroup H) : Set H)).map
          H.subtype =
        ((Subgroup.normalizer (Y : Set G)).subgroupOf H).map
          H.subtype := by
      rw [Subgroup.subgroupOf_normalizer_eq hYH]
    _ = Subgroup.normalizer (Y : Set G) ⊓ H :=
      Subgroup.subgroupOf_map_subtype
        (Subgroup.normalizer (Y : Set G)) H
    _ = H ⊓ Subgroup.normalizer (Y : Set G) := inf_comm _ _

/-- Every subgroup of a cyclic group is characteristic. -/
private theorem subgroup_characteristic_of_isCyclic13
    {C : Type*} [Group C] [IsCyclic C] (H : Subgroup C) :
    H.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  obtain ⟨m, hm⟩ := e.toMonoidHom.map_cyclic
  rintro _ ⟨x, hx, rfl⟩
  rw [hm]
  exact H.zpow_mem hx m

/-- A characteristic subgroup is invariant under the full ambient
normalizer of its parent. -/
private theorem characteristic_map_subtype_le_normalizer13
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

/-- Transport a Sylow subgroup through a Hall inclusion. -/
private theorem exists_sylow_eq_map_of_sylow_hall13
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {A : Subgroup K} (hA : IsHall pi A) (hpPi : p ∈ pi)
    (P : Sylow p A) :
    ∃ Q : Sylow p K,
      (Q : Subgroup K) = (P : Subgroup A).map A.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup K := (P : Subgroup A).map A.subtype
  have hSp : IsPGroup p S := P.isPGroup'.map A.subtype
  have hpAindex : ¬ p ∣ A.index := by
    intro hpIndex
    exact hA.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpAindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

/-- A prime belonging to the Hall set and dividing the ambient group
already divides the Hall subgroup. -/
private theorem prime_dvd_card_isHall13
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {A : Subgroup K} (hA : IsHall pi A) (hpPi : p ∈ pi)
    (hpK : p ∣ Nat.card K) : p ∣ Nat.card A := by
  rw [← A.card_mul_index] at hpK
  rcases hp.dvd_mul.mp hpK with hpA | hpIndex
  · exact hpA
  · exact (hA.isPiNumber_index hp hpIndex hpPi).elim

/-- Cauchy's theorem in the rank-one subgroup language. -/
private theorem exists_rankOne_le_of_prime_dvd13
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

/-- A nontrivial finite `p`-group contains a rank-one elementary-abelian
subgroup. -/
private theorem exists_rankOne_le_of_isPGroup_ne_bot13
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hKp : IsPGroup p K) (hKne : K ≠ ⊥) :
    ∃ P : Subgroup G, P ≤ K ∧ IsElementaryAbelianOfRank p 1 P := by
  have hpK : p ∣ Nat.card K :=
    hKp.card_eq_or_dvd.resolve_left
      (fun hcard ↦ hKne (Subgroup.card_eq_one.mp hcard))
  exact exists_rankOne_le_of_prime_dvd13 hpK

/-- A cyclic Sylow subgroup rules out elementary-abelian rank two in the
ambient subgroup. -/
private theorem not_rankTwo_of_cyclic_sylow13
    {G : Type u} [Group G] [Finite G]
    {H P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hPH : IsSylowSubgroupOf p P H) (hcyc : IsCyclic P) :
    ¬ HasElementaryAbelianRankAtLeast p 2 H := by
  rintro ⟨A, hAH, hA⟩
  obtain ⟨Q, hQP⟩ := hPH
  let AH : Subgroup H := A.subgroupOf H
  have hAHrank : IsElementaryAbelianOfRank p 2 AH := hA.subgroupOf hAH
  obtain ⟨S, hAHS⟩ := hAHrank.isPGroup.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq H S Q
  let B : Subgroup H := AH.map (MulAut.conj x).toMonoidHom
  have hBQ : B ≤ (Q : Subgroup H) := by
    have hSQ :
        (S : Subgroup H).map (MulAut.conj x).toMonoidHom =
          (Q : Subgroup H) := by
      change MulAut.conj x • (S : Subgroup H) = (Q : Subgroup H)
      rw [← Sylow.coe_subgroup_smul, hx]
    exact (Subgroup.map_mono hAHS).trans_eq hSQ
  let BG : Subgroup G := B.map H.subtype
  have hBGP : BG ≤ P := by
    rw [hQP]
    exact Subgroup.map_mono hBQ
  have hBG : IsElementaryAbelianOfRank p 2 BG :=
    (hAHrank.map_of_injective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective).map_of_injective
        H.subtype H.subtype_injective
  letI : IsCyclic P := hcyc
  let eBG : BG.subgroupOf P ≃* BG :=
    Subgroup.subgroupOfEquivOfLe hBGP
  have hcycBGsub : IsCyclic (BG.subgroupOf P) := by infer_instance
  have hcycBG : IsCyclic BG := eBG.isCyclic.mp hcycBGsub
  exact hBG.not_isCyclic Fact.out hcycBG

/-- The four prime classes partition the prime divisors of a maximal
subgroup.  This is the set-valued form of `partition_pi_mmax` used by the
source proof. -/
private theorem primeSupport_mmax_partition13
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hpM : p ∈ primeSupport (Nat.card M)) :
    p ∈ sigmaPrimes M ∨ p ∈ tau1Primes M ∨
      p ∈ tau2Primes M ∨ p ∈ tau3Primes M := by
  have hp : p.Prime := hpM.1
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hpSigma : p ∈ sigmaPrimes M
  · exact Or.inl hpSigma
  obtain ⟨P, hPM, hP⟩ := exists_rankOne_le_of_prime_dvd13 hpM.2
  have hRankOne : HasElementaryAbelianRankAtLeast p 1 M :=
    ⟨P, hPM, hP⟩
  by_cases hRankTwo : HasElementaryAbelianRankAtLeast p 2 M
  · have hNoRankThree :
        ¬ HasElementaryAbelianRankAtLeast p 3 M := by
      intro hRankThree
      exact hpSigma (alpha_sub_sigma hM ⟨hp, hRankThree⟩)
    exact Or.inr (Or.inr (Or.inl
      ⟨hp, hpSigma, hRankTwo, hNoRankThree⟩))
  · by_cases hpDer : p ∣ Nat.card (_root_.commutator M)
    · exact Or.inr (Or.inr (Or.inr
        ⟨hp, hpSigma, hRankOne, hRankTwo, hpDer⟩))
    · exact Or.inr (Or.inl
        ⟨hp, hpSigma, hRankOne, hRankTwo, hpDer⟩)

/-- If a prime divisor of a maximal subgroup is neither tau-one nor
tau-two, every Sylow subgroup for that prime lies in the derived subgroup.
This is the `sSH'` step in the source proof of Lemma 13.1. -/
private theorem sylow_le_commutator_of_not_tau12_13
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hH : H ∈ minSimple_max_groups (G := G))
    (hpH : p ∈ primeSupport (Nat.card H))
    (hpNotTau1 : p ∉ tau1Primes H)
    (hpNotTau2 : p ∉ tau2Primes H)
    (P : Sylow p H) :
    (P : Subgroup H) ≤ _root_.commutator H := by
  let PG : Subgroup G := (P : Subgroup H).map H.subtype
  rcases primeSupport_mmax_partition13 hH hpH with
    hpSigma | hpTau1 | hpTau2 | hpTau3
  · have hPGsigma : PG ≤ sigmaCore H :=
      le_normal_isHall_of_isPiNumber13
        (sigmaCore_normal H) (Msigma_Hall hH)
        (Subgroup.map_subtype_le (P : Subgroup H))
        ((P.isPGroup'.map H.subtype).isPiNumber_natCard hpSigma)
    have hPGder : PG ≤ ⁅H, H⁆ := by
      simpa [H.map_subtype_commutator] using
        hPGsigma.trans (Msigma_der1 hH)
    apply (Subgroup.map_le_map_iff_of_injective
      H.subtype_injective).mp
    simpa [PG, H.map_subtype_commutator] using hPGder
  · exact (hpNotTau1 hpTau1).elim
  · exact (hpNotTau2 hpTau2).elim
  · have hpNotSigma : p ∉ sigmaPrimes H := hpTau3.2.1
    have hPGpi : IsPiNumber (sigmaPrimes H)ᶜ (Nat.card PG) :=
      (P.isPGroup'.map H.subtype).isPiNumber_natCard hpNotSigma
    obtain ⟨F, hPGF, hFH, hHallF⟩ :=
      MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
        (Subgroup.map_subtype_le (P : Subgroup H)) (mmax_sol hH)
          (sigmaPrimes H)ᶜ hPGpi
    obtain ⟨⟨E₁, hE₁F, hHallE₁⟩,
      ⟨E₃, hE₃F, hHallE₃⟩⟩ :=
      ex_tau13_compl hFH hHallF
    obtain ⟨E₂, _hE₂F, _hHallE₂, hCompl⟩ :=
      ex_tau2_compl hFH hHallF hE₁F hHallE₁ hE₃F hHallE₃
    have hctx : SigmaComplementContext F E₁ E₂ E₃ :=
      sigma_compl_context hH hCompl
    have hPGE₃ : PG ≤ E₃ := by
      exact le_normal_isHall_of_isPiNumber13
        hctx.E₃_normal hHallE₃ hPGF
        ((P.isPGroup'.map H.subtype).isPiNumber_natCard hpTau3)
    have hPGderF : PG ≤ (_root_.commutator F).map F.subtype :=
      hPGE₃.trans hctx.E₃_le_commutator
    have hderFH :
        (_root_.commutator F).map F.subtype ≤ ⁅H, H⁆ := by
      simpa [F.map_subtype_commutator, H.map_subtype_commutator] using
        (Subgroup.commutator_mono hFH hFH)
    have hPGder : PG ≤ ⁅H, H⁆ := hPGderF.trans hderFH
    apply (Subgroup.map_le_map_iff_of_injective
      H.subtype_injective).mp
    simpa [PG, H.map_subtype_commutator] using hPGder

/-- The beta-Frattini factorization used in Lemma 13.1. -/
private theorem betaCore_sup_inf_normalizer_eq13
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {H Y : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hH : H ∈ minSimple_max_groups (G := G))
    (hYH : Y ≤ H) (hYD : Y ≤ ⁅H, H⁆)
    (hYsyl : IsSylowSubgroupOf q Y ⁅H, H⁆)
    (hqNotBeta : q ∉ betaPrimes H) :
    betaCore H ⊔ (H ⊓ Subgroup.normalizer (Y : Set G)) = H := by
  classical
  let B : Subgroup H := (betaCore H).subgroupOf H
  let D : Subgroup H := _root_.commutator H
  let YH : Subgroup H := Y.subgroupOf H
  have hBnormal : B.Normal := by
    simpa [B] using betaCore_normal H
  letI : B.Normal := hBnormal
  have hDnormal : D.Normal := by
    dsimp [D]
    infer_instance
  letI : D.Normal := hDnormal
  have hBD : B ≤ D := by
    intro x hx
    change (x : G) ∈ betaCore H at hx
    change x ∈ D
    obtain ⟨y, hy, hyx⟩ := Mbeta_der1 hH hx
    have hyx' : y = x := H.subtype_injective hyx
    simpa [hyx'] using hy
  have hYHD : YH ≤ D := by
    intro y hy
    have hyD : (y : G) ∈ ⁅H, H⁆ := hYD hy
    rw [← H.map_subtype_commutator] at hyD
    obtain ⟨d, hd, hdy⟩ := hyD
    exact H.subtype_injective hdy ▸ hd
  let YD : Subgroup D := YH.subgroupOf D
  have hYHp : IsPGroup q YH :=
    hYsyl.isPGroup.of_equiv
      (Subgroup.subgroupOfEquivOfLe hYH).symm
  have hYDp : IsPGroup q YD :=
    hYHp.of_equiv
      (Subgroup.subgroupOfEquivOfLe hYHD).symm
  obtain ⟨S, hYS⟩ := hYsyl
  have hYDindex : YD.index = S.index := by
    change YH.relIndex D = S.index
    calc
      YH.relIndex D =
          (YH.map H.subtype).relIndex (D.map H.subtype) :=
        (Subgroup.relIndex_map_map_of_injective
          YH D H.subtype_injective).symm
      _ = Y.relIndex ⁅H, H⁆ := by
        rw [Subgroup.map_subgroupOf_eq_of_le hYH,
          H.map_subtype_commutator]
      _ = ((S : Subgroup (⁅H, H⁆ : Subgroup G)).map
            (⁅H, H⁆).subtype).relIndex ⁅H, H⁆ := by rw [hYS]
      _ = ((S : Subgroup (⁅H, H⁆ : Subgroup G)).map
            (⁅H, H⁆).subtype).relIndex
            ((⊤ : Subgroup (⁅H, H⁆ : Subgroup G)).map
              (⁅H, H⁆).subtype) := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (S : Subgroup (⁅H, H⁆ : Subgroup G)).relIndex ⊤ :=
        Subgroup.relIndex_map_map_of_injective _ _
          (⁅H, H⁆).subtype_injective
      _ = S.index :=
        (S : Subgroup (⁅H, H⁆ : Subgroup G)).relIndex_top_right
  let SD : Sylow q D := hYDp.toSylow (by
    rw [hYDindex]
    exact S.not_dvd_index)
  have hSDcoe : (SD : Subgroup D) = YD :=
    IsPGroup.toSylow_coe hYDp (by
      rw [hYDindex]
      exact S.not_dvd_index)
  have hYHsylD : IsSylowSubgroupOf q YH D := by
    exact ⟨SD, by
      rw [hSDcoe]
      exact (Subgroup.map_subgroupOf_eq_of_le hYHD).symm⟩
  have hnil : Group.IsNilpotent (D ⧸ B.subgroupOf D) := by
    simpa [B, D] using Mbeta_quo_nil hH
  let N : Subgroup H := B ⊔ YH
  have hNnormal : N.Normal := by
    dsimp [N]
    exact normal_sup_of_sylow_quotient_nilpotent13
      hBD hYHD hYHsylD hnil
  letI : N.Normal := hNnormal
  have hND : N ≤ D := sup_le hBD hYHD
  let ND : Subgroup D := N.subgroupOf D
  have hSDND : (SD : Subgroup D) ≤ ND := by
    rw [hSDcoe]
    exact Subgroup.subgroupOf_mono D le_sup_right
  let SDN : Sylow q ND := SD.subtype hSDND
  let eND : ND ≃* N := Subgroup.subgroupOfEquivOfLe hND
  let SN : Sylow q N :=
    SDN.mapSurjective (f := eND.toMonoidHom) eND.surjective
  have hSNcoe :
      (SN : Subgroup N) =
        (SDN : Subgroup ND).map eND.toMonoidHom := by
    change
      ((SDN.mapSurjective (f := eND.toMonoidHom)
          eND.surjective : Sylow q N) : Subgroup N) = _
    rw [Sylow.coe_mapSurjective]
  have hSNmap : (SN : Subgroup N).map N.subtype = YH := by
    calc
      (SN : Subgroup N).map N.subtype =
          (SDN : Subgroup ND).map
            (N.subtype.comp eND.toMonoidHom) := by
        rw [hSNcoe, Subgroup.map_map]
      _ = (SDN : Subgroup ND).map
            (D.subtype.comp ND.subtype) := by
        apply congrArg
        ext x
        rfl
      _ = (SD : Subgroup D).map D.subtype := by
        dsimp only [SDN]
        rw [Sylow.coe_subtype, ← Subgroup.map_map,
          Subgroup.map_subgroupOf_eq_of_le hSDND]
      _ = YH := by
        rw [hSDcoe]
        exact Subgroup.map_subgroupOf_eq_of_le hYHD
  let U : Subgroup H := Subgroup.normalizer (YH : Set H)
  have hUN : U ⊔ N = ⊤ := by
    simpa [U, hSNmap] using SN.normalizer_sup_eq_top
  have hBU : B ⊔ U = ⊤ := by
    apply top_unique
    rw [← hUN]
    apply sup_le
    · exact le_sup_right
    · dsimp [N]
      exact sup_le le_sup_left (Subgroup.le_normalizer.trans le_sup_right)
  have hUmap : U.map H.subtype =
      H ⊓ Subgroup.normalizer (Y : Set G) := by
    simpa only [U, YH] using map_normalizer_subgroupOf13 hYH
  have hmapped := congrArg (fun K : Subgroup H ↦ K.map H.subtype) hBU
  rw [Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le (betaCore_le H),
    hUmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmapped
  exact hmapped

/-! ## Lemma 13.1 and Corollary 13.2 -/

/-- `BGsection13.v: Msigma_setI_mmax_central`, Bender--Glauberman
Lemma 13.1. -/
theorem Msigma_setI_mmax_central
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E H : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hpE : p ∈ primeSupport (Nat.card E))
    (hpH : p ∈ primeSupport (Nat.card H))
    (hpNotTau1H : p ∉ tau1Primes H)
    (hcomm : ⁅sigmaCore M ⊓ H, M ⊓ H⁆ ≠ ⊥)
    (hnotConj : ∀ g : G,
      H ≠ M.map (MulAut.conj g).toMonoidHom) :
    (∀ P : Subgroup G,
      P ≤ M ⊓ H → IsPGroup p P →
        P ≤ Subgroup.centralizer
          ((sigmaCore M ⊓ H : Subgroup G) : Set G)) ∧
      p ∉ tau2Primes H ∧
      (p ∈ tau1Primes M →
        p ∈ betaPrimes (⊤ : Subgroup G)) := by
  let R : Subgroup G :=
    ⁅sigmaCore M ⊓ H, M ⊓ H⁆
  have hRne : R ≠ ⊥ := by
    simpa only [R] using hcomm
  let q : ℕ := Nat.minFac (Nat.card R)
  have hRcardNeOne : Nat.card R ≠ 1 :=
    (R.one_lt_card_iff_ne_bot.mpr hRne).ne'
  have hq : q.Prime :=
    Nat.minFac_prime hRcardNeOne
  letI : Fact q.Prime := ⟨hq⟩
  have hp : p.Prime := hpE.1
  letI : Fact p.Prime := ⟨hp⟩
  have hqR : q ∣ Nat.card R :=
    Nat.minFac_dvd (Nat.card R)
  have hMnormSigma :
      M ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (sigmaCore_le M)).mp (sigmaCore_normal M)
  have hRleSigma : R ≤ sigmaCore M := by
    have hcommLe :
        ⁅sigmaCore M, M ⊓ H⁆ ≤ sigmaCore M :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        (inf_le_left.trans hMnormSigma)
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans hcommLe
  have hqSigmaSupport :
      q ∈ primeSupport (Nat.card (sigmaCore M)) :=
    ⟨hq, hqR.trans (Subgroup.card_dvd_of_le hRleSigma)⟩
  have hqSigma : q ∈ sigmaPrimes M := by
    rwa [pi_Msigma hM] at hqSigmaSupport
  let D : Subgroup G := ⁅H, H⁆
  have hRD : R ≤ D := by
    dsimp only [R, D]
    exact Subgroup.commutator_mono inf_le_right inf_le_right
  have hqD : q ∣ Nat.card D :=
    hqR.trans (Subgroup.card_dvd_of_le hRD)
  let S : Sylow q D := Classical.choice Sylow.nonempty
  let Y : Subgroup G :=
    (S : Subgroup D).map D.subtype
  have hYsyl : IsSylowSubgroupOf q Y D :=
    ⟨S, rfl⟩
  have hYne : Y ≠ ⊥ := by
    have hSne : (S : Subgroup D) ≠ ⊥ :=
      S.ne_bot_of_dvd_card hqD
    intro hYbot
    apply hSne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (S : Subgroup D) D.subtype_injective).mp hYbot
  have hYH : Y ≤ H :=
    (Subgroup.map_subtype_le (S : Subgroup D)).trans
      H.commutator_le_self
  have hYsigma : IsPiNumber (sigmaPrimes M) (Nat.card Y) :=
    (S.isPGroup'.map D.subtype).isPiNumber_natCard hqSigma
  have hnotConjSymm : ∀ g : G,
      M ≠ H.map (MulAut.conj g).toMonoidHom :=
    not_conjugate_symm13 hnotConj
  have hqNotBetaH : q ∉ betaPrimes H := by
    intro hqBetaH
    exact Set.disjoint_left.mp (sigma_disjoint hH hM hnotConjSymm).2.1
      (beta_sub_alpha H hqBetaH) hqSigma
  have hYD : Y ≤ ⁅H, H⁆ := by
    simpa only [D] using
      (Subgroup.map_subtype_le (S : Subgroup D))
  let I : Subgroup G :=
    H ⊓ Subgroup.normalizer (Y : Set G)
  have hfactor : betaCore H ⊔ I = H := by
    simpa only [I] using
      betaCore_sup_inf_normalizer_eq13 hH hYH hYD hYsyl hqNotBetaH
  have hYfamily :
      H ∈ minSimple_max_groups_of (G := G) (Y : Set G) :=
    ⟨hH, hYH⟩
  have hJsub :
      p ∉ betaPrimes (⊤ : Subgroup G) →
        ¬ HasElementaryAbelianRankAtLeast p 2
            (H ⊓ Subgroup.normalizer (Y : Set G)) ∧
          (p ∈ tau1Primes M →
            ¬ p ∣ Nat.card
              (_root_.commutator
                (H ⊓ Subgroup.normalizer (Y : Set G) : Subgroup G))) := by
    intro hpNotBeta
    exact (sigma_Jsub hM hYsigma hYne).2
      hEM hHallE hpE hpNotBeta hYfamily hnotConj
  have hpNotTau2H : p ∉ tau2Primes H := by
    intro hpTau2H
    have hpNotBetaTop : p ∉ betaPrimes (⊤ : Subgroup G) :=
      (tau2_not_beta hH hpTau2H).1
    have hpNotBetaH : p ∉ betaPrimes H := by
      intro hpBetaH
      have hpInter : p ∈
          sigmaPrimes H ∩ betaPrimes (⊤ : Subgroup G) := by
        rwa [predI_sigma_beta hH]
      exact hpNotBetaTop hpInter.2
    have hpBetaCore : ¬ p ∣ Nat.card (betaCore H) := by
      intro hpCard
      exact hpNotBetaH (betaCore_isPiNumber H hpTau2H.1 hpCard)
    let PI : Sylow p I := default
    have hPIH : IsSylowSubgroupOf p
        ((PI : Subgroup I).map I.subtype) H :=
      isSylowSubgroupOf_map_of_normal_sup13
        (betaCore_le H) inf_le_left (betaCore_normal H)
          hfactor hpBetaCore PI
    obtain ⟨A, hAPI, hA⟩ :=
      exists_elementaryAbelian_le_ambientSylow13
        hPIH hpTau2H.2.2.1
    have hAI : A ≤ I :=
      hAPI.trans (Subgroup.map_subtype_le (PI : Subgroup I))
    exact (hJsub hpNotBetaTop).1 ⟨A, by simpa [I] using hAI, hA⟩
  have hpTau1ImpBeta :
      p ∈ tau1Primes M → p ∈ betaPrimes (⊤ : Subgroup G) := by
    intro hpTau1M
    by_contra hpNotBeta
    have hpNotBetaH : p ∉ betaPrimes H := by
      intro hpBetaH
      have hpInter : p ∈
          sigmaPrimes H ∩ betaPrimes (⊤ : Subgroup G) := by
        rwa [predI_sigma_beta hH]
      exact hpNotBeta hpInter.2
    have hpHder : p ∣ Nat.card (_root_.commutator H) := by
      rcases primeSupport_mmax_partition13 hH hpH with
        hpSigmaH | hpTau1H | hpTau2H | hpTau3H
      · let SH : Subgroup H := (sigmaCore H).subgroupOf H
        have hpSH : p ∣ Nat.card SH :=
          prime_dvd_card_isHall13 hpH.1 (Msigma_Hall hH)
            hpSigmaH hpH.2
        have hpSigmaCard : p ∣ Nat.card (sigmaCore H) := by
          rwa [MathlibSupport.natCard_subgroupOf_eq (sigmaCore_le H)] at hpSH
        have hSigmaDer : sigmaCore H ≤ ⁅H, H⁆ := by
          simpa only [H.map_subtype_commutator] using Msigma_der1 hH
        have hpAmbientDer : p ∣ Nat.card (⁅H, H⁆ : Subgroup G) :=
          hpSigmaCard.trans (Subgroup.card_dvd_of_le hSigmaDer)
        rw [← H.map_subtype_commutator,
          Subgroup.card_map_of_injective H.subtype_injective] at hpAmbientDer
        exact hpAmbientDer
      · exact (hpNotTau1H hpTau1H).elim
      · exact (hpNotTau2H hpTau2H).elim
      · exact hpTau3H.2.2.2.2
    have hpNotSigmaM : p ∉ sigmaPrimes M := by
      have hpEsub : p ∣ Nat.card (E.subgroupOf M) := by
        rw [MathlibSupport.natCard_subgroupOf_eq hEM]
        exact hpE.2
      exact hHallE.isPiNumber_card hpE.1 hpEsub
    have hpq : p ≠ q := by
      intro hpq
      exact hpNotSigmaM (hpq ▸ hqSigma)
    let YH : Subgroup H := Y.subgroupOf H
    have hDsub : (⁅H, H⁆).subgroupOf H =
        _root_.commutator H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le
          H.commutator_le_self,
        H.map_subtype_commutator]
    have hYHder : YH ≤ _root_.commutator H := by
      rw [← hDsub]
      intro y hy
      exact hYD hy
    have hYHp : IsPGroup q YH :=
      hYsyl.isPGroup.of_equiv
        (Subgroup.subgroupOfEquivOfLe hYH).symm
    have hYHsyl : IsSylowSubgroupOf q YH
        (_root_.commutator H) := by
      rw [← hDsub]
      exact isSylowSubgroupOf_subgroupOf13 hYH
        H.commutator_le_self hYD hYsyl
    obtain ⟨PD, hPD⟩ :=
      (beta'_cent_Sylow hH hpNotBetaH hqNotBetaH hYHp
        (Or.inl ⟨hpq, hYHder⟩)).2.2 hYHsyl
    have hpPD : p ∣ Nat.card PD :=
      PD.isPGroup'.card_eq_or_dvd.resolve_left
        (fun hcard ↦
          PD.ne_bot_of_dvd_card hpHder (Subgroup.card_eq_one.mp hcard))
    let U : Subgroup H := Subgroup.normalizer (YH : Set H)
    have hUmap : U.map H.subtype = I := by
      simpa only [U, YH, I] using map_normalizer_subgroupOf13 hYH
    have hderUmap :
        (((_root_.commutator U).map U.subtype).map H.subtype :
            Subgroup G) = ⁅I, I⁆ := by
      calc
        (((_root_.commutator U).map U.subtype).map H.subtype :
              Subgroup G) =
            (⁅U, U⁆ : Subgroup H).map H.subtype := by
              rw [U.map_subtype_commutator]
        _ = ⁅U.map H.subtype, U.map H.subtype⁆ := by
          rw [Subgroup.map_commutator]
        _ = ⁅I, I⁆ := by rw [hUmap]
    have hPDmap :
        (((PD : Subgroup (_root_.commutator H)).map
              (_root_.commutator H).subtype).map H.subtype :
            Subgroup G) ≤ ⁅I, I⁆ := by
      exact (Subgroup.map_mono hPD).trans_eq hderUmap
    have hpPDmap : p ∣ Nat.card
        (((PD : Subgroup (_root_.commutator H)).map
              (_root_.commutator H).subtype).map H.subtype :
            Subgroup G) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective,
        Subgroup.card_map_of_injective
          (_root_.commutator H).subtype_injective]
      exact hpPD
    have hpIder : p ∣ Nat.card (⁅I, I⁆ : Subgroup G) :=
      hpPDmap.trans (Subgroup.card_dvd_of_le hPDmap)
    have hpIderIntrinsic :
        p ∣ Nat.card (_root_.commutator I) := by
      rw [← I.map_subtype_commutator,
        Subgroup.card_map_of_injective I.subtype_injective] at hpIder
      exact hpIder
    exact (hJsub hpNotBeta).2 hpTau1M
      (by simpa only [I] using hpIderIntrinsic)
  constructor
  swap
  exact ⟨hpNotTau2H, hpTau1ImpBeta⟩
  intro P hPMH hPp
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.commutator_comm]
  -- The alpha-core quotient argument from the final paragraph of the
  -- source proof is carried out below, after choosing an ambient Sylow
  -- subgroup of `H` containing `P`.
  have hPH : P ≤ H := hPMH.trans inf_le_right
  have hPM : P ≤ M := hPMH.trans inf_le_left
  let PH : Subgroup H := P.subgroupOf H
  have hPHp : IsPGroup p PH :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hPHQ⟩ := hPHp.exists_le_sylow
  have hQder : (Q : Subgroup H) ≤ _root_.commutator H :=
    sylow_le_commutator_of_not_tau12_13
      hH hpH hpNotTau1H hpNotTau2H Q
  let A : Subgroup H := (alphaCore H).subgroupOf H
  let DH : Subgroup H := _root_.commutator H
  have hAnormal : A.Normal := by
    simpa [A] using alphaCore_normal H
  letI : A.Normal := hAnormal
  have hDHnormal : DH.Normal := by
    dsimp [DH]
    infer_instance
  letI : DH.Normal := hDHnormal
  have hADH : A ≤ DH := by
    apply (Subgroup.map_le_map_iff_of_injective
      H.subtype_injective).mp
    simpa [A, DH, H.map_subtype_commutator,
      Subgroup.map_subgroupOf_eq_of_le (alphaCore_le H)] using
        (Malpha_sub_Msigma hH).trans (Msigma_der1 hH)
  have hQsylDH : IsSylowSubgroupOf p (Q : Subgroup H) DH := by
    let QD : Sylow p DH := Q.subtype hQder
    exact ⟨QD, by
      simpa [QD, Sylow.coe_subtype] using
        (Subgroup.map_subgroupOf_eq_of_le hQder).symm⟩
  have hnilDH : Group.IsNilpotent (DH ⧸ A.subgroupOf DH) := by
    let pi : H →* H ⧸ A := QuotientGroup.mk' A
    have hmapDH : DH.map pi =
        _root_.commutator (H ⧸ A) := by
      dsimp [DH, pi]
      rw [map_commutator_eq,
        MonoidHom.range_eq_top.mpr
          (QuotientGroup.mk'_surjective A)]
      exact (_root_.commutator_def (H ⧸ A)).symm
    letI : Group.IsNilpotent (DH.map pi) := by
      rw [hmapDH]
      simpa [A] using Malpha_quo_nil hH
    exact Group.nilpotent_of_mulEquiv
      (subgroupQuotientEquivImage13 A DH).symm
  have hAQnormal : (A ⊔ (Q : Subgroup H)).Normal :=
    normal_sup_of_sylow_quotient_nilpotent13
      hADH hQder hQsylDH hnilDH
  let K : Subgroup G := sigmaCore M ⊓ H
  let KH : Subgroup H := K.subgroupOf H
  have hPnormSigma :
      P ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
    hPM.trans hMnormSigma
  have hPnormH : P ≤ Subgroup.normalizer (H : Set G) :=
    hPH.trans Subgroup.le_normalizer
  have hPnormK : P ≤ Subgroup.normalizer (K : Set G) := by
    exact (le_inf hPnormSigma hPnormH).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hPHnormKH : PH ≤ Subgroup.normalizer (KH : Set H) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    change ((y : G) ∈ K ↔
      (x : G) * (y : G) * (x : G)⁻¹ ∈ K)
    exact (Subgroup.mem_normalizer_iff.mp (hPnormK hx)) (y : G)
  have hpNotSigmaM : p ∉ sigmaPrimes M := by
    have hpEsub : p ∣ Nat.card (E.subgroupOf M) := by
      rw [MathlibSupport.natCard_subgroupOf_eq hEM]
      exact hpE.2
    exact hHallE.isPiNumber_card hp hpEsub
  have hpKH : ¬ p ∣ Nat.card KH := by
    intro hpCard
    have hpK : p ∣ Nat.card K := by
      rwa [MathlibSupport.natCard_subgroupOf_eq inf_le_right] at hpCard
    have hpSigmaCore : p ∣ Nat.card (sigmaCore M) :=
      hpK.trans (Subgroup.card_dvd_of_le inf_le_left)
    exact hpNotSigmaM (sigmaCore_isPiNumber M hp hpSigmaCore)
  have hKHp' : IsPPrimeSubgroup p KH := by
    exact hp.coprime_iff_not_dvd.mpr hpKH
  have hAnormalTop : (A.subgroupOf (⊤ : Subgroup H)).Normal := by
    exact Subgroup.Normal.subgroupOf hAnormal (⊤ : Subgroup H)
  have hAQnormalTop :
      ((A ⊔ (Q : Subgroup H)).subgroupOf
        (⊤ : Subgroup H)).Normal := by
    exact Subgroup.Normal.subgroupOf hAQnormal (⊤ : Subgroup H)
  have hcommLe : ⁅KH, PH⁆ ≤ KH ⊓ A :=
    commutator_le_inf_of_normal_sup_of_coprime13
      (G := H) (H := (⊤ : Subgroup H))
      (S := A) (A := PH) (B := (Q : Subgroup H)) (K := KH)
      le_top le_top le_top hPHQ le_top
      hAnormalTop hAQnormalTop hPHnormKH Q.isPGroup' hKHp'
  have hAlphaSigma : alphaCore H ⊓ sigmaCore M = ⊥ :=
    (sigma_disjoint hH hM hnotConjSymm).1
  have hcommBot : ⁅KH, PH⁆ = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxinf := hcommLe hx
    have hxAS : (x : G) ∈ alphaCore H ⊓ sigmaCore M :=
      ⟨hxinf.2, hxinf.1.1⟩
    rw [hAlphaSigma] at hxAS
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (Subgroup.mem_bot.mp hxAS))
  have hmapped := congrArg
    (fun L : Subgroup H ↦ L.map H.subtype) hcommBot
  rw [Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le inf_le_right,
    Subgroup.map_subgroupOf_eq_of_le hPH,
    Subgroup.map_bot] at hmapped
  simpa [K, KH, PH] using hmapped

/-- `BGsection13.v: cent_norm_tau13_mmax`, Bender--Glauberman
Corollary 13.2. -/
theorem cent_norm_tau13_mmax
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E P H : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau13 : p ∈ tau1Primes M ∨ p ∈ tau3Primes M)
    (hPM : P ≤ M) (hPp : IsPGroup p P)
    (hH : H ∈ minSimple_max_groups (G := G))
    (hNormPH : Subgroup.normalizer (P : Set G) ≤ H) :
    (∀ P₁ : Subgroup G,
      P₁ ≤ M ⊓ H → IsPGroup p P₁ →
        P₁ ≤ Subgroup.centralizer
          ((sigmaCore M ⊓ H : Subgroup G) : Set G)) ∧
      (∀ X : Subgroup G,
        X ≤ E ⊓ H →
          IsPiNumber (tau1Primes H)ᶜ (Nat.card X) →
            X ≤ Subgroup.centralizer
              ((sigmaCore M ⊓ H : Subgroup G) : Set G)) ∧
      (⁅sigmaCore M ⊓ H, M ⊓ H⁆ ≠ ⊥ →
        p ∈ sigmaPrimes H ∧
          (p ∈ tau1Primes M → p ∈ betaPrimes H)) := by
  have hp : p.Prime := hpTau13.elim (fun h ↦ h.1) (fun h ↦ h.1)
  letI : Fact p.Prime := ⟨hp⟩
  have hPne : P ≠ ⊥ := by
    intro hP
    have hbotNormal : (⊥ : Subgroup G).Normal := inferInstance
    have hnormalizerBot :
        Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hbotNormal
    have htop : (⊤ : Subgroup G) ≤ H := by
      rw [hP, hnormalizerBot] at hNormPH
      exact hNormPH
    exact (not_le_of_gt (mmax_proper hH)) htop
  have hpP : p ∣ Nat.card P :=
    hPp.card_eq_or_dvd.resolve_left
      (fun hcard ↦ hPne (Subgroup.card_eq_one.mp hcard))
  have hpMcard : p ∣ Nat.card M :=
    hpP.trans (Subgroup.card_dvd_of_le hPM)
  have hpHcard : p ∣ Nat.card H :=
    hpP.trans (Subgroup.card_dvd_of_le
      (Subgroup.le_normalizer.trans hNormPH))
  have hpNotSigmaM : p ∉ sigmaPrimes M :=
    hpTau13.elim (fun h ↦ h.2.1) (fun h ↦ h.2.1)
  have hpE : p ∈ primeSupport (Nat.card E) := by
    rw [pi_sigma_compl hEM hHallE]
    exact ⟨⟨hp, hpMcard⟩, hpNotSigmaM⟩
  have hpH : p ∈ primeSupport (Nat.card H) := ⟨hp, hpHcard⟩
  have hpClass : p ∈ sigmaPrimes H ∨ p ∈ tau2Primes H :=
    prime_class_mmax_norm hH hPp hNormPH
  have hpNotTau1H : p ∉ tau1Primes H := by
    intro hpTau1H
    rcases hpClass with hpSigmaH | hpTau2H
    · exact hpTau1H.2.1 hpSigmaH
    · exact hpTau1H.2.2.2.1 hpTau2H.2.2.1
  have hnotConj : ∀ g : G,
      H ≠ M.map (MulAut.conj g).toMonoidHom :=
    mmax_norm_notJ hM hH hPp hPM hNormPH (Or.inr hpTau13)
  by_cases hcomm : ⁅sigmaCore M ⊓ H, M ⊓ H⁆ = ⊥
  · have hcent : M ⊓ H ≤
        Subgroup.centralizer ((sigmaCore M ⊓ H : Subgroup G) : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      rw [Subgroup.commutator_comm]
      exact hcomm
    exact ⟨fun P₁ hP₁ _ ↦ hP₁.trans hcent, by
      intro X hX _
      have hXM : X ≤ M := (hX.trans inf_le_left).trans hEM
      have hXH : X ≤ H := hX.trans inf_le_right
      exact (le_inf hXM hXH).trans hcent,
      fun hne ↦ (hne hcomm).elim⟩
  · have hbase := Msigma_setI_mmax_central
      hM hEM hHallE hH hpE hpH hpNotTau1H hcomm hnotConj
    have hpSigmaH : p ∈ sigmaPrimes H :=
      hpClass.resolve_right (fun hpTau2H ↦ hbase.2.1 hpTau2H)
    constructor
    exact hbase.1
    constructor
    swap
    · intro _
      constructor
      · exact hpSigmaH
      · intro hpTau1M
        have hpBetaTop := hbase.2.2 hpTau1M
        have hpInter : p ∈
            sigmaPrimes H ∩ betaPrimes (⊤ : Subgroup G) :=
          ⟨hpSigmaH, hpBetaTop⟩
        rwa [predI_sigma_beta hH] at hpInter
    intro X hX hXpi
    apply le_of_sylow_le13
    intro q hqX Q
    let QG : Subgroup G :=
      (Q : Subgroup X).map X.subtype
    have hQX : QG ≤ X :=
      Subgroup.map_subtype_le (Q : Subgroup X)
    have hXE : X ≤ E := hX.trans inf_le_left
    have hXH : X ≤ H := hX.trans inf_le_right
    have hqE : q ∈ primeSupport (Nat.card E) :=
      ⟨hqX.1, hqX.2.trans
        (Subgroup.card_dvd_of_le hXE)⟩
    have hqH : q ∈ primeSupport (Nat.card H) :=
      ⟨hqX.1, hqX.2.trans
        (Subgroup.card_dvd_of_le hXH)⟩
    have hqNotTau1H : q ∉ tau1Primes H :=
      hXpi hqX.1 hqX.2
    have hQMH : QG ≤ M ⊓ H :=
      le_inf ((hQX.trans hXE).trans hEM)
        (hQX.trans hXH)
    have hQq : IsPGroup q QG :=
      Q.isPGroup'.map X.subtype
    have hqbase := Msigma_setI_mmax_central
      hM hEM hHallE hH hqE hqH hqNotTau1H
        hcomm hnotConj
    exact hqbase.1 QG hQMH hQq

/-! ## Corollary 13.3 -/

/-- `BGsection13.v: cyclic_primact_Msigma`, Corollary 13.3(a). -/
theorem cyclic_primact_Msigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E P : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    [Fact p.Prime]
    (hSylowP : IsSylowSubgroupOf p P E)
    (hcyclicP : IsCyclic P) :
    IsPrimeAction (sigmaCore M) P := by
  intro X hXP hXne
  obtain ⟨PE, hPE⟩ := hSylowP
  have hPEsub : P ≤ E := by
    rw [hPE]
    exact Subgroup.map_subtype_le (PE : Subgroup E)
  have hPp : IsPGroup p P := by
    rw [hPE]
    exact PE.isPGroup'.map E.subtype
  have hPM : P ≤ M := hPEsub.trans hEM
  have hXp : IsPGroup p X := hPp.to_le hXP
  have hpP : p ∣ Nat.card P :=
    hPp.card_eq_or_dvd.resolve_left
      (fun hcard ↦ hXne
        (le_bot_iff.mp (hXP.trans_eq (Subgroup.card_eq_one.mp hcard))))
  have hpMcard : p ∣ Nat.card M :=
    hpP.trans (Subgroup.card_dvd_of_le hPM)
  have hpNotSigmaM : p ∉ sigmaPrimes M := by
    have hpEsub : p ∣ Nat.card (E.subgroupOf M) := by
      rw [MathlibSupport.natCard_subgroupOf_eq hEM]
      exact hpP.trans (Subgroup.card_dvd_of_le hPEsub)
    exact hHallE.isPiNumber_card Fact.out hpEsub
  have hRankOneM : HasElementaryAbelianRankAtLeast p 1 M := by
    obtain ⟨Y, hYX, hY⟩ :=
      exists_rankOne_le_of_isPGroup_ne_bot13 hXp hXne
    exact ⟨Y, hYX.trans (hXP.trans hPM), hY⟩
  let eEM : E.subgroupOf M ≃* E :=
    Subgroup.subgroupOfEquivOfLe hEM
  let PEM : Sylow p (E.subgroupOf M) :=
    PE.mapSurjective (f := eEM.symm.toMonoidHom)
      eEM.symm.surjective
  have hPEMcoe :
      (PEM : Subgroup (E.subgroupOf M)) =
        (PE : Subgroup E).map eEM.symm.toMonoidHom := by
    change
      ((PE.mapSurjective (f := eEM.symm.toMonoidHom)
          eEM.symm.surjective : Sylow p (E.subgroupOf M)) :
        Subgroup (E.subgroupOf M)) = _
    rw [Sylow.coe_mapSurjective]
  obtain ⟨PM, hPMmap⟩ :=
    exists_sylow_eq_map_of_sylow_hall13
      (K := M) (A := E.subgroupOf M)
      (Fact.out : p.Prime) hHallE hpNotSigmaM PEM
  have hPMambient :
      (PM : Subgroup M).map M.subtype = P := by
    rw [hPMmap, hPEMcoe]
    rw [Subgroup.map_map, Subgroup.map_map, hPE]
    apply congrArg (fun f : E →* G ↦ (PE : Subgroup E).map f)
    ext x
    rfl
  have hPMsyl : IsSylowSubgroupOf p P M :=
    ⟨PM, hPMambient.symm⟩
  have hNoRankTwo :
      ¬ HasElementaryAbelianRankAtLeast p 2 M :=
    not_rankTwo_of_cyclic_sylow13 hPMsyl hcyclicP
  have hpTau13 : p ∈ tau1Primes M ∨ p ∈ tau3Primes M := by
    by_cases hpDer : p ∣ Nat.card (_root_.commutator M)
    · exact Or.inr
        ⟨Fact.out, hpNotSigmaM, hRankOneM, hNoRankTwo, hpDer⟩
    · exact Or.inl
        ⟨Fact.out, hpNotSigmaM, hRankOneM, hNoRankTwo, hpDer⟩
  have hXproper : X < ⊤ := mFT_pgroup_proper X hXp
  have hNXproper : Subgroup.normalizer (X : Set G) < ⊤ :=
    mFT_norm_proper X hXne hXproper
  obtain ⟨H, hH, hNXH⟩ :=
    mmax_exists (Subgroup.normalizer (X : Set G)) hNXproper
  letI : IsCyclic P := hcyclicP
  let XP : Subgroup P := X.subgroupOf P
  have hXPchar : XP.Characteristic :=
    subgroup_characteristic_of_isCyclic13 XP
  letI : XP.Characteristic := hXPchar
  have hNormPnormX : Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (X : Set G) := by
    simpa [XP, Subgroup.map_subgroupOf_eq_of_le hXP] using
      characteristic_map_subtype_le_normalizer13 P XP
  have hPnormX : P ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.le_normalizer.trans hNormPnormX
  have hPH : P ≤ H := hPnormX.trans hNXH
  have hNormPH : Subgroup.normalizer (P : Set G) ≤ H :=
    hNormPnormX.trans hNXH
  have hbase := cent_norm_tau13_mmax hM hEM hHallE hpTau13
    hPM hPp hH hNormPH
  have hPcentral : P ≤ Subgroup.centralizer
      ((sigmaCore M ⊓ H : Subgroup G) : Set G) :=
    hbase.1 P (le_inf hPM hPH) hPp
  apply le_antisymm
  · intro z hz
    exact ⟨hz.1, by
      have hzH : z ∈ H :=
        hNXH (Subgroup.centralizer_le_normalizer (X : Set G) hz.2)
      have hzK : z ∈ sigmaCore M ⊓ H := ⟨hz.1, hzH⟩
      change z ∈ Subgroup.centralizer (P : Set G)
      exact (Subgroup.mem_centralizer_iff.mpr fun a ha ↦
        (Subgroup.mem_centralizer_iff.mp (hPcentral ha) z hzK).symm)⟩
  · intro z hz
    exact ⟨hz.1, by
      change z ∈ Subgroup.centralizer (X : Set G)
      exact Subgroup.centralizer_le hXP hz.2⟩

/-- `BGsection13.v: tau3_primact_Msigma`, Corollary 13.3(b). -/
theorem tau3_primact_Msigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₃ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hE₃E : E₃ ≤ E)
    (hHallE₃ : IsHall (tau3Primes M) (E₃.subgroupOf E)) :
    IsPrimeAction (sigmaCore M) E₃ := by
  obtain ⟨E₁, hE₁E, hHallE₁⟩ :=
    (ex_tau13_compl hEM hHallE).1
  obtain ⟨E₂, _hE₂E, _hHallE₂, hCompl⟩ :=
    ex_tau2_compl hEM hHallE hE₁E hHallE₁ hE₃E hHallE₃
  have hctx : SigmaComplementContext E E₁ E₂ E₃ :=
    sigma_compl_context hM hCompl
  intro X hXE₃ hXne
  let p : ℕ := Nat.minFac (Nat.card X)
  have hXcardNe : Nat.card X ≠ 1 :=
    (X.one_lt_card_iff_ne_bot.mpr hXne).ne'
  have hp : p.Prime := Nat.minFac_prime hXcardNe
  letI : Fact p.Prime := ⟨hp⟩
  have hpX : p ∣ Nat.card X := Nat.minFac_dvd (Nat.card X)
  obtain ⟨Y, hYX, hY⟩ := exists_rankOne_le_of_prime_dvd13 hpX
  have hYne : Y ≠ ⊥ := hY.ne_bot
  have hYE₃ : Y ≤ E₃ := hYX.trans hXE₃
  have hpE₃sub : p ∣ Nat.card (E₃.subgroupOf E) := by
    rw [MathlibSupport.natCard_subgroupOf_eq hE₃E]
    exact hpX.trans (Subgroup.card_dvd_of_le hXE₃)
  have hpTau3 : p ∈ tau3Primes M :=
    hHallE₃.isPiNumber_card hp hpE₃sub
  have hYp : IsPGroup p Y := hY.isPGroup
  have hYproper : Y < ⊤ := mFT_pgroup_proper Y hYp
  have hNYproper : Subgroup.normalizer (Y : Set G) < ⊤ :=
    mFT_norm_proper Y hYne hYproper
  obtain ⟨H, hH, hNYH⟩ :=
    mmax_exists (Subgroup.normalizer (Y : Set G)) hNYproper
  letI : IsCyclic E₃ := hctx.E₃_cyclic
  let YE₃ : Subgroup E₃ := Y.subgroupOf E₃
  have hYE₃char : YE₃.Characteristic :=
    subgroup_characteristic_of_isCyclic13 YE₃
  letI : YE₃.Characteristic := hYE₃char
  have hEnormE₃ : E ≤ Subgroup.normalizer (E₃ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE₃E).mp
      hctx.E₃_normal
  have hEnormY : E ≤ Subgroup.normalizer (Y : Set G) := by
    have hnorm := hEnormE₃.trans
      (characteristic_map_subtype_le_normalizer13 E₃ YE₃)
    simpa [YE₃, Subgroup.map_subgroupOf_eq_of_le hYE₃] using hnorm
  have hEH : E ≤ H := hEnormY.trans hNYH
  have hYM : Y ≤ M := hYE₃.trans (hE₃E.trans hEM)
  have hbase := cent_norm_tau13_mmax hM hEM hHallE
    (Or.inr hpTau3) hYM hYp hH hNYH
  have hE₃derH : E₃ ≤ ⁅H, H⁆ := by
    have hEderH : (_root_.commutator E).map E.subtype ≤ ⁅H, H⁆ := by
      simpa [E.map_subtype_commutator, H.map_subtype_commutator] using
        (Subgroup.commutator_mono hEH hEH)
    exact hctx.E₃_le_commutator.trans hEderH
  have hE₃tau1' : IsPiNumber (tau1Primes H)ᶜ (Nat.card E₃) := by
    intro q hq hqE₃ hqTau1
    have hqAmbient : q ∣ Nat.card (⁅H, H⁆ : Subgroup G) :=
      hqE₃.trans (Subgroup.card_dvd_of_le hE₃derH)
    have hqIntrinsic : q ∣ Nat.card (_root_.commutator H) := by
      rw [← H.map_subtype_commutator,
        Subgroup.card_map_of_injective H.subtype_injective] at hqAmbient
      exact hqAmbient
    exact hqTau1.2.2.2.2 hqIntrinsic
  have hE₃central : E₃ ≤ Subgroup.centralizer
      ((sigmaCore M ⊓ H : Subgroup G) : Set G) :=
    hbase.2.1 E₃
      (le_inf hE₃E (hE₃E.trans hEH)) hE₃tau1'
  apply le_antisymm
  · intro z hz
    exact ⟨hz.1, by
      have hzH : z ∈ H :=
        hNYH (Subgroup.centralizer_le_normalizer (Y : Set G)
          (Subgroup.centralizer_le hYX hz.2))
      have hzK : z ∈ sigmaCore M ⊓ H := ⟨hz.1, hzH⟩
      change z ∈ Subgroup.centralizer (E₃ : Set G)
      exact (Subgroup.mem_centralizer_iff.mpr fun a ha ↦
        (Subgroup.mem_centralizer_iff.mp (hE₃central ha) z hzK).symm)⟩
  · intro z hz
    exact ⟨hz.1, by
      change z ∈ Subgroup.centralizer (X : Set G)
      exact Subgroup.centralizer_le hXE₃ hz.2⟩

/-! ## Theorems 13.4 and 13.5 -/

/-- The source proof of Theorem 13.4, separated from the public statement so
that the conditional choice between the sigma and alpha cores remains local. -/
private theorem cent_tau1Elem_Msigma_direct13
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E P R : Subgroup G} {p r : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau1 : p ∈ tau1Primes M)
    (hr : r.Prime)
    (hP : RankOneLineIn p E P)
    (hR : RankOneLineIn r (centralizerWithin E P) R) :
    centralizerWithin (sigmaCore M) P ≤
      centralizerWithin (sigmaCore M) R := by
  classical
  letI : Fact p.Prime := ⟨hpTau1.1⟩
  have haux :
      ∀ {p r : ℕ} {P R : Subgroup G},
        p ∈ tau1Primes M → r.Prime →
        RankOneLineIn p E P →
        RankOneLineIn r (centralizerWithin E P) R →
        (r ∈ tau1Primes M →
          centralizerWithin (alphaCore M) P ≤
            centralizerWithin (alphaCore M) R →
          centralizerWithin (alphaCore M) P =
            centralizerWithin (alphaCore M) R) →
        centralizerWithin (sigmaCore M) P ≤
          centralizerWithin (sigmaCore M) R := by
    intro p r P R hpTau hr hP hR hsym
    letI : Fact p.Prime := ⟨hpTau.1⟩
    letI : Fact r.Prime := ⟨hr⟩
    have hPE : P ≤ E := hP.1
    have hPelem : IsElementaryAbelianOfRank p 1 P := hP.2
    have hPp : IsPGroup p P := hPelem.isPGroup
    have hPne : P ≠ ⊥ := hPelem.ne_bot
    have hRE : R ≤ E := hR.1.trans (centralizerWithin_le_left E P)
    have hRcentP : R ≤ Subgroup.centralizer (P : Set G) := by
      intro x hx
      exact (hR.1 hx).2
    have hPcentR : P ≤ Subgroup.centralizer (R : Set G) :=
      centralizer_le_symm13 hRcentP
    have hRelem : IsElementaryAbelianOfRank r 1 R := hR.2
    have hRp : IsPGroup r R := hRelem.isPGroup
    have hRne : R ≠ ⊥ := hRelem.ne_bot
    have hPM : P ≤ M := hPE.trans hEM
    have hRM : R ≤ M := hRE.trans hEM
    let alphaCentLe : Prop :=
      centralizerWithin (alphaCore M) P ≤
        centralizerWithin (alphaCore M) R
    let Z : Subgroup G :=
      if alphaCentLe then sigmaCore M else alphaCore M
    let C : Subgroup G := centralizerWithin Z P
    have hZsigma : Z ≤ sigmaCore M := by
      dsimp only [Z]
      by_cases hle : alphaCentLe
      · simpa only [if_pos hle] using
          (show sigmaCore M ≤ sigmaCore M from le_rfl)
      · simp only [if_neg hle]
        exact Malpha_sub_Msigma hM
    have hCsigma : C ≤ sigmaCore M :=
      (centralizerWithin_le_left Z P).trans hZsigma
    have hCM : C ≤ M := hCsigma.trans (sigmaCore_le M)
    have hRnormZ : R ≤ Subgroup.normalizer (Z : Set G) := by
      apply hRM.trans
      dsimp only [Z]
      by_cases hle : alphaCentLe
      · simpa only [if_pos hle] using
          ((Subgroup.normal_subgroupOf_iff_le_normalizer
            (sigmaCore_le M)).mp (sigmaCore_normal M))
      · simpa only [if_neg hle] using
          ((Subgroup.normal_subgroupOf_iff_le_normalizer
            (alphaCore_le M)).mp (alphaCore_normal M))
    have hNormPCent : Subgroup.normalizer (P : Set G) ≤
        Subgroup.normalizer
          (Subgroup.centralizer (P : Set G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (P : Set G))).mp inferInstance
    have hRnormCentP : R ≤ Subgroup.normalizer
        (Subgroup.centralizer (P : Set G) : Set G) :=
      hRcentP.trans (Subgroup.centralizer_le_normalizer (P : Set G)) |>.trans
        hNormPCent
    have hRnormC : R ≤ Subgroup.normalizer (C : Set G) := by
      dsimp only [C, centralizerWithin]
      exact (le_inf hRnormZ hRnormCentP).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hcopCR : (Nat.card C).Coprime (Nat.card R) :=
      (coprime_sigma_compl hEM hHallE).coprime_dvd_left
        (Subgroup.card_dvd_of_le hCsigma) |>.coprime_dvd_right
          (Subgroup.card_dvd_of_le hRE)
    have hsolC : IsSolvable C := by
      letI : IsSolvable M := mmax_sol hM
      exact isSolvable_of_injective
        (Subgroup.inclusion hCM)
        (Subgroup.inclusion_injective hCM)
    have hCcentR : C ≤ Subgroup.centralizer (R : Set G) := by
      apply le_of_normalized_sylow_le13 hRnormC hcopCR hsolC
      intro q hqC S hRnormS
      letI : Fact q.Prime := ⟨hqC.1⟩
      let SG : Subgroup G := (S : Subgroup C).map C.subtype
      have hSGC : SG ≤ C :=
        Subgroup.map_subtype_le (S : Subgroup C)
      have hSGsigma : SG ≤ sigmaCore M := hSGC.trans hCsigma
      have hSGM : SG ≤ M := hSGsigma.trans (sigmaCore_le M)
      have hSGcentP : SG ≤ Subgroup.centralizer (P : Set G) := by
        intro x hx
        exact (hSGC hx).2
      have hPcentSG : P ≤ Subgroup.centralizer (SG : Set G) :=
        centralizer_le_symm13 hSGcentP
      have hSGq : IsPGroup q SG := S.isPGroup'.map C.subtype
      have hSGne : SG ≠ ⊥ := by
        intro hbot
        have hSne : (S : Subgroup C) ≠ ⊥ :=
          S.ne_bot_of_dvd_card hqC.2
        exact hSne ((Subgroup.map_eq_bot_iff_of_injective
          (S : Subgroup C) C.subtype_injective).mp hbot)
      have hqSG : q ∣ Nat.card SG :=
        hSGq.card_eq_or_dvd.resolve_left
          (fun hc ↦ hSGne (Subgroup.card_eq_one.mp hc))
      let Q : Subgroup G := ⁅SG, R⁆
      have hQSG : Q ≤ SG := by
        dsimp only [Q]
        exact Subgroup.le_normalizer_iff_commutator_le_left.mp hRnormS
      have hQq : IsPGroup q Q := hSGq.to_le hQSG
      have hRnormQ : R ≤ Subgroup.normalizer (Q : Set G) := by
        dsimp only [Q]
        exact Subgroup.normalizer_commutator_ge_right SG R
      by_cases hQbot : Q = ⊥
      · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
        simpa only [Q] using hQbot
      have hqSigmaM : q ∈ sigmaPrimes M := by
        apply (sigmaCore_isPiNumber M) hqC.1
        exact hqSG.trans (Subgroup.card_dvd_of_le hSGsigma)
      have hNPproper : Subgroup.normalizer (P : Set G) < ⊤ :=
        mFT_norm_proper P hPne (mFT_pgroup_proper P hPp)
      obtain ⟨H, hH, hNPH⟩ :=
        mmax_exists (Subgroup.normalizer (P : Set G)) hNPproper
      have hPH : P ≤ H := Subgroup.le_normalizer.trans hNPH
      have hRH : R ≤ H :=
        hRcentP.trans (Subgroup.centralizer_le_normalizer (P : Set G)) |>.trans
          hNPH
      have hSGH : SG ≤ H :=
        hSGcentP.trans (Subgroup.centralizer_le_normalizer (P : Set G)) |>.trans
          hNPH
      have hQH : Q ≤ H := hQSG.trans hSGH
      have hQM : Q ≤ M := hQSG.trans hSGM
      have hcommSigmaRne : ⁅sigmaCore M ⊓ H, R⁆ ≠ ⊥ := by
        intro hbot
        apply hQbot
        apply le_bot_iff.mp
        exact (Subgroup.commutator_mono
          (le_inf hSGsigma hSGH) le_rfl).trans_eq
          (by simpa using hbot)
      have hcommInterNe : ⁅sigmaCore M ⊓ H, M ⊓ H⁆ ≠ ⊥ := by
        intro hbot
        apply hcommSigmaRne
        apply le_bot_iff.mp
        exact (Subgroup.commutator_mono le_rfl (le_inf hRM hRH)).trans_eq
          hbot
      have hbase := cent_norm_tau13_mmax hM hEM hHallE
        (Or.inl hpTau) hPM hPp hH hNPH
      have hclass := hbase.2.2 hcommInterNe
      have hpSigmaH : p ∈ sigmaPrimes H := hclass.1
      have hpBetaH : p ∈ betaPrimes H := hclass.2 hpTau
      have hrTauH : r ∈ tau1Primes H := by
        by_contra hrNot
        have hRpi : IsPiNumber (tau1Primes H)ᶜ (Nat.card R) :=
          hRp.isPiNumber_natCard hrNot
        have hRcentral :=
          hbase.2.1 R
            (le_inf hRE hRH) hRpi
        apply hcommSigmaRne
        rw [Subgroup.commutator_comm,
          Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact hRcentral
      have hPbetaH : P ≤ betaCore H := by
        exact le_normal_isHall_of_isPiNumber13
          (betaCore_normal H) (Mbeta_Hall hH) hPH
          (hPp.isPiNumber_natCard hpBetaH)
      have hPalphaH : P ≤ alphaCore H :=
        hPbetaH.trans (betaCore_le_alphaCore H)
      have hPcentQ : P ≤ Subgroup.centralizer (Q : Set G) :=
        hPcentSG.trans (Subgroup.centralizer_le hQSG)
      have hPcentSup : P ≤ Subgroup.centralizer ((R ⊔ Q : Subgroup G) : Set G) := by
        exact le_centralizer_sup13 hPcentR hPcentQ
      have hCentAlphaSupNe :
          centralizerWithin (alphaCore H) (R ⊔ Q) ≠ ⊥ := by
        intro hbot
        apply hPne
        apply le_bot_iff.mp
        exact (le_inf hPalphaH hPcentSup).trans_eq hbot
      have hnotConj : ∀ g : G,
          H ≠ M.map (MulAut.conj g).toMonoidHom :=
        mmax_norm_notJ hM hH hPp hPM hNPH
          (Or.inr (Or.inl hpTau))
      have hHneM : H ≠ M := by
        intro hHM
        exact hnotConj 1
          (hHM.trans (map_conj_one13 M).symm)
      have hSGab : IsMulCommutative SG := by
        by_contra hnoncomm
        have huniq := nonabelian_Uniqueness hSGq hnoncomm
        have hfamily := def_uniq_mmax huniq hM hSGM
        exact hHneM (eq_uniq_mmax hfamily hH hSGH)
      have hcopSGR : (Nat.card SG).Coprime (Nat.card R) :=
        hcopCR.coprime_dvd_left (Subgroup.card_dvd_of_le hSGC)
      have hregular : centralizerWithin Q R = ⊥ := by
        simpa only [Q] using
          centralizerWithin_commutator_eq_bot_of_coprime_abelian_12_12
            hRnormS hcopSGR hSGab
      have hqNotAlphaH : q ∉ alphaPrimes H := by
        intro hqAlphaH
        have hnotConjSymm := not_conjugate_symm13 hnotConj
        exact Set.disjoint_left.mp
          (sigma_disjoint hH hM hnotConjSymm).2.1 hqAlphaH hqSigmaM
      have hRlineH : RankOneLineIn r H R := ⟨hRH, hRelem⟩
      have hrR : r ∣ Nat.card R :=
        hRp.card_eq_or_dvd.resolve_left
          (fun hc ↦ hRne (Subgroup.card_eq_one.mp hc))
      have hrNotSigmaM : r ∉ sigmaPrimes M := by
        have hrEsub : r ∣ Nat.card (E.subgroupOf M) := by
          rw [MathlibSupport.natCard_subgroupOf_eq hEM]
          exact hrR.trans (Subgroup.card_dvd_of_le hRE)
        exact hHallE.isPiNumber_card hr hrEsub
      have hqr : q ≠ r := by
        intro hqr
        exact hrNotSigmaM (hqr ▸ hqSigmaM)
      have hAlphaHne : alphaCore H ≠ ⊥ := by
        intro hbot
        apply hCentAlphaSupNe
        simp [hbot, centralizerWithin]
      have huniqNQ :
          minSimple_max_groups_of (G := G)
              (Subgroup.normalizer (Q : Set G) : Set G) = {H} := by
        by_contra hnonuniq
        have hbad :=
          (cent_Malpha_reg_tau1 hH hrTauH hqC.1 hqr hRH hRelem
            hQbot hRnormQ hregular hnonuniq).1
              hAlphaHne hqNotAlphaH hQq hQH
        exact hCentAlphaSupNe (by simpa [sup_comm] using hbad.2)
      have hHfamily : H ∈ minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (Q : Set G) : Set G) := by
        rw [huniqNQ]
        exact Set.mem_singleton H
      have hembed := sigma_subgroup_embedding hM hqSigmaM hQM hQq hQbot
        hHfamily hHneM
      let I : Subgroup G := M ⊓ H
      let QI : Subgroup I := Q.subgroupOf I
      have hQIpi : IsPGroup q QI :=
        hQq.of_equiv
          (Subgroup.subgroupOfEquivOfLe (le_inf hQM hQH)).symm
      obtain ⟨T, hQIT⟩ := hQIpi.exists_le_sylow
      have hQambient : Q ≤ ambientSylow I T := by
        rw [← Subgroup.map_subgroupOf_eq_of_le (le_inf hQM hQH)]
        exact Subgroup.map_mono hQIT
      have hTdata := hembed.2 T hQambient
      by_cases hqSigmaH : q ∈ sigmaPrimes H
      · have hgood := (if_pos hqSigmaH) ▸ hTdata.2.2
        have htauSub : tau1Primes H ⊆
            tau1Primes M ∪ alphaPrimes M := hgood.2.1
        have hbetaAlphaM : betaCore M = alphaCore M := hgood.2.2.1
        have hAlphaMne : alphaCore M ≠ ⊥ := hgood.2.2.2
        have hrTauM : r ∈ tau1Primes M := by
          rcases htauSub hrTauH with hrTauM | hrAlphaM
          · exact hrTauM
          · exact (hrNotSigmaM (alpha_sub_sigma hM hrAlphaM)).elim
        have hqNotAlphaM : q ∉ alphaPrimes M := by
          intro hqAlphaM
          exact Set.disjoint_left.mp (sigma_disjoint hM hH hnotConj).2.1
            hqAlphaM hqSigmaH
        have hnonuniqM :
            minSimple_max_groups_of (G := G)
                (Subgroup.normalizer (Q : Set G) : Set G) ≠ {M} := by
          rw [huniqNQ]
          intro hsingle
          exact hHneM (Set.singleton_injective hsingle)
        have hMalpha :=
          (cent_Malpha_reg_tau1 hM hrTauM hqC.1 hqr hRM hRelem
            hQbot hRnormQ hregular hnonuniqM).1
              hAlphaMne hqNotAlphaM hQq hQM
        have hAlphaLe : alphaCentLe := by
          by_contra hnot
          have hSGalpha : SG ≤ alphaCore M := by
            exact hSGC.trans (centralizerWithin_le_left Z P) |>.trans
              (by simpa [Z, alphaCentLe, hnot])
          exact hqNotAlphaM
            ((alphaCore_isPiNumber M) hqC.1
              (hqSG.trans (Subgroup.card_dvd_of_le hSGalpha)))
        have hAlphaEq :
            centralizerWithin (alphaCore M) P =
              centralizerWithin (alphaCore M) R :=
          hsym hrTauM hAlphaLe
        let A : Subgroup G := centralizerWithin (alphaCore M) R
        have hAalpha : A ≤ alphaCore M := centralizerWithin_le_left _ _
        have hAcentR : A ≤ Subgroup.centralizer (R : Set G) := by
          intro x hx
          exact hx.2
        have hAcentP : A ≤ Subgroup.centralizer (P : Set G) := by
          change centralizerWithin (alphaCore M) R ≤
            Subgroup.centralizer (P : Set G)
          rw [← hAlphaEq]
          intro x hx
          exact hx.2
        have hSGnormAlpha : SG ≤
            Subgroup.normalizer (alphaCore M : Set G) :=
          hSGM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
            (alphaCore_le M)).mp (alphaCore_normal M))
        have hcommASalpha : ⁅A, SG⁆ ≤ alphaCore M :=
          (Subgroup.commutator_mono hAalpha le_rfl).trans
            (Subgroup.le_normalizer_iff_commutator_le_left.mp hSGnormAlpha)
        have hcommAScentP : ⁅A, SG⁆ ≤
            Subgroup.centralizer (P : Set G) :=
          (Subgroup.commutator_mono hAcentP hSGcentP).trans
            (Subgroup.le_normalizer_iff_commutator_le_left.mp
              (Subgroup.le_normalizer :
                Subgroup.centralizer (P : Set G) ≤
                  Subgroup.normalizer
                    (Subgroup.centralizer (P : Set G) : Set G)))
        have hcommASA : ⁅A, SG⁆ ≤ A := by
          change ⁅A, SG⁆ ≤ centralizerWithin (alphaCore M) R
          rw [← hAlphaEq]
          exact le_inf hcommASalpha hcommAScentP
        have hrot1 : ⁅⁅R, A⁆, SG⁆ = ⊥ := by
          have hRA : ⁅R, A⁆ = ⊥ := by
            rw [Subgroup.commutator_comm,
              Subgroup.commutator_eq_bot_iff_le_centralizer]
            exact hAcentR
          simp only [hRA, Subgroup.commutator_bot_left]
        have hrot2 : ⁅⁅A, SG⁆, R⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          exact hcommASA.trans hAcentR
        have htriple : ⁅⁅SG, R⁆, A⁆ = ⊥ :=
          Subgroup.commutator_commutator_eq_bot_of_rotate hrot1 hrot2
        have hAcentQ : A ≤ Subgroup.centralizer (Q : Set G) := by
          rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
            Subgroup.commutator_comm]
          simpa only [Q] using htriple
        have hAcentSup : A ≤
            Subgroup.centralizer ((R ⊔ Q : Subgroup G) : Set G) := by
          exact le_centralizer_sup13 hAcentR hAcentQ
        have hAwithin : A ≤
            centralizerWithin (alphaCore M) (R ⊔ Q) :=
          le_inf hAalpha hAcentSup
        have hAbot : A = ⊥ :=
          le_bot_iff.mp (hAwithin.trans_eq
            (by simpa [sup_comm] using hMalpha.2))
        exact (hMalpha.1 (by simpa only [A] using hAbot)).elim
      · have hbad := (if_neg hqSigmaH) ▸ hTdata.2.2
        have hHallI : IsHall (sigmaPrimes H)ᶜ
            ((M ⊓ H).subgroupOf H) := hbad.2.2
        have hpI : p ∣ Nat.card ((M ⊓ H).subgroupOf H) := by
          rw [MathlibSupport.natCard_subgroupOf_eq inf_le_right]
          have hpP : p ∣ Nat.card P :=
            hPp.card_eq_or_dvd.resolve_left
              (fun hc ↦ hPne (Subgroup.card_eq_one.mp hc))
          exact hpP.trans
            (Subgroup.card_dvd_of_le (le_inf hPM hPH))
        exact ((hHallI.isPiNumber_card hpTau.1 hpI) hpSigmaH).elim
    have hCZ : C ≤ Z := centralizerWithin_le_left Z P
    have hwithin : C ≤ centralizerWithin Z R :=
      le_inf hCZ hCcentR
    by_cases hle : alphaCentLe
    · simpa only [C, Z, if_pos hle] using hwithin
    · exact (hle (by simpa only [C, Z, if_neg hle] using hwithin)).elim
  have hRlineE : RankOneLineIn r E R :=
    ⟨hR.1.trans (centralizerWithin_le_left E P), hR.2⟩
  have hPcentR : P ≤ Subgroup.centralizer (R : Set G) :=
    centralizer_le_symm13 (show R ≤ Subgroup.centralizer (P : Set G) from
      fun x hx ↦ (hR.1 hx).2)
  have hPlineCentR : RankOneLineIn p (centralizerWithin E R) P :=
    ⟨le_inf hP.1 hPcentR, hP.2⟩
  have hsym : r ∈ tau1Primes M →
      centralizerWithin (alphaCore M) P ≤
        centralizerWithin (alphaCore M) R →
      centralizerWithin (alphaCore M) P =
        centralizerWithin (alphaCore M) R := by
    intro hrTau hPR
    have hRP := haux hrTau hpTau1.1 hRlineE hPlineCentR
      (fun _ hRP ↦ le_antisymm hRP hPR)
    apply le_antisymm hPR
    intro x hx
    have hxSigmaR : x ∈ centralizerWithin (sigmaCore M) R :=
      ⟨(Malpha_sub_Msigma hM hx.1), hx.2⟩
    have hxSigmaP := hRP hxSigmaR
    exact ⟨hx.1, hxSigmaP.2⟩
  exact haux hpTau1 hr hP hR hsym

/-- `BGsection13.v: cent_tau1Elem_Msigma`, Bender--Glauberman
Theorem 13.4. -/
theorem cent_tau1Elem_Msigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E P R : Subgroup G} {p r : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau1 : p ∈ tau1Primes M)
    (hr : r.Prime)
    (hP : RankOneLineIn p E P)
    (hR : RankOneLineIn r (centralizerWithin E P) R) :
    centralizerWithin (sigmaCore M) P ≤
      centralizerWithin (sigmaCore M) R := by
  exact cent_tau1Elem_Msigma_direct13
    hM hEM hHallE hpTau1 hr hP hR

/-- `BGsection13.v: tau1_primact_Msigma`, Bender--Glauberman
Theorem 13.5. -/
theorem tau1_primact_Msigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₁ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hE₁E : E₁ ≤ E)
    (hHallE₁ : IsHall (tau1Primes M) (E₁.subgroupOf E)) :
    IsPrimeAction (sigmaCore M) E₁ := by
  obtain ⟨E₃, hE₃E, hHallE₃⟩ :=
    (ex_tau13_compl hEM hHallE).2
  obtain ⟨E₂, _hE₂E, _hHallE₂, hCompl⟩ :=
    ex_tau2_compl hEM hHallE hE₁E hHallE₁ hE₃E hHallE₃
  have hctx : SigmaComplementContext E E₁ E₂ E₃ :=
    sigma_compl_context hM hCompl
  intro X hXE₁ hXne
  let p : ℕ := Nat.minFac (Nat.card X)
  have hXcardNe : Nat.card X ≠ 1 :=
    (X.one_lt_card_iff_ne_bot.mpr hXne).ne'
  have hp : p.Prime := Nat.minFac_prime hXcardNe
  letI : Fact p.Prime := ⟨hp⟩
  have hpX : p ∣ Nat.card X := Nat.minFac_dvd (Nat.card X)
  obtain ⟨P, hPX, hP⟩ := exists_rankOne_le_of_prime_dvd13 hpX
  have hPE₁ : P ≤ E₁ := hPX.trans hXE₁
  have hPE : P ≤ E := hPE₁.trans hE₁E
  have hpE₁sub : p ∣ Nat.card (E₁.subgroupOf E) := by
    rw [MathlibSupport.natCard_subgroupOf_eq hE₁E]
    exact hpX.trans (Subgroup.card_dvd_of_le hXE₁)
  have hpTau1 : p ∈ tau1Primes M :=
    hHallE₁.isPiNumber_card hp hpE₁sub
  have hPline : RankOneLineIn p E P := ⟨hPE, hP⟩
  letI : IsCyclic E₁ := hctx.E₁_cyclic
  have hPE₁cent : E₁ ≤ Subgroup.centralizer (P : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val
      (mul_comm (⟨a, ha⟩ : E₁) ⟨b, hPE₁ hb⟩).symm
  have hE₁central : E₁ ≤ Subgroup.centralizer
      ((centralizerWithin (sigmaCore M) P : Subgroup G) : Set G) := by
    apply le_of_sylow_le13
    intro r hrE₁ S
    letI : Fact r.Prime := ⟨hrE₁.1⟩
    let SG : Subgroup G := (S : Subgroup E₁).map E₁.subtype
    have hSGE₁ : SG ≤ E₁ :=
      Subgroup.map_subtype_le (S : Subgroup E₁)
    have hSGne : SG ≠ ⊥ := by
      intro hbot
      exact S.ne_bot_of_dvd_card hrE₁.2
        ((Subgroup.map_eq_bot_iff_of_injective
          (S : Subgroup E₁) E₁.subtype_injective).mp hbot)
    have hSGp : IsPGroup r SG := S.isPGroup'.map E₁.subtype
    obtain ⟨R, hRSG, hR⟩ :=
      exists_rankOne_le_of_isPGroup_ne_bot13 hSGp hSGne
    have hRE₁ : R ≤ E₁ := hRSG.trans hSGE₁
    have hRE : R ≤ E := hRE₁.trans hE₁E
    have hRPcent : R ≤ Subgroup.centralizer (P : Set G) :=
      hRE₁.trans hPE₁cent
    have hRline : RankOneLineIn r (centralizerWithin E P) R :=
      ⟨le_inf hRE hRPcent, hR⟩
    have hcentPR : centralizerWithin (sigmaCore M) P ≤
        centralizerWithin (sigmaCore M) R :=
      cent_tau1Elem_Msigma hM hEM hHallE hpTau1
        hrE₁.1 hPline hRline
    have hrE₁sub : r ∣ Nat.card (E₁.subgroupOf E) := by
      rw [MathlibSupport.natCard_subgroupOf_eq hE₁E]
      exact hrE₁.2
    have hrTau1 : r ∈ tau1Primes M :=
      hHallE₁.isPiNumber_card hrE₁.1 hrE₁sub
    let eE₁E : E₁.subgroupOf E ≃* E₁ :=
      Subgroup.subgroupOfEquivOfLe hE₁E
    let SE : Sylow r (E₁.subgroupOf E) :=
      S.mapSurjective (f := eE₁E.symm.toMonoidHom)
        eE₁E.symm.surjective
    have hSEcoe :
        (SE : Subgroup (E₁.subgroupOf E)) =
          (S : Subgroup E₁).map eE₁E.symm.toMonoidHom := by
      change
        ((S.mapSurjective (f := eE₁E.symm.toMonoidHom)
            eE₁E.symm.surjective : Sylow r (E₁.subgroupOf E)) :
          Subgroup (E₁.subgroupOf E)) = _
      rw [Sylow.coe_mapSurjective]
    obtain ⟨TE, hTE⟩ := exists_sylow_eq_map_of_sylow_hall13
      (K := E) (A := E₁.subgroupOf E) hrE₁.1
        hHallE₁ hrTau1 SE
    have hTEambient :
        (TE : Subgroup E).map E.subtype = SG := by
      rw [hTE, hSEcoe]
      dsimp only [SG]
      rw [Subgroup.map_map, Subgroup.map_map]
      apply congrArg (fun f : E₁ →* G ↦ (S : Subgroup E₁).map f)
      ext x
      rfl
    have hSGsylE : IsSylowSubgroupOf r SG E :=
      ⟨TE, hTEambient.symm⟩
    have hSGcyc : IsCyclic SG := by
      let eSG : (SG.subgroupOf E₁) ≃* SG :=
        Subgroup.subgroupOfEquivOfLe hSGE₁
      have hcycSub : IsCyclic (SG.subgroupOf E₁) := by infer_instance
      exact eSG.isCyclic.mp hcycSub
    have hprimeSG := cyclic_primact_Msigma hM hEM hHallE
      hSGsylE hSGcyc
    have hcentRSG : centralizerWithin (sigmaCore M) R =
        centralizerWithin (sigmaCore M) SG :=
      hprimeSG.centralizer_eq hRSG hR.ne_bot
    have hcentPSG : centralizerWithin (sigmaCore M) P ≤
        centralizerWithin (sigmaCore M) SG := by
      rw [← hcentRSG]
      exact hcentPR
    intro a ha
    change a ∈ Subgroup.centralizer
      ((centralizerWithin (sigmaCore M) P : Subgroup G) : Set G)
    exact Subgroup.mem_centralizer_iff.mpr fun z hz ↦
      (Subgroup.mem_centralizer_iff.mp (hcentPSG hz).2 a ha).symm
  apply le_antisymm
  · intro z hz
    exact ⟨hz.1, by
      change z ∈ Subgroup.centralizer (E₁ : Set G)
      exact Subgroup.mem_centralizer_iff.mpr fun a ha ↦
        (Subgroup.mem_centralizer_iff.mp
          (hE₁central ha) z ⟨hz.1,
            Subgroup.centralizer_le hPX hz.2⟩).symm⟩
  · intro z hz
    exact ⟨hz.1, by
      change z ∈ Subgroup.centralizer (X : Set G)
      exact Subgroup.centralizer_le hXE₁ hz.2⟩

/-- The dichotomy used by Lemma 13.6: a tau-one fixed line in the sigma
core either has beta prime or lies in the derived sigma core. -/
private theorem tau1_centralizer_beta_or_derived13
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₁ X : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hE₁E : E₁ ≤ E)
    (hHallE₁ : IsHall (tau1Primes M) (E₁.subgroupOf E))
    (hE₁ne : E₁ ≠ ⊥)
    (hXfull : X ≤ centralizerWithin (sigmaCore M) E₁)
    (hX : IsElementaryAbelianOfRank q 1 X) :
    q ∈ betaPrimes M ∨
      X ≤ (_root_.commutator (sigmaCore M)).map
        (sigmaCore M).subtype := by
  classical
  by_cases hqBeta : q ∈ betaPrimes M
  · exact Or.inl hqBeta
  · apply Or.inr
    by_contra hnotDerived
    let D : Subgroup G :=
      (_root_.commutator (sigmaCore M)).map
        (sigmaCore M).subtype
    have hnotD : ¬ X ≤ D := by
      simpa only [D] using hnotDerived
    have hEnormSigma :
        E ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
      hEM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (sigmaCore_le M)).mp (sigmaCore_normal M))
    have hsolSigma : IsSolvable (sigmaCore M) := by
      letI : IsSolvable M := mmax_sol hM
      exact isSolvable_of_injective
        (Subgroup.inclusion (sigmaCore_le M))
        (Subgroup.inclusion_injective (sigmaCore_le M))
    have hcopSigmaE :
        (Nat.card (sigmaCore M)).Coprime (Nat.card E) :=
      coprime_sigma_compl hEM hHallE
    obtain ⟨SQ, hEnormSQ⟩ :=
      exists_sylow_normalized_of_coprime_of_isSolvable
        (p := q) hEnormSigma hcopSigmaE hsolSigma
    let SQG : Subgroup G :=
      (SQ : Subgroup (sigmaCore M)).map (sigmaCore M).subtype
    have hSQsigma : SQG ≤ sigmaCore M := by
      dsimp only [SQG]
      exact Subgroup.map_subtype_le (SQ : Subgroup (sigmaCore M))

    let Eder : Subgroup G :=
      (_root_.commutator E).map E.subtype
    obtain ⟨H, hHSigma, hHHall, hEderCentH⟩ :=
      der_compl_cent_beta' hM hEM hHallE
    let QH : Sylow q (H.subgroupOf (sigmaCore M)) :=
      Classical.choice Sylow.nonempty
    obtain ⟨T, hT⟩ :=
      exists_sylow_eq_map_of_sylow_hall13
        (K := sigmaCore M)
        (A := H.subgroupOf (sigmaCore M))
        (p := q) (Fact.out : q.Prime) hHHall
        (show q ∈ (betaPrimes M)ᶜ from hqBeta) QH
    let TG : Subgroup G :=
      (T : Subgroup (sigmaCore M)).map (sigmaCore M).subtype
    have hTGH : TG ≤ H := by
      dsimp only [TG]
      rw [hT]
      exact
        (Subgroup.map_mono
          (Subgroup.map_subtype_le
            (QH : Subgroup (H.subgroupOf (sigmaCore M))))).trans_eq
          (Subgroup.map_subgroupOf_eq_of_le hHSigma)
    have hEderCentTG :
        Eder ≤ Subgroup.centralizer (TG : Set G) :=
      hEderCentH.trans (Subgroup.centralizer_le hTGH)
    have hTGcentEder :
        TG ≤ Subgroup.centralizer (Eder : Set G) :=
      Subgroup.le_centralizer_iff.mp hEderCentTG
    have hEderNormTG :
        Eder ≤ Subgroup.normalizer (TG : Set G) :=
      hEderCentTG.trans
        (Subgroup.centralizer_le_normalizer (TG : Set G))
    have hEderE : Eder ≤ E := by
      dsimp only [Eder]
      exact Subgroup.map_subtype_le (_root_.commutator E)
    have hEderNormSigma :
        Eder ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
      hEderE.trans hEnormSigma
    have hcopSigmaEder :
        (Nat.card (sigmaCore M)).Coprime (Nat.card Eder) :=
      hcopSigmaE.coprime_dvd_right
        (Subgroup.card_dvd_of_le hEderE)
    have hEderNormSQ :
        Eder ≤ Subgroup.normalizer (SQG : Set G) := by
      simpa only [SQG] using hEderE.trans hEnormSQ
    obtain ⟨c, hc, hSQconj⟩ :=
      exists_mem_inf_centralizer_conj_sylow_of_coprime_of_isSolvable
        hEderNormSigma hcopSigmaEder hsolSigma SQ T
        hEderNormSQ hEderNormTG
    have hSQconjG :
        SQG = TG.map (MulAut.conj c⁻¹).toMonoidHom := by
      simpa only [SQG, TG] using hSQconj
    have hcInvNormCent :
        c⁻¹ ∈ Subgroup.normalizer
          (Subgroup.centralizer (Eder : Set G) : Set G) :=
      Subgroup.le_normalizer
        ((Subgroup.centralizer (Eder : Set G)).inv_mem hc.2)
    have hmapCentEder :
        (Subgroup.centralizer (Eder : Set G)).map
            (MulAut.conj c⁻¹).toMonoidHom =
          Subgroup.centralizer (Eder : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hcInvNormCent
    have hSQcentEder :
        SQG ≤ Subgroup.centralizer (Eder : Set G) := by
      calc
        SQG = TG.map (MulAut.conj c⁻¹).toMonoidHom := hSQconjG
        _ ≤ (Subgroup.centralizer (Eder : Set G)).map
              (MulAut.conj c⁻¹).toMonoidHom :=
          Subgroup.map_mono hTGcentEder
        _ = Subgroup.centralizer (Eder : Set G) := hmapCentEder

    have hXsigma : X ≤ sigmaCore M :=
      hXfull.trans (centralizerWithin_le_left (sigmaCore M) E₁)
    have hXcentE₁ :
        X ≤ Subgroup.centralizer (E₁ : Set G) :=
      hXfull.trans inf_le_right
    have hE₁centX :
        E₁ ≤ Subgroup.centralizer (X : Set G) :=
      Subgroup.le_centralizer_iff.mp hXcentE₁
    have hE₁normX :
        E₁ ≤ Subgroup.normalizer (X : Set G) :=
      hE₁centX.trans
        (Subgroup.centralizer_le_normalizer (X : Set G))
    have hE₁normSigma :
        E₁ ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
      hE₁E.trans hEnormSigma
    have hcopSigmaE₁ :
        (Nat.card (sigmaCore M)).Coprime (Nat.card E₁) :=
      hcopSigmaE.coprime_dvd_right
        (Subgroup.card_dvd_of_le hE₁E)
    obtain ⟨V, hE₁normV, hXV⟩ :=
      exists_normalized_sylow_ge_of_coprime_of_isSolvable
        (p := q) hE₁normSigma hcopSigmaE₁ hsolSigma
        hXsigma hX.isPGroup hE₁normX
    obtain ⟨x, hx, hSQV⟩ :=
      exists_mem_inf_centralizer_conj_sylow_of_coprime_of_isSolvable
        hE₁normSigma hcopSigmaE₁ hsolSigma SQ V
        (hE₁E.trans hEnormSQ) hE₁normV
    let Y : Subgroup G :=
      X.map (MulAut.conj x⁻¹).toMonoidHom
    have hYSQ : Y ≤ SQG := by
      calc
        Y ≤
            (((V : Subgroup (sigmaCore M)).map
                (sigmaCore M).subtype : Subgroup G).map
              (MulAut.conj x⁻¹).toMonoidHom) := by
          dsimp only [Y]
          exact Subgroup.map_mono hXV
        _ = SQG := by
          simpa only [SQG] using hSQV.symm
    have hYSigma : Y ≤ sigmaCore M :=
      hYSQ.trans hSQsigma
    have hY : IsElementaryAbelianOfRank q 1 Y := by
      dsimp only [Y]
      exact hX.map_of_injective
        (MulAut.conj x⁻¹).toMonoidHom
        (MulAut.conj x⁻¹).injective
    have hYcentEder :
        Y ≤ Subgroup.centralizer (Eder : Set G) :=
      hYSQ.trans hSQcentEder
    have hxInvNormCentE₁ :
        x⁻¹ ∈ Subgroup.normalizer
          (Subgroup.centralizer (E₁ : Set G) : Set G) :=
      Subgroup.le_normalizer
        ((Subgroup.centralizer (E₁ : Set G)).inv_mem hx.2)
    have hmapCentE₁ :
        (Subgroup.centralizer (E₁ : Set G)).map
            (MulAut.conj x⁻¹).toMonoidHom =
          Subgroup.centralizer (E₁ : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxInvNormCentE₁
    have hYcentE₁ :
        Y ≤ Subgroup.centralizer (E₁ : Set G) := by
      dsimp only [Y]
      exact (Subgroup.map_mono hXcentE₁).trans_eq hmapCentE₁

    have hSigmaNormD :
        sigmaCore M ≤ Subgroup.normalizer (D : Set G) := by
      have hnorm :
          Subgroup.normalizer (sigmaCore M : Set G) ≤
            Subgroup.normalizer (D : Set G) := by
        simpa only [D] using
          characteristic_map_subtype_le_normalizer13
            (sigmaCore M) (_root_.commutator (sigmaCore M))
      exact (Subgroup.le_normalizer : sigmaCore M ≤
        Subgroup.normalizer (sigmaCore M : Set G)).trans hnorm
    have hxNormD : x ∈ Subgroup.normalizer (D : Set G) :=
      hSigmaNormD hx.1
    have hDmap :
        D.map (MulAut.conj x).toMonoidHom = D :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxNormD
    have hYback :
        Y.map (MulAut.conj x).toMonoidHom = X := by
      have hback := map_conj_inv_map_conj13 X x⁻¹
      simpa only [Y, inv_inv] using hback
    have hYnotD : ¬ Y ≤ D := by
      intro hYD
      apply hnotD
      calc
        X = Y.map (MulAut.conj x).toMonoidHom := hYback.symm
        _ ≤ D.map (MulAut.conj x).toMonoidHom :=
          Subgroup.map_mono hYD
        _ = D := hDmap

    obtain ⟨E₃, hE₃E, hHallE₃⟩ :=
      (ex_tau13_compl hEM hHallE).2
    obtain ⟨E₂, hE₂E, hHallE₂, hCompl⟩ :=
      ex_tau2_compl hEM hHallE hE₁E hHallE₁ hE₃E hHallE₃
    have hctx : SigmaComplementContext E E₁ E₂ E₃ :=
      sigma_compl_context hM hCompl
    have hEdecomp : E₃ ⊔ (E₂ ⊔ E₁) = E := by
      have htop :
          E₃.subgroupOf E ⊔ (E₂ ⊔ E₁).subgroupOf E = ⊤ :=
        hctx.E₃_E₂₁_sdprod.2.2.2.sup_eq_top
      calc
        E₃ ⊔ (E₂ ⊔ E₁) =
            (E₃.subgroupOf E).map E.subtype ⊔
              ((E₂ ⊔ E₁).subgroupOf E).map E.subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le hE₃E,
            Subgroup.map_subgroupOf_eq_of_le
              (sup_le hE₂E hE₁E)]
        _ =
            (E₃.subgroupOf E ⊔
              (E₂ ⊔ E₁).subgroupOf E).map E.subtype := by
          rw [Subgroup.map_sup]
        _ = (⊤ : Subgroup E).map E.subtype :=
          congrArg (Subgroup.map E.subtype) htop
        _ = E := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hE₂ne : E₂ ≠ ⊥ := by
      intro hE₂bot
      have hEeq : E₃ ⊔ E₁ = E := by
        simpa only [hE₂bot, bot_sup_eq] using hEdecomp
      have hE₃Eder : E₃ ≤ Eder := by
        simpa only [Eder] using hctx.E₃_le_commutator
      have hYcentE₃ :
          Y ≤ Subgroup.centralizer (E₃ : Set G) :=
        hYcentEder.trans (Subgroup.centralizer_le hE₃Eder)
      have hE₃centY :
          E₃ ≤ Subgroup.centralizer (Y : Set G) :=
        Subgroup.le_centralizer_iff.mp hYcentE₃
      have hE₁centY :
          E₁ ≤ Subgroup.centralizer (Y : Set G) :=
        Subgroup.le_centralizer_iff.mp hYcentE₁
      have hEcentY :
          E ≤ Subgroup.centralizer (Y : Set G) := by
        rw [← hEeq]
        exact sup_le hE₃centY hE₁centY
      have hYcentE :
          Y ≤ Subgroup.centralizer (E : Set G) :=
        Subgroup.le_centralizer_iff.mp hEcentY
      have hYwithinE :
          Y ≤ centralizerWithin (sigmaCore M) E :=
        le_inf hYSigma hYcentE
      have hYderived :=
        hYwithinE.trans (sigma_compl_embedding hM hEM hHallE).1
      exact hYnotD (by simpa only [D] using hYderived)

    have hE₂cardNe : Nat.card E₂ ≠ 1 :=
      fun hc ↦ hE₂ne (Subgroup.card_eq_one.mp hc)
    obtain ⟨s, hs, hsE₂⟩ :=
      Nat.exists_prime_and_dvd hE₂cardNe
    letI : Fact s.Prime := ⟨hs⟩
    have hsE₂sub : s ∣ Nat.card (E₂.subgroupOf E) := by
      rw [MathlibSupport.natCard_subgroupOf_eq hE₂E]
      exact hsE₂
    have hsTau : s ∈ tau2Primes M :=
      hHallE₂.isPiNumber_card hs hsE₂sub
    obtain ⟨A, hAE, hAM, hA⟩ :=
      ex_tau2Elem hEM hHallE hsTau
    have hTau := tau2_context hM hsTau hAM hA
    have hTauCompl :=
      tau2_compl_context hM hEM hHallE hsTau hAE hA

    have hE₁cardNe : Nat.card E₁ ≠ 1 :=
      fun hc ↦ hE₁ne (Subgroup.card_eq_one.mp hc)
    obtain ⟨r, hr, hrE₁⟩ :=
      Nat.exists_prime_and_dvd hE₁cardNe
    letI : Fact r.Prime := ⟨hr⟩
    obtain ⟨R, hRE₁, hR⟩ :=
      exists_rankOne_le_of_prime_dvd13 hrE₁
    have hrE₁sub : r ∣ Nat.card (E₁.subgroupOf E) := by
      rw [MathlibSupport.natCard_subgroupOf_eq hE₁E]
      exact hrE₁
    have hrTau : r ∈ tau1Primes M :=
      hHallE₁.isPiNumber_card hr hrE₁sub
    have hRline : RankOneLineIn r E R :=
      ⟨hRE₁.trans hE₁E, hR⟩

    let C : Subgroup G := centralizerWithin A E₁
    have hCcentY :
        C ≤ Subgroup.centralizer (Y : Set G) := by
      intro a ha
      by_cases ha1 : a = 1
      · subst a
        exact Subgroup.one_mem _
      · let L : Subgroup G := Subgroup.zpowers a
        have hapow : a ^ s = 1 :=
          congrArg Subtype.val (hA.pow_eq_one ⟨a, ha.1⟩)
        have haorder : orderOf a = s :=
          ((Nat.dvd_prime hs).mp
            (orderOf_dvd_of_pow_eq_one hapow)).resolve_left
              (by simpa [orderOf_eq_one_iff] using ha1)
        have hLcard : Nat.card L = s := by
          dsimp only [L]
          rw [Nat.card_zpowers, haorder]
        have hLrank : IsElementaryAbelianOfRank s 1 L :=
          isElementaryAbelianOfRank_one_of_card_eq_prime hLcard
        have haCentR :
            a ∈ Subgroup.centralizer (R : Set G) :=
          Subgroup.centralizer_le hRE₁ ha.2
        have hLline :
            RankOneLineIn s (centralizerWithin E R) L := by
          exact ⟨le_inf
            ((Subgroup.zpowers_le.mpr ha.1).trans hAE)
            (Subgroup.zpowers_le.mpr haCentR), hLrank⟩
        have hcentRL :
            centralizerWithin (sigmaCore M) R ≤
              centralizerWithin (sigmaCore M) L :=
          cent_tau1Elem_Msigma hM hEM hHallE
            hrTau hs hRline hLline
        have hYcentR :
            Y ≤ Subgroup.centralizer (R : Set G) :=
          hYcentE₁.trans (Subgroup.centralizer_le hRE₁)
        have hYwithinR :
            Y ≤ centralizerWithin (sigmaCore M) R :=
          le_inf hYSigma hYcentR
        have hYwithinL :
            Y ≤ centralizerWithin (sigmaCore M) L :=
          hYwithinR.trans hcentRL
        have hLcentY :
            L ≤ Subgroup.centralizer (Y : Set G) :=
          Subgroup.le_centralizer_iff.mp
            (hYwithinL.trans inf_le_right)
        exact hLcentY (Subgroup.mem_zpowers a)

    have hE₁tau1 :
        IsPiNumber (tau1Primes M) (Nat.card E₁) := by
      rw [← MathlibSupport.natCard_subgroupOf_eq hE₁E]
      exact hHallE₁.isPiNumber_card
    have hE₁tau2' :
        IsPiNumber (tau2Primes M)ᶜ (Nat.card E₁) :=
      hE₁tau1.mono (tau2'1 M)
    have hAtau2 :
        IsPiNumber (tau2Primes M) (Nat.card A) :=
      hA.isPGroup.isPiNumber_natCard hsTau
    have hcopAE₁ :
        (Nat.card A).Coprime (Nat.card E₁) :=
      hAtau2.coprime_compl hE₁tau2'
    have hE₁normA :
        E₁ ≤ Subgroup.normalizer (A : Set G) :=
      hE₁E.trans hTauCompl.A_normalizer_le
    letI : IsMulCommutative A := hA.commutative
    letI : IsSolvable A :=
      Submission.OddOrder.MathlibSupport.isSolvable_of_comm
        (fun a b : A ↦ mul_comm a b)
    have hAdecomp :
        A ≤ ⁅E₁, A⁆ ⊔ centralizerWithin A E₁ :=
      le_commutator_sup_centralizerWithin_of_coprime
        (K := A) (R := E₁) hE₁normA hcopAE₁
    have hcommLeEder : ⁅E₁, A⁆ ≤ Eder := by
      simpa only [Eder, E.map_subtype_commutator] using
        (Subgroup.commutator_mono hE₁E hAE)
    have hYcentComm :
        Y ≤ Subgroup.centralizer ((⁅E₁, A⁆ : Subgroup G) : Set G) :=
      hYcentEder.trans
        (Subgroup.centralizer_le hcommLeEder)
    have hcommCentY :
        ⁅E₁, A⁆ ≤ Subgroup.centralizer (Y : Set G) :=
      Subgroup.le_centralizer_iff.mp hYcentComm
    have hACentY :
        A ≤ Subgroup.centralizer (Y : Set G) :=
      hAdecomp.trans (sup_le hcommCentY hCcentY)
    have hYcentA :
        Y ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.le_centralizer_iff.mp hACentY
    have hYwithinA :
        Y ≤ centralizerWithin (sigmaCore M) A :=
      le_inf hYSigma hYcentA
    have hYbotLe : Y ≤ ⊥ := by
      rw [← hTau.centralizerWithin_eq_bot]
      exact hYwithinA
    exact hY.ne_bot (le_bot_iff.mp hYbotLe)

/-! ## Lemmas 13.6 and 13.7 -/

/-- `BGsection13.v: cent_cent_Msigma_tau1_uniq`, Bender--Glauberman
Lemma 13.6. -/
theorem cent_cent_Msigma_tau1_uniq
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₁ P X : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hE₁E : E₁ ≤ E)
    (hHallE₁ : IsHall (tau1Primes M) (E₁.subgroupOf E))
    (hPE₁ : P ≤ E₁) (hPne : P ≠ ⊥)
    (hXcent : X ≤ centralizerWithin (sigmaCore M) P)
    (hX : IsElementaryAbelianOfRank q 1 X) :
    minSimple_max_groups_of (G := G)
        (Subgroup.centralizer (X : Set G) : Set G) = {M} ∧
      ∀ S : Sylow q ((sigmaCore M).subgroupOf M),
        minSimple_max_groups_of (G := G)
          ((((S : Subgroup ((sigmaCore M).subgroupOf M)).map
                ((sigmaCore M).subgroupOf M).subtype).map M.subtype :
              Subgroup G) : Set G) = {M} := by
  have hprime : IsPrimeAction (sigmaCore M) E₁ :=
    tau1_primact_Msigma hM hEM hHallE hE₁E hHallE₁
  have hcentEq : centralizerWithin (sigmaCore M) P =
      centralizerWithin (sigmaCore M) E₁ :=
    hprime.centralizer_eq hPE₁ hPne
  have hE₁ne : E₁ ≠ ⊥ := by
    intro hE₁
    apply hPne
    exact le_bot_iff.mp (hPE₁.trans_eq hE₁)
  have hXfull : X ≤ centralizerWithin (sigmaCore M) E₁ := by
    rw [← hcentEq]
    exact hXcent
  have hXsigma : X ≤ sigmaCore M :=
    hXcent.trans (centralizerWithin_le_left (sigmaCore M) P)
  have hXM : X ≤ M := hXsigma.trans (sigmaCore_le M)
  have hcase := tau1_centralizer_beta_or_derived13
    hM hEM hHallE hE₁E hHallE₁ hE₁ne hXfull hX
  have huniq := cent_der_sigma_uniq hM hXM hX hcase
  exact huniq

/-- Direct source proof of Lemma 13.7, including the corrected
equal-centralizer branch from the Coq development. -/
private theorem tau13_join_prime_action_direct13
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (hctx : SigmaComplementContext E E₁ E₂ E₃)
    (hprime₁ : IsPrimeAction (sigmaCore M) E₁)
    (hprime₃ : IsPrimeAction (sigmaCore M) E₃)
    (hnotRegular : ¬ IsSemiregularConjugation E₃ E₁) :
    IsPrimeAction (sigmaCore M) (E₃ ⊔ E₁) := by
  classical
  let J : Subgroup G := E₃ ⊔ E₁
  change IsPrimeAction (sigmaCore M) J
  letI : IsCyclic E₁ := hctx.E₁_cyclic
  letI : IsCyclic E₃ := hctx.E₃_cyclic
  have hJE : J ≤ E := by
    dsimp only [J]
    exact sup_le hCompl.E₃_le_E hCompl.E₁_le_E
  have hJM : J ≤ M := hJE.trans hCompl.E_le_M
  have hE₁J : E₁ ≤ J := by
    dsimp only [J]
    exact le_sup_right
  have hE₃J : E₃ ≤ J := by
    dsimp only [J]
    exact le_sup_left
  have hEnormE₃ : E ≤ Subgroup.normalizer (E₃ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCompl.E₃_le_E).mp
      hctx.E₃_normal
  have hMnormSigma :
      M ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (sigmaCore_le M)).mp (sigmaCore_normal M)

  simp only [IsSemiregularConjugation, not_forall] at hnotRegular
  obtain ⟨a, haNe, b, hfix, hbNe⟩ := hnotRegular
  let A₀ : Subgroup G := Subgroup.zpowers (a : G)
  let B₀ : Subgroup G := Subgroup.zpowers (b : G)
  have hA₀ne : A₀ ≠ ⊥ := by
    dsimp only [A₀]
    intro hbot
    apply haNe
    apply Subtype.ext
    exact Subgroup.zpowers_eq_bot.mp hbot
  have hB₀ne : B₀ ≠ ⊥ := by
    dsimp only [B₀]
    intro hbot
    apply hbNe
    apply Subtype.ext
    exact Subgroup.zpowers_eq_bot.mp hbot
  have hA₀E₁ : A₀ ≤ E₁ :=
    Subgroup.zpowers_le.mpr a.property
  have hB₀E₃ : B₀ ≤ E₃ :=
    Subgroup.zpowers_le.mpr b.property
  let p : ℕ := Nat.minFac (Nat.card A₀)
  let r : ℕ := Nat.minFac (Nat.card B₀)
  have hp : p.Prime :=
    Nat.minFac_prime ((A₀.one_lt_card_iff_ne_bot.mpr hA₀ne).ne')
  have hr : r.Prime :=
    Nat.minFac_prime ((B₀.one_lt_card_iff_ne_bot.mpr hB₀ne).ne')
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact r.Prime := ⟨hr⟩
  have hpA₀ : p ∣ Nat.card A₀ := Nat.minFac_dvd (Nat.card A₀)
  have hrB₀ : r ∣ Nat.card B₀ := Nat.minFac_dvd (Nat.card B₀)
  obtain ⟨P, hPA₀, hP⟩ :=
    exists_rankOne_le_of_prime_dvd13 hpA₀
  obtain ⟨R, hRB₀, hR⟩ :=
    exists_rankOne_le_of_prime_dvd13 hrB₀
  have hPE₁ : P ≤ E₁ := hPA₀.trans hA₀E₁
  have hPE : P ≤ E := hPE₁.trans hCompl.E₁_le_E
  have hRE₃ : R ≤ E₃ := hRB₀.trans hB₀E₃
  have hRE : R ≤ E := hRE₃.trans hCompl.E₃_le_E
  have hPne : P ≠ ⊥ := hP.ne_bot
  have hRne : R ≠ ⊥ := hR.ne_bot
  have hpE₁sub : p ∣ Nat.card (E₁.subgroupOf E) := by
    rw [MathlibSupport.natCard_subgroupOf_eq hCompl.E₁_le_E]
    exact hpA₀.trans (Subgroup.card_dvd_of_le hA₀E₁)
  have hrE₃sub : r ∣ Nat.card (E₃.subgroupOf E) := by
    rw [MathlibSupport.natCard_subgroupOf_eq hCompl.E₃_le_E]
    exact hrB₀.trans (Subgroup.card_dvd_of_le hB₀E₃)
  have hpTau₁ : p ∈ tau1Primes M :=
    hCompl.hall_E₁.isPiNumber_card hp hpE₁sub
  have hrTau₃ : r ∈ tau3Primes M :=
    hCompl.hall_E₃.isPiNumber_card hr hrE₃sub
  have hab : Commute (a : G) (b : G) := by
    rw [Commute]
    calc
      (a : G) * (b : G) =
          ((a : G) * (b : G) * (a : G)⁻¹) * (a : G) := by group
      _ = (b : G) * (a : G) := by rw [hfix]
  have hRPcent : R ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hRB₀ hx)
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hPA₀ hy)
    exact (hab.zpow_zpow m n).eq
  have hPline : RankOneLineIn p E P := ⟨hPE, hP⟩
  have hRline : RankOneLineIn r (centralizerWithin E P) R :=
    ⟨le_inf hRE hRPcent, hR⟩
  have hcentPR :
      centralizerWithin (sigmaCore M) P ≤
        centralizerWithin (sigmaCore M) R :=
    cent_tau1Elem_Msigma hM hCompl.E_le_M hCompl.hall_E
      hpTau₁ hr hPline hRline

  by_cases heqPR :
      centralizerWithin (sigmaCore M) P =
        centralizerWithin (sigmaCore M) R
  · have hcentE₁E₃ :
        centralizerWithin (sigmaCore M) E₁ =
          centralizerWithin (sigmaCore M) E₃ := by
      calc
        centralizerWithin (sigmaCore M) E₁ =
            centralizerWithin (sigmaCore M) P :=
          (hprime₁ P hPE₁ hPne).symm
        _ = centralizerWithin (sigmaCore M) R := heqPR
        _ = centralizerWithin (sigmaCore M) E₃ :=
          hprime₃ R hRE₃ hRne
    have hHallE₁J :
        IsHall (tau1Primes M) (E₁.subgroupOf J) :=
      isHall_subgroupOf_intermediate13
        hE₁J hJE hCompl.hall_E₁
    have hHallE₃J :
        IsHall (tau3Primes M) (E₃.subgroupOf J) :=
      isHall_subgroupOf_intermediate13
        hE₃J hJE hCompl.hall_E₃
    have hE₃normalJ : (E₃.subgroupOf J).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hE₃J).mpr
        (hJE.trans hEnormE₃)
    have hE₁pi :
        IsPiNumber (tau1Primes M ∪ tau3Primes M)
          (Nat.card E₁) := by
      have h := hCompl.hall_E₁.isPiNumber_card.mono
        (Set.subset_union_left :
          tau1Primes M ⊆ tau1Primes M ∪ tau3Primes M)
      rwa [MathlibSupport.natCard_subgroupOf_eq hCompl.E₁_le_E] at h
    have hE₃pi :
        IsPiNumber (tau1Primes M ∪ tau3Primes M)
          (Nat.card E₃) := by
      have h := hCompl.hall_E₃.isPiNumber_card.mono
        (Set.subset_union_right :
          tau3Primes M ⊆ tau1Primes M ∪ tau3Primes M)
      rwa [MathlibSupport.natCard_subgroupOf_eq hCompl.E₃_le_E] at h
    let E₁J : Subgroup J := E₁.subgroupOf J
    let E₃J : Subgroup J := E₃.subgroupOf J
    have hE₃Jnormal : E₃J.Normal := by
      simpa only [E₃J] using hE₃normalJ
    have hE₁Jpi :
        IsPiNumber (tau1Primes M ∪ tau3Primes M)
          (Nat.card E₁J) := by
      dsimp only [E₁J]
      rw [MathlibSupport.natCard_subgroupOf_eq hE₁J]
      exact hE₁pi
    have hE₃Jpi :
        IsPiNumber (tau1Primes M ∪ tau3Primes M)
          (Nat.card E₃J) := by
      dsimp only [E₃J]
      rw [MathlibSupport.natCard_subgroupOf_eq hE₃J]
      exact hE₃pi
    have hsupJ : E₃J ⊔ E₁J = ⊤ := by
      change E₃.subgroupOf J ⊔ E₁.subgroupOf J = ⊤
      rw [← Subgroup.subgroupOf_sup hE₃J hE₁J]
      simpa only [J] using Subgroup.subgroupOf_self J
    have hJpi :
        IsPiNumber (tau1Primes M ∪ tau3Primes M)
          (Nat.card J) := by
      have h := isPiNumber_card_sup_of_normal_left
        hE₃Jnormal hE₃Jpi hE₁Jpi
      simpa [hsupJ] using h
    have hJsol : IsSolvable J :=
      mFT_sol (lt_of_le_of_lt hJM (mmax_proper hM))
    have hjoinOfBoth :
        ∀ {z : G},
          z ∈ Subgroup.centralizer (E₃ : Set G) →
          z ∈ Subgroup.centralizer (E₁ : Set G) →
          z ∈ Subgroup.centralizer (J : Set G) := by
      intro z hz₃ hz₁
      let Z₀ : Subgroup G := Subgroup.zpowers z
      have hZE₃ : Z₀ ≤ Subgroup.centralizer (E₃ : Set G) :=
        Subgroup.zpowers_le.mpr hz₃
      have hZE₁ : Z₀ ≤ Subgroup.centralizer (E₁ : Set G) :=
        Subgroup.zpowers_le.mpr hz₁
      have hE₃Z : E₃ ≤ Subgroup.centralizer (Z₀ : Set G) :=
        Subgroup.le_centralizer_iff.mp hZE₃
      have hE₁Z : E₁ ≤ Subgroup.centralizer (Z₀ : Set G) :=
        Subgroup.le_centralizer_iff.mp hZE₁
      have hJZ : J ≤ Subgroup.centralizer (Z₀ : Set G) := by
        simpa only [J] using sup_le hE₃Z hE₁Z
      have hZJ : Z₀ ≤ Subgroup.centralizer (J : Set G) :=
        Subgroup.le_centralizer_iff.mp hJZ
      exact hZJ (Subgroup.mem_zpowers z)
    intro X hXJ hXne
    apply le_antisymm
    · let q : ℕ := Nat.minFac (Nat.card X)
      have hq : q.Prime :=
        Nat.minFac_prime ((X.one_lt_card_iff_ne_bot.mpr hXne).ne')
      letI : Fact q.Prime := ⟨hq⟩
      have hqX : q ∣ Nat.card X := Nat.minFac_dvd (Nat.card X)
      obtain ⟨Y, hYX, hY⟩ :=
        exists_rankOne_le_of_prime_dvd13 hqX
      have hYJ : Y ≤ J := hYX.trans hXJ
      have hYne : Y ≠ ⊥ := hY.ne_bot
      have hqJ : q ∣ Nat.card J :=
        hqX.trans (Subgroup.card_dvd_of_le hXJ)
      rcases hJpi hq hqJ with hqTau₁ | hqTau₃
      · obtain ⟨x, hYE₁x, _hE₁xJ, _hHallE₁x,
            _hfit, _hdiv, _htransport⟩ :=
          exists_ambient_isHall_map_conj_ge_of_isSolvable
            (K := J) (A := Y) (H := E₁)
            hYJ hE₁J hJsol
            (hY.isPGroup.isPiNumber_natCard hqTau₁)
            hHallE₁J
        let E₁x : Subgroup G :=
          E₁.map (MulAut.conj (x : G)).toMonoidHom
        change Y ≤ E₁x at hYE₁x
        let Y₀ : Subgroup G :=
          Y.map (MulAut.conj ((x : G)⁻¹)).toMonoidHom
        have hcancel :
            E₁x.map (MulAut.conj ((x : G)⁻¹)).toMonoidHom =
              E₁ := by
          simpa only [E₁x] using
            map_conj_inv_map_conj13 E₁ (x : G)
        have hY₀E₁ : Y₀ ≤ E₁ := by
          calc
            Y₀ ≤ E₁x.map
                (MulAut.conj ((x : G)⁻¹)).toMonoidHom :=
              Subgroup.map_mono hYE₁x
            _ = E₁ := hcancel
        have hY₀ne : Y₀ ≠ ⊥ := by
          intro hbot
          apply hYne
          exact (Subgroup.map_eq_bot_iff_of_injective
            Y (MulAut.conj ((x : G)⁻¹)).injective).mp hbot
        intro z hz
        let z₀ : G := (MulAut.conj ((x : G)⁻¹)) z
        have hxM : (x : G) ∈ M := hJM x.property
        have hxInvNormSigma :
            (x : G)⁻¹ ∈ Subgroup.normalizer (sigmaCore M : Set G) :=
          hMnormSigma (M.inv_mem hxM)
        have hSigmaInv :
            (sigmaCore M).map
                (MulAut.conj ((x : G)⁻¹)).toMonoidHom =
              sigmaCore M :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp hxInvNormSigma
        have hz₀Sigma : z₀ ∈ sigmaCore M := by
          dsimp only [z₀]
          rw [← hSigmaInv]
          exact Subgroup.mem_map_of_mem
            (MulAut.conj ((x : G)⁻¹)).toMonoidHom hz.1
        have hz₀centY₀ :
            z₀ ∈ Subgroup.centralizer (Y₀ : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          rintro y₀ ⟨y, hy, rfl⟩
          have hyX : y ∈ X := hYX hy
          have hyz : y * z = z * y := hz.2 y hyX
          dsimp only [z₀]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          calc
            (x : G)⁻¹ * y * (x : G) *
                  ((x : G)⁻¹ * z * (x : G)) =
                (x : G)⁻¹ * (y * z) * (x : G) := by group
            _ = (x : G)⁻¹ * (z * y) * (x : G) := by rw [hyz]
            _ = (x : G)⁻¹ * z * (x : G) *
                  ((x : G)⁻¹ * y * (x : G)) := by group
        have hz₀withinY₀ :
            z₀ ∈ centralizerWithin (sigmaCore M) Y₀ :=
          ⟨hz₀Sigma, hz₀centY₀⟩
        have hz₀withinE₁ :
            z₀ ∈ centralizerWithin (sigmaCore M) E₁ := by
          rw [← hprime₁ Y₀ hY₀E₁ hY₀ne]
          exact hz₀withinY₀
        have hz₀withinE₃ :
            z₀ ∈ centralizerWithin (sigmaCore M) E₃ := by
          rw [← hcentE₁E₃]
          exact hz₀withinE₁
        have hxInvNormE₃ :
            (x : G)⁻¹ ∈ Subgroup.normalizer (E₃ : Set G) :=
          hEnormE₃ (E.inv_mem (hJE x.property))
        have hE₃Inv :
            E₃.map (MulAut.conj ((x : G)⁻¹)).toMonoidHom = E₃ :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp hxInvNormE₃
        have hzCentE₃ :
            z ∈ Subgroup.centralizer (E₃ : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro c hc
          let c₀ : G := (MulAut.conj ((x : G)⁻¹)) c
          have hc₀E₃ : c₀ ∈ E₃ := by
            dsimp only [c₀]
            rw [← hE₃Inv]
            exact Subgroup.mem_map_of_mem
              (MulAut.conj ((x : G)⁻¹)).toMonoidHom hc
          have hc₀z₀ : c₀ * z₀ = z₀ * c₀ :=
            hz₀withinE₃.2 c₀ hc₀E₃
          dsimp only [c₀, z₀] at hc₀z₀
          simp only [MulAut.conj_apply, inv_inv] at hc₀z₀
          calc
            c * z = (x : G) *
                (((x : G)⁻¹ * c * (x : G)) *
                  ((x : G)⁻¹ * z * (x : G))) * (x : G)⁻¹ := by group
            _ = (x : G) *
                (((x : G)⁻¹ * z * (x : G)) *
                  ((x : G)⁻¹ * c * (x : G))) * (x : G)⁻¹ := by
              rw [hc₀z₀]
            _ = z * c := by group
        have hzWithinE₃ :
            z ∈ centralizerWithin (sigmaCore M) E₃ :=
          ⟨hz.1, hzCentE₃⟩
        have hzWithinE₁ :
            z ∈ centralizerWithin (sigmaCore M) E₁ := by
          rw [hcentE₁E₃]
          exact hzWithinE₃
        exact ⟨hz.1, hjoinOfBoth hzWithinE₃.2 hzWithinE₁.2⟩
      · have hYE₃ : Y ≤ E₃ :=
          le_normal_isHall_of_isPiNumber13
            hE₃normalJ hHallE₃J hYJ
            (hY.isPGroup.isPiNumber_natCard hqTau₃)
        intro z hz
        have hzWithinY :
            z ∈ centralizerWithin (sigmaCore M) Y :=
          ⟨hz.1, Subgroup.centralizer_le hYX hz.2⟩
        have hzWithinE₃ :
            z ∈ centralizerWithin (sigmaCore M) E₃ := by
          rw [← hprime₃ Y hYE₃ hYne]
          exact hzWithinY
        have hzWithinE₁ :
            z ∈ centralizerWithin (sigmaCore M) E₁ := by
          rw [hcentE₁E₃]
          exact hzWithinE₃
        exact ⟨hz.1, hjoinOfBoth hzWithinE₃.2 hzWithinE₁.2⟩
    · exact centralizerWithin_antitone_right hXJ
  · have hltPR :
        centralizerWithin (sigmaCore M) P <
          centralizerWithin (sigmaCore M) R :=
      lt_of_le_of_ne hcentPR heqPR
    have hcentRne : centralizerWithin (sigmaCore M) R ≠ ⊥ :=
      (lt_of_le_of_lt bot_le hltPR).ne'
    have hE₂bot : E₂ = ⊥ := by
      by_contra hE₂ne
      let q : ℕ := Nat.minFac (Nat.card E₂)
      have hq : q.Prime :=
        Nat.minFac_prime ((E₂.one_lt_card_iff_ne_bot.mpr hE₂ne).ne')
      letI : Fact q.Prime := ⟨hq⟩
      have hqE₂ : q ∣ Nat.card E₂ := Nat.minFac_dvd (Nat.card E₂)
      have hqE₂sub : q ∣ Nat.card (E₂.subgroupOf E) := by
        rwa [MathlibSupport.natCard_subgroupOf_eq hCompl.E₂_le_E]
      have hqTau₂ : q ∈ tau2Primes M :=
        hCompl.hall_E₂.isPiNumber_card hq hqE₂sub
      obtain ⟨A, hAE, _hAM, hA⟩ :=
        ex_tau2Elem hCompl.E_le_M hCompl.hall_E hqTau₂
      have hreg :=
        (tau2_regular hM hCompl hqTau₂ hAE hA).E₃_regular
      exact hcentRne
        (centralizerWithin_eq_bot_of_semiregular13 hreg hRE₃ hRne)
    let RE₃ : Subgroup E₃ := R.subgroupOf E₃
    have hRE₃char : RE₃.Characteristic :=
      subgroup_characteristic_of_isCyclic13 RE₃
    letI : RE₃.Characteristic := hRE₃char
    have hEnormR : E ≤ Subgroup.normalizer (R : Set G) := by
      have hnorm := hEnormE₃.trans
        (characteristic_map_subtype_le_normalizer13 E₃ RE₃)
      simpa only [RE₃, Subgroup.map_subgroupOf_eq_of_le hRE₃] using hnorm
    have hRM : R ≤ M := hRE.trans hCompl.E_le_M
    have hRproper : R < ⊤ := mFT_pgroup_proper R hR.isPGroup
    have hNRproper : Subgroup.normalizer (R : Set G) < ⊤ :=
      mFT_norm_proper R hRne hRproper
    obtain ⟨H, hH, hNRH⟩ :=
      mmax_exists (Subgroup.normalizer (R : Set G)) hNRproper
    have hEH : E ≤ H := hEnormR.trans hNRH
    have hRH : R ≤ H := hRE.trans hEH
    have hPH : P ≤ H := hPE.trans hEH
    have hPM : P ≤ M := hPE.trans hCompl.E_le_M
    have hE₁H : E₁ ≤ H := hCompl.E₁_le_E.trans hEH
    let C_R : Subgroup G := centralizerWithin (sigmaCore M) R
    let K₀ : Subgroup G := sigmaCore M ⊓ H
    have hCRK₀ : C_R ≤ K₀ := by
      intro z hz
      exact ⟨hz.1,
        hNRH (Subgroup.centralizer_le_normalizer (R : Set G) hz.2)⟩
    have hcommCRP : ⁅C_R, P⁆ ≠ ⊥ := by
      intro hbot
      have hleCent : C_R ≤ Subgroup.centralizer (P : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      have hle : centralizerWithin (sigmaCore M) R ≤
          centralizerWithin (sigmaCore M) P := by
        intro z hz
        exact ⟨hz.1, hleCent hz⟩
      exact (not_le_of_gt hltPR) hle
    have hcommK₀P : ⁅K₀, P⁆ ≠ ⊥ := by
      intro hbot
      apply hcommCRP
      apply le_antisymm
      · calc
          ⁅C_R, P⁆ ≤ ⁅K₀, P⁆ :=
            Subgroup.commutator_mono hCRK₀ le_rfl
          _ ≤ ⊥ := le_of_eq hbot
      · exact bot_le
    have htiE₁ : centralizerWithin E₁ K₀ = ⊥ := by
      by_contra hCne
      let C₁ : Subgroup G := centralizerWithin E₁ K₀
      have hC₁E₁ : C₁ ≤ E₁ := centralizerWithin_le_left E₁ K₀
      have hK₀withinC₁ : K₀ ≤
          centralizerWithin (sigmaCore M) C₁ := by
        exact le_inf inf_le_left
          (Subgroup.le_centralizer_iff.mp
            (show C₁ ≤ Subgroup.centralizer (K₀ : Set G) from
              inf_le_right))
      have hle : centralizerWithin (sigmaCore M) R ≤
          centralizerWithin (sigmaCore M) C₁ :=
        hCRK₀.trans hK₀withinC₁
      have hCeq := hprime₁ C₁ hC₁E₁ hCne
      have hPeq := hprime₁ P hPE₁ hPne
      rw [hCeq, ← hPeq] at hle
      exact (not_le_of_gt hltPR) hle
    have hPMH : P ≤ M ⊓ H := le_inf hPM hPH
    have hcommK₀MH : ⁅sigmaCore M ⊓ H, M ⊓ H⁆ ≠ ⊥ := by
      intro hbot
      apply hcommK₀P
      apply le_antisymm
      · calc
          ⁅K₀, P⁆ ≤ ⁅sigmaCore M ⊓ H, M ⊓ H⁆ :=
            Subgroup.commutator_mono le_rfl hPMH
          _ ≤ ⊥ := le_of_eq hbot
      · exact bot_le
    have hbase :=
      cent_norm_tau13_mmax hM hCompl.E_le_M hCompl.hall_E
        (Or.inr hrTau₃) hRM hR.isPGroup hH hNRH
    have hrSigmaH : r ∈ sigmaPrimes H :=
      (hbase.2.2 hcommK₀MH).1
    have hE₁tau₁H :
        IsPiNumber (tau1Primes H) (Nat.card E₁) := by
      intro q hq hqE₁
      by_contra hqNotTau₁
      letI : Fact q.Prime := ⟨hq⟩
      obtain ⟨Y, hYE₁, hY⟩ :=
        exists_rankOne_le_of_prime_dvd13 hqE₁
      have hYE : Y ≤ E := hYE₁.trans hCompl.E₁_le_E
      have hYH : Y ≤ H := hYE.trans hEH
      have hYpi : IsPiNumber (tau1Primes H)ᶜ (Nat.card Y) :=
        hY.isPGroup.isPiNumber_natCard hqNotTau₁
      have hYcent : Y ≤ Subgroup.centralizer (K₀ : Set G) :=
        hbase.2.1
          Y (le_inf hYE hYH) hYpi
      have hYle : Y ≤ centralizerWithin E₁ K₀ :=
        le_inf hYE₁ hYcent
      have hYbot : Y ≤ ⊥ := by
        rw [← htiE₁]
        exact hYle
      exact hY.ne_bot (le_bot_iff.mp hYbot)
    have hE₁sigmaComplH :
        IsPiNumber (sigmaPrimes H)ᶜ (Nat.card E₁) := by
      intro q hq hqE₁
      exact (hE₁tau₁H hq hqE₁).2.1
    obtain ⟨F, hE₁F, hFH, hHallF⟩ :=
      MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
        hE₁H (mmax_sol hH) (sigmaPrimes H)ᶜ hE₁sigmaComplH
    have hFsol : IsSolvable F := sigma_compl_sol hFH hHallF
    obtain ⟨F₁, hE₁F₁, hF₁F, hHallF₁⟩ :=
      MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
        hE₁F hFsol (tau1Primes H) hE₁tau₁H
    have hRsigmaH : R ≤ sigmaCore H :=
      le_normal_isHall_of_isPiNumber13
        (sigmaCore_normal H) (Msigma_Hall hH)
        hRH (hR.isPGroup.isPiNumber_natCard hrSigmaH)
    have hRwithinP : R ≤ centralizerWithin (sigmaCore H) P :=
      le_inf hRsigmaH hRPcent
    have hprimeF₁ : IsPrimeAction (sigmaCore H) F₁ :=
      tau1_primact_Msigma hH hFH hHallF hF₁F hHallF₁
    have hRwithinF₁ : R ≤ centralizerWithin (sigmaCore H) F₁ := by
      rw [← hprimeF₁ P (hPE₁.trans hE₁F₁) hPne]
      exact hRwithinP
    have hE₁centR : E₁ ≤ Subgroup.centralizer (R : Set G) := by
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((hRwithinF₁ hz).2 e (hE₁F₁ he)).symm
    have hE₃centR : E₃ ≤ Subgroup.centralizer (R : Set G) := by
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact congrArg Subtype.val
        (mul_comm (⟨z, hRE₃ hz⟩ : E₃) (⟨e, he⟩ : E₃))
    have hsd : IsInternalSemidirectProductIn E₃ E₁ E := by
      simpa only [hE₂bot, bot_sup_eq] using hctx.E₃_E₂₁_sdprod
    have hsupE : E₃ ⊔ E₁ = E := by
      have htop : E₃.subgroupOf E ⊔ E₁.subgroupOf E = ⊤ :=
        hsd.2.2.2.sup_eq_top
      calc
        E₃ ⊔ E₁ =
            (E₃.subgroupOf E).map E.subtype ⊔
              (E₁.subgroupOf E).map E.subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le hCompl.E₃_le_E,
            Subgroup.map_subgroupOf_eq_of_le hCompl.E₁_le_E]
        _ = (E₃.subgroupOf E ⊔ E₁.subgroupOf E).map E.subtype := by
          rw [Subgroup.map_sup]
        _ = (⊤ : Subgroup E).map E.subtype :=
          congrArg (Subgroup.map E.subtype) htop
        _ = E := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hEcentR : E ≤ Subgroup.centralizer (R : Set G) := by
      rw [← hsupE]
      exact sup_le hE₃centR hE₁centR
    have hRcentE : R ≤ Subgroup.centralizer (E : Set G) :=
      Subgroup.le_centralizer_iff.mp hEcentR
    have hRleFixed : R ≤ centralizerWithin E₃ E :=
      le_inf hRE₃ hRcentE
    have hRbot : R ≤ ⊥ := by
      rw [← hctx.centralizerWithin_eq_bot]
      exact hRleFixed
    exact (hRne (le_bot_iff.mp hRbot)).elim

/-- `BGsection13.v: tau13_primact_Msigma`, Bender--Glauberman
Lemma 13.7. -/
theorem tau13_primact_Msigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (hnotRegular : ¬ IsSemiregularConjugation E₃ E₁) :
    IsPrimeAction (sigmaCore M) (E₃ ⊔ E₁) := by
  have hctx : SigmaComplementContext E E₁ E₂ E₃ :=
    sigma_compl_context hM hCompl
  have hprime₁ : IsPrimeAction (sigmaCore M) E₁ :=
    tau1_primact_Msigma hM hCompl.E_le_M hCompl.hall_E
      hCompl.E₁_le_E hCompl.hall_E₁
  have hprime₃ : IsPrimeAction (sigmaCore M) E₃ :=
    tau3_primact_Msigma hM hCompl.E_le_M hCompl.hall_E
      hCompl.E₃_le_E hCompl.hall_E₃
  exact tau13_join_prime_action_direct13
    hM hCompl hctx hprime₁ hprime₃ hnotRegular

end

end Submission.OddOrder.BG.Section13
