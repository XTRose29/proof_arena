import Submission.OddOrder.BG.Section06.PuigConsequences
import Submission.OddOrder.MathlibSupport.CoprimeNilpotentCentralizer
import Submission.OddOrder.MathlibSupport.FittingPCore
import Submission.OddOrder.MathlibSupport.PPrimePCore
import Submission.OddOrder.MathlibSupport.SCNCentralizer

/-!
# Bender--Glauberman Proposition 7.5(b): the SCN prime-core step

An SCN subgroup of a Sylow `p`-subgroup forces every normalized
`p'`-subgroup into the `p'`-core.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport

universe u

/-- SCN data restricts to every ambient subgroup containing its Sylow
subgroup. -/
theorem IsSCN.subgroupOf {G : Type u} [Group G]
    {P A X : Subgroup G} (hA : IsSCN P A) (hPX : P ≤ X) :
    IsSCN (P.subgroupOf X) (A.subgroupOf X) := by
  letI : IsMulCommutative A := hA.commutative
  refine
    { le_sylow := ?_
      le_normalizer := ?_
      commutative := inferInstance
      centralizerWithin_eq := ?_ }
  · intro a ha
    exact hA.le_sylow ha
  · intro x hx
    apply Subgroup.mem_set_normalizer_iff.mpr
    intro a
    change (a : G) ∈ A ↔
      (x : G) * (a : G) * (x : G)⁻¹ ∈ A
    exact (Subgroup.mem_set_normalizer_iff.mp
      (hA.le_normalizer hx) (a : G))
  · ext x
    constructor
    · rintro ⟨hxP, hxcent⟩
      apply hA.centralizerWithin_eq.le
      refine ⟨hxP, ?_⟩
      intro a ha
      let aX : X := ⟨a, hPX (hA.le_sylow ha)⟩
      exact congrArg Subtype.val (hxcent aX ha)
    · intro hxA
      refine ⟨hA.le_sylow hxA, ?_⟩
      intro a ha
      apply Subtype.ext
      change (a : G) * (x : G) = (x : G) * (a : G)
      exact congrArg (fun z : A ↦ (z : G))
        (mul_comm' (⟨(a : G), ha⟩ : A) (⟨(x : G), hxA⟩ : A))

/-- Bender--Glauberman Proposition 7.5(b), prime-core form: a `p'`-subgroup
normalized by an SCN subgroup of a Sylow `p`-subgroup lies in the `p'`-core.
-/
theorem le_pPrimeCore_of_isSCN_normalizes
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [IsSolvable G]
    (hodd : Odd (Nat.card G)) (P : Sylow p G)
    {A Y : Subgroup G} (hA : IsSCN (P : Subgroup G) A)
    (hYprime : IsPPrimeSubgroup p Y)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤ pPrimeCore p G := by
  let K : Subgroup G := pPrimeCore p G
  letI : K.Normal := by
    dsimp [K]
    infer_instance
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let Q : Subgroup (G ⧸ K) := pCore p (G ⧸ K)
  let Aq : Subgroup (G ⧸ K) := A.map q
  let Yq : Subgroup (G ⧸ K) := Y.map q
  letI : Q.Normal := by
    dsimp [Q]
    infer_instance
  letI : IsSolvable (G ⧸ K) := by infer_instance

  have hAnormal : (A.subgroupOf (P : Subgroup G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA.le_sylow).mpr
      hA.le_normalizer
  have hAK₂ : A ≤ pPrimePCore p G :=
    (Submission.OddOrder.BG.Section06.odd_p_abelian_constrained hodd)
      P A hA.commutative hA.le_sylow hAnormal
  have hAqQ : Aq ≤ Q := by
    rintro _ ⟨a, ha, rfl⟩
    exact hAK₂ ha

  have hYqPrime : IsPPrimeSubgroup p Yq := by
    rw [IsPPrimeSubgroup]
    exact hYprime.coprime_dvd_right (Subgroup.card_map_dvd Y q)
  have hQp : IsPGroup p Q := by
    dsimp [Q]
    exact pCore_isPGroup
  obtain ⟨n, hQcard⟩ := IsPGroup.iff_card.mp hQp
  have hQYcoprime : Nat.Coprime (Nat.card Q) (Nat.card Yq) := by
    rw [hQcard]
    exact hYqPrime.pow_left n
  have hQYdisjoint : Disjoint Q Yq :=
    Subgroup.disjoint_of_coprime_natCard hQYcoprime

  have hAq_normalizes_Yq :
      Aq ≤ Subgroup.normalizer (Yq : Set (G ⧸ K)) :=
    (Subgroup.map_mono hAY).trans (Y.le_normalizer_map q)
  have hcommY : ⁅Aq, Yq⁆ ≤ Yq :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      hAq_normalizes_Yq
  have hcommQ : ⁅Aq, Yq⁆ ≤ Q :=
    (Subgroup.commutator_mono hAqQ le_top).trans
      (Subgroup.commutator_le_left Q (⊤ : Subgroup (G ⧸ K)))
  have hcommBot : ⁅Aq, Yq⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf hcommQ hcommY).trans
      (disjoint_iff.mp hQYdisjoint).le
  have hAq_centralizes_Yq :
      Aq ≤ Subgroup.centralizer (Yq : Set (G ⧸ K)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot

  let Pq : Sylow p (G ⧸ K) :=
    P.mapSurjective (QuotientGroup.mk'_surjective K)
  have hQPq : Q ≤ (Pq : Subgroup (G ⧸ K)) := pCore_le_sylow Pq
  have hPK : Disjoint (P : Subgroup G) K := by
    dsimp [K]
    exact disjoint_pPrimeCore_of_isPGroup P.isPGroup'
  have hcentralizerQAq : centralizerWithin Q Aq ≤ Aq := by
    intro x hx
    have hxPq : x ∈ (P : Subgroup G).map q := by
      simpa [Pq, q] using hQPq hx.1
    rcases hxPq with ⟨g, hgP, hgx⟩
    refine ⟨g, ?_, hgx⟩
    apply hA.centralizerWithin_eq.le
    refine ⟨hgP, ?_⟩
    intro a ha
    have hqa : q a ∈ Aq := ⟨a, ha, rfl⟩
    have hcommq := hx.2 (q a) hqa
    rw [← hgx] at hcommq
    have heq : q (a * g) = q (g * a) := by
      simpa only [map_mul] using hcommq
    have hdiffK : (a * g)⁻¹ * (g * a) ∈ K :=
      QuotientGroup.eq.mp heq
    have haP : a ∈ (P : Subgroup G) := hA.le_sylow ha
    have hdiffP : (a * g)⁻¹ * (g * a) ∈ (P : Subgroup G) :=
      (P : Subgroup G).mul_mem
        ((P : Subgroup G).inv_mem ((P : Subgroup G).mul_mem haP hgP))
        ((P : Subgroup G).mul_mem hgP haP)
    have hdiffInf : (a * g)⁻¹ * (g * a) ∈
        (P : Subgroup G) ⊓ K := ⟨hdiffP, hdiffK⟩
    rw [disjoint_iff.mp hPK] at hdiffInf
    exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp hdiffInf)

  let C : Subgroup (G ⧸ K) := centralizerWithin Q Yq
  have hAqC : Aq ≤ C := by
    intro a ha
    exact ⟨hAqQ ha, hAq_centralizes_Yq ha⟩
  have hself : centralizerWithin Q C ≤ C := by
    intro x hx
    apply hAqC
    apply hcentralizerQAq
    refine ⟨hx.1, ?_⟩
    intro a ha
    exact hx.2 a (hAqC ha)

  have hYq_normalizes_Q :
      Yq ≤ Subgroup.normalizer (Q : Set (G ⧸ K)) := by
    rw [Q.normalizer_eq_top]
    exact le_top
  letI : Group.IsNilpotent Q := hQp.isNilpotent
  have hYq_centralizes_Q :
      Yq ≤ Subgroup.centralizer (Q : Set (G ⧸ K)) :=
    coprime_nilpotent_centralizes_of_selfCentralizing_fixedPoints
      hYq_normalizes_Q hQYcoprime hself

  have hprimeCoreQuotient : pPrimeCore p (G ⧸ K) = ⊥ := by
    simpa [K] using
      (pPrimeCore_quotient_self_eq_bot (G := G) (p := p))
  have hFitting : fittingCore (G ⧸ K) = Q := by
    dsimp [Q]
    exact fittingCore_eq_pCore_of_pPrimeCore_eq_bot p hprimeCoreQuotient
  have hYqQ : Yq ≤ Q := by
    have hYq_centralizes_Fitting :
        Yq ≤ Subgroup.centralizer
          (fittingCore (G ⧸ K) : Set (G ⧸ K)) := by
      rw [hFitting]
      exact hYq_centralizes_Q
    rw [← hFitting]
    exact hYq_centralizes_Fitting.trans centralizer_fittingCore_le
  have hYqBot : Yq = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf hYqQ le_rfl).trans
      (disjoint_iff.mp hQYdisjoint).le

  change Y ≤ K
  intro y hy
  have hyq : q y ∈ Yq := ⟨y, hy, rfl⟩
  rw [hYqBot] at hyq
  exact (QuotientGroup.eq_one_iff y).mp (Subgroup.mem_bot.mp hyq)

end Submission.OddOrder.BG.Section07
