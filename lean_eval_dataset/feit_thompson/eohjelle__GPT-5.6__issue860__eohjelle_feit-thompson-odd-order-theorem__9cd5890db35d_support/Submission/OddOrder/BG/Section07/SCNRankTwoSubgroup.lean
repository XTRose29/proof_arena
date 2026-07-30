import Submission.OddOrder.BG.Section04.OddNormalRankTwoExists
import Submission.OddOrder.BG.Section05.OmegaUpperCentralSetup
import Submission.OddOrder.MathlibSupport.Centralizer

/-!
# The rank-two subgroup used in Bender--Glauberman Proposition 7.5(b)

The first omega subgroup of the center of `P` is transported to the ambient
group.  A normal rank-two subgroup inside `A` can then be chosen either inside
that omega subgroup, or containing it when the latter is cyclic.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport

universe u

/-- The ambient image of `Ω₁(Z(P))`. -/
def omegaOneCenterAmbient
    {G : Type u} [Group G] (p : ℕ) (P : Subgroup G) : Subgroup G :=
  (Submission.OddOrder.BG.Section05.omegaOneCenter p P).map P.subtype

/-- The ambient image of `Ω₁(Z(P))` lies in the center of `P`. -/
theorem omegaOneCenterAmbient_le_centerWithin
    {G : Type u} [Group G] (p : ℕ) (P : Subgroup G) :
    omegaOneCenterAmbient p P ≤ centerWithin P := by
  rw [omegaOneCenterAmbient, ← map_center_eq_centerWithin P]
  exact Subgroup.map_mono
    (Submission.OddOrder.BG.Section05.omegaOneCenter_le_center
      (G := P) p)

private theorem rankTwo_map_subtype
    {G : Type u} [Group G] {p : ℕ} {P : Subgroup G}
    {E : Subgroup P} (hE : IsElementaryAbelianOfRank p 2 E) :
    IsElementaryAbelianOfRank p 2 (E.map P.subtype) := by
  refine
    { isPGroup := hE.isPGroup.map P.subtype
      commutative := ?_
      pow_eq_one := ?_
      card_eq := ?_ }
  · letI : IsMulCommutative E := hE.commutative
    infer_instance
  · rintro ⟨x, y, hy, rfl⟩
    apply Subtype.ext
    have hyPow := congrArg Subtype.val (hE.pow_eq_one ⟨y, hy⟩)
    simpa using congrArg P.subtype hyPow
  · calc
      Nat.card (E.map P.subtype) = Nat.card E :=
        Subgroup.card_map_of_injective P.subtype_injective
      _ = p ^ 2 := hE.card_eq

private theorem map_subtype_subgroupOf_normal
    {G : Type u} [Group G] {P : Subgroup G} {E : Subgroup P}
    (hE : E.Normal) :
    ((E.map P.subtype).subgroupOf P).Normal := by
  change ((E.map P.subtype).comap P.subtype).Normal
  rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  exact hE

/-- The normal elementary-abelian rank-two subgroup required in the proof of
`BGsection7.SCN_normed_constrained`. -/
theorem exists_normal_rankTwo_with_omegaOneCenter_dichotomy
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P A : Subgroup G}
    (hP : IsPGroup p P) (hodd : Odd (Nat.card P))
    (hAP : A ≤ P) (hAnormal : (A.subgroupOf P).Normal)
    (hAncyc : ¬ IsCyclic A)
    (hZA : omegaOneCenterAmbient p P ≤ A) :
    ∃ B : Subgroup G,
      B ≤ A ∧
      (B.subgroupOf P).Normal ∧
      IsElementaryAbelianOfRank p 2 B ∧
      (B ≤ omegaOneCenterAmbient p P ∨
        Nat.card (omegaOneCenterAmbient p P) = p ∧
          omegaOneCenterAmbient p P ≤ B) := by
  classical
  have hAne : A ≠ ⊥ := by
    intro hAbot
    apply hAncyc
    rw [hAbot]
    infer_instance
  have hPne : P ≠ ⊥ := by
    intro hPbot
    apply hAne
    rw [hPbot] at hAP
    exact le_bot_iff.mp hAP
  letI : Nontrivial P := P.nontrivial_iff_ne_bot.mpr hPne

  let ZP : Subgroup P :=
    Submission.OddOrder.BG.Section05.omegaOneCenter p P
  let Z : Subgroup G := omegaOneCenterAmbient p P
  let eZ : ZP ≃* Z :=
    ZP.equivMapOfInjective P.subtype P.subtype_injective
  have hZPp : IsPGroup p ZP := hP.to_subgroup ZP
  have hZPpow : ∀ z : ZP, z ^ p = 1 := by
    intro z
    simpa [ZP] using
      (Submission.OddOrder.BG.Section05.omegaOneCenter_pow_eq_one
        (G := P) p z)
  have hZPne : ZP ≠ ⊥ := by
    have hcenterPp : IsPGroup p (Subgroup.center P) :=
      hP.to_subgroup (Subgroup.center P)
    have hcenterNe : Subgroup.center P ≠ ⊥ := hP.bot_lt_center.ne'
    have hcenterCard : Nat.card (Subgroup.center P) ≠ 1 :=
      ((Subgroup.center P).one_lt_card_iff_ne_bot.mpr hcenterNe).ne'
    have hpCenter : p ∣ Nat.card (Subgroup.center P) :=
      hcenterPp.card_eq_or_dvd.resolve_left hcenterCard
    obtain ⟨z, hzOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := Subgroup.center P) p hpCenter
    have hzNe : z ≠ 1 := by
      intro hz
      rw [hz, orderOf_one] at hzOrder
      exact (Fact.out : p.Prime).ne_one hzOrder.symm
    have hzPow : z ^ p = 1 := by
      rw [← hzOrder]
      exact pow_orderOf_eq_one z
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    refine ⟨⟨(z : P), ?_⟩, ?_⟩
    · dsimp [ZP, Submission.OddOrder.BG.Section05.omegaOneCenter]
      exact ⟨z, mem_omegaOne_of_pow_eq_one p hzPow, rfl⟩
    · intro hzOne
      apply hzNe
      apply Subtype.ext
      exact congrArg (fun y : ZP => (y : P)) hzOne

  by_cases hZcyc : IsCyclic Z
  · letI : IsCyclic ZP := eZ.isCyclic.mpr hZcyc
    letI := Fintype.ofFinite ZP
    have hZPcardLe : Nat.card ZP ≤ p := by
      rw [Nat.card_eq_fintype_card]
      simpa only [hZPpow, Finset.filter_true, Finset.card_univ] using
        (IsCyclic.card_pow_eq_one_le (α := ZP)
          (Fact.out : p.Prime).pos)
    have hpZP : p ∣ Nat.card ZP :=
      hZPp.card_eq_or_dvd.resolve_left
        (ZP.one_lt_card_iff_ne_bot.mpr hZPne).ne'
    have hZPcard : Nat.card ZP = p :=
      le_antisymm hZPcardLe (Nat.le_of_dvd Nat.card_pos hpZP)
    have hZcard : Nat.card Z = p := by
      calc
        Nat.card Z = Nat.card ZP := by
          dsimp [Z, ZP, omegaOneCenterAmbient]
          exact Subgroup.card_map_of_injective P.subtype_injective
        _ = p := hZPcard

    let AP : Subgroup P := A.subgroupOf P
    let eA : AP ≃* A := Subgroup.subgroupOfEquivOfLe hAP
    have hAPncyc : ¬ IsCyclic AP := by
      intro hcyc
      exact hAncyc (eA.isCyclic.mp hcyc)
    letI : AP.Normal := by
      simpa [AP] using hAnormal
    obtain ⟨E, hEAP, hEnormal, hErank⟩ :=
      Submission.OddOrder.BG.Section04.odd_normal_p2Elem_exists
        hP hodd AP hAPncyc
    let B : Subgroup G := E.map P.subtype
    have hBA : B ≤ A := by
      dsimp [B]
      calc
        E.map P.subtype ≤ AP.map P.subtype := Subgroup.map_mono hEAP
        _ = A := by
          simpa [AP] using Subgroup.map_subgroupOf_eq_of_le hAP
    have hBnormal : (B.subgroupOf P).Normal := by
      dsimp [B]
      exact map_subtype_subgroupOf_normal hEnormal
    have hBrank : IsElementaryAbelianOfRank p 2 B := by
      dsimp [B]
      exact rankTwo_map_subtype hErank
    have hEne : E ≠ ⊥ := hErank.ne_bot
    letI : E.Normal := hEnormal
    have hEcenter : E ⊓ Subgroup.center P ≠ ⊥ :=
      normal_inf_center_ne_bot hP E hEne
    have hEcenterLe : E ⊓ Subgroup.center P ≤ E ⊓ ZP := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      let xCenter : Subgroup.center P := ⟨x, hx.2⟩
      have hxPow : xCenter ^ p = 1 := by
        apply Subtype.ext
        exact congrArg (fun y : E => (y : P))
          (hErank.pow_eq_one ⟨x, hx.1⟩)
      dsimp [ZP, Submission.OddOrder.BG.Section05.omegaOneCenter]
      exact ⟨xCenter, mem_omegaOne_of_pow_eq_one p hxPow, rfl⟩
    have hEinfZ : E ⊓ ZP ≠ ⊥ := by
      intro hbot
      apply hEcenter
      apply le_bot_iff.mp
      rw [hbot] at hEcenterLe
      exact hEcenterLe
    have hEsubZne : E.subgroupOf ZP ≠ ⊥ := by
      intro hbot
      exact hEinfZ
        (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot))
    have hZPprime : (Nat.card ZP).Prime := by
      rw [hZPcard]
      exact Fact.out
    letI : Fact (Nat.card ZP).Prime := ⟨hZPprime⟩
    have hEsubZtop : E.subgroupOf ZP = ⊤ :=
      (E.subgroupOf ZP).eq_bot_or_eq_top_of_prime_card.resolve_left
        hEsubZne
    have hZPE : ZP ≤ E := Subgroup.subgroupOf_eq_top.mp hEsubZtop
    have hZB : Z ≤ B := by
      dsimp [Z, ZP, B, omegaOneCenterAmbient]
      exact Subgroup.map_mono hZPE
    refine ⟨B, hBA, hBnormal, hBrank, Or.inr ?_⟩
    exact ⟨by simpa [Z] using hZcard, by simpa [Z] using hZB⟩
  · have hZPncyc : ¬ IsCyclic ZP := by
      intro hcyc
      exact hZcyc (eZ.isCyclic.mp hcyc)
    letI : ZP.Normal := inferInstance
    obtain ⟨E, hEZP, hEnormal, hErank⟩ :=
      Submission.OddOrder.BG.Section04.odd_normal_p2Elem_exists
        hP hodd ZP hZPncyc
    let B : Subgroup G := E.map P.subtype
    have hBZ : B ≤ Z := by
      dsimp [B, Z, ZP, omegaOneCenterAmbient]
      exact Subgroup.map_mono hEZP
    have hBA : B ≤ A := hBZ.trans (by simpa [Z] using hZA)
    have hBnormal : (B.subgroupOf P).Normal := by
      dsimp [B]
      exact map_subtype_subgroupOf_normal hEnormal
    have hBrank : IsElementaryAbelianOfRank p 2 B := by
      dsimp [B]
      exact rankTwo_map_subtype hErank
    refine ⟨B, hBA, hBnormal, hBrank, Or.inl ?_⟩
    simpa [Z] using hBZ

end Submission.OddOrder.BG.Section07
