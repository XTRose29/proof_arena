import Submission.OddOrder.BG.Section04.MetacyclicOmegaOne
import Submission.OddOrder.BG.Section04.OddPGroupRankOne
import Submission.OddOrder.MathlibSupport.HuppertDerivedCyclic
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
The maximal-cyclic-subgroup step in Huppert's Proposition 4.11.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- If the derived subgroup is cyclic, the omega-one bound forces a finite
odd `p`-group to be metacyclic.  This is the final maximality argument in
`BGsection4.v: p2_Ohm1_metacyclic`. -/
theorem isMetacyclic_of_commutator_isCyclic_of_omegaOne_card_le_prime_sq
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hOmega : Nat.card (omegaOne p G) ≤ p ^ 2)
    (hDerivedCyclic : IsCyclic (_root_.commutator G)) :
    IsMetacyclic G := by
  classical
  let D : Subgroup G := _root_.commutator G
  let s : Set (Subgroup G) := {A | IsCyclic A ∧ D ≤ A}
  have hs : s.Nonempty := ⟨D, hDerivedCyclic, le_rfl⟩
  obtain ⟨S, hS, hSmax⟩ := s.toFinite.exists_maximal hs
  have hScyclic : IsCyclic S := hS.1
  have hDS : D ≤ S := hS.2
  have hSnormal : S.Normal := by
    apply Subgroup.Normal.of_commutator_le
    simpa [D] using hDS
  letI : S.Normal := hSnormal
  letI : IsCyclic S := hScyclic
  have hSmaximal (U : Subgroup G) (hUcyclic : IsCyclic U) (hSU : S ≤ U) :
      U ≤ S :=
    hSmax ⟨hUcyclic, hDS.trans hSU⟩ hSU
  let Q := G ⧸ S
  let q : G →* Q := QuotientGroup.mk' S
  have hQp : IsPGroup p Q := hG.to_quotient S
  have hQodd : Odd (Nat.card Q) := by
    have hdvd : Nat.card Q ∣ Nat.card G := by
      rw [show Nat.card Q = S.index by
        exact S.index_eq_card.symm]
      exact S.index_dvd_card
    exact hodd.of_dvd_nat hdvd

  have hOmegaImageUnique (L : Subgroup Q) (hLcard : Nat.card L = p) :
      (omegaOne p G).map q = L := by
    let U : Subgroup G := L.comap q
    have hSU : S ≤ U := by
      intro x hx
      change q x ∈ L
      have hqx : q x = 1 := by
        dsimp [q]
        exact (QuotientGroup.eq_one_iff x).mpr hx
      rw [hqx]
      exact L.one_mem
    let SU : Subgroup U := S.subgroupOf U
    have hSUnormal : SU.Normal := by
      dsimp [SU]
      infer_instance
    letI : SU.Normal := hSUnormal
    have hSUcyclic : IsCyclic SU :=
      (Subgroup.subgroupOfEquivOfLe hSU).isCyclic.mpr hScyclic
    letI : IsCyclic SU := hSUcyclic
    have hUmap : U.map q = L := by
      dsimp [U, q]
      exact Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective S) L
    let eUL : U ⧸ SU ≃* L :=
      (QuotientGroup.liftEquiv SU (q.subgroupMap_surjective U) (by
        dsimp [SU, q]
        rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])).trans
        (MulEquiv.subgroupCongr hUmap)
    have hLcyclic : IsCyclic L := by
      letI : Fact (Nat.card L).Prime := ⟨hLcard ▸ (Fact.out : p.Prime)⟩
      exact isCyclic_of_prime_card rfl
    have hUQuotientCyclic : IsCyclic (U ⧸ SU) :=
      eUL.isCyclic.mpr hLcyclic
    have hUmeta : IsMetacyclic U :=
      isMetacyclic_of_normal_cyclic_quotient
        U SU hSUnormal hSUcyclic hUQuotientCyclic
    have hUnotcyclic : ¬ IsCyclic U := by
      intro hUcyclic
      have hUS : U ≤ S := hSmaximal U hUcyclic hSU
      have hUeq : U = S := le_antisymm hUS hSU
      have hLbot : L = ⊥ := by
        rw [← hUmap, hUeq]
        apply le_antisymm
        · rintro _ ⟨x, hx, rfl⟩
          exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff x).mpr hx)
        · exact bot_le
      have hpone : p = 1 := by
        rw [← hLcard, hLbot]
        exact Subgroup.card_bot
      exact (Fact.out : p.Prime).ne_one hpone
    have hUp : IsPGroup p U := hG.to_subgroup U
    have hUodd : Odd (Nat.card U) :=
      hodd.of_dvd_nat U.card_subgroup_dvd_card
    have hElemU : IsElementaryAbelianOfRank p 2 (omegaOne p U) :=
      omegaOne_isElementaryAbelian_rank_two_of_isMetacyclic
        hUmeta hUp hUodd hUnotcyclic
    let W : Subgroup G := (omegaOne p U).map U.subtype
    have hWle : W ≤ omegaOne p G := by
      dsimp [W]
      exact map_omegaOne_le p U.subtype
    have hWcard : Nat.card W = p ^ 2 := by
      dsimp [W]
      rw [Subgroup.card_map_of_injective U.subtype_injective,
        hElemU.card_eq]
    have hWOmega : W = omegaOne p G := by
      apply Subgroup.eq_of_le_of_card_ge hWle
      rw [hWcard]
      exact hOmega
    let I : Subgroup Q := (omegaOne p U).map (q.comp U.subtype)
    have hIle : I ≤ L := by
      rintro _ ⟨w, _hw, rfl⟩
      apply hUmap.le
      exact ⟨w, w.property, rfl⟩
    have hIne : I ≠ ⊥ := by
      intro hIbot
      have hOmegaSU : omegaOne p U ≤ SU := by
        have hmapBot : (omegaOne p U).map (q.comp U.subtype) = ⊥ := hIbot
        have hleKer := (Subgroup.map_eq_bot_iff (omegaOne p U)).mp hmapBot
        have hkerEq : (q.comp U.subtype).ker = SU := by
          ext x
          change ((x : G) : G ⧸ S) = 1 ↔ (x : G) ∈ S
          exact QuotientGroup.eq_one_iff (N := S) (x : G)
        rw [hkerEq] at hleKer
        exact hleKer
      have hOmegaCyclic : IsCyclic (omegaOne p U) :=
        Subgroup.isCyclic_of_le hOmegaSU
      exact hElemU.not_isCyclic Fact.out hOmegaCyclic
    have hIcardNeOne : Nat.card I ≠ 1 :=
      (I.one_lt_card_iff_ne_bot.mpr hIne).ne'
    have hpDvdI : p ∣ Nat.card I :=
      (hQp.to_subgroup I).card_eq_or_dvd.resolve_left hIcardNeOne
    have hpLeI : p ≤ Nat.card I := Nat.le_of_dvd Nat.card_pos hpDvdI
    have hIL : I = L := by
      apply Subgroup.eq_of_le_of_card_ge hIle
      rw [hLcard]
      exact hpLeI
    have hWmap : W.map q = I := by
      dsimp [W, I]
      rw [Subgroup.map_map]
    calc
      (omegaOne p G).map q = W.map q := by rw [hWOmega]
      _ = I := hWmap
      _ = L := hIL

  have hQcyclic : IsCyclic Q := by
    apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
      hQp hQodd).mpr
    rintro ⟨E, hE⟩
    haveI : Nontrivial E := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      rw [hE.card_eq]
      exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
    obtain ⟨e, he⟩ := exists_ne (1 : E)
    let L0 : Subgroup E := Subgroup.zpowers e
    have heOrder : orderOf e = p := by
      exact ((Nat.dvd_prime (Fact.out : p.Prime)).mp
        (orderOf_dvd_of_pow_eq_one (hE.pow_eq_one e))).resolve_left
          (by rw [orderOf_eq_one_iff]; exact he)
    have hL0card : Nat.card L0 = p := by
      dsimp [L0]
      rw [Nat.card_zpowers, heOrder]
    have hL0lt : L0 < ⊤ := by
      apply lt_of_le_of_ne le_top
      intro htop
      have hcardEq := congrArg (fun H : Subgroup E ↦ Nat.card H) htop
      rw [hL0card, Subgroup.card_top, hE.card_eq] at hcardEq
      have hpLtSq : p < p ^ 2 := by
        rw [pow_two]
        exact lt_mul_of_one_lt_right
          (Fact.out : p.Prime).pos (Fact.out : p.Prime).one_lt
      exact (ne_of_lt hpLtSq) hcardEq
    obtain ⟨f, hf⟩ := SetLike.exists_of_lt hL0lt
    have hfne : f ≠ 1 := by
      intro hf1
      apply hf.2
      rw [hf1]
      exact L0.one_mem
    let M0 : Subgroup E := Subgroup.zpowers f
    have hfOrder : orderOf f = p := by
      exact ((Nat.dvd_prime (Fact.out : p.Prime)).mp
        (orderOf_dvd_of_pow_eq_one (hE.pow_eq_one f))).resolve_left
          (by rw [orderOf_eq_one_iff]; exact hfne)
    have hM0card : Nat.card M0 = p := by
      dsimp [M0]
      rw [Nat.card_zpowers, hfOrder]
    let L : Subgroup Q := L0.map E.subtype
    let M : Subgroup Q := M0.map E.subtype
    have hLcard : Nat.card L = p := by
      dsimp [L]
      rw [Subgroup.card_map_of_injective E.subtype_injective, hL0card]
    have hMcard : Nat.card M = p := by
      dsimp [M]
      rw [Subgroup.card_map_of_injective E.subtype_injective, hM0card]
    have hLM : L = M := by
      rw [← hOmegaImageUnique L hLcard,
        ← hOmegaImageUnique M hMcard]
    have hL0M0 : L0 = M0 := by
      apply Subgroup.map_injective E.subtype_injective
      exact hLM
    apply hf.2
    rw [hL0M0]
    exact Subgroup.mem_zpowers f
  exact isMetacyclic_of_normal_cyclic_quotient
    G S hSnormal hScyclic hQcyclic

end

end Submission.OddOrder.BG.Section04
