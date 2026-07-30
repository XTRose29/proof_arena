import Submission.OddOrder.MathlibSupport.CriticalAutomorphism
import Submission.OddOrder.MathlibSupport.CriticalOmegaAutomorphism
import Submission.OddOrder.MathlibSupport.OmegaOneSmallNilpotency
import Submission.OddOrder.MathlibSupport.ThompsonCritical

/-!
The odd critical-subgroup theorem from `BGsection1`.

Starting with a Thompson critical subgroup `K`, the required subgroup is the
ambient image of `Ω₁(K)`.  The small nilpotency-class omega theorem gives its
exponent, while the critical automorphism results control its pointwise
automorphism fixer.
-/

namespace Submission.OddOrder.BG.Section01

open Submission.OddOrder.MathlibSupport

universe u

/-- Bender--Glauberman, Theorem 1.13 (`critical_odd`). -/
theorem critical_odd
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hne : Nat.card G ≠ 1) :
    ∃ H : Subgroup G,
      H.Characteristic ∧
      ⁅H, (⊤ : Subgroup G)⁆ ≤ centerWithin H ∧
      Group.nilpotencyClass H ≤ 2 ∧
      Monoid.exponent H = p ∧
      IsPGroup p (fixingSubgroup (MulAut G) (H : Set G)) := by
  classical
  obtain ⟨K, hK⟩ := thompson_critical hG
  letI : K.Characteristic := hK.characteristic
  have hKp : IsPGroup p K := hG.to_subgroup K
  have hKodd : Odd (Nat.card K) :=
    hodd.of_dvd_nat K.card_subgroup_dvd_card
  have hpodd : Odd p :=
    hodd.of_dvd_nat (hG.card_eq_or_dvd.resolve_left hne)
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have htopbot : (⊤ : Subgroup G) = ⊥ := by
      calc
        (⊤ : Subgroup G) = Subgroup.centralizer (K : Set G) := by
          symm
          apply Subgroup.centralizer_eq_top_iff_subset.mpr
          intro x hx
          rw [hKbot] at hx
          rw [Subgroup.mem_bot.mp hx]
          exact Subgroup.one_mem _
        _ = centerWithin K := hK.centralizer_eq_center
        _ = ⊥ := by simp [hKbot, centerWithin, centralizerWithin]
    haveI : Subsingleton (Subgroup G) :=
      subsingleton_iff_bot_eq_top.mp htopbot.symm
    haveI : Subsingleton G := Subgroup.subsingleton_iff.mp inferInstance
    exact hne Nat.card_unique
  have hKcard : Nat.card K ≠ 1 :=
    (K.one_lt_card_iff_ne_bot.mpr hKne).ne'
  have hOmegaNe : omegaOne p K ≠ ⊥ :=
    omegaOne_ne_bot_of_isPGroup hKp hKcard

  let O : Subgroup K := omegaOne p K
  let H : Subgroup G := O.map K.subtype
  let e : O ≃* H :=
    O.equivMapOfInjective K.subtype K.subtype_injective
  have hOnontrivial : Nontrivial O := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    exact O.one_lt_card_iff_ne_bot.mpr hOmegaNe
  letI : Nontrivial O := hOnontrivial
  letI : Nontrivial H := e.symm.toEquiv.nontrivial
  have hHchar : H.Characteristic := by
    dsimp [H, O]
    infer_instance
  letI : H.Characteristic := hHchar
  have hHK : H ≤ K := by
    dsimp [H, O]
    exact Subgroup.map_subtype_le _
  have hHp : IsPGroup p H := hG.to_subgroup H

  have hHcomm : ⁅H, (⊤ : Subgroup G)⁆ ≤ centerWithin H := by
    have hcommK : ⁅H, (⊤ : Subgroup G)⁆ ≤ centerWithin K := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono le_rfl hHK).trans
        hK.commutator_le_center
    intro x hx
    have hxH : x ∈ H :=
      Subgroup.commutator_le_left H (⊤ : Subgroup G) hx
    have hxCenterK : x ∈ centerWithin K := hcommK hx
    rw [mem_centerWithin]
    refine ⟨hxH, ?_⟩
    intro y hy
    exact (mem_centerWithin.mp hxCenterK).2 y (hHK hy)

  have hHclass : Group.nilpotencyClass H ≤ 2 := by
    have hcentral : _root_.commutator H ≤ Subgroup.center H := by
      intro c hc
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      have hcAmbient : (c : G) ∈ ⁅H, H⁆ := by
        rw [← H.map_subtype_commutator]
        exact Subgroup.mem_map_of_mem H.subtype hc
      have hcWithin : (c : G) ∈ centerWithin H :=
        hHcomm ((Subgroup.commutator_mono le_rfl le_top) hcAmbient)
      exact (mem_centerWithin.mp hcWithin).2 (x : G) x.property
    have hbot :
        Subgroup.lowerCentralSeries (⊤ : Subgroup H) 2 = ⊥ := by
      rw [show 2 = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ,
        Subgroup.top_lowerCentralSeries_one,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro x _
      exact Subgroup.mem_center_iff.mp (hcentral hz) x
    letI : Group.IsNilpotent H := hHp.isNilpotent
    exact
      (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le
        (G := H) (n := 2)).mp hbot

  have hKclass : Group.nilpotencyClass K ≤ 2 := critical_class2 hK
  have hKclassBound :
      Group.nilpotencyClass K ≤ if 3 < p then 3 else 2 := by
    exact hKclass.trans (by split_ifs <;> omega)
  have hOpow : ∀ z : O, z ^ p = 1 := by
    intro z
    apply Subtype.ext
    exact omegaOne_pow_eq_one_of_small_nilpotencyClass
      p Fact.out hpodd hKp hKclassBound z z.property
  have hHpow : ∀ z : H, z ^ p = 1 := by
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    simpa only [map_pow, map_one] using congrArg e (hOpow w)
  have hHexp : Monoid.exponent H = p := by
    apply (Monoid.exponent_eq_prime_iff (Fact.out : p.Prime)).mpr
    intro z hz
    exact orderOf_eq_prime (hHpow z) hz

  have hHfixer :
      IsPGroup p (fixingSubgroup (MulAut G) (H : Set G)) := by
    apply isPGroup_of_prime_order_elements
    intro q hq hqp a haOrder
    have haOrderAmbient : orderOf (a : MulAut G) = q :=
      (Subgroup.orderOf_coe a).trans haOrder
    have haFixK :
        (a : MulAut G) ∈ fixingSubgroup (MulAut G) (K : Set G) :=
      critical_fixes_of_fixes_map_omegaOne_of_prime_order
        hK hKp hKodd hq hqp (a : MulAut G) haOrderAmbient a.property
    let b : fixingSubgroup (MulAut G) (K : Set G) :=
      ⟨(a : MulAut G), haFixK⟩
    have hbOrder : orderOf b = q := by
      rw [← Subgroup.orderOf_coe b]
      exact haOrderAmbient
    have hFixKp := critical_fixingSubgroup_isPGroup hG hK
    have hbOne : b = 1 := by
      by_contra hbNe
      have hpq : p ∣ q := by
        rw [← hbOrder]
        exact hFixKp.dvd_orderOf hbNe
      rcases (Nat.dvd_prime hq).mp hpq with hpOne | hpEq
      · exact (Fact.out : p.Prime).ne_one hpOne
      · exact hqp hpEq.symm
    apply Subtype.ext
    change (a : MulAut G) = 1
    exact congrArg
      (fun z : fixingSubgroup (MulAut G) (K : Set G) => (z : MulAut G))
      hbOne

  exact ⟨H, hHchar, hHcomm, hHclass, hHexp, hHfixer⟩

end Submission.OddOrder.BG.Section01
