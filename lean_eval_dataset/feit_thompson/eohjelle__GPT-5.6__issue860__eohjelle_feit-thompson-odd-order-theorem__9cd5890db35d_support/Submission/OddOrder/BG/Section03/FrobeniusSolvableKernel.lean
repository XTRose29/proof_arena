import Submission.OddOrder.BG.Section03.FrobeniusNilpotentKernel
import Submission.OddOrder.BG.Section03.SemiregularConjugation

/-!
# Nilpotence of a solvable Frobenius kernel

This file ports `BGsection3.v: Frobenius_sol_kernel_nil` (lines
1364--1375).  A nontrivial Frobenius complement contains a subgroup of
prime order.  Restricting the fixed-point-free conjugation action to that
subgroup gives a Frobenius decomposition inside the subgroup generated with
the kernel, where `prime_Frobenius_sol_kernel_nil` applies.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

/-- `BGsection3.v: Frobenius_sol_kernel_nil`.

The kernel of a finite solvable Frobenius group is nilpotent. -/
theorem Frobenius_sol_kernel_nil
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G}
    (hFrob : IsFrobeniusDecomposition K R)
    (hsol : IsSolvable G) :
    Group.IsNilpotent K := by
  classical
  letI : IsSolvable G := hsol
  letI : K.Normal := hFrob.kernel_normal
  have hRcardNe : Nat.card R ≠ 1 :=
    (R.one_lt_card_iff_ne_bot.mpr hFrob.complement_ne_bot).ne'
  obtain ⟨p, hp, hpR⟩ := Nat.exists_prime_and_dvd hRcardNe
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := R) p hpR
  let R₀ : Subgroup G := (Subgroup.zpowers x).map R.subtype
  have hR₀R : R₀ ≤ R := by
    dsimp only [R₀]
    exact Subgroup.map_subtype_le _
  have hcardR₀ : Nat.card R₀ = p := by
    dsimp only [R₀]
    rw [Subgroup.card_map_of_injective R.subtype_injective,
      Nat.card_zpowers, hxOrder]
  have hR₀prime : (Nat.card R₀).Prime := by
    rw [hcardR₀]
    exact hp
  have hR₀ne : R₀ ≠ ⊥ := by
    rw [← R₀.one_lt_card_iff_ne_bot, hcardR₀]
    exact hp.one_lt
  have hnormR₀K : R₀ ≤ Subgroup.normalizer (K : Set G) := by
    rw [K.normalizer_eq_top]
    exact le_top
  have hregR₀ : IsSemiregularConjugation K R₀ := by
    intro r hr k hfix
    let rR : R := ⟨(r : G), hR₀R r.property⟩
    have hrR : rR ≠ 1 := by
      intro hrR
      apply hr
      apply Subtype.ext
      exact congrArg (fun y : R => (y : G)) hrR
    exact hFrob.fixedPointFree rR hrR k hfix
  let J : Subgroup G := R₀ ⊔ K
  let KJ : Subgroup J := K.subgroupOf J
  let RJ : Subgroup J := R₀.subgroupOf J
  have hFrobJ : IsFrobeniusDecomposition KJ RJ := by
    simpa only [J, KJ, RJ] using
      hregR₀.isFrobeniusDecomposition_sup
        hnormR₀K hFrob.kernel_ne_bot hR₀ne
  have hsolJ : IsSolvable J :=
    isSolvable_subgroup_of_isSolvable J
  have hRJprime : (Nat.card RJ).Prime := by
    rw [natCard_subgroupOf_eq
      (show R₀ ≤ J from le_sup_left)]
    exact hR₀prime
  have hcentJ : centralizerWithin KJ RJ = ⊥ := by
    apply le_bot_iff.mp
    intro k hk
    letI : Nontrivial RJ :=
      RJ.nontrivial_iff_ne_bot.mpr hFrobJ.complement_ne_bot
    obtain ⟨r, hr⟩ := exists_ne (1 : RJ)
    let kKJ : KJ := ⟨k, hk.1⟩
    have hcomm : (r : J) * k = k * (r : J) :=
      hk.2 (r : J) r.property
    have hfix :
        (r : J) * (kKJ : J) * (r : J)⁻¹ = (kKJ : J) := by
      dsimp only [kKJ]
      rw [hcomm]
      simp
    have hkOne : kKJ = 1 :=
      hFrobJ.fixedPointFree r hr kKJ hfix
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hkOne)
  have hnilKJ : Group.IsNilpotent KJ :=
    prime_Frobenius_sol_kernel_nil hFrobJ.isComplement
      hFrobJ.kernel_normal hsolJ hRJprime hcentJ
  let eKJ : KJ ≃* K :=
    Subgroup.subgroupOfEquivOfLe
      (show K ≤ J from le_sup_right)
  exact (Group.isNilpotent_congr eKJ).mp hnilKJ

end

end Submission.OddOrder.BG.Section03
