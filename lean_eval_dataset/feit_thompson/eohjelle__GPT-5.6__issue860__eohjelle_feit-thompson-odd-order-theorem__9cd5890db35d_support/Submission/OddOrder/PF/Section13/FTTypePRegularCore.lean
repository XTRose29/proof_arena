import Submission.OddOrder.BG.AppendixC.Arithmetic
import Submission.OddOrder.PF.Section13.FTTypePBounds

/-!
# Peterfalvi Section 13: regularity of the type-P Fitting core

This module proves the regular-core, Galois/non-Galois, and
normalizer-centralizer conclusions from the analytic Section 13 bounds.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.BG.AppendixC
open Submission.OddOrder.MathlibSupport
open scoped Classical IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {S U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) regularCoreFintype
    (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace FTTypePSetupContext

/-- The geometric quotient denoted `ustar` in PF Section 13. -/
def ustar (ctx : FTTypePSetupContext S U W W₁ W₂ defW) : ℕ :=
  (ctx.p ^ ctx.q - 1) / (ctx.p - 1)

end FTTypePSetupContext

private theorem regularCore_ustar_eq_nU
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hp : ctx.p.Prime) :
    ctx.ustar = nU ctx.p ctx.q :=
  (nU_eq_div_of_prime hp).symm

private theorem regularCore_primeDivisor_modEq
    {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hcop : (nU p q).Coprime (p - 1))
    (hr : r.Prime) (hrU : r ∣ nU p q) :
    Nat.ModEq q r 1 := by
  have hr_not_pred : ¬ r ∣ p - 1 := fun hrp ↦
    (Nat.not_coprime_of_dvd_of_dvd hr.one_lt hrU hrp) hcop
  have hr_pow : r ∣ p ^ q - 1 := by
    rw [← nU_mul_sub_one p q hp.one_le]
    exact dvd_mul_of_dvd_left hrU (p - 1)
  letI : Fact r.Prime := ⟨hr⟩
  have hp_pow : (p : ZMod r) ^ q = 1 := by
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact ((Nat.modEq_iff_dvd' (one_le_pow₀ hp.one_le)).2 hr_pow).symm
  have hp_nonzero : (p : ZMod r) ≠ 0 := by
    intro hp0
    have : (0 : ZMod r) = 1 := by
      simpa only [hp0, zero_pow hq.ne_zero] using hp_pow
    exact zero_ne_one this
  have hp_not_one : (p : ZMod r) ≠ 1 := by
    intro hp1
    have hmod : Nat.ModEq r p 1 :=
      (ZMod.natCast_eq_natCast_iff p 1 r).mp
        (by simpa only [Nat.cast_one] using hp1)
    exact hr_not_pred ((Nat.modEq_iff_dvd' hp.one_le).mp hmod.symm)
  have horder : orderOf (p : ZMod r) = q := by
    apply ((Nat.dvd_prime hq).mp (orderOf_dvd_iff_pow_eq_one.mpr hp_pow)).resolve_left
    exact fun h ↦ hp_not_one (orderOf_eq_one_iff.mp h)
  have hq_dvd : q ∣ r - 1 := by
    rw [← horder]
    exact ZMod.orderOf_dvd_card_sub_one hp_nonzero
  exact ((Nat.modEq_iff_dvd' hr.pos).2 hq_dvd).symm

private theorem regularCore_divisor_modEq
    {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hodd : Odd (nU p q))
    (hcop : (nU p q).Coprime (p - 1)) :
    ∀ b, b ∣ nU p q → Nat.ModEq q b 1 := by
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
      intro hb
      by_cases hb1 : b = 1
      · simpa only [hb1] using (Nat.ModEq.refl 1 : Nat.ModEq q 1 1)
      · have hUpos : 0 < nU p q := by
          rcases hodd with ⟨k, hk⟩
          omega
        have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hb hUpos
        obtain ⟨r, hr, hrb⟩ := Nat.exists_prime_and_dvd hb1
        let c := b / r
        have hrc : r * c = b := Nat.mul_div_cancel' hrb
        have hclt : c < b := Nat.div_lt_self hbpos hr.one_lt
        have hcb : c ∣ b := ⟨r, by simpa only [Nat.mul_comm] using hrc.symm⟩
        have hcr := ih c hclt (hcb.trans hb)
        have hrr := regularCore_primeDivisor_modEq hp hq hcop hr (hrb.trans hb)
        rw [← hrc]
        simpa only [one_mul] using hrr.mul hcr

/-- `PFsection13.v: FTtypeP_primes_mod_cases`, Peterfalvi (13.14). -/
theorem FTtypeP_primes_mod_cases
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Odd ctx.ustar ∧
      (Nat.ModEq ctx.q ctx.p 1 → ctx.q ∣ ctx.ustar) ∧
      (¬ Nat.ModEq ctx.q ctx.p 1 →
        ctx.ustar.Coprime (ctx.p - 1) ∧
          Nat.ModEq ctx.q ctx.ustar 1 ∧
          ∀ b, b ∣ ctx.ustar → Nat.ModEq ctx.q b 1) := by
  have hprime := FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP
  have hq : ctx.q.Prime := hprime.1
  have hp : ctx.p.Prime := hprime.2
  have hpodd : Odd ctx.p := by
    change Odd (Nat.card W₂)
    exact mFT_odd W₂
  have hqodd : Odd ctx.q := by
    change Odd (Nat.card W₁)
    exact mFT_odd W₁
  have hmod2 : Nat.ModEq 2 (nU ctx.p ctx.q) ctx.q :=
    nU_modEq_length_of_dvd_sub_one hp.one_le
      (even_iff_two_dvd.mp (Nat.Odd.sub_odd hpodd odd_one))
  have hodd : Odd (nU ctx.p ctx.q) := by
    rw [Nat.odd_iff]
    calc
      nU ctx.p ctx.q % 2 = ctx.q % 2 := hmod2
      _ = 1 := Nat.odd_iff.mp hqodd
  rw [regularCore_ustar_eq_nU ctx hp]
  refine ⟨hodd, ?_, ?_⟩
  · intro hpmod
    exact (dvd_nU_iff_dvd_length_of_dvd_sub_one hp.one_le
      ((Nat.modEq_iff_dvd' hp.one_le).mp hpmod.symm)).2 (dvd_refl ctx.q)
  · intro hpmod
    have hcop : (nU ctx.p ctx.q).Coprime (ctx.p - 1) := by
      by_contra hnot
      obtain ⟨r, hr, hrU, hrp⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
      have hrq : r ∣ ctx.q :=
        (dvd_nU_iff_dvd_length_of_dvd_sub_one hp.one_le hrp).1 hrU
      have hr_eq : r = ctx.q :=
        ((Nat.dvd_prime hq).mp hrq).resolve_left hr.ne_one
      apply hpmod
      subst r
      exact ((Nat.modEq_iff_dvd' hp.one_le).2 hrp).symm
    have hall := regularCore_divisor_modEq hp hq hodd hcop
    exact ⟨hcop, hall _ (dvd_refl _), hall⟩

private theorem regularCore_mem_actionKernel
    (ctx : PTypeFCoreContext S U W W₁ W₂) (u : U) :
    u ∈ (ptypeFCoreAction ctx).ker ↔
      ∀ h : G, h ∈ Fitting_core S →
        ⁅(u : G), h⁆ ∈ Ptype_Fcore_kernel ctx := by
  unfold ptypeFCoreAction
  exact mem_ker_subgroupConjugationFactorHom_iff _ _ _ _ _ u

private theorem regularCore_complementKernel_eq_C
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Ptype_Fcompl_kernel ctx.ptypeCtx = ctx.C := by
  have hcore : Ptype_Fcore_kernel ctx.ptypeCtx = ⊥ :=
    Ptype_Fcore_kernel_trivial ctx
  rw [Ptype_Fcompl_kernel]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine mem_centralizerWithin.mpr ⟨u.property, ?_⟩
    intro h hh
    have hcomm := (regularCore_mem_actionKernel ctx.ptypeCtx u).mp hu h hh
    rw [hcore] at hcomm
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (Subgroup.mem_bot.mp hcomm)).symm
  · intro hx
    obtain ⟨hxU, hxcent⟩ := mem_centralizerWithin.mp hx
    let u : U := ⟨x, hxU⟩
    refine ⟨u, (regularCore_mem_actionKernel ctx.ptypeCtx u).mpr ?_, rfl⟩
    intro h hh
    rw [hcore]
    exact Subgroup.mem_bot.mpr
      (commutatorElement_eq_one_iff_mul_comm.mpr (hxcent h hh).symm)

private theorem regularCore_actionKernel_map_eq_C
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.D.C.map U.subtype = ctx.C := by
  change (ptypeFCoreAction ctx.ptypeCtx).ker.map U.subtype = ctx.C
  exact regularCore_complementKernel_eq_C ctx

private theorem regularCore_actionKernel_eq_CInU
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.D.C = ctx.CInU := by
  apply Subgroup.map_injective U.subtype_injective
  rw [regularCore_actionKernel_map_eq_C ctx]
  exact (Subgroup.map_subgroupOf_eq_of_le
    (centralizerWithin_le_left U ctx.P)).symm

private theorem regularCore_actionFactorCard_eq_u
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    pTypeActionFactorCard ctx.D = ctx.u := by
  unfold pTypeActionFactorCard
  letI : ctx.D.C.Normal := ctx.D.C_normal
  change Nat.card (U ⧸ ctx.D.C) = ctx.CInU.index
  rw [← ctx.D.C.index_eq_card, regularCore_actionKernel_eq_CInU ctx]

@[simp] private theorem regularCore_actionPrime
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.D.p = ctx.p := by
  rw [Ptype_factor_action_p, Ptype_factor_prime ctx]

@[simp] private theorem regularCore_actionRank
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.D.q = ctx.q :=
  rfl

private theorem regularCore_centralizer_normalized
    {A B C : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) :
    A ≤ Subgroup.normalizer (centralizerWithin B C : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha x hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hAB ha) x).mp hx.1, ?_⟩
  intro c hc
  have hc' : a⁻¹ * c * a ∈ C := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (C : Set G)).inv_mem (hAC ha)) c).mp hc
  calc
    c * (a * x * a⁻¹) = a * ((a⁻¹ * c * a) * x) * a⁻¹ := by group
    _ = a * (x * (a⁻¹ * c * a)) * a⁻¹ := by rw [hx.2 _ hc']
    _ = (a * x * a⁻¹) * c := by group

private theorem regularCore_q_dvd_C_pred
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.q ∣ Nat.card ctx.C - 1 := by
  let J := U ⊔ W₁
  let UJ := U.subgroupOf J
  let WJ := W₁.subgroupOf J
  have hCU : ctx.C ≤ U := centralizerWithin_le_left U ctx.P
  have hWnormP : W₁ ≤ Subgroup.normalizer (ctx.P : Set G) := by
    have hSnorm : S ≤ Subgroup.normalizer (ctx.P : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub S)).mp
        (Fcore_normal S)
    exact ctx.StypeP.1.2.1.1.trans hSnorm
  have hWnormC : W₁ ≤ Subgroup.normalizer (ctx.C : Set G) :=
    regularCore_centralizer_normalized ctx.StypeP.2.1.2.2.1 hWnormP
  have hfrob : IsFrobeniusDecomposition UJ WJ := by
    simpa only [PTypeFrobeniusProduct, J, UJ, WJ] using
      (FTtypeP_facts ctx).2.2.1
  letI : MulDistribMulAction W₁ ctx.C :=
    subgroupConjugationAction ctx.C W₁ hWnormC
  have hfree : ∀ r : W₁, r ≠ 1 → ∀ c : ctx.C,
      r • c = c → c = 1 := by
    intro r hr c hc
    let rJ : WJ :=
      ⟨⟨(r : G),
          (show W₁ ≤ U ⊔ W₁ from le_sup_right) r.property⟩,
        r.property⟩
    let cJ : UJ :=
      ⟨⟨(c : G),
          (show U ≤ U ⊔ W₁ from le_sup_left) (hCU c.property)⟩,
        hCU c.property⟩
    have hrJ : rJ ≠ 1 := by
      intro h
      apply hr
      apply Subtype.ext
      simpa [rJ] using congrArg (fun z : WJ ↦ (((z : J) : G))) h
    have hcG : (r : G) * (c : G) * (r : G)⁻¹ = (c : G) := by
      simpa only [coe_subgroupConjugationAction_smul] using
        congrArg Subtype.val hc
    have hcJ : (rJ : J) * (cJ : J) * (rJ : J)⁻¹ = (cJ : J) := by
      apply Subtype.ext
      exact hcG
    have hcOne := hfrob.fixedPointFree rJ hrJ cJ hcJ
    apply Subtype.ext
    simpa [cJ] using congrArg (fun z : UJ ↦ (((z : J) : G))) hcOne
  let orbitCount := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := W₁) (X := ctx.C))
  have hcardRaw :
      Nat.card ctx.C = 1 + orbitCount * Nat.card W₁ := by
    simpa only [orbitCount] using
      natCard_eq_one_add_fixedOneOrbits_mul_natCard
        (G := W₁) (X := ctx.C) (fun r ↦ smul_one r) hfree
  have hcard :
      Nat.card ctx.C = 1 + Nat.card W₁ * orbitCount := by
    calc
      Nat.card ctx.C = 1 + orbitCount * Nat.card W₁ := hcardRaw
      _ = 1 + Nat.card W₁ * orbitCount := by rw [Nat.mul_comm]
  refine ⟨orbitCount, ?_⟩
  change Nat.card ctx.C - 1 = Nat.card W₁ * orbitCount
  rw [hcard]
  omega

private theorem regularCore_two_q_dvd_C_pred
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    2 * ctx.q ∣ Nat.card ctx.C - 1 := by
  exact (Nat.coprime_two_left.mpr (mFT_odd W₁)).mul_dvd_of_dvd_of_dvd
    (even_iff_two_dvd.mp (Nat.Odd.sub_odd (mFT_odd ctx.C) odd_one))
    (regularCore_q_dvd_C_pred ctx)

private theorem regularCore_directProduct_card
    {A B K : Subgroup G} (h : IsInternalDirectProductIn A B K) :
    Nat.card A * Nat.card B = Nat.card K := by
  simpa only [MathlibSupport.natCard_subgroupOf_eq h.left_le,
    MathlibSupport.natCard_subgroupOf_eq h.right_le] using
      h.complement.card_mul

private theorem regularCore_semidirectProduct_card
    {A B K : Subgroup G} (h : IsInternalSemidirectProductIn A B K) :
    Nat.card A * Nat.card B = Nat.card K := by
  simpa only [MathlibSupport.natCard_subgroupOf_eq h.1,
    MathlibSupport.natCard_subgroupOf_eq h.2.1] using
      h.2.2.2.card_mul

private theorem regularCore_complement_card
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Nat.card U = ctx.u * Nat.card ctx.C := by
  calc
    Nat.card U = ctx.CInU.index * Nat.card ctx.CInU :=
      ctx.CInU.index_mul_card.symm
    _ = ctx.u * Nat.card ctx.C := by
      rw [MathlibSupport.natCard_subgroupOf_eq
        (centralizerWithin_le_left U ctx.P)]

private theorem regularCore_setup_card
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Nat.card S = ctx.p ^ ctx.q * (ctx.u * Nat.card ctx.C) * ctx.q := by
  have hPcard := (FTtypeP_facts ctx).2.2.2.2.2.1
  have hderived := regularCore_semidirectProduct_card ctx.StypeP.2.1.2.2.2
  have hmaximal := regularCore_semidirectProduct_card ctx.StypeP.1.2.2.2
  calc
    Nat.card S = Nat.card ctx.PU * ctx.q := by
      simpa only [FTTypePSetupContext.q] using hmaximal.symm
    _ = (Nat.card ctx.P * Nat.card U) * ctx.q := by rw [hderived]
    _ = ctx.p ^ ctx.q * (ctx.u * Nat.card ctx.C) * ctx.q := by
      rw [hPcard, regularCore_complement_card ctx]

private def regularCore_coefficient (p q : ℕ) : ℝ :=
  let qm1 : ℝ := (q - 1 : ℕ)
  1 - qm1⁻¹ - qm1 / (q : ℝ) ^ p +
    (qm1 * (q : ℝ) ^ p)⁻¹

/-! Replacement: ratio coefficient and exceptional arithmetic. -/

namespace FTTypePRegularCorePrimesRegInternal

private theorem ratioCoefficient_eq
    {p q : ℕ} (hp2 : 2 ≤ p) (hq2 : 2 ≤ q) :
    regularCore_coefficient p q =
      ((q : ℝ) - 2) / ((q : ℝ) - 1) *
        (1 - 1 / (q : ℝ) ^ (p - 1)) := by
  unfold regularCore_coefficient
  dsimp only
  have hqPos : 0 < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hqNe : (q : ℝ) ≠ 0 := hqPos.ne'
  have hqTwo : (2 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hq2
  have hqm1Pos : 0 < (q : ℝ) - 1 := by
    linarith
  have hqm1Ne : (q : ℝ) - 1 ≠ 0 := hqm1Pos.ne'
  have hpSplit : p = (p - 1) + 1 := by omega
  have hpowSplit :
      (q : ℝ) ^ p = (q : ℝ) ^ (p - 1) * (q : ℝ) := by
    calc
      (q : ℝ) ^ p = (q : ℝ) ^ ((p - 1) + 1) :=
        congrArg (fun n : ℕ ↦ (q : ℝ) ^ n) hpSplit
      _ = (q : ℝ) ^ (p - 1) * (q : ℝ) := by
        rw [pow_succ]
  rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one, hpowSplit]
  field_simp [hqNe, hqm1Ne] <;> ring

private theorem ratioCoefficient_gt_four_fifths
    {p q : ℕ} (hp3 : 3 ≤ p) (hq7 : 7 ≤ q) :
    (4 : ℝ) / 5 < regularCore_coefficient p q := by
  rw [ratioCoefficient_eq (by omega) (by omega)]
  have hqReal : (7 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq7
  have hdenPos : 0 < (q : ℝ) - 1 := by nlinarith
  have hfirst :
      (5 : ℝ) / 6 ≤ ((q : ℝ) - 2) / ((q : ℝ) - 1) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6) hdenPos).2
    nlinarith
  have hpowNat : 49 ≤ q ^ (p - 1) := by
    calc
      49 = 7 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq7 2
      _ ≤ q ^ (p - 1) :=
        Nat.pow_le_pow_right (by omega : 0 < q) (by omega)
  have hpowReal : (49 : ℝ) ≤ (q : ℝ) ^ (p - 1) := by
    exact_mod_cast hpowNat
  have hinv : 1 / (q : ℝ) ^ (p - 1) ≤ (1 : ℝ) / 49 :=
    one_div_le_one_div_of_le (by norm_num) hpowReal
  have hsecond :
      (48 : ℝ) / 49 ≤ 1 - 1 / (q : ℝ) ^ (p - 1) := by
    nlinarith
  have hfirstNonneg :
      0 ≤ ((q : ℝ) - 2) / ((q : ℝ) - 1) :=
    div_nonneg (by nlinarith) hdenPos.le
  calc
    (4 : ℝ) / 5 < ((5 : ℝ) / 6) * ((48 : ℝ) / 49) := by
      norm_num
    _ ≤ ((q : ℝ) - 2) / ((q : ℝ) - 1) *
          (1 - 1 / (q : ℝ) ^ (p - 1)) :=
      mul_le_mul hfirst hsecond (by norm_num) hfirstNonneg

private theorem ratioCoefficient_gt_seven_tenths
    {p q : ℕ} (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) :
    (7 : ℝ) / 10 < regularCore_coefficient p q := by
  rw [ratioCoefficient_eq (by omega) (by omega)]
  have hqReal : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq5
  have hdenPos : 0 < (q : ℝ) - 1 := by nlinarith
  have hfirst :
      (3 : ℝ) / 4 ≤ ((q : ℝ) - 2) / ((q : ℝ) - 1) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hdenPos).2
    nlinarith
  have hpowNat : 25 ≤ q ^ (p - 1) := by
    calc
      25 = 5 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq5 2
      _ ≤ q ^ (p - 1) :=
        Nat.pow_le_pow_right (by omega : 0 < q) (by omega)
  have hpowReal : (25 : ℝ) ≤ (q : ℝ) ^ (p - 1) := by
    exact_mod_cast hpowNat
  have hinv : 1 / (q : ℝ) ^ (p - 1) ≤ (1 : ℝ) / 25 :=
    one_div_le_one_div_of_le (by norm_num) hpowReal
  have hsecond :
      (24 : ℝ) / 25 ≤ 1 - 1 / (q : ℝ) ^ (p - 1) := by
    nlinarith
  have hfirstNonneg :
      0 ≤ ((q : ℝ) - 2) / ((q : ℝ) - 1) :=
    div_nonneg (by nlinarith) hdenPos.le
  calc
    (7 : ℝ) / 10 < ((3 : ℝ) / 4) * ((24 : ℝ) / 25) := by
      norm_num
    _ ≤ ((q : ℝ) - 2) / ((q : ℝ) - 1) *
          (1 - 1 / (q : ℝ) ^ (p - 1)) :=
      mul_le_mul hfirst hsecond (by norm_num) hfirstNonneg

private theorem ratioCoefficient_gt_fortynine_hundredths
    {p : ℕ} (hp5 : 5 ≤ p) :
    (49 : ℝ) / 100 < regularCore_coefficient p 3 := by
  rw [ratioCoefficient_eq (p := p) (q := 3)
    (by omega) (by norm_num)]
  have hpowNat : 81 ≤ 3 ^ (p - 1) := by
    calc
      81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (p - 1) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega)
  have hpowReal : (81 : ℝ) ≤ (3 : ℝ) ^ (p - 1) := by
    exact_mod_cast hpowNat
  have hinv : 1 / (3 : ℝ) ^ (p - 1) ≤ (1 : ℝ) / 81 :=
    one_div_le_one_div_of_le (by norm_num) hpowReal
  have hinv' : ((3 : ℝ) ^ (p - 1))⁻¹ ≤ ((81 : ℝ))⁻¹ := by
    simpa only [one_div] using hinv
  norm_num
  norm_num at hinv'
  nlinarith [hinv']

private theorem ratioCoefficient_upper
    {p q u c : ℕ}
    (hp2 : 2 ≤ p) (hq1 : 1 ≤ q)
    (hu : u ≤ (p ^ q - 1) / (p - 1))
    (hc : 0 < c)
    (hratio : regularCore_coefficient p q *
        (p : ℝ) ^ (q - 1) / (q : ℝ) <
      (u : ℝ) / (c : ℝ)) :
    regularCore_coefficient p q <
      (q : ℝ) * (p : ℝ) /
        ((c : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
  let m : ℝ := regularCore_coefficient p q
  change m * (p : ℝ) ^ (q - 1) / (q : ℝ) <
    (u : ℝ) / (c : ℝ) at hratio
  change m < (q : ℝ) * (p : ℝ) /
    ((c : ℝ) * ((p - 1 : ℕ) : ℝ))
  have hpPos : 0 < p := by omega
  have hqPos : 0 < q := by omega
  have hqRealPos : 0 < (q : ℝ) := by exact_mod_cast hqPos
  have hcRealPos : 0 < (c : ℝ) := by exact_mod_cast hc
  have hpredPos : 0 < p - 1 := Nat.sub_pos_of_lt (by omega)
  have hpredRealPos : 0 < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast hpredPos
  have hmulNat : (p - 1) * u ≤ p ^ q - 1 := by
    calc
      (p - 1) * u ≤ (p - 1) * ((p ^ q - 1) / (p - 1)) :=
        Nat.mul_le_mul_left (p - 1) hu
      _ ≤ p ^ q - 1 := Nat.mul_div_le (p ^ q - 1) (p - 1)
  have hpowNatPos : 0 < p ^ q := pow_pos hpPos q
  have hmulNatStrict : (p - 1) * u < p ^ q := by omega
  have hmulReal :
      ((p - 1 : ℕ) : ℝ) * (u : ℝ) < (p : ℝ) ^ q := by
    exact_mod_cast hmulNatStrict
  have hqSplit : q = (q - 1) + 1 := by omega
  have hpowSplit :
      (p : ℝ) ^ q = (p : ℝ) ^ (q - 1) * (p : ℝ) := by
    calc
      (p : ℝ) ^ q = (p : ℝ) ^ ((q - 1) + 1) :=
        congrArg (fun n : ℕ ↦ (p : ℝ) ^ n) hqSplit
      _ = (p : ℝ) ^ (q - 1) * (p : ℝ) := by
        rw [pow_succ]
  have hpRealPos : 0 < (p : ℝ) := by exact_mod_cast hpPos
  have hpowPredPos : 0 < (p : ℝ) ^ (q - 1) :=
    pow_pos hpRealPos (q - 1)
  have hcross :
      (m * (p : ℝ) ^ (q - 1)) * (c : ℝ) <
        (u : ℝ) * (q : ℝ) :=
    (div_lt_div_iff₀ hqRealPos hcRealPos).mp hratio
  have hcrossPred := mul_lt_mul_of_pos_right hcross hpredRealPos
  have hmulQ := mul_lt_mul_of_pos_right hmulReal hqRealPos
  have hlarge :
      (m * (c : ℝ) * ((p - 1 : ℕ) : ℝ)) *
          (p : ℝ) ^ (q - 1) <
        ((q : ℝ) * (p : ℝ)) * (p : ℝ) ^ (q - 1) := by
    calc
      (m * (c : ℝ) * ((p - 1 : ℕ) : ℝ)) *
          (p : ℝ) ^ (q - 1) =
          ((m * (p : ℝ) ^ (q - 1)) * (c : ℝ)) *
            ((p - 1 : ℕ) : ℝ) := by ring
      _ < ((u : ℝ) * (q : ℝ)) * ((p - 1 : ℕ) : ℝ) :=
        hcrossPred
      _ = (((p - 1 : ℕ) : ℝ) * (u : ℝ)) * (q : ℝ) := by ring
      _ < (p : ℝ) ^ q * (q : ℝ) := hmulQ
      _ = ((q : ℝ) * (p : ℝ)) * (p : ℝ) ^ (q - 1) := by
        rw [hpowSplit]
        ring
  have hcancel :
      m * (c : ℝ) * ((p - 1 : ℕ) : ℝ) <
        (q : ℝ) * (p : ℝ) :=
    lt_of_mul_lt_mul_right hlarge hpowPredPos.le
  apply (lt_div_iff₀ (mul_pos hcRealPos hpredRealPos)).2
  simpa only [mul_assoc] using hcancel

private theorem ratio_exception
    {p q u c : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q)
    (hu : u ≤ (p ^ q - 1) / (p - 1))
    (hc : 1 < c)
    (hdiv : 2 * q ∣ c - 1)
    (hcop : Nat.Coprime p c)
    (hratio :
      let qm1 : ℝ := (q - 1 : ℕ)
      (1 - qm1⁻¹ - qm1 / (q : ℝ) ^ p +
          (qm1 * (q : ℝ) ^ p)⁻¹) *
            (p : ℝ) ^ (q - 1) / (q : ℝ) <
        (u : ℝ) / (c : ℝ)) :
    q = 3 ∧ p = 5 ∧ c = 7 := by
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpodd
  have hq3Lower : 3 ≤ q := hq.odd_iff.mp hqodd
  obtain ⟨k, hk⟩ := hdiv
  have hcFormula : c = 2 * q * k + 1 := by
    omega
  have hkPos : 0 < k := by
    by_contra hkNotPos
    have hkZero : k = 0 := Nat.eq_zero_of_not_pos hkNotPos
    subst k
    norm_num at hcFormula
    omega
  have hkOne : 1 ≤ k := by omega
  have hcLower : 2 * q + 1 ≤ c := by
    calc
      2 * q + 1 = (2 * q) * 1 + 1 := by ring
      _ ≤ (2 * q) * k + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (2 * q) hkOne) 1
      _ = c := hcFormula.symm
  have hratioCoefficient :
      regularCore_coefficient p q *
          (p : ℝ) ^ (q - 1) / (q : ℝ) <
        (u : ℝ) / (c : ℝ) := by
    simpa only [regularCore_coefficient] using hratio
  have hmUpper := ratioCoefficient_upper
    (p := p) (q := q) (u := u) (c := c)
    (by omega) (by omega) hu (by omega) hratioCoefficient
  have hq3 : q = 3 := by
    by_contra hqNe3
    have hq5 : 5 ≤ q := by
      rcases hqodd with ⟨aq, haq⟩
      omega
    by_cases hqEq5 : q = 5
    · subst q
      have hmLower := ratioCoefficient_gt_seven_tenths
        (p := p) (q := 5) hp3 (by norm_num)
      have hc11 : 11 ≤ c := by
        norm_num at hcLower ⊢
        exact hcLower
      by_cases hpEq3 : p = 3
      · subst p
        have hfrac :
            (5 : ℝ) * (3 : ℝ) /
                ((c : ℝ) * (((3 - 1 : ℕ) : ℝ))) ≤
              (15 : ℝ) / 22 := by
          have hcReal : (11 : ℝ) ≤ (c : ℝ) := by
            exact_mod_cast hc11
          have hden : 0 < (c : ℝ) * (((3 - 1 : ℕ) : ℝ)) := by
            have hcPosReal : 0 < (c : ℝ) := by
              exact_mod_cast (show 0 < c by omega)
            positivity
          apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 22)).2
          norm_num
          nlinarith
        have hbad : (7 : ℝ) / 10 < (15 : ℝ) / 22 :=
          lt_trans hmLower (lt_of_lt_of_le hmUpper hfrac)
        norm_num at hbad
      · have hpNe5 : p ≠ 5 := hpq
        have hp7 : 7 ≤ p := by
          rcases hpodd with ⟨ap, hap⟩
          omega
        have hpReal : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp7
        have hcReal : (11 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc11
        have hpredCast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
        have hden : 0 < (c : ℝ) * ((p - 1 : ℕ) : ℝ) := by
          have hcPosReal : 0 < (c : ℝ) := by
            exact_mod_cast (show 0 < c by omega)
          have hpredPosReal : 0 < ((p - 1 : ℕ) : ℝ) := by
            exact_mod_cast (show 0 < p - 1 by omega)
          exact mul_pos hcPosReal hpredPosReal
        have hfrac :
            (5 : ℝ) * (p : ℝ) /
                ((c : ℝ) * ((p - 1 : ℕ) : ℝ)) ≤
              (3 : ℝ) / 5 := by
          apply (div_le_iff₀ hden).2
          rw [hpredCast]
          have hcpred :
              (11 : ℝ) * ((p : ℝ) - 1) ≤
                (c : ℝ) * ((p : ℝ) - 1) :=
            mul_le_mul_of_nonneg_right hcReal (by nlinarith)
          nlinarith
        have hbad : (7 : ℝ) / 10 < (3 : ℝ) / 5 :=
          lt_trans hmLower (lt_of_lt_of_le hmUpper hfrac)
        norm_num at hbad
    · have hq7 : 7 ≤ q := by
        rcases hqodd with ⟨aq, haq⟩
        omega
      have hmLower := ratioCoefficient_gt_four_fifths hp3 hq7
      have hpReal : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      have hqReal : (7 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq7
      have hcLowerReal : 2 * (q : ℝ) + 1 ≤ (c : ℝ) := by
        exact_mod_cast hcLower
      have hpredCast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
      have hden : 0 < (c : ℝ) * ((p - 1 : ℕ) : ℝ) := by
        have hcPosReal : 0 < (c : ℝ) := by
          exact_mod_cast (show 0 < c by omega)
        have hpredPosReal : 0 < ((p - 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < p - 1 by omega)
        exact mul_pos hcPosReal hpredPosReal
      have hfrac :
          (q : ℝ) * (p : ℝ) /
              ((c : ℝ) * ((p - 1 : ℕ) : ℝ)) ≤
            (3 : ℝ) / 4 := by
        apply (div_le_iff₀ hden).2
        rw [hpredCast]
        have hbase :
            4 * (q : ℝ) * (p : ℝ) ≤
              3 * (2 * (q : ℝ) + 1) * ((p : ℝ) - 1) := by
          have hnonneg : 0 ≤ (q : ℝ) * ((p : ℝ) - 3) :=
            mul_nonneg (by positivity) (by nlinarith)
          nlinarith
        have hcpred :
            (2 * (q : ℝ) + 1) * ((p : ℝ) - 1) ≤
              (c : ℝ) * ((p : ℝ) - 1) :=
          mul_le_mul_of_nonneg_right hcLowerReal (by nlinarith)
        nlinarith
      have hbad : (4 : ℝ) / 5 < (3 : ℝ) / 4 :=
        lt_trans hmLower (lt_of_lt_of_le hmUpper hfrac)
      norm_num at hbad
  subst q
  have hp5 : 5 ≤ p := by
    rcases hpodd with ⟨ap, hap⟩
    omega
  have hmLower := ratioCoefficient_gt_fortynine_hundredths hp5
  have hcFormula3 : c = 6 * k + 1 := by
    norm_num at hcFormula
    exact hcFormula
  have hc7 : c = 7 := by
    by_contra hcNe7
    have hkNeOne : k ≠ 1 := by
      intro hkOneEq
      subst k
      norm_num at hcFormula3
      exact hcNe7 hcFormula3
    have hkTwo : 2 ≤ k := by omega
    have hc13 : 13 ≤ c := by omega
    have hpReal : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
    have hcReal : (13 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc13
    have hpredCast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    have hden : 0 < (c : ℝ) * ((p - 1 : ℕ) : ℝ) := by
      have hcPosReal : 0 < (c : ℝ) := by
        exact_mod_cast (show 0 < c by omega)
      have hpredPosReal : 0 < ((p - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < p - 1 by omega)
      exact mul_pos hcPosReal hpredPosReal
    have hfrac :
        (3 : ℝ) * (p : ℝ) /
            ((c : ℝ) * ((p - 1 : ℕ) : ℝ)) ≤
          (3 : ℝ) / 8 := by
      apply (div_le_iff₀ hden).2
      rw [hpredCast]
      have hcpred :
          (13 : ℝ) * ((p : ℝ) - 1) ≤
            (c : ℝ) * ((p : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hcReal (by nlinarith)
      nlinarith
    have hbad : (49 : ℝ) / 100 < (3 : ℝ) / 8 :=
      lt_trans hmLower (lt_of_lt_of_le hmUpper hfrac)
    norm_num at hbad
  have hmUpper7 :
      regularCore_coefficient p 3 <
        (3 : ℝ) * (p : ℝ) /
          ((7 : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
    simpa only [hc7, Nat.cast_ofNat] using hmUpper
  have hpLt11 : p < 11 := by
    by_contra hpNotLt
    have hp11 : 11 ≤ p := by omega
    have hpReal : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp11
    have hpredCast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    have hden : 0 < (7 : ℝ) * ((p - 1 : ℕ) : ℝ) := by
      have hpredPosReal : 0 < ((p - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < p - 1 by omega)
      positivity
    have hfrac :
        (3 : ℝ) * (p : ℝ) /
            ((7 : ℝ) * ((p - 1 : ℕ) : ℝ)) ≤
          (12 : ℝ) / 25 := by
      apply (div_le_iff₀ hden).2
      rw [hpredCast]
      nlinarith
    have hbad : (49 : ℝ) / 100 < (12 : ℝ) / 25 :=
      lt_trans hmLower (lt_of_lt_of_le hmUpper7 hfrac)
    norm_num at hbad
  have hcop7 : Nat.Coprime p 7 := by
    simpa only [hc7] using hcop
  have hpNe7 : p ≠ 7 := by
    intro hp7
    subst p
    norm_num at hcop7
  have hpNe9 : p ≠ 9 := by
    intro hp9
    subst p
    norm_num at hp
  have hpEq5 : p = 5 := by
    rcases hpodd with ⟨ap, hap⟩
    omega
  exact ⟨rfl, hpEq5, hc7⟩

end FTTypePRegularCorePrimesRegInternal

open FTTypePRegularCorePrimesRegInternal

/-! Replacement: regular F-core public endpoints. -/

/-- `PFsection13.v: FTtypeP_Ind_Fitting_reg_Fcore`. -/
theorem FTtypeP_Ind_Fitting_reg_Fcore
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (lambda : ClassFunction S ℂ)
    (Slam : lambda ∈ ftTypePCoreFamily S)
    (irrHlam : lambda ∈ irr_Ind_Fitting S) :
    Nat.card ctx.C = 1 := by
  apply Nat.le_antisymm
  · by_contra hnot
    have hcgt : 1 < Nat.card ctx.C := Nat.lt_of_not_ge hnot
    have hprimes :=
      FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP
    have hq : ctx.q.Prime := hprimes.1
    have hp : ctx.p.Prime := hprimes.2
    have hpq : ctx.p ≠ ctx.q := by
      intro hpq'
      have hcop := ctx.primeTI.factor_card_coprime
      have hqOne : ctx.q = 1 := by
        change Nat.Coprime ctx.q ctx.p at hcop
        rw [hpq'] at hcop
        exact (Nat.coprime_self ctx.q).mp hcop
      exact hq.ne_one hqOne
    have hPCoprimeU : Nat.Coprime ctx.p (Nat.card U) := by
      have hcop : Nat.Coprime (Nat.card ctx.P) (Nat.card U) :=
        (Ptype_Fcore_coprime ctx.ptypeCtx).coprime_dvd_right
          (Subgroup.card_dvd_of_le
            (show U ≤ U ⊔ W₁ from le_sup_left))
      have hPcard := (FTtypeP_facts ctx).2.2.2.2.2.1
      rw [hPcard] at hcop
      exact (Nat.coprime_pow_left_iff hq.pos ctx.p (Nat.card U)).mp hcop
    have hPCoprimeC : Nat.Coprime ctx.p (Nat.card ctx.C) :=
      hPCoprimeU.coprime_dvd_right
        (Subgroup.card_dvd_of_le (centralizerWithin_le_left U ctx.P))
    obtain ⟨hq3, hp5, hc7⟩ :=
      ratio_exception hp hq hpq
        (mFT_odd W₂) (mFT_odd W₁)
        (FTtypeP_facts ctx).2.2.2.2.2.2.1 hcgt
        (regularCore_two_q_dvd_C_pred ctx)
        hPCoprimeC
        (FTtypeP_compl_ker_ratio_lb ctx lambda Slam irrHlam)
    have hGalois : ctx.galoisAlternative := by
      by_contra hnotGal
      let data := typeP_Galois_Pn ctx.actionHypotheses hnotGal
      let K := pointwiseActionKernel ctx.D.U_action data.H₁
      let a := K.index
      have ha_gt : 1 < a := by
        simpa only [a, K, data] using data.index_gt_one
      have ha_dvd : a ∣ 4 := by
        simpa only [a, K, data, regularCore_actionPrime ctx, hp5]
          using data.index_dvd_prime_pred
      have ha_odd : Odd a :=
        (mFT_odd U).of_dvd_nat K.index_dvd_card
      have ha_le : a ≤ 4 := Nat.le_of_dvd (by norm_num) ha_dvd
      have ha3 : a = 3 := by
        rcases ha_odd with ⟨k, hk⟩
        omega
      rw [ha3] at ha_dvd
      norm_num at ha_dvd
    let data := typeP_Galois_P ctx.actionHypotheses hGalois
    have huQuot : Nat.card (U ⧸ ctx.D.C) = ctx.u := by
      simpa only [pTypeActionFactorCard] using
        regularCore_actionFactorCard_eq_u ctx
    have huDvd : ctx.u ∣ 31 := by
      have h := data.complement_factor_dvd
      rw [huQuot, regularCore_actionPrime ctx,
        regularCore_actionRank ctx, hp5, hq3] at h
      norm_num at h ⊢
      exact h
    have hPcard : Nat.card ctx.P = 125 := by
      have h := (FTtypeP_facts ctx).2.2.2.2.2.1
      rw [hp5, hq3] at h
      norm_num at h ⊢
      exact h
    let pctx := typeP_context S U W W₁ W₂ defW ctx.StypeP
    have hHcard : Nat.card ctx.H = 875 := by
      have h := regularCore_directProduct_card pctx.fitting_decomposition
      rw [hPcard, hc7] at h
      norm_num at h ⊢
      exact h.symm
    have hHS : ctx.H ≤ S := fittingWithin_le S
    let HS : Subgroup S := ctx.H.subgroupOf S
    have hHScard : Nat.card HS = 875 := by
      rw [MathlibSupport.natCard_subgroupOf_eq hHS, hHcard]
    have hidx : HS.index = 3 * ctx.u := by
      apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 875)
      calc
        875 * HS.index = Nat.card HS * HS.index := by rw [hHScard]
        _ = Nat.card S := HS.card_mul_index
        _ = ctx.p ^ ctx.q * (ctx.u * Nat.card ctx.C) * ctx.q :=
          regularCore_setup_card ctx
        _ = 875 * (3 * ctx.u) := by
          rw [hp5, hq3, hc7]
          ring
    have huCases : ctx.u = 1 ∨ ctx.u = 31 :=
      (Nat.dvd_prime (by norm_num)).mp huDvd
    have hHallCoprime : Nat.Coprime (Nat.card HS) HS.index := by
      rw [hHScard, hidx]
      rcases huCases with hu1 | hu31
      · rw [hu1]
        norm_num
      · rw [hu31]
        norm_num
    have hHleP : ctx.H ≤ ctx.P :=
      Fcore_max (isHall_primeSupport HS hHallCoprime) hHS
        (fittingWithin_subgroupOf_normal S)
        (fittingWithin_isNilpotent S)
    have hCleH : ctx.C ≤ ctx.H :=
      pctx.fitting_decomposition.right_le
    have hCleP : ctx.C ≤ ctx.P := hCleH.trans hHleP
    have hCleU : ctx.C ≤ U := centralizerWithin_le_left U ctx.P
    have hInner : IsInternalSemidirectProductIn ctx.P U ctx.PU :=
      ctx.StypeP.2.1.2.2.2
    have hdisPU : Disjoint ctx.P U :=
      FTContextInternal.ambient_disjoint_of_subgroupOf8
        hInner.1 hInner.2.1 hInner.2.2.2.disjoint
    have hCbot : ctx.C = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact hdisPU.le_bot ⟨hCleP hx, hCleU hx⟩
    have hCone : Nat.card ctx.C = 1 := by
      rw [hCbot]
      simp
    omega
  · exact Nat.card_pos

/-- `PFsection13.v: FTtypeP_reg_Fcore`. -/
theorem FTtypeP_reg_Fcore
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.C = ⊥ := by
  by_cases hhas : ∃ lambda ∈ ftTypePCoreFamily S,
      lambda ∈ irr_Ind_Fitting S
  · obtain ⟨lambda, Slam, irrHlam⟩ := hhas
    exact Subgroup.eq_bot_of_card_eq ctx.C
      (FTtypeP_Ind_Fitting_reg_Fcore ctx lambda Slam irrHlam)
  · exact (FTtypeP_no_Ind_Fitting_facts ctx hhas).2.1

/-- `PFsection13.v: Ptype_Fcompl_kernel_trivial`. -/
theorem Ptype_Fcompl_kernel_trivial
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Ptype_Fcompl_kernel ctx.ptypeCtx = ⊥ := by
  calc
    Ptype_Fcompl_kernel ctx.ptypeCtx = ctx.C :=
      regularCore_complementKernel_eq_C ctx
    _ = ⊥ := FTtypeP_reg_Fcore ctx
private theorem regularCore_coefficient_gt_half
    {p q : ℕ} (hp : 2 ≤ p) (hq : 5 ≤ q) :
    (1 : ℝ) / 2 < regularCore_coefficient p q := by
  let R : ℝ := (q - 1 : ℕ)
  let Q : ℝ := q
  let X : ℝ := Q ^ p
  have hRpos : 0 < R := by
    dsimp only [R]
    exact_mod_cast (show 0 < q - 1 by omega)
  have hRge : (4 : ℝ) ≤ R := by
    dsimp only [R]
    exact_mod_cast (show 4 ≤ q - 1 by omega)
  have hQpos : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast (show 0 < q by omega)
  have hXpos : 0 < X := pow_pos hQpos p
  have hfourNat : 4 * (q - 1) ≤ q ^ p := by
    calc
      4 * (q - 1) ≤ q * (q - 1) :=
        Nat.mul_le_mul_right (q - 1) (by omega)
      _ ≤ q * q := Nat.mul_le_mul_left q (Nat.sub_le q 1)
      _ = q ^ 2 := by ring
      _ ≤ q ^ p := Nat.pow_le_pow_right (by omega) hp
  have hfour : (4 : ℝ) * R ≤ X := by
    dsimp only [R, X, Q]
    exact_mod_cast hfourNat
  have hinvR : R⁻¹ ≤ (1 : ℝ) / 4 := by
    have h :=
      (inv_le_inv₀ hRpos (by norm_num : (0 : ℝ) < 4)).2 hRge
    simpa only [one_div] using h
  have hRdivX : R / X ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hXpos).2
    nlinarith [hfour]
  have hpositiveTail : 0 < (R * X)⁻¹ :=
    inv_pos.mpr (mul_pos hRpos hXpos)
  change (1 : ℝ) / 2 < 1 - R⁻¹ - R / X + (R * X)⁻¹
  nlinarith

private theorem regularCore_coefficient_three_lower
    {p : ℕ} (hp : 3 ≤ p) :
    (23 : ℝ) / 54 ≤ regularCore_coefficient p 3 := by
  let X : ℝ := (3 : ℝ) ^ p
  have hXpos : 0 < X := by positivity
  have hXge : (27 : ℝ) ≤ X := by
    dsimp only [X]
    exact_mod_cast
      (Nat.pow_le_pow_right (by decide : 0 < 3) hp)
  have hfrac : (2 : ℝ) / X ≤ (2 : ℝ) / 27 := by
    apply (div_le_iff₀ hXpos).2
    nlinarith
  have htail : 0 ≤ X⁻¹ * (2 : ℝ)⁻¹ :=
    mul_nonneg (inv_nonneg.mpr hXpos.le)
      (inv_nonneg.mpr (by norm_num))
  change (23 : ℝ) / 54 ≤
    1 - (2 : ℝ)⁻¹ - 2 / X + ((2 : ℝ) * X)⁻¹
  rw [mul_inv_rev]
  calc
    (23 : ℝ) / 54 =
        1 - (2 : ℝ)⁻¹ - (2 : ℝ) / 27 + 0 := by
      norm_num
    _ ≤ 1 - (2 : ℝ)⁻¹ - 2 / X + X⁻¹ * (2 : ℝ)⁻¹ := by
      linarith

private theorem nonGalois_two_mul_lt_two_pow_pred
    (q : ℕ) (hq : 5 ≤ q) :
    2 * q < 2 ^ (q - 1) := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
      calc
        2 * (q + 1) < 2 * (2 * q) := by omega
        _ < 2 * 2 ^ (q - 1) :=
          (Nat.mul_lt_mul_left (by decide : 0 < 2)).2 ih
        _ = 2 ^ ((q + 1) - 1) := by
          rw [show (q + 1) - 1 = q by omega]
          conv_rhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ q)]
          rw [pow_succ']

private theorem nonGalois_force_rank_three
    {p q u₀ : ℕ}
    (hp : 3 ≤ p)
    (hpOdd : Odd p)
    (hqPrime : q.Prime)
    (hqOdd : Odd q)
    (hdiv : u₀ ∣ ((p - 1) / 2) ^ (q - 1))
    (hratio :
      regularCore_coefficient p q *
          (p : ℝ) ^ (q - 1) / (q : ℝ) < (u₀ : ℝ)) :
    q = 3 := by
  by_contra hqne
  have hq3 : 3 ≤ q := hqPrime.odd_iff.mp hqOdd
  have hq5 : 5 ≤ q := by
    obtain ⟨k, hk⟩ := hqOdd
    omega
  let t := (p - 1) / 2
  let P : ℝ := p
  let Q : ℝ := q
  let T : ℝ := t
  let e := q - 1
  have htPos : 0 < t := by
    dsimp only [t]
    omega
  have htPowPos : 0 < t ^ e := pow_pos htPos e
  have huLeNat : u₀ ≤ t ^ e := Nat.le_of_dvd htPowPos hdiv
  have htwoDvd : 2 ∣ p - 1 :=
    even_iff_two_dvd.mp (Nat.Odd.sub_odd hpOdd odd_one)
  have htwoT : 2 * t = p - 1 := by
    dsimp only [t]
    exact Nat.mul_div_cancel' htwoDvd
  have htwoTle : 2 * t ≤ p := by omega
  have hPpos : 0 < P := by
    dsimp only [P]
    exact_mod_cast (show 0 < p by omega)
  have hQpos : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast hqPrime.pos
  have hPpowPos : 0 < P ^ e := pow_pos hPpos e
  have hTP : T / P ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hPpos).2
    have htwoTleReal : (2 : ℝ) * T ≤ P := by
      dsimp only [T, P]
      exact_mod_cast htwoTle
    nlinarith
  have hpowRatio :
      (T / P) ^ e ≤ ((1 : ℝ) / 2) ^ e :=
    pow_le_pow_left₀ (by positivity) hTP e
  have huReal : (u₀ : ℝ) ≤ T ^ e := by
    dsimp only [T]
    exact_mod_cast huLeNat
  have huFrac :
      (u₀ : ℝ) / P ^ e ≤ (1 : ℝ) / (2 : ℝ) ^ e := by
    calc
      (u₀ : ℝ) / P ^ e ≤ T ^ e / P ^ e :=
        div_le_div_of_nonneg_right huReal hPpowPos.le
      _ = (T / P) ^ e := by rw [div_pow]
      _ ≤ ((1 : ℝ) / 2) ^ e := hpowRatio
      _ = (1 : ℝ) / (2 : ℝ) ^ e := by
        rw [div_pow]
        simp
  have hratioMul :
      regularCore_coefficient p q * P ^ e < (u₀ : ℝ) * Q := by
    apply (div_lt_iff₀ hQpos).mp
    simpa only [P, Q, e] using hratio
  have hcoefUpper :
      regularCore_coefficient p q < Q * (u₀ : ℝ) / P ^ e := by
    apply (lt_div_iff₀ hPpowPos).2
    simpa only [mul_comm] using hratioMul
  have hcoefUpper' :
      regularCore_coefficient p q < Q / (2 : ℝ) ^ e := by
    calc
      regularCore_coefficient p q <
          Q * (u₀ : ℝ) / P ^ e := hcoefUpper
      _ = Q * ((u₀ : ℝ) / P ^ e) := by ring
      _ ≤ Q * ((1 : ℝ) / (2 : ℝ) ^ e) :=
        mul_le_mul_of_nonneg_left huFrac hQpos.le
      _ = Q / (2 : ℝ) ^ e := by ring
  have htwoPowNat : 2 * q < 2 ^ e := by
    simpa only [e] using nonGalois_two_mul_lt_two_pow_pred q hq5
  have htwoPowReal : (2 : ℝ) * Q < (2 : ℝ) ^ e := by
    dsimp only [Q]
    exact_mod_cast htwoPowNat
  have hQhalf : Q / (2 : ℝ) ^ e < (1 : ℝ) / 2 := by
    apply (div_lt_iff₀ (pow_pos (by norm_num) e)).2
    nlinarith
  have hcoefLower : (1 : ℝ) / 2 < regularCore_coefficient p q :=
    regularCore_coefficient_gt_half (by omega) hq5
  linarith

private theorem nonGalois_force_full_half_square
    {p u₀ : ℕ}
    (hp : 3 ≤ p)
    (hpOdd : Odd p)
    (hdiv : u₀ ∣ ((p - 1) / 2) ^ 2)
    (hratio :
      regularCore_coefficient p 3 * (p : ℝ) ^ 2 / 3 <
        (u₀ : ℝ)) :
    u₀ = ((p - 1) / 2) ^ 2 := by
  let t := (p - 1) / 2
  let P : ℝ := p
  let U₀ : ℝ := u₀
  have htPos : 0 < t := by
    dsimp only [t]
    omega
  have htSqPos : 0 < t ^ 2 := pow_pos htPos 2
  obtain ⟨b, hb⟩ := hdiv
  by_contra hproper
  have hbPos : 0 < b := by
    have hmulPos : 0 < u₀ * b := by
      rw [← hb]
      exact htSqPos
    exact Nat.pos_of_mul_pos_left hmulPos
  have hbNeOne : b ≠ 1 := by
    intro hbOne
    apply hproper
    simpa only [hbOne, Nat.mul_one] using hb.symm
  have hbTwo : 2 ≤ b := by omega
  have htwiceU : 2 * u₀ ≤ t ^ 2 := by
    calc
      2 * u₀ ≤ b * u₀ := Nat.mul_le_mul_right u₀ hbTwo
      _ = u₀ * b := Nat.mul_comm _ _
      _ = t ^ 2 := hb.symm
  have htwoDvd : 2 ∣ p - 1 :=
    even_iff_two_dvd.mp (Nat.Odd.sub_odd hpOdd odd_one)
  have htwoT : 2 * t = p - 1 := by
    dsimp only [t]
    exact Nat.mul_div_cancel' htwoDvd
  have hfourTSq : 4 * t ^ 2 = (p - 1) ^ 2 := by
    rw [← htwoT]
    ring
  have heighthU : 8 * u₀ ≤ (p - 1) ^ 2 := by
    nlinarith
  have hcoef :
      (23 : ℝ) / 54 ≤ regularCore_coefficient p 3 :=
    regularCore_coefficient_three_lower hp
  have hfactorNonneg : 0 ≤ P ^ 2 / (3 : ℝ) := by positivity
  have hlower : (23 : ℝ) * P ^ 2 / 162 < U₀ := by
    calc
      (23 : ℝ) * P ^ 2 / 162 =
          ((23 : ℝ) / 54) * (P ^ 2 / 3) := by ring
      _ ≤ regularCore_coefficient p 3 * (P ^ 2 / 3) :=
        mul_le_mul_of_nonneg_right hcoef hfactorNonneg
      _ = regularCore_coefficient p 3 * P ^ 2 / 3 := by ring
      _ < U₀ := by simpa only [P, U₀] using hratio
  have hupper : 8 * U₀ ≤ (P - 1) ^ 2 := by
    have hcast :
        ((8 * u₀ : ℕ) : ℝ) ≤ (((p - 1) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast heighthU
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast
    rw [Nat.cast_sub (by omega : 1 ≤ p)] at hcast
    simpa only [P, U₀, Nat.cast_one] using hcast
  have hPthree : (3 : ℝ) ≤ P := by
    dsimp only [P]
    exact_mod_cast hp
  have hPsq : (9 : ℝ) ≤ P ^ 2 := by
    nlinarith [sq_nonneg (P - 3)]
  nlinarith

/-! ### Peterfalvi (13.13), non-Galois branch -/

/-- `PFsection13.v: FTtypeP_Ind_Fitting_nonGalois_facts`. -/
theorem FTtypeP_Ind_Fitting_nonGalois_facts
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (lambda : ClassFunction S ℂ)
    (Slam : lambda ∈ ftTypePCoreFamily S)
    (irrHlam : lambda ∈ irr_Ind_Fitting S) :
    ¬ ctx.galoisAlternative →
      ctx.q = 3 ∧ Nat.card U = ((ctx.p - 1) / 2) ^ 2 := by
  intro hnonGalois
  let p := ctx.p
  let q := ctx.q
  let u₀ := ctx.u
  let t := (p - 1) / 2
  let D := ctx.D
  let hD := ctx.actionHypotheses
  let data := typeP_Galois_Pn hD hnonGalois
  let a := pTypeNonGaloisIndex hD hnonGalois
  have hprimes : q.Prime ∧ p.Prime :=
    FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP
  have hqPrime : q.Prime := hprimes.1
  have hpPrime : p.Prime := hprimes.2
  have hpOdd : Odd p := by
    change Odd (Nat.card W₂)
    exact mFT_odd W₂
  have hqOdd : Odd q := by
    change Odd (Nat.card W₁)
    exact mFT_odd W₁
  have hpThree : 3 ≤ p := hpPrime.odd_iff.mp hpOdd
  have hDp : D.p = p := by
    simpa only [D, p] using regularCore_actionPrime ctx
  have hDq : D.q = q := by
    simpa only [D, q] using regularCore_actionRank ctx
  have hCcard : Nat.card ctx.C = 1 :=
    FTtypeP_Ind_Fitting_reg_Fcore ctx lambda Slam irrHlam
  have hratio :
      regularCore_coefficient p q *
          (p : ℝ) ^ (q - 1) / (q : ℝ) < (u₀ : ℝ) := by
    have hbound := FTtypeP_compl_ker_ratio_lb ctx lambda Slam irrHlam
    simpa only [regularCore_coefficient, p, q, u₀, hCcard,
      Nat.cast_one, div_one] using hbound
  letI : D.C.Normal := D.C_normal
  obtain ⟨iota, hiota⟩ := data.complement_factor_vector
  have hvectorDvd : Nat.card (U ⧸ D.C) ∣ a ^ (D.q - 1) := by
    calc
      Nat.card (U ⧸ D.C) ∣
          Nat.card (Multiplicative (Fin (D.q - 1) → ZMod a)) :=
        Subgroup.card_dvd_of_injective iota hiota
      _ = a ^ (D.q - 1) := by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
          Nat.card_fin, Nat.card_zmod]
  have hvectorDvd' : u₀ ∣ a ^ (q - 1) := by
    dsimp only [u₀]
    rw [← regularCore_actionFactorCard_eq_u ctx]
    change Nat.card (U ⧸ D.C) ∣ a ^ (q - 1)
    simpa only [hDq] using hvectorDvd
  let K := pointwiseActionKernel ctx.D.U_action data.H₁
  have hKindexOdd : Odd K.index :=
    (mFT_odd U).of_dvd_nat K.index_dvd_card
  have haOdd : Odd a := by
    simpa only [a, pTypeNonGaloisIndex, K, data, hD, D] using hKindexOdd
  have haPred : a ∣ p - 1 := by
    have h := pTypeNonGaloisIndex_dvd_prime_pred hD hnonGalois
    change a ∣ D.p - 1 at h
    simpa only [hDp] using h
  obtain ⟨k, hk⟩ := haPred
  have hpPredEven : Even (p - 1) := Nat.Odd.sub_odd hpOdd odd_one
  have hkEven : 2 ∣ k := by
    have htwoMul : 2 ∣ a * k := by
      rw [← hk]
      exact even_iff_two_dvd.mp hpPredEven
    exact haOdd.coprime_two_right.symm.dvd_of_dvd_mul_left htwoMul
  obtain ⟨j, hj⟩ := hkEven
  have htwoDvd : 2 ∣ p - 1 := even_iff_two_dvd.mp hpPredEven
  have haHalf : a ∣ t := by
    refine ⟨j, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
    calc
      2 * t = p - 1 := by
        dsimp only [t]
        exact Nat.mul_div_cancel' htwoDvd
      _ = a * k := hk
      _ = 2 * (a * j) := by rw [hj]; ring
  have hhalfPower : u₀ ∣ t ^ (q - 1) :=
    hvectorDvd'.trans (pow_dvd_pow_of_dvd haHalf (q - 1))
  have hqThree : q = 3 :=
    nonGalois_force_rank_three
      hpThree hpOdd hqPrime hqOdd hhalfPower hratio
  have hhalfSquare : u₀ ∣ t ^ 2 := by
    simpa only [hqThree, Nat.reduceSub] using hhalfPower
  have hratioThree :
      regularCore_coefficient p 3 * (p : ℝ) ^ 2 / 3 <
        (u₀ : ℝ) := by
    simpa only [hqThree, Nat.reduceSub, Nat.cast_ofNat] using hratio
  have huSquare : u₀ = t ^ 2 :=
    nonGalois_force_full_half_square
      hpThree hpOdd hhalfSquare hratioThree
  have hCInUcard : Nat.card ctx.CInU = 1 := by
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      (centralizerWithin_le_left U ctx.P)]
    exact hCcard
  have hcardU : Nat.card U = u₀ := by
    calc
      Nat.card U = Nat.card (U ⧸ ctx.CInU) * Nat.card ctx.CInU :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup ctx.CInU
      _ = ctx.CInU.index * 1 := by
        rw [← ctx.CInU.index_eq_card, hCInUcard]
      _ = u₀ := by
        simp only [u₀, FTTypePSetupContext.u, Nat.mul_one]
  refine ⟨by simpa only [q] using hqThree, ?_⟩
  calc
    Nat.card U = u₀ := hcardU
    _ = t ^ 2 := huSquare
    _ = ((ctx.p - 1) / 2) ^ 2 := by rfl

/-- `PFsection13.v: FTtypeP_nonGalois_facts`. -/
theorem FTtypeP_nonGalois_facts
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ¬ ctx.galoisAlternative →
      ctx.q = 3 ∧ Nat.card U = ((ctx.p - 1) / 2) ^ 2 := by
  intro hnonGalois
  by_cases hex : ∃ lambda ∈ ftTypePCoreFamily S,
      lambda ∈ irr_Ind_Fitting S
  · obtain ⟨lambda, Slam, irrHlam⟩ := hex
    exact FTtypeP_Ind_Fitting_nonGalois_facts
      ctx lambda Slam irrHlam hnonGalois
  · have hfacts := FTtypeP_no_Ind_Fitting_facts ctx hex
    exact (hnonGalois hfacts.1).elim

private def regularGaloisThreshold (p q : ℕ) : ℝ :=
  (q : ℝ) * (p : ℝ) /
    (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ))

private theorem regularCore_coefficient_five_gt
    (p : ℕ) (hp3 : 3 ≤ p) :
    (7 : ℝ) / 10 < regularCore_coefficient p 5 := by
  simpa only [regularCore_coefficient] using
    (ratioCoefficient_gt_seven_tenths
      (p := p) (q := 5) hp3 (by norm_num : 5 ≤ 5))

private theorem regularCore_coefficient_large_rank_gt
    (p q : ℕ) (hp3 : 3 ≤ p) (hq7 : 7 ≤ q) :
    (4 : ℝ) / 5 < regularCore_coefficient p q := by
  simpa only [regularCore_coefficient] using
    (ratioCoefficient_gt_four_fifths
      (p := p) (q := q) hp3 hq7)

private theorem regularGaloisThreshold_lt_three_fourths
    (p q : ℕ) (hp3 : 3 ≤ p) :
    regularGaloisThreshold p q < (3 : ℝ) / 4 := by
  have hpSub : 0 < p - 1 := by omega
  have hden :
      0 < (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
    positivity
  rw [regularGaloisThreshold, div_lt_iff₀ hden]
  push_cast [show 1 ≤ p by omega]
  have hp3Real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hnonneg : 0 ≤ (q : ℝ) * ((p : ℝ) - 3) := by
    exact mul_nonneg (Nat.cast_nonneg q) (sub_nonneg.mpr hp3Real)
  nlinarith

private theorem regularGaloisThreshold_five_lt
    (p : ℕ) (hp3 : 3 ≤ p) :
    regularGaloisThreshold p 5 < (7 : ℝ) / 10 := by
  have hpSub : 0 < p - 1 := Nat.sub_pos_of_lt (by omega)
  have hden :
      0 < (((2 * 5 + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
    have hpSubReal : 0 < ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast hpSub
    positivity
  rw [regularGaloisThreshold, div_lt_iff₀ hden]
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  have hp3Real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  norm_num at ⊢
  nlinarith

private theorem regularCore_coefficient_three
    (p : ℕ) (hp1 : 1 ≤ p) :
    regularCore_coefficient p 3 =
      (1 : ℝ) / 2 - 1 / (2 * (3 : ℝ) ^ (p - 1)) := by
  have hpow :
      (3 : ℝ) ^ p = (3 : ℝ) ^ (p - 1) * 3 := by
    calc
      (3 : ℝ) ^ p = (3 : ℝ) ^ ((p - 1) + 1) := by
        congr 1
        omega
      _ = (3 : ℝ) ^ (p - 1) * 3 := pow_succ _ _
  change
    1 - (2 : ℝ)⁻¹ - 2 / (3 : ℝ) ^ p +
        ((2 : ℝ) * (3 : ℝ) ^ p)⁻¹ =
      (1 : ℝ) / 2 - 1 / (2 * (3 : ℝ) ^ (p - 1))
  rw [hpow]
  field_simp
  ring

private theorem regularGalois_three_lower
    (p : ℕ) (hp : p.Prime) (hpOdd : Odd p) (hp5 : 5 ≤ p) :
    (((p ^ 2 - 1 : ℕ) : ℝ) / 6) <
      regularCore_coefficient p 3 * (p : ℝ) ^ 2 / 3 := by
  have hexponential :=
    lbound_expn_odd_prime 3 p (by norm_num) hpOdd
      Nat.prime_three hp (by omega : 3 ≠ p)
  have hpowNat : 3 ^ p = 3 ^ (p - 1) * 3 := by
    calc
      3 ^ p = 3 ^ ((p - 1) + 1) := by
        congr 1
        omega
      _ = 3 ^ (p - 1) * 3 := pow_succ _ _
  rw [hpowNat] at hexponential
  have hpSqLt : p ^ 2 < 3 ^ (p - 1) := by omega
  have hpSqLtReal : (p : ℝ) ^ 2 < (3 : ℝ) ^ (p - 1) := by
    exact_mod_cast hpSqLt
  have hfraction :
      (p : ℝ) ^ 2 / (3 : ℝ) ^ (p - 1) < 1 :=
    (div_lt_one (by positivity)).2 hpSqLtReal
  rw [regularCore_coefficient_three p hp.one_le]
  have hcast : (((p ^ 2 - 1 : ℕ) : ℝ)) = (p : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub (one_le_pow₀ hp.one_le)]
    norm_num
  rw [hcast]
  have hrearrange :
      ((1 : ℝ) / 2 - 1 / (2 * (3 : ℝ) ^ (p - 1))) *
          (p : ℝ) ^ 2 / 3 =
        (p : ℝ) ^ 2 / 6 -
          ((p : ℝ) ^ 2 / (3 : ℝ) ^ (p - 1)) / 6 := by
    field_simp
    ring
  rw [hrearrange]
  nlinarith

private theorem regularCore_coefficient_lt_threshold
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (lambda : ClassFunction S ℂ)
    (Slam : lambda ∈ ftTypePCoreFamily S)
    (irrHlam : lambda ∈ irr_Ind_Fitting S)
    (b : ℕ)
    (hfactor : ctx.ustar = b * ctx.u)
    (hb : 2 * ctx.q < b) :
    regularCore_coefficient ctx.p ctx.q <
      regularGaloisThreshold ctx.p ctx.q := by
  have hprimes :=
    FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP
  have hq : ctx.q.Prime := hprimes.1
  have hp : ctx.p.Prime := hprimes.2
  have hCcard : Nat.card ctx.C = 1 :=
    FTtypeP_Ind_Fitting_reg_Fcore ctx lambda Slam irrHlam
  have hraw := FTtypeP_compl_ker_ratio_lb ctx lambda Slam irrHlam
  change
    regularCore_coefficient ctx.p ctx.q *
          (ctx.p : ℝ) ^ (ctx.q - 1) / (ctx.q : ℝ) <
      (ctx.u : ℝ) / (Nat.card ctx.C : ℝ) at hraw
  have hratio :
      regularCore_coefficient ctx.p ctx.q *
          (ctx.p : ℝ) ^ (ctx.q - 1) / (ctx.q : ℝ) <
        (ctx.u : ℝ) := by
    simpa only [hCcard, Nat.cast_one, div_one] using hraw
  let c : ℕ := 2 * ctx.q + 1
  have hcPos : 0 < c := by
    dsimp only [c]
    omega
  have hcLeB : c ≤ b := by
    dsimp only [c]
    omega
  have hscaledLe :
      c * ctx.u ≤ (ctx.p ^ ctx.q - 1) / (ctx.p - 1) := by
    change c * ctx.u ≤ ctx.ustar
    rw [hfactor]
    exact Nat.mul_le_mul_right ctx.u hcLeB
  have hcRealNe : (c : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hcPos.ne'
  have hratioScaled :
      regularCore_coefficient ctx.p ctx.q *
            (ctx.p : ℝ) ^ (ctx.q - 1) / (ctx.q : ℝ) <
        (((c * ctx.u : ℕ) : ℝ)) / (c : ℝ) := by
    norm_num only [Nat.cast_mul]
    rw [mul_div_cancel_left₀ _ hcRealNe]
    exact hratio
  have hupper := ratioCoefficient_upper
    (p := ctx.p) (q := ctx.q) (u := c * ctx.u) (c := c)
    hp.two_le hq.one_le hscaledLe hcPos hratioScaled
  dsimp only [c] at hupper
  simpa only [regularCore_coefficient, regularGaloisThreshold] using hupper
/-! ### Peterfalvi (13.15), induced local upper bound -/

/-- `PFsection13.v: FTtypeP_Ind_Fitting_Galois_ub`. -/
theorem FTtypeP_Ind_Fitting_Galois_ub
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (lambda : ClassFunction S ℂ)
    (Slam : lambda ∈ ftTypePCoreFamily S)
    (irrHlam : lambda ∈ irr_Ind_Fitting S)
    (b : ℕ)
    (hfactor : ctx.ustar = b * ctx.u) :
    b ≤ 2 * ctx.q := by
  by_contra hbLe
  have hb : 2 * ctx.q < b := by omega
  have hprimes :=
    FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP
  have hq : ctx.q.Prime := hprimes.1
  have hp : ctx.p.Prime := hprimes.2
  have hqOdd : Odd ctx.q := by
    change Odd (Nat.card W₁)
    exact mFT_odd W₁
  have hpOdd : Odd ctx.p := by
    change Odd (Nat.card W₂)
    exact mFT_odd W₂
  have hp3 : 3 ≤ ctx.p := hp.odd_iff.mp hpOdd
  have hq3 : 3 ≤ ctx.q := hq.odd_iff.mp hqOdd
  have hupper :=
    regularCore_coefficient_lt_threshold
      ctx lambda Slam irrHlam b hfactor hb
  have hqEq : ctx.q = 3 := by
    obtain ⟨k, hk⟩ := hqOdd
    rcases (show ctx.q = 3 ∨ ctx.q = 5 ∨ 7 ≤ ctx.q by omega) with
      hthree | hfive | hlarge
    · exact hthree
    · have hcoeff := regularCore_coefficient_five_gt ctx.p hp3
      have hthreshold := regularGaloisThreshold_five_lt ctx.p hp3
      rw [hfive] at hupper
      linarith
    · have hcoeff :=
        regularCore_coefficient_large_rank_gt ctx.p ctx.q hp3 hlarge
      have hthreshold :=
        regularGaloisThreshold_lt_three_fourths ctx.p ctx.q hp3
      linarith
  have hpNeQ : ctx.p ≠ ctx.q := by
    intro hpq
    have hcop := ctx.primeTI.factor_card_coprime
    change Nat.Coprime ctx.q ctx.p at hcop
    rw [hpq] at hcop
    exact hq.ne_one ((Nat.coprime_self ctx.q).mp hcop)
  have hp5 : 5 ≤ ctx.p := by
    rcases hpOdd with ⟨k, hk⟩
    omega
  have hCcard : Nat.card ctx.C = 1 :=
    FTtypeP_Ind_Fitting_reg_Fcore ctx lambda Slam irrHlam
  have hraw := FTtypeP_compl_ker_ratio_lb ctx lambda Slam irrHlam
  change
    regularCore_coefficient ctx.p ctx.q *
          (ctx.p : ℝ) ^ (ctx.q - 1) / (ctx.q : ℝ) <
      (ctx.u : ℝ) / (Nat.card ctx.C : ℝ) at hraw
  have hratio :
      regularCore_coefficient ctx.p ctx.q *
          (ctx.p : ℝ) ^ (ctx.q - 1) / (ctx.q : ℝ) <
        (ctx.u : ℝ) := by
    simpa only [hCcard, Nat.cast_one, div_one] using hraw
  have hlower := regularGalois_three_lower ctx.p hp hpOdd hp5
  rw [hqEq] at hratio
  norm_num only [Nat.reduceSub] at hratio
  have huReal : (((ctx.p ^ 2 - 1 : ℕ) : ℝ) / 6) < (ctx.u : ℝ) :=
    hlower.trans hratio
  have huNatStrict : ctx.p ^ 2 - 1 < 6 * ctx.u := by
    have hmul := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 6)).mp huReal
    have hcast :
        (((ctx.p ^ 2 - 1 : ℕ) : ℝ)) <
          (((6 * ctx.u : ℕ) : ℝ)) := by
      norm_num only [Nat.cast_mul]
      nlinarith
    exact_mod_cast hcast
  have huNat : ctx.p ^ 2 ≤ 6 * ctx.u := by omega
  have hb7 : 7 ≤ b := by omega
  have hlarge : 7 * ctx.p ^ 2 ≤ 6 * ctx.ustar := by
    calc
      7 * ctx.p ^ 2 ≤ b * ctx.p ^ 2 :=
        Nat.mul_le_mul_right (ctx.p ^ 2) hb7
      _ ≤ b * (6 * ctx.u) := Nat.mul_le_mul_left b huNat
      _ = 6 * (b * ctx.u) := by ring
      _ = 6 * ctx.ustar := by rw [← hfactor]
  have hustar : ctx.ustar = ctx.p ^ 2 + ctx.p + 1 := by
    rw [regularCore_ustar_eq_nU ctx hp, hqEq]
    simp [nU, Finset.sum_range_succ]
    ring
  rw [hustar] at hlarge
  have hpLe6 : ctx.p ≤ 6 := by nlinarith
  have hpEq : ctx.p = 5 := by
    obtain ⟨k, hk⟩ := hpOdd
    omega
  have hustarEq : ctx.ustar = 31 := by
    rw [hustar, hpEq]
    norm_num
  have hbDvd : b ∣ 31 := by
    rw [← hustarEq]
    exact ⟨ctx.u, hfactor⟩
  have hbEq : b = 31 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hbDvd with
      hbOne | hbThirtyOne
    · omega
    · exact hbThirtyOne
  have huEq : ctx.u = 1 := by
    apply Nat.mul_left_cancel (by norm_num : 0 < 31)
    simpa only [hustarEq, hbEq, Nat.mul_one] using hfactor.symm
  rw [hpEq, huEq] at hratio
  norm_num [regularCore_coefficient] at hratio

/-! ### Passing from regularity to the PF9 Galois quotient -/

private theorem regularGalois_actionKernel_eq_bot
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.D.C = ⊥ := by
  apply (Subgroup.map_eq_bot_iff_of_injective
    ctx.D.C U.subtype_injective).mp
  change (ptypeFCoreAction ctx.ptypeCtx).ker.map U.subtype = ⊥
  simpa only [Ptype_Fcompl_kernel] using
    Ptype_Fcompl_kernel_trivial ctx

private theorem regularGalois_u_eq_card
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.u = Nat.card U := by
  change (ctx.C.subgroupOf U).index = Nat.card U
  rw [FTtypeP_reg_Fcore ctx, Subgroup.bot_subgroupOf,
    Subgroup.index_bot]

/-! ### Peterfalvi (13.15), global Galois-complement cardinal -/

/-- `PFsection13.v: card_FTtypeP_Galois_compl`. -/
theorem card_FTtypeP_Galois_compl
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.galoisAlternative →
      Nat.card U =
        if Nat.ModEq ctx.q ctx.p 1 then ctx.ustar / ctx.q
        else ctx.ustar := by
  intro hGalois
  letI : ctx.D.C.Normal := ctx.D.C_normal
  have hker : ctx.D.C = ⊥ := regularGalois_actionKernel_eq_bot ctx
  have hquotCard : Nat.card (U ⧸ ctx.D.C) = Nat.card U := by
    calc
      Nat.card (U ⧸ ctx.D.C) = ctx.D.C.index :=
        ctx.D.C.index_eq_card.symm
      _ = Nat.card U := by rw [hker, Subgroup.index_bot]
  have hdivRaw :=
    (typeP_Galois_P ctx.actionHypotheses hGalois).complement_factor_dvd
  have hdiv : Nat.card U ∣ ctx.ustar := by
    simpa only [hquotCard, regularCore_actionPrime,
      regularCore_actionRank, FTTypePSetupContext.ustar] using hdivRaw
  have huCard : ctx.u = Nat.card U := regularGalois_u_eq_card ctx
  have huDvd : ctx.u ∣ ctx.ustar := by simpa only [huCard] using hdiv
  obtain ⟨b, hfactorRaw⟩ := huDvd
  have hfactor : ctx.ustar = b * ctx.u := by
    simpa only [Nat.mul_comm] using hfactorRaw
  have hbBound : b ≤ 2 * ctx.q := by
    by_cases hex : ∃ lambda ∈ ftTypePCoreFamily S,
        lambda ∈ irr_Ind_Fitting S
    · obtain ⟨lambda, Slam, irrHlam⟩ := hex
      exact FTtypeP_Ind_Fitting_Galois_ub
        ctx lambda Slam irrHlam b hfactor
    · have hno := FTtypeP_no_Ind_Fitting_facts ctx hex
      have huUstar : ctx.u = ctx.ustar := by
        simpa only [FTTypePSetupContext.ustar] using hno.2.2
      have hbOne : b = 1 := by
        have huPos : 0 < ctx.u := by
          simpa only [huCard] using (Nat.card_pos (α := U))
        apply Nat.mul_right_cancel huPos
        calc
          b * ctx.u = ctx.ustar := hfactor.symm
          _ = ctx.u := huUstar.symm
          _ = 1 * ctx.u := (Nat.one_mul _).symm
      rw [hbOne]
      have hqPos : 0 < ctx.q := Nat.card_pos
      omega
  have hcases := FTtypeP_primes_mod_cases ctx
  have hoddUstar : Odd ctx.ustar := hcases.1
  have hbDvd : b ∣ ctx.ustar := ⟨ctx.u, hfactor⟩
  have hoddB : Odd b := Odd.of_dvd_nat hoddUstar hbDvd
  have hqPrime : ctx.q.Prime :=
    (FTtypeP_primes S U W W₁ W₂ defW
      ctx.maxS ctx.StypeP).1
  have hqOdd : Odd ctx.q := by
    change Odd (Nat.card W₁)
    exact mFT_odd W₁
  have hUlePU : U ≤ ctx.PU := ctx.StypeP.2.1.2.2.2.2.1
  have hUdvdPU : Nat.card U ∣ Nat.card ctx.PU :=
    Subgroup.card_dvd_of_le hUlePU
  have hcopQCardU : Nat.Coprime ctx.q (Nat.card U) :=
    (ctx.primeTI.kernel_complement_card_coprime.of_dvd_left
      hUdvdPU).symm
  have hcopQU : Nat.Coprime ctx.q ctx.u := by
    rw [huCard]
    exact hcopQCardU
  by_cases hpOne : Nat.ModEq ctx.q ctx.p 1
  · have hqDvdUstar : ctx.q ∣ ctx.ustar := hcases.2.1 hpOne
    have hqDvdBU : ctx.q ∣ b * ctx.u := by
      rw [← hfactor]
      exact hqDvdUstar
    have hqDvdB : ctx.q ∣ b :=
      hcopQU.dvd_of_dvd_mul_right hqDvdBU
    obtain ⟨c, hbc⟩ := hqDvdB
    have hcLe : c ≤ 2 := by
      apply Nat.le_of_mul_le_mul_left _ hqPrime.pos
      calc
        ctx.q * c = b := hbc.symm
        _ ≤ 2 * ctx.q := hbBound
        _ = ctx.q * 2 := by ring
    have hoddC : Odd c := by
      rw [hbc] at hoddB
      exact (Nat.odd_mul.mp hoddB).2
    have hcEq : c = 1 := by
      rcases hoddC with ⟨k, hk⟩
      omega
    have hbEq : b = ctx.q := by
      rw [hbc, hcEq, Nat.mul_one]
    rw [if_pos hpOne, ← huCard, hfactor, hbEq]
    simpa only [Nat.mul_comm] using
      (Nat.mul_div_left ctx.u hqPrime.pos).symm
  · have hmodB : Nat.ModEq ctx.q b 1 :=
      (hcases.2.2 hpOne).2.2 b hbDvd
    have hbOne : 1 ≤ b := hoddB.pos
    have hqDvdPred : ctx.q ∣ b - 1 :=
      (Nat.modEq_iff_dvd' hbOne).mp hmodB.symm
    obtain ⟨c, hbcPred⟩ := hqDvdPred
    have hbForm : b = 1 + ctx.q * c := by omega
    have hcLt : c < 2 := by
      apply lt_of_mul_lt_mul_left _ (Nat.zero_le ctx.q)
      calc
        ctx.q * c < 1 + ctx.q * c := by omega
        _ = b := hbForm.symm
        _ ≤ 2 * ctx.q := hbBound
        _ = ctx.q * 2 := by ring
    have hcEq : c = 0 := by
      by_contra hcNe
      have hcOne : c = 1 := by omega
      apply (Nat.not_even_iff_odd.mpr hoddB)
      rw [hbForm, hcOne]
      simpa only [Nat.mul_one, Nat.add_comm] using hqOdd.add_one
    have hbEq : b = 1 := by
      rw [hbForm, hcEq]
      simp
    rw [if_neg hpOne, ← huCard, hfactor, hbEq]
    simp

/-! ## Normalizer and centralizer of the second cyclic factor -/

private theorem ftTypePNormCent_semidirect_restrict_right
    {A B C D : Subgroup G}
    (h : IsInternalSemidirectProductIn A B C) (hDB : D ≤ B) :
    IsInternalSemidirectProductIn A D (A ⊔ D) := by
  have hAC : A ≤ C := h.1
  have hDC : D ≤ C := hDB.trans h.2.1
  have hCnormA : C ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAC).mp h.2.2.1
  have hAnormal : (A.subgroupOf (A ⊔ D)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le Subgroup.le_normalizer (hDC.trans hCnormA))
  have hdis : Disjoint (A.subgroupOf (A ⊔ D))
      (D.subgroupOf (A ⊔ D)) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    have hxC : (⟨(x : G), (show A ⊔ D ≤ C from
        sup_le hAC hDC) x.property⟩ : C) ∈
        (A.subgroupOf C) ⊓ (B.subgroupOf C) :=
      ⟨hx.1, hDB hx.2⟩
    have hxBot := h.2.2.2.disjoint.le_bot hxC
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact congrArg (fun w : C ↦ (w : G))
      (Subgroup.mem_bot.mp hxBot)
  refine ⟨le_sup_left, le_sup_right, hAnormal, ?_⟩
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  letI : (A.subgroupOf (A ⊔ D)).Normal := hAnormal
  rw [← Subgroup.normal_mul,
    ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.subgroupOf_self]
  rfl

private theorem ftTypePNormCent_centralizerWithin_normalized
    {A B C : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) :
    A ≤ Subgroup.normalizer (centralizerWithin B C : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha x hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hAB ha) x).mp hx.1, ?_⟩
  intro c hc
  have haInvC : a⁻¹ ∈ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normalizer (C : Set G)).inv_mem (hAC ha)
  have hc' : a⁻¹ * c * a ∈ C := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp haInvC c).mp hc
  have hcomm := hx.2 (a⁻¹ * c * a) hc'
  calc
    c * (a * x * a⁻¹) =
        a * ((a⁻¹ * c * a) * x) * a⁻¹ := by group
    _ = a * (x * (a⁻¹ * c * a)) * a⁻¹ := by rw [hcomm]
    _ = (a * x * a⁻¹) * c := by group

private theorem ftTypePNormCent_le_centralizer_sup
    {X A B : Subgroup G}
    (hA : X ≤ Subgroup.centralizer (A : Set G))
    (hB : X ≤ Subgroup.centralizer (B : Set G)) :
    X ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply Subgroup.le_centralizer_iff.mpr
  exact sup_le
    (Subgroup.le_centralizer_iff.mp hA)
    (Subgroup.le_centralizer_iff.mp hB)

private theorem ftTypePNormCent_frobenius_semiregular
    {H R : Subgroup G} (hFrob : PTypeFrobeniusProduct H R) :
    IsSemiregularConjugation H R := by
  let J : Subgroup G := H ⊔ R
  change IsFrobeniusDecomposition
    (H.subgroupOf J) (R.subgroupOf J) at hFrob
  have hHJ : H ≤ J := by
    dsimp only [J]
    exact le_sup_left
  have hRJ : R ≤ J := by
    dsimp only [J]
    exact le_sup_right
  intro r hr h hh
  let rJ : R.subgroupOf J :=
    ⟨⟨(r : G), hRJ r.property⟩, r.property⟩
  let hJ : H.subgroupOf J :=
    ⟨⟨(h : G), hHJ h.property⟩, h.property⟩
  have hrJ : rJ ≠ 1 := by
    intro hrOne
    apply hr
    apply Subtype.ext
    exact congrArg (fun z : R.subgroupOf J ↦ (((z : J) : G))) hrOne
  have hfix : (rJ : J) * (hJ : J) * (rJ : J)⁻¹ = (hJ : J) := by
    apply Subtype.ext
    exact hh
  have hhOne := hFrob.fixedPointFree rJ hrJ hJ hfix
  apply Subtype.ext
  exact congrArg (fun z : H.subgroupOf J ↦ (((z : J) : G))) hhOne

/-! The TI condition on the regular F-core puts the full normalizer of
`W₂` back inside the chosen maximal subgroup. -/
private theorem ftTypePNormCent_normalizer_le_S
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Subgroup.normalizer (W₂ : Set G) ≤ S := by
  have hW₂P : W₂ ≤ ctx.P := ctx.StypeP.2.2.2.1.2.2.1
  have hW₂ne : W₂ ≠ ⊥ := ctx.StypeP.2.2.2.1.2.1
  have hP_eq_H : ctx.P = ctx.H := by
    have hdecomp :=
      (typeP_context S U W W₁ W₂ defW ctx.StypeP).fitting_decomposition
    have hsup : ctx.P ⊔ ctx.C = ctx.H :=
      FTContextInternal.directProduct_sup_eq8 hdecomp
    rw [FTtypeP_reg_Fcore ctx, sup_bot_eq] at hsup
    exact hsup
  have hP_TI : IsNormalizedTI
      (subgroupNonidentity ctx.P) (⊤ : Subgroup G) S := by
    have hcommon := compl_of_typeII_IV S U W W₁ W₂ defW
      ctx.maxS ctx.StypeP ctx.notType5
    simpa only [hP_eq_H] using hcommon.2.2.2
  intro y hy
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW₂ne
  have hxP : (x : G) ∈ subgroupNonidentity ctx.P := by
    refine ⟨hW₂P x.property, ?_⟩
    intro hxOne
    exact hxne (Subtype.ext hxOne)
  have hxConjW₂ : y⁻¹ * (x : G) * y ∈ W₂ := by
    have hxSet : (x : G) ∈ (W₂ : Set G) := x.property
    have hconjSet : y⁻¹ * (x : G) * y ∈ (W₂ : Set G) :=
      ((Subgroup.mem_set_normalizer_iff''.mp hy) (x : G)).mp hxSet
    exact hconjSet
  have hxConjP : y⁻¹ * (x : G) * y ∈
      subgroupNonidentity ctx.P := by
    refine ⟨hW₂P hxConjW₂, ?_⟩
    intro hOne
    apply hxne
    apply Subtype.ext
    calc
      (x : G) = y * (y⁻¹ * (x : G) * y) * y⁻¹ := by group
      _ = 1 := by rw [hOne]; simp
  exact ((isNormalizedTI_iff_mem_conj.mp hP_TI).2.2 hxP
    (show y ∈ (⊤ : Subgroup G) from trivial)).mp hxConjP

/-! Maschke supplies a complement `Q` to `W₂` inside `P`.  Wielandt makes
`K = U ∩ N(W₂)` centralize `Q`; Frobenius normal-subgroup structure makes it
centralize `W₂`, and regularity then kills `K`. -/
private theorem ftTypePNormCent_exists_invariant_complement
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hPelem : IsElementaryAbelianGroup ctx.p ctx.P)
    (hPcard : Nat.card ctx.P = ctx.p ^ ctx.q)
    {A : Subgroup G}
    (hAleUW₁ : A ≤ U ⊔ W₁)
    (hAnormP : A ≤ Subgroup.normalizer (ctx.P : Set G))
    (hAnormW₂ : A ≤ Subgroup.normalizer (W₂ : Set G)) :
    ∃ Q : Subgroup G,
      Q ≤ ctx.P ∧
      Disjoint W₂ Q ∧
      W₂ ⊔ Q = ctx.P ∧
      A ≤ Subgroup.normalizer (Q : Set G) := by
  have hprimes : ctx.q.Prime ∧ ctx.p.Prime :=
    FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP
  letI : Fact ctx.p.Prime := ⟨hprimes.2⟩
  letI : IsMulCommutative ctx.P := hPelem.commutative
  have hW₂P : W₂ ≤ ctx.P := ctx.StypeP.2.2.2.1.2.2.1
  let W₂P : Subgroup ctx.P := W₂.subgroupOf ctx.P
  let f : A →* MulAut ctx.P :=
    pTypeSubgroupConjugationHom ctx.P A hAnormP
  have hW₂Pinv : ∀ a : A,
      W₂P.map (f a).toMonoidHom = W₂P := by
    intro a
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      change (a : G) * (x : G) * (a : G)⁻¹ ∈ W₂
      exact (Subgroup.mem_normalizer_iff.mp
        (hAnormW₂ a.property) (x : G)).mp hx
    · exact (Subgroup.card_map_of_injective (f a).injective).ge
  have hpP : ctx.p ∣ Nat.card ctx.P := by
    rw [hPcard]
    exact dvd_pow_self ctx.p hprimes.1.ne_zero
  have hPcopA : Nat.Coprime (Nat.card ctx.P) (Nat.card A) :=
    (Ptype_Fcore_coprime ctx.ptypeCtx).coprime_dvd_right
      (Subgroup.card_dvd_of_le hAleUW₁)
  have hpA : ¬ ctx.p ∣ Nat.card A :=
    hprimes.2.coprime_iff_not_dvd.mp (hPcopA.coprime_dvd_left hpP)
  obtain ⟨Q₀, hcompl, hQ₀inv⟩ :=
    exists_invariant_complement_of_coprime_mulAut_action
      hPelem.pow_eq_one f hpA W₂P hW₂Pinv
  let Q : Subgroup G := Q₀.map ctx.P.subtype
  have hQleP : Q ≤ ctx.P := Subgroup.map_subtype_le Q₀
  have hW₂Pmap : W₂P.map ctx.P.subtype = W₂ :=
    Subgroup.map_subgroupOf_eq_of_le hW₂P
  have hdisW₂Q : Disjoint W₂ Q := by
    have hmap := Subgroup.disjoint_map ctx.P.subtype_injective hcompl.disjoint
    rw [hW₂Pmap] at hmap
    exact hmap
  have hsupW₂Q : W₂ ⊔ Q = ctx.P := by
    have htopMap : (⊤ : Subgroup ctx.P).map ctx.P.subtype = ctx.P :=
      (MonoidHom.range_eq_map ctx.P.subtype).symm.trans ctx.P.range_subtype
    calc
      W₂ ⊔ Q = (W₂P ⊔ Q₀).map ctx.P.subtype := by
        rw [Subgroup.map_sup, hW₂Pmap]
      _ = (⊤ : Subgroup ctx.P).map ctx.P.subtype :=
        congrArg (Subgroup.map ctx.P.subtype) hcompl.codisjoint.eq_top
      _ = ctx.P := htopMap
  refine ⟨Q, hQleP, hdisW₂Q, hsupW₂Q, ?_⟩
  rw [Subgroup.le_normalizer_iff]
  intro a ha x hx
  obtain ⟨p, hp, rfl⟩ := hx
  let p' : ctx.P :=
    ⟨(a : G) * (p : G) * (a : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hAnormP ha) (p : G)).mp
        p.property⟩
  refine ⟨p', ?_, rfl⟩
  change f ⟨a, ha⟩ p ∈ Q₀
  have hmap : f ⟨a, ha⟩ p ∈
      Q₀.map (f ⟨a, ha⟩).toMonoidHom := ⟨p, hp, rfl⟩
  rw [hQ₀inv ⟨a, ha⟩] at hmap
  exact hmap

private theorem ftTypePNormCent_kernel_centralizes_factor
    {A K : Subgroup G}
    (hFrobA : IsFrobeniusDecomposition
      (K.subgroupOf A) (W₁.subgroupOf A))
    (hKleA : K ≤ A)
    (hW₁leA : W₁ ≤ A)
    (hAnormW₂ : A ≤ Subgroup.normalizer (W₂ : Set G))
    (hW₁centW₂ : W₁ ≤ Subgroup.centralizer (W₂ : Set G)) :
    K ≤ Subgroup.centralizer (W₂ : Set G) := by
  let CW : Subgroup G := centralizerWithin A W₂
  have hAnormCW : A ≤ Subgroup.normalizer (CW : Set G) :=
    ftTypePNormCent_centralizerWithin_normalized
      Subgroup.le_normalizer hAnormW₂
  have hCWA : CW ≤ A := centralizerWithin_le_left A W₂
  have hCWnormal : (CW.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCWA).mpr hAnormCW
  letI : (CW.subgroupOf A).Normal := hCWnormal
  have hW₁CW : W₁ ≤ CW := by
    intro w hw
    exact ⟨hW₁leA hw, hW₁centW₂ hw⟩
  have hKCW : K ≤ CW := by
    by_contra hnot
    have hnotSub : ¬ K.subgroupOf A ≤ CW.subgroupOf A := by
      intro hsub
      apply hnot
      intro k hk
      let kA : A := ⟨k, hKleA hk⟩
      have hk' : kA ∈ CW.subgroupOf A :=
        hsub (show kA ∈ K.subgroupOf A from hk)
      exact hk'
    have hproper : CW.subgroupOf A < K.subgroupOf A :=
      hFrobA.normal_proper_kernel hnotSub
    have hW₁subC : W₁.subgroupOf A ≤ CW.subgroupOf A := by
      intro w hw
      exact hW₁CW hw
    have hW₁subK : W₁.subgroupOf A ≤ K.subgroupOf A :=
      hW₁subC.trans hproper.le
    apply hFrobA.complement_ne_bot
    apply le_antisymm _ bot_le
    intro w hw
    exact hFrobA.isComplement.disjoint.le_bot ⟨hW₁subK hw, hw⟩
  intro k hk
  exact (hKCW hk).2

private theorem ftTypePNormCent_kernel_centralizes_complement
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {K Q : Subgroup G}
    (hFrobA : IsFrobeniusDecomposition
      (K.subgroupOf (K ⊔ W₁)) (W₁.subgroupOf (K ⊔ W₁)))
    (hAnormQ : K ⊔ W₁ ≤ Subgroup.normalizer (Q : Set G))
    (hQleP : Q ≤ ctx.P)
    (hQcopA : Nat.Coprime (Nat.card Q) (Nat.card ↥(K ⊔ W₁)))
    (hcentQW₁ : centralizerWithin Q W₁ = ⊥) :
    K ≤ Subgroup.centralizer (Q : Set G) := by
  letI : IsSolvable ctx.P := by infer_instance
  have hQsol : IsSolvable Q :=
    isSolvable_of_injective (Subgroup.inclusion hQleP)
      (Subgroup.inclusion_injective hQleP)
  exact (Frobenius_Wielandt_fixpoint hFrobA hAnormQ hQcopA hQsol).2.1
    hcentQW₁

private theorem ftTypePNormCent_inter_eq_bot
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hFrobUW₁ : PTypeFrobeniusProduct U W₁)
    (hPelem : IsElementaryAbelianGroup ctx.p ctx.P)
    (hPcard : Nat.card ctx.P = ctx.p ^ ctx.q) :
    U ⊓ Subgroup.normalizer (W₂ : Set G) = ⊥ := by
  letI : IsMulCommutative ctx.P := hPelem.commutative
  have hW₂P : W₂ ≤ ctx.P := ctx.StypeP.2.2.2.1.2.2.1
  have hW₁ne : W₁ ≠ ⊥ := ctx.StypeP.1.2.2.1
  have hW₁centW₂ : W₁ ≤ Subgroup.centralizer (W₂ : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (defW.commute ⟨w, hw⟩ ⟨z, hz⟩).symm.eq
  have hPcentW₂ : ctx.P ≤ Subgroup.centralizer (W₂ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      (mul_comm (⟨y, hW₂P hy⟩ : ctx.P) (⟨x, hx⟩ : ctx.P))
  have hW₁normW₂ : W₁ ≤ Subgroup.normalizer (W₂ : Set G) :=
    hW₁centW₂.trans (Subgroup.centralizer_le_normalizer (W₂ : Set G))

  let K : Subgroup G := U ⊓ Subgroup.normalizer (W₂ : Set G)
  change K = ⊥
  by_cases hKbot : K = ⊥
  · exact hKbot
  have hKleU : K ≤ U := by
    dsimp only [K]
    exact inf_le_left
  have hKnormW₂ : K ≤ Subgroup.normalizer (W₂ : Set G) := by
    dsimp only [K]
    exact inf_le_right
  let A : Subgroup G := W₁ ⊔ K
  have hAnormW₂ : A ≤ Subgroup.normalizer (W₂ : Set G) := by
    dsimp only [A]
    exact sup_le hW₁normW₂ hKnormW₂
  have hAleUW₁ : A ≤ U ⊔ W₁ := by
    dsimp only [A]
    exact sup_le le_sup_right (hKleU.trans le_sup_left)
  have hFcoreSd := Ptype_Fcore_sdprod ctx.ptypeCtx
  have hAleS : A ≤ S := hAleUW₁.trans hFcoreSd.2.1
  have hSnormP : S ≤ Subgroup.normalizer (ctx.P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub S)).mp
      (Fcore_normal S)
  have hAnormP : A ≤ Subgroup.normalizer (ctx.P : Set G) :=
    hAleS.trans hSnormP

  obtain ⟨Q, hQleP, hdisW₂Q, hsupW₂Q, hAnormQ⟩ :=
    ftTypePNormCent_exists_invariant_complement
      (A := A) ctx hPelem hPcard hAleUW₁ hAnormP hAnormW₂

  have hW₁normK : W₁ ≤ Subgroup.normalizer (K : Set G) := by
    dsimp only [K]
    exact (le_inf ctx.StypeP.2.1.2.2.1
      (hW₁normW₂.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hregK : IsSemiregularConjugation K W₁ :=
    (ftTypePNormCent_frobenius_semiregular hFrobUW₁).mono_left hKleU
  have hFrobA : IsFrobeniusDecomposition
      (K.subgroupOf A) (W₁.subgroupOf A) := by
    simpa only [A] using
      hregK.isFrobeniusDecomposition_sup hW₁normK hKbot hW₁ne
  have hcentQW₁ : centralizerWithin Q W₁ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hxPW₁ : x ∈ centralizerWithin ctx.P W₁ :=
      ⟨hQleP hx.1, hx.2⟩
    have hxW₂ : x ∈ W₂ := by
      rw [← typeP_cent_core_compl S U W W₁ W₂ defW ctx.StypeP]
      exact hxPW₁
    exact hdisW₂Q.le_bot ⟨hxW₂, hx.1⟩
  have hPcopA : Nat.Coprime (Nat.card ctx.P) (Nat.card A) :=
    (Ptype_Fcore_coprime ctx.ptypeCtx).coprime_dvd_right
      (Subgroup.card_dvd_of_le hAleUW₁)
  have hFrobKW₁ : IsFrobeniusDecomposition
      (K.subgroupOf (K ⊔ W₁)) (W₁.subgroupOf (K ⊔ W₁)) := by
    have hsupEq : W₁ ⊔ K = K ⊔ W₁ := sup_comm W₁ K
    rw [← hsupEq]
    exact hFrobA
  have hKW₁normQ : K ⊔ W₁ ≤ Subgroup.normalizer (Q : Set G) := by
    simpa only [A, sup_comm] using hAnormQ
  have hQcopKW₁ : Nat.Coprime (Nat.card Q) (Nat.card ↥(K ⊔ W₁)) := by
    have hQcopA : Nat.Coprime (Nat.card Q) (Nat.card A) :=
      hPcopA.coprime_dvd_left (Subgroup.card_dvd_of_le hQleP)
    simpa only [A, sup_comm] using hQcopA
  have hKcentQ : K ≤ Subgroup.centralizer (Q : Set G) :=
    ftTypePNormCent_kernel_centralizes_complement
      ctx hFrobKW₁ hKW₁normQ hQleP hQcopKW₁ hcentQW₁

  have hKleA : K ≤ A := by
    dsimp only [A]
    exact le_sup_right
  have hW₁leA : W₁ ≤ A := by
    dsimp only [A]
    exact le_sup_left
  have hKcentW₂ : K ≤ Subgroup.centralizer (W₂ : Set G) :=
    ftTypePNormCent_kernel_centralizes_factor
      hFrobA hKleA hW₁leA hAnormW₂ hW₁centW₂
  have hKcentP : K ≤ Subgroup.centralizer (ctx.P : Set G) := by
    rw [← hsupW₂Q]
    exact ftTypePNormCent_le_centralizer_sup hKcentW₂ hKcentQ
  have hKleC : K ≤ ctx.C := by
    intro k hk
    exact ⟨hKleU hk, hKcentP hk⟩
  apply le_antisymm _ bot_le
  rw [← FTtypeP_reg_Fcore ctx]
  exact hKleC

/-! Once `U ∩ N(W₂)` is trivial, the two nested semidirect decompositions
of `S` show that every normalizer element lies in `P ∨ W₁`. -/
private theorem ftTypePNormCent_normalizer_le_sup
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hPcentW₂ : ctx.P ≤ Subgroup.centralizer (W₂ : Set G))
    (hKbot : U ⊓ Subgroup.normalizer (W₂ : Set G) = ⊥) :
    Subgroup.normalizer (W₂ : Set G) ≤ ctx.P ⊔ W₁ := by
  have hW₁centW₂ : W₁ ≤ Subgroup.centralizer (W₂ : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (defW.commute ⟨w, hw⟩ ⟨z, hz⟩).symm.eq
  have hW₁normW₂ : W₁ ≤ Subgroup.normalizer (W₂ : Set G) :=
    hW₁centW₂.trans (Subgroup.centralizer_le_normalizer (W₂ : Set G))
  have hPnormW₂ : ctx.P ≤ Subgroup.normalizer (W₂ : Set G) :=
    hPcentW₂.trans (Subgroup.centralizer_le_normalizer (W₂ : Set G))
  intro y hy
  have hyS : y ∈ S := ftTypePNormCent_normalizer_le_S ctx hy
  have hOuter := ctx.StypeP.1.2.2.2
  let yS : S := ⟨y, hyS⟩
  obtain ⟨⟨d, w⟩, hdw⟩ := hOuter.2.2.2.2 yS
  have hdwG : (d : G) * (w : G) = y :=
    congrArg (fun z : S ↦ (z : G)) hdw
  have hwNorm : (w : G) ∈ Subgroup.normalizer (W₂ : Set G) :=
    hW₁normW₂ w.property
  have hdNorm : (d : G) ∈ Subgroup.normalizer (W₂ : Set G) := by
    have hmem := (Subgroup.normalizer (W₂ : Set G)).mul_mem hy
      ((Subgroup.normalizer (W₂ : Set G)).inv_mem hwNorm)
    have heq : y * (w : G)⁻¹ = (d : G) := by
      rw [← hdwG]
      group
    rwa [heq] at hmem
  have hInner := ctx.StypeP.2.1.2.2.2
  let dPU : ctx.PU := ⟨(d : G), d.property⟩
  obtain ⟨⟨p, u⟩, hpu⟩ := hInner.2.2.2.2 dPU
  have hpuG : (p : G) * (u : G) = (d : G) :=
    congrArg (fun z : ctx.PU ↦ (z : G)) hpu
  have hpNorm : (p : G) ∈ Subgroup.normalizer (W₂ : Set G) :=
    hPnormW₂ p.property
  have huNorm : (u : G) ∈ Subgroup.normalizer (W₂ : Set G) := by
    have hmem := (Subgroup.normalizer (W₂ : Set G)).mul_mem
      ((Subgroup.normalizer (W₂ : Set G)).inv_mem hpNorm) hdNorm
    have heq : (p : G)⁻¹ * (d : G) = (u : G) := by
      rw [← hpuG]
      group
    rwa [heq] at hmem
  have huK : (u : G) ∈ U ⊓ Subgroup.normalizer (W₂ : Set G) :=
    ⟨u.property, huNorm⟩
  have huOne : (u : G) = 1 := by
    rw [hKbot] at huK
    exact Subgroup.mem_bot.mp huK
  have hyEq : y = (p : G) * (w : G) := by
    calc
      y = (d : G) * (w : G) := hdwG.symm
      _ = ((p : G) * (u : G)) * (w : G) := by rw [hpuG]
      _ = (p : G) * (w : G) := by rw [huOne]; simp
  rw [hyEq]
  exact Subgroup.mul_mem_sup p.property w.property

/-- `PFsection13.v: FTtypeP_norm_cent_compl`, Peterfalvi (13.16). -/
theorem FTtypeP_norm_cent_compl
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    IsInternalSemidirectProductIn ctx.P W₁
        (Subgroup.normalizer (W₂ : Set G)) ∧
      IsInternalSemidirectProductIn ctx.P W₁
        (Subgroup.centralizer (W₂ : Set G)) := by
  rcases FTtypeP_facts ctx with
    ⟨_, _, hFrobUW₁, _, hPelem, hPcard, _, _, _, _⟩
  letI : IsMulCommutative ctx.P := hPelem.commutative
  have hW₂P : W₂ ≤ ctx.P := ctx.StypeP.2.2.2.1.2.2.1
  have hW₁centW₂ : W₁ ≤ Subgroup.centralizer (W₂ : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (defW.commute ⟨w, hw⟩ ⟨z, hz⟩).symm.eq
  have hPcentW₂ : ctx.P ≤ Subgroup.centralizer (W₂ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      (mul_comm (⟨y, hW₂P hy⟩ : ctx.P) (⟨x, hx⟩ : ctx.P))
  have hKbot : U ⊓ Subgroup.normalizer (W₂ : Set G) = ⊥ :=
    ftTypePNormCent_inter_eq_bot ctx hFrobUW₁ hPelem hPcard
  have hnormLe : Subgroup.normalizer (W₂ : Set G) ≤ ctx.P ⊔ W₁ :=
    ftTypePNormCent_normalizer_le_sup ctx hPcentW₂ hKbot
  have hPW₁centW₂ : ctx.P ⊔ W₁ ≤
      Subgroup.centralizer (W₂ : Set G) :=
    sup_le hPcentW₂ hW₁centW₂
  have hPW₁normW₂ : ctx.P ⊔ W₁ ≤
      Subgroup.normalizer (W₂ : Set G) :=
    hPW₁centW₂.trans (Subgroup.centralizer_le_normalizer (W₂ : Set G))
  have hnormEq : Subgroup.normalizer (W₂ : Set G) = ctx.P ⊔ W₁ :=
    le_antisymm hnormLe hPW₁normW₂
  have hcentEq : Subgroup.centralizer (W₂ : Set G) = ctx.P ⊔ W₁ :=
    le_antisymm
      ((Subgroup.centralizer_le_normalizer (W₂ : Set G)).trans hnormLe)
      hPW₁centW₂
  have hPW₁sd : IsInternalSemidirectProductIn
      ctx.P W₁ (ctx.P ⊔ W₁) :=
    ftTypePNormCent_semidirect_restrict_right
      (Ptype_Fcore_sdprod ctx.ptypeCtx) le_sup_right
  constructor
  · rw [hnormEq]
    exact hPW₁sd
  · rw [hcentEq]
    exact hPW₁sd

end

end Submission.OddOrder.PF
