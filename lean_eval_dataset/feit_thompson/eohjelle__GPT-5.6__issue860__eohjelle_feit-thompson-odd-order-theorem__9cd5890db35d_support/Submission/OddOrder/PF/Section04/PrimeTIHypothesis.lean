import Mathlib.Data.Nat.ModEq
import Submission.OddOrder.MathlibSupport.Hall
import Submission.OddOrder.MathlibSupport.SubgroupCardinality
import Submission.OddOrder.PF.Section02.DadeHypothesis
import Submission.OddOrder.PF.Section03.CyclicTIGroupFacts

/-!
# Peterfalvi Section 4: the prime-TI hypothesis

This file ports the group-theoretic infrastructure around Peterfalvi's
Hypothesis 4.2.  The ambient subgroup `L` is an internal semidirect product
of `K` by `W₁`, while `W = W₁ × W₂` and the centralizer in `K` of
every nonidentity element of `W₁` is exactly `W₂`.

The main conclusions are the normalized-TI statement for `W \ W₂` and
the resulting `CyclicTIHypothesis` needed by the Section 3 character theory.
The quotient construction following this block in the Coq source is kept for
a later file.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport

universe u

variable {Gamma : Type u} [Group Gamma]

/-- Peterfalvi Hypothesis 4.2, with all five ambient subgroups explicit.

The Hall condition is stated for the copy of `W₁` inside `L`; its prime set
is the prime support of the (equivalent) ambient subgroup `W₁`. -/
structure PrimeTIHypothesis
    (L K W W₁ W₂ : Subgroup Gamma)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop where
  semidirect : IsInternalSemidirectProductIn K W₁ L
  complement_ne_bot : W₁ ≠ ⊥
  complement_hall :
    IsHall (primeSupport (Nat.card W₁)) (W₁.subgroupOf L)
  complement_cyclic : IsCyclic W₁
  fixed_ne_bot : W₂ ≠ ⊥
  fixed_le_kernel : W₂ ≤ K
  fixed_cyclic : IsCyclic W₂
  centralizer_kernel :
    ∀ x : W₁, x ≠ 1 →
      centralizerWithin K (Subgroup.zpowers (x : Gamma)) = W₂
  odd_card : Odd (Nat.card W)

/-- The larger prime-TI set used in Peterfalvi 4.3(a). -/
def primeTISet (W W₂ : Subgroup Gamma) : Set Gamma :=
  (W : Set Gamma) \ (W₂ : Set Gamma)

@[simp]
theorem mem_primeTISet {W W₂ : Subgroup Gamma} {x : Gamma} :
    x ∈ primeTISet W W₂ ↔ x ∈ W ∧ x ∉ W₂ := by
  simp [primeTISet]

private theorem conjugate_eq_self_of_mem_cyclic
    {W : Subgroup Gamma} (hcyclic : IsCyclic W)
    {a g : Gamma} (ha : a ∈ W) (hg : g ∈ W) :
    g⁻¹ * a * g = a := by
  letI : IsCyclic W := hcyclic
  let aW : W := ⟨a, ha⟩
  let gW : W := ⟨g, hg⟩
  have hcomm : (g : Gamma) * a = a * g := by
    exact congrArg Subtype.val (mul_comm' gW aW)
  calc
    g⁻¹ * a * g = g⁻¹ * (a * g) := by rw [mul_assoc]
    _ = g⁻¹ * (g * a) := by rw [hcomm.symm]
    _ = a := by simp

namespace PrimeTIHypothesis

variable {L K W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

/-- The kernel lies in `L`. -/
theorem kernel_le_group
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) : K ≤ L :=
  h.semidirect.1

/-- The semidirect-product complement lies in `L`. -/
theorem complement_le_group
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) : W₁ ≤ L :=
  h.semidirect.2.1

/-- The kernel is normal in `L`, expressed on subgroup types. -/
theorem kernel_normal
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    (K.subgroupOf L).Normal :=
  h.semidirect.2.2.1

/-- The two factors are complementary inside `L`. -/
theorem semidirect_complement
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    (K.subgroupOf L).IsComplement' (W₁.subgroupOf L) :=
  h.semidirect.2.2.2

/-- Normality of the kernel inside `L`, in ambient normalizer form. -/
theorem group_le_normalizer_kernel
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    L ≤ Subgroup.normalizer (K : Set Gamma) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.kernel_le_group).mp
    h.kernel_normal

/-- The direct product `W` lies in `L`. -/
theorem directProduct_le_group
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) : W ≤ L := by
  intro w hw
  let wW : W := ⟨w, hw⟩
  let p : W₁ × W₂ := defW.mulEquiv.symm wW
  have hpL : (p.1 : Gamma) * (p.2 : Gamma) ∈ L :=
    L.mul_mem (h.complement_le_group p.1.property)
      (h.kernel_le_group (h.fixed_le_kernel p.2.property))
  have hpw : (p.1 : Gamma) * (p.2 : Gamma) = w := by
    have heq := defW.coe_mulEquiv_apply p
    rw [defW.mulEquiv.apply_symm_apply] at heq
    exact heq.symm
  rwa [hpw] at hpL

/-- The Hall clause and the semidirect decomposition make the kernel and
complement orders coprime. -/
theorem kernel_complement_card_coprime
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    Nat.Coprime (Nat.card K) (Nat.card W₁) := by
  have hcop := h.complement_hall.coprime_card_index
  rw [h.semidirect_complement.index_eq_card,
    natCard_subgroupOf_eq h.complement_le_group,
    natCard_subgroupOf_eq h.kernel_le_group] at hcop
  exact hcop.symm

/-- The two direct factors of `W` have coprime orders. -/
theorem factor_card_coprime
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    Nat.Coprime (Nat.card W₁) (Nat.card W₂) := by
  have hdiv : Nat.card W₂ ∣ Nat.card K :=
    Subgroup.card_dvd_of_le h.fixed_le_kernel
  exact (h.kernel_complement_card_coprime.of_dvd_left hdiv).symm

/-- The internal direct product `W` is cyclic. -/
theorem cyclic
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) : IsCyclic W := by
  apply defW.mulEquiv.isCyclic.mp
  exact Group.isCyclic_prod_iff.mpr
    ⟨h.complement_cyclic, h.fixed_cyclic, h.factor_card_coprime⟩

/-- In particular, the direct product `W` is commutative. -/
theorem directProduct_isMulCommutative
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    IsMulCommutative W := by
  letI : IsCyclic W := h.cyclic
  infer_instance

/-- The order of `W₁` is odd. -/
theorem complement_odd_card
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    Odd (Nat.card W₁) :=
  Odd.of_dvd_nat h.odd_card (Subgroup.card_dvd_of_le defW.left_le)

/-- The order of `W₂` is odd. -/
theorem fixed_odd_card
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    Odd (Nat.card W₂) :=
  Odd.of_dvd_nat h.odd_card (Subgroup.card_dvd_of_le defW.right_le)

/-- The larger set `W \ W₂` is nonempty. -/
theorem primeTISet_nonempty
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    (primeTISet W W₂).Nonempty := by
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    h.complement_ne_bot
  refine ⟨(x : Gamma), ?_⟩
  rw [mem_primeTISet]
  refine ⟨defW.left_le x.property, ?_⟩
  intro hxW₂
  have hx' :
      (((defW.mulEquiv (x, 1) : W) : Gamma)) ∈ W₂ := by
    simpa using hxW₂
  exact hx ((defW.mulEquiv_mem_right_iff (x, 1)).mp hx')

/-- The cyclic-TI set of Section 3 is nonempty. -/
theorem cyclicTISet_nonempty
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    (cyclicTISet W W₁ W₂).Nonempty := by
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    h.complement_ne_bot
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.fixed_ne_bot
  let w : W := defW.mulEquiv (x, y)
  refine ⟨(w : Gamma), ?_⟩
  rw [mem_cyclicTISet]
  refine ⟨w.property, ?_, ?_⟩
  · intro hwW₁
    exact hy ((defW.mulEquiv_mem_left_iff (x, y)).mp hwW₁)
  · intro hwW₂
    exact hx ((defW.mulEquiv_mem_right_iff (x, y)).mp hwW₂)

/-- The cyclic-TI set is contained in the larger prime-TI set. -/
theorem cyclicTISet_subset_primeTISet
    (_h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    cyclicTISet W W₁ W₂ ⊆ primeTISet W W₂ := by
  intro x hx
  exact ⟨(mem_cyclicTISet.mp hx).1, (mem_cyclicTISet.mp hx).2.2⟩

/-- Coprime-power extraction recovers the `W₁` coordinate of an element
of `W`.  This is the Lean replacement for the source proof's `pi(W₁)`
constituent calculation. -/
private theorem leftFactor_conjugate_mem
    (h : PrimeTIHypothesis L K W W₁ W₂ defW)
    {a k : Gamma} (haW : a ∈ W)
    (hakW : k⁻¹ * a * k ∈ W) :
    let aW : W := ⟨a, haW⟩
    (k⁻¹ * (defW.mulEquiv.symm aW).1 * k : Gamma) ∈ W₁ := by
  let aW : W := ⟨a, haW⟩
  let bW : W := ⟨k⁻¹ * a * k, hakW⟩
  let p : W₁ × W₂ := defW.mulEquiv.symm aW
  let q : W₁ × W₂ := defW.mulEquiv.symm bW
  let e0 := Nat.chineseRemainder h.factor_card_coprime 1 0
  let e : Nat := e0
  have heW₁ : e ≡ 1 [MOD Nat.card W₁] := e0.property.1
  have heW₂ : e ≡ 0 [MOD Nat.card W₂] := e0.property.2
  have hp₁pow : ((p.1 : W₁) : Gamma) ^ e = (p.1 : Gamma) := by
    have hmod : e ≡ 1 [MOD orderOf (p.1 : Gamma)] :=
      heW₁.of_dvd (W₁.orderOf_dvd_natCard p.1.property)
    simpa using
      (pow_eq_pow_iff_modEq.mpr hmod :
        ((p.1 : W₁) : Gamma) ^ e = (p.1 : Gamma) ^ 1)
  have hp₂pow : ((p.2 : W₂) : Gamma) ^ e = 1 := by
    apply pow_eq_one_iff_modEq.mpr
    exact heW₂.of_dvd (W₂.orderOf_dvd_natCard p.2.property)
  have hq₁pow : ((q.1 : W₁) : Gamma) ^ e = (q.1 : Gamma) := by
    have hmod : e ≡ 1 [MOD orderOf (q.1 : Gamma)] :=
      heW₁.of_dvd (W₁.orderOf_dvd_natCard q.1.property)
    simpa using
      (pow_eq_pow_iff_modEq.mpr hmod :
        ((q.1 : W₁) : Gamma) ^ e = (q.1 : Gamma) ^ 1)
  have hq₂pow : ((q.2 : W₂) : Gamma) ^ e = 1 := by
    apply pow_eq_one_iff_modEq.mpr
    exact heW₂.of_dvd (W₂.orderOf_dvd_natCard q.2.property)
  have haDecomp : a = (p.1 : Gamma) * (p.2 : Gamma) := by
    have heq := defW.coe_mulEquiv_apply p
    rw [defW.mulEquiv.apply_symm_apply] at heq
    exact heq
  have hbDecomp : k⁻¹ * a * k = (q.1 : Gamma) * (q.2 : Gamma) := by
    have heq := defW.coe_mulEquiv_apply q
    rw [defW.mulEquiv.apply_symm_apply] at heq
    exact heq
  have hapow : a ^ e = (p.1 : Gamma) := by
    rw [haDecomp, (defW.commute p.1 p.2).mul_pow, hp₁pow,
      hp₂pow, mul_one]
  have hbpow : (k⁻¹ * a * k) ^ e = (q.1 : Gamma) := by
    rw [hbDecomp, (defW.commute q.1 q.2).mul_pow, hq₁pow,
      hq₂pow, mul_one]
  have hconjLeft :
      k⁻¹ * (p.1 : Gamma) * k = (q.1 : Gamma) := by
    calc
      k⁻¹ * (p.1 : Gamma) * k = k⁻¹ * (a ^ e) * k := by rw [hapow]
      _ = (k⁻¹ * a * k) ^ e := by
        simpa [MulAut.conj_apply] using
          (map_pow (MulAut.conj k⁻¹) a e)
      _ = (q.1 : Gamma) := hbpow
  change k⁻¹ * (p.1 : Gamma) * k ∈ W₁
  rw [hconjLeft]
  exact q.1.property

/-- First part of Peterfalvi 4.3(a): `W \ W₂` is normalized TI in `L`,
with relative normalizer `W`. -/
theorem normedTI_primeTISet
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    IsNormalizedTI (primeTISet W W₂) L W := by
  apply isNormalizedTI_iff_mem_conj.mpr
  refine ⟨h.primeTISet_nonempty, h.directProduct_le_group, ?_⟩
  intro a ha g hg
  constructor
  · intro hag
    have ha' := mem_primeTISet.mp ha
    have hag' := mem_primeTISet.mp hag
    let gL : L := ⟨g, hg⟩
    rcases h.semidirect_complement.2 gL with ⟨⟨kL, xL⟩, hkxL⟩
    let k : K := ⟨((kL : L) : Gamma), kL.property⟩
    let x : W₁ := ⟨((xL : L) : Gamma), xL.property⟩
    have hkx : (k : Gamma) * (x : Gamma) = g := by
      simpa [k, x, gL] using congrArg Subtype.val hkxL
    let b : Gamma := k⁻¹ * a * k
    have hxW : (x : Gamma) ∈ W := defW.left_le x.property
    have hbBack : b = (x : Gamma) * (g⁻¹ * a * g) * (x : Gamma)⁻¹ := by
      dsimp [b]
      rw [← hkx]
      group
    have hbW : b ∈ W := by
      rw [hbBack]
      exact W.mul_mem (W.mul_mem hxW hag'.1) (W.inv_mem hxW)
    let aW : W := ⟨a, ha'.1⟩
    let r : W₁ := (defW.mulEquiv.symm aW).1
    have hrNe : r ≠ 1 := by
      intro hr
      have haW₂ : a ∈ W₂ := by
        have hp :=
          (defW.mulEquiv_mem_right_iff (defW.mulEquiv.symm aW)).mpr hr
        simpa [aW] using hp
      exact ha'.2 haW₂
    have hrConjW₁ : k⁻¹ * (r : Gamma) * k ∈ W₁ := by
      exact h.leftFactor_conjugate_mem ha'.1 hbW
    let d : Gamma := (r : Gamma)⁻¹ * (k⁻¹ * (r : Gamma) * k)
    have hrNormalizer : (r : Gamma) ∈ Subgroup.normalizer (K : Set Gamma) :=
      h.group_le_normalizer_kernel (h.complement_le_group r.property)
    have hkConjK : (r : Gamma)⁻¹ * (k : Gamma)⁻¹ * (r : Gamma) ∈ K :=
      (Subgroup.mem_normalizer_iff''.mp hrNormalizer (k : Gamma)⁻¹).mp
        (K.inv_mem k.property)
    have hdK : d ∈ K := by
      simpa only [d, mul_assoc, Subgroup.coe_inv] using
        K.mul_mem hkConjK k.property
    have hdW₁ : d ∈ W₁ := by
      exact W₁.mul_mem (W₁.inv_mem r.property) hrConjW₁
    have hdisjoint : Disjoint K W₁ :=
      Subgroup.disjoint_of_coprime_natCard
        h.kernel_complement_card_coprime
    have hdOne : d = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hdisjoint]
      exact ⟨hdK, hdW₁⟩
    have hrConj : k⁻¹ * (r : Gamma) * k = r := by
      have hm := congrArg (fun z : Gamma => (r : Gamma) * z) hdOne
      simpa [d, mul_assoc] using hm
    have hrCommute : Commute (r : Gamma) (k : Gamma) := by
      rw [commute_iff_eq]
      have hm := congrArg (fun z : Gamma => (k : Gamma) * z) hrConj
      simpa [mul_assoc] using hm
    have hkCentralizer :
        (k : Gamma) ∈ centralizerWithin K (Subgroup.zpowers (r : Gamma)) := by
      refine ⟨k.property, ?_⟩
      intro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (hrCommute.zpow_left n).eq
    have hkW₂ : (k : Gamma) ∈ W₂ := by
      rw [← h.centralizer_kernel r hrNe]
      exact hkCentralizer
    rw [← hkx]
    exact W.mul_mem (defW.right_le hkW₂) hxW
  · intro hgW
    rw [conjugate_eq_self_of_mem_cyclic h.cyclic
      (mem_primeTISet.mp ha).1 hgW]
    exact ha

/-- Source-compatible name for the first part of Peterfalvi 4.3(a). -/
theorem normedTI_prTIset
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    IsNormalizedTI (primeTISet W W₂) L W :=
  h.normedTI_primeTISet

/-- Second part of Peterfalvi 4.3(a): the prime-TI hypothesis supplies the
cyclic-TI hypothesis used throughout Section 3. -/
theorem prime_cycTIhyp
    (h : PrimeTIHypothesis L K W W₁ W₂ defW) :
    CyclicTIHypothesis L W W₁ W₂ defW where
  cyclic := h.cyclic
  odd_card := h.odd_card
  normedTI := by
    apply isNormalizedTI_iff_mem_conj.mpr
    refine ⟨h.cyclicTISet_nonempty, h.directProduct_le_group, ?_⟩
    intro a ha g hg
    constructor
    · intro hag
      have haLarge : a ∈ primeTISet W W₂ :=
        h.cyclicTISet_subset_primeTISet ha
      have hagLarge : g⁻¹ * a * g ∈ primeTISet W W₂ :=
        h.cyclicTISet_subset_primeTISet hag
      exact
        ((isNormalizedTI_iff_mem_conj.mp h.normedTI_primeTISet).2.2
          haLarge hg).mp hagLarge
    · intro hgW
      rw [conjugate_eq_self_of_mem_cyclic h.cyclic
        (mem_cyclicTISet.mp ha).1 hgW]
      exact ha

end PrimeTIHypothesis

end

end Submission.OddOrder.PF
