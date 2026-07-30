import Submission.OddOrder.MathlibSupport.Centralizer

/-!
Peterfalvi 2.1: conjugates of a centralizer right coset partition the
corresponding right coset of a coprime-order normalizing element.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped Pointwise

universe u

/-- A family of nonempty, pairwise-disjoint sets whose union is `D`.
This is the propositional content of MathComp's `partition P D`. -/
def IsSetPartition {α : Type*} (P : Set (Set α)) (D : Set α) : Prop :=
  ⋃₀ P = D ∧ P.PairwiseDisjoint id ∧ (∅ : Set α) ∉ P

/-- Conjugation by a subgroup on the ambient group. -/
abbrev subgroupConjugationActionOnAmbient {G : Type*} [Group G]
    (H : Subgroup G) : MulDistribMulAction H G :=
  MulDistribMulAction.compHom G (MulAut.conj.comp H.subtype)

/-- Peterfalvi 2.1.

The explicit action instances select conjugation on both ambient elements and
their subsets; without them Mathlib's inherited subgroup action is left
translation. -/
theorem partition_cent_rcoset
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (g : G)
    (hNg : g ∈ Subgroup.normalizer (H : Set G))
    (hcop : Nat.Coprime (Nat.card H) (orderOf g)) :
    let conjugationAction := subgroupConjugationActionOnAmbient H
    letI : SMul H G := conjugationAction.toSMul
    letI : MulAction H G := conjugationAction.toMulAction
    letI : MulAction H (Set G) := Set.mulActionSet
    let C := centralizerWithin H (Subgroup.zpowers g)
    let Cg : Set G := (C : Set G) * ({g} : Set G)
    IsSetPartition (MulAction.orbit H Cg) ((H : Set G) * ({g} : Set G)) ∧
      (MulAction.orbit H Cg).ncard = C.relIndex H := by
  let conjugationAction := subgroupConjugationActionOnAmbient H
  letI : SMul H G := conjugationAction.toSMul
  letI : MulAction H G := conjugationAction.toMulAction
  letI : MulAction H (Set G) := Set.mulActionSet
  let C := centralizerWithin H (Subgroup.zpowers g)
  let Cg : Set G := (C : Set G) * ({g} : Set G)
  change IsSetPartition (MulAction.orbit H Cg) ((H : Set G) * ({g} : Set G)) ∧
    (MulAction.orbit H Cg).ncard = C.relIndex H

  let e : ℕ := Nat.chineseRemainder hcop 0 1
  have heH : e ≡ 0 [MOD Nat.card H] :=
    (Nat.chineseRemainder hcop 0 1).property.1
  have heg : e ≡ 1 [MOD orderOf g] :=
    (Nat.chineseRemainder hcop 0 1).property.2
  have hgpow : g ^ e = g := by
    simpa using (pow_eq_pow_iff_modEq.mpr heg : g ^ e = g ^ 1)

  have hcpow (c : C) : (c : G) ^ e = 1 := by
    apply pow_eq_one_iff_modEq.mpr
    exact heH.of_dvd (H.orderOf_dvd_natCard c.property.1)
  have hccomm (c : C) : Commute (c : G) g :=
    (c.property.2 g (Subgroup.mem_zpowers g)).symm

  have hbase {u : G} (hu : u ∈ Cg) : u ^ e = g := by
    rcases Set.mem_mul.mp hu with ⟨c, hc, y, hy, rfl⟩
    rw [Set.mem_singleton_iff.mp hy]
    let cC : C := ⟨c, hc⟩
    rw [(hccomm cC).mul_pow, hcpow cC, hgpow, one_mul]

  have hrecover (h : H) {u : G} (hu : u ∈ h • Cg) : u ^ e = h • g := by
    rcases Set.mem_smul_set.mp hu with ⟨v, hv, rfl⟩
    change (MulAut.conj (h : G) v) ^ e = MulAut.conj (h : G) g
    rw [← map_pow, hbase hv]

  have hginCg : g ∈ Cg := by
    simp [Cg]

  have memC_of_fix (h : H) (hh : h • g = g) : (h : G) ∈ C := by
    refine ⟨h.property, ?_⟩
    have hcomm : Commute (h : G) g := by
      change (h : G) * g * (h : G)⁻¹ = g at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    intro a ha
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (hcomm.zpow_right z).symm.eq

  have block_fixed (h : H) (hc : (h : G) ∈ C) : h • Cg = Cg := by
    have hfixg : h • g = g := by
      change (h : G) * g * (h : G)⁻¹ = g
      exact mul_inv_eq_iff_eq_mul.mpr
        (hc.2 g (Subgroup.mem_zpowers g)).symm
    have hCsub : MulAut.conj (h : G) • C = C :=
      Subgroup.conj_smul_eq_self_of_mem hc
    have hCset : MulAut.conj (h : G) '' (C : Set G) = (C : Set G) := by
      have := congrArg (fun K : Subgroup G ↦ (K : Set G)) hCsub
      simpa only [Subgroup.coe_pointwise_smul, ← Set.image_smul,
        MulAut.smul_def] using this
    change MulAut.conj (h : G) '' Cg = Cg
    change MulAut.conj (h : G) '' ((C : Set G) * {g}) =
      (C : Set G) * {g}
    rw [Set.image_mul, hCset, Set.image_singleton]
    change (C : Set G) * {h • g} = (C : Set G) * {g}
    rw [hfixg]

  have hstab : MulAction.stabilizer H Cg = C.subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hh
      have hgmem : h • g ∈ Cg := by
        rw [← hh]
        exact Set.smul_mem_smul_set (a := h) hginCg
      have hfix : h • g = g :=
        (hrecover h (Set.smul_mem_smul_set (a := h) hginCg)).symm.trans
          (hbase hgmem)
      exact memC_of_fix h hfix
    · intro hh
      exact block_fixed h hh

  have horbitcard : (MulAction.orbit H Cg).ncard = C.relIndex H := by
    rw [← MulAction.index_stabilizer H Cg, hstab]
    rfl

  have blocks_eq_of_nonempty_inter (h k : H)
      (hu : ((h • Cg) ∩ (k • Cg)).Nonempty) : h • Cg = k • Cg := by
    rcases hu with ⟨u, huh, huk⟩
    have hconjg : h • g = k • g :=
      (hrecover h huh).symm.trans (hrecover k huk)
    have hrfixg : (k⁻¹ * h) • g = g := by
      rw [mul_smul, hconjg, inv_smul_smul]
    have hrblock : (k⁻¹ * h) • Cg = Cg :=
      block_fixed (k⁻¹ * h) (memC_of_fix (k⁻¹ * h) hrfixg)
    calc
      h • Cg = (k * (k⁻¹ * h)) • Cg := by simp
      _ = k • ((k⁻¹ * h) • Cg) := mul_smul _ _ _
      _ = k • Cg := by rw [hrblock]

  have hpair : (MulAction.orbit H Cg).PairwiseDisjoint id := by
    rw [Set.pairwiseDisjoint_iff]
    rintro A ⟨h, rfl⟩ B ⟨k, rfl⟩ hinter
    exact blocks_eq_of_nonempty_inter h k (by simpa using hinter)

  have hnonempty : (∅ : Set G) ∉ MulAction.orbit H Cg := by
    rintro ⟨h, hh⟩
    change h • Cg = (∅ : Set G) at hh
    have hgmem : h • g ∈ h • Cg :=
      Set.smul_mem_smul_set (a := h) hginCg
    rw [hh] at hgmem
    exact hgmem

  have hnormalizes (h : H) : g * (h : G) * g⁻¹ ∈ H :=
    ((Subgroup.mem_set_normalizer_iff.mp hNg) (h : G)).mp h.property

  have hunion_subset : ⋃₀ (MulAction.orbit H Cg) ⊆
      (H : Set G) * ({g} : Set G) := by
    intro u hu
    rcases Set.mem_sUnion.mp hu with ⟨B, hB, huB⟩
    rcases hB with ⟨h, rfl⟩
    rcases Set.mem_smul_set.mp huB with ⟨v, hv, rfl⟩
    rcases Set.mem_mul.mp hv with ⟨c, hc, y, hy, rfl⟩
    rw [Set.mem_singleton_iff.mp hy]
    have hconjinv : g * (h : G)⁻¹ * g⁻¹ ∈ H :=
      hnormalizes ⟨(h : G)⁻¹, H.inv_mem h.property⟩
    have hcoef : (h : G) * c * (g * (h : G)⁻¹ * g⁻¹) ∈ H :=
      H.mul_mem (H.mul_mem h.property hc.1) hconjinv
    refine Set.mem_mul.mpr ⟨(h : G) * c * (g * (h : G)⁻¹ * g⁻¹),
      hcoef, g, Set.mem_singleton g, ?_⟩
    change ((h : G) * c * (g * (h : G)⁻¹ * g⁻¹)) * g =
      (h : G) * (c * g) * (h : G)⁻¹
    group

  have hCgcard : Cg.ncard = Nat.card C := by
    change ((C : Set G) * {g}).ncard = Nat.card C
    rw [Set.mul_singleton,
      Set.ncard_image_of_injective _ (mul_left_injective g)]
    rfl

  have htargetcard : ((H : Set G) * ({g} : Set G)).ncard = Nat.card H := by
    rw [Set.mul_singleton,
      Set.ncard_image_of_injective _ (mul_left_injective g)]
    rfl

  have hCsubcard : Nat.card (C.subgroupOf H) = Nat.card C :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (centralizerWithin_le_left H (Subgroup.zpowers g))).toEquiv

  have hrelmul : C.relIndex H * Nat.card C = Nat.card H := by
    change (C.subgroupOf H).index * Nat.card C = Nat.card H
    rw [← hCsubcard]
    exact (C.subgroupOf H).index_mul_card

  have horbitfinite : (MulAction.orbit H Cg).Finite := Set.toFinite _

  have hblockcard {B : Set G} (hB : B ∈ MulAction.orbit H Cg) :
      B.ncard = Cg.ncard := by
    rcases hB with ⟨h, rfl⟩
    change (h • Cg).ncard = Cg.ncard
    exact Set.ncard_smul_set h Cg

  have hunioncard : (⋃₀ (MulAction.orbit H Cg)).ncard =
      (MulAction.orbit H Cg).ncard * Cg.ncard := by
    have hsUnion_eq : ⋃₀ (MulAction.orbit H Cg) =
        ⋃ B ∈ MulAction.orbit H Cg, B := by
      ext x
      simp
    rw [hsUnion_eq]
    calc
      (⋃ B ∈ MulAction.orbit H Cg, B).ncard =
          ∑ᶠ B ∈ MulAction.orbit H Cg, B.ncard :=
        horbitfinite.ncard_biUnion
          (fun B _ ↦ Set.toFinite B) hpair
      _ = ∑ᶠ _B ∈ MulAction.orbit H Cg, Cg.ncard :=
        finsum_mem_congr rfl (fun B hB ↦ hblockcard hB)
      _ = (∑ᶠ _B ∈ MulAction.orbit H Cg, (1 : ℕ)) * Cg.ncard := by
        rw [finsum_mem_mul' (fun _ : Set G ↦ 1) Cg.ncard horbitfinite]
        simp
      _ = (MulAction.orbit H Cg).ncard * Cg.ncard := by
        rw [finsum_one]

  have hunioncard_target : (⋃₀ (MulAction.orbit H Cg)).ncard =
      ((H : Set G) * ({g} : Set G)).ncard := by
    calc
      (⋃₀ (MulAction.orbit H Cg)).ncard =
          (MulAction.orbit H Cg).ncard * Cg.ncard := hunioncard
      _ = C.relIndex H * Nat.card C := by rw [horbitcard, hCgcard]
      _ = Nat.card H := hrelmul
      _ = ((H : Set G) * ({g} : Set G)).ncard := htargetcard.symm

  have hunion_eq : ⋃₀ (MulAction.orbit H Cg) =
      (H : Set G) * ({g} : Set G) :=
    Set.eq_of_subset_of_ncard_le hunion_subset hunioncard_target.ge

  exact ⟨⟨hunion_eq, hpair, hnonempty⟩, horbitcard⟩

end

end Submission.OddOrder.PF
