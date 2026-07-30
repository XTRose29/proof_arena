import Submission.OddOrder.BG.Section03.SemidirectProperKernel
import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.SolvableComplementConjugacy

/-!
The central-product decomposition for a solvable coprime action.

This is the subgroup form of `BGsection1.coprime_cent_prod`. Complement
conjugacy replaces the prime-order Sylow argument used by the earlier
specialized theorem.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R : Subgroup G}

/-- Internal-complement engine for the general coprime central-product
decomposition. -/
theorem le_commutator_sup_centralizerWithin_of_coprime_complement
    [IsSolvable K]
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : (Nat.card K).Coprime (Nat.card R)) :
    K ≤ ⁅R, K⁆ ⊔ centralizerWithin K R := by
  classical
  letI : K.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [← hKR.sup_eq_top]
    exact sup_le Subgroup.le_normalizer hnormK
  let H : Subgroup G := ⁅R, K⁆
  have hHK : H ≤ K := by
    dsimp [H]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hnormK
  have hnormH : R ≤ Subgroup.normalizer (H : Set G) := by
    dsimp [H]
    exact Subgroup.normalizer_commutator_ge_left R K
  have hnormHK : K ≤ Subgroup.normalizer (H : Set G) := by
    dsimp [H]
    exact Subgroup.normalizer_commutator_ge_right R K
  letI : H.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [← hKR.sup_eq_top]
    exact sup_le hnormHK hnormH
  let L : Subgroup G := R ⊔ H
  let HL : Subgroup L := H.subgroupOf L
  let RL : Subgroup L := R.subgroupOf L
  letI : HL.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : H.Normal) L
  have hHLRL : HL.IsComplement' RL := by
    simpa [L, HL, RL] using
      Submission.OddOrder.BG.Section03.properKernel_subgroupOf_isComplement
        hKR hHK hnormH
  have hcardHL : Nat.card HL = Nat.card H := by
    exact natCard_subgroupOf_eq (show H ≤ L from le_sup_right)
  have hcardRL : Nat.card RL = Nat.card R := by
    exact natCard_subgroupOf_eq (show R ≤ L from le_sup_left)
  let toK : HL →* K :=
    { toFun := fun h ↦ ⟨((h : L) : G), hHK h.property⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  letI : IsSolvable HL :=
    solvable_of_solvable_injective (f := toK) (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : K ↦ (z : G)) hab)
  have hcopHL : (Nat.card HL).Coprime HL.index := by
    rw [hHLRL.symm.index_eq_card, hcardHL, hcardRL]
    exact hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hHK)
  intro k hk
  let Rk : Subgroup G := R.map (MulAut.conj k).toMonoidHom
  have hRkL : Rk ≤ L := by
    rintro z ⟨r, hr, rfl⟩
    change k * r * k⁻¹ ∈ L
    rw [show k * r * k⁻¹ = ⁅k, r⁆ * r by
      simpa using (conj_eq_commutatorElement_mul (g₁ := k) (g₂ := r))]
    apply L.mul_mem
    · apply (show H ≤ L from le_sup_right)
      have hmem : ⁅k, r⁆ ∈ ⁅K, R⁆ :=
        Subgroup.commutator_mem_commutator hk hr
      simpa [H, Subgroup.commutator_comm R K] using hmem
    · exact (show R ≤ L from le_sup_left) hr
  let RkL : Subgroup L := Rk.subgroupOf L
  have hcardRkL : Nat.card RkL = Nat.card R := by
    calc
      Nat.card RkL = Nat.card Rk := natCard_subgroupOf_eq hRkL
      _ = Nat.card R := by
        dsimp [Rk]
        exact Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hHLRkL : HL.IsComplement' RkL := by
    apply Subgroup.isComplement'_of_coprime
    · rw [hcardRkL, ← hcardRL]
      exact hHLRL.card_mul
    · rw [hcardRkL, hcardHL]
      exact hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hHK)
  obtain ⟨h, hh⟩ :=
    Subgroup.solvable_complement_conjugacy hcopHL hHLRL hHLRkL
  let hG : G := ((h : HL) : L)
  have hhH : hG ∈ H := h.property
  have hRkEq : Rk = R.map (MulAut.conj hG).toMonoidHom := by
    calc
      Rk = RkL.map L.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hRkL).symm
      _ = (RL.map (MulAut.conj (h : L)).toMonoidHom).map
          L.subtype := by rw [hh]
      _ = RL.map
          (L.subtype.comp (MulAut.conj (h : L)).toMonoidHom) :=
        Subgroup.map_map RL L.subtype
          (MulAut.conj (h : L)).toMonoidHom
      _ = RL.map
          ((MulAut.conj hG).toMonoidHom.comp L.subtype) := rfl
      _ = (RL.map L.subtype).map
          (MulAut.conj hG).toMonoidHom := by rw [Subgroup.map_map]
      _ = R.map (MulAut.conj hG).toMonoidHom := by
        rw [Subgroup.map_subgroupOf_eq_of_le
          (show R ≤ L from le_sup_left)]
  let c : G := hG⁻¹ * k
  have hcK : c ∈ K :=
    K.mul_mem (K.inv_mem (hHK hhH)) hk
  have hmapC : R.map (MulAut.conj c).toMonoidHom ≤ R := by
    rintro z ⟨r, hr, rfl⟩
    have hkr : (MulAut.conj k).toMonoidHom r ∈ Rk :=
      Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hr
    rw [hRkEq] at hkr
    rcases hkr with ⟨r', hr', heq⟩
    have heq' : hG⁻¹ * (k * r * k⁻¹) * hG = r' := by
      change hG * r' * hG⁻¹ = k * r * k⁻¹ at heq
      rw [← heq]
      group
    change c * r * c⁻¹ ∈ R
    rw [show c * r * c⁻¹ = r' by
      simpa [c, mul_assoc] using heq']
    exact hr'
  have hcNorm : c ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge hmapC
    exact (Subgroup.card_map_of_injective (MulAut.conj c).injective).ge
  have hcCentral : c ∈ centralizerWithin K R := by
    refine ⟨hcK, ?_⟩
    intro r hr
    have hcommK : ⁅c, r⁆ ∈ K := by
      have hmem : ⁅c, r⁆ ∈ ⁅K, R⁆ :=
        Subgroup.commutator_mem_commutator hcK hr
      apply hHK
      simpa [H, Subgroup.commutator_comm R K] using hmem
    have hcommR : ⁅c, r⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem
        ((Subgroup.mem_normalizer_iff.mp hcNorm r).mp hr)
        (R.inv_mem hr)
    have hcommOne : ⁅c, r⁆ = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hKR.disjoint]
      exact ⟨hcommK, hcommR⟩
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcommOne).symm
  have hdecomp : hG * c = k := by
    dsimp [c]
    group
  rw [← hdecomp]
  exact (⁅R, K⁆ ⊔ centralizerWithin K R).mul_mem
    ((show H ≤ ⁅R, K⁆ ⊔ centralizerWithin K R from le_sup_left) hhH)
    ((show centralizerWithin K R ≤
      ⁅R, K⁆ ⊔ centralizerWithin K R from le_sup_right) hcCentral)

/-- Exact no-global-factorization form of MathComp's `coprime_cent_prod`. -/
theorem le_commutator_sup_centralizerWithin_of_coprime
    [IsSolvable K]
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : (Nat.card K).Coprime (Nat.card R)) :
    K ≤ ⁅R, K⁆ ⊔ centralizerWithin K R := by
  classical
  let L : Subgroup G := K ⊔ R
  let KL : Subgroup L := K.subgroupOf L
  let RL : Subgroup L := R.subgroupOf L
  have hKLmap : KL.map L.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le (show K ≤ L from le_sup_left)
  have hRLmap : RL.map L.subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le (show R ≤ L from le_sup_right)
  have hcardKL : Nat.card KL = Nat.card K :=
    natCard_subgroupOf_eq (show K ≤ L from le_sup_left)
  have hcardRL : Nat.card RL = Nat.card R :=
    natCard_subgroupOf_eq (show R ≤ L from le_sup_right)
  have hnormKLambient : L ≤ Subgroup.normalizer (K : Set G) := by
    dsimp [L]
    exact sup_le Subgroup.le_normalizer hnormK
  letI : KL.Normal := by
    exact Subgroup.normal_subgroupOf_of_le_normalizer hnormKLambient
  have hsup : KL ⊔ RL = ⊤ := by
    change K.subgroupOf L ⊔ R.subgroupOf L = ⊤
    rw [← Subgroup.subgroupOf_sup
      (show K ≤ L from le_sup_left) (show R ≤ L from le_sup_right)]
    exact Subgroup.subgroupOf_self L
  have hdisKR : Disjoint K R :=
    Subgroup.disjoint_of_coprime_natCard hcop
  have hdis : Disjoint KL RL := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hdisKR]
      exact ⟨hz.1, hz.2⟩
    exact Subgroup.mem_bot.mp hzbot
  have hcomp : KL.IsComplement' RL := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
    rw [← Subgroup.normal_mul KL RL, hsup]
    rfl
  have hnormKL : RL ≤ Subgroup.normalizer (KL : Set L) := by
    rw [KL.normalizer_eq_top]
    exact le_top
  let toK : KL →* K :=
    { toFun := fun k ↦ ⟨((k : L) : G), k.property⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  letI : IsSolvable KL :=
    solvable_of_solvable_injective (f := toK) (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : K ↦ (z : G)) hab)
  have hcopL : (Nat.card KL).Coprime (Nat.card RL) := by
    simpa [hcardKL, hcardRL] using hcop
  have hinside : KL ≤ ⁅RL, KL⁆ ⊔ centralizerWithin KL RL :=
    le_commutator_sup_centralizerWithin_of_coprime_complement
      hcomp hnormKL hcopL
  have hmapComm : ⁅RL, KL⁆.map L.subtype = ⁅R, K⁆ := by
    rw [Subgroup.map_commutator, hRLmap, hKLmap]
  have hmapCent : (centralizerWithin KL RL).map L.subtype ≤
      centralizerWithin K R := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨hc.1, ?_⟩
    intro r hr
    let rL : L := ⟨r, (show R ≤ L from le_sup_right) hr⟩
    have hrRL : rL ∈ RL := hr
    exact congrArg Subtype.val ((mem_centralizerWithin.mp hc).2 rL hrRL)
  intro k hk
  let kL : L := ⟨k, (show K ≤ L from le_sup_left) hk⟩
  have hkKL : kL ∈ KL := hk
  have hkMap : (k : G) ∈
      (⁅RL, KL⁆ ⊔ centralizerWithin KL RL).map L.subtype :=
    ⟨kL, hinside hkKL, rfl⟩
  rw [Subgroup.map_sup, hmapComm] at hkMap
  exact (sup_le_sup le_rfl hmapCent) hkMap

end Submission.OddOrder.MathlibSupport
