import Submission.OddOrder.MathlibSupport.CommutatorSup
import Submission.OddOrder.MathlibSupport.CoprimeSolvableCentralProduct

/-!
Idempotence of the mixed commutator for a solvable coprime action.

This is the general internal-action form of MathComp's `coprime_commGid`.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R : Subgroup G}

private theorem commutator_commutator_eq_of_coprime_of_sup_eq_top
    [IsSolvable K]
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : (Nat.card K).Coprime (Nat.card R))
    (htop : K ⊔ R = ⊤) :
    ⁅R, ⁅R, K⁆⁆ = ⁅R, K⁆ := by
  let H : Subgroup G := ⁅R, K⁆
  let C : Subgroup G := centralizerWithin K R
  let N : Subgroup G := ⁅R, H⁆
  have hHK : H ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hnormK
  have hnormH : R ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.normalizer_commutator_ge_left R K
  have hNH : N ≤ H :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hnormH
  have hKsup : K = H ⊔ C := by
    apply le_antisymm
    · exact le_commutator_sup_centralizerWithin_of_coprime hnormK hcop
    · exact sup_le hHK (centralizerWithin_le_left K R)
  have hnormNR : R ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.normalizer_commutator_ge_left R H
  have hnormNH : H ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.normalizer_commutator_ge_right R H
  have hnormHC : C ≤ Subgroup.normalizer (H : Set G) :=
    (centralizerWithin_le_left K R).trans
      (Subgroup.normalizer_commutator_ge_right R K)
  have hnormRC : C ≤ Subgroup.normalizer (R : Set G) :=
    (show C ≤ Subgroup.centralizer (R : Set G) from inf_le_right) |>.trans
      (Subgroup.centralizer_le_normalizer (R : Set G))
  have hnormNC : C ≤ Subgroup.normalizer (N : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    dsimp [N]
    rw [Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormRC hc),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormHC hc)]
  have hnormNK : K ≤ Subgroup.normalizer (N : Set G) := by
    rw [hKsup]
    exact sup_le hnormNH hnormNC
  letI : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [← htop]
    exact sup_le hnormNK hnormNR
  have hRCbot : ⁅R, C⁆ = ⊥ := by
    rw [Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact inf_le_right
  have hRK : ⁅R, K⁆ ≤ N := by
    rw [hKsup]
    exact commutator_sup_le_of_normal le_rfl (hRCbot.le.trans bot_le)
  apply le_antisymm hNH
  simpa [H, N] using hRK

/-- For a coprime action on a finite solvable group, applying the mixed
commutator operation twice does not shrink its image. -/
theorem commutator_commutator_eq_of_coprime
    [IsSolvable K]
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : (Nat.card K).Coprime (Nat.card R)) :
    ⁅R, ⁅R, K⁆⁆ = ⁅R, K⁆ := by
  classical
  let L : Subgroup G := K ⊔ R
  let KL : Subgroup L := K.subgroupOf L
  let RL : Subgroup L := R.subgroupOf L
  have hKmap : KL.map L.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le (show K ≤ L from le_sup_left)
  have hRmap : RL.map L.subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le (show R ≤ L from le_sup_right)
  have hcardKL : Nat.card KL = Nat.card K :=
    natCard_subgroupOf_eq (show K ≤ L from le_sup_left)
  have hcardRL : Nat.card RL = Nat.card R :=
    natCard_subgroupOf_eq (show R ≤ L from le_sup_right)
  have hnormAmbient : L ≤ Subgroup.normalizer (K : Set G) := by
    dsimp [L]
    exact sup_le Subgroup.le_normalizer hnormK
  letI : KL.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormAmbient
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
  have htop : KL ⊔ RL = ⊤ := by
    change K.subgroupOf L ⊔ R.subgroupOf L = ⊤
    rw [← Subgroup.subgroupOf_sup
      (show K ≤ L from le_sup_left) (show R ≤ L from le_sup_right)]
    exact Subgroup.subgroupOf_self L
  have hidem : ⁅RL, ⁅RL, KL⁆⁆ = ⁅RL, KL⁆ :=
    commutator_commutator_eq_of_coprime_of_sup_eq_top
      hnormKL hcopL htop
  have hmapInner : ⁅RL, KL⁆.map L.subtype = ⁅R, K⁆ := by
    rw [Subgroup.map_commutator, hRmap, hKmap]
  have hmap := congrArg (Subgroup.map L.subtype) hidem
  simpa [Subgroup.map_commutator, hmapInner, hRmap] using hmap

end Submission.OddOrder.MathlibSupport
