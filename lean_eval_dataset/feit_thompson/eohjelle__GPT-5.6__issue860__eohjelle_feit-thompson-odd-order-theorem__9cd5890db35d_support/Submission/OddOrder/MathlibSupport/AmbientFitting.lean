import Submission.OddOrder.MathlibSupport.FittingNilpotent
import Submission.OddOrder.MathlibSupport.PCoreFunctorial
import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer

/-!
# Ambient Fitting subgroups

The Fitting core of a subgroup, mapped back into the ambient group, together
with its containment, normalizer, nilpotence, and prime-core identities.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- The Fitting core of `M`, viewed in the ambient group. -/
def fittingWithin (M : Subgroup G) : Subgroup G :=
  (fittingCore M).map M.subtype

theorem fittingWithin_le (M : Subgroup G) : fittingWithin M ≤ M :=
  Subgroup.map_subtype_le _

theorem fittingWithin_subgroupOf_eq (M : Subgroup G) :
    (fittingWithin M).subgroupOf M = fittingCore M := by
  change ((fittingCore M).map M.subtype).comap M.subtype = fittingCore M
  exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

instance fittingWithin_subgroupOf_normal (M : Subgroup G) :
    ((fittingWithin M).subgroupOf M).Normal := by
  rw [fittingWithin_subgroupOf_eq]
  infer_instance

theorem fittingWithin_le_normalizer (M : Subgroup G) :
    M ≤ Subgroup.normalizer (fittingWithin M : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (fittingWithin_le M)).mp
    (by infer_instance)

theorem le_normalizer_fittingWithin_of_le_normalizer
    {M N : Subgroup G}
    (hNM : N ≤ Subgroup.normalizer (M : Set G)) :
    N ≤ Subgroup.normalizer (fittingWithin M : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  simpa [fittingWithin] using
    (characteristic_map_subtype_invariant_under_normalizer
      M N (fittingCore M) hNM)

instance fittingWithin_isNilpotent [Finite G] (M : Subgroup G) :
    Group.IsNilpotent (fittingWithin M) := by
  exact Group.nilpotent_of_mulEquiv
    ((fittingCore M).equivMapOfInjective M.subtype M.subtype_injective)

theorem map_pCore_fittingCore_eq_pCore [Finite G] (M : Subgroup G)
    (p : ℕ) [Fact p.Prime] :
    (pCore p (fittingCore M)).map (fittingCore M).subtype = pCore p M := by
  apply le_antisymm
  · apply le_pCore (pCore_isPGroup.map (fittingCore M).subtype)
    infer_instance
  · rw [← Subgroup.map_subgroupOf_eq_of_le (pCore_le_fittingCore p)]
    apply Subgroup.map_mono
    apply le_pCore
    · exact pCore_isPGroup.of_equiv
        (Subgroup.subgroupOfEquivOfLe (pCore_le_fittingCore p)).symm
    · infer_instance

theorem map_pCore_fittingWithin_eq_map_pCore [Finite G] (M : Subgroup G)
    (p : ℕ) [Fact p.Prime] :
    (pCore p (fittingWithin M)).map (fittingWithin M).subtype =
      (pCore p M).map M.subtype := by
  let eF : fittingCore M ≃* fittingWithin M :=
    (fittingCore M).equivMapOfInjective M.subtype M.subtype_injective
  have hker : IsPGroup p eF.toMonoidHom.ker := by
    rw [eF.toMonoidHom.ker_eq_bot_iff.mpr eF.injective]
    exact IsPGroup.of_bot
  have hpmap : (pCore p (fittingCore M)).map eF.toMonoidHom =
      pCore p (fittingWithin M) :=
    map_pCore_eq_of_surjective_of_ker_isPGroup eF.toMonoidHom
      eF.surjective hker
  rw [← hpmap, Subgroup.map_map]
  have hcomp : (fittingWithin M).subtype.comp eF.toMonoidHom =
      M.subtype.comp (fittingCore M).subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, map_pCore_fittingCore_eq_pCore]

/-- The Fitting core of the `p'`-core agrees with the `p'`-core of the
Fitting core, after both are mapped into the ambient group. -/
theorem map_fittingCore_pPrimeCore_eq_map_pPrimeCore_fittingCore
    [Finite G] (p : ℕ) [Fact p.Prime] :
    (fittingCore (pPrimeCore p G)).map (pPrimeCore p G).subtype =
      (pPrimeCore p (fittingCore G)).map (fittingCore G).subtype := by
  let N : Subgroup G := pPrimeCore p G
  let F : Subgroup G := fittingCore G
  let L : Subgroup G := (fittingCore N).map N.subtype
  let R : Subgroup G := (pPrimeCore p F).map F.subtype
  change L = R
  have hLN : L ≤ N := by
    exact Subgroup.map_subtype_le _
  have hLnormal : L.Normal := by
    dsimp [L, N]
    infer_instance
  have hLnil : Group.IsNilpotent L := by
    dsimp [L]
    exact Group.nilpotent_of_mulEquiv
      ((fittingCore N).equivMapOfInjective N.subtype N.subtype_injective)
  have hLF : L ≤ F := by
    exact nilpotent_normal_le_fittingCore hLnormal hLnil
  have hLcop : Nat.Coprime p (Nat.card L) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).coprime_dvd_right
      (L.subgroupOf N).card_subgroup_dvd_card
  have hLR : L ≤ R := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hLF]
    apply Subgroup.map_mono
    apply le_pPrimeCore
    · rw [IsPPrimeSubgroup]
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLF).toEquiv]
    · infer_instance
  have hRF : R ≤ F := by
    exact Subgroup.map_subtype_le _
  have hRnormal : R.Normal := by
    dsimp [R, F]
    infer_instance
  have hRcop : Nat.Coprime p (Nat.card R) := by
    dsimp [R]
    rw [Subgroup.card_map_of_injective F.subtype_injective]
    exact pPrimeCore_coprime_card
  have hRN : R ≤ N := by
    exact le_pPrimeCore hRcop hRnormal
  have hRnil : Group.IsNilpotent R := by
    letI : Group.IsNilpotent F := by
      dsimp [F]
      infer_instance
    letI : Group.IsNilpotent (pPrimeCore p F) := by infer_instance
    exact Group.nilpotent_of_mulEquiv
      ((pPrimeCore p F).equivMapOfInjective F.subtype F.subtype_injective)
  have hRL : R ≤ L := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hRN]
    apply Subgroup.map_mono
    apply nilpotent_normal_le_fittingCore
    · infer_instance
    · letI : Group.IsNilpotent R := hRnil
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hRN).symm
  exact le_antisymm hLR hRL

end Submission.OddOrder.MathlibSupport
