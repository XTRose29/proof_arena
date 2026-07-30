import Submission.OddOrder.BG.Section07.PrimeSetCoreFunctorial
import Submission.OddOrder.MathlibSupport.AmbientFitting

/-!
# The prime-set core of the Fitting subgroup

This is the ambient-subgroup form of MathComp's `Fitting_pcore`: the
Fitting subgroup of a prime-set core is the corresponding prime-set core
of the Fitting subgroup.
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07

universe u

/-- The Fitting core of a prime-set core is the prime-set core of the
Fitting core, with all subgroups viewed in the original ambient group. -/
theorem fittingWithin_primeSetCore_eq_primeSetCore_fittingWithin
    {G : Type u} [Group G] [Finite G]
    (pi : Set ℕ) (X : Subgroup G) :
    fittingWithin (primeSetCore pi X) =
      primeSetCore pi (fittingWithin X) := by
  let N : Subgroup G := primeSetCore pi X
  let F : Subgroup G := fittingWithin X
  let L : Subgroup G := fittingWithin N
  let R : Subgroup G := primeSetCore pi F
  change L = R

  have hNX : N ≤ X := by
    simpa [N] using primeSetCore_le pi X
  have hNpi : IsPiNumber pi (Nat.card N) := by
    simpa [N] using primeSetCore_isPiNumber pi X
  have hXnormN : X ≤ Subgroup.normalizer (N : Set G) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mp (by
      simpa [N] using primeSetCore_normal pi X)

  have hFX : F ≤ X := by
    simpa [F] using fittingWithin_le X
  have hXnormF : X ≤ Subgroup.normalizer (F : Set G) := by
    simpa [F] using fittingWithin_le_normalizer X

  have hLN : L ≤ N := by
    simpa [L] using fittingWithin_le N
  have hLX : L ≤ X := hLN.trans hNX
  have hXnormL : X ≤ Subgroup.normalizer (L : Set G) := by
    simpa [L] using
      (le_normalizer_fittingWithin_of_le_normalizer
        (M := N) (N := X) hXnormN)
  have hLnormalX : (L.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hXnormL
  have hLF : L ≤ F := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hLX]
    apply Subgroup.map_mono
    apply nilpotent_normal_le_fittingCore hLnormalX
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLX).symm
  have hLnormalF : (L.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLF).mpr
      (hFX.trans hXnormL)
  have hLpi : IsPiNumber pi (Nat.card L) := by
    apply hNpi.of_dvd
    rw [← Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hLN).toEquiv]
    exact (L.subgroupOf N).card_subgroup_dvd_card
  have hLR : L ≤ R := by
    change L ≤ primeSetCore pi F
    rw [primeSetCore]
    exact le_sSup ⟨hLF, hLnormalF, hLpi⟩

  have hRF : R ≤ F := by
    simpa [R] using primeSetCore_le pi F
  have hRX : R ≤ X := hRF.trans hFX
  have hRpi : IsPiNumber pi (Nat.card R) := by
    simpa [R] using primeSetCore_isPiNumber pi F
  have hXnormR : X ≤ Subgroup.normalizer (R : Set G) := by
    simpa [R] using
      (le_normalizer_primeSetCore_of_le_normalizer
        (pi := pi) (X := F) (N := X) hXnormF)
  have hRnormalX : (R.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRX).mpr hXnormR
  have hRN : R ≤ N := by
    change R ≤ primeSetCore pi X
    rw [primeSetCore]
    exact le_sSup ⟨hRX, hRnormalX, hRpi⟩
  letI : Group.IsNilpotent R := by
    letI : Group.IsNilpotent F := by
      dsimp [F]
      infer_instance
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hRF)
  have hRnormalN : (R.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).mpr
      (hNX.trans hXnormR)
  have hRL : R ≤ L := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hRN]
    apply Subgroup.map_mono
    apply nilpotent_normal_le_fittingCore hRnormalN
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hRN).symm

  exact le_antisymm hLR hRL

end Submission.OddOrder.BG.Section08
