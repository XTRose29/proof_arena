import Submission.OddOrder.MathlibSupport.NilpotentCentralizer
import Submission.OddOrder.MathlibSupport.StableFactor

/-!
The nilpotent faithful coprime-action centralizer theorem.

This assembles the stable-factor lemma and the nilpotent normalizer condition
into the mathlib-shaped form of `BGsection1.coprime_nil_faithful_cent_stab`.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

theorem coprime_nilpotent_centralizes_of_selfCentralizing_fixedPoints
    {A H : Subgroup G} [Group.IsNilpotent H]
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hcoprime : Nat.Coprime (Nat.card H) (Nat.card A))
    (hself : centralizerWithin H (centralizerWithin H A) ≤
      centralizerWithin H A) :
    A ≤ Subgroup.centralizer (H : Set G) := by
  let C : Subgroup G := centralizerWithin H A
  let CIn : Subgroup H := centralizerIn H A
  let NIn : Subgroup H := Subgroup.normalizer (CIn : Set H)
  let N : Subgroup G := NIn.map H.subtype
  have hCmap : CIn.map H.subtype = C := by
    exact centralizerIn_map_subtype H A
  have hNC : C ≤ N := by
    rw [← hCmap]
    exact Subgroup.map_mono Subgroup.le_normalizer
  have hNH : N ≤ H := by
    dsimp [N]
    exact Subgroup.map_subtype_le _
  have hAC : A ≤ Subgroup.centralizer (C : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hc.2 a ha).symm
  have hNnormalizesC : N ≤ Subgroup.normalizer (C : Set G) := by
    rw [← hCmap]
    dsimp [N, NIn]
    exact Subgroup.le_normalizer_map H.subtype
  have hNormalizerNormalizesCentralizer :
      Subgroup.normalizer (C : Set G) ≤
        Subgroup.normalizer (Subgroup.centralizer (C : Set G) : Set G) := by
    exact Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (C : Set G)) |>.mp inferInstance
  have hcommCentralizer : ⁅A, N⁆ ≤ Subgroup.centralizer (C : Set G) := by
    exact (Subgroup.commutator_mono hAC hNnormalizesC).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        hNormalizerNormalizesCentralizer)
  have hcommH : ⁅A, N⁆ ≤ H := by
    exact (Subgroup.commutator_mono le_rfl hNH).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hAH)
  have hcommC : ⁅A, N⁆ ≤ C := by
    apply (le_inf hcommH hcommCentralizer).trans
    simpa [C, centralizerWithin] using hself
  have hcoprimeN : Nat.Coprime (Nat.card N) (Nat.card A) :=
    hcoprime.coprime_dvd_left (Subgroup.card_dvd_of_le hNH)
  have hAN : A ≤ Subgroup.centralizer (N : Set G) :=
    stableFactor_centralizes hAC hNC hcommC hcoprimeN
  apply centralizes_of_centralizes_normalizer_centralizer (H := H) (A := A)
  simpa [N, NIn, CIn] using hAN

end Submission.OddOrder.MathlibSupport
