import Submission.OddOrder.BG.Section06.PuigConsequences
import Submission.OddOrder.BG.Section07.MaximalSubgroups

/-!
# Bender--Glauberman Theorem 8.1(b): the mapped Puig center

This file packages the ambient image of the center of the Puig subgroup of a
Sylow subgroup of a maximal subgroup.  Keeping the center in the ambient group
is useful later: maximal subgroups containing the same ambient Sylow subgroup
then literally use the same subgroup.
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport

universe u

private theorem map_centerWithin_puig_top_eq
    {G : Type u} [Group G] (D : Subgroup G) :
    (centerWithin (puig (⊤ : Subgroup D))).map D.subtype =
      centerWithin (puig D) := by
  have htop : (⊤ : Subgroup D).map D.subtype = D := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simpa only [htop] using
    (Submission.OddOrder.BG.AppendixAB.map_centerWithin_puig_eq_of_injective_on
        D.subtype (⊤ : Subgroup D) (fun _ _ hxy =>
          Subtype.ext (D.subtype_injective hxy)))

/-- The center of the Puig subgroup of a mapped Sylow subgroup lies in that
mapped Sylow subgroup. -/
theorem centerWithin_puig_map_sylow_le_map_sylow
    {G : Type u} [Group G] {M : Subgroup G} {p : ℕ}
    (P : Sylow p M) :
    centerWithin (puig ((P : Subgroup M).map M.subtype)) ≤
      (P : Subgroup M).map M.subtype :=
  (centralizerWithin_le_left _ _).trans
    (puig_le ((P : Subgroup M).map M.subtype))

/-- Under the hypotheses of the Puig-center theorem, the canonical ambient
Puig center is normal after restriction to the maximal subgroup. -/
theorem centerWithin_puig_map_sylow_normal_subgroupOf
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (M : Subgroup G) (P : Sylow p M)
    (hodd : Odd (Nat.card M)) (hsol : IsSolvable M)
    (hcore : pPrimeCore p M = ⊥) :
    ((centerWithin (puig ((P : Subgroup M).map M.subtype))).subgroupOf M).Normal := by
  let ZM : Subgroup M := centerWithin (puig (P : Subgroup M))
  let Z : Subgroup G := centerWithin (puig ((P : Subgroup M).map M.subtype))
  have hZleM : Z ≤ M :=
    (centerWithin_puig_map_sylow_le_map_sylow P).trans
      (Subgroup.map_subtype_le (P : Subgroup M))
  have hmap : ZM.map M.subtype = Z := by
    simpa only [ZM, Z] using
      (Submission.OddOrder.BG.AppendixAB.map_centerWithin_puig_eq_of_injective_on
          M.subtype (P : Subgroup M) (fun _ _ hxy =>
            Subtype.ext (M.subtype_injective hxy)))
  have hsubgroupOf : Z.subgroupOf M = ZM := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hZleM, hmap]
  letI : IsSolvable M := hsol
  have hZMnormal : ZM.Normal := by
    simpa only [ZM] using
      (Submission.OddOrder.BG.Section06.Puig_center_normal hodd P hcore)
  simpa only [Z, hsubgroupOf] using hZMnormal

/-- A nontrivial subgroup of a mapped Sylow subgroup forces the canonical
ambient Puig center to be nontrivial. -/
theorem centerWithin_puig_map_sylow_ne_bot_of_le
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M : Subgroup G} (P : Sylow p M) {A : Subgroup G}
    (hA : A ≤ (P : Subgroup M).map M.subtype) (hAne : A ≠ ⊥) :
    centerWithin (puig ((P : Subgroup M).map M.subtype)) ≠ ⊥ := by
  let PM : Subgroup G := (P : Subgroup M).map M.subtype
  let R : Subgroup PM := centerWithin (puig (⊤ : Subgroup PM))
  have hRmap : R.map PM.subtype = centerWithin (puig PM) := by
    simpa only [R] using map_centerWithin_puig_top_eq PM
  intro hZbot
  have hRbot : R = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective R PM.subtype_injective).mp
    rw [hRmap, hZbot]
  have hPMp : IsPGroup p PM := by
    dsimp only [PM]
    exact P.isPGroup'.map M.subtype
  have htopbot : (⊤ : Subgroup PM) = ⊥ :=
    Submission.OddOrder.BG.Section06.trivg_center_Puig_pgroup hPMp (by
      simpa only [R] using hRbot)
  apply hAne
  apply le_bot_iff.mp
  intro a ha
  have haPM : a ∈ PM := by
    exact hA ha
  have hatop : (⟨a, haPM⟩ : PM) ∈ (⊤ : Subgroup PM) := trivial
  rw [htopbot] at hatop
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hatop))

/-- The ambient normalizer of a mapped Sylow subgroup normalizes its
canonical ambient Puig center. -/
theorem normalizer_map_sylow_le_normalizer_centerWithin_puig
    {G : Type u} [Group G] {p : ℕ} {M : Subgroup G}
    (P : Sylow p M) :
    Subgroup.normalizer ((P : Subgroup M).map M.subtype : Set G) ≤
      Subgroup.normalizer
        (centerWithin (puig ((P : Subgroup M).map M.subtype)) : Set G) := by
  let PM : Subgroup G := (P : Subgroup M).map M.subtype
  let R : Subgroup PM := centerWithin (puig (⊤ : Subgroup PM))
  letI : R.Characteristic := by
    dsimp only [R]
    infer_instance
  have hRmap : R.map PM.subtype = centerWithin (puig PM) := by
    simpa only [R] using map_centerWithin_puig_top_eq PM
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [← hRmap] at hz ⊢
    exact characteristic_map_subtype_invariant_under_normalizer
      PM (Subgroup.normalizer (PM : Set G)) R le_rfl g hg z hz
  · intro hz
    have hginv : g⁻¹ ∈ Subgroup.normalizer (PM : Set G) :=
      (Subgroup.normalizer (PM : Set G)).inv_mem hg
    have hzR : g * z * g⁻¹ ∈ R.map PM.subtype := by
      rwa [hRmap]
    have hz' := characteristic_map_subtype_invariant_under_normalizer
      PM (Subgroup.normalizer (PM : Set G)) R le_rfl g⁻¹ hginv
        (g * z * g⁻¹) hzR
    rw [hRmap] at hz'
    simpa [PM, mul_assoc] using hz'

/-- If a maximal subgroup has trivial `p'`-core and contains a nontrivial
subgroup of the image of one of its Sylow `p`-subgroups, that image is already
an ambient Sylow `p`-subgroup. -/
theorem exists_ambient_sylow_eq_map_of_pPrimeCore_eq_bot
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M : Subgroup G) (P : Sylow p M)
    (hM : M ∈ Submission.OddOrder.BG.Section07.minSimple_max_groups (G := G))
    (hcore : pPrimeCore p M = ⊥) {A : Subgroup G}
    (hA : A ≤ (P : Subgroup M).map M.subtype) (hAne : A ≠ ⊥) :
    ∃ Q : Sylow p G,
      (Q : Subgroup G) = (P : Subgroup M).map M.subtype := by
  let PM : Subgroup G := (P : Subgroup M).map M.subtype
  let Z : Subgroup G := centerWithin (puig PM)
  have hZlePM : Z ≤ PM := by
    simpa only [Z, PM] using centerWithin_puig_map_sylow_le_map_sylow P
  have hZleM : Z ≤ M :=
    hZlePM.trans (Subgroup.map_subtype_le (P : Subgroup M))
  have hZnormal : (Z.subgroupOf M).Normal := by
    simpa only [Z, PM] using
      centerWithin_puig_map_sylow_normal_subgroupOf
        M P (Submission.OddOrder.BG.Section07.mFT_odd M)
          (Submission.OddOrder.BG.Section07.mmax_sol hM) hcore
  have hZne : Z ≠ ⊥ := by
    simpa only [Z, PM] using
      centerWithin_puig_map_sylow_ne_bot_of_le P hA hAne
  have hnormalizerZ : Subgroup.normalizer (Z : Set G) = M :=
    Submission.OddOrder.BG.Section07.mmax_normal hM hZleM hZnormal hZne
  apply Submission.OddOrder.BG.Section07.mmax_sigma_Sylow hM P
  have hnormalizers :
      Subgroup.normalizer (PM : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
    simpa only [PM, Z] using
      normalizer_map_sylow_le_normalizer_centerWithin_puig P
  rwa [hnormalizerZ] at hnormalizers

end Submission.OddOrder.BG.Section08
