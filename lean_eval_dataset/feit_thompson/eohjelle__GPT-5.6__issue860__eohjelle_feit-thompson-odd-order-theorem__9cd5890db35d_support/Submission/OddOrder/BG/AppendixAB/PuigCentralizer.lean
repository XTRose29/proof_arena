import Submission.OddOrder.BG.AppendixAB.PuigStructural
import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.SelfCentralizing

/-!
Center and centralizer properties of the Puig series from Bender--Glauberman
Appendix B.

This module contains the characteristic-center statement and all six
inclusions in Lemma B.1(f).  The self-centralizing inclusions use the maximal
normal abelian subgroup argument in `MathlibSupport.SelfCentralizing`.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- This is `BGappendixAB.center_Puig_char`, stated for every characteristic
ambient subgroup rather than only the whole group. -/
instance centerWithin_puig_characteristic (D : Subgroup G) [D.Characteristic] :
    (centerWithin (puig D)).Characteristic := by
  change (puig D ⊓ Subgroup.centralizer (puig D : Set G)).Characteristic
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  rw [Subgroup.map_inf _ _ _ e.injective]
  rw [Subgroup.characteristic_iff_map_eq.mp
    (by infer_instance : (puig D).Characteristic) e]
  rw [Subgroup.characteristic_iff_map_eq.mp
    (by infer_instance : (Subgroup.centralizer (puig D : Set G)).Characteristic) e]

/-- This is `BGappendixAB.sub_center_cent_Puig_at`, i.e. the second inclusion
in B & G Lemma B.1(f). -/
theorem centerWithin_le_centralizerWithin_puigAt (n : ℕ) (D : Subgroup G) :
    centerWithin D ≤ centralizerWithin D (puigAt n D) :=
  centerWithin_le_centralizerWithin (puigAt_le n D)

/-- The center inclusion for the lower terminal Puig term, corresponding to
the fourth inclusion in B & G Lemma B.1(f). -/
theorem centerWithin_le_centralizerWithin_puigInf (D : Subgroup G) :
    centerWithin D ≤ centralizerWithin D (puigInf D) :=
  centerWithin_le_centralizerWithin (puigInf_le D)

/-- The center inclusion for the upper terminal Puig term, corresponding to
the sixth inclusion in B & G Lemma B.1(f). -/
theorem centerWithin_le_centralizerWithin_puig (D : Subgroup G) :
    centerWithin D ≤ centralizerWithin D (puig D) :=
  centerWithin_le_centralizerWithin (puig_le D)

/-- This is `BGappendixAB.sub_cent_Puig_at`, the first inclusion in B & G
Lemma B.1(f). -/
theorem centralizerWithin_puigAt_le {p : ℕ} [Fact p.Prime] (n : ℕ)
    (D : Subgroup G) [Finite D] (hn : 0 < n) (hD : IsPGroup p D) :
    centralizerWithin D (puigAt n D) ≤ puigAt n D := by
  obtain ⟨M', hM', hM'cent⟩ :=
    exists_selfCentralizing_isNormalAbelian (G := D) hD
  letI : M'.Normal := hM'.normal
  letI : IsMulCommutative M' := hM'.isMulCommutative
  let M : Subgroup G := M'.map D.subtype
  have hMD : M ≤ D := Subgroup.map_subtype_le M'
  haveI : IsMulCommutative M := by
    dsimp [M]
    infer_instance
  have hMsub : M.subgroupOf D = M' := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMD]
  have hMnormal : D ≤ Subgroup.normalizer M := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hMD).mp
    exact hMsub.symm ▸ (by infer_instance)
  have hMabelian : IsAbelianSubgroup M := fun x y => mul_comm' x y
  have hMcent : centralizerWithin D M = M := by
    apply le_antisymm ?_ ?_
    · intro x hx
      let xD : D := ⟨x, hx.1⟩
      have hxDcent : xD ∈ Subgroup.centralizer (M' : Set D) := by
        intro m hm
        apply Subtype.ext
        exact hx.2 m (by exact ⟨m, hm, rfl⟩)
      have hxM' : xD ∈ M' := by
        rw [← hM'cent]
        exact hxDcent
      exact ⟨xD, hxM', rfl⟩
    · intro x hx
      refine ⟨hMD hx, ?_⟩
      intro m hm
      exact congrArg Subtype.val (mul_comm' ⟨m, hm⟩ ⟨x, hx⟩)
  have hMpuig : M ≤ puigAt n D :=
    normal_abelian_le_puigAt hn hMD hMnormal hMabelian
  calc
    centralizerWithin D (puigAt n D) ≤ centralizerWithin D M :=
      centralizerWithin_antitone_right hMpuig
    _ = M := hMcent
    _ ≤ puigAt n D := hMpuig

/-- This is `BGappendixAB.sub_cent_Puig_inf`, the third inclusion in B & G
Lemma B.1(f). -/
theorem centralizerWithin_puigInf_le {p : ℕ} [Fact p.Prime] (D : Subgroup G)
    [Finite D] (hD : IsPGroup p D) : centralizerWithin D (puigInf D) ≤ puigInf D := by
  rw [puigInf]
  apply centralizerWithin_puigAt_le (p := p) _ D (by
    have hcard : 0 < Nat.card D := Nat.card_pos
    omega) hD

/-- This is `BGappendixAB.sub_cent_Puig`, the fifth inclusion in B & G
Lemma B.1(f). -/
theorem centralizerWithin_puig_le {p : ℕ} [Fact p.Prime] (D : Subgroup G)
    [Finite D] (hD : IsPGroup p D) : centralizerWithin D (puig D) ≤ puig D := by
  rw [puig]
  apply centralizerWithin_puigAt_le (p := p) _ D (by omega) hD

/-- This is `BGappendixAB.trivg_center_Puig_pgroup`, the final remark in B & G
Lemma B.1(f), in direct rather than contrapositive form. -/
theorem eq_bot_of_centerWithin_puig_eq_bot {p : ℕ} [Fact p.Prime]
    (D : Subgroup G) [Finite D] (hD : IsPGroup p D)
    (hcenter : centerWithin (puig D) = ⊥) : D = ⊥ := by
  by_contra hDbot
  letI : Nontrivial D := D.nontrivial_iff_ne_bot.mpr hDbot
  have hcenterD : centerWithin D ≤ centerWithin (puig D) := by
    intro x hx
    have hxCentralizer : x ∈ centralizerWithin D (puig D) :=
      centerWithin_le_centralizerWithin_puig D hx
    exact ⟨centralizerWithin_puig_le D hD hxCentralizer, hxCentralizer.2⟩
  have hcenterDbot : centerWithin D = ⊥ :=
    le_bot_iff.mp (hcenterD.trans_eq hcenter)
  exact centerWithin_ne_bot D hD hcenterDbot

end Submission.OddOrder.BG.AppendixAB
