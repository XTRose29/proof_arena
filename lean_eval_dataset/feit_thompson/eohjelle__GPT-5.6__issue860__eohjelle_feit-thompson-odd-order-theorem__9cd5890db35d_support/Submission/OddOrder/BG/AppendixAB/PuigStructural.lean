import Submission.OddOrder.BG.AppendixAB.PuigLimit
import Submission.OddOrder.BG.Section01.PuigFunctorial

/-!
Structural properties of the Puig series from Bender-Glauberman Appendix B.

Equivalence functoriality makes every Puig term of a characteristic subgroup
characteristic.  The final theorem ports `BGappendixAB.abelian_norm_Puig`, the
normal-abelian inclusion in every positive term.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01

variable {G : Type*} [Group G]

instance puigAt_characteristic (n : ℕ) (D : Subgroup G) [D.Characteristic] :
    (puigAt n D).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  rw [map_puigAt_equiv]
  congr 1
  exact Subgroup.characteristic_iff_map_eq.mp (by infer_instance) e

instance puigInf_characteristic (D : Subgroup G) [D.Characteristic] :
    (puigInf D).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  rw [map_puigInf_equiv]
  congr 1
  exact Subgroup.characteristic_iff_map_eq.mp (by infer_instance) e

instance puig_characteristic (D : Subgroup G) [D.Characteristic] :
    (puig D).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  rw [map_puig_equiv]
  congr 1
  exact Subgroup.characteristic_iff_map_eq.mp (by infer_instance) e

/-- This specializes `BGappendixAB.Puig_char` to the whole ambient group. -/
theorem puig_top_characteristic : (puig (⊤ : Subgroup G)).Characteristic :=
  inferInstance

/-- This is `BGappendixAB.abelian_norm_Puig`, i.e. B & G Lemma B.1(e). -/
theorem normal_abelian_le_puigAt {n : ℕ} {D A : Subgroup G} (hn : 0 < n)
    (hAD : A ≤ D) (hAnorm : D ≤ Subgroup.normalizer A)
    (hAcomm : IsAbelianSubgroup A) : A ≤ puigAt n D := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [puigAt_succ]
  apply le_sSup
  exact ⟨hAD, (puigAt_le k D).trans hAnorm, hAcomm⟩

end Submission.OddOrder.BG.AppendixAB
