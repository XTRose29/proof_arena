import Submission.OddOrder.BG.Section01.Puig

/-!
`p`-group strengthening for normalized abelian generators.

This ports `BGappendixAB.norm_abgen_pgroup`, which upgrades every generator in
a normalized-abelian presentation of a `p`-group to a normalized abelian
`p`-subgroup.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01

variable {G : Type*} [Group G] {p : ℕ} {X D : Subgroup G}

/-- This is `BGappendixAB.norm_abgen_pgroup`. -/
theorem normalizedGenerated_isPGroup (hD : IsPGroup p D)
    (hgen : GeneratedBy (NormalizedAbelian X) D) :
    GeneratedBy (PNormalizedAbelian p X) D := by
  obtain ⟨S, hS, rfl⟩ := hgen
  refine ⟨S, ?_, rfl⟩
  intro A hAS
  have hA : A ≤ sSup S := le_sSup hAS
  exact ⟨IsPGroup.to_le hD hA, hS A hAS⟩

end Submission.OddOrder.BG.AppendixAB
