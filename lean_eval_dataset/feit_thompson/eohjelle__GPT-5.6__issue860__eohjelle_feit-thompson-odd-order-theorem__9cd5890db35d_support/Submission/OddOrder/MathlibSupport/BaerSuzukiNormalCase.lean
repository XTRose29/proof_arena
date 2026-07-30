import Submission.OddOrder.MathlibSupport.BaerSuzukiSylow

/-!
The normal-Sylow branch of the Baer-Suzuki induction.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- If the conjugacy class of `x` is contained in a Sylow subgroup of the
subgroup it generates, then `x` already belongs to the ambient p-core. -/
theorem mem_pCore_of_conjugatesOf_le_sylow {p : ℕ} {x : G}
    (P : Sylow p (conjugacyClassGenerated x))
    (hclass : conjugatesOf x ⊆
      (P : Subgroup (conjugacyClassGenerated x)).map
        (conjugacyClassGenerated x).subtype) :
    x ∈ pCore p G := by
  let E : Subgroup G := conjugacyClassGenerated x
  let PG : Subgroup G := (P : Subgroup E).map E.subtype
  have hEP : E ≤ PG := by
    change Subgroup.closure (conjugatesOf x) ≤ PG
    exact (Subgroup.closure_le PG).mpr hclass
  have hPE : PG ≤ E := Subgroup.map_subtype_le _
  have hEP_eq : E = PG := le_antisymm hEP hPE
  have hPGp : IsPGroup p PG := P.isPGroup'.map E.subtype
  have hEp : IsPGroup p E := by
    rw [hEP_eq]
    exact hPGp
  exact mem_pCore_of_conjugacyClassGenerated_isPGroup hEp

end Submission.OddOrder.MathlibSupport
