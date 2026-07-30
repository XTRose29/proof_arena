import Submission.OddOrder.MathlibSupport.PCoreFunctorial
import Mathlib.GroupTheory.Nilpotent

/-!
The `p`-core of the quotient by the `p`-core is trivial.

For finite nilpotent groups this also identifies the expected `p'` cardinality
consequence.  These are the mathlib-facing forms of the
`trivg_pcore_quotient` bridge used in `BGsection5.v: Aut_narrow`.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] {p : ℕ}

/-- Quotienting a group by its `p`-core leaves a group with trivial
`p`-core. -/
theorem pCore_quotient_pCore_eq_bot :
    pCore p (G ⧸ pCore p G) = ⊥ := by
  rw [← map_pCore_quotient_eq
    (pCore_isPGroup (p := p) (G := G))]
  apply (Subgroup.map_eq_bot_iff (pCore p G)).mpr
  rw [QuotientGroup.ker_mk']

/-- A finite nilpotent group with trivial `p`-core has cardinality not
divisible by `p`. -/
theorem not_dvd_natCard_of_pCore_eq_bot_of_isNilpotent
    [Finite G] [Fact p.Prime] [Group.IsNilpotent G]
    (hcore : pCore p G = ⊥) :
    ¬ p ∣ Nat.card G := by
  classical
  let P : Sylow p G := Classical.choice inferInstance
  intro hp
  have hPnormal : (P : Subgroup G).Normal := inferInstance
  have hPle : (P : Subgroup G) ≤ pCore p G :=
    le_pCore P.isPGroup' hPnormal
  have hPbot : (P : Subgroup G) = ⊥ := by
    apply le_antisymm
    · simpa [hcore] using hPle
    · exact bot_le
  exact P.ne_bot_of_dvd_card hp hPbot

/-- The quotient by the `p`-core of a finite nilpotent group has cardinality
not divisible by `p`. -/
theorem not_dvd_natCard_quotient_pCore_of_isNilpotent
    [Finite G] [Fact p.Prime]
    [Group.IsNilpotent (G ⧸ pCore p G)] :
    ¬ p ∣ Nat.card (G ⧸ pCore p G) :=
  not_dvd_natCard_of_pCore_eq_bot_of_isNilpotent
    pCore_quotient_pCore_eq_bot

end Submission.OddOrder.MathlibSupport
