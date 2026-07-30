import Submission.OddOrder.MathlibSupport.MinimalNormal

/-!
Chief factors in the quotient-oriented form used by `BGsection1`.

For normal `V`, the section `U / V` is represented by the image of `U` in
`G / V`.  Requiring that image to be minimal normal gives a compact interface
that composes directly with the minimal-normal support.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- `U / V` is a chief factor of `G`. -/
def IsChiefFactor (V U : Subgroup G) [V.Normal] : Prop :=
  V ≤ U ∧ U.Normal ∧
    IsMinimalNormal (U.map (QuotientGroup.mk' V))

namespace IsChiefFactor

variable {V U : Subgroup G} [V.Normal]

theorem le (h : IsChiefFactor V U) : V ≤ U :=
  h.1

theorem upper_normal (h : IsChiefFactor V U) : U.Normal :=
  h.2.1

theorem quotient_minimal_normal (h : IsChiefFactor V U) :
    IsMinimalNormal (U.map (QuotientGroup.mk' V)) :=
  h.2.2

theorem lt (h : IsChiefFactor V U) : V < U := by
  refine lt_of_le_of_ne h.le ?_
  intro hUV
  have himage : U.map (QuotientGroup.mk' V) = ⊥ := by
    rw [← hUV, QuotientGroup.map_mk'_self]
  exact h.quotient_minimal_normal.ne_bot himage

/-- `BGsection1.sol_chief_abelem`: a chief factor of a finite solvable group
is elementary abelian. -/
theorem exists_prime_isPGroup_pow_eq_one [Finite G] [IsSolvable G]
    (h : IsChiefFactor V U) :
    ∃ p : ℕ, p.Prime ∧
      IsPGroup p (U.map (QuotientGroup.mk' V)) ∧
      ∀ x : U.map (QuotientGroup.mk' V), x ^ p = 1 :=
  h.quotient_minimal_normal.exists_prime_isPGroup_pow_eq_one

end IsChiefFactor

end Submission.OddOrder.MathlibSupport
