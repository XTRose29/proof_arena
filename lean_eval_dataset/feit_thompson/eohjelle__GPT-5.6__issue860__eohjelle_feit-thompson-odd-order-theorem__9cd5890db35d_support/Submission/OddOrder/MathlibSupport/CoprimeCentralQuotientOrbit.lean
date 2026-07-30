import Submission.OddOrder.MathlibSupport.CoprimeCentralFixedPoint

/-!
Full-size quotient orbits from coprime kernel and acting-group cardinalities.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {X : Type v}
variable [Group G] [Group X] [MulDistribMulAction G X]
variable (N : Subgroup X) [N.Normal] [MulAction.QuotientAction G N]

omit [MulDistribMulAction G X] [N.Normal] [MulAction.QuotientAction G N] in
/-- Cardinality coprimality descends to the order of each acting element. -/
theorem natCard_coprime_orderOf_of_natCard_coprime
    (hcop : (Nat.card N).Coprime (Nat.card G)) (g : G) :
    (Nat.card N).Coprime (orderOf g) :=
  hcop.coprime_dvd_right (orderOf_dvd_natCard g)

/-- Coprimality of the whole kernel with the acting group supplies the
element-order hypotheses needed for fixed-coset lifting. -/
theorem natCard_quotient_orbit_eq_natCard_of_coprime_kernel
    [Finite G] (q : X ⧸ N) (hq : q ≠ 1)
    (hcop : (Nat.card X).Coprime (Nat.card G))
    (hfixN : ∀ g : G, ∀ n : N, g • (n : X) = n)
    (hfixed : ∀ g : G, g ≠ 1 -> ∀ x : X, g • x = x -> x ∈ N) :
    Nat.card (MulAction.orbit G q) = Nat.card G := by
  have hcopN : (Nat.card N).Coprime (Nat.card G) :=
    hcop.coprime_dvd_left N.card_subgroup_dvd_card
  apply natCard_quotient_orbit_eq_natCard_of_coprime_fixed_subgroup N q hq
  · intro g _
    exact natCard_coprime_orderOf_of_natCard_coprime N hcopN g
  · exact hfixN
  · exact hfixed

end Submission.OddOrder.MathlibSupport
