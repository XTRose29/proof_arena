import Submission.OddOrder.MathlibSupport.QuotientFixedPointOrbit

/-!
Coprime fixed-coset lifting when the quotient subgroup is fixed pointwise.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {X : Type v}
variable [Group G] [Group X] [MulDistribMulAction G X]
variable (N : Subgroup X) [N.Normal] [MulAction.QuotientAction G N]

omit [N.Normal] [MulAction.QuotientAction G N] in
/-- A fixed coset has no nontrivial error in a pointwise-fixed subgroup whose
cardinality is coprime to the order of the acting element. -/
theorem fixed_of_coprime_order_of_fixed_subgroup
    (g : G) (x : X)
    (hcop : (Nat.card N).Coprime (orderOf g))
    (hfixN : ∀ n : N, g • (n : X) = n)
    (herr : (g • x)⁻¹ * x ∈ N) :
    g • x = x := by
  let n : N := ⟨(g • x)⁻¹ * x, herr⟩
  have hgx : g • x = x * (n : X)⁻¹ := by
    change g • x = x * ((g • x)⁻¹ * x)⁻¹
    group
  have hgn : g • (n : X) = n := hfixN n
  have hiter : ∀ k : Nat, g ^ k • x = x * ((n : X)⁻¹) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', mul_smul, ih, smul_mul', hgx, smul_pow', smul_inv', hgn]
        simp [pow_succ', mul_assoc]
  have hxpow : x = x * ((n : X)⁻¹) ^ orderOf g := by
    simpa using hiter (orderOf g)
  have hnvalpow : ((n : X)⁻¹) ^ orderOf g = 1 := by
    have hcancel := congrArg (fun y : X => x⁻¹ * y) hxpow
    simpa [mul_assoc] using hcancel.symm
  have hninv : n⁻¹ = 1 := by
    apply (powCoprime hcop).injective
    simp only [powCoprime_apply]
    apply Subtype.ext
    simpa using hnvalpow
  have hn : n = 1 := inv_eq_one.mp hninv
  simpa [hn] using hgx

omit [N.Normal] [MulAction.QuotientAction G N] in
/-- Under the same coprime hypotheses, a representative of a fixed coset lies
in the quotient subgroup whenever all genuinely fixed representatives do. -/
theorem fixed_rep_mem_of_coprime_order_of_fixed_subgroup
    (g : G)
    (hcop : (Nat.card N).Coprime (orderOf g))
    (hfixN : ∀ n : N, g • (n : X) = n)
    (hfixed : ∀ x : X, g • x = x -> x ∈ N) :
    ∀ x : X, (g • x)⁻¹ * x ∈ N -> x ∈ N := by
  intro x hx
  exact hfixed x
    (fixed_of_coprime_order_of_fixed_subgroup N g x hcop hfixN hx)

/-- Pointwise-fixed coprime quotient subgroups turn representative fixed-point
control into full-size nonidentity quotient orbits. -/
theorem natCard_quotient_orbit_eq_natCard_of_coprime_fixed_subgroup
    [Finite G] (q : X ⧸ N) (hq : q ≠ 1)
    (hcop : ∀ g : G, g ≠ 1 -> (Nat.card N).Coprime (orderOf g))
    (hfixN : ∀ g : G, ∀ n : N, g • (n : X) = n)
    (hfixed : ∀ g : G, g ≠ 1 -> ∀ x : X, g • x = x -> x ∈ N) :
    Nat.card (MulAction.orbit G q) = Nat.card G := by
  apply natCard_quotient_orbit_eq_natCard_of_fixed_rep_mem N q hq
  intro g hg
  exact fixed_rep_mem_of_coprime_order_of_fixed_subgroup N g
    (hcop g hg) (hfixN g) (hfixed g hg)

end Submission.OddOrder.MathlibSupport
