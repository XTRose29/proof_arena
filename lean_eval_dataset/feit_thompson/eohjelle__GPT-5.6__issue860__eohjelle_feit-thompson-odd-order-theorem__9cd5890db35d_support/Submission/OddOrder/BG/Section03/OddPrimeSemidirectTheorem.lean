import Submission.OddOrder.BG.Section03.OddPrimeSemidirectExtraspecial

/-!
Strong-induction closure of Bender-Glauberman Theorem 3.4.
-/

namespace Submission.OddOrder.BG.Section03

universe u v w

noncomputable section

/-- The cardinality-indexed statement used to close the recursive subgroup
and quotient branches of Theorem 3.4. -/
def OddPrimeSemidirectStatement
    (k : Type v) [Field k] (n : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] [IsSolvable G],
    Nat.card G = n →
    ∀ (V : Type w) [AddCommGroup V] [Module k V] [Finite V]
      (rho : Representation k G V) (K R : Subgroup G) [K.Normal],
      K.IsComplement' R →
      Nat.Coprime (Nat.card K) (Nat.card R) →
      Odd (Nat.card G) →
      (Nat.card R).Prime →
      (Nat.card G : k) ≠ 0 →
      Representation.invariants
        (rho.comp R.subtype : Representation k R V) = ⊥ →
      ⁅R, K⁆ ≤ rho.ker

/-- Theorem 3.4 holds at every finite cardinality. -/
theorem oddPrimeSemidirectStatement_all
    (k : Type v) [Field k] (n : ℕ) :
    OddPrimeSemidirectStatement.{u, v, w} k n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G _ _ _ hcard V _ _ _ rho K R _ hKR hcop hodd hRprime
        hGcard hfix
      have hnormK : R ≤ Subgroup.normalizer (K : Set G) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : K.Normal)]
        exact le_top
      have ihGlobal : OddPrimeSemidirectGlobalInductionHypothesis.{u, v, w}
          k (Nat.card G) := by
        intro J _ _ _ W _ _ _ rhoJ L T _ hlt hLT hcopJT hoddJ hTprime
          hJcard hfixJ
        apply ih (Nat.card J)
        · rwa [← hcard]
        · rfl
        · exact hLT
        · exact hcopJT
        · exact hoddJ
        · exact hTprime
        · exact hJcard
        · exact hfixJ
      exact kernel_commutator_le_representation_ker_of_extraspecial_theorem
        rho hKR hnormK hcop hodd hRprime hGcard hfix ihGlobal

/-- `BGsection3.v: odd_prime_sdprod_rfix0` in mathlib-facing form. -/
theorem odd_prime_sdprod_rfix0
    {k : Type v} [Field k]
    {G : Type u} [Group G] [Fintype G] [IsSolvable G]
    {V : Type w} [AddCommGroup V] [Module k V] [Finite V]
    (rho : Representation k G V) (K R : Subgroup G) [K.Normal]
    (hKR : K.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hRprime : (Nat.card R).Prime)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hfix : Representation.invariants
      (rho.comp R.subtype : Representation k R V) = ⊥) :
    ⁅R, K⁆ ≤ rho.ker :=
  oddPrimeSemidirectStatement_all k (Nat.card G) G rfl V rho K R
    hKR hcop hodd hRprime hGcard hfix

end

end Submission.OddOrder.BG.Section03
