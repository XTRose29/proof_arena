import Submission.OddOrder.BG.Section02.OddGL2AlgebraicallyClosedStep

/-!
The algebraically closed form of `BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [IsAlgClosed F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]

/-- The commutator of a finite odd-order group faithfully represented in
dimension two over an algebraically closed field is primary for the field
characteristic. -/
theorem odd_faithful_finrank_two_commutator_isPGroup
    {p : ℕ} [CharP F p] [Fact p.Prime]
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2) (hodd : Odd (Nat.card G)) :
    IsPGroup p (_root_.commutator G) := by
  let P : ℕ → Prop := fun n ↦
    ∀ (K : Type u) [Group K] [Finite K],
      Nat.card K = n →
      (sigma : Representation F K V) → Function.Injective sigma →
      Odd (Nat.card K) → IsPGroup p (_root_.commutator K)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp only [P]
        intro K _ _ hcard sigma hsigma hoddK
        apply odd_faithful_finrank_two_commutator_isPGroup_step
          sigma hsigma hdim hoddK
        intro L _ _ hlt hoddL tau htau
        have hlt' : Nat.card L < n := by
          simpa [← hcard] using hlt
        exact ih (Nat.card L) hlt' L rfl tau htau hoddL
  exact hP (Nat.card G) G rfl rho hrho hodd

end Submission.OddOrder.BG.Section02
