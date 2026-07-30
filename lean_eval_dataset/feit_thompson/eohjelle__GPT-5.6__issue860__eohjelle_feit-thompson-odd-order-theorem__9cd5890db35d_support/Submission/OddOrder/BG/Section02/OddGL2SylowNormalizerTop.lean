import Submission.OddOrder.BG.Section02.OddGL2NormalizerExclusion
import Submission.OddOrder.BG.Section02.OddGL2SubgroupInduction

/-!
The normal-Sylow reduction in `BGsection2.der1_odd_GL2_charf`.

For a prime dividing the ambient commutator, the proper-normalizer branch is
incompatible with the strong induction hypothesis.  Hence the selected Sylow
subgroup is normal in the ambient group.
-/

namespace Submission.OddOrder.BG.Section02

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Semiring F] [Group G] [Finite G] [AddCommMonoid V] [Module F V]

/-- A Sylow `q`-subgroup is normal when `q` divides the ambient commutator and
the smaller odd faithfully represented groups have `p`-primary commutator. -/
theorem sylow_normalizer_eq_top_of_card_induction
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hodd : Odd (Nat.card G)) (hpq : p ≠ q) (Q : Sylow q G)
    (hqcomm : q ∣ Nat.card (_root_.commutator G))
    (ih : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → Odd (Nat.card K) →
      (sigma : Representation F K V) → Function.Injective sigma →
      IsPGroup p (_root_.commutator K)) :
    Subgroup.normalizer (Q : Set G) = ⊤ := by
  by_contra hproper
  have hnormalizer :
      IsPGroup p (_root_.commutator (Subgroup.normalizer (Q : Set G))) :=
    normalizer_commutator_isPGroup_of_card_induction
      rho hrho hodd Q hproper ih
  exact (not_dvd_card_commutator_of_normalizer_commutator_isPGroup
    Q hnormalizer hpq) hqcomm

end Submission.OddOrder.BG.Section02
