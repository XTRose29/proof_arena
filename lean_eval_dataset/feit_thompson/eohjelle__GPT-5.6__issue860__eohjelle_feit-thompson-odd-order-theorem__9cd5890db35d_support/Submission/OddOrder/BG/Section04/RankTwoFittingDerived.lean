import Submission.OddOrder.BG.Section04.RankTwoChiefFactorCentralizer
import Submission.OddOrder.MathlibSupport.ChiefStabilizerFitting

/-!
Bender--Glauberman Theorem 4.20(a).

Every chief factor below the Fitting subgroup has prime-power order.  Under
the rank-two hypothesis, Corollary 4.19 says that the derived subgroup
centralizes each such factor.  Hall's chief-factor stabilizer criterion then
places the derived subgroup inside the Fitting subgroup.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

universe u

/-- `BGsection4.v: rank2_der1_sub_Fitting` (Theorem 4.20(a)). -/
theorem rank2_der1_sub_Fitting
    {G : Type u} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    (hsol : IsSolvable G)
    (hRank : ∀ p : ℕ, p.Prime →
      ¬ ∃ E : Subgroup (fittingCore G),
        IsElementaryAbelianOfRank p 3 E) :
    _root_.commutator G ≤ fittingCore G := by
  letI : IsSolvable G := hsol
  apply normal_le_fittingCore_of_stabilizes_chiefFactors
    (H := _root_.commutator G) (by infer_instance)
  intro V U _ hchief hUF
  obtain ⟨p, hp, hfactor, _hexp⟩ :=
    hchief.exists_prime_isPGroup_pow_eq_one
  letI : Fact p.Prime := ⟨hp⟩
  exact rank2_der1_cent_chief
    (G := G) (p := p) (Gs := fittingCore G) (U := U) (V := V)
    hodd hsol (by infer_instance) (hRank p hp) hchief hfactor hUF

end Submission.OddOrder.BG.Section04
