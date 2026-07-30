import Submission.OddOrder.BG.Section02.DerivedSylowTranslatedLine
import Submission.OddOrder.MathlibSupport.OddTwoLineAction
import Submission.OddOrder.MathlibSupport.SubgroupModuleAmbientAction

/-!
Ambient elements fix both derived-Sylow eigenlines in
`BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport
open scoped MonoidAlgebra

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- Odd ambient order rules out swapping the two derived-Sylow eigenlines,
so every represented group element fixes both. This is `redG` in the source
proof. -/
theorem derivedSylow_lines_fixed_by_ambient
    {q : ℕ} (hodd : Odd (Nat.card G))
    (rho : Representation F G V) (Q : Sylow q G)
    (hN : (derivedSylowPart Q).Normal)
    (m n : Submodule F[derivedSylowPart Q]
      (derivedSylowRepresentation rho Q).asModule)
    (hmn : IsCompl m n) (x : derivedSylowPart Q) (a b : F)
    (hma : invariantLineAction (derivedSylowRepresentation rho Q) m x =
      a • LinearMap.id)
    (hna : invariantLineAction (derivedSylowRepresentation rho Q) n x =
      b • LinearMap.id)
    (hab : a ≠ b)
    (hmdim : Module.finrank F (m.restrictScalars F) = 1)
    (hndim : Module.finrank F (n.restrictScalars F) = 1) :
    ∀ y : G,
      translateRestrictedInvariantSubspace rho (derivedSylowPart Q) m y =
          m.restrictScalars F ∧
        translateRestrictedInvariantSubspace rho (derivedSylowPart Q) n y =
          n.restrictScalars F := by
  have hmnF : IsCompl (m.restrictScalars F) (n.restrictScalars F) :=
    (Submodule.isCompl_restrictScalars_iff F).mpr hmn
  have hUperm : ∀ y : G,
      (m.restrictScalars F).map
          (subgroupModuleAmbientLinearEquivHom rho
            (derivedSylowPart Q) y).toLinearMap ≤ m.restrictScalars F ∨
        (m.restrictScalars F).map
          (subgroupModuleAmbientLinearEquivHom rho
            (derivedSylowPart Q) y).toLinearMap ≤ n.restrictScalars F := by
    intro y
    change translateRestrictedInvariantSubspace
        rho (derivedSylowPart Q) m y ≤ m.restrictScalars F ∨
      translateRestrictedInvariantSubspace
        rho (derivedSylowPart Q) m y ≤ n.restrictScalars F
    exact derivedSylow_translatedLine_le_left_or_right
      rho Q hN m n m hmn x a b hma hna hab hmdim y
  have hWperm : ∀ y : G,
      (n.restrictScalars F).map
          (subgroupModuleAmbientLinearEquivHom rho
            (derivedSylowPart Q) y).toLinearMap ≤ m.restrictScalars F ∨
        (n.restrictScalars F).map
          (subgroupModuleAmbientLinearEquivHom rho
            (derivedSylowPart Q) y).toLinearMap ≤ n.restrictScalars F := by
    intro y
    change translateRestrictedInvariantSubspace
        rho (derivedSylowPart Q) n y ≤ m.restrictScalars F ∨
      translateRestrictedInvariantSubspace
        rho (derivedSylowPart Q) n y ≤ n.restrictScalars F
    exact derivedSylow_translatedLine_le_left_or_right
      rho Q hN m n n hmn x a b hma hna hab hndim y
  intro y
  have hfix := odd_action_preserves_complementary_lines hodd
    (subgroupModuleAmbientLinearEquivHom rho (derivedSylowPart Q))
    (m.restrictScalars F) (n.restrictScalars F) hmnF hmdim hndim
    hUperm hWperm y
  change translateRestrictedInvariantSubspace
      rho (derivedSylowPart Q) m y = m.restrictScalars F ∧
    translateRestrictedInvariantSubspace
      rho (derivedSylowPart Q) n y = n.restrictScalars F at hfix
  exact hfix

end Submission.OddOrder.BG.Section02
