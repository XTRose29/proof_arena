import Submission.OddOrder.BG.Section02.DerivedSylowPart
import Submission.OddOrder.MathlibSupport.PGroupCommutatorProper

/-!
Strictness of the derived-Sylow intersection in the noncommutative branch of
`BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- If the derived-Sylow part has nontrivial commutator, then it is a proper
subgroup of the ambient group. -/
theorem derivedSylowPart_ne_top_of_commutator_ne_bot
    {q : ℕ} [Fact q.Prime] (Q : Sylow q G)
    (hcomm : _root_.commutator (derivedSylowPart Q) ≠ ⊥) :
    derivedSylowPart Q ≠ ⊤ := by
  have hpart_ne_bot : derivedSylowPart Q ≠ ⊥ := by
    intro hbot
    apply hcomm
    apply (_root_.commutator_eq_bot_iff (derivedSylowPart Q)).mpr
    exact ⟨⟨fun a b => by
      apply Subtype.ext
      have ha : (a : G) = 1 := by
        have : (a : G) ∈ (⊥ : Subgroup G) := by
          rw [← hbot]
          exact a.2
        simpa using this
      have hb : (b : G) = 1 := by
        have : (b : G) ∈ (⊥ : Subgroup G) := by
          rw [← hbot]
          exact b.2
        simpa using this
      simp [ha, hb]⟩⟩
  letI : Nontrivial (derivedSylowPart Q) :=
    (Subgroup.nontrivial_iff_ne_bot (derivedSylowPart Q)).mpr hpart_ne_bot
  letI : Nontrivial G :=
    Function.Injective.nontrivial (derivedSylowPart Q).subtype_injective
  intro htop
  have hQtop : (Q : Subgroup G) = ⊤ := by
    apply top_unique
    rw [← htop]
    exact derivedSylowPart_le_sylow Q
  have htopP : IsPGroup q (⊤ : Subgroup G) := by
    rw [← hQtop]
    exact Q.isPGroup'
  have hGp : IsPGroup q G := htopP.of_equiv Subgroup.topEquiv
  apply commutator_ne_top_of_isPGroup hGp
  apply top_unique
  rw [← htop]
  exact derivedSylowPart_le_commutator Q

end Submission.OddOrder.BG.Section02
