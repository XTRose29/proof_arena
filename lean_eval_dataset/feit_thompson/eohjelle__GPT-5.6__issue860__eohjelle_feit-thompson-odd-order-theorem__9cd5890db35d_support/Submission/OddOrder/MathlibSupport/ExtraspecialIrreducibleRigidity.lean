import Submission.OddOrder.MathlibSupport.ExtraspecialIrreducibleDegree
import Submission.OddOrder.MathlibSupport.IrreducibleCharacterRigidity

/-!
Rigidity of faithful irreducible representations of extraspecial groups under
restriction to the center.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w x

variable {k : Type u} {G : Type v} {V : Type w} {W : Type x}
variable [Field k] [IsAlgClosed k] [CharZero k]
variable [Group G] [Finite G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]
variable {p n : ℕ} [Fact p.Prime]

namespace IsExtraspecial

/-- A faithful irreducible extraspecial representation is determined, up to
equivalence, by its scalar character on the center. Faithfulness of the second
representation follows from equality of the center characters. -/
theorem nonempty_equiv_of_schurCenterScalarCharacter_eq
    (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (hcard : Nat.card G = p ^ (2 * n + 1))
    (rho : Representation k G V) (sigma : Representation k G W)
    [Representation.IsIrreducible rho]
    [Representation.IsIrreducible sigma]
    (hrho : Function.Injective rho)
    (hcenter : schurCenterScalarCharacter rho =
      schurCenterScalarCharacter sigma) :
    Nonempty (rho.Equiv sigma) := by
  have hscalarRho :
      Function.Injective (schurCenterScalarCharacter rho) :=
    (IsPGroup.representation_injective_iff_schurCenterScalarCharacter rho hpG).mp hrho
  have hscalarSigma :
      Function.Injective (schurCenterScalarCharacter sigma) := by
    intro z w hzw
    apply hscalarRho
    rw [hcenter]
    exact hzw
  have hsigma : Function.Injective sigma :=
    (IsPGroup.representation_injective_iff_schurCenterScalarCharacter sigma hpG).mpr
      hscalarSigma
  have hdegreeRho := hG.faithful_irreducible_finrank_eq hpG hcard rho hrho
  have hdegreeSigma := hG.faithful_irreducible_finrank_eq hpG hcard sigma hsigma
  apply nonempty_representationEquiv_of_irreducible_character_eq rho sigma
  funext g
  by_cases hg : g ∈ Subgroup.center G
  · let z : Subgroup.center G := ⟨g, hg⟩
    rw [show rho.character g = rho.character z from rfl,
      show sigma.character g = sigma.character z from rfl,
      character_center_eq_finrank_mul_schurCenterScalarCharacter rho z,
      character_center_eq_finrank_mul_schurCenterScalarCharacter sigma z,
      hdegreeRho, hdegreeSigma]
    exact congrArg (fun c : k ↦ ((p ^ n : ℕ) : k) * c)
      (congrArg Units.val (DFunLike.congr_fun hcenter z))
  · rw [hG.toIsSpecial.character_eq_zero_of_not_mem_center rho hrho hg,
      hG.toIsSpecial.character_eq_zero_of_not_mem_center sigma hsigma hg]

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
