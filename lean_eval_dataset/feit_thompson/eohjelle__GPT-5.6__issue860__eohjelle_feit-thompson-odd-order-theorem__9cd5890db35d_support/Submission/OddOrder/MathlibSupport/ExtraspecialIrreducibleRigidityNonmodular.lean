import Submission.OddOrder.MathlibSupport.ExtraspecialCharacterVanishing
import Submission.OddOrder.MathlibSupport.ExtraspecialCenterFaithfulness
import Submission.OddOrder.MathlibSupport.IrreducibleCharacterRigidity
import Submission.OddOrder.MathlibSupport.IrreducibleCenterScalarTwist

/-!
Rigidity of faithful extraspecial irreducibles in arbitrary nonmodular
characteristic.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w x

variable {k : Type u} {G : Type v} {V : Type w} {W : Type x}
variable [Field k] [IsAlgClosed k]
variable [Group G] [Finite G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]
variable {p : ℕ} [Fact p.Prime]

namespace IsExtraspecial

/-- In nonmodular characteristic, faithful irreducibles of equal dimension
and with the same scalar center character are equivalent. -/
theorem nonempty_equiv_of_schurCenterScalarCharacter_eq_of_finrank_eq
    (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (rho : Representation k G V) (sigma : Representation k G W)
    [Representation.IsIrreducible rho]
    [Representation.IsIrreducible sigma]
    (hcard : (Nat.card G : k) ≠ 0)
    (hrho : Function.Injective rho)
    (hdegree : Module.finrank k V = Module.finrank k W)
    (hcenter : schurCenterScalarCharacter rho =
      schurCenterScalarCharacter sigma) :
    Nonempty (rho.Equiv sigma) := by
  have hscalarRho :
      Function.Injective (schurCenterScalarCharacter rho) :=
    (IsPGroup.representation_injective_iff_schurCenterScalarCharacter rho hpG).mp hrho
  have hscalarSigma :
      Function.Injective (schurCenterScalarCharacter sigma) := by
    intro z t hzt
    apply hscalarRho
    rw [hcenter]
    exact hzt
  have hsigma : Function.Injective sigma :=
    (IsPGroup.representation_injective_iff_schurCenterScalarCharacter sigma hpG).mpr
      hscalarSigma
  apply nonempty_representationEquiv_of_irreducible_character_eq_of_card_ne_zero
    rho sigma hcard
  funext g
  by_cases hg : g ∈ Subgroup.center G
  · let z : Subgroup.center G := ⟨g, hg⟩
    rw [show rho.character g = rho.character z from rfl,
      show sigma.character g = sigma.character z from rfl,
      character_center_eq_finrank_mul_schurCenterScalarCharacter rho z,
      character_center_eq_finrank_mul_schurCenterScalarCharacter sigma z,
      hdegree]
    exact congrArg (fun c : k ↦ (Module.finrank k W : k) * c)
      (congrArg Units.val (DFunLike.congr_fun hcenter z))
  · rw [hG.toIsSpecial.character_eq_zero_of_not_mem_center rho hrho hg,
      hG.toIsSpecial.character_eq_zero_of_not_mem_center sigma hsigma hg]

/-- A center-fixing automorphism preserves a faithful irreducible
extraspecial representation in every nonmodular characteristic. -/
theorem nonempty_equiv_comp_mulAut_of_fixed_center_of_card_ne_zero
    (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    [Nontrivial V]
    (hcard : (Nat.card G : k) ≠ 0)
    (hrho : Function.Injective rho) (a : MulAut G)
    (hfix : ∀ z : Subgroup.center G, a (z : G) = z) :
    letI : Representation.IsIrreducible
        (rho.comp a.toMonoidHom : Representation k G V) :=
      representation_irreducible_comp_mulAut rho a
    Nonempty (rho.Equiv
      (rho.comp a.toMonoidHom : Representation k G V)) := by
  letI : Representation.IsIrreducible
      (rho.comp a.toMonoidHom : Representation k G V) :=
    representation_irreducible_comp_mulAut rho a
  apply hG.nonempty_equiv_of_schurCenterScalarCharacter_eq_of_finrank_eq
    hpG rho (rho.comp a.toMonoidHom : Representation k G V) hcard hrho rfl
  exact (schurCenterScalarCharacter_comp_mulAut_eq_of_fixed_center
    rho a hfix).symm

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
