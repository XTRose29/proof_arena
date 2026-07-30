import Mathlib.RepresentationTheory.Character

/-!
Representations twisted by automorphisms of the acting group.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Precomposition by a group automorphism preserves faithfulness. -/
theorem representation_comp_mulAut_injective_iff
    (rho : Representation k G V) (a : MulAut G) :
    Function.Injective (rho.comp a.toMonoidHom) ↔ Function.Injective rho := by
  constructor
  · intro h x y hxy
    apply a.symm.injective
    apply h
    simpa using hxy
  · intro h
    exact h.comp a.injective

/-- Twisting a representation composes its character with the automorphism. -/
theorem representation_comp_mulAut_character
    [FiniteDimensional k V] (rho : Representation k G V)
    (a : MulAut G) (g : G) :
    Representation.character
        (rho.comp a.toMonoidHom : Representation k G V) g =
      Representation.character rho (a g) :=
  rfl

/-- Precomposition by a group automorphism preserves irreducibility. -/
theorem representation_irreducible_comp_mulAut
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (a : MulAut G) :
    Representation.IsIrreducible (rho.comp a.toMonoidHom) := by
  let twist : Representation k G V := rho.comp a.toMonoidHom
  have hbot_ne_top :
      (⊥ : Subrepresentation twist) ≠ ⊤ := by
    intro h
    apply IsSimpleOrder.bot_ne_top (α := Subrepresentation rho)
    apply SetLike.ext
    intro v
    have hv := congrArg (fun U : Subrepresentation twist ↦ v ∈ U) h
    change (v ∈ (⊥ : Submodule k V)) = (v ∈ (⊤ : Submodule k V)) at hv
    change v ∈ (⊥ : Submodule k V) ↔ v ∈ (⊤ : Submodule k V)
    exact iff_of_eq hv
  letI : Nontrivial (Subrepresentation twist) :=
    ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
  refine IsSimpleOrder.of_forall_eq_top fun U hU ↦ ?_
  let U' : Subrepresentation rho :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule g v hv := by
        obtain ⟨g, rfl⟩ := a.surjective g
        exact U.apply_mem_toSubmodule g hv }
  have hU' : U' ≠ ⊥ := by
    intro hbot
    apply hU
    apply SetLike.ext
    intro v
    have hv := congrArg (fun W : Subrepresentation rho ↦ v ∈ W) hbot
    change (v ∈ U.toSubmodule) = (v ∈ (⊥ : Submodule k V)) at hv
    change v ∈ U.toSubmodule ↔ v ∈ (⊥ : Submodule k V)
    exact iff_of_eq hv
  have htop : U' = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'
  apply SetLike.ext
  intro v
  have hv := congrArg (fun W : Subrepresentation rho ↦ v ∈ W) htop
  change (v ∈ U.toSubmodule) = (v ∈ (⊤ : Submodule k V)) at hv
  change v ∈ U.toSubmodule ↔ v ∈ (⊤ : Submodule k V)
  exact iff_of_eq hv

end Submission.OddOrder.MathlibSupport
