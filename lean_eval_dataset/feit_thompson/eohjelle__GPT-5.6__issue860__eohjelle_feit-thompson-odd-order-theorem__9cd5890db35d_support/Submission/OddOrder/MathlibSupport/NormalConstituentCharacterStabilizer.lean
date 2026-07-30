import Submission.OddOrder.MathlibSupport.IrreducibleCharacterRigidity
import Submission.OddOrder.MathlibSupport.NormalConstituentTwistEquiv
import Submission.OddOrder.MathlibSupport.RepresentationAutomorphismTwist

/-!
The Clifford inertia subgroup stabilizing the character, equivalently the
isomorphism class, of a simple normal-restriction constituent.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Ambient inverse conjugation acts on functions on a normal subgroup. -/
@[reducible]
def normalConjugationFunctionMulAction
    (N : Subgroup G) [N.Normal] : MulAction G (N → k) where
  smul g f n := f ((MulAut.conjNormal g).symm n)
  one_smul f := by
    funext n
    change f ((MulAut.conjNormal 1).symm n) = f n
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_symm_apply]
    simp
  mul_smul g h f := by
    funext n
    change f ((MulAut.conjNormal (g * h)).symm n) =
      f ((MulAut.conjNormal h).symm ((MulAut.conjNormal g).symm n))
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_symm_apply, MulAut.conjNormal_symm_apply,
      MulAut.conjNormal_symm_apply]
    group

/-- The inertia subgroup stabilizing the ordinary character of a normal
constituent. -/
noncomputable def normalConstituentCharacterStabilizer
    [FiniteDimensional k V]
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) : Subgroup G := by
  letI := normalConjugationFunctionMulAction (k := k) N
  exact MulAction.stabilizer G (Representation.character U.toRepresentation)

theorem mem_normalConstituentCharacterStabilizer_iff
    [FiniteDimensional k V]
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) (g : G) :
    g ∈ normalConstituentCharacterStabilizer rho N U ↔
      ∀ n : N, U.toRepresentation.character ((MulAut.conjNormal g).symm n) =
        U.toRepresentation.character n := by
  change
    (fun n ↦ U.toRepresentation.character ((MulAut.conjNormal g).symm n)) =
        U.toRepresentation.character ↔ _
  exact ⟨fun h n ↦ congrFun h n, fun h ↦ funext h⟩

/-- Inner conjugation by `N` fixes every constituent character. -/
theorem normal_le_normalConstituentCharacterStabilizer
    [FiniteDimensional k V]
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) :
    N ≤ normalConstituentCharacterStabilizer rho N U := by
  intro g hg
  rw [mem_normalConstituentCharacterStabilizer_iff]
  let x : N := ⟨g, hg⟩
  intro n
  have harg : (MulAut.conjNormal g).symm n = x⁻¹ * n * x := by
    apply Subtype.ext
    simp [x]
  rw [harg]
  simpa using U.toRepresentation.char_conj n x⁻¹

/-- For a finite simple constituent in characteristic zero, character inertia
is exactly invariance of its representation isomorphism class. -/
theorem mem_normalConstituentCharacterStabilizer_iff_nonempty_equiv_twist
    [IsAlgClosed k] [CharZero k] [Finite G] [FiniteDimensional k V]
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible U.toRepresentation] (g : G) :
    g ∈ normalConstituentCharacterStabilizer rho N U ↔
      Nonempty (Representation.Equiv U.toRepresentation
        (U.toRepresentation.comp (MulAut.conjNormal g).symm.toMonoidHom)) := by
  let twist : Representation k N U.toSubmodule :=
    U.toRepresentation.comp (MulAut.conjNormal g).symm.toMonoidHom
  letI : Representation.IsIrreducible twist :=
    representation_irreducible_comp_mulAut U.toRepresentation
      (MulAut.conjNormal g).symm
  constructor
  · intro hg
    apply nonempty_representationEquiv_of_irreducible_character_eq
    funext n
    rw [representation_comp_mulAut_character]
    exact (mem_normalConstituentCharacterStabilizer_iff rho N U g).mp hg n |>.symm
  · rintro ⟨e⟩
    rw [mem_normalConstituentCharacterStabilizer_iff]
    have hchar := Representation.char_iso e
    intro n
    have hn := congrFun hchar n
    rw [representation_comp_mulAut_character] at hn
    exact hn.symm

/-- Equivalently, character inertia means that the original constituent is
isomorphic to the representation on its translated subspace. -/
theorem mem_normalConstituentCharacterStabilizer_iff_nonempty_equiv_translate
    [IsAlgClosed k] [CharZero k] [Finite G] [FiniteDimensional k V]
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible U.toRepresentation] (g : G) :
    g ∈ normalConstituentCharacterStabilizer rho N U ↔
      Nonempty (Representation.Equiv U.toRepresentation
        (conjugateNormalSubrepresentation rho N g U).toRepresentation) := by
  rw [mem_normalConstituentCharacterStabilizer_iff_nonempty_equiv_twist]
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans (normalConstituentTwistEquiv rho N g U)⟩
  · rintro ⟨e⟩
    exact ⟨e.trans (normalConstituentTwistEquiv rho N g U).symm⟩

end Submission.OddOrder.MathlibSupport
