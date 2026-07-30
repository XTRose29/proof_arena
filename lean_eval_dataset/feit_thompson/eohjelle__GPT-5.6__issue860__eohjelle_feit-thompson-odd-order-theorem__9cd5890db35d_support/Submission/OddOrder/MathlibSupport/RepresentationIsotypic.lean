import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RepresentationTheory.Irreducible
import Submission.OddOrder.MathlibSupport.SubrepresentationModuleEquiv

/-!
Isotypic representations and a finite semisimple spanning criterion.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- A representation is isotypic when all of its simple subrepresentations
are mutually equivalent. -/
def IsRepresentationIsotypic (rho : Representation k G V) : Prop :=
  ∀ U W : Subrepresentation rho,
    Representation.IsIrreducible U.toRepresentation →
    Representation.IsIrreducible W.toRepresentation →
    Nonempty (Representation.Equiv U.toRepresentation W.toRepresentation)

/-- In a semisimple representation, every simple subrepresentation is
equivalent to a member of any finite simple family whose supremum is top. -/
theorem exists_equiv_finset_of_sup_eq_top
    (rho : Representation k G V)
    [IsSemisimpleModule k[G] rho.asModule]
    (W : Subrepresentation rho)
    (hW : Representation.IsIrreducible W.toRepresentation)
    (s : Finset (Subrepresentation rho))
    (hsimple : ∀ X ∈ s, Representation.IsIrreducible X.toRepresentation)
    (hsup : s.sup id = ⊤) :
    ∃ X ∈ s, Nonempty (Representation.Equiv W.toRepresentation X.toRepresentation) := by
  classical
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := rho)
  let t : Finset (Submodule k[G] rho.asModule) := s.image e
  have htsup : t.sup id = ⊤ := by
    change (s.image e).sup id = ⊤
    rw [Finset.sup_image]
    change s.sup e = ⊤
    have hmap := map_finset_sup e s id
    calc
      s.sup e = e (s.sup id) := by
        exact hmap.symm
      _ = ⊤ := by rw [hsup, e.map_top]
  have htsSup : sSup (t : Set (Submodule k[G] rho.asModule)) = ⊤ := by
    rw [← Finset.sup_id_eq_sSup]
    exact htsup
  letI (m : (t : Set (Submodule k[G] rho.asModule))) :
      IsSimpleModule k[G] m.1 := by
    obtain ⟨X, hXs, hXm⟩ := Finset.mem_image.mp m.2
    letI : Representation.IsIrreducible X.toRepresentation := hsimple X hXs
    rw [← hXm]
    exact (irreducible_toRepresentation_iff_isSimpleModule_asSubmodule
      rho X).mp inferInstance
  letI : Representation.IsIrreducible W.toRepresentation := hW
  letI : IsSimpleModule k[G] W.asSubmodule :=
    (irreducible_toRepresentation_iff_isSimpleModule_asSubmodule
      rho W).mp inferInstance
  obtain ⟨m, hm, ⟨em⟩⟩ :=
    W.asSubmodule.linearEquiv_of_sSup_eq_top (s := (t : Set _)) htsSup
  obtain ⟨X, hXs, hXm⟩ := Finset.mem_image.mp hm
  subst m
  refine ⟨X, hXs, ?_⟩
  exact (nonempty_subrepresentationEquiv_iff_nonempty_submoduleEquiv
    rho W X).mpr ⟨em⟩

end Submission.OddOrder.MathlibSupport
