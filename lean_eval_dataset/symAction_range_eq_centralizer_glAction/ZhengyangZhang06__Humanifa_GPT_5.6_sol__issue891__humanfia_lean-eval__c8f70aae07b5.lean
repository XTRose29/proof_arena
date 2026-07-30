import Submission.DoubleCentralizer
import Submission.FirstCentralizer
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Data.Fintype.Card

open LeanEval.RepresentationTheory
open scoped TensorProduct

namespace Submission

open FirstCentralizer DoubleCentralizer

private theorem centralizer_adjoin
    {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (s : Set A) :
    Subalgebra.centralizer R (Algebra.adjoin R s : Set A) =
      Subalgebra.centralizer R s := by
  apply le_antisymm
  · exact Subalgebra.centralizer_le R s (Algebra.adjoin R s) Algebra.subset_adjoin
  · intro z hz
    apply (Subalgebra.mem_centralizer_iff R).2
    intro y hy
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun x hx ↦
      ((Subalgebra.mem_centralizer_iff R).1 hz x hx).symm).symm

theorem symAction_range_eq_centralizer_glAction {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {k : ℕ} [Invertible (k.factorial : R)] :
    Algebra.adjoin R (Set.range (symAction R M k)) =
      Subalgebra.centralizer R (Set.range (glAction R M k)) := by
  letI : NeZero (Nat.card (Equiv.Perm (Fin k)) : R) :=
    ⟨by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using
        (isUnit_of_invertible (k.factorial : R)).ne_zero⟩
  calc
    Algebra.adjoin R (Set.range (symAction R M k)) =
        Subalgebra.centralizer R
          (Subalgebra.centralizer R (Set.range (symAction R M k)) :
            Set (Module.End R (⨂[R]^k M))) :=
      adjoin_range_eq_doubleCentralizer (symAction R M k)
    _ = Subalgebra.centralizer R
          (Algebra.adjoin R (Set.range (glAction R M k)) :
            Set (Module.End R (⨂[R]^k M))) := by
      rw [glAction_adjoin_eq_symAction_centralizer R M k]
    _ = Subalgebra.centralizer R (Set.range (glAction R M k)) :=
      centralizer_adjoin _

end Submission
