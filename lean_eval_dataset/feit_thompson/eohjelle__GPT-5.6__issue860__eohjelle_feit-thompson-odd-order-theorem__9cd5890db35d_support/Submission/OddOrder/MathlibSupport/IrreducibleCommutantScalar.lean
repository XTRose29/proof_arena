import Mathlib.RepresentationTheory.Irreducible

/-!
Scalar endomorphisms in the commutant of an irreducible representation.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [Group G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- An endomorphism commuting with every represented group element is scalar
on a finite-dimensional irreducible representation over an algebraically
closed field. -/
theorem exists_eq_smul_one_of_commute_irreducible
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (T : Module.End k V)
    (hT : ∀ g : G, Commute T (rho g)) :
    ∃ c : k, T = c • (1 : Module.End k V) := by
  let f : Representation.IntertwiningMap rho rho :=
    { toLinearMap := T
      isIntertwining' := fun g ↦ by
        ext v
        exact DFunLike.congr_fun (hT g).eq v }
  obtain ⟨c, hc⟩ :=
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      |>.2 f
  refine ⟨c, ?_⟩
  ext v
  have hv := congrArg
    (fun q : Representation.IntertwiningMap rho rho ↦ q v) hc
  simpa [f] using hv.symm

end Submission.OddOrder.MathlibSupport
