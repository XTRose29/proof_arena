import Submission.OddOrder.MathlibSupport.LinearEquivConjugationEquiv

/-!
Conjugation rank drops constructed directly from free cyclic orbit vectors.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {V : Type v} {J : Type w}
variable [Field k] [AddCommGroup V] [Module k V]

/-- Independent endomorphism orbits shifted freely by inverse conjugation
produce the exact primitive-root eigenspace rank drop once the scalar line,
orbit span, and ambient dimension are tight. -/
theorem primitiveRoot_conjugation_rank_drop_of_cyclic_orbits
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [FiniteDimensional k V] [Nontrivial V]
    [Fintype J]
    (f : V ≃ₗ[k] V)
    (orbit : J -> ZMod h -> Module.End k V)
    (horbit_independent :
      LinearIndependent k
        (fun p : J × ZMod h => orbit p.1 p.2))
    (hshift : ∀ j t,
      linearEquivConjugation f (orbit j t) = orbit j (t + 1))
    (hone_not_mem :
      (1 : Module.End k V) ∉
        indexedWeightBlock (k := k)
          (cyclicOrbitFourierFamily homega orbit) 0)
    (hspan :
      endomorphismScalarLine (k := k) (V := V) ⊔
        Submodule.span k
          (Set.range
            (fun p : J × ZMod h => orbit p.1 p.2)) = ⊤)
    (hambient :
      Module.finrank k (Module.End k V) = h * Fintype.card J + 1) :
    ∀ m : ZMod h, m ≠ 0 ->
      Module.finrank k
          (Module.End.eigenspace (linearEquivConjugation f)
            (primitiveRootUnitWeight homega 0 : k)) =
        Module.finrank k
            (Module.End.eigenspace (linearEquivConjugation f)
              (primitiveRootUnitWeight homega m : k)) + 1 := by
  apply primitiveRoot_conjugation_rank_drop_of_independent_vectors homega f
    (cyclicOrbitFourierFamily homega orbit)
  · exact cyclicOrbitFourierFamily_global_linearIndependent
      homega orbit horbit_independent
  · intro i j
    rw [Module.End.mem_eigenspace_iff]
    exact linearEquiv_apply_cyclicOrbitFourierFamily homega orbit
      (linearEquivConjugationEquiv f) (fun j t => hshift j t) i j
  · exact hone_not_mem
  · rw [span_cyclicOrbitFourierFamily_global_eq
      homega orbit horbit_independent]
    exact hspan
  · exact hambient

end Submission.OddOrder.MathlibSupport
