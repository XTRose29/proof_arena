import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Submission.OddOrder.MathlibSupport.RepresentationBurnsideDensity

/-!
# An index bound for irreducible representations

If a subgroup acts by scalars on an irreducible representation, then the
square of the representation degree is bounded by the subgroup index.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {T : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [Group T] [Finite T]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- If every element of a subgroup acts by a scalar in an irreducible
representation, then the square of the representation degree is at most the
subgroup index. -/
theorem Representation.IsIrreducible.finrank_sq_le_index_of_scalar_subgroup
    (rho : Representation k T V) [Representation.IsIrreducible rho]
    (D : Subgroup T)
    (hscalar : ∀ d : D, ∃ c : k,
      rho (d : T) = c • (1 : Module.End k V)) :
    Module.finrank k V ^ 2 ≤ D.index := by
  classical
  letI := Fintype.ofFinite (T ⧸ D)
  let representative : T ⧸ D → T := fun x ↦ Quotient.out x
  let S : Submodule k (Module.End k V) :=
    Submodule.span k (Set.range fun x : T ⧸ D ↦ rho (representative x))
  have hrepresented (g : T) : rho g ∈ S := by
    let x : T ⧸ D := QuotientGroup.mk g
    have hx : (representative x)⁻¹ * g ∈ D := by
      apply QuotientGroup.eq.mp
      exact Quotient.out_eq' x
    let d : D := ⟨(representative x)⁻¹ * g, hx⟩
    have hg : g = representative x * (d : T) := by
      simp [d]
    obtain ⟨c, hc⟩ := hscalar d
    rw [hg, rho.map_mul, hc]
    simpa only [mul_smul_comm, mul_one] using
      S.smul_mem c (Submodule.subset_span ⟨x, rfl⟩)
  have halgebra (a : k[T]) : rho.asAlgebraHom a ∈ S := by
    induction a using MonoidAlgebra.induction_on with
    | hM g =>
        simpa using hrepresented g
    | hadd a b ha hb =>
        simpa only [map_add] using S.add_mem ha hb
    | hsmul c a ha =>
        simpa only [map_smul] using S.smul_mem c ha
  have hspan : S = ⊤ := by
    apply top_unique
    intro f _
    obtain ⟨a, rfl⟩ :=
      Representation.IsIrreducible.asAlgebraHom_surjective rho f
    exact halgebra a
  have hEndLe :
      Module.finrank k (Module.End k V) ≤ Fintype.card (T ⧸ D) := by
    have hfinrank := finrank_span_le_card (R := k)
      (M := Module.End k V)
      (Set.range fun x : T ⧸ D ↦ rho (representative x))
    change Module.finrank k S ≤ _ at hfinrank
    rw [hspan, finrank_top] at hfinrank
    exact hfinrank.trans (by
      rw [Set.toFinset_card]
      exact Fintype.card_range_le _)
  have hEnd : Module.finrank k (Module.End k V) =
      Module.finrank k V * Module.finrank k V := by
    exact Module.finrank_linearMap k k V V
  rw [pow_two, ← hEnd, D.index_eq_card, Nat.card_eq_fintype_card]
  exact hEndLe

end Submission.OddOrder.MathlibSupport
