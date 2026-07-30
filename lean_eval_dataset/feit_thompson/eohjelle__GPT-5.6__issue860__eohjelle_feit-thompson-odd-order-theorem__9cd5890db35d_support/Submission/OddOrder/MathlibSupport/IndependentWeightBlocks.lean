import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Submission.OddOrder.MathlibSupport.CyclicOrbitFourierBasis

/-!
Equal-rank blocks obtained by grouping an independent finite family by weight.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w x

variable {k : Type u} {W : Type v} {I : Type w} {J : Type x}
variable [Field k] [AddCommGroup W] [Module k W]

/-- The span of all vectors carrying one fixed weight. -/
def indexedWeightBlock (v : I -> J -> W) (i : I) : Submodule k W :=
  Submodule.span k (Set.range (v i))

/-- A slice of a globally independent rectangular family is independent. -/
theorem linearIndependent_weight_slice
    (v : I -> J -> W)
    (hv : LinearIndependent k (fun p : I × J => v p.1 p.2))
    (i : I) :
    LinearIndependent k (v i) := by
  change LinearIndependent k
    ((fun p : I × J => v p.1 p.2) ∘ fun j : J => (i, j))
  exact hv.comp (fun j : J => (i, j)) (by
    intro a b hab
    exact congrArg Prod.snd hab)

/-- Every block cut from a globally independent rectangular family has rank
equal to the number of vectors in that weight. -/
theorem finrank_indexedWeightBlock
    [Fintype J] (v : I -> J -> W)
    (hv : LinearIndependent k (fun p : I × J => v p.1 p.2))
    (i : I) :
    Module.finrank k (indexedWeightBlock (k := k) v i) = Fintype.card J := by
  exact finrank_span_eq_card (linearIndependent_weight_slice v hv i)

/-- Pointwise containment of weighted vectors in a submodule family extends
to containment of their blocks. -/
theorem indexedWeightBlock_le
    (v : I -> J -> W) (E : I -> Submodule k W)
    (hvE : ∀ i j, v i j ∈ E i) (i : I) :
    indexedWeightBlock (k := k) v i ≤ E i := by
  rw [indexedWeightBlock, Submodule.span_le]
  rintro x ⟨j, rfl⟩
  exact hvE i j

/-- Grouping a rectangular family into weight blocks does not change its
total span. -/
theorem iSup_indexedWeightBlock
    (v : I -> J -> W) :
    ⨆ i, indexedWeightBlock (k := k) v i =
      Submodule.span k (Set.range (fun p : I × J => v p.1 p.2)) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    rw [indexedWeightBlock, Submodule.span_le]
    rintro x ⟨j, rfl⟩
    exact Submodule.subset_span ⟨(i, j), rfl⟩
  · rw [Submodule.span_le]
    rintro x ⟨p, rfl⟩
    exact (le_iSup (indexedWeightBlock (k := k) v) p.1)
      (Submodule.subset_span ⟨p.2, rfl⟩)

/-- A distinguished line and all weight blocks span whenever the line and
the underlying rectangular family span. -/
theorem sup_iSup_indexedWeightBlock_eq_top
    (v : I -> J -> W) (L : Submodule k W)
    (hspan : L ⊔ Submodule.span k
      (Set.range (fun p : I × J => v p.1 p.2)) = ⊤) :
    L ⊔ ⨆ i, indexedWeightBlock (k := k) v i = ⊤ := by
  rw [iSup_indexedWeightBlock]
  exact hspan

end Submission.OddOrder.MathlibSupport
