import Submission.OddOrder.MathlibSupport.EigenspaceBlockRankDrop
import Submission.OddOrder.MathlibSupport.PrimitiveRootConjugationFinrank

/-!
Primitive-root conjugation rank drops from spanning equal-rank blocks.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/-- A scalar line and equal-rank blocks spanning the endomorphism space
force the primitive-root conjugation eigenspace at zero to have rank one
larger than every nonzero eigenspace. -/
theorem primitiveRoot_conjugation_rank_drop_of_blocks
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [FiniteDimensional k V]
    (f : V ≃ₗ[k] V) (c : Nat)
    (B : ZMod h -> Submodule k (Module.End k V))
    (hB_le : ∀ i : ZMod h,
      B i ≤ Module.End.eigenspace (linearEquivConjugation f)
        (primitiveRootUnitWeight homega i : k))
    (hB_rank : ∀ i : ZMod h, Module.finrank k (B i) = c)
    (L : Submodule k (Module.End k V))
    (hL_le : L ≤ Module.End.eigenspace (linearEquivConjugation f)
      (primitiveRootUnitWeight homega 0 : k))
    (hL_rank : Module.finrank k L = 1)
    (hL_disjoint : Disjoint L (B 0))
    (hblocks_span : L ⊔ ⨆ i, B i = ⊤)
    (hambient : Module.finrank k (Module.End k V) = h * c + 1) :
    ∀ m : ZMod h, m ≠ 0 ->
      Module.finrank k
          (Module.End.eigenspace (linearEquivConjugation f)
            (primitiveRootUnitWeight homega 0 : k)) =
        Module.finrank k
            (Module.End.eigenspace (linearEquivConjugation f)
              (primitiveRootUnitWeight homega m : k)) + 1 := by
  let E : ZMod h -> Submodule k (Module.End k V) := fun i =>
    Module.End.eigenspace (linearEquivConjugation f)
      (primitiveRootUnitWeight homega i : k)
  have hB_le' (i : ZMod h) : B i ≤ E i := hB_le i
  have hL_le' : L ≤ E 0 := hL_le
  have hindependent : iSupIndep E := by
    change iSupIndep
      (Module.End.eigenspace (linearEquivConjugation f) ∘
        fun i : ZMod h => (primitiveRootUnitWeight homega i : k))
    exact (Module.End.eigenspaces_iSupIndep
      (linearEquivConjugation f)).comp
        (primitiveRootUnitWeight_val_injective homega)
  have hspan : ⨆ i, E i = ⊤ := by
    apply top_unique
    rw [← hblocks_span]
    apply sup_le
    · exact hL_le'.trans (le_iSup E 0)
    · exact iSup_mono hB_le'
  have hambient' :
      Module.finrank k (Module.End k V) =
        Fintype.card (ZMod h) * c + 1 := by
    simpa using hambient
  obtain ⟨hrank0, hrank⟩ := eigenspace_rank_drop_of_blocks
    (k := k) (W := Module.End k V) (i0 := (0 : ZMod h)) c E B
    hindependent hspan hB_le' hB_rank L hL_le' hL_rank hL_disjoint
    hambient'
  intro m hm
  calc
    Module.finrank k
        (Module.End.eigenspace (linearEquivConjugation f)
          (primitiveRootUnitWeight homega 0 : k)) = c + 1 := hrank0
    _ = Module.finrank k
          (Module.End.eigenspace (linearEquivConjugation f)
            (primitiveRootUnitWeight homega m : k)) + 1 := by
      rw [hrank m hm]

end Submission.OddOrder.MathlibSupport
