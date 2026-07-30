import Submission.OddOrder.MathlibSupport.SCNCentralizer

/-!
Injective functoriality of self-centralizing normal abelian subgroups.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

namespace IsSCN

/-- SCN data transports along an injective group homomorphism. -/
theorem map_of_injective
    {G : Type u} {H : Type v} [Group G] [Group H]
    {P A : Subgroup G} (h : IsSCN P A)
    (f : G →* H) (hf : Function.Injective f) :
    IsSCN (P.map f) (A.map f) := by
  refine
    { le_sylow := Subgroup.map_mono h.le_sylow
      le_normalizer :=
        (Subgroup.map_mono h.le_normalizer).trans
          (Subgroup.le_normalizer_map (H := A) f)
      commutative := ?_
      centralizerWithin_eq := ?_ }
  · letI : IsMulCommutative A := h.commutative
    exact Subgroup.map_isMulCommutative A f
  · apply le_antisymm
    · rintro y hy
      rcases hy.1 with ⟨x, hxP, rfl⟩
      have hxComm : ∀ a ∈ A, a * x = x * a := by
        intro a ha
        apply hf
        simpa using hy.2 (f a) ⟨a, ha, rfl⟩
      have hxC : x ∈ centralizerWithin P A := ⟨hxP, hxComm⟩
      exact ⟨x, h.centralizerWithin_eq ▸ hxC, rfl⟩
    · rintro y ⟨a, ha, rfl⟩
      refine ⟨⟨a, h.le_sylow ha, rfl⟩, ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      have haC : a ∈ centralizerWithin P A :=
        h.centralizerWithin_eq.symm ▸ ha
      simpa using congrArg f (haC.2 b hb)

end IsSCN

end Submission.OddOrder.MathlibSupport
