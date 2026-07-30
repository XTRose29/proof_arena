import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
Functoriality of elementary-abelian cardinal rank under embeddings.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {p n : ℕ} {E : Subgroup G}

/-- An injective group homomorphism preserves elementary-abelian cardinal
rank. -/
theorem IsElementaryAbelianOfRank.map_of_injective
    (hE : IsElementaryAbelianOfRank p n E)
    (f : G →* H) (hf : Function.Injective f) :
    IsElementaryAbelianOfRank p n (E.map f) := by
  refine
    { isPGroup := hE.isPGroup.map f
      commutative := ?_
      pow_eq_one := ?_
      card_eq := ?_ }
  · letI : IsMulCommutative E := hE.commutative
    infer_instance
  · rintro ⟨x, y, hy, rfl⟩
    apply Subtype.ext
    have hyPow := hE.pow_eq_one ⟨y, hy⟩
    have hyPow' := congrArg f (congrArg Subtype.val hyPow)
    simpa using hyPow'
  · calc
      Nat.card (E.map f) = Nat.card E :=
        Subgroup.card_map_of_injective hf
      _ = p ^ n := hE.card_eq

end Submission.OddOrder.MathlibSupport
