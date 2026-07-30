import Submission.OddOrder.MathlibSupport.OmegaOne
import Mathlib.GroupTheory.PGroup

/-!
Functoriality and characteristicity of the first omega subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {K : Type v} [Group G] [Group K]

theorem map_omegaOne_le (p : ℕ) (f : G →* K) :
    (omegaOne p G).map f ≤ omegaOne p K := by
  rw [omegaOne, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨x, hx, rfl⟩
  change f x ^ p = 1
  rw [← f.map_pow, hx, f.map_one]

theorem map_omegaOne_equiv (p : ℕ) (e : G ≃* K) :
    (omegaOne p G).map e.toMonoidHom = omegaOne p K := by
  rw [omegaOne, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e x ^ p = 1
    simpa using congrArg e hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change e.symm y ^ p = 1
    simpa using congrArg e.symm hy

/-- The cardinality of the first omega subgroup is invariant under group
equivalence. -/
theorem natCard_omegaOne_eq_of_mulEquiv [Finite G] [Finite K]
    (p : ℕ) (e : G ≃* K) :
    Nat.card (omegaOne p G) = Nat.card (omegaOne p K) := by
  rw [← map_omegaOne_equiv p e]
  exact (Subgroup.card_map_of_injective e.injective).symm

instance omegaOne_characteristic (p : ℕ) : (omegaOne p G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  exact map_omegaOne_equiv p

instance omegaOne_normal (p : ℕ) : (omegaOne p G).Normal :=
  inferInstance

theorem omegaOne_isPGroup (p : ℕ) (hG : IsPGroup p G) :
    IsPGroup p (omegaOne p G) :=
  hG.to_subgroup (omegaOne p G)

end Submission.OddOrder.MathlibSupport
