import Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.Frattini
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
Submodules of an elementary abelian group as multiplicative subgroups.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- `ZMod p`-submodules of the additive form of an elementary abelian group
are exactly its subgroups. -/
def elementaryAbelianGroupSubmoduleSubgroupOrderIso
    (G : Type*) [Group G] (p : ℕ) [IsMulCommutative G]
    [Module (ZMod p) (Additive G)] :
    Submodule (ZMod p) (Additive G) ≃o Subgroup G :=
  (AddSubgroup.toZModSubmodule p).symm.trans AddSubgroup.toSubgroup'

/-- An elementary abelian group, presented with its canonical prime-field
module structure, has trivial Frattini subgroup. -/
theorem frattini_eq_bot_of_elementaryAbelianModule
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    [IsMulCommutative G] [Module (ZMod p) (Additive G)] :
    frattini G = ⊥ := by
  classical
  let e := elementaryAbelianGroupSubmoduleSubgroupOrderIso G p
  apply le_bot_iff.mp
  intro x hx
  apply Subgroup.mem_bot.mpr
  by_contra hxone
  let v : Additive G := Additive.ofMul x
  have hv : v ∉ (⊥ : Submodule (ZMod p) (Additive G)) := by
    simpa [v] using hxone
  obtain ⟨f, hfv, _⟩ := Submodule.exists_le_ker_of_notMem
    (K := ZMod p) (V := Additive G) hv
  have hker : IsCoatom (LinearMap.ker f) := by
    rw [isCoatom_iff_ge_of_le]
    constructor
    · intro htop
      apply hfv
      rw [← LinearMap.mem_ker, htop]
      trivial
    · intro W hWtop hkerW
      intro w hw
      by_contra hwker
      apply hWtop
      apply top_unique
      intro z _hz
      let c : ZMod p := f z / f w
      have hfw : f w ≠ 0 := by
        intro hzero
        apply hwker
        exact LinearMap.mem_ker.mpr hzero
      have hdiff : z - c • w ∈ LinearMap.ker f := by
        rw [LinearMap.mem_ker, map_sub, map_smul]
        change f z - c * f w = 0
        rw [show c * f w = f z by
          dsimp [c]
          exact div_mul_cancel₀ (f z) hfw, sub_self]
      have hcw : c • w ∈ W := W.smul_mem c hw
      have hzEq : z = (z - c • w) + c • w := by abel
      rw [hzEq]
      exact W.add_mem (hkerW hdiff) hcw
  let H : Subgroup G := e (LinearMap.ker f)
  have hH : IsCoatom H := (e.isCoatom_iff (LinearMap.ker f)).mpr hker
  have hxH : x ∈ H := frattini_le_coatom hH hx
  have hvker : v ∈ LinearMap.ker f := by exact hxH
  exact hfv (LinearMap.mem_ker.mp hvker)

/-- `ZMod p`-submodules of `Additive E` are exactly subgroups of `E`. -/
def elementaryAbelianSubmoduleSubgroupOrderIso
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)] :
    Submodule (ZMod p) (Additive E) ≃o Subgroup E :=
  (AddSubgroup.toZModSubmodule p).symm.trans AddSubgroup.toSubgroup'

@[simp]
theorem mem_elementaryAbelianSubmoduleSubgroupOrderIso
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    (W : Submodule (ZMod p) (Additive E)) (x : E) :
    x ∈ elementaryAbelianSubmoduleSubgroupOrderIso E p W ↔
      Additive.ofMul x ∈ W :=
  Iff.rfl

@[simp]
theorem elementaryAbelianSubmoduleSubgroupOrderIso_bot
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)] :
    elementaryAbelianSubmoduleSubgroupOrderIso E p ⊥ = ⊥ :=
  (elementaryAbelianSubmoduleSubgroupOrderIso E p).map_bot

@[simp]
theorem elementaryAbelianSubmoduleSubgroupOrderIso_top
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)] :
    elementaryAbelianSubmoduleSubgroupOrderIso E p ⊤ = ⊤ :=
  (elementaryAbelianSubmoduleSubgroupOrderIso E p).map_top

end Submission.OddOrder.MathlibSupport
