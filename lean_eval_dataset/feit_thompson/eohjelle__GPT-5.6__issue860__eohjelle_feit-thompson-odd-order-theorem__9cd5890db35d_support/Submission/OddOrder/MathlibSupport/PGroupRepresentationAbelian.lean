import Submission.OddOrder.MathlibSupport.PGroupInvariantQuotient

/-!
Faithful two-dimensional modular representations of finite `p`-groups have
commutative domain.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- In characteristic `p`, the image of a finite `p`-group in a vector space
of dimension at most two is commutative. -/
theorem representation_apply_commute_of_isPGroup_charP_finrank_le_two
    {p : ℕ} [CharP F p] [Fact p.Prime]
    (rho : Representation F G V) (hG : IsPGroup p G)
    (hdim : Module.finrank F V ≤ 2) (g h : G) :
    Commute (rho g) (rho h) := by
  classical
  let U := rho.invariants
  let tau : Representation F G (V ⧸ U) := quotientByInvariants rho
  letI : tau.IsTrivial := quotientByInvariants_isTrivial rho hG hdim
  have hdelta (k : G) (x : V) : rho k x - x ∈ U := by
    have hx := tau.isTrivial_apply k (Submodule.Quotient.mk x)
    change Submodule.Quotient.mk (rho k x) = Submodule.Quotient.mk x at hx
    exact (Submodule.Quotient.eq U).mp hx
  have hfix (k : G) {x : V} (hx : x ∈ U) : rho k x = x := hx k
  rw [commute_iff_eq]
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply]
  calc
    rho g (rho h x) = rho g (x + (rho h x - x)) := by
      congr 1
      abel
    _ = rho g x + rho g (rho h x - x) := (rho g).map_add _ _
    _ = rho g x + (rho h x - x) := by
      rw [hfix g (hdelta h x)]
    _ = rho h x + (rho g x - x) := by abel
    _ = rho h x + rho h (rho g x - x) := by
      rw [hfix h (hdelta g x)]
    _ = rho h (x + (rho g x - x)) := ((rho h).map_add _ _).symm
    _ = rho h (rho g x) := by
      congr 1
      abel

/-- A finite `p`-group with a faithful representation of dimension at most
two over a field of characteristic `p` is commutative. -/
theorem isMulCommutative_of_faithful_isPGroup_charP_finrank_le_two
    {p : ℕ} [CharP F p] [Fact p.Prime]
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hG : IsPGroup p G) (hdim : Module.finrank F V ≤ 2) :
    IsMulCommutative G := by
  refine ⟨⟨fun g h ↦ ?_⟩⟩
  apply hrho
  rw [map_mul, map_mul]
  exact (representation_apply_commute_of_isPGroup_charP_finrank_le_two
    rho hG hdim g h).eq

end Submission.OddOrder.MathlibSupport
