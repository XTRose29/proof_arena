import Mathlib.GroupTheory.SemidirectProduct

/-!
# Projection onto an internal semidirect-product complement

If a normal subgroup `N` and a subgroup `H` are complementary in `K`, the
unique factorization `k = n * h` defines a group homomorphism from `K` to
`H`.  This file packages that homomorphism and its basic evaluation rules.
-/

namespace Subgroup.IsComplement'

universe u

/-- The canonical projection onto the right factor of an internal
semidirect product. -/
noncomputable def rightProjection
    {K : Type u} [Group K]
    {N H : Subgroup K} [N.Normal]
    (h : N.IsComplement' H) : K →* H :=
  SemidirectProduct.rightHom.comp
    (SemidirectProduct.mulEquivSubgroup h).symm.toMonoidHom

/-- The right projection restricts to the identity on the complement. -/
@[simp]
theorem rightProjection_apply_right
    {K : Type u} [Group K]
    {N H : Subgroup K} [N.Normal]
    (h : N.IsComplement' H) (x : H) :
    h.rightProjection (x : K) = x := by
  let e := SemidirectProduct.mulEquivSubgroup h
  have hx : e.symm (x : K) = SemidirectProduct.inr x := by
    apply e.injective
    rw [e.apply_symm_apply]
    change (x : K) = (1 : K) * (x : K)
    simp
  simp [rightProjection, e, hx]

/-- The right projection is trivial on the normal factor. -/
@[simp]
theorem rightProjection_apply_left
    {K : Type u} [Group K]
    {N H : Subgroup K} [N.Normal]
    (h : N.IsComplement' H) (x : N) :
    h.rightProjection (x : K) = 1 := by
  let e := SemidirectProduct.mulEquivSubgroup h
  have hx : e.symm (x : K) = SemidirectProduct.inl x := by
    apply e.injective
    rw [e.apply_symm_apply]
    change (x : K) = (x : K) * (1 : K)
    simp
  simp [rightProjection, e, hx]

/-- On the canonical factorization `n * x`, the right projection returns
the complement factor `x`. -/
@[simp]
theorem rightProjection_apply_mul
    {K : Type u} [Group K]
    {N H : Subgroup K} [N.Normal]
    (h : N.IsComplement' H) (n : N) (x : H) :
    h.rightProjection ((n : K) * (x : K)) = x := by
  rw [map_mul, rightProjection_apply_left, rightProjection_apply_right,
    one_mul]

end Subgroup.IsComplement'
