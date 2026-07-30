import Submission.OddOrder.PF.Section01.NormalSubgroupConstituentKernels

/-!
# Induction and quotient inflation

This file supplies the quotient/inflation infrastructure for Peterfalvi
1.6(b).  The main theorem is stated for an arbitrary surjective group
homomorphism: if its kernel lies in the inducing subgroup, then pulling a
class function back along the homomorphism commutes with induction.

The proof is the direct finite-group character calculation.  Every fiber of
the surjection is a torsor for its kernel, while the inducing subgroup has
cardinality `|ker q| * |H.map q|`; these two kernel factors cancel in the
normalized induction formula.  Quotient inflation is then the specialization
to `QuotientGroup.mk' K`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u v

namespace ClassFunction

variable {G Q : Type u} {k : Type v}
  [Group G] [Group Q] [Field k]

/-- Pull a class function back along a group homomorphism.  For quotient
maps, this is inflation. -/
def comap (q : G →* Q) : ClassFunction Q k →ₗ[k] ClassFunction G k where
  toFun f :=
    ⟨fun g ↦ f (q g), fun x g ↦ by
      simpa only [map_mul, map_inv] using
        ClassFunction.conj_apply f (q x) (q g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem comap_apply (q : G →* Q) (f : ClassFunction Q k) (g : G) :
    comap q f g = f (q g) :=
  rfl

/-- Pullback along a surjective homomorphism is injective. -/
theorem comap_injective (q : G →* Q) (hq : Function.Surjective q) :
    Function.Injective (comap (k := k) q) := by
  intro f₁ f₂ h
  ext y
  obtain ⟨x, rfl⟩ := hq y
  exact congrArg (fun f : ClassFunction G k ↦ f x) h

/-- Summing a function after a finite surjection multiplies its sum by the
cardinality of the homomorphism kernel. -/
theorem sum_comp_surjective [Fintype G] [Fintype Q]
    (q : G →* Q) (hq : Function.Surjective q) (F : Q → k) :
    (∑ x : G, F (q x)) = Nat.card q.ker • ∑ y : Q, F y := by
  classical
  rw [← Fintype.sum_fiberwise q (fun x : G ↦ F (q x))]
  rw [Finset.smul_sum]
  apply Fintype.sum_congr
  intro y
  have hcard : Fintype.card {x : G // q x = y} = Nat.card q.ker := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (q.fiberEquivKerOfSurjective hq y)
  calc
    (∑ x : {x : G // q x = y}, F (q x)) =
        ∑ _x : {x : G // q x = y}, F y := by
      apply Fintype.sum_congr
      intro x
      rw [x.property]
    _ = Fintype.card {x : G // q x = y} • F y := by simp
    _ = Nat.card q.ker • F y := by rw [hcard]

/-- Cardinality of a subgroup containing the kernel, expressed through its
image under a homomorphism. -/
theorem natCard_eq_ker_mul_map [Finite G]
    (q : G →* Q) (H : Subgroup G) (hker : q.ker ≤ H) :
    Nat.card H = Nat.card q.ker * Nat.card (H.map q) := by
  let qH := q.subgroupMap H
  have hrange : qH.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (q.subgroupMap_surjective H)
  have hmul := (qH.ker).card_mul_index
  rw [Subgroup.index_ker qH, hrange, Subgroup.card_top] at hmul
  have hkcard : Nat.card qH.ker = Nat.card q.ker := by
    rw [Subgroup.ker_subgroupMap]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
  rw [hkcard] at hmul
  exact hmul.symm

/-- Membership in the image subgroup can be detected before applying a
homomorphism when its kernel is contained in the subgroup. -/
theorem map_mem_map_iff (q : G →* Q) (H : Subgroup G)
    (hker : q.ker ≤ H) (g : G) :
    q g ∈ H.map q ↔ g ∈ H := by
  change g ∈ (H.map q).comap q ↔ g ∈ H
  rw [Subgroup.comap_map_eq_self hker]

/-- The induction summands before and after a quotient map agree pointwise. -/
theorem inductionKernel_comap_subgroupMap
    (q : G →* Q) (H : Subgroup G) (hker : q.ker ≤ H)
    (f : ClassFunction (H.map q) k) (x g : G) :
    inductionKernel (H.map q) f (q x) (q g) =
      inductionKernel H (comap (q.subgroupMap H) f) x g := by
  have hmem :
      (q x)⁻¹ * q g * q x ∈ H.map q ↔ x⁻¹ * g * x ∈ H := by
    simpa only [map_inv, map_mul] using
      (map_mem_map_iff q H hker (x⁻¹ * g * x))
  by_cases hx : x⁻¹ * g * x ∈ H
  · have hqx : (q x)⁻¹ * q g * q x ∈ H.map q := hmem.2 hx
    rw [inductionKernel_of_mem _ _ _ _ hqx,
      inductionKernel_of_mem _ _ _ _ hx, comap_apply]
    apply congrArg f
    apply Subtype.ext
    simp
  · have hqx : (q x)⁻¹ * q g * q x ∉ H.map q := hmem.not.mpr hx
    rw [inductionKernel_of_notMem _ _ _ _ hqx,
      inductionKernel_of_notMem _ _ _ _ hx]

/-- Inflation along a finite surjection commutes with induction from every
subgroup containing the kernel.  This is the generic form of source
`cfIndMod`. -/
theorem comap_induce_surjective [Fintype G] [Fintype Q] [CharZero k]
    (q : G →* Q) (hq : Function.Surjective q)
    (H : Subgroup G) [Fintype H] [Fintype (H.map q)]
    (hker : q.ker ≤ H) (f : ClassFunction (H.map q) k) :
    comap q (induce (H.map q) f) =
      induce H (comap (q.subgroupMap H) f) := by
  ext g
  simp only [comap_apply, induce_apply, inductionValue]
  have hsum :
      (∑ x : G,
          inductionKernel H (comap (q.subgroupMap H) f) x g) =
        Nat.card q.ker •
          ∑ y : Q, inductionKernel (H.map q) f y (q g) := by
    calc
      _ = ∑ x : G, inductionKernel (H.map q) f (q x) (q g) := by
        apply Fintype.sum_congr
        intro x
        exact (inductionKernel_comap_subgroupMap q H hker f x g).symm
      _ = _ := sum_comp_surjective q hq
        (fun y : Q ↦ inductionKernel (H.map q) f y (q g))
  rw [hsum, natCard_eq_ker_mul_map q H hker]
  rw [← Nat.cast_smul_eq_nsmul k, smul_eq_mul, Nat.cast_mul]
  have hcard : (Nat.card q.ker : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hmapcard : (Nat.card (H.map q) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp [hcard, hmapcard]

/-- Inflation from a quotient group, as pullback along its quotient map. -/
abbrev inflate (K : Subgroup G) [K.Normal] :
    ClassFunction (G ⧸ K) k →ₗ[k] ClassFunction G k :=
  comap (QuotientGroup.mk' K)

@[simp]
theorem inflate_apply (K : Subgroup G) [K.Normal]
    (f : ClassFunction (G ⧸ K) k) (g : G) :
    inflate K f g = f (QuotientGroup.mk' K g) :=
  rfl

/-- Quotient specialization of `comap_induce_surjective`: inflation from
the image of `H` in `G ⧸ K` commutes with induction whenever `K ≤ H`.

This is the quotient-image form of Peterfalvi's source lemma `cfIndMod`.
The subgroup `H.map (QuotientGroup.mk' K)` is canonically isomorphic to
`H ⧸ K.subgroupOf H`. -/
theorem inflate_induce_quotientImage [Fintype G] [CharZero k]
    (K H : Subgroup G) [K.Normal] (hKH : K ≤ H)
    (f : ClassFunction (H.map (QuotientGroup.mk' K)) k) :
    inflate K (induce (H.map (QuotientGroup.mk' K)) f) =
      induce H (comap ((QuotientGroup.mk' K).subgroupMap H) f) := by
  apply comap_induce_surjective (QuotientGroup.mk' K)
    (QuotientGroup.mk'_surjective K) H
  simpa only [QuotientGroup.ker_mk'] using hKH

end ClassFunction

end

end Submission.OddOrder.PF
