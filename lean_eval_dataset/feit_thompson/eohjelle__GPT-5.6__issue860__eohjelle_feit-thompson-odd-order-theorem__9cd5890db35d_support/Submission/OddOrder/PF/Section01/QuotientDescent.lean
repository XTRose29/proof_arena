import Submission.OddOrder.PF.Section01.QuotientInduction

/-!
# Descent of induced class functions

This file completes the quotient half of Peterfalvi 1.6(b).  A class
function descends through a surjective homomorphism when the homomorphism
kernel acts trivially by left translation.  The main theorem proves that
descending an induced class function agrees with inducing the descended
class function.  Its specialization to a quotient map is the source lemma
`cfIndQuo` (in the canonically equivalent quotient-image formulation).
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u v

namespace ClassFunction

variable {G Q : Type u} {k : Type v}
  [Group G] [Group Q] [Field k]

/-- The source `cfker`: the subgroup of elements acting trivially by left
translation on a class function. -/
def translationKernel (f : ClassFunction G k) : Subgroup G where
  carrier := {a | ∀ x, f (a * x) = f x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb x
    rw [mul_assoc, ha, hb]
  inv_mem' := by
    intro a ha x
    have h := ha (a⁻¹ * x)
    simpa [mul_assoc] using h.symm

@[simp]
theorem mem_translationKernel_iff (f : ClassFunction G k) (a : G) :
    a ∈ translationKernel f ↔ ∀ x, f (a * x) = f x :=
  Iff.rfl

/-- A class function whose translation kernel contains `q.ker` is constant
on the fibers of `q`. -/
theorem eq_of_map_eq_of_ker_le_translationKernel
    (q : G →* Q) (f : ClassFunction G k)
    (hker : q.ker ≤ translationKernel f)
    {x y : G} (hxy : q x = q y) : f x = f y := by
  have hmem : x * y⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy]
    simp
  have h := hker hmem y
  simpa [mul_assoc] using h

/-- Descend a class function through a surjective homomorphism whose kernel
acts trivially. -/
def descend (q : G →* Q) (hq : Function.Surjective q)
    (f : ClassFunction G k) (hker : q.ker ≤ translationKernel f) :
    ClassFunction Q k where
  val y := f (Function.surjInv hq y)
  property a y := by
    calc
      f (Function.surjInv hq (a * y * a⁻¹)) =
          f (Function.surjInv hq a * Function.surjInv hq y *
            (Function.surjInv hq a)⁻¹) := by
        apply eq_of_map_eq_of_ker_le_translationKernel q f hker
        rw [Function.rightInverse_surjInv hq (a * y * a⁻¹)]
        simp only [map_mul, map_inv]
        rw [Function.rightInverse_surjInv hq a,
          Function.rightInverse_surjInv hq y]
      _ = f (Function.surjInv hq y) :=
        ClassFunction.conj_apply f _ _

@[simp]
theorem comap_descend
    (q : G →* Q) (hq : Function.Surjective q)
    (f : ClassFunction G k) (hker : q.ker ≤ translationKernel f) :
    comap q (descend q hq f hker) = f := by
  ext x
  apply eq_of_map_eq_of_ker_le_translationKernel q f hker
  exact Function.rightInverse_surjInv hq (q x)

/-- The kernel of a homomorphism acts trivially on every pulled-back class
function. -/
theorem ker_le_translationKernel_comap
    (q : G →* Q) (f : ClassFunction Q k) :
    q.ker ≤ translationKernel (comap q f) := by
  intro a ha x
  change f (q (a * x)) = f (q x)
  rw [map_mul, MonoidHom.mem_ker.mp ha, one_mul]

@[simp]
theorem descend_comap
    (q : G →* Q) (hq : Function.Surjective q)
    (f : ClassFunction Q k) :
    descend q hq (comap q f)
      (ker_le_translationKernel_comap q f) = f := by
  ext y
  change f (q (Function.surjInv hq y)) = f y
  rw [Function.rightInverse_surjInv hq]

/-- If a class function on an inducing subgroup descends through the
restricted homomorphism, then its induced class function descends through
the ambient homomorphism. -/
theorem ker_le_translationKernel_induce [Fintype G] [Fintype Q]
    [CharZero k]
    (q : G →* Q) (hq : Function.Surjective q)
    (H : Subgroup G) (hker : q.ker ≤ H)
    (f : ClassFunction H k)
    (hf : (q.subgroupMap H).ker ≤ translationKernel f) :
    q.ker ≤ translationKernel (induce H f : ClassFunction G k) := by
  let psi := descend (q.subgroupMap H) (q.subgroupMap_surjective H) f hf
  have hpull : comap (q.subgroupMap H) psi = f :=
    comap_descend _ _ _ _
  have hind : induce H f = comap q (induce (H.map q) psi) := by
    rw [← hpull]
    exact (comap_induce_surjective q hq H hker psi).symm
  rw [hind]
  exact ker_le_translationKernel_comap q _

/-- Generic source `cfIndQuo`: descent of an induced class function is the
induction of the descended class function. -/
theorem induce_descend_surjective [Fintype G] [Fintype Q] [CharZero k]
    (q : G →* Q) (hq : Function.Surjective q)
    (H : Subgroup G) (hker : q.ker ≤ H)
    (f : ClassFunction H k)
    (hf : (q.subgroupMap H).ker ≤ translationKernel f) :
    induce (H.map q)
        (descend (q.subgroupMap H) (q.subgroupMap_surjective H) f hf) =
      descend q hq (induce H f)
        (ker_le_translationKernel_induce q hq H hker f hf) := by
  apply comap_injective q hq
  rw [comap_descend]
  rw [comap_induce_surjective q hq H hker]
  rw [comap_descend]

/-- Quotient specialization of `induce_descend_surjective`.  It is the
quotient-image form of the source lemma `cfIndQuo`. -/
theorem induce_descend_quotientImage [Fintype G] [CharZero k]
    (K H : Subgroup G) [K.Normal] (hKH : K ≤ H)
    (f : ClassFunction H k)
    (hf : K.subgroupOf H ≤ translationKernel f) :
    induce (H.map (QuotientGroup.mk' K))
        (descend ((QuotientGroup.mk' K).subgroupMap H)
          ((QuotientGroup.mk' K).subgroupMap_surjective H) f (by
            rwa [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])) =
      descend (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
        (induce H f) (ker_le_translationKernel_induce
          (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) H
          (by simpa only [QuotientGroup.ker_mk'] using hKH) f (by
            rwa [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])) := by
  exact induce_descend_surjective (QuotientGroup.mk' K)
    (QuotientGroup.mk'_surjective K) H
    (by simpa only [QuotientGroup.ker_mk'] using hKH) f (by
      rwa [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])

end ClassFunction

end

end Submission.OddOrder.PF
