import Submission.OddOrder.PF.Section01.QuotientDescent

/-!
# Literal subgroup quotients in Peterfalvi 1.6

Lean distinguishes the quotient group `H ⧸ K.subgroupOf H` from the image
of `H` as a subgroup of `G ⧸ K`.  This file supplies the canonical
first-isomorphism equivalence between them and transports class functions
across it.  The final `cfIndMod` and `cfIndQuo` statements therefore use the
literal subgroup quotient appearing in the Coq source, while their proofs
reuse the quotient-image results.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u v

namespace ClassFunction

variable {G : Type u} {k : Type v}
  [Group G] [Field k]

/-- The translation kernel of a class function is normal.  This is the
normality property of MathComp's `cfker`. -/
instance translationKernel_normal (f : ClassFunction G k) :
    (translationKernel f).Normal where
  conj_mem a ha g := by
    intro x
    calc
      f ((g * a * g⁻¹) * x) = f (a * (g⁻¹ * x * g)) := by
        convert ClassFunction.conj_apply f g (a * (g⁻¹ * x * g)) using 1
        all_goals group
      _ = f (g⁻¹ * x * g) := ha _
      _ = f x := by
        simpa only [inv_inv] using ClassFunction.conj_apply f g⁻¹ x

/-- The canonical first-isomorphism equivalence from the subgroup quotient
to the image of the subgroup in the ambient quotient. -/
noncomputable def subgroupQuotientEquivImage
    (K H : Subgroup G) [K.Normal] (_hKH : K ≤ H) :
    (H ⧸ K.subgroupOf H) ≃* H.map (QuotientGroup.mk' K) :=
  QuotientGroup.liftEquiv (K.subgroupOf H)
    ((QuotientGroup.mk' K).subgroupMap_surjective H) (by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])

@[simp]
theorem subgroupQuotientEquivImage_mk
    (K H : Subgroup G) [K.Normal] (hKH : K ≤ H) (h : H) :
    subgroupQuotientEquivImage K H hKH (QuotientGroup.mk h) =
      (QuotientGroup.mk' K).subgroupMap H h :=
  rfl

@[simp]
theorem subgroupQuotientEquivImage_symm_subgroupMap
    (K H : Subgroup G) [K.Normal] (hKH : K ≤ H) (h : H) :
    (subgroupQuotientEquivImage K H hKH).symm
        ((QuotientGroup.mk' K).subgroupMap H h) =
      QuotientGroup.mk h := by
  apply (subgroupQuotientEquivImage K H hKH).injective
  simp

/-- Transport a class function on the literal subgroup quotient to the
canonically isomorphic image subgroup in the ambient quotient. -/
def subgroupQuotientToImage
    (K H : Subgroup G) [K.Normal] (hKH : K ≤ H) :
    ClassFunction (H ⧸ K.subgroupOf H) k →ₗ[k]
      ClassFunction (H.map (QuotientGroup.mk' K)) k :=
  comap (subgroupQuotientEquivImage K H hKH).symm.toMonoidHom

@[simp]
theorem subgroupQuotientToImage_apply
    (K H : Subgroup G) [K.Normal] (hKH : K ≤ H)
    (f : ClassFunction (H ⧸ K.subgroupOf H) k)
    (x : H.map (QuotientGroup.mk' K)) :
    subgroupQuotientToImage K H hKH f x =
      f ((subgroupQuotientEquivImage K H hKH).symm x) :=
  rfl

@[simp]
theorem comap_subgroupQuotientToImage
    (K H : Subgroup G) [K.Normal] (hKH : K ≤ H)
    (f : ClassFunction (H ⧸ K.subgroupOf H) k) :
    comap ((QuotientGroup.mk' K).subgroupMap H)
        (subgroupQuotientToImage K H hKH f) =
      inflate (K.subgroupOf H) f := by
  ext h
  simp [inflate]

/-- Descend a class function to the literal quotient by a subgroup of its
translation kernel.  This is the source operation `quo`. -/
def quotientDescend
    (K : Subgroup G) [K.Normal] (f : ClassFunction G k)
    (hK : K ≤ translationKernel f) : ClassFunction (G ⧸ K) k :=
  descend (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) f (by
    simpa only [QuotientGroup.ker_mk'] using hK)

@[simp]
theorem inflate_quotientDescend
    (K : Subgroup G) [K.Normal] (f : ClassFunction G k)
    (hK : K ≤ translationKernel f) :
    inflate K (quotientDescend K f hK) = f := by
  apply comap_descend

/-- Transporting literal quotient descent to the image quotient agrees
with descent through the restricted ambient quotient map. -/
theorem subgroupQuotientToImage_quotientDescend
    (K H : Subgroup G) [K.Normal] (hKH : K ≤ H)
    (f : ClassFunction H k)
    (hf : K.subgroupOf H ≤ translationKernel f) :
    subgroupQuotientToImage K H hKH
        (quotientDescend (K.subgroupOf H) f hf) =
      descend ((QuotientGroup.mk' K).subgroupMap H)
        ((QuotientGroup.mk' K).subgroupMap_surjective H) f (by
          rwa [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']) := by
  apply comap_injective ((QuotientGroup.mk' K).subgroupMap H)
    ((QuotientGroup.mk' K).subgroupMap_surjective H)
  rw [comap_subgroupQuotientToImage, inflate_quotientDescend,
    comap_descend]

/-- A normal subgroup of the inducing subgroup's translation kernel lies
in the translation kernel after induction. -/
theorem le_translationKernel_induce [Fintype G] [CharZero k]
    (K H : Subgroup G) [K.Normal] (hKH : K ≤ H)
    (f : ClassFunction H k)
    (hf : K.subgroupOf H ≤ translationKernel f) :
    K ≤ translationKernel (induce H f : ClassFunction G k) := by
  have hf' :
      ((QuotientGroup.mk' K).subgroupMap H).ker ≤ translationKernel f := by
    rwa [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  have h := ker_le_translationKernel_induce
    (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) H
    (by simpa only [QuotientGroup.ker_mk'] using hKH) f hf'
  simpa only [QuotientGroup.ker_mk'] using h

/-- Source-shaped `cfIndMod`: induction from the literal quotient `H/K`
commutes with inflation to `G`. -/
theorem cfIndMod [Fintype G] [CharZero k]
    (K H : Subgroup G) [K.Normal] (hKH : K ≤ H)
    (f : ClassFunction (H ⧸ K.subgroupOf H) k) :
    induce H (inflate (K.subgroupOf H) f) =
      inflate K
        (induce (H.map (QuotientGroup.mk' K))
          (subgroupQuotientToImage K H hKH f)) := by
  have hpull :
      comap ((QuotientGroup.mk' K).subgroupMap H)
          (subgroupQuotientToImage K H hKH f) =
        inflate (K.subgroupOf H) f := by
    exact comap_subgroupQuotientToImage K H hKH f
  symm
  calc
    inflate K
          (induce (H.map (QuotientGroup.mk' K))
            (subgroupQuotientToImage K H hKH f)) =
        induce H
          (comap ((QuotientGroup.mk' K).subgroupMap H)
            (subgroupQuotientToImage K H hKH f)) :=
      inflate_induce_quotientImage K H hKH _
    _ = induce H (inflate (K.subgroupOf H) f) := by rw [hpull]

/-- Source-shaped `cfIndQuo`: quotienting an induced class function is the
induction of the quotient class function. -/
theorem cfIndQuo [Fintype G] [CharZero k]
    (K H : Subgroup G) [K.Normal] (hKH : K ≤ H)
    (f : ClassFunction H k)
    (hf : K.subgroupOf H ≤ translationKernel f) :
    induce (H.map (QuotientGroup.mk' K))
        (subgroupQuotientToImage K H hKH
          (quotientDescend (K.subgroupOf H) f hf)) =
      quotientDescend K (induce H f)
        (le_translationKernel_induce K H hKH f hf) := by
  have hf' :
      ((QuotientGroup.mk' K).subgroupMap H).ker ≤ translationKernel f := by
    rwa [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  calc
    induce (H.map (QuotientGroup.mk' K))
          (subgroupQuotientToImage K H hKH
            (quotientDescend (K.subgroupOf H) f hf)) =
        induce (H.map (QuotientGroup.mk' K))
          (descend ((QuotientGroup.mk' K).subgroupMap H)
            ((QuotientGroup.mk' K).subgroupMap_surjective H) f hf') := by
      rw [subgroupQuotientToImage_quotientDescend]
    _ = descend (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
        (induce H f) (ker_le_translationKernel_induce
          (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) H
          (by simpa only [QuotientGroup.ker_mk'] using hKH) f hf') := by
      exact induce_descend_quotientImage K H hKH f hf
    _ = quotientDescend K (induce H f)
        (le_translationKernel_induce K H hKH f hf) := by
      rfl

end ClassFunction

end

end Submission.OddOrder.PF
