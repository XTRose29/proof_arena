import Submission.OddOrder.PF.Section09.PTypeCoreActionKernel
import Submission.OddOrder.PF.Section09.PTypeNonGaloisSelectedCoordinate

/-!
# Peterfalvi Section 9: the quotient-regular character in the rigid branch

This module carries out the character-norm calculation in Peterfalvi
(9.11.4).  The selected pointwise action kernel is pulled back to the derived
subgroup, its quotient-regular character is induced to the maximal subgroup,
and the norm is evaluated by the outer-complement translates.

The narrow interface used by the support and pairing phases lives in
`PTypeCoreGammaInternal`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section16
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open PTypeCoreContextInternal
open PTypeCoreBoundsInternal
open PTypeCoreActionKernelInternal
open PTypeNonGaloisSelectedCoordinateInternal
open PTypeNonGaloisInertiaCoreInternal
open scoped BigOperators Classical

universe u

namespace PTypeCoreGammaInternal

local instance pTypeCoreGammaDerivedNormal
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    (M : Subgroup G) : (pTypeCoreDerived M).Normal :=
  Submission.OddOrder.BG.Section16.TypeSpecInternal.derivedWithin_normal16 M

/-! ## Quotient-regular characters -/

/-- Source `alpha = gamma - psi1`. -/
def pTypeCoreAlpha
    {M : Type u} [Group M]
    (gamma psi : ClassFunction M ℂ) : ClassFunction M ℂ :=
  gamma - psi

/-- Inducing the trivial character from a normal subgroup gives the inflated
regular character of the quotient. -/
theorem pTypeCore_induce_trivial_normal_apply
    {Q : Type u} [Group Q] [Fintype Q]
    (K : Subgroup Q) [K.Normal] (x : Q) :
    ClassFunction.induce K
        ((IrreducibleCharacter.trivial : IrreducibleCharacter K ℂ) :
          ClassFunction K ℂ) x =
      if x ∈ K then (K.index : ℂ) else 0 := by
  classical
  rw [ClassFunction.induce_apply_formula]
  by_cases hx : x ∈ K
  · rw [if_pos hx]
    have hconj (y : Q) : y⁻¹ * x * y ∈ K := by
      simpa using (inferInstance : K.Normal).conj_mem x hx y⁻¹
    simp_rw [dif_pos (hconj _), IrreducibleCharacter.trivial_apply]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_eq_nat_card, mul_one,
      ← Subgroup.card_mul_index K, Nat.cast_mul]
    field_simp
  · rw [if_neg hx]
    have hconj (y : Q) : y⁻¹ * x * y ∉ K := by
      intro hy
      have hy' := (inferInstance : K.Normal).conj_mem
        (y⁻¹ * x * y) hy y
      have : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
      rw [this] at hy'
      exact hx hy'
    simp_rw [dif_neg (hconj _)]
    simp

/-- The pairing of two quotient-regular characters is determined by the
index of the intersection of their kernels. -/
private theorem pairing_induced_trivial_normal
    {Q : Type u} [Group Q] [Fintype Q]
    (K L : Subgroup Q) [K.Normal] [L.Normal] :
    characterPairing
        (ClassFunction.induce K
          ((IrreducibleCharacter.trivial : IrreducibleCharacter K ℂ) :
            ClassFunction K ℂ))
        (ClassFunction.induce L
          ((IrreducibleCharacter.trivial : IrreducibleCharacter L ℂ) :
            ClassFunction L ℂ)) =
      (K.index : ℂ) * (L.index : ℂ) / ((K ⊓ L).index : ℂ) := by
  classical
  let c : ℂ := (K.index : ℂ) * (L.index : ℂ)
  have hterm (x : Q) :
      ClassFunction.induce K
          ((IrreducibleCharacter.trivial : IrreducibleCharacter K ℂ) :
            ClassFunction K ℂ) x *
        ClassFunction.induce L
          ((IrreducibleCharacter.trivial : IrreducibleCharacter L ℂ) :
            ClassFunction L ℂ) x⁻¹ =
      if x ∈ (K ⊓ L) then c else 0 := by
    rw [pTypeCore_induce_trivial_normal_apply,
      pTypeCore_induce_trivial_normal_apply]
    by_cases hxK : x ∈ K <;> by_cases hxL : x ∈ L <;>
      simp [hxK, hxL, c]
  have hcount :
      (∑ x : Q, if x ∈ (K ⊓ L) then (1 : ℂ) else 0) =
        (Nat.card ↥(K ⊓ L) : ℂ) := by
    rw [Finset.sum_boole]
    congr 2
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype (fun x : Q ↦ x ∈ (K ⊓ L))).symm
  rw [characterPairing]
  calc
    (Nat.card Q : ℂ)⁻¹ *
          ∑ x : Q,
            ClassFunction.induce K
                ((IrreducibleCharacter.trivial :
                  IrreducibleCharacter K ℂ) : ClassFunction K ℂ) x *
              ClassFunction.induce L
                ((IrreducibleCharacter.trivial :
                  IrreducibleCharacter L ℂ) : ClassFunction L ℂ) x⁻¹ =
        (Nat.card Q : ℂ)⁻¹ *
          ∑ x : Q, if x ∈ (K ⊓ L) then c else 0 := by
            congr 1
            exact Finset.sum_congr rfl (fun x _ ↦ hterm x)
    _ = (Nat.card Q : ℂ)⁻¹ *
          ((∑ x : Q, if x ∈ (K ⊓ L) then (1 : ℂ) else 0) * c) := by
            congr 1
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x ∈ (K ⊓ L) <;> simp [hx]
    _ = (Nat.card Q : ℂ)⁻¹ * (Nat.card ↥(K ⊓ L) : ℂ) * c := by
          rw [hcount]
          ring
    _ = (K.index : ℂ) * (L.index : ℂ) /
          ((K ⊓ L).index : ℂ) := by
            rw [← Subgroup.card_mul_index (K ⊓ L), Nat.cast_mul]
            have hcard : (Nat.card ↥(K ⊓ L) : ℂ) ≠ 0 :=
              Nat.cast_ne_zero.mpr (Nat.card_pos (α := ↥(K ⊓ L))).ne'
            have hindex : (((K ⊓ L).index : ℕ) : ℂ) ≠ 0 :=
              Nat.cast_ne_zero.mpr (K ⊓ L).index_ne_zero_of_finite
            dsimp only [c]
            field_simp [hcard, hindex]

/-- For a normal subgroup with a chosen complement, the norm after induction
is the sum of the pairings with the complement translates. -/
private theorem induce_normal_pairing_eq_sum_complement
    {Q : Type u} [Group Q] [Fintype Q]
    (N V : Subgroup Q) [N.Normal]
    (hcomp : N.IsComplement' V) (f : ClassFunction N ℂ) :
    characterPairing (ClassFunction.induce N f)
        (ClassFunction.induce N f) =
      ∑ v : V,
        characterPairing f
          (ClassFunction.normalConjugate N (v : Q) f) := by
  classical
  have hsum :
      (∑ x : Q, ClassFunction.normalConjugate N x f) =
        (Nat.card N : ℂ) •
          ∑ v : V, ClassFunction.normalConjugate N (v : Q) f := by
    calc
      (∑ x : Q, ClassFunction.normalConjugate N x f) =
          ∑ z : N × V,
            ClassFunction.normalConjugate N
              ((z.1 : Q) * (z.2 : Q)) f := by
            symm
            refine Fintype.sum_equiv hcomp.equiv.symm
              (fun z : N × V ↦ ClassFunction.normalConjugate N
                ((z.1 : Q) * (z.2 : Q)) f)
              (fun x : Q ↦ ClassFunction.normalConjugate N x f) ?_
            intro z
            simp only [Subgroup.IsComplement.equiv_symm_apply]
      _ = ∑ n : N, ∑ v : V,
          ClassFunction.normalConjugate N
            ((n : Q) * (v : Q)) f := by
            rw [Fintype.sum_prod_type]
      _ = ∑ _n : N, ∑ v : V,
          ClassFunction.normalConjugate N (v : Q) f := by
            apply Finset.sum_congr rfl
            intro n _
            apply Finset.sum_congr rfl
            intro v _
            rw [ClassFunction.normalConjugate_mul,
              ClassFunction.normalConjugate_coe]
      _ = (Nat.card N : ℂ) •
          ∑ v : V, ClassFunction.normalConjugate N (v : Q) f := by
            rw [Finset.sum_const, Finset.card_univ,
              ← Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  rw [ClassFunction.frobeniusReciprocity,
    ClassFunction.restrict_induce_eq_average_normalConjugates, hsum,
    smul_smul]
  have hcard : (Nat.card N : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := N)).ne'
  rw [inv_mul_cancel₀ hcard, one_smul]
  change IrreducibleCharacter.pairingLeft f
      (∑ v : V, ClassFunction.normalConjugate N (v : Q) f) = _
  rw [map_sum]
  rfl

/-! ## The selected character and its induction -/

/-- The selected quotient-regular character on `HU = H ⋊ U`. -/
def pTypeCoreSelectedInducedTrivial
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    ClassFunction (pTypeCoreDerived M) ℂ :=
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  ClassFunction.induce T
    ((IrreducibleCharacter.trivial : IrreducibleCharacter T ℂ) :
      ClassFunction T ℂ)

/-- Source `gamma = Ind[M, H ⋊ U₁] 1`. -/
def pTypeCoreGamma
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    ClassFunction M ℂ :=
  ClassFunction.induce (pTypeCoreDerived M)
    (pTypeCoreSelectedInducedTrivial ctx facts not_Galois)

/-- The two inductions defining `gamma` preserve virtual characters. -/
theorem pTypeCoreGamma_isVirtual
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    ClassFunction.IsVirtual
      (pTypeCoreGamma ctx facts not_Galois) := by
  let HU := pTypeCoreDerived M
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let oneT : VirtualCharacter T ℂ :=
    Finsupp.single IrreducibleCharacter.trivial 1
  let zHU : VirtualCharacter HU ℂ := VirtualCharacter.induce T oneT
  let zM : VirtualCharacter M ℂ := VirtualCharacter.induce HU zHU
  refine ⟨zM, ?_⟩
  simp only [zM, zHU, oneT, pTypeCoreGamma,
    pTypeCoreSelectedInducedTrivial,
    VirtualCharacter.realize_induce,
    VirtualCharacter.realize_single, Int.cast_one, one_smul]
  rfl

/-- The selected quotient-regular character is the index `a` on its kernel
and zero elsewhere. -/
theorem pTypeCoreSelectedInducedTrivial_apply
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (x : pTypeCoreDerived M) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    pTypeCoreSelectedInducedTrivial ctx facts not_Galois x =
      if x ∈ T then (pTypeNonGaloisIndex hD not_Galois : ℂ) else 0 := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  change ClassFunction.induce T
      ((IrreducibleCharacter.trivial : IrreducibleCharacter T ℂ) :
        ClassFunction T ℂ) x = _
  rw [pTypeCore_induce_trivial_normal_apply,
    pTypeNonGaloisH1InertiaInHU_index ctx facts not_Galois]

/-- The degree of `gamma` is `q * a`. -/
theorem pTypeCoreGamma_one
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    pTypeCoreGamma ctx facts not_Galois 1 =
      ((D.q * pTypeNonGaloisIndex hD not_Galois : ℕ) : ℂ) := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let HU := pTypeCoreDerived M
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  change ClassFunction.induce HU
      (ClassFunction.induce T
        ((IrreducibleCharacter.trivial : IrreducibleCharacter T ℂ) :
          ClassFunction T ℂ)) 1 = _
  rw [ClassFunction.induce_one, ClassFunction.induce_one,
    IrreducibleCharacter.trivial_apply,
    pTypeNonGaloisH1InertiaInHU_index ctx facts not_Galois,
    pTypeCore_index_eq_q ctx facts, mul_one, Nat.cast_mul]

/-! ## Translated selected inertia subgroups -/

/-- The pullback to `HU` of the `w`-translate of the selected pointwise
action kernel. -/
def pTypeCoreTranslatedSelectedInertia
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) : Subgroup (pTypeCoreDerived M) :=
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  (actionConjugate D.W₁_action_U K w).comap
    (pTypeNonGaloisHUToUProjection ctx)

instance pTypeCoreTranslatedSelectedInertia_normal
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) :
    (pTypeCoreTranslatedSelectedInertia
      ctx facts not_Galois w).Normal := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let Kw := actionConjugate D.W₁_action_U K w
  have hKw : Kw.Normal := by
    change (K.map (D.W₁_action_U w).toMonoidHom).Normal
    exact Subgroup.Normal.map data.actionKernel_normal
      (D.W₁_action_U w).toMonoidHom
      (D.W₁_action_U w).surjective
  exact Subgroup.Normal.comap hKw
    (pTypeNonGaloisHUToUProjection ctx)

/-- Translating the selected kernel does not change its pullback index. -/
theorem pTypeCoreTranslatedSelectedInertia_index
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) :
    (pTypeCoreTranslatedSelectedInertia
      ctx facts not_Galois w).index =
      pTypeNonGaloisIndex
        (Ptype_factor_action_hypotheses ctx facts) not_Galois := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let Kw := actionConjugate D.W₁_action_U K w
  calc
    (pTypeCoreTranslatedSelectedInertia
        ctx facts not_Galois w).index = Kw.index :=
      Kw.index_comap_of_surjective
        (pTypeNonGaloisHUToUProjection_surjective ctx)
    _ = K.index := Subgroup.index_map_equiv K (D.W₁_action_U w)
    _ = pTypeNonGaloisIndex hD not_Galois := rfl

/-- The canonical projection `HU → U` intertwines conjugation by `W₁`
with the given `W₁`-action on `U`. -/
private theorem HUToUProjection_conj_W₁
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (w : W₁) (x : pTypeCoreDerived M) :
    let D := Ptype_factor_action ctx facts
    let wM : M := ⟨(w : G), ctx.typeP.1.2.1.1 w.property⟩
    pTypeNonGaloisHUToUProjection ctx
        (MulAut.conjNormal wM x) =
      D.W₁_action_U w (pTypeNonGaloisHUToUProjection ctx x) := by
  classical
  let D := Ptype_factor_action ctx facts
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let UHU := (U.subgroupOf M).subgroupOf HU
  let pi : HU →* U := pTypeNonGaloisHUToUProjection ctx
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans hDerM
  let wM : M := ⟨(w : G), ctx.typeP.1.2.1.1 w.property⟩
  have hinner : H.IsComplement' UHU := by
    simpa only [H, UHU] using pTypeCoreH_isComplement_U ctx
  obtain ⟨⟨n, v⟩, hnv⟩ := hinner.2 x
  have hnv' : (n : HU) * (v : HU) = x := by
    simpa only [Subgroup.IsComplement.equiv_symm_apply] using hnv
  let u : U := ⟨(((v : HU) : M) : G), v.property⟩
  let u' : U := D.W₁_action_U w u
  let v' : UHU :=
    ⟨⟨⟨(u' : G), hUM u'.property⟩, hUder u'.property⟩,
      u'.property⟩
  have hvConj : MulAut.conjNormal wM (v : HU) = (v' : HU) := by
    apply Subtype.ext
    apply Subtype.ext
    change (w : G) * (u : G) * (w : G)⁻¹ = (u' : G)
    rfl
  let FM : Subgroup M := (Fitting_core M).subgroupOf M
  let nFM : FM := ⟨((n : HU) : M), n.property⟩
  let nFM' : FM := MulAut.conjNormal wM nFM
  let n' : H :=
    ⟨⟨(nFM' : M), hHder nFM'.property⟩, nFM'.property⟩
  have hnConj : MulAut.conjNormal wM (n : HU) = (n' : HU) := by
    apply Subtype.ext
    rfl
  have hnOne : pi (n : HU) = 1 := by
    apply MonoidHom.mem_ker.mp
    change (n : HU) ∈ (pTypeNonGaloisHUToUProjection ctx).ker
    rw [pTypeNonGaloisHUToUProjection_ker ctx]
    exact n.property
  have hnOne' : pi (n' : HU) = 1 := by
    apply MonoidHom.mem_ker.mp
    change (n' : HU) ∈ (pTypeNonGaloisHUToUProjection ctx).ker
    rw [pTypeNonGaloisHUToUProjection_ker ctx]
    exact n'.property
  have hvProj : pi (v : HU) = u :=
    pTypeNonGaloisHUToUProjection_apply_complement ctx v
  have hvProj' : pi (v' : HU) = u' :=
    pTypeNonGaloisHUToUProjection_apply_complement ctx v'
  calc
    pi (MulAut.conjNormal wM x) =
        pi (MulAut.conjNormal wM ((n : HU) * (v : HU))) := by
          rw [hnv']
    _ = pi (MulAut.conjNormal wM (n : HU)) *
          pi (MulAut.conjNormal wM (v : HU)) := by
          rw [map_mul, map_mul]
    _ = u' := by rw [hnConj, hvConj, hnOne', hvProj', one_mul]
    _ = D.W₁_action_U w (pi ((n : HU) * (v : HU))) := by
          rw [map_mul, hnOne, hvProj, one_mul]
    _ = D.W₁_action_U w (pi x) := by rw [hnv']

/-- Literal conjugation of the selected inertia subgroup agrees with the
translated pullback. -/
private theorem selectedInertia_conjugate_eq_translated
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) :
    let HU := pTypeCoreDerived M
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    let wM : M := ⟨(w : G), ctx.typeP.1.2.1.1 w.property⟩
    T.map (MulAut.conjNormal wM).toMonoidHom =
      pTypeCoreTranslatedSelectedInertia
        ctx facts not_Galois w := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU := pTypeCoreDerived M
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let pi : HU →* U := pTypeNonGaloisHUToUProjection ctx
  have hW₁M : W₁ ≤ M := ctx.typeP.1.2.1.1
  let wM : M := ⟨(w : G), hW₁M w.property⟩
  let winvM : M := ⟨((w⁻¹ : W₁) : G), hW₁M (w⁻¹).property⟩
  ext x
  rw [Subgroup.mem_map_equiv]
  change pi ((MulAut.conjNormal wM).symm x) ∈ K ↔
    pi x ∈ actionConjugate D.W₁_action_U K w
  have harg : (MulAut.conjNormal wM).symm x =
      MulAut.conjNormal winvM x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [harg, HUToUProjection_conj_W₁
    ctx facts w⁻¹ x, mem_actionConjugate_iff]
  rfl

/-- The selected pullback intersected with its translate is the pullback of
the corresponding intersection in `U`. -/
theorem pTypeCore_selectedInertia_inf_translated_eq
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    let K := pointwiseActionKernel D.U_action data.H₁
    pTypeNonGaloisH1InertiaInHU ctx facts not_Galois ⊓
        pTypeCoreTranslatedSelectedInertia ctx facts not_Galois w =
      (K ⊓ actionConjugate D.W₁_action_U K w).comap
        (pTypeNonGaloisHUToUProjection ctx) := by
  rfl

/-- In the rigid branch, a nonidentity translate meets the selected inertia
subgroup in index `u`. -/
theorem pTypeCore_selectedInertia_inf_translated_index
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {S₂ : Finset (ClassFunction M ℂ)}
    (rigid : PTypeCoreRigidFacts ctx facts not_Galois S₂)
    (w : W₁) (hw : w ≠ 1) :
    let D := Ptype_factor_action ctx facts
    (pTypeNonGaloisH1InertiaInHU ctx facts not_Galois ⊓
        pTypeCoreTranslatedSelectedInertia
          ctx facts not_Galois w).index =
      pTypeActionFactorCard D := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  rw [pTypeCore_selectedInertia_inf_translated_eq]
  calc
    ((K ⊓ actionConjugate D.W₁_action_U K w).comap
        (pTypeNonGaloisHUToUProjection ctx)).index =
        (K ⊓ actionConjugate D.W₁_action_U K w).index :=
      (K ⊓ actionConjugate D.W₁_action_U K w).index_comap_of_surjective
        (pTypeNonGaloisHUToUProjection_surjective ctx)
    _ = D.C.index := by
      rw [PTypeCoreActionKernelInternal.PTypeCoreRigidFacts.actionKernel_inf_eq
        rigid w hw]
    _ = pTypeActionFactorCard D :=
      (pTypeCore_actionFactorCard_eq_C_index D).symm

/-! ## The norm of `gamma` -/

/-- Conjugating the selected quotient-regular character replaces its kernel
by the translated selected inertia subgroup. -/
private theorem selectedInducedTrivial_normalConjugate
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) :
    let HU := pTypeCoreDerived M
    let Tw := pTypeCoreTranslatedSelectedInertia
      ctx facts not_Galois w
    let wM : M := ⟨(w : G), ctx.typeP.1.2.1.1 w.property⟩
    ClassFunction.normalConjugate HU wM
        (pTypeCoreSelectedInducedTrivial ctx facts not_Galois) =
      ClassFunction.induce Tw
        ((IrreducibleCharacter.trivial : IrreducibleCharacter Tw ℂ) :
          ClassFunction Tw ℂ) := by
  classical
  let HU := pTypeCoreDerived M
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let Tw := pTypeCoreTranslatedSelectedInertia
    ctx facts not_Galois w
  have hW₁M : W₁ ≤ M := ctx.typeP.1.2.1.1
  let wM : M := ⟨(w : G), hW₁M w.property⟩
  have hTw : T.map (MulAut.conjNormal wM).toMonoidHom = Tw :=
    selectedInertia_conjugate_eq_translated
      ctx facts not_Galois w
  ext x
  rw [ClassFunction.normalConjugate_apply,
    pTypeCoreSelectedInducedTrivial_apply,
    pTypeCore_induce_trivial_normal_apply,
    pTypeCoreTranslatedSelectedInertia_index]
  have hmem : (MulAut.conjNormal wM).symm x ∈ T ↔ x ∈ Tw := by
    rw [← hTw, Subgroup.mem_map_equiv]
  by_cases hx : x ∈ Tw
  · rw [if_pos hx, if_pos (hmem.mpr hx)]
  · rw [if_neg hx, if_neg (hmem.not.mpr hx)]

/-- A translate contributes `a²` divided by the index of the corresponding
inertia intersection. -/
private theorem selectedInducedTrivial_pairing_translate
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let HU := pTypeCoreDerived M
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    let Tw := pTypeCoreTranslatedSelectedInertia
      ctx facts not_Galois w
    let wM : M := ⟨(w : G), ctx.typeP.1.2.1.1 w.property⟩
    characterPairing
        (pTypeCoreSelectedInducedTrivial ctx facts not_Galois)
        (ClassFunction.normalConjugate HU wM
          (pTypeCoreSelectedInducedTrivial ctx facts not_Galois)) =
      (pTypeNonGaloisIndex hD not_Galois : ℂ) ^ 2 /
        ((T ⊓ Tw).index : ℂ) := by
  dsimp only
  let hD := Ptype_factor_action_hypotheses ctx facts
  let HU := pTypeCoreDerived M
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let Tw := pTypeCoreTranslatedSelectedInertia
    ctx facts not_Galois w
  have hW₁M : W₁ ≤ M := ctx.typeP.1.2.1.1
  let wM : M := ⟨(w : G), hW₁M w.property⟩
  rw [selectedInducedTrivial_normalConjugate]
  change characterPairing
      (ClassFunction.induce T
        ((IrreducibleCharacter.trivial : IrreducibleCharacter T ℂ) :
          ClassFunction T ℂ))
      (ClassFunction.induce Tw
        ((IrreducibleCharacter.trivial : IrreducibleCharacter Tw ℂ) :
          ClassFunction Tw ℂ)) = _
  rw [pairing_induced_trivial_normal,
    pTypeNonGaloisH1InertiaInHU_index ctx facts not_Galois,
    pTypeCoreTranslatedSelectedInertia_index]
  ring

/-- The identity translate contributes `a`. -/
private theorem selectedInducedTrivial_pairing_one
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let HU := pTypeCoreDerived M
    characterPairing
        (pTypeCoreSelectedInducedTrivial ctx facts not_Galois)
        (ClassFunction.normalConjugate HU (1 : M)
          (pTypeCoreSelectedInducedTrivial ctx facts not_Galois)) =
      (pTypeNonGaloisIndex hD not_Galois : ℂ) := by
  dsimp only
  let hD := Ptype_factor_action_hypotheses ctx facts
  let HU := pTypeCoreDerived M
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  rw [ClassFunction.normalConjugate_one]
  change characterPairing
      (ClassFunction.induce T
        ((IrreducibleCharacter.trivial : IrreducibleCharacter T ℂ) :
          ClassFunction T ℂ))
      (ClassFunction.induce T
        ((IrreducibleCharacter.trivial : IrreducibleCharacter T ℂ) :
          ClassFunction T ℂ)) = _
  rw [pairing_induced_trivial_normal, inf_idem,
    pTypeNonGaloisH1InertiaInHU_index ctx facts not_Galois]
  have ha : (pTypeNonGaloisIndex hD not_Galois : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Nat.zero_lt_of_lt
        (one_lt_pTypeNonGaloisIndex hD not_Galois)).ne'
  field_simp [ha]

/-- Every nonidentity translate contributes the common value `a²/u`. -/
private theorem selectedInducedTrivial_pairing_translate_of_ne_one
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {S₂ : Finset (ClassFunction M ℂ)}
    (rigid : PTypeCoreRigidFacts ctx facts not_Galois S₂)
    (w : W₁) (hw : w ≠ 1) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let HU := pTypeCoreDerived M
    let wM : M := ⟨(w : G), ctx.typeP.1.2.1.1 w.property⟩
    characterPairing
        (pTypeCoreSelectedInducedTrivial ctx facts not_Galois)
        (ClassFunction.normalConjugate HU wM
          (pTypeCoreSelectedInducedTrivial ctx facts not_Galois)) =
      (((pTypeNonGaloisIndex hD not_Galois) ^ 2 : ℕ) : ℂ) /
        (pTypeActionFactorCard D : ℂ) := by
  dsimp only
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let HU := pTypeCoreDerived M
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let Tw := pTypeCoreTranslatedSelectedInertia
    ctx facts not_Galois w
  have hW₁M : W₁ ≤ M := ctx.typeP.1.2.1.1
  let wM : M := ⟨(w : G), hW₁M w.property⟩
  rw [selectedInducedTrivial_pairing_translate,
    pTypeCore_selectedInertia_inf_translated_index rigid w hw]
  norm_cast

/-- The norm calculation in (9.11.4): the identity translate contributes
`a`, while the `q - 1` nonidentity translates each contribute `a²/u`. -/
theorem pTypeCoreGamma_pairing
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {S₂ : Finset (ClassFunction M ℂ)}
    (rigid : PTypeCoreRigidFacts ctx facts not_Galois S₂) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let a := pTypeNonGaloisIndex hD not_Galois
    let u₀ := pTypeActionFactorCard D
    characterPairing (pTypeCoreGamma ctx facts not_Galois)
        (pTypeCoreGamma ctx facts not_Galois) =
      (a : ℂ) + ((((D.q - 1) * a ^ 2 : ℕ) : ℂ) / (u₀ : ℂ)) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let a := pTypeNonGaloisIndex hD not_Galois
  let u₀ := pTypeActionFactorCard D
  let HU := pTypeCoreDerived M
  let theta := pTypeCoreSelectedInducedTrivial
    ctx facts not_Galois
  let W₁M := W₁.subgroupOf M
  have hW₁M : W₁ ≤ M := ctx.typeP.1.2.1.1
  let eW : W₁M ≃* W₁ := Subgroup.subgroupOfEquivOfLe hW₁M
  have houter : HU.IsComplement' W₁M :=
    ctx.typeP.1.2.2.2.2.2.2
  have hreindex :
      (∑ v : W₁M,
          characterPairing theta
            (ClassFunction.normalConjugate HU (v : M) theta)) =
        ∑ w : W₁,
          characterPairing theta
            (ClassFunction.normalConjugate HU
              (⟨(w : G), hW₁M w.property⟩ : M) theta) := by
    calc
      (∑ v : W₁M,
          characterPairing theta
            (ClassFunction.normalConjugate HU (v : M) theta)) =
          ∑ w : W₁,
            characterPairing theta
              (ClassFunction.normalConjugate HU
                ((eW.symm w : W₁M) : M) theta) := by
            exact (Equiv.sum_comp eW.symm.toEquiv
              (fun v : W₁M ↦ characterPairing theta
                (ClassFunction.normalConjugate HU (v : M) theta))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro w _
        congr 2
  change characterPairing (ClassFunction.induce HU theta)
      (ClassFunction.induce HU theta) = _
  rw [induce_normal_pairing_eq_sum_complement
    HU W₁M houter theta, hreindex]
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun w : W₁ ↦ characterPairing theta
      (ClassFunction.normalConjugate HU
        (⟨(w : G), hW₁M w.property⟩ : M) theta)) (1 : W₁)]
  have hone :
      characterPairing theta
          (ClassFunction.normalConjugate HU
            (⟨((1 : W₁) : G), hW₁M (1 : W₁).property⟩ : M) theta) =
        (a : ℂ) := by
    have hOneM :
        (⟨((1 : W₁) : G), hW₁M (1 : W₁).property⟩ : M) = 1 := by
      apply Subtype.ext
      simp
    rw [hOneM]
    simpa only [theta, a] using
      selectedInducedTrivial_pairing_one ctx facts not_Galois
  rw [hone]
  have hrest :
      (∑ w : {w : W₁ // w ≠ 1},
          characterPairing theta
            (ClassFunction.normalConjugate HU
              (⟨((w : W₁) : G), hW₁M (w : W₁).property⟩ : M) theta)) =
        (((Nat.card W₁ - 1) * a ^ 2 : ℕ) : ℂ) / (u₀ : ℂ) := by
    calc
      (∑ w : {w : W₁ // w ≠ 1},
          characterPairing theta
            (ClassFunction.normalConjugate HU
              (⟨((w : W₁) : G), hW₁M (w : W₁).property⟩ : M) theta)) =
          ∑ _w : {w : W₁ // w ≠ 1},
            (((a ^ 2 : ℕ) : ℂ) / (u₀ : ℂ)) := by
              apply Finset.sum_congr rfl
              intro w _
              simpa only [theta, D, hD, a, u₀] using
                selectedInducedTrivial_pairing_translate_of_ne_one
                  rigid w w.property
      _ = ((Nat.card W₁ - 1 : ℕ) : ℂ) *
          (((a ^ 2 : ℕ) : ℂ) / (u₀ : ℂ)) := by
            have hcard :
                Fintype.card {w : W₁ // w ≠ 1} = Nat.card W₁ - 1 := by
              calc
                Fintype.card {w : W₁ // w ≠ 1} =
                    Fintype.card W₁ - 1 := Set.card_ne_eq _
                _ = Nat.card W₁ - 1 := by
                  rw [Fintype.card_eq_nat_card]
            rw [Finset.sum_const, nsmul_eq_mul,
              Finset.card_univ, hcard]
      _ = (((Nat.card W₁ - 1) * a ^ 2 : ℕ) : ℂ) /
          (u₀ : ℂ) := by
            rw [Nat.cast_mul, Nat.cast_pow]
            ring
  rw [hrest, D.card_W₁]

end PTypeCoreGammaInternal

end

end Submission.OddOrder.PF
