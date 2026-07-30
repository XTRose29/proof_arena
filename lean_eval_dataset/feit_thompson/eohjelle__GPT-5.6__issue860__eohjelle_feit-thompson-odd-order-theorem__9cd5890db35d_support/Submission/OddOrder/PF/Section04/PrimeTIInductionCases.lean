import Mathlib.GroupTheory.GroupAction.SubMulAction
import Submission.OddOrder.MathlibSupport.PrimeOrderFixedPoint
import Submission.OddOrder.PF.Section04.PrimeTIReducedStructure

/-!
# The irreducible induction alternatives for a prime-TI kernel

This file ports the two assertions of Peterfalvi 4.5(b).  The main point is
that an irreducible character of the Frobenius kernel which is not one of the
selected restrictions has trivial inertia quotient, and hence induces
irreducibly.  As in the source, the inertia argument uses Brauer's permutation
lemma and a coprime fixed-point argument on conjugacy classes.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical
open Submission.OddOrder.MathlibSupport

universe u

/-! ## Brauer permutation for an arbitrary group automorphism -/

namespace PrimeTIInductionCasesAux

variable {G k : Type u} [Group G] [Fintype G]
  [Field k] [IsAlgClosed k] [CharZero k]

local instance : Invertible (Nat.card G : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

local instance : Fintype (ConjClasses G) := Fintype.ofFinite _
local instance : DecidableEq (ConjClasses G) := Classical.decEq _
local instance : DecidableEq (IrreducibleCharacter G k) := Classical.decEq _

/-- Pullback of class functions along a group automorphism, as a linear map. -/
private def classFunctionComapLinear (e : G ≃* G) :
    ClassFunction G k →ₗ[k] ClassFunction G k where
  toFun f :=
    ⟨fun g ↦ f (e g), fun x g ↦ by
      change f (e (x * g * x⁻¹)) = f (e g)
      rw [map_mul, map_mul, map_inv]
      exact ClassFunction.conj_apply f (e x) (e g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem classFunctionComapLinear_apply
    (e : G ≃* G) (f : ClassFunction G k) (g : G) :
    classFunctionComapLinear e f g = f (e g) :=
  rfl

/-- The row permutation which is intertwined with pullback along `e`. -/
private def irreduciblePermutationLinear (e : G ≃* G) :
    (IrreducibleCharacter G k → k) →ₗ[k]
      (IrreducibleCharacter G k → k) := by
  exact Matrix.toLin'
    (Equiv.Perm.permMatrix k
      (IrreducibleCharacter.equivOfMulEquiv e.symm))

@[simp]
private theorem irreduciblePermutationLinear_apply
    (e : G ≃* G) (a : IrreducibleCharacter G k → k)
    (chi : IrreducibleCharacter G k) :
    irreduciblePermutationLinear e a chi =
      a (IrreducibleCharacter.comapMulEquiv e.symm chi) := by
  rw [irreduciblePermutationLinear, Matrix.toLin'_apply,
    Matrix.permMatrix_mulVec]
  rfl

/-- The permutation induced by an automorphism on conjugacy classes. -/
def conjClassesEquiv (e : G ≃* G) :
    ConjClasses G ≃ ConjClasses G where
  toFun := ConjClasses.map e.toMonoidHom
  invFun := ConjClasses.map e.symm.toMonoidHom
  left_inv C := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
    change ConjClasses.mk (e.symm (e g)) = ConjClasses.mk g
    rw [e.symm_apply_apply]
  right_inv C := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
    change ConjClasses.mk (e (e.symm g)) = ConjClasses.mk g
    rw [e.apply_symm_apply]

@[simp]
private theorem conjClassesEquiv_mk (e : G ≃* G) (g : G) :
    conjClassesEquiv e (ConjClasses.mk g) = ConjClasses.mk (e g) :=
  rfl

/-- The corresponding permutation operator on conjugacy-class coordinates. -/
private def conjClassesPermutationLinear (e : G ≃* G) :
    (ConjClasses G → k) →ₗ[k] (ConjClasses G → k) := by
  exact Matrix.toLin' (Equiv.Perm.permMatrix k (conjClassesEquiv e))

@[simp]
private theorem conjClassesPermutationLinear_apply
    (e : G ≃* G) (a : ConjClasses G → k) (C : ConjClasses G) :
    conjClassesPermutationLinear e a C = a (conjClassesEquiv e C) := by
  rw [conjClassesPermutationLinear, Matrix.toLin'_apply,
    Matrix.permMatrix_mulVec]
  rfl

private theorem conjClassesLinearEquiv_conj_comap
    (e : G ≃* G) :
    (ClassFunction.conjClassesLinearEquiv (G := G) (k := k)).conj
        (classFunctionComapLinear (G := G) (k := k) e) =
      conjClassesPermutationLinear (G := G) (k := k) e := by
  apply LinearMap.ext
  intro f
  funext C
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
  rw [conjClassesPermutationLinear_apply]
  rfl

private theorem irreducibleCharacterSynthesis_comap
    (e : G ≃* G) (a : IrreducibleCharacter G k → k) :
    irreducibleCharacterSynthesis (irreduciblePermutationLinear e a) =
      classFunctionComapLinear e (irreducibleCharacterSynthesis a) := by
  ext g
  simp only [irreducibleCharacterSynthesis,
    Fintype.linearCombination_apply, irreduciblePermutationLinear_apply,
    classFunctionComapLinear_apply, ClassFunction.finset_sum_apply,
    ClassFunction.smul_apply, smul_eq_mul]
  apply Fintype.sum_equiv
    (IrreducibleCharacter.equivOfMulEquiv e.symm)
  intro chi
  change
    a (IrreducibleCharacter.comapMulEquiv e.symm chi) * chi g =
      a (IrreducibleCharacter.comapMulEquiv e.symm chi) *
        IrreducibleCharacter.comapMulEquiv e.symm chi (e g)
  rw [IrreducibleCharacter.comapMulEquiv_apply, e.symm_apply_apply]

private theorem irreducibleCharacterSynthesisEquiv_conj_comap
    (e : G ≃* G) :
    (irreducibleCharacterSynthesisEquiv
        (irreducibleCharacterComplete (G := G) (k := k))).conj
        (irreduciblePermutationLinear e) =
      classFunctionComapLinear e := by
  ext f g
  let a := (irreducibleCharacterSynthesisEquiv
    (irreducibleCharacterComplete (G := G) (k := k))).symm f
  have h := irreducibleCharacterSynthesis_comap (G := G) (k := k) e a
  simpa [irreducibleCharacterSynthesisEquiv, a,
    LinearEquiv.conj_apply_apply] using
      congrArg (fun q : ClassFunction G k ↦ q g) h

/-- Brauer's permutation lemma for a general automorphism: the fixed
irreducible rows and fixed conjugacy-class columns have equal cardinality. -/
theorem brauerPermutationCardinality_mulEquiv (e : G ≃* G) :
    (Function.fixedPoints
        (IrreducibleCharacter.equivOfMulEquiv (k := k) e.symm)).ncard =
      (Function.fixedPoints (conjClassesEquiv e)).ncard := by
  have hrow :
      LinearMap.trace k (IrreducibleCharacter G k → k)
          (irreduciblePermutationLinear e) =
        ((Function.fixedPoints
          (IrreducibleCharacter.equivOfMulEquiv
            (k := k) e.symm)).ncard : k) := by
    rw [irreduciblePermutationLinear, Matrix.trace_toLin'_eq,
      Matrix.trace_permutation]
  have hclass :
      LinearMap.trace k (ConjClasses G → k)
          (conjClassesPermutationLinear e) =
        ((Function.fixedPoints (conjClassesEquiv e)).ncard : k) := by
    rw [conjClassesPermutationLinear, Matrix.trace_toLin'_eq,
      Matrix.trace_permutation]
  have htrace₁ := LinearMap.trace_conj'
    (R := k) (classFunctionComapLinear e)
      (ClassFunction.conjClassesLinearEquiv (G := G) (k := k))
  rw [conjClassesLinearEquiv_conj_comap (G := G) (k := k) e] at htrace₁
  have htrace₂ := LinearMap.trace_conj'
    (R := k) (irreduciblePermutationLinear e)
      (irreducibleCharacterSynthesisEquiv
        (irreducibleCharacterComplete (G := G) (k := k)))
  rw [irreducibleCharacterSynthesisEquiv_conj_comap
    (G := G) (k := k) e] at htrace₂
  have hcast :
      ((Function.fixedPoints
        (IrreducibleCharacter.equivOfMulEquiv
          (k := k) e.symm)).ncard : k) =
        ((Function.fixedPoints (conjClassesEquiv e)).ncard : k) := by
    rw [← hrow, ← hclass, htrace₁, htrace₂]
  exact Nat.cast_injective hcast

/-! ## Fixed representatives of coprime invariant conjugacy classes -/

/-- Ambient conjugation acts on the conjugacy classes of a normal subgroup. -/
private def normalConjClassesMulAction
    {A : Type u} [Group A] (H : Subgroup A) [H.Normal] :
    MulAction A (ConjClasses H) where
  smul a C :=
    ConjClasses.map (MulAut.conjNormal a).toMonoidHom C
  one_smul C := by
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective C
    change ConjClasses.mk (MulAut.conjNormal 1 x) = ConjClasses.mk x
    congr 1
    apply Subtype.ext
    simp
  mul_smul a b C := by
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective C
    change ConjClasses.mk (MulAut.conjNormal (a * b) x) =
      ConjClasses.mk (MulAut.conjNormal a (MulAut.conjNormal b x))
    congr 1
    exact congrArg (fun q : MulAut H ↦ q x)
      (map_mul (MulAut.conjNormal (H := H)) a b)

private theorem natCard_conjClassCarrier_dvd
    (C : ConjClasses G) : Nat.card C.carrier ∣ Nat.card G := by
  obtain ⟨x, hx⟩ := ConjClasses.exists_rep C
  rw [← hx]
  letI : Fintype (MulAction.orbit (ConjAct G) x) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer (ConjAct G) x) :=
    Fintype.ofFinite _
  have horbit :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (ConjAct G) x
  have horbit' :
      Nat.card (MulAction.orbit (ConjAct G) x) *
          Nat.card (MulAction.stabilizer (ConjAct G) x) =
        Nat.card G := by
    simpa only [Nat.card_eq_fintype_card, ConjAct.card] using horbit
  rw [congrArg (fun S : Set G ↦ Nat.card S)
    (ConjAct.orbit_eq_carrier_conjClasses x)] at horbit'
  exact ⟨Nat.card (MulAction.stabilizer (ConjAct G) x), horbit'.symm⟩

/-- An automorphism of prime order, coprime to the normal subgroup, fixes a
representative of every invariant conjugacy class. -/
theorem exists_fixed_conjugacy_representative
    {A : Type u} [Group A] [Fintype A]
    (H : Subgroup A) [H.Normal] [Fintype H]
    (a : A) (hprime : (orderOf a).Prime)
    (hcop : (orderOf a).Coprime (Nat.card H))
    (C : ConjClasses H)
    (hC : conjClassesEquiv (MulAut.conjNormal a) C = C) :
    ∃ x : H, ConjClasses.mk x = C ∧ MulAut.conjNormal a x = x := by
  let P : Subgroup A := Subgroup.zpowers a
  letI : MulDistribMulAction P H :=
    MulDistribMulAction.compHom H
      ((MulAut.conjNormal (H := H)).comp P.subtype)
  letI : MulAction A (ConjClasses H) := normalConjClassesMulAction H
  have haC : a • C = C := hC
  let S : SubMulAction P H :=
    { carrier := C.carrier
      smul_mem' := by
        intro b x hx
        rw [ConjClasses.mem_carrier_iff_mk_eq] at hx ⊢
        have hbC : (b : A) • C = C :=
          smul_eq_self_of_mem_zpowers b.property haC
        change ConjClasses.mk (b • x) = C
        calc
          ConjClasses.mk (b • x) =
              (b : A) • ConjClasses.mk x := rfl
          _ = (b : A) • C := congrArg ((b : A) • ·) hx
          _ = C := hbC }
  have hS_carrier : (S : Set H) = C.carrier := by
    rfl
  have hcardSdvd : Nat.card S ∣ Nat.card H := by
    rw [← SetLike.coe_sort_coe S, hS_carrier]
    exact natCard_conjClassCarrier_dvd (G := H) C
  have hprimeP : (Nat.card P).Prime := by
    simpa only [P, Nat.card_zpowers] using hprime
  have hcopPS : (Nat.card P).Coprime (Nat.card S) := by
    rw [show Nat.card P = orderOf a by simp only [P, Nat.card_zpowers]]
    exact hcop.coprime_dvd_right hcardSdvd
  obtain ⟨y, hy⟩ :=
    nonempty_fixedPoints_of_prime_natCard
      (A := P) (X := S) hprimeP hcopPS
  let aP : P := ⟨a, Subgroup.mem_zpowers a⟩
  have hyfixS : aP • (y : S) = y :=
    (MulAction.mem_fixedPoints.mp hy) aP
  have hyfixH : MulAut.conjNormal a ((y : S) : H) = ((y : S) : H) := by
    have hval := congrArg (fun z : S ↦ (z : H)) hyfixS
    change MulAut.conjNormal (aP : A) ((y : S) : H) =
      ((y : S) : H) at hval
    simpa only [aP] using hval
  refine ⟨((y : S) : H), ?_, hyfixH⟩
  exact ConjClasses.mem_carrier_iff_mk_eq.mp (y : S).property

/-- The character obtained by ambient normal conjugation agrees with
pullback along the inverse inner automorphism. -/
theorem comap_conjNormal_symm
    {A : Type u} [Group A] [Fintype A]
    (H : Subgroup A) [H.Normal] [Fintype H]
    (a : A) (chi : IrreducibleCharacter H k) :
    IrreducibleCharacter.comapMulEquiv
        (MulAut.conjNormal a).symm chi =
      chi.normalConjugate H a := by
  apply IrreducibleCharacter.ext
  intro x
  rw [IrreducibleCharacter.comapMulEquiv_apply]
  rfl

/-- Restriction of an ambient class function is fixed by ambient
conjugation. -/
theorem normalConjugate_restrict
    {A : Type u} [Group A] [Fintype A]
    (H : Subgroup A) [H.Normal] [Fintype H]
    (a : A) (f : ClassFunction A k) :
    ClassFunction.normalConjugate H a (ClassFunction.restrict H f) =
      ClassFunction.restrict H f := by
  ext x
  rw [ClassFunction.normalConjugate_apply]
  change f (((MulAut.conjNormal a).symm x : H) : A) = f (x : A)
  simpa only [MulAut.conjNormal_symm_apply, inv_inv] using
    ClassFunction.conj_apply f a⁻¹ (x : A)

end PrimeTIInductionCasesAux

/-! ## Peterfalvi 4.5(b) -/

namespace PrimeTIHypothesis

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {L K W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}
  (h : PrimeTIHypothesis L K W W₁ W₂ defW)
  (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp)

local instance primeTIInductionCasesInvertibleCard
    {A : Type u} [Group A] [Fintype A] :
    Invertible (Nat.card A : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private theorem primeTI_Ires_normalConjugate
    [hKLNormal : (K.subgroupOf L).Normal]
    (a : L) (j : IrreducibleCharacter W₂ k) :
    (h.primeTI_Ires iso j).normalConjugate (K.subgroupOf L) a =
      h.primeTI_Ires iso j := by
  apply Subtype.ext
  rw [IrreducibleCharacter.coe_normalConjugate]
  rw [← h.cfRes_prTIirr iso
    (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k) j]
  exact PrimeTIInductionCasesAux.normalConjugate_restrict
    (K.subgroupOf L) a (h.primeTICharacter iso
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k) j)

/-- A fixed irreducible kernel character under a nonidentity complement
element belongs to the selected prime-TI family. -/
private theorem exists_primeTI_Ires_of_complement_fixed
    [hKLNormal : (K.subgroupOf L).Normal]
    (theta : IrreducibleCharacter (K.subgroupOf L) k)
    (z : L) (hzW₁ : z ∈ W₁.subgroupOf L) (hzne : z ≠ 1)
    (hztheta : theta.normalConjugate (K.subgroupOf L) z = theta) :
    ∃ j : IrreducibleCharacter W₂ k, theta = h.primeTI_Ires iso j := by
  let H : Subgroup L := K.subgroupOf L
  letI : H.Normal := hKLNormal
  have hzOrderNe : orderOf z ≠ (1 : ℕ) := by
    intro hzOrder
    exact hzne (orderOf_eq_one_iff.mp hzOrder)
  obtain ⟨p, hp, hpOrder⟩ := Nat.exists_prime_and_dvd
    hzOrderNe
  let m : ℕ := orderOf z / p
  let a : L := z ^ m
  have haOrder : orderOf a = p := by
    exact orderOf_pow_orderOf_div (orderOf_pos z).ne' hpOrder
  have haW₁ : a ∈ W₁.subgroupOf L := by
    exact (W₁.subgroupOf L).pow_mem hzW₁ m
  have hatheta : theta.normalConjugate H a = theta := by
    letI := IrreducibleCharacter.normalConjugationMulAction
      (k := k) H
    have haZ : a ∈ Subgroup.zpowers z := by
      exact (Subgroup.zpowers z).pow_mem (Subgroup.mem_zpowers z) m
    exact smul_eq_self_of_mem_zpowers haZ hztheta
  let e : H ≃* H := MulAut.conjNormal a
  let rowPerm : IrreducibleCharacter H k ≃ IrreducibleCharacter H k :=
    IrreducibleCharacter.equivOfMulEquiv e.symm
  let classPerm : ConjClasses H ≃ ConjClasses H :=
    PrimeTIInductionCasesAux.conjClassesEquiv e
  let FixedIrr := Function.fixedPoints rowPerm
  let FixedClass := Function.fixedPoints classPerm
  have hbrauer : Nat.card FixedIrr = Nat.card FixedClass := by
    exact PrimeTIInductionCasesAux.brauerPermutationCardinality_mulEquiv
      (G := H) (k := k) e
  let iresToFixed : IrreducibleCharacter W₂ k → FixedIrr := fun j ↦
    ⟨h.primeTI_Ires iso j, by
      change IrreducibleCharacter.comapMulEquiv e.symm
          (h.primeTI_Ires iso j) = h.primeTI_Ires iso j
      simpa only [e, H] using
        (PrimeTIInductionCasesAux.comap_conjNormal_symm
          (k := k) (K.subgroupOf L) a (h.primeTI_Ires iso j)).trans
          (h.primeTI_Ires_normalConjugate iso a j)⟩
  have hiResInjective : Function.Injective iresToFixed := by
    intro j r hjr
    exact h.prTIres_inj iso
      (congrArg (fun q : FixedIrr ↦ q.1) hjr)
  have haOrderGamma : orderOf ((a : L) : Gamma) = p := by
    exact (Subgroup.orderOf_coe a).trans haOrder
  let aW₁ : W₁ := ⟨((a : L) : Gamma), haW₁⟩
  have haW₁Order : orderOf (aW₁ : Gamma) = p := haOrderGamma
  have hpW₁ : p ∣ Nat.card W₁ := by
    rw [← haW₁Order]
    exact W₁.orderOf_dvd_natCard aW₁.property
  have hpHcop : p.Coprime (Nat.card H) := by
    rw [natCard_subgroupOf_eq h.kernel_le_group]
    exact (h.kernel_complement_card_coprime.coprime_dvd_right hpW₁).symm
  let fixedClassRep (C : FixedClass) : H := Classical.choose
    (PrimeTIInductionCasesAux.exists_fixed_conjugacy_representative
      H a (by simpa only [haOrder] using hp)
      (by simpa only [haOrder] using hpHcop) C.1 C.2)
  have fixedClassRep_spec (C : FixedClass) :
      ConjClasses.mk (fixedClassRep C) = C.1 ∧
        MulAut.conjNormal a (fixedClassRep C) = fixedClassRep C :=
    Classical.choose_spec
      (PrimeTIInductionCasesAux.exists_fixed_conjugacy_representative
        H a (by simpa only [haOrder] using hp)
        (by simpa only [haOrder] using hpHcop) C.1 C.2)
  let fixedClassToW₂ : FixedClass → W₂ := fun C ↦
    ⟨(((fixedClassRep C : H) : L) : Gamma), by
      have hxCommute : Commute (aW₁ : Gamma)
          (((fixedClassRep C : H) : L) : Gamma) := by
        have hfix := congrArg (fun y : H ↦ (((y : H) : L) : Gamma))
          (fixedClassRep_spec C).2
        rw [commute_iff_eq]
        exact mul_inv_eq_iff_eq_mul.mp (by
          simpa [aW₁, MulAut.conjNormal_apply, mul_assoc] using hfix)
      have hxCentralizer : (((fixedClassRep C : H) : L) : Gamma) ∈
          centralizerWithin K (Subgroup.zpowers (aW₁ : Gamma)) := by
        refine ⟨(fixedClassRep C).property, ?_⟩
        intro y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (hxCommute.zpow_left n).eq
      rw [h.centralizer_kernel aW₁ (by
        intro haone
        have haoneGamma : (aW₁ : Gamma) = 1 :=
          congrArg Subtype.val haone
        have : orderOf (aW₁ : Gamma) = 1 :=
          orderOf_eq_one_iff.mpr haoneGamma
        rw [haW₁Order] at this
        exact hp.ne_one this)] at hxCentralizer
      exact hxCentralizer⟩
  have hfixedClassInjective : Function.Injective fixedClassToW₂ := by
    intro C D hCD
    apply Subtype.ext
    have hrep : fixedClassRep C = fixedClassRep D := by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : W₂ ↦ (x : Gamma)) hCD
    exact (fixedClassRep_spec C).1.symm.trans
      ((congrArg ConjClasses.mk hrep).trans (fixedClassRep_spec D).1)
  have hcardFixedClass : Nat.card FixedClass ≤ Nat.card W₂ :=
    Nat.card_le_card_of_injective fixedClassToW₂ hfixedClassInjective
  letI : IsCyclic W₂ := h.fixed_cyclic
  have hcardFixed : Nat.card FixedIrr =
      Nat.card (IrreducibleCharacter W₂ k) := by
    apply Nat.le_antisymm
    · calc
        Nat.card FixedIrr = Nat.card FixedClass := hbrauer
        _ ≤ Nat.card W₂ := hcardFixedClass
        _ = Nat.card (IrreducibleCharacter W₂ k) := by
          simpa only [Nat.card_eq_fintype_card] using
            (IrreducibleCharacter.card_eq_natCard_of_isCyclic
              (C := W₂) (k := k)).symm
    · exact Nat.card_le_card_of_injective iresToFixed hiResInjective
  have hiResSurjective : Function.Surjective iresToFixed :=
    ((Nat.bijective_iff_injective_and_card iresToFixed).mpr
      ⟨hiResInjective, hcardFixed.symm⟩).2
  let thetaFixed : FixedIrr :=
    ⟨theta, by
      change IrreducibleCharacter.comapMulEquiv e.symm theta = theta
      simpa only [e, H] using
        (PrimeTIInductionCasesAux.comap_conjNormal_symm
          (k := k) (K.subgroupOf L) a theta).trans hatheta⟩
  obtain ⟨j, hj⟩ := hiResSurjective thetaFixed
  exact ⟨j, congrArg Subtype.val hj |>.symm⟩

/-- Peterfalvi 4.5(b), first assertion.  A kernel irreducible is either one
of the selected restrictions, or it induces irreducibly and is different
from every prime-TI rectangle entry. -/
theorem prTIres_irr_cases
    (theta : IrreducibleCharacter (K.subgroupOf L) k) :
    (∃ j : IrreducibleCharacter W₂ k, theta = h.primeTI_Ires iso j) ∨
      (IsIrreducibleCharacter L k
          (ClassFunction.induce (K.subgroupOf L)
            (theta : ClassFunction (K.subgroupOf L) k)) ∧
        ∀ (i : IrreducibleCharacter W₁ k)
          (j : IrreducibleCharacter W₂ k),
          ClassFunction.induce (K.subgroupOf L)
          (theta : ClassFunction (K.subgroupOf L) k) ≠
            h.primeTICharacter iso i j) := by
  classical
  letI : (K.subgroupOf L).Normal := h.kernel_normal
  let H : Subgroup L := K.subgroupOf L
  letI : H.Normal := by
    simpa only [H] using h.kernel_normal
  let C : Subgroup L := W₁.subgroupOf L
  by_cases himage : ∃ j : IrreducibleCharacter W₂ k,
      theta = h.primeTI_Ires iso j
  · exact Or.inl himage
  have hmeet : C ⊓ ClassFunction.inertia H
      (theta : ClassFunction H k) = ⊥ := by
    apply le_antisymm
    · intro z hz
      have hzC : z ∈ C := hz.1
      have hzI : z ∈ ClassFunction.inertia H
          (theta : ClassFunction H k) := hz.2
      have hzone : z = 1 := by
        by_contra hzne
        have hztheta : theta.normalConjugate H z = theta := by
          apply Subtype.ext
          exact (ClassFunction.mem_inertia_iff H
            (theta : ClassFunction H k) z).mp hzI
        obtain ⟨j, hj⟩ := h.exists_primeTI_Ires_of_complement_fixed
          iso theta z hzC hzne hztheta
        exact himage ⟨j, hj⟩
      simpa only [hzone] using (show (1 : L) ∈ (⊥ : Subgroup L) by simp)
    · exact bot_le
  have hinertiaLe : ClassFunction.inertia H
      (theta : ClassFunction H k) ≤ H := by
    intro x hxI
    obtain ⟨⟨a, b⟩, hab⟩ := h.semidirect_complement.2 x
    have haI : (a : L) ∈ ClassFunction.inertia H
        (theta : ClassFunction H k) :=
      ClassFunction.le_inertia H (theta : ClassFunction H k) a.property
    have hbI : (b : L) ∈ ClassFunction.inertia H
        (theta : ClassFunction H k) := by
      have hprod := (ClassFunction.inertia H
        (theta : ClassFunction H k)).mul_mem
          ((ClassFunction.inertia H
            (theta : ClassFunction H k)).inv_mem haI) hxI
      simpa only [← hab, inv_mul_cancel_left] using hprod
    have hbBot : (b : L) ∈ (⊥ : Subgroup L) := by
      rw [← hmeet]
      exact ⟨b.property, hbI⟩
    have hbone : (b : L) = 1 := Subgroup.mem_bot.mp hbBot
    have hx_eq_a : x = (a : L) := by
      calc
        x = (a : L) * (b : L) := hab.symm
        _ = (a : L) * 1 :=
          congrArg (fun y : L ↦ (a : L) * y) hbone
        _ = (a : L) := mul_one _
    exact hx_eq_a.symm ▸ a.property
  have hirr : IsIrreducibleCharacter L k
      (ClassFunction.induce H (theta : ClassFunction H k)) := by
    exact ClassFunction.inertia_Ind_irr H theta hinertiaLe
  refine Or.inr ⟨hirr, ?_⟩
  intro i j heq
  apply himage
  refine ⟨j, ?_⟩
  have hpair : characterPairing
      (ClassFunction.induce H (theta : ClassFunction H k))
      (h.primeTICharacter iso i j) = 1 := by
    rw [heq]
    exact IrreducibleCharacter.characterPairing_self
      (h.primeTIIndex iso (i, j))
  rw [ClassFunction.frobeniusReciprocity H,
    h.cfRes_prTIirr iso,
    IrreducibleCharacter.characterPairing_eq_ite] at hpair
  by_contra hne
  rw [if_neg hne] at hpair
  exact zero_ne_one hpair

/-- The reduced prime-TI column is never irreducible. -/
theorem prTIred_not_irr (j : IrreducibleCharacter W₂ k) :
    ¬ IsIrreducibleCharacter L k (h.primeTIRed iso j) := by
  intro hirr
  let mu : IrreducibleCharacter L k := ⟨h.primeTIRed iso j, hirr⟩
  have hnorm : characterPairing (h.primeTIRed iso j)
      (h.primeTIRed iso j) = 1 :=
    IrreducibleCharacter.characterPairing_self mu
  rw [h.cfnorm_prTIred iso] at hnorm
  have hcard : Nat.card W₁ = 1 := by
    apply Nat.cast_injective (R := k)
    simpa only [Nat.cast_one] using hnorm
  exact h.complement_ne_bot (Subgroup.card_eq_one.mp hcard)

private theorem exists_constituent_restrict
    (phi : IrreducibleCharacter L k) :
    ∃ theta : IrreducibleCharacter (K.subgroupOf L) k,
      theta.IsConstituent
        (ClassFunction.restrict (K.subgroupOf L)
          (phi : ClassFunction L k)) := by
  let H : Subgroup L := K.subgroupOf L
  let R : FDRep k H :=
    FDRep.restrictToSubgroup H phi.representation
  letI : CategoryTheory.Simple phi.representation :=
    phi.representation_simple
  letI : Nontrivial phi.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero phi.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  letI : Nontrivial R :=
    inferInstanceAs (Nontrivial phi.representation)
  obtain ⟨theta, htheta⟩ :=
    ClassFunction.exists_irreducible_constituent_of_nontrivial R
  refine ⟨theta, ?_⟩
  rw [← phi.ofRepresentation_representation,
    ← FDRep.ofRepresentation_restrictToSubgroup]
  exact htheta

/-- Peterfalvi 4.5(b), second assertion.  Every irreducible character of
`L` is either a prime-TI rectangle entry or is induced from a kernel
irreducible outside the selected family. -/
theorem prTIind_irr_cases (phi : IrreducibleCharacter L k) :
    (∃ (i : IrreducibleCharacter W₁ k)
      (j : IrreducibleCharacter W₂ k),
        phi = h.primeTIIndex iso (i, j)) ∨
      ∃ theta : IrreducibleCharacter (K.subgroupOf L) k,
        theta ∉ Set.range (h.primeTI_Ires iso) ∧
          (phi : ClassFunction L k) =
            ClassFunction.induce (K.subgroupOf L)
              (theta : ClassFunction (K.subgroupOf L) k) := by
  classical
  let H : Subgroup L := K.subgroupOf L
  obtain ⟨theta, htheta⟩ :=
    exists_constituent_restrict (K := K) (L := L) phi
  have hconstInd : phi.IsConstituent
      (ClassFunction.induce H (theta : ClassFunction H k)) :=
    (theta.isConstituent_restrict_iff_induce H phi).mp htheta
  rcases h.prTIres_irr_cases iso theta with ⟨j, hj⟩ | ⟨hirr, _⟩
  · have hpairRed : characterPairing (h.primeTIRed iso j)
        (phi : ClassFunction L k) ≠ 0 := by
      rw [← h.cfInd_prTIres iso, ← hj]
      exact hconstInd
    have hexists : ∃ i : IrreducibleCharacter W₁ k,
        h.primeTIIndex iso (i, j) = phi := by
      by_contra hnone
      have hne (i : IrreducibleCharacter W₁ k) :
          h.primeTIIndex iso (i, j) ≠ phi := by
        intro hi
        exact hnone ⟨i, hi⟩
      apply hpairRed
      rw [h.primeTIRed_eq_sum]
      change characterPairingRight (phi : ClassFunction L k)
        (∑ i : IrreducibleCharacter W₁ k,
          h.primeTICharacter iso i j) = 0
      rw [map_sum]
      change (∑ i : IrreducibleCharacter W₁ k,
        characterPairing
          (h.primeTIIndex iso (i, j) : ClassFunction L k)
          (phi : ClassFunction L k)) = 0
      simp [IrreducibleCharacter.characterPairing_eq_ite, hne]
    obtain ⟨i, hi⟩ := hexists
    exact Or.inl ⟨i, j, hi.symm⟩
  · let psi : IrreducibleCharacter L k :=
      ⟨ClassFunction.induce H (theta : ClassFunction H k), hirr⟩
    have hpsi : psi = phi := by
      by_contra hne
      apply hconstInd
      change characterPairing (psi : ClassFunction L k)
        (phi : ClassFunction L k) = 0
      rw [IrreducibleCharacter.characterPairing_eq_ite, if_neg hne]
    refine Or.inr ⟨theta, ?_, ?_⟩
    · rintro ⟨j, hj⟩
      have hredIrr : IsIrreducibleCharacter L k (h.primeTIRed iso j) := by
        rw [← h.cfInd_prTIres iso, hj]
        exact hirr
      exact h.prTIred_not_irr iso j hredIrr
    · exact congrArg Subtype.val hpsi |>.symm

end PrimeTIHypothesis

end

end Submission.OddOrder.PF
