import Submission.OddOrder.PF.Section09.PTypeCoreBounds
import Submission.OddOrder.PF.Section09.PTypeNonGaloisTwoCoordinate

/-!
# Peterfalvi Section 9: the rigid action-kernel calculation

This module carries out Peterfalvi (9.11.2).  A two-coordinate character
detects the index of the intersection of a selected pointwise action kernel
with a nontrivial translate.  In the rigid degree branch that index has only
two possible values, and the group action forces the intersection to be the
full action kernel in either case.

The declarations used by later core phases live in
`PTypeCoreActionKernelInternal`; this is implementation infrastructure rather
than an additional source-facing theorem layer.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section16
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open PTypeCoreContextInternal
open PTypeCoreBoundsInternal
open PTypeNonGaloisTwoCoordinateInternal
open scoped BigOperators Classical

universe u

namespace PTypeCoreActionKernelInternal

/-! ## Finite subgroup arithmetic -/

/-- Nested finite subgroups with the same ambient index are equal. -/
private theorem eq_of_le_of_index_eq
    {Q : Type u} [Group Q] [Finite Q]
    {A B : Subgroup Q} (hAB : A ≤ B)
    (hindex : A.index = B.index) :
    A = B := by
  apply le_antisymm hAB
  apply Subgroup.relIndex_eq_one.mp
  have hmul := A.relIndex_mul_index hAB
  have hBpos : 0 < B.index :=
    Nat.pos_of_ne_zero B.index_ne_zero_of_finite
  rw [hindex] at hmul
  exact Nat.mul_right_cancel hBpos (by simpa using hmul)

/-- The action-factor cardinality is the index of the full action kernel. -/
theorem pTypeCore_actionFactorCard_eq_C_index
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) :
    pTypeActionFactorCard D = D.C.index := by
  letI : D.C.Normal := D.C_normal
  unfold pTypeActionFactorCard
  exact D.C.index_eq_card.symm

/-- The action factor is no larger than the abelianization of the
complement.  Equality is precisely the rigid identity `C = U'`. -/
theorem pTypeCore_factorCard_le_derivedIndex
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁)
    (hD : PTypeFactorActionHypotheses D) :
    pTypeActionFactorCard D ≤ (_root_.commutator U).index ∧
      (pTypeActionFactorCard D = (_root_.commutator U).index ↔
        D.C = _root_.commutator U) := by
  have hdiv : D.C.index ∣ (_root_.commutator U).index :=
    Subgroup.index_dvd_of_le hD.commutator_le_C
  have hle : D.C.index ≤ (_root_.commutator U).index :=
    Nat.le_of_dvd
      (Nat.pos_of_ne_zero
        (_root_.commutator U).index_ne_zero_of_finite)
      hdiv
  rw [pTypeCore_actionFactorCard_eq_C_index D]
  refine ⟨hle, ?_⟩
  constructor
  · intro heq
    exact (eq_of_le_of_index_eq hD.commutator_le_C heq.symm).symm
  · intro hC
    rw [hC]

/-! ## The translated pointwise kernel -/

/-- Translating a pointwise kernel agrees with taking the pointwise kernel
of the translated constituent. -/
private theorem actionConjugate_pointwiseKernel_eq
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁)
    (L : Subgroup Hbar) (w : W₁) :
    actionConjugate D.W₁_action_U
        (pointwiseActionKernel D.U_action L) w =
      pointwiseActionKernel D.U_action
        (actionConjugate D.W₁_action L w) := by
  ext x
  rw [mem_actionConjugate_iff,
    D.mem_pointwiseActionKernel_actionConjugate_iff]
  simp

/-- If the index of `K ∩ Kʷ` is either the index of `C` or the index of
`K`, then a nonidentity `w` forces `K ∩ Kʷ = C`. -/
private theorem actionKernel_inf_eq_C_of_index_cases
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (data : TypePGaloisNonConclusion D)
    (w : W₁) (hw : w ≠ 1)
    (hindex :
      let K := pointwiseActionKernel D.U_action data.H₁
      let J := K ⊓ actionConjugate D.W₁_action_U K w
      J.index = D.C.index ∨ J.index = K.index) :
    let K := pointwiseActionKernel D.U_action data.H₁
    K ⊓ actionConjugate D.W₁_action_U K w = D.C := by
  classical
  letI : Fact (Nat.Prime D.q) := ⟨D.q_prime⟩
  let K := pointwiseActionKernel D.U_action data.H₁
  let Kw := actionConjugate D.W₁_action_U K w
  let J := K ⊓ Kw
  change J.index = D.C.index ∨ J.index = K.index at hindex
  change J = D.C
  rcases hindex with hJC | hJK
  · have hCJ : D.C = J :=
      eq_of_le_of_index_eq
        (pTypeNonGalois_C_le_twoCoordinateKernelInf D data w) hJC.symm
    exact hCJ.symm
  · have hJKer : J = K :=
      eq_of_le_of_index_eq inf_le_left hJK
    have hKleKw : K ≤ Kw := by
      rw [← hJKer]
      exact inf_le_right
    have hKwIndex : Kw.index = K.index := by
      simpa [Kw, actionConjugate] using
        Subgroup.index_map_equiv K (D.W₁_action_U w)
    have hKFixed : K = Kw :=
      eq_of_le_of_index_eq hKleKw hKwIndex.symm
    let Stab : Subgroup W₁ :=
      { carrier := {z |
          actionConjugate D.W₁_action_U K z = K}
        one_mem' := by simp
        mul_mem' := by
          intro x y hx hy
          change actionConjugate D.W₁_action_U K x = K at hx
          change actionConjugate D.W₁_action_U K y = K at hy
          change actionConjugate D.W₁_action_U K (x * y) = K
          rw [actionConjugate_mul, hy, hx]
        inv_mem' := by
          intro z hz
          change actionConjugate D.W₁_action_U K z = K at hz
          have hzinv :
              K = actionConjugate D.W₁_action_U K z⁻¹ := by
            calc
              K = actionConjugate D.W₁_action_U K (z⁻¹ * z) := by
                simp
              _ = actionConjugate D.W₁_action_U
                    (actionConjugate D.W₁_action_U K z) z⁻¹ :=
                actionConjugate_mul D.W₁_action_U K z⁻¹ z
              _ = actionConjugate D.W₁_action_U K z⁻¹ := by
                rw [hz]
          exact hzinv.symm }
    have hwStab : w ∈ Stab := by
      change actionConjugate D.W₁_action_U K w = K
      exact hKFixed.symm
    have hStabTop (z : W₁) :
        actionConjugate D.W₁_action_U K z = K := by
      change z ∈ Stab
      apply Subgroup.zpowers_le_of_mem hwStab
      rw [zpowers_eq_top_of_prime_card D.card_W₁ hw]
      exact Subgroup.mem_top z
    have hKleC : K ≤ D.C := by
      intro x hx
      rw [D.C_eq_iInf_pointwiseActionKernel_of_iSup_eq_top
        data.H₁ data.conjugates_direct.1, Subgroup.mem_iInf]
      intro z
      rw [← actionConjugate_pointwiseKernel_eq D data.H₁ z]
      rw [hStabTop z]
      exact hx
    have hCleK : D.C ≤ K :=
      (pTypeNonGalois_C_le_twoCoordinateKernelInf D data (1 : W₁)).trans
        inf_le_left
    have hCK : D.C = K := le_antisymm hCleK hKleC
    exact hJKer.trans hCK.symm

/-! ## Landing the two-coordinate character in the core family -/

set_option maxHeartbeats 1000000 in
/-- Inducing the two-coordinate character from `HU` to `M` produces a member
of the canonical core family with degree `q * [U : K ∩ Kʷ]`. -/
private theorem twoCoordinate_induced_member_degree
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (w : W₁) (hw : w ≠ 1) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    let K := pointwiseActionKernel D.U_action data.H₁
    let J := K ⊓ actionConjugate D.W₁_action_U K w
    ∃ phi : ClassFunction M ℂ,
      phi ∈ pTypeCoreFamilyOfContext ctx ∧
        phi 1 = ((D.q * J.index : ℕ) : ℂ) := by
  letI : Fintype G := pTypeCoreContextFintypeOfFinite G
  classical
  have hfacts : facts = Ptype_Fcore_factor_facts ctx :=
    Subsingleton.elim _ _
  subst facts
  let facts := Ptype_Fcore_factor_facts ctx
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀CPrime := pTypeCoreKernelDerivedComplement ctx
  let K := pointwiseActionKernel D.U_action data.H₁
  let J := K ⊓ actionConjugate D.W₁_action_U K w
  obtain ⟨s, hs, hsDegree⟩ :=
    pTypeNonGalois_twoCoordinate_coreCharacter
      ctx facts not_Galois w hw
  let phi : ClassFunction M ℂ :=
    ClassFunction.induce HU (s : ClassFunction HU ℂ)
  refine ⟨phi, ?_, ?_⟩
  · unfold pTypeCoreFamilyOfContext
    apply seqIndP.mpr
    refine ⟨s, ?_, rfl⟩
    simpa only [H, H₀CPrime, pTypeCoreFitting,
      pTypeCoreKernelDerivedComplement, pTypeH0CPrimeInDerived] using hs
  · have hsDegree' : Module.finrank ℂ s.representation = J.index := by
      simpa only [pTypeIrreducibleDegree] using hsDegree
    calc
      phi 1 = (HU.index : ℂ) * s 1 :=
        ClassFunction.induce_one HU _
      _ = (D.q : ℂ) * (J.index : ℂ) := by
        rw [pTypeCore_index_eq_q ctx facts,
          IrreducibleCharacter.apply_one_eq_finrank, hsDegree']
      _ = ((D.q * J.index : ℕ) : ℂ) := by
        rw [Nat.cast_mul]

/-! ## Character degrees force the action-kernel identity -/

/-- The two-coordinate degree and a two-valued core degree spectrum force
the translated-kernel intersection to be exactly `C`. -/
private theorem nonGalois_actionKernel_inf_eq
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (hdegree :
      let D := Ptype_factor_action ctx facts
      let hD := Ptype_factor_action_hypotheses ctx facts
      ∀ phi ∈ pTypeCoreFamilyOfContext ctx,
        phi 1 = ((D.q * pTypeActionFactorCard D : ℕ) : ℂ) ∨
          phi 1 = ((D.q * pTypeNonGaloisIndex hD not_Galois : ℕ) : ℂ))
    (w : W₁) (hw : w ≠ 1) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    let K := pointwiseActionKernel D.U_action data.H₁
    K ⊓ actionConjugate D.W₁_action_U K w = D.C := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let J := K ⊓ actionConjugate D.W₁_action_U K w
  change ∀ phi ∈ pTypeCoreFamilyOfContext ctx,
    phi 1 = ((D.q * pTypeActionFactorCard D : ℕ) : ℂ) ∨
      phi 1 = ((D.q * pTypeNonGaloisIndex hD not_Galois : ℕ) : ℂ)
    at hdegree
  change J = D.C
  have htwo :=
    twoCoordinate_induced_member_degree ctx facts not_Galois w hw
  change ∃ phi : ClassFunction M ℂ,
      phi ∈ pTypeCoreFamilyOfContext ctx ∧
        phi 1 = ((D.q * J.index : ℕ) : ℂ) at htwo
  obtain ⟨phi, hphi, hphiDegree⟩ := htwo
  have hindex :
      J.index = pTypeActionFactorCard D ∨
        J.index = pTypeNonGaloisIndex hD not_Galois := by
    rcases hdegree phi hphi with hqu | hqa
    · left
      apply Nat.mul_left_cancel D.q_prime.pos
      apply Nat.cast_injective (R := ℂ)
      exact hphiDegree.symm.trans hqu
    · right
      apply Nat.mul_left_cancel D.q_prime.pos
      apply Nat.cast_injective (R := ℂ)
      exact hphiDegree.symm.trans hqa
  apply actionKernel_inf_eq_C_of_index_cases data w hw
  rcases hindex with hqu | hqa
  · exact Or.inl (hqu.trans (pTypeCore_actionFactorCard_eq_C_index D))
  · exact Or.inr hqa

/-- The intersection identity gives the numerical bound `u ≤ a²`. -/
private theorem nonGalois_factorCard_le_index_sq
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (hdegree :
      let D := Ptype_factor_action ctx facts
      let hD := Ptype_factor_action_hypotheses ctx facts
      ∀ phi ∈ pTypeCoreFamilyOfContext ctx,
        phi 1 = ((D.q * pTypeActionFactorCard D : ℕ) : ℂ) ∨
          phi 1 = ((D.q * pTypeNonGaloisIndex hD not_Galois : ℕ) : ℂ)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    pTypeActionFactorCard D ≤ pTypeNonGaloisIndex hD not_Galois ^ 2 := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  have hW₁ : 1 < Nat.card W₁ := by
    rw [D.card_W₁]
    exact D.q_prime.one_lt
  letI : Nontrivial W₁ :=
    Finite.one_lt_card_iff_nontrivial.mp hW₁
  obtain ⟨w, hw⟩ := exists_ne (1 : W₁)
  let Kw := actionConjugate D.W₁_action_U K w
  let J := K ⊓ Kw
  have hTI := nonGalois_actionKernel_inf_eq
    ctx facts not_Galois hdegree w hw
  change J = D.C at hTI
  have hKwIndex : Kw.index = K.index := by
    simpa [Kw, actionConjugate] using
      Subgroup.index_map_equiv K (D.W₁_action_U w)
  calc
    pTypeActionFactorCard D = D.C.index :=
      pTypeCore_actionFactorCard_eq_C_index D
    _ = J.index := by rw [hTI]
    _ ≤ K.index * Kw.index := Subgroup.index_inf_le
    _ = K.index ^ 2 := by rw [hKwIndex, pow_two]
    _ = pTypeNonGaloisIndex hD not_Galois ^ 2 := rfl

/-! ## Divisibility and parity consequences -/

/-- The selected pointwise-kernel index divides the full action-factor
cardinality. -/
theorem pTypeCore_nonGalois_index_dvd_factorCard
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    pTypeNonGaloisIndex
        (Ptype_factor_action_hypotheses ctx facts) not_Galois ∣
      pTypeActionFactorCard (Ptype_factor_action ctx facts) := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  have hCK : D.C ≤ K :=
    (pTypeNonGalois_C_le_twoCoordinateKernelInf D data (1 : W₁)).trans
      inf_le_left
  calc
    pTypeNonGaloisIndex hD not_Galois = K.index := rfl
    _ ∣ D.C.index := Subgroup.index_dvd_of_le hCK
    _ = pTypeActionFactorCard D :=
      (pTypeCore_actionFactorCard_eq_C_index D).symm

/-- Oddness of `a` forces the cofactor in `a ∣ p - 1` to be even.  Hence
`2a ≤ p - 1`, with the expected equality criterion. -/
theorem pTypeCore_twice_index_le_prime_pred
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let a := pTypeNonGaloisIndex hD not_Galois
    2 * a ≤ D.p - 1 ∧
      (2 * a = D.p - 1 ↔ a = (D.p - 1) / 2) := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let a := pTypeNonGaloisIndex hD not_Galois
  have hFactorOdd : Odd (Nat.card (ptypeFCoreFactor ctx)) := by
    have hFodd : Odd (Nat.card (Fitting_core M)) :=
      odd_natCard_subgroup (Fitting_core M)
        IsMinSimpleOddGroup.odd_card
    exact odd_natCard_quotient
      ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)) hFodd
  have hpOdd : Odd D.p := by
    have hH₁Odd : Odd (Nat.card data.H₁) :=
      odd_natCard_subgroup data.H₁ hFactorOdd
    simpa only [data.card_H₁] using hH₁Odd
  have huOdd : Odd (pTypeActionFactorCard D) := by
    unfold pTypeActionFactorCard
    exact odd_natCard_quotient D.C
      (mFT_odd U)
  have haDvdU : a ∣ pTypeActionFactorCard D :=
    pTypeCore_nonGalois_index_dvd_factorCard ctx facts not_Galois
  have haOdd : Odd a := huOdd.of_dvd_nat haDvdU
  obtain ⟨k, hk⟩ := data.index_dvd_prime_pred
  have hk' : D.p - 1 = a * k := by
    simpa only [a, pTypeNonGaloisIndex] using hk
  have hpPredEven : Even (D.p - 1) :=
    Nat.Odd.sub_odd hpOdd odd_one
  have hkEven : 2 ∣ k := by
    have htwoMul : 2 ∣ a * k := by
      rw [← hk']
      exact even_iff_two_dvd.mp hpPredEven
    exact haOdd.coprime_two_right.symm.dvd_of_dvd_mul_left htwoMul
  have hkPos : 0 < k := by
    have hpPredPos : 0 < D.p - 1 :=
      Nat.sub_pos_of_lt D.p_prime.one_lt
    rw [hk'] at hpPredPos
    exact Nat.pos_of_mul_pos_left hpPredPos
  have hkTwo : 2 ≤ k := Nat.le_of_dvd hkPos hkEven
  have hle : 2 * a ≤ D.p - 1 := by
    rw [hk']
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left a hkTwo
  refine ⟨hle, ?_⟩
  have htwoDvd : 2 ∣ D.p - 1 := even_iff_two_dvd.mp hpPredEven
  constructor
  · intro heq
    apply (Nat.eq_div_iff_mul_eq_left
      (by decide : 2 ≠ 0) htwoDvd).2
    simpa only [Nat.mul_comm] using heq.symm
  · intro haHalf
    have hmul :=
      (Nat.eq_div_iff_mul_eq_left
        (by decide : 2 ≠ 0) htwoDvd).1 haHalf
    simpa only [Nat.mul_comm] using hmul.symm

/-! ## Stable rigid-branch interface -/

namespace PTypeCoreRigidFacts

/-- Rigid specialization of the translated action-kernel identity. -/
theorem actionKernel_inf_eq
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {S₂ : Finset (ClassFunction M ℂ)}
    (rigid : PTypeCoreBoundsInternal.PTypeCoreRigidFacts
      ctx facts not_Galois S₂)
    (w : W₁) (hw : w ≠ 1) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    let K := pointwiseActionKernel D.U_action data.H₁
    K ⊓ actionConjugate D.W₁_action_U K w = D.C := by
  exact nonGalois_actionKernel_inf_eq ctx facts not_Galois
    (PTypeCoreBoundsInternal.PTypeCoreRigidFacts.degree_cases rigid) w hw

/-- Rigid specialization of the numerical conclusion `u ≤ a²`. -/
theorem factorCard_le_index_sq
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {S₂ : Finset (ClassFunction M ℂ)}
    (rigid : PTypeCoreBoundsInternal.PTypeCoreRigidFacts
      ctx facts not_Galois S₂) :
    pTypeActionFactorCard (Ptype_factor_action ctx facts) ≤
      pTypeNonGaloisIndex
          (Ptype_factor_action_hypotheses ctx facts) not_Galois ^ 2 := by
  exact nonGalois_factorCard_le_index_sq ctx facts not_Galois
    (PTypeCoreBoundsInternal.PTypeCoreRigidFacts.degree_cases rigid)

/-- The extension scale `u / a` is nontrivial in the rigid branch. -/
theorem one_lt_factorCard_div_index
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {S₂ : Finset (ClassFunction M ℂ)}
    (rigid : PTypeCoreBoundsInternal.PTypeCoreRigidFacts
      ctx facts not_Galois S₂) :
    1 < pTypeActionFactorCard (Ptype_factor_action ctx facts) /
      pTypeNonGaloisIndex
        (Ptype_factor_action_hypotheses ctx facts) not_Galois := by
  have hdvd := pTypeCore_nonGalois_index_dvd_factorCard
    ctx facts not_Galois
  obtain ⟨m, hm⟩ := hdvd
  have haPos : 0 < pTypeNonGaloisIndex
      (Ptype_factor_action_hypotheses ctx facts) not_Galois :=
    Nat.zero_lt_of_lt (one_lt_pTypeNonGaloisIndex
      (Ptype_factor_action_hypotheses ctx facts) not_Galois)
  have huPos : 0 < pTypeActionFactorCard
      (Ptype_factor_action ctx facts) := by
    unfold pTypeActionFactorCard
    exact Nat.card_pos
  have hmPos : 0 < m := by
    by_contra hmNotPos
    have hmZero : m = 0 := Nat.eq_zero_of_not_pos hmNotPos
    rw [hmZero, mul_zero] at hm
    omega
  have hmNeOne : m ≠ 1 := by
    intro hmOne
    apply rigid.forced_degrees_ne
    rw [hm, hmOne, mul_one]
  have hmGtOne : 1 < m := by omega
  calc
    1 < m := hmGtOne
    _ = pTypeActionFactorCard (Ptype_factor_action ctx facts) /
        pTypeNonGaloisIndex
          (Ptype_factor_action_hypotheses ctx facts) not_Galois := by
      rw [hm, Nat.mul_comm, Nat.mul_div_left m haPos]

/-- The rigid degree slice contains a character. -/
theorem exists_slice_character
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {S₂ : Finset (ClassFunction M ℂ)}
    (rigid : PTypeCoreBoundsInternal.PTypeCoreRigidFacts
      ctx facts not_Galois S₂) :
    ∃ psi, psi ∈ S₂ := by
  have hdvd := pTypeCore_nonGalois_index_dvd_factorCard
    ctx facts not_Galois
  have hscale := one_lt_factorCard_div_index rigid
  apply Finset.card_pos.mp
  rw [rigid.slice_card_two, Nat.mul_div_assoc 2 hdvd]
  omega

end PTypeCoreRigidFacts

end PTypeCoreActionKernelInternal

end

end Submission.OddOrder.PF
