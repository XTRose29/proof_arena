import Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary
import Submission.OddOrder.PF.Section01.InertiaInductionCorrespondence
import Submission.OddOrder.PF.Section01.IrreducibleCharacterTransport
import Submission.OddOrder.PF.Section01.MulCharacterTwist
import Submission.OddOrder.PF.Section01.NonzeroCharacterConstituent
import Submission.OddOrder.PF.Section01.NormalSubgroupConstituentKernels
import Submission.OddOrder.PF.Section01.QuotientDescent
import Submission.OddOrder.PF.Section03.DirectProductCharacters
import Submission.OddOrder.PF.Section05.SeqIndGlobal
import Submission.OddOrder.PF.Section08.FTSupportPartition
import Submission.OddOrder.PF.Section09.PTypeFCoreKernel
import Submission.OddOrder.PF.Section09.PTypeGaloisAction

/-!
# Peterfalvi Section 9: non-Galois character infrastructure

This module supplies the character predicates, canonical subgroup models, and
elementary index arithmetic shared by the proof phases of Peterfalvi (9.8).
The quotient-character and coordinate-character arguments live in downstream
modules.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15

universe u

/-! ## Character families -/

/-- The degree of an irreducible complex character. -/
def pTypeIrreducibleDegree
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) : ℕ :=
  Module.finrank ℂ chi.representation

/-- A class function is an irreducible character of a prescribed degree. -/
def pTypeIsIrreducibleOfDegree
    {Q : Type u} [Group Q] [Fintype Q]
    (n : ℕ) (zeta : ClassFunction Q ℂ) : Prop :=
  ∃ chi : IrreducibleCharacter Q ℂ,
    (chi : ClassFunction Q ℂ) = zeta ∧
      pTypeIrreducibleDegree chi = n

/-- The reducible members of the Dade-induced family from `H₀` over `H`. -/
def pTypeReducibleLayer
    {M : Type u} [Group M] [Fintype M]
    (HU : Subgroup M) (H H₀ : Subgroup HU) :
    Finset (ClassFunction M ℂ) :=
  (seqIndD (k := ℂ) HU H H₀).filter fun zeta ↦
    ¬ IsIrreducibleCharacter M ℂ zeta

/-- The intrinsic linear-character predicate. -/
def pTypeIsLinearCharacter
    {Q : Type u} [Group Q] [Fintype Q]
    (xi : IrreducibleCharacter Q ℂ) : Prop :=
  pTypeIrreducibleDegree xi = 1

/-- The predicate called `isIndHC` in Peterfalvi (9.8). -/
def pTypeIsIndHC
    {M : Type u} [Group M] [Fintype M]
    (HU : Subgroup M) (H H₀C : Subgroup HU) (HC : Subgroup M)
    (q u : ℕ) (zeta : ClassFunction M ℂ) : Prop :=
  zeta 1 = ((q * u : ℕ) : ℂ) ∧
    zeta ∈ seqIndD (k := ℂ) HU H H₀C ∧
      ∃ xi : IrreducibleCharacter HC ℂ,
        pTypeIsLinearCharacter xi ∧
          zeta = ClassFunction.induce HC (xi : ClassFunction HC ℂ)

namespace internal


/-- Complement decompositions transport across group equivalences. -/
theorem pTypeIsComplement_map_mulEquiv
    {A B : Type u} [Group A] [Finite A]
    [Group B] [Finite B]
    {N C : Subgroup A} (hNC : N.IsComplement' C)
    (e : A ≃* B) :
    (N.map e.toMonoidHom).IsComplement'
      (C.map e.toMonoidHom) := by
  apply Subgroup.isComplement'_of_card_mul_and_disjoint
  · rw [Subgroup.card_map_of_injective e.injective,
      Subgroup.card_map_of_injective e.injective,
      hNC.card_mul]
    exact Nat.card_congr e.toEquiv
  · exact Subgroup.disjoint_map e.injective hNC.disjoint

/-- Restrict a complement decomposition to a subgroup containing its left
factor. -/
theorem pTypeIsComplement_subgroupOf_of_left_le
    {A : Type u} [Group A]
    {N C T : Subgroup A}
    (hNC : N.IsComplement' C) (hNT : N ≤ T) :
    (N.subgroupOf T).IsComplement'
      ((C ⊓ T).subgroupOf T) := by
  change Function.Bijective
    (fun x : (N.subgroupOf T) × ((C ⊓ T).subgroupOf T) ↦
      (x.1 : T) * (x.2 : T))
  constructor
  · intro x y hxy
    let xA : N × C :=
      (⟨((x.1 : T) : A), x.1.property⟩,
        ⟨((x.2 : T) : A), x.2.property.1⟩)
    let yA : N × C :=
      (⟨((y.1 : T) : A), y.1.property⟩,
        ⟨((y.2 : T) : A), y.2.property.1⟩)
    have hxyA : (xA.1 : A) * (xA.2 : A) =
        (yA.1 : A) * (yA.2 : A) :=
      congrArg Subtype.val hxy
    have hpair : xA = yA := hNC.1 hxyA
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : N × C ↦ (z.1 : A)) hpair
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : N × C ↦ (z.2 : A)) hpair
  · intro t
    obtain ⟨⟨n, c⟩, hnc⟩ := hNC.2 (t : A)
    have hcT : (c : A) ∈ T := by
      have hcEq : (c : A) = (n : A)⁻¹ * (t : A) := by
        rw [← hnc]
        simp
      rw [hcEq]
      exact T.mul_mem (T.inv_mem (hNT n.property)) t.property
    let nT : N.subgroupOf T :=
      ⟨⟨(n : A), hNT n.property⟩, n.property⟩
    let cT : (C ⊓ T).subgroupOf T :=
      ⟨⟨(c : A), hcT⟩, ⟨c.property, hcT⟩⟩
    refine ⟨(nT, cT), ?_⟩
    apply Subtype.ext
    exact hnc

/-- In a finite complement decomposition `A = N C`, every subgroup `T`
containing `N` has the same ambient index as `T ∩ C` has in `C`. -/
theorem pTypeIndex_eq_relIndex_of_isComplement_of_left_le
    {A : Type u} [Group A] [Finite A]
    {N C T : Subgroup A}
    (hNC : N.IsComplement' C) (hNT : N ≤ T) :
    T.index = T.relIndex C := by
  have hNCT := pTypeIsComplement_subgroupOf_of_left_le hNC hNT
  have hNrel : N.relIndex T = Nat.card ↑(C ⊓ T) := by
    change (N.subgroupOf T).index = Nat.card ↑(C ⊓ T)
    calc
      (N.subgroupOf T).index =
          Nat.card ((C ⊓ T).subgroupOf T) :=
        hNCT.symm.index_eq_card
      _ = Nat.card ↑(C ⊓ T) :=
        natCard_subgroupOf_eq inf_le_right
  have hNindex : N.index = Nat.card C :=
    hNC.symm.index_eq_card
  have hleft : Nat.card ↑(C ⊓ T) * T.index = Nat.card C := by
    calc
      Nat.card ↑(C ⊓ T) * T.index =
          N.relIndex T * T.index := by rw [hNrel]
      _ = N.index := Subgroup.relIndex_mul_index hNT
      _ = Nat.card C := hNindex
  have hright : Nat.card ↑(C ⊓ T) * T.relIndex C =
      Nat.card C := by
    calc
      Nat.card ↑(C ⊓ T) * T.relIndex C =
          T.relIndex C * Nat.card ↑(T ⊓ C) := by
            rw [mul_comm, inf_comm]
      _ = (T ⊓ C).relIndex C * Nat.card ↑(T ⊓ C) := by
            rw [Subgroup.inf_relIndex_right]
      _ = ((T ⊓ C).subgroupOf C).index *
          Nat.card ↑(T ⊓ C) := rfl
      _ = ((T ⊓ C).subgroupOf C).index *
          Nat.card ((T ⊓ C).subgroupOf C) := by
            rw [natCard_subgroupOf_eq inf_le_right]
      _ = Nat.card C :=
        ((T ⊓ C).subgroupOf C).index_mul_card
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.card_pos (α := ↑(C ⊓ T))) (hleft.trans hright.symm)

/-- The F-core kernel enlarged by the complement action kernel intersects the
F-core in the original F-core kernel. -/
theorem pTypeFcoreKernel_sup_complKernel_inf_Fcore
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (Ptype_Fcore_kernel ctx ⊔ Ptype_Fcompl_kernel ctx) ⊓
        Fitting_core M =
      Ptype_Fcore_kernel ctx := by
  let H₀ := Ptype_Fcore_kernel ctx
  let H := Fitting_core M
  let C := Ptype_Fcompl_kernel ctx
  have hH₀H : H₀ ≤ H := (Ptype_Fcore_kernel_lt ctx).le
  have hHM : H ≤ M := Fcore_sub M
  have hCM : C ≤ M :=
    (Ptype_Fcompl_kernel_le ctx).trans
      (ctx.typeP.2.1.2.1.trans ctx.typeP.1.2.2.2.1)
  have hH₀M : H₀ ≤ M := hH₀H.trans hHM
  have hHder : H ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hdisHU : Disjoint H U := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    let xD : derivedWithin M := ⟨x, hHder hx.1⟩
    have hxD : xD ∈
        (H.subgroupOf (derivedWithin M)) ⊓
          (U.subgroupOf (derivedWithin M)) :=
      ⟨hx.1, hx.2⟩
    have hxBot : xD ∈ (⊥ : Subgroup (derivedWithin M)) :=
      ctx.typeP.2.1.2.2.2.2.2.2.disjoint.le_bot hxD
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxBot)
  have hdisHC : Disjoint H C :=
    hdisHU.mono le_rfl (Ptype_Fcompl_kernel_le ctx)
  let H₀M : Subgroup M := H₀.subgroupOf M
  let HM : Subgroup M := H.subgroupOf M
  let CM : Subgroup M := C.subgroupOf M
  letI : H₀M.Normal := by
    simpa only [H₀M, H₀] using Ptype_Fcore_kernel_normal_M ctx
  apply le_antisymm
  · intro x hx
    let xM : M := ⟨x, hHM hx.2⟩
    have hxSupM : xM ∈ H₀M ⊔ CM := by
      rw [← Subgroup.subgroupOf_sup hH₀M hCM]
      exact hx.1
    obtain ⟨h₀, hh₀, c, hc, hh₀c⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hxSupM
    have hh₀H : h₀ ∈ HM := hH₀H hh₀
    have hxHM : xM ∈ HM := hx.2
    have hcEq : c = h₀⁻¹ * xM := by
      rw [← hh₀c]
      simp
    have hcH : (c : Gamma) ∈ H := by
      rw [hcEq]
      exact HM.mul_mem (HM.inv_mem hh₀H) hxHM
    have hcBot : (c : Gamma) ∈ (⊥ : Subgroup Gamma) := by
      rw [← disjoint_iff.mp hdisHC]
      exact ⟨hcH, hc⟩
    have hcOne : c = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.mp hcBot
    have hxEq : x = (h₀ : Gamma) := by
      have hxMEq : xM = h₀ := by
        rw [← hh₀c, hcOne, mul_one]
      exact congrArg Subtype.val hxMEq
    rw [hxEq]
    exact hh₀
  · intro x hx
    have hxSup : x ∈ H₀ ⊔ C :=
      (show H₀ ≤ H₀ ⊔ C from le_sup_left) hx
    exact ⟨hxSup, hH₀H hx⟩

/-- Induction multiplies an irreducible character degree by the subgroup
index.  This is shared with the fixed-degree phase. -/
theorem pTypeIrreducibleDegree_eq_index_mul_of_induced
    {Q : Type u} [Group Q] [Fintype Q]
    (T : Subgroup Q) (psi : IrreducibleCharacter T ℂ)
    (chi : IrreducibleCharacter Q ℂ)
    (hchi : (chi : ClassFunction Q ℂ) =
      ClassFunction.induce T (psi : ClassFunction T ℂ)) :
    pTypeIrreducibleDegree chi =
      T.index * pTypeIrreducibleDegree psi := by
  apply Nat.cast_injective (R := ℂ)
  change (Module.finrank ℂ chi.representation : ℂ) =
    ((T.index * Module.finrank ℂ psi.representation : ℕ) : ℂ)
  rw [← IrreducibleCharacter.apply_one_eq_finrank, hchi,
    ClassFunction.induce_one,
    IrreducibleCharacter.apply_one_eq_finrank, Nat.cast_mul]

/-- An index divisor of an inducing subgroup also divides the induced
irreducible degree. -/
theorem pTypeIrreducibleDegree_dvd_of_inertiaIndex_dvd
    {Q : Type u} [Group Q] [Fintype Q]
    (T : Subgroup Q) (psi : IrreducibleCharacter T ℂ)
    (chi : IrreducibleCharacter Q ℂ)
    (hchi : (chi : ClassFunction Q ℂ) =
      ClassFunction.induce T (psi : ClassFunction T ℂ))
    {a : ℕ} (ha : a ∣ T.index) :
    a ∣ pTypeIrreducibleDegree chi := by
  rw [pTypeIrreducibleDegree_eq_index_mul_of_induced T psi chi hchi]
  exact dvd_mul_of_dvd_left ha _

end internal

/-- The numerator `(p - 1) * |U|` in the lower bound of clause (d). -/
def pTypeNonGaloisLowerNumerator
    {M : Type u} [Group M] [Fintype M]
    (p : ℕ) (U : Subgroup M) : ℕ :=
  (p - 1) * Nat.card U

/-- The denominator `a² * |U'|` in the lower bound of clause (d). -/
def pTypeNonGaloisLowerDenominator
    {M : Type u} [Group M] [Fintype M]
    (a : ℕ) (U' : Subgroup M) : ℕ :=
  a ^ 2 * Nat.card U'

/-- The number of degree-`q * a` irreducibles in the indicated Dade family. -/
def pTypeNonGaloisDegreeCount
    {M : Type u} [Group M] [Fintype M]
    (HU : Subgroup M) (H H₀U' : Subgroup HU) (q a : ℕ) : ℕ :=
  ((seqIndD (k := ℂ) HU H H₀U').filter fun zeta ↦
    pTypeIsIrreducibleOfDegree (q * a) zeta).card

/-! ## Canonical subgroup models -/

/-- The derived subgroup `HU`, viewed inside the maximal subgroup. -/
abbrev pTypeHUInMaximal
    {Gamma : Type u} [Group Gamma]
    (L K : Subgroup Gamma) : Subgroup L :=
  K.subgroupOf L

/-- The Fitting subgroup `H`, viewed inside `HU`. -/
abbrev pTypeHInDerived
    {Gamma : Type u} [Group Gamma]
    (L K H : Subgroup Gamma) : Subgroup (pTypeHUInMaximal L K) :=
  (H.subgroupOf L).subgroupOf (pTypeHUInMaximal L K)

/-- The subgroup `H₀`, viewed inside `HU`. -/
abbrev pTypeH0InDerived
    {Gamma : Type u} [Group Gamma]
    (L K H₀ : Subgroup Gamma) : Subgroup (pTypeHUInMaximal L K) :=
  (H₀.subgroupOf L).subgroupOf (pTypeHUInMaximal L K)

/-- The subgroup `H₀C`, formed inside `HU`. -/
def pTypeH0CInDerived
    {Gamma : Type u} [Group Gamma]
    (L K H₀ U W₁ : Subgroup Gamma)
    {Hbar : Type u} [Group Hbar] [Finite Hbar]
    [Finite U] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) :
    Subgroup (pTypeHUInMaximal L K) :=
  pTypeH0InDerived L K H₀ ⊔
    ((D.C.map U.subtype).subgroupOf L).subgroupOf
      (pTypeHUInMaximal L K)

/-- The concrete chief factor `H / H₀`. -/
abbrev pTypeNonGaloisChiefFactor
    {Gamma : Type u} [Group Gamma]
    (L H H₀ : Subgroup Gamma)
    [((H₀.subgroupOf L).subgroupOf (H.subgroupOf L)).Normal] :=
  H.subgroupOf L ⧸
    (H₀.subgroupOf L).subgroupOf (H.subgroupOf L)

/-- Map the action kernel from the complement into the maximal subgroup. -/
def pTypeActionKernelInMaximal
    {L U W₁ Hbar : Type u}
    [Group L] [Group U] [Group W₁] [Group Hbar]
    [Finite Hbar] [Finite U] [Finite W₁]
    (UinL : U →* L) (D : PTypeFactorActionData Hbar U W₁) : Subgroup L :=
  D.C.map UinL

/-- The order `|U / C|` of the complement's faithful action factor. -/
def pTypeActionFactorCard
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) : ℕ := by
  letI : D.C.Normal := D.C_normal
  exact Nat.card (U ⧸ D.C)

/-! ## The non-Galois index and lower-bound arithmetic -/

/-- The index of the pointwise stabilizer selected by the non-Galois
alternative. -/
def pTypeNonGaloisIndex
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (hD : PTypeFactorActionHypotheses D)
    (not_Galois : ¬ typeP_Galois D) : ℕ :=
  let data := typeP_Galois_Pn hD not_Galois
  (pointwiseActionKernel D.U_action data.H₁).index

/-- The selected non-Galois index is nontrivial. -/
theorem one_lt_pTypeNonGaloisIndex
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (hD : PTypeFactorActionHypotheses D)
    (not_Galois : ¬ typeP_Galois D) :
    1 < pTypeNonGaloisIndex hD not_Galois :=
  (typeP_Galois_Pn hD not_Galois).index_gt_one

/-- The selected non-Galois index divides `p - 1`. -/
theorem pTypeNonGaloisIndex_dvd_prime_pred
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (hD : PTypeFactorActionHypotheses D)
    (not_Galois : ¬ typeP_Galois D) :
    pTypeNonGaloisIndex hD not_Galois ∣ D.p - 1 :=
  (typeP_Galois_Pn hD not_Galois).index_dvd_prime_pred

/-- The commutator subgroup lies in the selected pointwise action kernel. -/
theorem pTypeDerived_le_nonGaloisActionKernel
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (hD : PTypeFactorActionHypotheses D)
    (not_Galois : ¬ typeP_Galois D) :
    _root_.commutator U ≤
      pointwiseActionKernel D.U_action
        (typeP_Galois_Pn hD not_Galois).H₁ := by
  let data := typeP_Galois_Pn hD not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  letI : K.Normal := data.actionKernel_normal
  letI : IsCyclic (U ⧸ K) := by
    change IsCyclic
      (U ⧸ pointwiseActionKernel D.U_action data.H₁)
    exact data.pointwise_factor_cyclic
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    (show IsMulCommutative (U ⧸ K) from inferInstance)

/-- Lagrange arithmetic for the divisibility half of clause (d). -/
theorem pTypeLowerDenominator_dvd_of_le
    {U : Type u} [Group U] [Finite U]
    (K U' : Subgroup U) (p a : ℕ)
    (hindex : K.index = a)
    (ha : a ∣ p - 1)
    (hU'K : U' ≤ K) :
    a ^ 2 * Nat.card U' ∣ (p - 1) * Nat.card U := by
  obtain ⟨c, hc⟩ := ha
  refine ⟨c * (U'.subgroupOf K).index, ?_⟩
  calc
    (p - 1) * Nat.card U = (a * c) * (a * Nat.card K) := by
      rw [hc, ← K.index_mul_card, hindex]
    _ = (a ^ 2 * Nat.card U') *
        (c * (U'.subgroupOf K).index) := by
      rw [← (U'.subgroupOf K).card_mul_index,
        natCard_subgroupOf_eq hU'K]
      ring

/-- Clause (d)'s divisibility before transporting the complement into the
maximal-subgroup type. -/
theorem pTypeNonGaloisLowerDenominator_dvd_internal
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (hD : PTypeFactorActionHypotheses D)
    (not_Galois : ¬ typeP_Galois D) :
    pTypeNonGaloisIndex hD not_Galois ^ 2 *
        Nat.card (_root_.commutator U) ∣
      (D.p - 1) * Nat.card U := by
  let data := typeP_Galois_Pn hD not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  change K.index ^ 2 * Nat.card (_root_.commutator U) ∣
    (D.p - 1) * Nat.card U
  exact pTypeLowerDenominator_dvd_of_le K (_root_.commutator U)
    D.p K.index rfl data.index_dvd_prime_pred
      (pTypeDerived_le_nonGaloisActionKernel hD not_Galois)

/-- The complement's derived subgroup, mapped into the maximal subgroup. -/
def pTypeDerivedComplementInMaximal
    {L U : Type u} [Group L] [Group U]
    (UinL : U →* L) : Subgroup L :=
  (_root_.commutator (G := U)).map UinL

namespace internal

/-- The direct inclusion and nested-subgroup inclusion give the same mapped
derived complement. -/
theorem pTypeDerivedComplementInMaximal_eq_subgroupOf
    {Gamma : Type u} [Group Gamma]
    {L U : Subgroup Gamma} (hUL : U ≤ L) :
    pTypeDerivedComplementInMaximal (Subgroup.inclusion hUL) =
      pTypeDerivedComplementInMaximal (U.subgroupOf L).subtype := by
  let e : U ≃* U.subgroupOf L :=
    (Subgroup.subgroupOfEquivOfLe hUL).symm
  have hcommutator :
      (_root_.commutator U).map e.toMonoidHom =
        _root_.commutator (U.subgroupOf L) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective,
      ← _root_.commutator_def]
  unfold pTypeDerivedComplementInMaximal
  calc
    (_root_.commutator U).map (Subgroup.inclusion hUL) =
        ((_root_.commutator U).map e.toMonoidHom).map
          (U.subgroupOf L).subtype := by
      rw [Subgroup.map_map]
      apply congrArg (fun f : U →* L ↦ (_root_.commutator U).map f)
      ext x
      rfl
    _ = (_root_.commutator (U.subgroupOf L)).map
        (U.subgroupOf L).subtype := by rw [hcommutator]

/-- Forming the commutator before inclusion agrees with restricting
`derivedWithin U` to the containing subgroup. -/
theorem pTypeDerivedComplementInMaximal_eq_derivedWithin_subgroupOf
    {Gamma : Type u} [Group Gamma]
    {L U : Subgroup Gamma} (hUL : U ≤ L) :
    pTypeDerivedComplementInMaximal (Subgroup.inclusion hUL) =
      (derivedWithin U).subgroupOf L := by
  unfold pTypeDerivedComplementInMaximal derivedWithin
  ext x
  constructor
  · rintro ⟨u, hu, hux⟩
    exact ⟨u, hu, congrArg Subtype.val hux⟩
  · rintro ⟨u, hu, hux⟩
    exact ⟨u, hu, Subtype.ext hux⟩

end internal

/-- Clause (d)'s divisibility after mapping the complement into the maximal
subgroup. -/
theorem pTypeNonGaloisLowerDenominator_dvd_mapped
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {L U W₁ : Subgroup Gamma}
    {Hbar : Type u} [Group Hbar] [Finite Hbar]
    {D : PTypeFactorActionData Hbar U W₁}
    (hUL : U ≤ L)
    (hD : PTypeFactorActionHypotheses D)
    (not_Galois : ¬ typeP_Galois D) :
    pTypeNonGaloisLowerDenominator
        (pTypeNonGaloisIndex hD not_Galois)
        (pTypeDerivedComplementInMaximal (Subgroup.inclusion hUL)) ∣
      pTypeNonGaloisLowerNumerator D.p (U.subgroupOf L) := by
  unfold pTypeNonGaloisLowerDenominator
    pTypeNonGaloisLowerNumerator pTypeDerivedComplementInMaximal
  rw [Subgroup.card_map_of_injective
      (Subgroup.inclusion_injective hUL),
    natCard_subgroupOf_eq hUL]
  exact pTypeNonGaloisLowerDenominator_dvd_internal hD not_Galois

/-- Conjugation by a normalizing subgroup, as a homomorphism to
automorphisms. -/
noncomputable def pTypeSubgroupConjugationHom
    {L : Type u} [Group L] (P A : Subgroup L)
    (hAP : A ≤ Subgroup.normalizer (P : Set L)) :
    A →* MulAut P := by
  letI : MulDistribMulAction A P :=
    subgroupConjugationAction P A hAP
  exact MulDistribMulAction.toMulAut A P

end

end Submission.OddOrder.PF
