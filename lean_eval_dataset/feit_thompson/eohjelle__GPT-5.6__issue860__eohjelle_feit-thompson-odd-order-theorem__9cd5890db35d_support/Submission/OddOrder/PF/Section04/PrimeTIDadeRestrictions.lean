import Mathlib.GroupTheory.FixedPointFree
import Submission.OddOrder.MathlibSupport.IrreducibleCharacterDegreeDivides
import Submission.OddOrder.MathlibSupport.MaschkeNormalConstituent
import Submission.OddOrder.MathlibSupport.RepresentationSubgroupNorm
import Submission.OddOrder.PF.Section01.NormalSubgroupConstituentKernels
import Submission.OddOrder.PF.Section02.ClassSupportProperties
import Submission.OddOrder.PF.Section02.DadeMap
import Submission.OddOrder.PF.Section04.PrimeTIInductionCases

/-!
# Prime-TI restrictions in the Dade setting

This file ports the first part of Peterfalvi 4.7, through the equality of
the signs of equal-degree entries in a prime-TI column.  It packages the
additional normal subgroup and Dade-set hypotheses, proves the required
vanishing theorem for irreducible characters off a normal kernel, and then
applies it to the selected prime-TI restrictions and their inductions.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical
open Submission.OddOrder.MathlibSupport

universe u v

/-! ## The prime-Dade hypotheses -/

variable {Gamma : Type u} [Group Gamma]

/-- The union, over nonidentity `h ∈ H`, of the nonidentity elements of
`C_K(h)`.  This is the set occurring in `prime_Dade_definition`. -/
def primeDadeCentralizerSupport
    (K H : Subgroup Gamma) : Set Gamma :=
  {x | x ∈ K ∧ x ≠ 1 ∧
    ∃ h, h ∈ H ∧ h ≠ 1 ∧ Commute x h}

/-- Peterfalvi's `prime_Dade_definition`. -/
structure PrimeDadeDefinition
    (L K H : Subgroup Gamma) (A A₀ : Set Gamma)
    (W W₁ W₂ : Subgroup Gamma)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop where
  normal_subgroup :
    H ≤ L ∧ (H.subgroupOf L).Normal
  fixed_le_subgroup : W₂ ≤ H
  subgroup_le_kernel : H ≤ K
  normal_set :
    A ⊆ (L : Set Gamma) ∧ L ≤ Subgroup.normalizer A
  centralizerSupport_le :
    primeDadeCentralizerSupport K H ⊆ A
  set_le_kernel_diff_one :
    A ⊆ (K : Set Gamma) \ {1}
  dadeSet_eq :
    A₀ = A ∪ classSupportWithin L (cyclicTISet W W₁ W₂)

/-- Peterfalvi's `prime_Dade_hypothesis`. -/
structure PrimeDadeHypothesis
    (G L K H : Subgroup Gamma) (A A₀ : Set Gamma)
    (W W₁ W₂ : Subgroup Gamma)
    (defW : IsInternalDirectProductIn W₁ W₂ W) : Prop where
  prDade_cycTI : CyclicTIHypothesis G W W₁ W₂ defW
  prDade_prTI : PrimeTIHypothesis L K W W₁ W₂ defW
  prDade_hyp : DadeHypothesis G L A₀
  prDade_def :
    PrimeDadeDefinition L K H A A₀ W W₁ W₂ defW

/-- The support `{1} ∪ A`, phrased for an arbitrary group type coercing to
the common ambient group.  In particular this accepts both `L` and the
nested subgroup type `K.subgroupOf L`. -/
def primeDadeSupport
    (J : Type v) [One J] [CoeTC J Gamma] (A : Set Gamma) : Set J :=
  {x | (x : Gamma) = 1 ∨ (x : Gamma) ∈ A}

@[simp]
theorem mem_primeDadeSupport
    {J : Type v} [One J] [CoeTC J Gamma]
    {A : Set Gamma} {x : J} :
    x ∈ primeDadeSupport J A ↔
      (x : Gamma) = 1 ∨ (x : Gamma) ∈ A :=
  Iff.rfl

namespace PrimeDadeHypothesis

variable {G L K H W W₁ W₂ : Subgroup Gamma} {A A₀ : Set Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}
  (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)

/-- The normal signalizer subgroup, regarded as a subgroup of the prime-TI
kernel inside `L`. -/
def signalizerInKernel
    (_pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW) :
    Subgroup (K.subgroupOf L) :=
  (H.subgroupOf L).subgroupOf (K.subgroupOf L)

include pd

/-- The smaller set `A` is contained in the Dade set `A₀`. -/
theorem set_subset_dadeSet : A ⊆ A₀ := by
  rw [pd.prDade_def.dadeSet_eq]
  exact Set.subset_union_left

/-- The Dade linear map supplied by the packaged Dade hypothesis. -/
noncomputable def dadeMap
    [Finite Gamma] {k : Type v} [Field k] :
    ClassFunction L k →ₗ[k] ClassFunction G k :=
  Dade pd.prDade_hyp

end PrimeDadeHypothesis

/-! ## A fixed-point-free vanishing lemma -/

/-- If a normal subgroup is not in the translation kernel of an
irreducible character, then the character vanishes at every element whose
centralizer in that normal subgroup is trivial.  This is the source lemma
`irr_reg_off_ker_0`, proved here from the subgroup norm and the bijective
commutator map of a fixed-point-free automorphism. -/
theorem irr_reg_off_ker_0
    {Q k : Type u} [Group Q] [Fintype Q]
    [Field k] [IsAlgClosed k] [CharZero k]
    (N : Subgroup Q) [N.Normal]
    (chi : IrreducibleCharacter Q k)
    (hker : ¬ N ≤
      ClassFunction.translationKernel (chi : ClassFunction Q k))
    (g : Q)
    (hcent : centralizerWithin N (Subgroup.zpowers g) = ⊥) :
    chi g = 0 := by
  let rho : Representation k Q chi.representation :=
    chi.representation.ρ
  let rhoN : Representation k N chi.representation :=
    rho.comp N.subtype
  let F : Subrepresentation rho :=
    normalInvariantsSubrepresentation rho N
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  have hF : F = ⊥ := by
    rcases eq_bot_or_eq_top F with hbot | htop
    · exact hbot
    · exfalso
      apply hker
      rw [ClassFunction.translationKernel_irreducibleCharacter chi]
      intro n hn
      rw [MonoidHom.mem_ker]
      apply LinearMap.ext
      intro x
      have hxF : x ∈ F := by
        rw [htop]
        trivial
      have hxInv : x ∈ rhoN.invariants := by
        change x ∈ F
        exact hxF
      exact (Representation.mem_invariants rhoN x).mp hxInv ⟨n, hn⟩
  have hfix : rhoN.invariants = ⊥ := by
    change F.toSubmodule = (⊥ : Submodule k chi.representation)
    exact congrArg Subrepresentation.toSubmodule hF
  have hnorm : rhoN.norm = 0 :=
    Representation.norm_eq_zero_of_invariants_eq_bot rhoN hfix
  let e : N ≃* N := MulAut.conjNormal g
  have he : MonoidHom.FixedPointFree e := by
    intro n hn
    apply Subtype.ext
    have hval : g * (n : Q) * g⁻¹ = (n : Q) := by
      simpa [e, MulAut.conjNormal_apply] using congrArg Subtype.val hn
    have hcomm : Commute g (n : Q) := by
      rw [commute_iff_eq]
      exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hval)
    have hncent : (n : Q) ∈
        centralizerWithin N (Subgroup.zpowers g) := by
      refine ⟨n.property, ?_⟩
      intro z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (hcomm.zpow_left m).eq
    have hnbot : (n : Q) ∈ (⊥ : Subgroup Q) := by
      rw [← hcent]
      exact hncent
    exact Subgroup.mem_bot.mp hnbot
  have hconst (n : N) : chi ((n : Q) * g) = chi g := by
    obtain ⟨x, hx⟩ := he.commutatorMap_surjective n
    have hxQ :
        (x : Q) / (g * (x : Q) * g⁻¹) = (n : Q) := by
      simpa [e, MulAut.conjNormal_apply] using congrArg Subtype.val hx
    have hconj :
        (n : Q) * g = (x : Q) * g * (x : Q)⁻¹ := by
      calc
        (n : Q) * g =
            ((x : Q) / (g * (x : Q) * g⁻¹)) * g := by
              rw [hxQ]
        _ = (x : Q) * g * (x : Q)⁻¹ := by
          rw [div_eq_mul_inv]
          group
    calc
      chi ((n : Q) * g) = chi ((x : Q) * g * (x : Q)⁻¹) :=
        congrArg (fun q : Q ↦ chi q) hconj
      _ = chi g :=
        ClassFunction.conj_apply (chi : ClassFunction Q k) (x : Q) g
  have hsumEnd :
      (∑ n : N, rho ((n : Q) * g)) = 0 := by
    calc
      (∑ n : N, rho ((n : Q) * g)) =
          (∑ n : N, rho (n : Q)) * rho g := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro n _
            rw [map_mul]
      _ = rhoN.norm * rho g := by rfl
      _ = 0 := by rw [hnorm, zero_mul]
  have hsumChar : (∑ n : N, chi ((n : Q) * g)) = 0 := by
    calc
      (∑ n : N, chi ((n : Q) * g)) =
          ∑ n : N, LinearMap.trace k chi.representation
            (rho ((n : Q) * g)) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [← chi.representation_character]
        rfl
      _ = LinearMap.trace k chi.representation
          (∑ n : N, rho ((n : Q) * g)) := by
        rw [map_sum]
      _ = 0 := by rw [hsumEnd, map_zero]
  have hcardmul : (Nat.card N : k) * chi g = 0 := by
    calc
      (Nat.card N : k) * chi g = ∑ _ : N, chi g := by
        simp [Nat.card_eq_fintype_card, nsmul_eq_mul]
      _ = ∑ n : N, chi ((n : Q) * g) := by
        apply Finset.sum_congr rfl
        intro n _
        exact (hconst n).symm
      _ = 0 := hsumChar
  have hcard : (Nat.card N : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  exact (mul_eq_zero.mp hcardmul).resolve_left hcard

/-! ## Support of the selected restrictions -/

namespace PrimeDadeHypothesis

variable {G L K H W W₁ W₂ : Subgroup Gamma} {A A₀ : Set Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}
  {k : Type u} [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)

local instance subgroupCoeTCToAmbient (S : Subgroup Gamma) :
    CoeTC S Gamma :=
  ⟨fun x ↦ x.1⟩

local instance subgroupOfCoeTCToAmbient (S T : Subgroup Gamma) :
    CoeTC (S.subgroupOf T) Gamma :=
  ⟨fun x ↦ x.1.1⟩

local instance primeDadeInvertibleCard
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- An irreducible character of `K` on which `H` acts nontrivially is
supported on `{1} ∪ A`. -/
theorem prDade_irr_on
    (theta : IrreducibleCharacter (K.subgroupOf L) k)
    (hker : ¬ pd.signalizerInKernel ≤
      ClassFunction.translationKernel
        (theta : ClassFunction (K.subgroupOf L) k)) :
    (theta : ClassFunction (K.subgroupOf L) k) ∈
      ClassFunction.supportedOn
        (primeDadeSupport (K.subgroupOf L) A) := by
  letI : (H.subgroupOf L).Normal :=
    pd.prDade_def.normal_subgroup.2
  letI : pd.signalizerInKernel.Normal :=
    Subgroup.Normal.subgroupOf
      (inferInstance : (H.subgroupOf L).Normal) (K.subgroupOf L)
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxone : (((x : K.subgroupOf L) : L) : Gamma) ≠ 1 := by
    intro hx1
    exact hx (Or.inl hx1)
  have hxA : (((x : K.subgroupOf L) : L) : Gamma) ∉ A := by
    intro hxin
    exact hx (Or.inr hxin)
  apply irr_reg_off_ker_0 pd.signalizerInKernel theta hker x
  apply eq_bot_iff.mpr
  intro z hz
  apply Subgroup.mem_bot.mpr
  by_contra hz1
  have hzGamma_ne : (((z : K.subgroupOf L) : L) : Gamma) ≠ 1 := by
    intro hzGamma
    apply hz1
    apply Subtype.ext
    exact Subtype.ext hzGamma
  have hzH : (((z : K.subgroupOf L) : L) : Gamma) ∈ H := by
    exact hz.1
  have hxComm : Commute
      (((x : K.subgroupOf L) : L) : Gamma)
      (((z : K.subgroupOf L) : L) : Gamma) := by
    rw [commute_iff_eq]
    exact congrArg
      (fun t : K.subgroupOf L ↦ (((t : K.subgroupOf L) : L) : Gamma))
      (hz.2 x (Subgroup.mem_zpowers x))
  have hxCentralizer :
      (((x : K.subgroupOf L) : L) : Gamma) ∈
        primeDadeCentralizerSupport K H := by
    exact ⟨x.property, hxone,
      (((z : K.subgroupOf L) : L) : Gamma), hzH, hzGamma_ne, hxComm⟩
  exact hxA (pd.prDade_def.centralizerSupport_le hxCentralizer)

/-- Induction to `L` preserves the support `{1} ∪ A`. -/
theorem prDade_Ind_irr_on
    (theta : IrreducibleCharacter (K.subgroupOf L) k)
    (hker : ¬ pd.signalizerInKernel ≤
      ClassFunction.translationKernel
        (theta : ClassFunction (K.subgroupOf L) k)) :
    ClassFunction.induce (K.subgroupOf L)
        (theta : ClassFunction (K.subgroupOf L) k) ∈
      ClassFunction.supportedOn (primeDadeSupport L A) := by
  have htheta := pd.prDade_irr_on theta hker
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  rw [ClassFunction.induce_apply_formula]
  suffices (∑ y : L,
      if hy : y⁻¹ * x * y ∈ K.subgroupOf L then
        (theta : ClassFunction (K.subgroupOf L) k)
          ⟨y⁻¹ * x * y, hy⟩ else 0) = 0 by
    rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro y _
  split_ifs with hy
  · apply ClassFunction.eq_zero_of_mem_supportedOn htheta
    intro hsupport
    rcases hsupport with hone | hAconj
    · apply hx
      left
      have hconjOne : y⁻¹ * x * y = 1 := by
        apply Subtype.ext
        exact hone
      have hxOne : x = 1 := by
        calc
          x = y * (y⁻¹ * x * y) * y⁻¹ := by group
          _ = 1 := by rw [hconjOne]; simp
      exact congrArg Subtype.val hxOne
    · apply hx
      right
      have hyNorm : ((y : L) : Gamma) ∈ Subgroup.normalizer A :=
        pd.prDade_def.normal_set.2 y.property
      exact (Subgroup.mem_set_normalizer_iff''.mp hyNorm
        ((x : L) : Gamma)).mpr hAconj
  · rfl

/-! ## Kernel exclusion and its support corollaries -/

/-- A nontrivial right-factor irreducible has nontrivial action by `H` on
its selected prime-TI restriction. -/
theorem cfker_prTIres
    (iso : CyclicTIIsometryData (k := k)
      pd.prDade_prTI.prime_cycTIhyp)
    (j : IrreducibleCharacter W₂ k)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    ¬ pd.signalizerInKernel ≤
      ClassFunction.translationKernel
        (pd.prDade_prTI.primeTI_Ires iso j :
          ClassFunction (K.subgroupOf L) k) := by
  intro hker
  let KL : Subgroup L := K.subgroupOf L
  let HL : Subgroup L := H.subgroupOf L
  let psi : IrreducibleCharacter KL k :=
    pd.prDade_prTI.primeTI_Ires iso j
  let mu : IrreducibleCharacter L k :=
    pd.prDade_prTI.primeTIIndex iso
      ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k), j)
  letI : KL.Normal := pd.prDade_prTI.kernel_normal
  letI : HL.Normal := pd.prDade_def.normal_subgroup.2
  have hHLKL : HL ≤ KL := by
    intro h hh
    exact pd.prDade_def.subgroup_le_kernel hh
  have hconst : psi.IsConstituent
      (ClassFunction.restrict KL (mu : ClassFunction L k)) := by
    unfold IrreducibleCharacter.IsConstituent
    rw [show ClassFunction.restrict KL (mu : ClassFunction L k) =
        (psi : ClassFunction KL k) by
      simpa [KL, mu, psi, PrimeTIHypothesis.primeTICharacter] using
        pd.prDade_prTI.cfRes_prTIirr iso
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k) j]
    rw [IrreducibleCharacter.characterPairing_self]
    exact one_ne_zero
  have hpsiKer : HL.subgroupOf KL ≤ psi.representation.ρ.ker := by
    rw [← ClassFunction.translationKernel_irreducibleCharacter psi]
    simpa [signalizerInKernel, HL, KL, psi] using hker
  have hmuKer : HL ≤ mu.representation.ρ.ker :=
    (IrreducibleCharacter.sub_ker_constituent_restrict_iff
      KL HL hHLKL mu psi hconst).mp hpsiKer
  have hmuTrans : HL ≤
      ClassFunction.translationKernel (mu : ClassFunction L k) := by
    rw [ClassFunction.translationKernel_irreducibleCharacter mu]
    exact hmuKer
  letI : IsCyclic W₂ := pd.prDade_prTI.fixed_cyclic
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    pd.prDade_prTI.complement_ne_bot
  have hjOne (y : W₂) : j y = 1 := by
    let wx : W := defW.mulEquiv (x, 1)
    let wxy : W := defW.mulEquiv (x, y)
    let yL : L :=
      ⟨(y : Gamma), pd.prDade_prTI.kernel_le_group
        (pd.prDade_prTI.fixed_le_kernel y.property)⟩
    let wxL : L :=
      ⟨wx, pd.prDade_prTI.directProduct_le_group wx.property⟩
    let wxyL : L :=
      ⟨wxy, pd.prDade_prTI.directProduct_le_group wxy.property⟩
    have hyHL : yL ∈ HL :=
      pd.prDade_def.fixed_le_subgroup y.property
    have htranslate : mu (yL * wxL) = mu wxL :=
      (ClassFunction.mem_translationKernel_iff
        (mu : ClassFunction L k) yL).mp (hmuTrans hyHL) wxL
    have hproduct : yL * wxL = wxyL := by
      apply Subtype.ext
      change (y : Gamma) * (wx : Gamma) = (wxy : Gamma)
      simpa [wx, wxy] using (defW.commute x y).eq.symm
    have hmuEq : mu wxyL = mu wxL := by
      rw [← hproduct]
      exact htranslate
    have hwx : wx ∈ primeTISetInW W W₂ := by
      rw [mem_primeTISetInW]
      intro hwxW₂
      exact hx ((defW.mulEquiv_mem_right_iff (x, 1)).mp hwxW₂)
    have hwxy : wxy ∈ primeTISetInW W W₂ := by
      rw [mem_primeTISetInW]
      intro hwxyW₂
      exact hx ((defW.mulEquiv_mem_right_iff (x, y)).mp hwxyW₂)
    have hvalx :=
      (pd.prDade_prTI.primeTICharacterData iso).restrict_character
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k) j
        hwx
    have hvalxy :=
      (pd.prDade_prTI.primeTICharacterData iso).restrict_character
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ k) j
        hwxy
    have heq :
        (pd.prDade_prTI.primeTISign iso j : k) * j y =
          (pd.prDade_prTI.primeTISign iso j : k) := by
      calc
        (pd.prDade_prTI.primeTISign iso j : k) * j y =
            mu wxyL := by
              simpa [mu, wxyL, wxy, PrimeTIHypothesis.primeTIIndex,
                PrimeTIHypothesis.primeTISign] using hvalxy.symm
        _ = mu wxL := hmuEq
        _ = (pd.prDade_prTI.primeTISign iso j : k) := by
          simpa [mu, wxL, wx, PrimeTIHypothesis.primeTIIndex,
            PrimeTIHypothesis.primeTISign] using hvalx
    have hsign : (pd.prDade_prTI.primeTISign iso j : k) ≠ 0 :=
      Int.cast_ne_zero.mpr
        (isSign_ne_zero (pd.prDade_prTI.primeTISign_isSign iso j))
    apply mul_left_cancel₀ hsign
    simpa using heq
  apply hj
  apply IrreducibleCharacter.ext
  intro y
  simpa using hjOne y

/-- The selected prime-TI restriction for a nontrivial right-factor
character is supported on `{1} ∪ A`. -/
theorem prDade_TIres_on
    (iso : CyclicTIIsometryData (k := k)
      pd.prDade_prTI.prime_cycTIhyp)
    (j : IrreducibleCharacter W₂ k)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    (pd.prDade_prTI.primeTI_Ires iso j :
        ClassFunction (K.subgroupOf L) k) ∈
      ClassFunction.supportedOn
        (primeDadeSupport (K.subgroupOf L) A) :=
  pd.prDade_irr_on _ (pd.cfker_prTIres iso j hj)

/-- The corresponding reduced prime-TI column is supported on `{1} ∪ A`
inside `L`. -/
theorem prDade_TIred_on
    (iso : CyclicTIIsometryData (k := k)
      pd.prDade_prTI.prime_cycTIhyp)
    (j : IrreducibleCharacter W₂ k)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    pd.prDade_prTI.primeTIRed iso j ∈
      ClassFunction.supportedOn (primeDadeSupport L A) := by
  rw [← pd.prDade_prTI.cfInd_prTIres iso j]
  exact pd.prDade_Ind_irr_on _ (pd.cfker_prTIres iso j hj)

/-! ## Equal degree gives equal sign -/

/-- Equal degrees in one prime-TI row have equal column signs. -/
theorem prDade_TIsign_eq
    (iso : CyclicTIIsometryData (k := k)
      pd.prDade_prTI.prime_cycTIhyp)
    (i : IrreducibleCharacter W₁ k)
    (j r : IrreducibleCharacter W₂ k)
    (hdegree :
      pd.prDade_prTI.primeTICharacter iso i j 1 =
        pd.prDade_prTI.primeTICharacter iso i r 1) :
    pd.prDade_prTI.primeTISign iso j =
      pd.prDade_prTI.primeTISign iso r := by
  have hmod : IsIntegralModEq (Nat.card W₁ : k)
      (pd.prDade_prTI.primeTISign iso j : k)
      (pd.prDade_prTI.primeTISign iso r : k) :=
    (pd.prDade_prTI.primeTICharacter_one_mod_card_left iso i j).symm.trans
      ((IsIntegralModEq.of_eq hdegree).trans
        (pd.prDade_prTI.primeTICharacter_one_mod_card_left iso i r))
  have hcardTwo : 2 < Nat.card W₁ :=
    pd.prDade_cycTI.two_lt_card_left
  have hcardNe : Nat.card W₁ ≠ 0 := by omega
  have hcastNe : (Nat.card W₁ : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr hcardNe
  have hnotDvd : ¬ Nat.card W₁ ∣ 2 := by
    intro hdvd
    have hle : Nat.card W₁ ≤ 2 :=
      Nat.le_of_dvd (by omega : 0 < 2) hdvd
    omega
  rcases pd.prDade_prTI.primeTISign_isSign iso j with hjp | hjm <;>
    rcases pd.prDade_prTI.primeTISign_isSign iso r with hrp | hrm
  · exact hjp.trans hrp.symm
  · exfalso
    obtain ⟨z, hz, heq⟩ := hmod
    rw [hjp, hrm] at heq
    norm_num at heq
    have heq' : (2 : k) = (Nat.card W₁ : k) * z := by
      simpa [Nat.card_eq_fintype_card] using heq
    have hdiv : (2 : k) / (Nat.card W₁ : k) = z := by
      apply (div_eq_iff hcastNe).2
      calc
        (2 : k) = (Nat.card W₁ : k) * z := heq'
        _ = z * (Nat.card W₁ : k) := mul_comm _ _
    have hint : IsIntegral ℤ ((2 : k) / (Nat.card W₁ : k)) := by
      rw [hdiv]
      exact hz
    exact hnotDvd
      (nat_dvd_of_cast_div_isIntegral 2 (Nat.card W₁) hcardNe hint)
  · exfalso
    obtain ⟨z, hz, heq⟩ := hmod
    rw [hjm, hrp] at heq
    norm_num at heq
    have heq' : -(2 : k) = (Nat.card W₁ : k) * z := by
      simpa [Nat.card_eq_fintype_card] using heq
    have hdiv : (2 : k) / (Nat.card W₁ : k) = -z := by
      apply (div_eq_iff hcastNe).2
      linear_combination -heq'
    have hint : IsIntegral ℤ ((2 : k) / (Nat.card W₁ : k)) := by
      rw [hdiv]
      exact hz.neg
    exact hnotDvd
      (nat_dvd_of_cast_div_isIntegral 2 (Nat.card W₁) hcardNe hint)
  · exact hjm.trans hrm.symm

end PrimeDadeHypothesis

end

end Submission.OddOrder.PF
