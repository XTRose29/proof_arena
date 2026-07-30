import Submission.OddOrder.PF.Section10.FTType345TauReduced
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Peterfalvi Section 10: the coprime lower bound

This phase proves Peterfalvi (10.6b).  The zero-column identity from the
preceding phase expresses `tau₁ zeta` as a sum of cyclic-TI character values
away from the full Dade support.  At elements of order coprime to `|W₁|`,
those values are integers and are constant on contragredient pairs.  Since
`W₁` has odd order, only the trivial character is fixed by contragredience,
so the sum is an odd, hence nonzero, integer.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open FTType345ConstantsInternal
open scoped BigOperators Classical Pointwise IsMulCommutative

universe u v w

/-! ## Restricting complex automorphisms -/

/-- A complex-valued form of `dvd_restrict_cfAut`.  Its cyclotomic-field
construction is performed in the relative algebraic closure of `ℚ` in `ℂ`,
whose automorphisms extend to `ℂ`. -/
private theorem dvd_restrict_cfAut_complex10
    (G : Type v) [Group G] [Fintype G]
    (a : ℕ) (mu : ℂ ≃ₐ[ℚ] ℂ) :
    ∃ nu : ℂ ≃ₐ[ℚ] ℂ,
      (∀ {G₀ : Type w} [Group G₀] [Fintype G₀]
          (chi : VirtualCharacter G₀ ℂ) (x : G₀),
          orderOf x ∣ a →
          nu (VirtualCharacter.realize chi x) =
            mu (VirtualCharacter.realize chi x)) ∧
      ∀ (chi : VirtualCharacter G ℂ) (x : G),
        (orderOf x).Coprime a →
        nu (VirtualCharacter.realize chi x) =
          VirtualCharacter.realize chi x := by
  by_cases ha0 : a = 0
  · subst a
    refine ⟨mu, fun _ _ _ ↦ rfl, ?_⟩
    intro chi x hx
    have hx1 : orderOf x = 1 := by
      simpa only [Nat.coprime_zero_right] using hx
    have hxo : orderOf x ∣ 1 := by simp [hx1]
    let omega : ℂˣ := 1
    have homega : IsPrimitiveRoot omega 1 := by simp [omega]
    simpa only [pow_one] using
      algEquiv_virtualCharacter_apply_eq_pow
        homega mu 1 (by simp [omega]) chi x hxo
  · let b : ℕ := ∏ x : G,
      if (orderOf x).Coprime a then orderOf x else 1
    have hab : a.Coprime b := by
      change a.Coprime
        (∏ x : G, if (orderOf x).Coprime a then orderOf x else 1)
      rw [Nat.coprime_fintype_prod_right_iff]
      intro x
      by_cases hx : (orderOf x).Coprime a
      · rw [if_pos hx]
        exact hx.symm
      · rw [if_neg hx]
        exact Nat.coprime_one_right a
    have hbpos : 0 < b := by
      dsimp only [b]
      apply Finset.prod_pos
      intro x _
      by_cases hx : (orderOf x).Coprime a
      · rw [if_pos hx]
        exact orderOf_pos x
      · rw [if_neg hx]
        exact Nat.zero_lt_one
    let A := algebraicClosure ℚ ℂ
    letI : Module.IsTorsionFree ℚ A :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr
        (algebraMap ℚ A).injective
    letI : IsAlgClosure ℚ A := by
      dsimp only [A]
      exact algebraicClosure.isAlgClosure ℚ ℂ
    letI : IsAlgClosed A := IsAlgClosure.isAlgClosed ℚ
    letI : CharZero A :=
      charZero_of_injective_algebraMap (algebraMap ℚ A).injective
    letI : NeZero a := ⟨ha0⟩
    letI : NeZero b := ⟨Nat.ne_of_gt hbpos⟩
    let rootsA : Set A :=
      {x | ∃ n ∈ ({a} : Set ℕ), n ≠ 0 ∧ x ^ n = 1}
    let rootsB : Set A :=
      {x | ∃ n ∈ ({b} : Set ℕ), n ≠ 0 ∧ x ^ n = 1}
    let Qa : IntermediateField ℚ A := IntermediateField.adjoin ℚ rootsA
    let Qb : IntermediateField ℚ A := IntermediateField.adjoin ℚ rootsB
    letI : Algebra ℚ Qa := Qa.algebra'
    letI : Algebra ℚ Qb := Qb.algebra'
    letI : IsCyclotomicExtension {a} ℚ Qa := by
      dsimp only [Qa, rootsA]
      apply
        IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      intro n hn _
      rw [Set.mem_singleton_iff] at hn
      subst n
      exact HasEnoughRootsOfUnity.exists_primitiveRoot A a
    letI : IsCyclotomicExtension {b} ℚ Qb := by
      dsimp only [Qb, rootsB]
      apply
        IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      intro n hn _
      rw [Set.mem_singleton_iff] at hn
      subst n
      exact HasEnoughRootsOfUnity.exists_primitiveRoot A b
    let wa : Qa := IsCyclotomicExtension.zeta a ℚ Qa
    let wb : Qb := IsCyclotomicExtension.zeta b ℚ Qb
    have hwa : IsPrimitiveRoot wa a :=
      IsCyclotomicExtension.zeta_spec a ℚ Qa
    have hwb : IsPrimitiveRoot wb b :=
      IsCyclotomicExtension.zeta_spec b ℚ Qb
    let QaA : Qa →ₐ[ℚ] A := Qa.val
    let QbA : Qb →ₐ[ℚ] A := Qb.val
    let AC : A →ₐ[ℚ] ℂ := A.val
    let QaC : Qa →ₐ[ℚ] ℂ := AC.comp QaA
    let QbC : Qb →ₐ[ℚ] ℂ := AC.comp QbA
    have hgenQa : IntermediateField.adjoin ℚ {wa} = ⊤ := by
      apply IntermediateField.toSubalgebra_injective
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic wa),
        IntermediateField.top_toSubalgebra]
      exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hwa
    have hgenQb : IntermediateField.adjoin ℚ {wb} = ⊤ := by
      apply IntermediateField.toSubalgebra_injective
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic wb),
        IntermediateField.top_toSubalgebra]
      exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hwb
    let muA : A ≃ₐ[ℚ] A := mu.algebraicClosure
    obtain ⟨nuA, hnuQa, hnuQb⟩ :=
      extend_coprime_Qn_aut a b wa wb QaA QbA muA hab
        hwa hgenQa hwb hgenQb
    obtain ⟨nu, hnu⟩ :=
      exists_complex_algEquiv_extending_algebraicClosure nuA
    refine ⟨nu, ?_, ?_⟩
    · intro G₀ _ _ chi x hx
      obtain ⟨q, hq⟩ :=
        virtualCharacter_value_exists_preimage QaC hwa chi x hx
      calc
        nu (VirtualCharacter.realize chi x) = nu (QaC q) := by rw [hq]
        _ = (nuA (QaA q) : A) := hnu (QaA q)
        _ = (muA (QaA q) : A) :=
          congrArg Subtype.val (hnuQa q)
        _ = mu (QaC q) := rfl
        _ = mu (VirtualCharacter.realize chi x) := by rw [hq]
    · intro chi x hx
      have hxb : orderOf x ∣ b := by
        have hd := Finset.dvd_prod_of_mem
          (fun y : G ↦ if (orderOf y).Coprime a then orderOf y else 1)
          (Finset.mem_univ x)
        change orderOf x ∣
          ∏ y : G, if (orderOf y).Coprime a then orderOf y else 1
        simpa only [if_pos hx] using hd
      obtain ⟨q, hq⟩ :=
        virtualCharacter_value_exists_preimage QbC hwb chi x hxb
      calc
        nu (VirtualCharacter.realize chi x) = nu (QbC q) := by rw [hq]
        _ = (nuA (QbA q) : A) := hnu (QbA q)
        _ = (QbA q : A) := congrArg Subtype.val (hnuQb q)
        _ = VirtualCharacter.realize chi x := hq

/-! ## Integral and contragredient-paired left-column values -/

private theorem cyclicTI_leftFactor_value_isInt10
    {Gamma : Type} [Group Gamma] [Fintype Gamma]
    {G W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ) (g : G)
    (hcop : Nat.Coprime (orderOf (g : Gamma)) (Nat.card W₁)) :
    ∃ z : ℤ,
      h.cyclicTIIsometry
          (IrreducibleCharacter.cyclicTICharacter defW i
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :
            ClassFunction W ℂ) g = (z : ℂ) := by
  let source : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW i
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
  let phi : ClassFunction G ℂ :=
    h.cyclicTIIsometry (source : ClassFunction W ℂ)
  have hphiIntegral : IsIntegral ℤ (phi g) := by
    obtain ⟨chi, epsilon, hepsilon, hphi⟩ :=
      (h.cyclicTIIsometryData (k := ℂ)).exists_signed_irreducible_image source
    have hchi : IsIntegral ℤ (chi g) := by
      rw [← chi.representation_character]
      exact representation_character_isIntegral chi.representation.ρ g
    have hepsilonIntegral : IsIntegral ℤ (epsilon : ℂ) :=
      isIntegral_intCast epsilon
    have hvalue := congrArg (fun f : ClassFunction G ℂ ↦ f g) hphi
    change phi g = (epsilon : ℂ) * chi g at hvalue
    rw [hvalue]
    exact hepsilonIntegral.mul hchi
  have hphiFixedComplex :
      ∀ sigma : ℂ ≃ₐ[ℚ] ℂ, sigma (phi g) = phi g := by
    intro sigma
    obtain ⟨nu, hagree, hfix⟩ :=
      dvd_restrict_cfAut_complex10 G (Nat.card W₁) sigma
    have hsource :
        ClassFunction.mapRingHom nu.toRingEquiv.toRingHom
            (source : ClassFunction W ℂ) =
          ClassFunction.mapRingHom sigma.toRingEquiv.toRingHom
            (source : ClassFunction W ℂ) := by
      ext y
      dsimp only [source]
      have hy := hagree
        (Finsupp.single i 1 : VirtualCharacter W₁ ℂ)
        (defW.leftProjection y) (orderOf_dvd_natCard _)
      simpa [ClassFunction.mapRingHom_apply,
        IrreducibleCharacter.cyclicTICharacter_leftFactor_apply] using hy
    let z : VirtualCharacter G ℂ :=
      h.cyclicTIIsometryVirtual (Finsupp.single source 1)
    have hz : VirtualCharacter.realize z = phi := by
      rw [h.realize_cyclicTIIsometryVirtual]
      simp only [VirtualCharacter.realize_single, Int.cast_one, one_smul,
        phi]
    calc
      sigma (phi g) =
          h.cyclicTIIsometry
            (ClassFunction.mapRingHom sigma.toRingEquiv.toRingHom
              (source : ClassFunction W ℂ)) g := by
        exact congrArg (fun f : ClassFunction G ℂ ↦ f g)
          (h.cfAut_cycTIiso sigma.toRingEquiv
            (source : ClassFunction W ℂ))
      _ = h.cyclicTIIsometry
            (ClassFunction.mapRingHom nu.toRingEquiv.toRingHom
              (source : ClassFunction W ℂ)) g := by
        rw [hsource]
      _ = nu (phi g) := by
        exact congrArg (fun f : ClassFunction G ℂ ↦ f g)
          (h.cfAut_cycTIiso nu.toRingEquiv
            (source : ClassFunction W ℂ)).symm
      _ = phi g := by
        simpa only [hz] using hfix z g (by simpa using hcop)
  have hphiIntegralQ : IsIntegral ℚ (phi g) :=
    IsIntegral.tower_top hphiIntegral
  let A := algebraicClosure ℚ ℂ
  letI : Module.IsTorsionFree ℚ A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap ℚ A).injective
  letI : IsAlgClosure ℚ A := by
    dsimp only [A]
    exact algebraicClosure.isAlgClosure ℚ ℂ
  let phiA : A :=
    ⟨phi g, mem_algebraicClosure_iff'.2 hphiIntegralQ⟩
  have hphiFixedA : ∀ sigma : A ≃ₐ[ℚ] A, sigma phiA = phiA := by
    intro sigma
    obtain ⟨sigmaC, hsigmaC⟩ :=
      exists_complex_algEquiv_extending_algebraicClosure sigma
    apply Subtype.ext
    exact (hsigmaC phiA).symm.trans (hphiFixedComplex sigmaC)
  have hphiRat : ∃ q : ℚ, phi g = (q : ℂ) := by
    have hmem : phiA ∈ Set.range (algebraMap ℚ A) :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed phiA).2 hphiFixedA
    obtain ⟨q, hq⟩ := hmem
    refine ⟨q, ?_⟩
    exact (congrArg Subtype.val hq).symm.trans rfl
  obtain ⟨z, hz⟩ :=
    (IsIntegral.exists_int_iff_exists_rat hphiIntegral).mp hphiRat
  exact ⟨z, by simpa only [phi, source] using hz⟩

private theorem cyclicTI_leftFactor_dual_value10
    {Gamma : Type} [Group Gamma] [Fintype Gamma]
    {G W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ) (g : G)
    (hcop : Nat.Coprime (orderOf (g : Gamma)) (Nat.card W₁)) :
    h.cyclicTIIsometry
        (IrreducibleCharacter.cyclicTICharacter defW
          (IrreducibleCharacter.dual i)
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :
          ClassFunction W ℂ) g =
      h.cyclicTIIsometry
        (IrreducibleCharacter.cyclicTICharacter defW i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :
          ClassFunction W ℂ) g := by
  let a := Nat.card W₁
  let k := a - 1
  have haPos : 0 < a := Nat.card_pos
  have hkcop : Nat.Coprime k a := by
    dsimp only [k]
    rw [Nat.coprime_self_sub_left haPos]
    exact Nat.coprime_one_left a
  obtain ⟨nu, hpow, hfix⟩ := make_pi_cfAut_complex G a k hkcop
  have hkInv (x : W₁) : x ^ k = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    have hka : k + 1 = a := by
      dsimp only [k]
      omega
    rw [hka]
    exact pow_card_eq_one'
  let source : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW i
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
  let sourceDual : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW
      (IrreducibleCharacter.dual i)
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
  have hsourcePower :
      ClassFunction.mapRingHom nu.toRingEquiv.toRingHom
          (source : ClassFunction W ℂ) =
        (sourceDual : ClassFunction W ℂ) := by
    ext y
    dsimp only [source, sourceDual]
    have hy := hpow
      (Finsupp.single i 1 : VirtualCharacter W₁ ℂ)
      (defW.leftProjection y) (orderOf_dvd_natCard _)
    simpa [ClassFunction.mapRingHom_apply,
      IrreducibleCharacter.cyclicTICharacter_leftFactor_apply,
      IrreducibleCharacter.dual_apply, hkInv] using hy
  let z : VirtualCharacter G ℂ :=
    h.cyclicTIIsometryVirtual (Finsupp.single source 1)
  have hz : VirtualCharacter.realize z =
      h.cyclicTIIsometry (source : ClassFunction W ℂ) := by
    rw [h.realize_cyclicTIIsometryVirtual]
    simp only [VirtualCharacter.realize_single, Int.cast_one, one_smul]
  calc
    h.cyclicTIIsometry (sourceDual : ClassFunction W ℂ) g =
        h.cyclicTIIsometry
          (ClassFunction.mapRingHom nu.toRingEquiv.toRingHom
            (source : ClassFunction W ℂ)) g := by rw [hsourcePower]
    _ = nu (h.cyclicTIIsometry (source : ClassFunction W ℂ) g) := by
      exact congrArg (fun f : ClassFunction G ℂ ↦ f g)
        (h.cfAut_cycTIiso nu.toRingEquiv
          (source : ClassFunction W ℂ)).symm
    _ = h.cyclicTIIsometry (source : ClassFunction W ℂ) g := by
      simpa only [hz] using hfix z g (by simpa [a] using hcop)

/-! ## The parity argument -/

private theorem int_sum_ne_zero_of_unique_fixed_involution10
    {I : Type*} [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm I) (i0 : I)
    (hinvol : ∀ i, sigma (sigma i) = i)
    (hsigma : ∀ i, sigma i = i ↔ i = i0)
    (c : I → ℤ) (hc : ∀ i, c (sigma i) = c i)
    (hc0 : c i0 = 1) :
    ∑ i, c i ≠ 0 := by
  let moved : Finset I := Finset.univ.filter fun i ↦ sigma i ≠ i
  have hsigmaMoved : ∀ i, i ∈ moved → sigma i ∈ moved := by
    intro i hi
    simp only [moved, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hfix
    apply hi
    exact sigma.injective hfix
  have hsigmaMovedNe : ∀ i, i ∈ moved → sigma i ≠ i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hpair (i : I) :
      (c i : ZMod 2) + (c (sigma i) : ZMod 2) = 0 := by
    rw [hc]
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    calc
      (c i : ZMod 2) + (c i : ZMod 2) =
          (2 : ZMod 2) * (c i : ZMod 2) := by ring_nf
      _ = 0 := by rw [htwo, zero_mul]
  have hmoved : ∑ i ∈ moved, (c i : ZMod 2) = 0 := by
    apply Finset.sum_involution
        (s := moved) (f := fun i ↦ (c i : ZMod 2))
        (fun i _ ↦ sigma i)
    · intro i _
      exact hpair i
    · intro i hi _
      exact hsigmaMovedNe i hi
    · exact hsigmaMoved
    · intro i _
      exact hinvol i
  have hfixed : Finset.univ.filter (fun i ↦ sigma i = i) = {i0} := by
    ext i
    simp [hsigma i]
  have hcast : ((∑ i, c i : ℤ) : ZMod 2) = 1 := by
    simp only [Int.cast_sum]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset I)) (p := fun i ↦ sigma i = i)]
    rw [hfixed, Finset.sum_singleton, hc0, Int.cast_one]
    have hmoved' :
        Finset.univ.filter (fun i ↦ ¬ sigma i = i) = moved := by
      ext i
      simp [moved]
    rw [hmoved', hmoved, add_zero]
  intro hzero
  rw [hzero, Int.cast_zero] at hcast
  exact zero_ne_one hcast

namespace FTType345CoherenceInternal

variable {Gamma : Type} [Group Gamma] [Fintype Gamma]
variable [IsMinSimpleOddGroup Gamma]
variable {M U W W₁ W₂ : Subgroup Gamma}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

private theorem coprime_zeroColumn_difference_supportedOn_fullSupport
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta) :
    (ftType345PrimeTI MtypeP).primeTIRed
          (ftType345IsoM MtypeP)
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
        zeta ∈
      ClassFunction.supportedOn
        {x : M | (x : Gamma) ∈ FTsupport M} := by
  let K : Subgroup M := ftType345DerivedInM M
  letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 M
  have hindex : K.index = Nat.card W₁ := by
    have houter : IsInternalSemidirectProductIn
        (derivedWithin M) W₁ M := MtypeP.1.2.2.2
    calc
      K.index = Nat.card (W₁.subgroupOf M) :=
        houter.2.2.2.symm.index_eq_card
      _ = Nat.card W₁ :=
        MathlibSupport.natCard_subgroupOf_eq houter.2.1
  have hbase := cfInd1_sub_lin_on (k := ℂ) K hzeta.mem_calS (by
    rw [hzeta.degree, hindex])
  rw [← (ftType345PrimeTI MtypeP).prTIred0
    (ftType345IsoM MtypeP)] at hbase
  have hnot1 : FTtype M ≠ 1 :=
    FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP
  have hgt : 2 < FTtype M := by
    have hrange := FTtype_range M
    omega
  rw [ClassFunction.mem_supportedOn_iff] at hbase ⊢
  intro x hx
  apply hbase x
  intro hxK
  apply hx
  have hxDerived : (x : Gamma) ∈
      subgroupNonidentity (derivedWithin M) :=
    ⟨hxK.1, fun hxOne ↦ hxK.2 (Subtype.ext hxOne)⟩
  change (x : Gamma) ∈ FTsupport M
  rw [FTsupp_eq1 hmaxM hgt, FTsupp1_type_gt2 M hgt]
  exact hxDerived

/-- Peterfalvi (10.6b): away from the full Dade support, every value of
the coherent reference row at order coprime to `|W₁|` has norm at least one. -/
theorem ftType345_zeta_tau1_coprime
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (tau₁ : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (hcoh : coherent_with
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau hmaxM) tau₁)
    (g : (⊤ : Subgroup Gamma))
    (hg : (g : Gamma) ∉ FT_Dade_full_support M)
    (hcop : Nat.Coprime (orderOf (g : Gamma)) (Nat.card W₁)) :
    1 ≤ ‖tau₁ zeta g‖ := by
  classical
  let ctiG := (ftType345PrimeDade hmaxM MtypeP).prDade_cycTI
  let eta (i : IrreducibleCharacter W₁ ℂ) :
      ClassFunction (⊤ : Subgroup Gamma) ℂ :=
    ftType345Eta hmaxM MtypeP i
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
  let alpha : ClassFunction M ℂ :=
    (ftType345PrimeTI MtypeP).primeTIRed
        (ftType345IsoM MtypeP)
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
      zeta
  have halphaOn : alpha ∈ ClassFunction.supportedOn
      {x : M | (x : Gamma) ∈ FTsupport M} := by
    simpa only [alpha] using
      coprime_zeroColumn_difference_supportedOn_fullSupport
        hmaxM MtypeP notMtype2 zeta hzeta
  have halphaZero : ftType345Tau hmaxM alpha g = 0 := by
    rw [← FT_DadeE M hmaxM alpha halphaOn]
    apply ClassFunction.eq_zero_of_mem_supportedOn
      (Dade_cfunS (FT_Dade_hyp M hmaxM) alpha)
    rwa [FT_Dade_supportE M hmaxM]
  have htau0 := ftType345_tau1mu0 hmaxM MtypeP notMtype2
    zeta hzeta tau₁ hcoh
  have htau0g := congrArg
    (fun f : ClassFunction (⊤ : Subgroup Gamma) ℂ ↦ f g) htau0
  have htauValue : tau₁ zeta g = ∑ i, eta i g := by
    change ftType345Tau hmaxM alpha g =
      (∑ i, eta i) g - tau₁ zeta g at htau0g
    rw [halphaZero] at htau0g
    simp only [ClassFunction.finset_sum_apply] at htau0g
    exact (sub_eq_zero.mp htau0g.symm).symm
  have hetaInt (i : IrreducibleCharacter W₁ ℂ) :
      ∃ z : ℤ, eta i g = (z : ℂ) := by
    simpa only [eta, ctiG, ftType345Eta,
      CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible,
      CyclicTIHypothesis.cyclicTIIsometry] using
      cyclicTI_leftFactor_value_isInt10 ctiG i g hcop
  let c (i : IrreducibleCharacter W₁ ℂ) : ℤ :=
    Classical.choose (hetaInt i)
  have hcValue (i : IrreducibleCharacter W₁ ℂ) :
      eta i g = (c i : ℂ) := Classical.choose_spec (hetaInt i)
  have hetaDual (i : IrreducibleCharacter W₁ ℂ) :
      eta (IrreducibleCharacter.dual i) g = eta i g := by
    simpa only [eta, ctiG, ftType345Eta,
      CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible,
      CyclicTIHypothesis.cyclicTIIsometry] using
      cyclicTI_leftFactor_dual_value10 ctiG i g hcop
  have hcDual (i : IrreducibleCharacter W₁ ℂ) :
      c (IrreducibleCharacter.dual i) = c i := by
    apply Int.cast_injective (α := ℂ)
    rw [← hcValue, ← hcValue]
    exact hetaDual i
  have heta00 : eta
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) g = 1 := by
    change ctiG.cyclicTIIsometry
      (IrreducibleCharacter.cyclicTICharacter defW
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :
        ClassFunction W ℂ) g = 1
    rw [IrreducibleCharacter.cyclicTICharacter_trivial,
      ctiG.cyclicTIIsometry_trivial]
    exact IrreducibleCharacter.trivial_apply g
  have hc0 : c
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) = 1 := by
    apply Int.cast_injective (α := ℂ)
    rw [← hcValue, heta00, Int.cast_one]
  have hsumNe : ∑ i, c i ≠ 0 := by
    apply int_sum_ne_zero_of_unique_fixed_involution10
      IrreducibleCharacter.dualEquiv
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
    · exact IrreducibleCharacter.dual_dual
    · intro i
      exact odd_eq_conj_irr1 (mFT_odd W₁) i
    · exact hcDual
    · exact hc0
  have hsumCast : (∑ i, eta i g) = ((∑ i, c i : ℤ) : ℂ) := by
    simp only [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact hcValue i
  rw [htauValue, hsumCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hsumNe

end FTType345CoherenceInternal

end

end Submission.OddOrder.PF
