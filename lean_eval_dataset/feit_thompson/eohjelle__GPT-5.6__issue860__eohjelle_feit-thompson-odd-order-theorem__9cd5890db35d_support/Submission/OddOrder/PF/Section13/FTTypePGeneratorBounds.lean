import Mathlib.Analysis.MeanInequalities
import Submission.OddOrder.PF.Section13.FTTypePCyclicRectangle

/-!
# Peterfalvi Section 13: bounds on cyclic generators

This module isolates the square-sum estimates used later in the three Fitting
rows and in the cover argument.  It also records that the distinguished
coherent rows are signed irreducibles, hence have algebraic-integer values.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open scoped BigOperators Classical Pointwise

universe u

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {S U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) generatorBoundsFintype
    (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace FTTypePGeneratorBoundsInternal

/-! ## Square sums on subgroup support -/

/-- Remove the identity term from the normalized norm of a supported class
function. -/
theorem sumNormSq_subgroupNonidentity_eq
    {Q : Type} [Group Q] [Fintype Q]
    (H : Subgroup Q) (phi : ClassFunction Q ℂ)
    (hsupport : phi ∈ ClassFunction.supportedOn (H : Set Q)) :
    ftTypePSumNormSq (subgroupNonidentity H) phi =
      (Nat.card Q : ℝ) * classFunctionNormSq phi -
        Complex.normSq (phi 1) := by
  let s : Finset Q :=
    FTTypePBoundsInfrastructureInternal.finiteSet
      (subgroupNonidentity H)
  have hone : (1 : Q) ∉ s := by
    simp [s, FTTypePBoundsInfrastructureInternal.finiteSet,
      subgroupNonidentity, nonidentitySet]
  have hzero :
      ∀ x ∈ Finset.univ, x ∉ insert 1 s →
        Complex.normSq (phi x) = 0 := by
    intro x _ hx
    have hxH : x ∉ H := by
      intro hxmem
      have hxne : x ≠ 1 := by
        intro h
        subst x
        exact hx (by simp)
      apply hx
      simp [s, FTTypePBoundsInfrastructureInternal.finiteSet,
        subgroupNonidentity, nonidentitySet, hxmem, hxne]
    rw [ClassFunction.eq_zero_of_mem_supportedOn hsupport hxH]
    exact Complex.normSq_zero
  have hdecompose :
      (∑ x : Q, Complex.normSq (phi x)) =
        Complex.normSq (phi 1) +
          ∑ x ∈ s, Complex.normSq (phi x) := by
    calc
      (∑ x : Q, Complex.normSq (phi x)) =
          ∑ x ∈ insert 1 s, Complex.normSq (phi x) := by
        symm
        exact Finset.sum_subset (Finset.subset_univ _) hzero
      _ = Complex.normSq (phi 1) +
          ∑ x ∈ s, Complex.normSq (phi x) :=
        Finset.sum_insert hone
  have hcard : (Nat.card Q : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hmass :
      ftTypePSumNormSq (subgroupNonidentity H) phi =
        ∑ x ∈ s, Complex.normSq (phi x) := by
    rw [ftTypePSumNormSq]
    apply Finset.sum_congr
    · ext x
      simp [s, FTTypePBoundsInfrastructureInternal.finiteSet]
    · intro x _
      rfl
  have hnorm :
      (Nat.card Q : ℝ) * classFunctionNormSq phi =
        ∑ x : Q, Complex.normSq (phi x) := by
    rw [classFunctionNormSq, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  rw [hmass, hnorm, hdecompose]
  apply Eq.symm
  exact add_sub_cancel_left (Complex.normSq (phi 1))
    (∑ x ∈ s, Complex.normSq (phi x))

/-! ## The integer-square inequality -/

private theorem integerSquareBound
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) (b : ℤ)
    (hcard : Nat.card ctx.P = ctx.p ^ ctx.q)
    (hindex : ctx.u ≤ (ctx.p ^ ctx.q - 1) / (ctx.p - 1)) :
    2 * (ctx.u : ℝ) * (b : ℝ) ≤
      ((Nat.card ctx.P - 1 : ℕ) : ℝ) * (b : ℝ) ^ 2 := by
  have hp : 3 ≤ ctx.p :=
    ctx.primeTI.prime_cycTIhyp.two_lt_card_right
  have hnat : 2 * ctx.u ≤ Nat.card ctx.P - 1 := by
    calc
      2 * ctx.u ≤ (ctx.p - 1) * ctx.u :=
        Nat.mul_le_mul_right ctx.u (by omega)
      _ ≤ (ctx.p - 1) * ((ctx.p ^ ctx.q - 1) / (ctx.p - 1)) :=
        Nat.mul_le_mul_left (ctx.p - 1) hindex
      _ ≤ ctx.p ^ ctx.q - 1 := Nat.mul_div_le _ _
      _ = Nat.card ctx.P - 1 := by rw [hcard]
  have hreal :
      2 * (ctx.u : ℝ) ≤ ((Nat.card ctx.P - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hb : (b : ℝ) ≤ (b : ℝ) ^ 2 := by
    by_cases hnonpos : b ≤ 0
    · have hnonpos' : (b : ℝ) ≤ 0 := by exact_mod_cast hnonpos
      nlinarith [sq_nonneg (b : ℝ)]
    · have hone : (1 : ℝ) ≤ (b : ℝ) := by
        exact_mod_cast (show 1 ≤ b by omega)
      nlinarith [sq_nonneg ((b : ℝ) - 1)]
  calc
    2 * (ctx.u : ℝ) * (b : ℝ) ≤
        2 * (ctx.u : ℝ) * (b : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ ((Nat.card ctx.P - 1 : ℕ) : ℝ) * (b : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hreal (sq_nonneg _)

/-- Peterfalvi's integral-square estimate for a type-P context. -/
theorem P1_int2
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) (b : ℤ) :
    2 * (ctx.u : ℝ) * (b : ℝ) ≤
      ((Nat.card ctx.P - 1 : ℕ) : ℝ) * (b : ℝ) ^ 2 := by
  obtain ⟨_, _, _, _, _, hcard, hindex, _, _, _⟩ := FTtypeP_facts ctx
  exact integerSquareBound ctx b hcard hindex

/-! ## Generators of cyclic groups -/

/-- A member of a subgroup generates its subtype exactly when it generates
that subgroup in the ambient group. -/
theorem mem_cyclicGenerators_iff_zpowers_coe_eq
    {Q : Type u} [Group Q] [Fintype Q]
    (L : Subgroup Q) (x : L) :
    x ∈ cyclicGenerators L ↔ Subgroup.zpowers (x : Q) = L := by
  rw [mem_cyclicGenerators]
  constructor
  · intro hx
    calc
      Subgroup.zpowers (x : Q) =
          (Subgroup.zpowers x).map L.subtype :=
        (MonoidHom.map_zpowers L.subtype x).symm
      _ = (⊤ : Subgroup L).map L.subtype := by rw [hx]
      _ = L := by rw [← MonoidHom.range_eq_map, L.range_subtype]
  · intro hx
    refine (Subgroup.eq_top_iff' (Subgroup.zpowers x)).2 ?_
    intro y
    have hy : (y : Q) ∈ Subgroup.zpowers (x : Q) := by
      rw [hx]
      exact y.property
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩

/-- Nonvanishing at one generator of a cyclic subgroup implies nonvanishing
at every other generator. -/
theorem irreducible_ne_zero_of_zpowers_eq
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) {x y : Q}
    (hxy : Subgroup.zpowers x = Subgroup.zpowers y)
    (hx : chi x ≠ 0) :
    chi y ≠ 0 := by
  classical
  have hxrange : x ∈ Subgroup.zpowers y := by
    rw [← hxy]
    exact Subgroup.mem_zpowers x
  rw [mem_zpowers_iff_mem_range_orderOf] at hxrange
  obtain ⟨k, _, hpow⟩ := Finset.mem_image.mp hxrange
  have hyrange : y ∈ Subgroup.zpowers x := by
    rw [hxy]
    exact Subgroup.mem_zpowers y
  have hcoprime : Nat.Coprime k (orderOf y) := by
    rw [← hpow] at hyrange
    simpa only [Nat.coprime_iff_gcd_eq_one] using
      (mem_zpowers_pow_iff.mp hyrange)
  obtain ⟨sigma, hsigma, _⟩ :=
    make_pi_cfAut_complex Q (orderOf y) k hcoprime
  have hgal := hsigma
    (Finsupp.single chi 1 : VirtualCharacter Q ℂ) y dvd_rfl
  have htransport : sigma (chi y) = chi x := by
    simpa only [VirtualCharacter.realize_single, Int.cast_one, one_smul,
      hpow] using hgal
  intro hy
  apply hx
  rw [← htransport, hy, map_zero]

private theorem card_le_sum_of_prod_ge_one
    {I : Type*} (s : Finset I) (f : I → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i)
    (hprod : 1 ≤ ∏ i ∈ s, f i) :
    (s.card : ℝ) ≤ ∑ i ∈ s, f i := by
  classical
  by_cases hs : s = ∅
  · subst s
    simp
  have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hsne
  have hamgm :
      (∏ i ∈ s, f i) ^ (s.card : ℝ)⁻¹ ≤
        (∑ i ∈ s, f i) / (s.card : ℝ) := by
    simpa using
      (Real.geom_mean_le_arith_mean s (fun _ ↦ (1 : ℝ)) f
        (fun _ _ ↦ zero_le_one) (by simpa using hcard) hf)
  have hone :
      1 ≤ (∏ i ∈ s, f i) ^ (s.card : ℝ)⁻¹ := by
    calc
      (1 : ℝ) = 1 ^ (s.card : ℝ)⁻¹ := by simp
      _ ≤ (∏ i ∈ s, f i) ^ (s.card : ℝ)⁻¹ :=
        Real.rpow_le_rpow zero_le_one hprod (inv_nonneg.mpr hcard.le)
  have hmean : 1 ≤ (∑ i ∈ s, f i) / (s.card : ℝ) :=
    hone.trans hamgm
  simpa using (le_div_iff₀' hcard).mp hmean

/-- Isaacs' square-sum estimate on the generators of a finite cyclic group. -/
theorem sumNormSq_character_generators
    {L : Type u} [Group L] [Fintype L] [IsCyclic L]
    (V : FDRep ℂ L)
    (hnz : ∀ x ∈ cyclicGenerators L, V.character x ≠ 0) :
    ((cyclicGenerators L).card : ℝ) ≤
      ∑ x ∈ cyclicGenerators L, Complex.normSq (V.character x) := by
  obtain ⟨n, hn⟩ := character_generator_normSq_product_natCast V
  have hpositive :
      0 < ∏ x ∈ cyclicGenerators L,
        Complex.normSq (V.character x) := by
    apply Finset.prod_pos
    intro x hx
    exact Complex.normSq_pos.mpr (hnz x hx)
  rw [hn] at hpositive
  have hnOne : 1 ≤ n := by exact_mod_cast hpositive
  apply card_le_sum_of_prod_ge_one
  · intro x _
    exact Complex.normSq_nonneg _
  · rw [hn]
    exact_mod_cast hnOne

/-! ## Signed irreducible rows -/

private theorem coherentImage_eq_signed_irreducible
    {L Q : Type u} [Group L] [Fintype L] [Group Q] [Fintype Q]
    {T : Set (ClassFunction L ℂ)}
    {tau nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction Q ℂ}
    (hcoh : coherent_with T (nonidentitySet L) tau nu)
    (chi : IrreducibleCharacter L ℂ)
    (hchi : (chi : ClassFunction L ℂ) ∈ T) :
    ∃ (psi : IrreducibleCharacter Q ℂ) (epsilon : ℤ),
      IsSign epsilon ∧
        nu (chi : ClassFunction L ℂ) =
          (epsilon : ℂ) • (psi : ClassFunction Q ℂ) := by
  letI : Invertible (Nat.card L : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card Q : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hclosure :
      (chi : ClassFunction L ℂ) ∈ AddSubgroup.closure T :=
    AddSubgroup.subset_closure hchi
  obtain ⟨z, hz⟩ := hcoh.mapsToVirtual _ hclosure
  have hpair :
      characterPairing (VirtualCharacter.realize z)
          (VirtualCharacter.realize z) = 1 := by
    rw [hz, hcoh.isometry _ hclosure _ hclosure,
      IrreducibleCharacter.characterPairing_self]
  have hnorm : normSq z = 1 := by
    apply Int.cast_injective (α := ℂ)
    calc
      (normSq z : ℂ) =
          characterPairing (VirtualCharacter.realize z)
            (VirtualCharacter.realize z) := by
        simpa [normSq] using
          (VirtualCharacter.characterPairing_realize z z).symm
      _ = 1 := hpair
      _ = ((1 : ℤ) : ℂ) := by norm_num
  obtain ⟨psi, epsilon, hepsilon, hzsingle⟩ :=
    eq_signed_single_of_normSq_eq_one z hnorm
  refine ⟨psi, epsilon, hepsilon, ?_⟩
  calc
    nu (chi : ClassFunction L ℂ) = VirtualCharacter.realize z := hz.symm
    _ = (epsilon : ℂ) • (psi : ClassFunction Q ℂ) := by
      rw [hzsingle, VirtualCharacter.realize_single]

/-- The coherent image of an irreducible Fitting-induced row is a signed
irreducible ambient character. -/
theorem tau1_lambda_eq_signed_irreducible
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (lambda : ClassFunction S ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (hcalS : lambda ∈ ftTypePCoreFamily S)
    (hirr : lambda ∈ irr_Ind_Fitting S) :
    ∃ (chi : IrreducibleCharacter G ℂ) (epsilon : ℤ),
      IsSign epsilon ∧
        tau1 lambda =
          (epsilon : ℂ) • (chi : ClassFunction G ℂ) := by
  let lambdaIrr : IrreducibleCharacter S ℂ := ⟨lambda, hirr.1⟩
  exact coherentImage_eq_signed_irreducible hcoh lambdaIrr hcalS

private theorem eta_eq_signed_irreducible
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ∃ (chi : IrreducibleCharacter G ℂ) (epsilon : ℤ),
      IsSign epsilon ∧
        ctx.eta i j =
          (epsilon : ℂ) • (chi : ClassFunction G ℂ) := by
  obtain ⟨chiTop, epsilon, hepsilon, himage⟩ :=
    ctx.isoG.cyclicTIImage_eq_signed_irreducible (i, j)
  let chi : IrreducibleCharacter G ℂ :=
    IrreducibleCharacter.comapMulEquiv Subgroup.topEquiv.symm chiTop
  refine ⟨chi, epsilon, hepsilon, ?_⟩
  apply ClassFunction.ext
  intro x
  have hat := congrArg
    (fun phi : ClassFunction (⊤ : Subgroup G) ℂ ↦
      phi (Subgroup.topEquiv.symm x)) himage
  change ctx.isoG.cyclicTIImage (i, j) (Subgroup.topEquiv.symm x) =
    (epsilon : ℂ) * chi x
  simpa only [ClassFunction.smul_apply, smul_eq_mul, chi,
    IrreducibleCharacter.comapMulEquiv_apply] using hat

/-- The distinguished left rectangle row is a signed irreducible. -/
theorem eta10_eq_signed_irreducible
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ∃ (chi : IrreducibleCharacter G ℂ) (epsilon : ℤ),
      IsSign epsilon ∧
        ftTypePEta10 ctx =
          (epsilon : ℂ) • (chi : ClassFunction G ℂ) := by
  simpa only [ftTypePEta10] using
    eta_eq_signed_irreducible ctx
      (ftTypePLeftIndex ctx) IrreducibleCharacter.trivial

/-- Values in the transported cyclic-TI rectangle are algebraic integers. -/
theorem eta_apply_isIntegral
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) (x : G) :
    IsIntegral ℤ (ctx.eta i j x) := by
  obtain ⟨chi, epsilon, _, heta⟩ :=
    eta_eq_signed_irreducible ctx i j
  have hchi : IsIntegral ℤ (chi x) := by
    rw [← chi.representation_character]
    exact representation_character_isIntegral chi.representation.ρ x
  have hepsilon : IsIntegral ℤ (epsilon : ℂ) :=
    isIntegral_intCast epsilon
  have hvalue := congrArg (fun phi : ClassFunction G ℂ ↦ phi x) heta
  change ctx.eta i j x = (epsilon : ℂ) * chi x at hvalue
  rw [hvalue]
  exact hepsilon.mul hchi

end FTTypePGeneratorBoundsInternal

end

end Submission.OddOrder.PF
