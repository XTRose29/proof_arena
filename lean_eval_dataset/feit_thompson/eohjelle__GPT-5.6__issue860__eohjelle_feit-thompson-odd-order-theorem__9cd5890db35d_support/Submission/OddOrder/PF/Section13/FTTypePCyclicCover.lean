import Submission.OddOrder.PF.Section13.FTTypePGeneratorBounds

/-!
# Peterfalvi Section 13: the cyclic cover of the non-Fitting set

The two rectangle rows used below cannot vanish simultaneously on the
non-Fitting set.  We combine that fact with a count by generated cyclic
subgroups: on each generator fiber, the square-sum estimate for a cyclic
representation bounds the number of nonzero values of a signed irreducible
character.  The union of the two nonzero loci then gives the required lower
bound.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open scoped BigOperators Classical Pointwise

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {S U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) cyclicCoverFintype
    (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace FTTypePCyclicCoverInternal

/-! ## The two rectangle rows cover -/

private theorem trace_eq_det_of_finrank_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (hdim : Module.finrank ℂ V = 1) (f : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V f = LinearMap.det f := by
  letI : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (hdim ▸ Nat.zero_lt_one)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let b : Module.Basis Unit ℂ V :=
    FiniteDimensional.basisSingleton Unit hdim v hv
  rw [LinearMap.trace_eq_matrix_trace ℂ b, ← LinearMap.det_toMatrix b]
  simp only [Matrix.trace, Finset.univ_unique, Finset.sum_singleton,
    Matrix.det_unique, Matrix.diag_apply]

private theorem cyclicIrreducible_value_ne_zero
    {Q : Type} [Group Q] [Fintype Q] [IsCyclic Q]
    (chi : IrreducibleCharacter Q ℂ) (x : Q) : chi x ≠ 0 := by
  rw [← chi.representation_character]
  change LinearMap.trace ℂ chi.representation (chi.representation.ρ x) ≠ 0
  rw [trace_eq_det_of_finrank_one (V := chi.representation)
    (IrreducibleCharacter.representation_finrank_eq_one_of_isCyclic chi)]
  exact (LinearMap.isUnit_det _
    (IsUnit.map chi.representation.ρ (Group.isUnit x))).ne_zero

private theorem eta10_zero_outside_cyclicSupport
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) {x : G}
    (hx0 : ftTypePEta10 ctx x = 0) :
    x ∉ classSupportWithin (⊤ : Subgroup G) (cyclicTISet W W₁ W₂) := by
  rintro ⟨z, hz, g, _hg, rfl⟩
  letI : IsCyclic W := ctx.primeDade.prDade_cycTI.cyclic
  let chiW : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW
      (ftTypePLeftIndex ctx) IrreducibleCharacter.trivial
  let zW : W := ⟨z, (mem_cyclicTISet.mp hz).1⟩
  have hzW : zW ∈ cyclicTISetInW W W₁ W₂ := by
    change z ∈ cyclicTISet W W₁ W₂
    exact hz
  have hrestriction := ctx.isoG.restrict (chiW : ClassFunction W ℂ) hzW
  have heta : ftTypePEta10 ctx z = chiW zW := by
    change
      ctx.isoG.cyclicTIImage
          (ftTypePLeftIndex ctx, IrreducibleCharacter.trivial)
          (Subgroup.topEquiv.symm z) = chiW zW
    let zTop : (⊤ : Subgroup G) := ⟨z, Subgroup.mem_top z⟩
    have htop : Subgroup.topEquiv.symm z = zTop := Subtype.ext rfl
    rw [htop]
    simpa only [CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible, chiW, zW, zTop,
      ClassFunction.comap_apply] using hrestriction
  apply cyclicIrreducible_value_ne_zero chiW zW
  rw [← heta]
  calc
    ftTypePEta10 ctx z = ftTypePEta10 ctx (g⁻¹ * z * g) := by
      symm
      simpa only [inv_inv] using
        ClassFunction.conj_apply (ftTypePEta10 ctx) g⁻¹ z
    _ = 0 := hx0

private theorem eta_left_zero_of_eta10_zero
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) (x : G)
    (heta10 : ftTypePEta10 ctx x = 0)
    (i : IrreducibleCharacter W₁ ℂ)
    (hi : i ≠ IrreducibleCharacter.trivial) :
    ctx.eta i IrreducibleCharacter.trivial x = 0 := by
  letI : IsCyclic W₁ := ctx.primeTI.prime_cycTIhyp.left_cyclic
  have hprime : (Nat.card W₁).Prime :=
    (FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP).1
  obtain ⟨sigma, hsigma⟩ :=
    exists_prime_cyclic_irreducible_algEquiv hprime
      ctx.primeTI.prime_cycTIhyp.left_cyclic
      (ftTypePLeftIndex ctx)
      (FTTypePBoundsInfrastructureInternal.leftIndex_ne_trivial ctx) i hi
  let source : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW
      (ftTypePLeftIndex ctx) IrreducibleCharacter.trivial
  let target : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW
      i IrreducibleCharacter.trivial
  have hsource :
      ClassFunction.mapRingHom sigma.toRingEquiv.toRingHom
          (source : ClassFunction W ℂ) =
        (target : ClassFunction W ℂ) := by
    rw [ClassFunction.mapRingHom_irreducible]
    apply congrArg
      (fun chi : IrreducibleCharacter W ℂ ↦ (chi : ClassFunction W ℂ))
    dsimp only [source, target]
    rw [← IrreducibleCharacter.cyclicTICharacter_mapRingEquiv,
      hsigma, IrreducibleCharacter.mapRingEquiv_trivial]
  have himage :
      ClassFunction.mapRingHom sigma.toRingEquiv.toRingHom
          (ctx.isoG.cyclicTIImage
            (ftTypePLeftIndex ctx, IrreducibleCharacter.trivial)) =
        ctx.isoG.cyclicTIImage (i, IrreducibleCharacter.trivial) := by
    rw [CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTIImage,
      ctx.isoG.mapRingEquiv_cyclicTIIsometry]
    exact congrArg ctx.isoG.linearMap hsource
  have hvalue := congrArg
    (fun phi : ClassFunction (⊤ : Subgroup G) ℂ ↦
      phi (Subgroup.topEquiv.symm x)) himage
  change sigma (ftTypePEta10 ctx x) =
    ctx.eta i IrreducibleCharacter.trivial x at hvalue
  rw [← hvalue, heta10, map_zero]

private theorem eta_rectangle_relation
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) (x : G)
    (hx : x ∉ classSupportWithin (⊤ : Subgroup G)
      (cyclicTISet W W₁ W₂))
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hi0 : ctx.eta i IrreducibleCharacter.trivial x = 0) :
    ctx.eta i j x = ctx.eta IrreducibleCharacter.trivial j x - 1 := by
  let hcyclic := ctx.primeDade.prDade_cycTI
  let alpha : ClassFunction W ℂ :=
    VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j)
  have halpha : alpha ∈
      ClassFunction.supportedOn (cyclicTISetInW W W₁ W₂) :=
    hcyclic.cyclicTIVirtualCharacter_mem_supportedOn i j
  have hinduced :
      ClassFunction.induce (W.subgroupOf (⊤ : Subgroup G))
          (ClassFunction.toSubgroupOf W (⊤ : Subgroup G)
            hcyclic.le_group alpha) ∈
        ClassFunction.supportedOn
          {y : (⊤ : Subgroup G) |
            (y : G) ∈ classSupportWithin (⊤ : Subgroup G)
              (cyclicTISet W W₁ W₂)} :=
    FTTypePCyclicRectangleInternal.induce_subgroupOf_mem_supportedOn_classSupportWithin
      (H := W) (L := (⊤ : Subgroup G)) (A := cyclicTISet W W₁ W₂)
      hcyclic.le_group alpha halpha
  have hinduced0 :
      hcyclic.induceClassFunction alpha (Subgroup.topEquiv.symm x) = 0 := by
    apply ClassFunction.eq_zero_of_mem_supportedOn hinduced
    change x ∉ classSupportWithin (⊤ : Subgroup G)
      (cyclicTISet W W₁ W₂)
    exact hx
  have himage0 :
      ctx.isoG.linearMap alpha (Subgroup.topEquiv.symm x) = 0 := by
    rw [ctx.isoG.induce_supported alpha halpha]
    exact hinduced0
  dsimp only [alpha] at himage0
  rw [realize_cyclicTIVirtualCharacter, map_add, map_sub, map_sub]
    at himage0
  simp only [ClassFunction.add_apply, ClassFunction.sub_apply] at himage0
  rw [ctx.isoG.map_trivial] at himage0
  simp only [IrreducibleCharacter.trivial_apply] at himage0
  change
    1 - ctx.eta i IrreducibleCharacter.trivial x -
        ctx.eta IrreducibleCharacter.trivial j x + ctx.eta i j x = 0
      at himage0
  rw [hi0] at himage0
  linear_combination himage0

private theorem rightColumn_and_eta10_not_both_zero
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) (x : G)
    (hcolumn : FTTypePCyclicRectangleInternal.etaRightColumn ctx x = 0)
    (heta10 : ftTypePEta10 ctx x = 0) : False := by
  letI : IsCyclic W₁ := ctx.primeTI.prime_cycTIhyp.left_cyclic
  let j : IrreducibleCharacter W₂ ℂ := ftTypePRightIndex ctx
  let a : ℂ := ctx.eta IrreducibleCharacter.trivial j x
  have hqPrime : ctx.q.Prime :=
    (FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP).1
  have houtside :
      x ∉ classSupportWithin (⊤ : Subgroup G) (cyclicTISet W W₁ W₂) :=
    eta10_zero_outside_cyclicSupport ctx heta10
  have hleft (i : IrreducibleCharacter W₁ ℂ)
      (hi : i ≠ IrreducibleCharacter.trivial) :
      ctx.eta i IrreducibleCharacter.trivial x = 0 :=
    eta_left_zero_of_eta10_zero ctx x heta10 i hi
  have hrect (i : IrreducibleCharacter W₁ ℂ)
      (hi : i ≠ IrreducibleCharacter.trivial) :
      ctx.eta i j x = a - 1 :=
    eta_rectangle_relation ctx x houtside i j (hleft i hi)
  have hsum0 :
      (∑ i : IrreducibleCharacter W₁ ℂ, ctx.eta i j x) = 0 := by
    simpa only [FTTypePCyclicRectangleInternal.etaRightColumn, j,
      ClassFunction.finset_sum_apply] using hcolumn
  let t := Finset.univ.erase
    (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
  have htcard : t.card = ctx.q - 1 := by
    dsimp only [t]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      IrreducibleCharacter.card_eq_natCard_of_isCyclic]
  have htail :
      (∑ i ∈ t, ctx.eta i j x) = ((ctx.q - 1 : ℕ) : ℂ) * (a - 1) := by
    calc
      (∑ i ∈ t, ctx.eta i j x) = ∑ _i ∈ t, (a - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hrect i (Finset.ne_of_mem_erase hi)
      _ = ((ctx.q - 1 : ℕ) : ℂ) * (a - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, htcard]
  have htotal :
      (∑ i : IrreducibleCharacter W₁ ℂ, ctx.eta i j x) =
        a + ((ctx.q - 1 : ℕ) : ℂ) * (a - 1) := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun i : IrreducibleCharacter W₁ ℂ ↦ ctx.eta i j x)
      (Finset.mem_univ _)]
    change a + (∑ i ∈ t, ctx.eta i j x) = _
    rw [htail]
  have harithmetic : a + ((ctx.q - 1 : ℕ) : ℂ) * (a - 1) = 0 := by
    rw [← htotal]
    exact hsum0
  have hqOne : 1 ≤ ctx.q := Nat.one_le_iff_ne_zero.mpr hqPrime.ne_zero
  have hpred : ((ctx.q - 1 : ℕ) : ℂ) = (ctx.q : ℂ) - 1 := by
    rw [Nat.cast_sub hqOne, Nat.cast_one]
  rw [hpred] at harithmetic
  have hqa : (ctx.q : ℂ) * (a - 1) = -1 := by
    linear_combination harithmetic
  have hq0 : (ctx.q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hqPrime.ne_zero
  have hetaValue :
      ctx.eta (ftTypePLeftIndex ctx) j x = -((ctx.q : ℂ)⁻¹) := by
    rw [hrect (ftTypePLeftIndex ctx)
      (FTTypePBoundsInfrastructureInternal.leftIndex_ne_trivial ctx)]
    apply mul_left_cancel₀ hq0
    rw [hqa, mul_neg, mul_inv_cancel₀ hq0]
  have hintegral : IsIntegral ℤ
      (ctx.eta (ftTypePLeftIndex ctx) j x) :=
    FTTypePGeneratorBoundsInternal.eta_apply_isIntegral
      ctx (ftTypePLeftIndex ctx) j x
  have hrational : ∃ r : ℚ,
      ctx.eta (ftTypePLeftIndex ctx) j x = (r : ℂ) := by
    refine ⟨-((ctx.q : ℚ)⁻¹), ?_⟩
    rw [hetaValue]
    change -((ctx.q : ℂ)⁻¹) =
      algebraMap ℚ ℂ (-((ctx.q : ℚ)⁻¹))
    rw [map_neg, map_inv₀]
    norm_num
  obtain ⟨z, hz⟩ :=
    (IsIntegral.exists_int_iff_exists_rat hintegral).mp hrational
  have hqzComplex : (ctx.q : ℂ) * (z : ℂ) = -1 := by
    rw [← hz, hetaValue, mul_neg, mul_inv_cancel₀ hq0]
  have hqz : (ctx.q : ℤ) * z = -1 := by
    exact_mod_cast hqzComplex
  have hdiv : (ctx.q : ℤ) ∣ 1 := by
    refine ⟨-z, ?_⟩
    rw [mul_neg, hqz]
    norm_num
  have hqEqOne : (ctx.q : ℤ) = 1 :=
    Int.eq_one_of_dvd_one (Int.natCast_nonneg ctx.q) hdiv
  apply hqPrime.ne_one
  exact_mod_cast hqEqOne

private theorem signedRightColumn_and_eta10_not_both_zero
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (b : Bool) (x : G)
    (hcolumn : ftTypePBooleanSign b *
      FTTypePCyclicRectangleInternal.etaRightColumn ctx x = 0)
    (heta10 : ftTypePEta10 ctx x = 0) : False := by
  apply rightColumn_and_eta10_not_both_zero ctx x
  · rcases mul_eq_zero.mp hcolumn with hsign | hzero
    · cases b <;> simp [ftTypePBooleanSign] at hsign
    · exact hzero
  · exact heta10

/-! ## Counting by generated cyclic subgroup -/

private def nonzeroPart (A : Set G) (phi : ClassFunction G ℂ) : Finset G :=
  (FTTypePBoundsInfrastructureInternal.finiteSet A).filter fun x ↦ phi x ≠ 0

private def generatedSubgroups
    (A : Set G) (phi : ClassFunction G ℂ) : Finset (Subgroup G) :=
  (nonzeroPart A phi).image fun x ↦ Subgroup.zpowers x

private def generatedFiber
    (A : Set G) (phi : ClassFunction G ℂ) (L : Subgroup G) : Finset G :=
  (nonzeroPart A phi).filter fun x ↦ Subgroup.zpowers x = L

private theorem signedIrreducible_fiber_bound
    (A : Set G) (phi : ClassFunction G ℂ)
    (chi : IrreducibleCharacter G ℂ) (epsilon : ℤ)
    (hepsilon : IsSign epsilon)
    (hphi : phi = (epsilon : ℂ) • (chi : ClassFunction G ℂ))
    (hclosed : ∀ {x y : G}, x ∈ A →
      Subgroup.zpowers x = Subgroup.zpowers y → y ∈ A)
    (L : Subgroup G) (hL : L ∈ generatedSubgroups A phi) :
    ((generatedFiber A phi L).card : ℝ) ≤
      ∑ x ∈ generatedFiber A phi L, Complex.normSq (phi x) := by
  classical
  obtain ⟨x, hx, hxL⟩ := Finset.mem_image.mp hL
  have hxData : x ∈ A ∧ phi x ≠ 0 := by
    simpa [nonzeroPart, FTTypePBoundsInfrastructureInternal.finiteSet]
      using hx
  letI : IsCyclic L := by
    rw [← hxL]
    infer_instance
  let V : FDRep ℂ L := FDRep.restrictToSubgroup L chi.representation
  have hphiValue (z : G) : phi z = (epsilon : ℂ) * chi z := by
    have hz := congrArg (fun f : ClassFunction G ℂ ↦ f z) hphi
    simpa only [ClassFunction.smul_apply, smul_eq_mul] using hz
  have hepsilon0 : (epsilon : ℂ) ≠ 0 :=
    Int.cast_ne_zero.mpr (isSign_ne_zero hepsilon)
  have hepsilonNorm (z : ℂ) :
      Complex.normSq ((epsilon : ℂ) * z) = Complex.normSq z := by
    rcases hepsilon with rfl | rfl <;> simp
  have hchiX : chi x ≠ 0 := by
    intro hzero
    apply hxData.2
    rw [hphiValue, hzero, mul_zero]
  let inclusion : L ↪ G := ⟨Subtype.val, Subtype.val_injective⟩
  have hfiber :
      (cyclicGenerators L).map inclusion = generatedFiber A phi L := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hz
      have hyL : Subgroup.zpowers (y : G) = L :=
        (FTTypePGeneratorBoundsInternal.mem_cyclicGenerators_iff_zpowers_coe_eq
          L y).mp hy
      have hxy : Subgroup.zpowers x = Subgroup.zpowers (y : G) :=
        hxL.trans hyL.symm
      have hyA : (y : G) ∈ A := hclosed hxData.1 hxy
      have hyChi : chi (y : G) ≠ 0 :=
        FTTypePGeneratorBoundsInternal.irreducible_ne_zero_of_zpowers_eq
          chi hxy hchiX
      have hyPhi : phi (y : G) ≠ 0 := by
        rw [hphiValue]
        exact mul_ne_zero hepsilon0 hyChi
      simp only [inclusion, generatedFiber, nonzeroPart,
        Finset.mem_filter]
      exact ⟨⟨(by simpa [FTTypePBoundsInfrastructureInternal.finiteSet]
        using hyA), hyPhi⟩, hyL⟩
    · intro hz
      have hzData :
          (z ∈ A ∧ phi z ≠ 0) ∧ Subgroup.zpowers z = L := by
        simpa [generatedFiber, nonzeroPart,
          FTTypePBoundsInfrastructureInternal.finiteSet] using hz
      have hzL : z ∈ L := by
        rw [← hzData.2]
        exact Subgroup.mem_zpowers z
      let zL : L := ⟨z, hzL⟩
      have hzGenerator : zL ∈ cyclicGenerators L :=
        (FTTypePGeneratorBoundsInternal.mem_cyclicGenerators_iff_zpowers_coe_eq
          L zL).mpr (by simpa only [zL] using hzData.2)
      exact Finset.mem_map.mpr ⟨zL, hzGenerator, rfl⟩
  have hVnonzero : ∀ y ∈ cyclicGenerators L, V.character y ≠ 0 := by
    intro y hy
    have hyL : Subgroup.zpowers (y : G) = L :=
      (FTTypePGeneratorBoundsInternal.mem_cyclicGenerators_iff_zpowers_coe_eq
        L y).mp hy
    have hxy : Subgroup.zpowers x = Subgroup.zpowers (y : G) :=
      hxL.trans hyL.symm
    have hyChi : chi (y : G) ≠ 0 :=
      FTTypePGeneratorBoundsInternal.irreducible_ne_zero_of_zpowers_eq
        chi hxy hchiX
    change chi.representation.character (y : G) ≠ 0
    simpa only [IrreducibleCharacter.representation_character] using hyChi
  have hnorm (y : L) :
      Complex.normSq (V.character y) =
        Complex.normSq (phi (y : G)) := by
    have hcharacter : V.character y = chi (y : G) := by
      change chi.representation.character (y : G) = chi (y : G)
      exact chi.representation_character (y : G)
    rw [hcharacter, hphiValue, hepsilonNorm]
  calc
    ((generatedFiber A phi L).card : ℝ) =
        ((cyclicGenerators L).card : ℝ) := by
      rw [← hfiber, Finset.card_map]
    _ ≤ ∑ y ∈ cyclicGenerators L, Complex.normSq (V.character y) :=
      FTTypePGeneratorBoundsInternal.sumNormSq_character_generators V hVnonzero
    _ = ∑ y ∈ cyclicGenerators L, Complex.normSq (phi (y : G)) := by
      apply Finset.sum_congr rfl
      intro y _
      exact hnorm y
    _ = ∑ z ∈ generatedFiber A phi L, Complex.normSq (phi z) := by
      rw [← hfiber]
      simp only [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro y _
      have hyval : inclusion y = (y : G) := rfl
      rw [hyval]

private theorem nonzeroPart_card_le_sumNormSq
    (A : Set G) (phi : ClassFunction G ℂ)
    (hfiber : ∀ L ∈ generatedSubgroups A phi,
      ((generatedFiber A phi L).card : ℝ) ≤
        ∑ x ∈ generatedFiber A phi L, Complex.normSq (phi x)) :
    ((nonzeroPart A phi).card : ℝ) ≤ ftTypePSumNormSq A phi := by
  have hmaps : ∀ x ∈ nonzeroPart A phi,
      Subgroup.zpowers x ∈ generatedSubgroups A phi := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hcardNat :
      (nonzeroPart A phi).card =
        ∑ L ∈ generatedSubgroups A phi, (generatedFiber A phi L).card := by
    simpa only [generatedFiber] using
      (Finset.card_eq_sum_card_fiberwise
        (s := nonzeroPart A phi) (t := generatedSubgroups A phi)
        (f := fun x ↦ Subgroup.zpowers x) hmaps)
  have hcardReal :
      ((nonzeroPart A phi).card : ℝ) =
        ∑ L ∈ generatedSubgroups A phi,
          ((generatedFiber A phi L).card : ℝ) := by
    simpa only [Nat.cast_sum] using
      congrArg (fun n : ℕ ↦ (n : ℝ)) hcardNat
  have hsumFibers :
      (∑ L ∈ generatedSubgroups A phi,
          ∑ x ∈ generatedFiber A phi L, Complex.normSq (phi x)) =
        ∑ x ∈ nonzeroPart A phi, Complex.normSq (phi x) := by
    simpa only [generatedFiber] using
      (Finset.sum_fiberwise_of_maps_to
        (s := nonzeroPart A phi) (t := generatedSubgroups A phi) hmaps
        (fun x ↦ Complex.normSq (phi x)))
  calc
    ((nonzeroPart A phi).card : ℝ) =
        ∑ L ∈ generatedSubgroups A phi,
          ((generatedFiber A phi L).card : ℝ) := hcardReal
    _ ≤ ∑ L ∈ generatedSubgroups A phi,
        ∑ x ∈ generatedFiber A phi L, Complex.normSq (phi x) := by
      apply Finset.sum_le_sum
      intro L hL
      exact hfiber L hL
    _ = ∑ x ∈ nonzeroPart A phi, Complex.normSq (phi x) := hsumFibers
    _ = ftTypePSumNormSq A phi := by
      unfold nonzeroPart ftTypePSumNormSq
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro x hxA hxFilter
      have hzero : phi x = 0 := by
        by_contra hne
        exact hxFilter (Finset.mem_filter.mpr ⟨hxA, hne⟩)
      simp [hzero]

private theorem signedIrreducible_nonFitting_count
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (K : Subgroup G) (phi : ClassFunction G ℂ)
    (chi : IrreducibleCharacter G ℂ) (epsilon : ℤ)
    (hepsilon : IsSign epsilon)
    (hphi : phi = (epsilon : ℂ) • (chi : ClassFunction G ℂ)) :
    ((nonzeroPart (ftTypePNonFittingSet ctx K) phi).card : ℝ) ≤
      ftTypePSumNormSq (ftTypePNonFittingSet ctx K) phi := by
  apply nonzeroPart_card_le_sumNormSq
  intro L hL
  exact signedIrreducible_fiber_bound
    (ftTypePNonFittingSet ctx K) phi chi epsilon hepsilon hphi
    (fun hx hxy ↦
      FTTypePCyclicRectangleInternal.nonFitting_mem_of_zpowers_eq
        ctx K hx hxy)
    L hL

private theorem coherentRow_nonFitting_count
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (K : Subgroup G)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (lambda : ClassFunction S ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (hcalS : lambda ∈ ftTypePCoreFamily S)
    (hirr : lambda ∈ irr_Ind_Fitting S) :
    ((nonzeroPart (ftTypePNonFittingSet ctx K) (tau1 lambda)).card : ℝ) ≤
      ftTypePSumNormSq (ftTypePNonFittingSet ctx K) (tau1 lambda) := by
  obtain ⟨chi, epsilon, hepsilon, hrow⟩ :=
    FTTypePGeneratorBoundsInternal.tau1_lambda_eq_signed_irreducible
      ctx tau1 lambda hcoh hcalS hirr
  exact signedIrreducible_nonFitting_count
    ctx K (tau1 lambda) chi epsilon hepsilon hrow

private theorem eta10_nonFitting_count
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) (K : Subgroup G) :
    ((nonzeroPart (ftTypePNonFittingSet ctx K) (ftTypePEta10 ctx)).card : ℝ) ≤
      ftTypePSumNormSq (ftTypePNonFittingSet ctx K) (ftTypePEta10 ctx) := by
  obtain ⟨chi, epsilon, hepsilon, hrow⟩ :=
    FTTypePGeneratorBoundsInternal.eta10_eq_signed_irreducible ctx
  exact signedIrreducible_nonFitting_count
    ctx K (ftTypePEta10 ctx) chi epsilon hepsilon hrow

private theorem two_nonzero_loci_cover_bound
    (A : Set G) (phi psi : ClassFunction G ℂ)
    (hcover : ∀ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet A,
      phi x ≠ 0 ∨ psi x ≠ 0)
    (hphi : ((nonzeroPart A phi).card : ℝ) ≤ ftTypePSumNormSq A phi)
    (hpsi : ((nonzeroPart A psi).card : ℝ) ≤ ftTypePSumNormSq A psi) :
    (ftTypePSetCard A : ℝ) ≤
      ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet A,
        (Complex.normSq (phi x) + Complex.normSq (psi x)) := by
  have hsubset :
      FTTypePBoundsInfrastructureInternal.finiteSet A ⊆
        nonzeroPart A phi ∪ nonzeroPart A psi := by
    intro x hx
    rcases hcover x hx with hxPhi | hxPsi
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hx, hxPhi⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hx, hxPsi⟩)
  have hcard :
      (FTTypePBoundsInfrastructureInternal.finiteSet A).card ≤
        (nonzeroPart A phi).card + (nonzeroPart A psi).card :=
    (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hcardReal :
      ((FTTypePBoundsInfrastructureInternal.finiteSet A).card : ℝ) ≤
        ((nonzeroPart A phi).card : ℝ) +
          ((nonzeroPart A psi).card : ℝ) := by
    exact_mod_cast hcard
  calc
    (ftTypePSetCard A : ℝ) =
        ((FTTypePBoundsInfrastructureInternal.finiteSet A).card : ℝ) := rfl
    _ ≤ ((nonzeroPart A phi).card : ℝ) +
        ((nonzeroPart A psi).card : ℝ) := hcardReal
    _ ≤ ftTypePSumNormSq A phi + ftTypePSumNormSq A psi :=
      add_le_add hphi hpsi
    _ = ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet A,
        (Complex.normSq (phi x) + Complex.normSq (psi x)) := by
      simp only [ftTypePSumNormSq, Finset.sum_add_distrib]

/-! ## Final lower bound -/

/-- Peterfalvi's cyclic cover of the complement of the two Fitting class
supports. -/
theorem sum_nonFitting_lb
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (K : Subgroup G)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (lambda : ClassFunction S ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (hTIred : typeP_TIred_coherent ctx tau1)
    (hcalS : lambda ∈ ftTypePCoreFamily S)
    (hirr : lambda ∈ irr_Ind_Fitting S) :
    (ftTypePSetCard (ftTypePNonFittingSet ctx K) : ℝ) ≤
      ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (ftTypePNonFittingSet ctx K),
        (Complex.normSq (tau1 lambda x) +
          Complex.normSq (ftTypePEta10 ctx x)) := by
  obtain ⟨b, hrow⟩ :=
    FTTypePCyclicRectangleInternal.tau1_lambda_eq_etaRightColumn_on_nonFitting
      ctx K tau1 lambda hcoh hTIred hcalS hirr
  apply two_nonzero_loci_cover_bound
  · intro x hx
    have hxNonFitting : x ∈ ftTypePNonFittingSet ctx K := by
      simpa [FTTypePBoundsInfrastructureInternal.finiteSet] using hx
    by_contra hzero
    rw [not_or, not_ne_iff, not_ne_iff] at hzero
    apply signedRightColumn_and_eta10_not_both_zero ctx b x
    · rw [← hrow x hxNonFitting, hzero.1]
    · exact hzero.2
  · exact coherentRow_nonFitting_count
      ctx K tau1 lambda hcoh hcalS hirr
  · exact eta10_nonFitting_count ctx K

end FTTypePCyclicCoverInternal

end

end Submission.OddOrder.PF
