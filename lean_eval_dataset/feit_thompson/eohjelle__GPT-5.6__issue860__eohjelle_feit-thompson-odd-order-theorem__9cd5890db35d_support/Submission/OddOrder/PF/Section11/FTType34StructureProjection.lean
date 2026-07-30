import Submission.OddOrder.PF.Section11.FTType34StructureNonorthogonality

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open PTypeCoreContextInternal
open scoped BigOperators Classical Pointwise IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {M U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) ftType34ProjectionFintypeOfFinite
    (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace FTType34StructureInternal

/-!
# Peterfalvi (11.9)(a): zero-row projection

This phase derives the zero-row projection from the preceding
nonorthogonality theorem and the canonical Section 11 infrastructure.
-/

local instance ftType34ProjectionInvertibleNatCardComplex
    {Q : Type} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private theorem pairing_sub_left_projection34
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing (a - b) c =
      characterPairing a c - characterPairing b c := by
  change characterPairingRight c (a - b) = _
  exact map_sub (characterPairingRight c) a b

private theorem pairing_sub_right_projection34
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing a (b - c) =
      characterPairing a b - characterPairing a c := by
  change characterPairingLeft a (b - c) = _
  exact map_sub (characterPairingLeft a) b c

private theorem ftType34S1_mem_referenceFamily_projection34
    (base : FTType34Base M U W W₁ W₂ defW)
    {zeta : ClassFunction M ℂ}
    (hzeta : zeta ∈ ftType34S1 base) :
    zeta ∈ FTType345ConstantsInternal.ftType345InducedFamily10 M := by
  have hderived : base.HU = derivedWithin M := by
    calc
      base.HU = FTcore M := base.FTcore_eq_HU.symm
      _ = derivedWithin M := FTcore_type_gt2 M base.type_gt_two
  have hK : base.HUInM =
      FTType345ConstantsInternal.ftType345DerivedInM M := by
    simp only [FTType34Base.HUInM,
      FTType345ConstantsInternal.ftType345DerivedInM, hderived]
  rw [ftType34S1, ftType34Layer] at hzeta
  rw [FTType345ConstantsInternal.ftType345InducedFamily10, ← hK]
  exact seqIndS base.HUInM
    (Iirr_kerDS (k := ℂ) (bot_le : (⊥ : Subgroup base.HUInM) ≤ base.HCInHU)
      (le_rfl : (⊤ : Subgroup base.HUInM) ≤ ⊤)) hzeta

private def ftType34S1_referenceChoice_projection34
    (base : FTType34Base M U W W₁ W₂ defW)
    {zeta : ClassFunction M ℂ}
    (hzeta : zeta ∈ ftType34S1 base) :
    FTType345ReferenceChoice M W₁ zeta where
  irreducible := ftType34S1_irreducible34 base zeta hzeta
  mem_calS := ftType34S1_mem_referenceFamily_projection34 base hzeta
  degree := ftType34S1_degree34 base zeta hzeta

theorem zeroColumn_fullSupport_projection34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta) :
    muZero34 base - zeta ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport M} := by
  let K : Subgroup M :=
    FTType345ConstantsInternal.ftType345DerivedInM M
  letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 M
  have hindex : K.index = Nat.card W₁ := by
    have houter : IsInternalSemidirectProductIn
        (derivedWithin M) W₁ M := base.MtypeP.1.2.2.2
    calc
      K.index = Nat.card (W₁.subgroupOf M) :=
        houter.2.2.2.symm.index_eq_card
      _ = Nat.card W₁ :=
        MathlibSupport.natCard_subgroupOf_eq houter.2.1
  have hbase := cfInd1_sub_lin_on (k := ℂ) K hzeta.mem_calS (by
    rw [hzeta.degree, hindex])
  rw [← base.primeTI.prTIred0 base.isoM] at hbase
  rw [ClassFunction.mem_supportedOn_iff] at hbase ⊢
  intro x hx
  apply hbase x
  intro hxK
  apply hx
  have hxDerived : (x : G) ∈ subgroupNonidentity (derivedWithin M) :=
    ⟨hxK.1, fun hxOne ↦ hxK.2 (Subtype.ext hxOne)⟩
  change (x : G) ∈ FTsupport M
  rw [FTsupp_eq1 base.maxM base.type_gt_two,
    FTsupp1_type_gt2 M base.type_gt_two]
  exact hxDerived

private theorem mapRingHom_muZero_projection34
    (base : FTType34Base M U W W₁ W₂ defW)
    (sigma : ℂ ≃+* ℂ) :
    ClassFunction.mapRingHom sigma.toRingHom (muZero34 base) =
      muZero34 base := by
  classical
  have hsum :
      muZero34 base =
        ∑ i : IrreducibleCharacter W₁ ℂ,
          base.primeTI.primeTICharacter base.isoM i
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂ ℂ) := by
    exact base.primeTI.primeTIRed_eq_sum base.isoM
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
  calc
    ClassFunction.mapRingHom sigma.toRingHom (muZero34 base) =
        ClassFunction.mapRingHom sigma.toRingHom
          (∑ i : IrreducibleCharacter W₁ ℂ,
            base.primeTI.primeTICharacter base.isoM i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) :=
      congrArg (ClassFunction.mapRingHom sigma.toRingHom) hsum
    _ = ∑ i : IrreducibleCharacter W₁ ℂ,
          ClassFunction.mapRingHom sigma.toRingHom
            (base.primeTI.primeTICharacter base.isoM i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) := by
      rw [map_sum]
    _ = ∑ i : IrreducibleCharacter W₁ ℂ,
          base.primeTI.primeTICharacter base.isoM i
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂ ℂ) := by
      apply Fintype.sum_equiv
        (IrreducibleCharacter.equivOfRingEquiv sigma)
      intro i
      change
        ClassFunction.mapRingHom sigma.toRingHom
            (base.primeTI.primeTIIndex base.isoM
              (i, (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) : ClassFunction M ℂ) =
          (base.primeTI.primeTIIndex base.isoM
            (IrreducibleCharacter.mapRingEquiv sigma i,
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) : ClassFunction M ℂ)
      rw [ClassFunction.mapRingHom_irreducible]
      change
        (IrreducibleCharacter.mapRingEquiv sigma
            (base.primeTI.primeTIIndex base.isoM
              (i, (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ))) : ClassFunction M ℂ) =
          (base.primeTI.primeTIIndex base.isoM
            (IrreducibleCharacter.mapRingEquiv sigma i,
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) : ClassFunction M ℂ)
      rw [← base.primeTI.primeTIIndex_mapRingEquiv base.isoM sigma,
        IrreducibleCharacter.mapRingEquiv_trivial]
    _ = muZero34 base := hsum.symm

private theorem mapRingHom_cyclicTIImage_projection34
    (base : FTType34Base M U W W₁ W₂ defW)
    (sigma : ℂ ≃+* ℂ)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.mapRingHom sigma.toRingHom
        (base.isoG.cyclicTIImage (i, j)) =
      base.isoG.cyclicTIImage
        (IrreducibleCharacter.mapRingEquiv sigma i,
          IrreducibleCharacter.mapRingEquiv sigma j) := by
  let source : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW i j
  let target : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW
      (IrreducibleCharacter.mapRingEquiv sigma i)
      (IrreducibleCharacter.mapRingEquiv sigma j)
  have hsourceIrr :
      IrreducibleCharacter.mapRingEquiv sigma source = target := by
    calc
      IrreducibleCharacter.mapRingEquiv sigma source =
          IrreducibleCharacter.cyclicTICharacter defW
            (IrreducibleCharacter.mapRingEquiv sigma i)
            (IrreducibleCharacter.mapRingEquiv sigma j) := by
        simpa only [source] using
          (IrreducibleCharacter.cyclicTICharacter_mapRingEquiv
            defW sigma i j).symm
      _ = target := rfl
  have hsource :
      ClassFunction.mapRingHom sigma.toRingHom
          (source : ClassFunction W ℂ) =
        (target : ClassFunction W ℂ) := by
    calc
      ClassFunction.mapRingHom sigma.toRingHom
          (source : ClassFunction W ℂ) =
          (IrreducibleCharacter.mapRingEquiv sigma source :
            ClassFunction W ℂ) :=
        ClassFunction.mapRingHom_irreducible sigma source
      _ = (target : ClassFunction W ℂ) :=
        congrArg
          (fun chi : IrreducibleCharacter W ℂ ↦
            (chi : ClassFunction W ℂ)) hsourceIrr
  rw [CyclicTIIsometryData.cyclicTIImage,
    CyclicTIIsometryData.cyclicTIImage,
    base.isoG.mapRingEquiv_cyclicTIIsometry]
  exact congrArg base.isoG.linearMap hsource

private theorem characterPairing_mapRingEquiv_projection34
    {Q : Type} [Group Q] [Fintype Q]
    (sigma : ℂ ≃+* ℂ)
    (f g : ClassFunction Q ℂ) :
    characterPairing
        (ClassFunction.mapRingHom sigma.toRingHom f)
        (ClassFunction.mapRingHom sigma.toRingHom g) =
      sigma (characterPairing f g) := by
  simp only [characterPairing, ClassFunction.mapRingHom_apply,
    map_mul, map_inv₀, map_natCast, map_sum]
  rfl

private theorem mapRingEquiv_ne_trivial_projection34
    {Q : Type} [Group Q] [Fintype Q]
    (sigma : ℂ ≃+* ℂ)
    (chi : IrreducibleCharacter Q ℂ)
    (hchi : chi ≠ IrreducibleCharacter.trivial) :
    IrreducibleCharacter.mapRingEquiv sigma chi ≠
      IrreducibleCharacter.trivial := by
  intro h
  rw [← IrreducibleCharacter.mapRingEquiv_trivial sigma] at h
  exact hchi ((IrreducibleCharacter.equivOfRingEquiv sigma).injective h)

private theorem rectangle_zeroRow_of_support_projection34
    {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (i₀ : I) (j₀ : J)
    (hI : 3 ≤ Fintype.card I) (hJ : 3 ≤ Fintype.card J)
    (h₀₀ : a i₀ j₀ = 1)
    (hrectangle : ∀ i j,
      a i j + a i₀ j₀ = a i j₀ + a i₀ j)
    (hleftOrbit : ∀ i k, i ≠ i₀ → k ≠ i₀ →
      (a i j₀ ≠ 0 ↔ a k j₀ ≠ 0))
    (hrightOrbit : ∀ j ell, j ≠ j₀ → ell ≠ j₀ →
      (a i₀ j ≠ 0 ↔ a i₀ ell ≠ 0))
    (hinteriorRight : ∀ i j ell,
      i ≠ i₀ → j ≠ j₀ → ell ≠ j₀ → a i j ≠ 0 →
        ∃ k, k ≠ i₀ ∧ a k ell ≠ 0)
    (hinteriorLeft : ∀ i j k,
      i ≠ i₀ → j ≠ j₀ → k ≠ i₀ → a i j ≠ 0 →
        ∃ ell, ell ≠ j₀ ∧ a k ell ≠ 0)
    (hbound :
      (Finset.univ.filter
        (fun ij : I × J ↦ a ij.1 ij.2 ≠ 0)).card ≤
          Fintype.card I + 1)
    (hnotColumn : ¬ ∀ i j,
      a i j = if j = j₀ then 1 else 0) :
    ∀ i j, a i j = if i = i₀ then 1 else 0 := by
  classical
  let A : Finset (I × J) :=
    Finset.univ.filter (fun ij ↦ a ij.1 ij.2 ≠ 0)
  have hA : A.card ≤ Fintype.card I + 1 := by
    simpa only [A] using hbound
  have hfullRectangleFalse
      (hfull : ∀ i j, i ≠ i₀ → j ≠ j₀ → a i j ≠ 0) : False := by
    let B : Finset (I × J) :=
      insert (i₀, j₀) ((Finset.univ.erase i₀).product
        (Finset.univ.erase j₀))
    have hBA : B ⊆ A := by
      intro ij hij
      rw [Finset.mem_insert] at hij
      rcases hij with rfl | hij
      · simp [A, h₀₀]
      · rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
        have hi' : ij.1 ≠ i₀ := Finset.ne_of_mem_erase hi
        have hj' : ij.2 ≠ j₀ := Finset.ne_of_mem_erase hj
        simp [A, hfull ij.1 ij.2 hi' hj']
    have hnotmem : (i₀, j₀) ∉
        (Finset.univ.erase i₀).product (Finset.univ.erase j₀) := by
      simp
    have hBcard : B.card =
        (Fintype.card I - 1) * (Fintype.card J - 1) + 1 := by
      rw [show B = insert (i₀, j₀)
          ((Finset.univ.erase i₀).product
            (Finset.univ.erase j₀)) from rfl,
        Finset.card_insert_of_notMem hnotmem]
      simp
    have hle : B.card ≤ A.card := Finset.card_le_card hBA
    rw [hBcard] at hle
    have hfactor : 2 ≤ Fintype.card J - 1 := by omega
    have hmul : (Fintype.card I - 1) * 2 ≤
        (Fintype.card I - 1) * (Fintype.card J - 1) :=
      Nat.mul_le_mul_left (Fintype.card I - 1) hfactor
    omega
  have hframeFalse
      (hleft : ∀ i, i ≠ i₀ → a i j₀ ≠ 0)
      (hright : ∀ j, j ≠ j₀ → a i₀ j ≠ 0) : False := by
    let L : Finset (I × J) :=
      (Finset.univ.erase i₀).product ({j₀} : Finset J)
    let R : Finset (I × J) :=
      ({i₀} : Finset I).product (Finset.univ.erase j₀)
    let B : Finset (I × J) := insert (i₀, j₀) (L ∪ R)
    have hLR : Disjoint L R := by
      rw [Finset.disjoint_left]
      intro ij hijL hijR
      have hiL := (Finset.mem_product.mp hijL).1
      have hiR := (Finset.mem_product.mp hijR).1
      have hne : ij.1 ≠ i₀ := Finset.ne_of_mem_erase hiL
      exact hne (by simpa using hiR)
    have hpoint : (i₀, j₀) ∉ L ∪ R := by
      simp [L, R]
    have hBA : B ⊆ A := by
      intro ij hij
      rw [Finset.mem_insert] at hij
      rcases hij with rfl | hij
      · simp [A, h₀₀]
      · rcases Finset.mem_union.mp hij with hij | hij
        · rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
          have hi' : ij.1 ≠ i₀ := Finset.ne_of_mem_erase hi
          have hj' : ij.2 = j₀ := by simpa using hj
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
          simpa [hj'] using hleft ij.1 hi'
        · rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
          have hi' : ij.1 = i₀ := by simpa using hi
          have hj' : ij.2 ≠ j₀ := Finset.ne_of_mem_erase hj
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
          simpa [hi'] using hright ij.2 hj'
    have hLcard : L.card = Fintype.card I - 1 := by
      simp [L, Finset.card_product]
    have hRcard : R.card = Fintype.card J - 1 := by
      simp [R, Finset.card_product]
    have hBcard : B.card =
        (Fintype.card I - 1) + (Fintype.card J - 1) + 1 := by
      rw [show B = insert (i₀, j₀) (L ∪ R) from rfl,
        Finset.card_insert_of_notMem hpoint,
        Finset.card_union_of_disjoint hLR, hLcard, hRcard]
    have hle : B.card ≤ A.card := Finset.card_le_card hBA
    rw [hBcard] at hle
    omega
  have hIone : 1 < Fintype.card I := by omega
  have hJone : 1 < Fintype.card J := by omega
  obtain ⟨i₁, hi₁⟩ := Fintype.exists_ne_of_one_lt_card hIone i₀
  obtain ⟨j₁, hj₁⟩ := Fintype.exists_ne_of_one_lt_card hJone j₀
  have hnotBoth : ¬ (a i₁ j₀ ≠ 0 ∧ a i₀ j₁ ≠ 0) := by
    rintro ⟨hli, hrj⟩
    apply hframeFalse
    · intro i hi
      exact (hleftOrbit i₁ i hi₁ hi).mp hli
    · intro j hj
      exact (hrightOrbit j₁ j hj₁ hj).mp hrj
  by_cases hleft₁ : a i₁ j₀ = 0
  · have hleftZero : ∀ i, i ≠ i₀ → a i j₀ = 0 := by
      intro i hi
      by_contra hne
      have := (hleftOrbit i i₁ hi hi₁).mp hne
      exact this hleft₁
    have hrightOne : ∀ j, j ≠ j₀ → a i₀ j = 1 := by
      intro j hj
      by_contra hneOne
      have hseed : a i₁ j ≠ 0 := by
        intro hzero
        have hrect := hrectangle i₁ j
        rw [hzero, hleftZero i₁ hi₁, h₀₀, zero_add] at hrect
        exact hneOne (by simpa only [zero_add] using hrect.symm)
      apply hfullRectangleFalse
      intro i ell hi hell
      obtain ⟨k, hk, hkell⟩ :=
        hinteriorRight i₁ j ell hi₁ hj hell hseed
      intro hzero
      apply hkell
      apply add_right_cancel (b := a i₀ j₀)
      calc
        a k ell + a i₀ j₀ = a k j₀ + a i₀ ell :=
          hrectangle k ell
        _ = a i j₀ + a i₀ ell := by
          rw [hleftZero k hk, hleftZero i hi]
        _ = a i ell + a i₀ j₀ := (hrectangle i ell).symm
        _ = 0 + a i₀ j₀ := by rw [hzero]
    have hinteriorZero : ∀ i j,
        i ≠ i₀ → j ≠ j₀ → a i j = 0 := by
      intro i j hi hj
      apply add_right_cancel (b := a i₀ j₀)
      calc
        a i j + a i₀ j₀ = a i j₀ + a i₀ j :=
          hrectangle i j
        _ = 0 + a i₀ j₀ := by
          rw [hleftZero i hi, hrightOne j hj, h₀₀]
    intro i j
    by_cases hi : i = i₀
    · subst i
      rw [if_pos rfl]
      by_cases hj : j = j₀
      · subst j
        exact h₀₀
      · exact hrightOne j hj
    · rw [if_neg hi]
      by_cases hj : j = j₀
      · subst j
        exact hleftZero i hi
      · exact hinteriorZero i j hi hj
  · have hleftNZ : a i₁ j₀ ≠ 0 := hleft₁
    have hright₁ : a i₀ j₁ = 0 := by
      by_contra hrightNZ
      exact hnotBoth ⟨hleftNZ, hrightNZ⟩
    have hrightZero : ∀ j, j ≠ j₀ → a i₀ j = 0 := by
      intro j hj
      by_contra hne
      have := (hrightOrbit j j₁ hj hj₁).mp hne
      exact this hright₁
    have hleftOne : ∀ i, i ≠ i₀ → a i j₀ = 1 := by
      intro i hi
      by_contra hneOne
      have hseed : a i j₁ ≠ 0 := by
        intro hzero
        have hrect := hrectangle i j₁
        rw [hzero, hrightZero j₁ hj₁, h₀₀, add_zero] at hrect
        exact hneOne (by simpa only [zero_add] using hrect.symm)
      apply hfullRectangleFalse
      intro k ell hk hell
      obtain ⟨j, hj, hkj⟩ :=
        hinteriorLeft i j₁ k hi hj₁ hk hseed
      intro hzero
      apply hkj
      apply add_right_cancel (b := a i₀ j₀)
      calc
        a k j + a i₀ j₀ = a k j₀ + a i₀ j :=
          hrectangle k j
        _ = a k j₀ + a i₀ ell := by
          rw [hrightZero j hj, hrightZero ell hell]
        _ = a k ell + a i₀ j₀ := (hrectangle k ell).symm
        _ = 0 + a i₀ j₀ := by rw [hzero]
    have hinteriorZero : ∀ i j,
        i ≠ i₀ → j ≠ j₀ → a i j = 0 := by
      intro i j hi hj
      apply add_right_cancel (b := a i₀ j₀)
      calc
        a i j + a i₀ j₀ = a i j₀ + a i₀ j :=
          hrectangle i j
        _ = 0 + a i₀ j₀ := by
          rw [hleftOne i hi, hrightZero j hj, h₀₀]
          ring
    exfalso
    apply hnotColumn
    intro i j
    by_cases hj : j = j₀
    · subst j
      rw [if_pos rfl]
      by_cases hi : i = i₀
      · subst i
        exact h₀₀
      · exact hleftOne i hi
    · rw [if_neg hj]
      by_cases hi : i = i₀
      · subst i
        exact hrightZero j hj
      · exact hinteriorZero i j hi hj

theorem FTtype34_zeroRowProjection34
    (base : FTType34Base M U W W₁ W₂ defW) :
    ∀ zeta ∈ ftType34S1 base,
      eqProjection34 base (dadeBridgeZero34 base zeta)
        (etaZeroRow34 base) := by
  classical
  intro zeta hzeta
  let pti := base.primeTI
  let isoM := base.isoM
  let isoG := base.isoG
  let dd := FT_Dade0_hyp M base.maxM
  let i₀ : IrreducibleCharacter W₁ ℂ := IrreducibleCharacter.trivial
  let j₀ : IrreducibleCharacter W₂ ℂ := IrreducibleCharacter.trivial
  let phi : ClassFunction M ℂ := muZero34 base - zeta
  let psi : ClassFunction (⊤ : Subgroup G) ℂ := Dade dd phi
  let a (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) : ℂ :=
    characterPairing psi (isoG.cyclicTIImage (i, j))
  let hzetaRef : FTType345ReferenceChoice M W₁ zeta :=
    ftType34S1_referenceChoice_projection34 base hzeta

  have hzetaVirtual : ClassFunction.IsVirtual zeta :=
    ⟨Finsupp.single ⟨zeta, hzetaRef.irreducible⟩ 1, by simp⟩
  have hphiVirtual : ClassFunction.IsVirtual phi := by
    exact (pti.prTIred_char isoM j₀).isVirtual.sub hzetaVirtual
  have hphiFull : phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport M} := by
    exact zeroColumn_fullSupport_projection34 base zeta hzetaRef
  have hphiSupport : phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
    rw [ClassFunction.mem_supportedOn_iff] at hphiFull ⊢
    intro x hx
    apply hphiFull x
    intro hxFull
    exact hx (FTsupp_sub0 M hxFull)
  obtain ⟨phiZ, hphiZ⟩ := hphiVirtual
  have hphiVirtual' : ClassFunction.IsVirtual phi := ⟨phiZ, hphiZ⟩
  obtain ⟨psiZ, hpsiZ, _⟩ := (Dade_Zisometry dd).2 phiZ (by
    simpa [phi, hphiZ] using hphiSupport)
  have hpsiVirtual : ClassFunction.IsVirtual psi := by
    exact ⟨psiZ, by simpa [psi, phi, hphiZ] using hpsiZ.symm⟩
  have hpsiZRealize : VirtualCharacter.realize psiZ = psi := by
    simpa [psi, phi, hphiZ] using hpsiZ.symm

  have hmuZ : characterPairing (muZero34 base) zeta = 0 := by
    rw [muZero34, mu34, pti.primeTIRed_eq_sum]
    change characterPairingRight zeta
      (∑ i : IrreducibleCharacter W₁ ℂ,
        pti.primeTICharacter isoM i j₀) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    exact FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      base.MtypeP zeta hzetaRef i j₀
  have hzMu : characterPairing zeta (muZero34 base) = 0 := by
    rw [characterPairing_comm, hmuZ]
  have hmuNorm : characterPairing (muZero34 base) (muZero34 base) =
      (base.q : ℂ) := by
    exact pti.cfnorm_prTIred isoM j₀
  have hzetaNorm : characterPairing zeta zeta = 1 :=
    IrreducibleCharacter.characterPairing_self
      ⟨zeta, hzetaRef.irreducible⟩
  have hphiNorm : characterPairing phi phi = (base.q + 1 : ℂ) := by
    simp only [phi]
    rw [pairing_sub_left_projection34,
      pairing_sub_right_projection34,
      pairing_sub_right_projection34]
    rw [hmuNorm, hmuZ, hzMu, hzetaNorm]
    push_cast
    ring
  have hpsiNorm : characterPairing psi psi = (base.q + 1 : ℂ) := by
    calc
      characterPairing psi psi = starCharacterPairing psi psi :=
        (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hpsiVirtual hpsiVirtual).symm
      _ = starCharacterPairing phi phi := by
        simpa [psi] using Dade_isometry dd phi phi hphiSupport hphiSupport
      _ = characterPairing phi phi :=
        PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hphiVirtual' hphiVirtual'
      _ = (base.q + 1 : ℂ) := hphiNorm

  have h₀₀ : a i₀ j₀ = 1 := by
    let oneTop : ClassFunction (⊤ : Subgroup G) ℂ :=
      (IrreducibleCharacter.trivial :
        IrreducibleCharacter (⊤ : Subgroup G) ℂ)
    let oneM : ClassFunction M ℂ :=
      (IrreducibleCharacter.trivial : IrreducibleCharacter M ℂ)
    have heta₀₀ : isoG.cyclicTIImage (i₀, j₀) = oneTop := by
      change isoG.linearMap
          (IrreducibleCharacter.cyclicTICharacter defW i₀ j₀ :
            ClassFunction W ℂ) = oneTop
      rw [show i₀ = (IrreducibleCharacter.trivial :
          IrreducibleCharacter W₁ ℂ) from rfl,
        show j₀ = (IrreducibleCharacter.trivial :
          IrreducibleCharacter W₂ ℂ) from rfl,
        IrreducibleCharacter.cyclicTICharacter_trivial, isoG.map_trivial]
    have honeTopVirtual : ClassFunction.IsVirtual oneTop :=
      ⟨Finsupp.single (IrreducibleCharacter.trivial :
        IrreducibleCharacter (⊤ : Subgroup G) ℂ) 1, by simp [oneTop]⟩
    have honeMVirtual : ClassFunction.IsVirtual oneM :=
      ⟨Finsupp.single (IrreducibleCharacter.trivial :
        IrreducibleCharacter M ℂ) 1, by simp [oneM]⟩
    have hcomap : ClassFunction.comap
        (Subgroup.inclusion dd.2.1) oneTop = oneM := by
      ext x
      simp [oneTop, oneM]
    have hrecip := Dade_reciprocity dd phi oneTop hphiSupport (by
      intro x hx y
      simp [oneTop])
    have hstar : starCharacterPairing psi oneTop =
        starCharacterPairing phi oneM := by
      simpa [psi, hcomap] using hrecip
    have hpair : characterPairing psi oneTop =
        characterPairing phi oneM := by
      calc
        characterPairing psi oneTop = starCharacterPairing psi oneTop :=
          (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
            hpsiVirtual honeTopVirtual).symm
        _ = starCharacterPairing phi oneM := hstar
        _ = characterPairing phi oneM :=
          PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
            hphiVirtual' honeMVirtual
    have hmuTriv : characterPairing (muZero34 base) oneM = 1 := by
      rw [characterPairing_comm]
      have h := pti.cfdot_prTIirr_red isoM
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j₀ j₀
      rw [if_pos rfl] at h
      simpa [muZero34, mu34, oneM, j₀,
        PrimeTIHypothesis.primeTICharacter, pti.prTIirr00 isoM] using h
    have htrivZ : characterPairing oneM zeta = 0 := by
      have h :=
        FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
          base.MtypeP zeta hzetaRef
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j₀
      simpa [oneM, j₀, FTType345ConstantsInternal.ftType345Mu2,
        PrimeTIHypothesis.primeTICharacter, pti.prTIirr00 isoM] using h
    have hzetaTriv : characterPairing zeta oneM = 0 := by
      rw [characterPairing_comm, htrivZ]
    have hsource : characterPairing phi oneM = 1 := by
      rw [show phi = muZero34 base - zeta from rfl,
        pairing_sub_left_projection34, hmuTriv, hzetaTriv, sub_zero]
    change characterPairing psi (isoG.cyclicTIImage (i₀, j₀)) = 1
    rw [heta₀₀]
    exact hpair.trans hsource

  have hzero : Set.EqOn
      (fun w : W ↦ psi
        ⟨w, base.primeDade.prDade_cycTI.le_group w.property⟩)
      0 (cyclicTISetInW W W₁ W₂) := by
    intro w hwCyclic
    let wM : M := ⟨w, pti.directProduct_le_group w.property⟩
    let wTop : (⊤ : Subgroup G) :=
      ⟨w, base.primeDade.prDade_cycTI.le_group w.property⟩
    have hwAmbient : (w : G) ∈ cyclicTISet W W₁ W₂ := hwCyclic
    have hwClass : (w : G) ∈
        classSupportWithin M (cyclicTISet W W₁ W₂) :=
      ⟨(w : G), hwAmbient, 1, M.one_mem, by simp⟩
    have hwA₀ : (w : G) ∈ FTsupport0 M := by
      rw [FTtypeP_supp0_def defW base.maxM base.MtypeP]
      exact Or.inr hwClass
    have hwNotFull : (w : G) ∉ FTsupport M := by
      rw [FTsupp_eq1 base.maxM base.type_gt_two,
        FTsupp1_type_gt2 M base.type_gt_two]
      intro hwFull
      exact base.primeDade.prDade_supp_disjoint hwAmbient hwFull.1
    have hDade := Dade_id dd phi hwA₀
    change psi wTop = (0 : W → ℂ) w
    simp only [Pi.zero_apply]
    calc
      psi wTop = phi wM := by simpa [psi, wTop, wM] using hDade
      _ = 0 := ClassFunction.eq_zero_of_mem_supportedOn hphiFull hwNotFull

  letI : IsCyclic W₁ := pti.complement_cyclic
  letI : IsCyclic W₂ := pti.fixed_cyclic
  have hcard₁ : Fintype.card (IrreducibleCharacter W₁ ℂ) = base.q :=
    IrreducibleCharacter.card_eq_natCard_of_isCyclic
  have hcard₂ : Fintype.card (IrreducibleCharacter W₂ ℂ) = base.p :=
    IrreducibleCharacter.card_eq_natCard_of_isCyclic
  have hpsiZNorm : normSq psiZ = (base.q + 1 : ℤ) := by
    apply Int.cast_injective (α := ℂ)
    rw [← VirtualCharacter.characterPairing_realize_self,
      hpsiZRealize, hpsiNorm]
    push_cast
    rfl
  have hNCle : isoG.cyclicTINC psi ≤ base.q + 1 := by
    have hle := isoG.cyclicTINC_realize_le_normSq psiZ
    rw [hpsiZRealize, hpsiZNorm] at hle
    exact_mod_cast hle

  have hcohTop : coherent
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (Dade dd) := by
    exact (base.coherent_targetMap_iff
      (S := (↑(ftType34S1 base) : Set (ClassFunction M ℂ)))
      (A := nonidentitySet M) (sigma := Dade dd)).mp
        (ftType34S1_coherent34 base)
  obtain ⟨nu, hnu⟩ := hcohTop

  have hzetaMapMem (sigma : ℂ ≃+* ℂ) :
      ClassFunction.mapRingHom sigma.toRingHom zeta ∈ ftType34S1 base := by
    rw [ftType34S1, ftType34Layer] at hzeta ⊢
    exact cfAut_seqInd (k := ℂ) sigma base.HUInM ⊤ base.HCInHU hzeta
  have hDadeDiffOrtho (sigma : ℂ ≃+* ℂ)
      (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      characterPairing
          (Dade dd
            (zeta - ClassFunction.mapRingHom sigma.toRingHom zeta))
          (isoG.cyclicTIImage (i, j)) = 0 := by
    let zetaSigma := ClassFunction.mapRingHom sigma.toRingHom zeta
    have hzetaSigma : zetaSigma ∈ ftType34S1 base := hzetaMapMem sigma
    have hdiffClosure : zeta - zetaSigma ∈ AddSubgroup.closure
        (↑(ftType34S1 base) : Set (ClassFunction M ℂ)) :=
      (AddSubgroup.closure
        (↑(ftType34S1 base) : Set (ClassFunction M ℂ))).sub_mem
          (AddSubgroup.subset_closure hzeta)
          (AddSubgroup.subset_closure hzetaSigma)
    have hdiffOff : zeta - zetaSigma ∈
        ClassFunction.supportedOn (nonidentitySet M) := by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      have hxOne : x = 1 := by simpa [nonidentitySet] using not_not.mp hx
      subst x
      simp only [ClassFunction.sub_apply]
      rw [ftType34S1_degree34 base zeta hzeta,
        ftType34S1_degree34 base zetaSigma hzetaSigma, sub_self]
    have hagree : nu (zeta - zetaSigma) = Dade dd (zeta - zetaSigma) :=
      hnu.agrees _ hdiffClosure hdiffOff
    let wij : IrreducibleCharacter W ℂ :=
      IrreducibleCharacter.cyclicTICharacter defW i j
    have hS₁Kernel : cfConjC_subset
        (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
        (FTtypePKernelLayer base.primeDade) :=
      ⟨ftType34S1_subset_kernelLayer34 base,
        (ftType34S1_cfConjC_subset34 base).2⟩
    have hzetaOrth : characterPairing (nu zeta)
        (isoG.cyclicTIImage (i, j)) = 0 := by
      simpa [CyclicTIIsometryData.cyclicTIImage,
        CyclicTIIsometryData.cyclicTISourceIrreducible, wij] using
          coherent_ortho_cycTIiso base.primeDade isoM isoG (mFT_odd M)
            hS₁Kernel hnu hzeta
            (ftType34S1_irreducible34 base zeta hzeta) wij
    have hzetaSigmaOrth : characterPairing (nu zetaSigma)
        (isoG.cyclicTIImage (i, j)) = 0 := by
      simpa [CyclicTIIsometryData.cyclicTIImage,
        CyclicTIIsometryData.cyclicTISourceIrreducible, wij] using
          coherent_ortho_cycTIiso base.primeDade isoM isoG (mFT_odd M)
            hS₁Kernel hnu hzetaSigma
            (ftType34S1_irreducible34 base zetaSigma hzetaSigma) wij
    rw [← hagree, map_sub, pairing_sub_left_projection34,
      hzetaOrth, hzetaSigmaOrth, sub_self]

  have hmapPsi (sigma : ℂ ≃+* ℂ) :
      ClassFunction.mapRingHom sigma.toRingHom psi =
        psi + Dade dd
          (zeta - ClassFunction.mapRingHom sigma.toRingHom zeta) := by
    calc
      ClassFunction.mapRingHom sigma.toRingHom psi =
          Dade dd (ClassFunction.mapRingHom sigma.toRingHom phi) :=
        (Dade_aut dd sigma.toRingHom phi).symm
      _ = Dade dd
          (phi + (zeta - ClassFunction.mapRingHom sigma.toRingHom zeta)) := by
        congr 1
        dsimp only [phi]
        rw [map_sub, mapRingHom_muZero_projection34]
        abel
      _ = psi + Dade dd
          (zeta - ClassFunction.mapRingHom sigma.toRingHom zeta) := by
        rw [map_add]
  have hcoefficientMap (sigma : ℂ ≃+* ℂ)
      (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      a (IrreducibleCharacter.mapRingEquiv sigma i)
          (IrreducibleCharacter.mapRingEquiv sigma j) = sigma (a i j) := by
    have hpair := characterPairing_mapRingEquiv_projection34 sigma psi
      (isoG.cyclicTIImage (i, j))
    rw [hmapPsi sigma, mapRingHom_cyclicTIImage_projection34,
      characterPairing_add_left,
      hDadeDiffOrtho sigma
        (IrreducibleCharacter.mapRingEquiv sigma i)
        (IrreducibleCharacter.mapRingEquiv sigma j), add_zero] at hpair
    exact hpair

  have hrectangle : ∀ i j,
      a i j + a i₀ j₀ = a i j₀ + a i₀ j := by
    intro i j
    simpa [a, i₀, j₀, CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible] using
        isoG.pairing_exchange hzero i i₀ j j₀
  have hleftOrbit : ∀ i k, i ≠ i₀ → k ≠ i₀ →
      (a i j₀ ≠ 0 ↔ a k j₀ ≠ 0) := by
    intro i k hi hk
    obtain ⟨sigma, hsigma⟩ :=
      exists_prime_cyclic_irreducible_algEquiv base.q_prime
        pti.complement_cyclic i hi k hk
    have hmap := hcoefficientMap sigma.toRingEquiv i j₀
    rw [hsigma, IrreducibleCharacter.mapRingEquiv_trivial] at hmap
    constructor
    · intro h
      rw [hmap]
      exact (map_ne_zero sigma).2 h
    · intro h hzero'
      apply h
      rw [hmap, hzero', map_zero]
  have hrightOrbit : ∀ j ell, j ≠ j₀ → ell ≠ j₀ →
      (a i₀ j ≠ 0 ↔ a i₀ ell ≠ 0) := by
    intro j ell hj hell
    obtain ⟨sigma, hsigma⟩ :=
      exists_prime_cyclic_irreducible_algEquiv base.p_prime
        pti.fixed_cyclic j hj ell hell
    have hmap := hcoefficientMap sigma.toRingEquiv i₀ j
    rw [hsigma, IrreducibleCharacter.mapRingEquiv_trivial] at hmap
    constructor
    · intro h
      rw [hmap]
      exact (map_ne_zero sigma).2 h
    · intro h hzero'
      apply h
      rw [hmap, hzero', map_zero]
  have hinteriorRight : ∀ i j ell,
      i ≠ i₀ → j ≠ j₀ → ell ≠ j₀ → a i j ≠ 0 →
        ∃ k, k ≠ i₀ ∧ a k ell ≠ 0 := by
    intro i j ell hi hj hell hij
    obtain ⟨sigma, hsigma⟩ :=
      exists_prime_cyclic_irreducible_algEquiv base.p_prime
        pti.fixed_cyclic j hj ell hell
    let k := IrreducibleCharacter.mapRingEquiv sigma.toRingEquiv i
    have hk : k ≠ i₀ := by
      exact mapRingEquiv_ne_trivial_projection34 sigma.toRingEquiv i hi
    refine ⟨k, hk, ?_⟩
    have hmap := hcoefficientMap sigma.toRingEquiv i j
    rw [hsigma] at hmap
    rw [hmap]
    exact (map_ne_zero sigma).2 hij
  have hinteriorLeft : ∀ i j k,
      i ≠ i₀ → j ≠ j₀ → k ≠ i₀ → a i j ≠ 0 →
        ∃ ell, ell ≠ j₀ ∧ a k ell ≠ 0 := by
    intro i j k hi hj hk hij
    obtain ⟨sigma, hsigma⟩ :=
      exists_prime_cyclic_irreducible_algEquiv base.q_prime
        pti.complement_cyclic i hi k hk
    let ell := IrreducibleCharacter.mapRingEquiv sigma.toRingEquiv j
    have hell : ell ≠ j₀ := by
      exact mapRingEquiv_ne_trivial_projection34 sigma.toRingEquiv j hj
    refine ⟨ell, hell, ?_⟩
    have hmap := hcoefficientMap sigma.toRingEquiv i j
    rw [hsigma] at hmap
    rw [hmap]
    exact (map_ne_zero sigma).2 hij
  have hnotColumn : ¬ ∀ i j,
      a i j = if j = j₀ then 1 else 0 := by
    intro hcolumn
    apply FTtype34_not_ortho_cycTIiso base zeta hzeta
    apply (eqProjection34_iff base
      (dadeBridgeZero34 base zeta) (etaColumn34 base j₀)).2
    intro i j
    have hbridge : characterPairing (dadeBridgeZero34 base zeta)
        (eta34 base i j) = a i j := by
      change characterPairing
          (base.targetMap (Dade dd phi))
          (base.targetMap (isoG.cyclicTIImage (i, j))) =
        characterPairing psi (isoG.cyclicTIImage (i, j))
      rw [base.targetMap_pairing]
    rw [hbridge, characterPairing_etaColumn34]
    exact hcolumn i j
  have hsupportBound :
      (Finset.univ.filter
        (fun ij : IrreducibleCharacter W₁ ℂ ×
            IrreducibleCharacter W₂ ℂ ↦ a ij.1 ij.2 ≠ 0)).card ≤
        Fintype.card (IrreducibleCharacter W₁ ℂ) + 1 := by
    rw [hcard₁]
    simpa [CyclicTIIsometryData.cyclicTINC,
      CyclicTIIsometryData.cyclicTICoefficientSupport, a] using hNCle
  have hcardI : 3 ≤ Fintype.card (IrreducibleCharacter W₁ ℂ) := by
    rw [hcard₁]
    exact base.primeDade.prDade_cycTI.two_lt_card_left
  have hcardJ : 3 ≤ Fintype.card (IrreducibleCharacter W₂ ℂ) := by
    rw [hcard₂]
    exact base.primeDade.prDade_cycTI.two_lt_card_right
  have hrow := rectangle_zeroRow_of_support_projection34
    a i₀ j₀ hcardI hcardJ h₀₀ hrectangle hleftOrbit hrightOrbit
      hinteriorRight hinteriorLeft hsupportBound hnotColumn
  apply (eqProjection34_iff base
    (dadeBridgeZero34 base zeta) (etaZeroRow34 base)).2
  intro i j
  have hbridge : characterPairing (dadeBridgeZero34 base zeta)
      (eta34 base i j) = a i j := by
    change characterPairing
        (base.targetMap (Dade dd phi))
        (base.targetMap (isoG.cyclicTIImage (i, j))) =
      characterPairing psi (isoG.cyclicTIImage (i, j))
    rw [base.targetMap_pairing]
  rw [hbridge, characterPairing_etaZeroRow34]
  exact hrow i j


end FTType34StructureInternal

end

end Submission.OddOrder.PF
