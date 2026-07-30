import Submission.OddOrder.PF.Section01.TwistedCharacterPairing
import Submission.OddOrder.PF.Section01.QuotientInduction
import Submission.OddOrder.PF.Section02.DadeBasicProperties
import Submission.OddOrder.PF.Section02.DadeCoverTI
import Submission.OddOrder.PF.Section02.DadeSupportPartition

/-!
# Peterfalvi 2.6(a) and 2.7: Dade reciprocity and isometry
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

universe u v

/-- Peterfalvi 2.7, in the coefficient-star pairing convention of the
source development. -/
theorem general_Dade_reciprocity
    {Γ : Type u} [Group Γ] [Fintype Γ]
    {k : Type v} [Field k] [CharZero k] [StarRing k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    (alpha : ClassFunction L k) (phi : ClassFunction G k)
    (psi : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A})
    (hpsi : ∀ {a : Γ} (ha : a ∈ A),
      psi ⟨a, ddA.1.1 ha⟩ =
        (Nat.card (DadeSignalizer ddA a) : k)⁻¹ *
          ∑ x : DadeSignalizer ddA a,
            phi ⟨(x : Γ) * a,
              G.mul_mem (Dade_signalizer_sub ddA a x.property)
                (ddA.2.1 (ddA.1.1 ha))⟩) :
    starCharacterPairing (Dade ddA alpha) phi =
      starCharacterPairing alpha psi := by
  let fG : Γ → k := fun x ↦
    if hx : x ∈ G then
      Dade ddA alpha ⟨x, hx⟩ * star (phi ⟨x, hx⟩)
    else 0
  let fL : Γ → k := fun x ↦
    if hx : x ∈ L then alpha ⟨x, hx⟩ * star (psi ⟨x, hx⟩)
    else 0

  have hpairG :
      starCharacterPairing (Dade ddA alpha) phi =
        (Nat.card G : k)⁻¹ * ∑ᶠ x ∈ Dade_support ddA, fG x := by
    rw [starCharacterPairing_eq_sum_of_mem_supportedOn
      (Dade_cfunS ddA alpha)]
    congr 1
    let e : {x : G // (x : Γ) ∈ Dade_support ddA} ≃ Dade_support ddA :=
      { toFun := fun x ↦ ⟨x, x.property⟩
        invFun := fun x ↦
          ⟨⟨x, Dade_support_sub ddA x.property⟩, x.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    calc
      _ = ∑ x : {x : G // (x : Γ) ∈ Dade_support ddA},
          Dade ddA alpha x * star (phi x) := by
        apply Finset.sum_subtype
        intro x
        simp
      _ = ∑ x : Dade_support ddA, fG x := by
        apply Fintype.sum_equiv e
        intro x
        simp [e, fG]
      _ = ∑ᶠ x : Dade_support ddA, fG x :=
        (finsum_eq_sum_of_fintype _).symm
      _ = ∑ᶠ x ∈ Dade_support ddA, fG x :=
        finsum_set_coe_eq_finsum_mem (f := fG) (Dade_support ddA)

  have hpairL :
      starCharacterPairing alpha psi =
        (Nat.card L : k)⁻¹ * ∑ᶠ x ∈ A, fL x := by
    rw [starCharacterPairing_eq_sum_of_mem_supportedOn halpha]
    congr 1
    let e : {x : L // (x : Γ) ∈ A} ≃ A :=
      { toFun := fun x ↦ ⟨x, x.property⟩
        invFun := fun x ↦ ⟨⟨x, ddA.1.1 x.property⟩, x.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    calc
      _ = ∑ x : {x : L // (x : Γ) ∈ A},
          alpha x * star (psi x) := by
        apply Finset.sum_subtype
        intro x
        simp
      _ = ∑ x : A, fL x := by
        apply Fintype.sum_equiv e
        intro x
        simp [e, fL]
      _ = ∑ᶠ x : A, fL x := (finsum_eq_sum_of_fintype _).symm
      _ = ∑ᶠ x ∈ A, fL x :=
        finsum_set_coe_eq_finsum_mem (f := fL) A

  rw [hpairG, hpairL]

  have hsumG :
      (∑ᶠ x ∈ Dade_support ddA, fG x) =
        ∑ B : Dade_supportBlocks ddA, ∑ᶠ x ∈ (B : Set Γ), fG x := by
    calc
      _ = ∑ᶠ B ∈ Dade_supportBlocks ddA,
          ∑ᶠ x ∈ B, fG x :=
        (Dade_supportBlocks_partition ddA).finsum_mem
          (Set.toFinite _) (fun B _ ↦ Set.toFinite B) fG
      _ = ∑ᶠ B : Dade_supportBlocks ddA,
          ∑ᶠ x ∈ (B : Set Γ), fG x := by
        exact (finsum_set_coe_eq_finsum_mem
          (f := fun B : Set Γ ↦ ∑ᶠ x ∈ B, fG x)
          (Dade_supportBlocks ddA)).symm
      _ = ∑ B : Dade_supportBlocks ddA,
          ∑ᶠ x ∈ (B : Set Γ), fG x := by
        rw [finsum_eq_sum_of_fintype]

  have hsumL :
      (∑ᶠ x ∈ A, fL x) =
        ∑ B : conjugacyClassBlocks L A, ∑ᶠ x ∈ (B : Set Γ), fL x := by
    calc
      _ = ∑ᶠ B ∈ conjugacyClassBlocks L A,
          ∑ᶠ x ∈ B, fL x :=
        (conjugacyClassBlocks_partition L A ddA.1.2).finsum_mem
          (Set.toFinite _) (fun B _ ↦ Set.toFinite B) fL
      _ = ∑ᶠ B : conjugacyClassBlocks L A,
          ∑ᶠ x ∈ (B : Set Γ), fL x := by
        exact (finsum_set_coe_eq_finsum_mem
          (f := fun B : Set Γ ↦ ∑ᶠ x ∈ B, fL x)
          (conjugacyClassBlocks L A)).symm
      _ = ∑ B : conjugacyClassBlocks L A,
          ∑ᶠ x ∈ (B : Set Γ), fL x := by
        rw [finsum_eq_sum_of_fintype]

  rw [hsumG, hsumL, Finset.mul_sum, Finset.mul_sum]
  have hblocks (a : Γ) (ha : a ∈ A) :
      (Nat.card G : k)⁻¹ *
          ∑ᶠ x ∈ Dade_support1 ddA a, fG x =
        (Nat.card L : k)⁻¹ *
          ∑ᶠ x ∈ conjugacyClassWithin L a, fL x := by
    let qG : Γ → k := fun x ↦
      if hx : x ∈ G then star (phi ⟨x, hx⟩) else 0
    have hfactorG :
        (∑ᶠ x ∈ Dade_support1 ddA a, fG x) =
          alpha ⟨a, ddA.1.1 ha⟩ *
            ∑ᶠ x ∈ Dade_support1 ddA a, qG x := by
      calc
        _ = ∑ᶠ x ∈ Dade_support1 ddA a,
            alpha ⟨a, ddA.1.1 ha⟩ * qG x := by
          apply finsum_mem_congr rfl
          intro x hx
          have hxG : x ∈ G := Dade_support_sub ddA ⟨a, ha, hx⟩
          simp only [fG, qG, dif_pos hxG]
          rw [DadeE ddA alpha ha ⟨x, hxG⟩ hx]
        _ = alpha ⟨a, ddA.1.1 ha⟩ *
            ∑ᶠ x ∈ Dade_support1 ddA a, qG x := by
          exact (mul_finsum_mem' qG _ (Set.toFinite _)).symm

    have hcoverSum :
        (∑ᶠ x ∈ Dade_support1 ddA a, qG x) =
          (centralizerWithin G (Subgroup.zpowers a)).relIndex G •
            ∑ x : DadeSignalizer ddA a,
              star (phi ⟨(x : Γ) * a,
                G.mul_mem (Dade_signalizer_sub ddA a x.property)
                  (ddA.2.1 (ddA.1.1 ha))⟩) := by
      let conjugationAction := subgroupConjugationActionOnAmbient G
      letI : SMul G Γ := conjugationAction.toSMul
      letI : MulAction G Γ := conjugationAction.toMulAction
      letI : MulAction G (Set Γ) := Set.mulActionSet
      let S : Set Γ :=
        (DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ)
      let C := centralizerWithin G (Subgroup.zpowers a)
      have hcover := normalizedTI_classSupport_partition
        (Dade_cover_TI ddA ha)
      change IsSetPartition (MulAction.orbit G S)
          (Dade_support1 ddA a) ∧
        (MulAction.orbit G S).ncard = C.relIndex G at hcover

      have hblock (B : Set Γ) (hB : B ∈ MulAction.orbit G S) :
          (∑ᶠ x ∈ B, qG x) = ∑ᶠ x ∈ S, qG x := by
        rcases hB with ⟨g, rfl⟩
        let e : S ≃ (g • S : Set Γ) := by
          change S ≃ (MulAction.toPerm g) '' S
          exact Equiv.Set.image (MulAction.toPerm g) S
            (MulAction.toPerm g).injective
        calc
          _ = ∑ᶠ x : (g • S : Set Γ), qG x :=
            (finsum_set_coe_eq_finsum_mem (f := qG) (g • S)).symm
          _ = ∑ x : (g • S : Set Γ), qG x := by
            rw [finsum_eq_sum_of_fintype]
          _ = ∑ x : S, qG x := by
            symm
            apply Fintype.sum_equiv e
            intro x
            have hxG : (x : Γ) ∈ G := by
              rcases Set.mem_mul.mp x.property with ⟨h, hh, y, hy, hxy⟩
              rw [Set.mem_singleton_iff] at hy
              subst y
              rw [← hxy]
              exact G.mul_mem (Dade_signalizer_sub ddA a hh)
                (ddA.2.1 (ddA.1.1 ha))
            have hexG : ((e x : (g • S : Set Γ)) : Γ) ∈ G := by
              rw [show ((e x : (g • S : Set Γ)) : Γ) =
                  g • (x : Γ) by rfl]
              change (g : Γ) * (x : Γ) * (g : Γ)⁻¹ ∈ G
              exact G.mul_mem (G.mul_mem g.property hxG)
                (G.inv_mem g.property)
            simp only [qG, dif_pos hxG, dif_pos hexG]
            have heG :
                (⟨((e x : (g • S : Set Γ)) : Γ), hexG⟩ : G) =
                  g * ⟨(x : Γ), hxG⟩ * g⁻¹ := by
              apply Subtype.ext
              rfl
            rw [heG]
            have hconj := ClassFunction.conj_apply phi g ⟨x, hxG⟩
            exact (congrArg star hconj).symm
          _ = ∑ᶠ x : S, qG x := (finsum_eq_sum_of_fintype _).symm
          _ = ∑ᶠ x ∈ S, qG x :=
            finsum_set_coe_eq_finsum_mem (f := qG) S

      have hsplit :
          (∑ᶠ x ∈ Dade_support1 ddA a, qG x) =
            ∑ᶠ B ∈ MulAction.orbit G S, ∑ᶠ x ∈ B, qG x :=
        hcover.1.finsum_mem (Set.toFinite _)
          (fun B _ ↦ Set.toFinite B) qG
      rw [hsplit]
      have hconst :
          (∑ᶠ B ∈ MulAction.orbit G S, ∑ᶠ x ∈ B, qG x) =
            (MulAction.orbit G S).ncard • ∑ᶠ x ∈ S, qG x := by
        let c := ∑ᶠ x ∈ S, qG x
        calc
          _ = ∑ᶠ _B ∈ MulAction.orbit G S, c := by
            apply finsum_mem_congr rfl
            intro B hB
            exact hblock B hB
          _ = (MulAction.orbit G S).ncard • c := by
            rw [finsum_mem_eq_finite_toFinset_sum _
              (Set.toFinite (MulAction.orbit G S))]
            simp only [Finset.sum_const]
            rw [Set.ncard_eq_toFinset_card
              (MulAction.orbit G S) (Set.toFinite _)]
      rw [hconst, hcover.2]
      congr 1
      let eH : DadeSignalizer ddA a ≃ S :=
        { toFun := fun x ↦ ⟨(x : Γ) * a, by
            apply Set.mem_mul.mpr
            exact ⟨x, x.property, a, Set.mem_singleton a, rfl⟩⟩
          invFun := fun y ↦ ⟨(y : Γ) * a⁻¹, by
            rcases Set.mem_mul.mp y.property with ⟨h, hh, z, hz, hzy⟩
            rw [Set.mem_singleton_iff] at hz
            subst z
            rw [← hzy]
            simpa [mul_assoc] using hh⟩
          left_inv := fun x ↦ by
            apply Subtype.ext
            simp
          right_inv := fun y ↦ by
            apply Subtype.ext
            simp }
      calc
        _ = ∑ᶠ x : S, qG x :=
          (finsum_set_coe_eq_finsum_mem (f := qG) S).symm
        _ = ∑ x : S, qG x := by rw [finsum_eq_sum_of_fintype]
        _ = ∑ x : DadeSignalizer ddA a,
            star (phi ⟨(x : Γ) * a,
              G.mul_mem (Dade_signalizer_sub ddA a x.property)
                (ddA.2.1 (ddA.1.1 ha))⟩) := by
          symm
          apply Fintype.sum_equiv eH
          intro x
          have hxaG : (x : Γ) * a ∈ G :=
            G.mul_mem (Dade_signalizer_sub ddA a x.property)
              (ddA.2.1 (ddA.1.1 ha))
          have heH : ((eH x : S) : Γ) = (x : Γ) * a := by
            rfl
          have heHG : ((eH x : S) : Γ) ∈ G := heH ▸ hxaG
          simp only [qG, dif_pos heHG]
          have hsub :
              (⟨(x : Γ) * a, hxaG⟩ : G) =
                ⟨((eH x : S) : Γ), heHG⟩ := by
            apply Subtype.ext
            exact heH.symm
          rw [hsub]

    have hclassL :
        (∑ᶠ x ∈ conjugacyClassWithin L a, fL x) =
          (conjugacyClassWithin L a).ncard •
            (alpha ⟨a, ddA.1.1 ha⟩ *
              star (psi ⟨a, ddA.1.1 ha⟩)) := by
      let c := alpha ⟨a, ddA.1.1 ha⟩ *
        star (psi ⟨a, ddA.1.1 ha⟩)
      have hconst :
          (∑ᶠ x ∈ conjugacyClassWithin L a, fL x) =
            ∑ᶠ _x ∈ conjugacyClassWithin L a, c := by
        apply finsum_mem_congr rfl
        intro x hx
        rcases hx with ⟨l, hl, rfl⟩
        have hxaL : l⁻¹ * a * l ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem hl) (ddA.1.1 ha)) hl
        have hconjEq :
            (⟨l⁻¹ * a * l, hxaL⟩ : L) =
              ⟨l⁻¹, L.inv_mem hl⟩ * ⟨a, ddA.1.1 ha⟩ *
                (⟨l⁻¹, L.inv_mem hl⟩ : L)⁻¹ := by
          apply Subtype.ext
          simp [mul_assoc]
        simp only [fL, dif_pos hxaL, c]
        rw [hconjEq, ClassFunction.conj_apply alpha,
          ClassFunction.conj_apply psi]
      rw [hconst]
      calc
        (∑ᶠ _x ∈ conjugacyClassWithin L a, c) =
            (∑ᶠ _x ∈ conjugacyClassWithin L a, (1 : k)) * c := by
          symm
          simpa using finsum_mem_mul' (fun _ : Γ ↦ (1 : k)) c
            (Set.toFinite (conjugacyClassWithin L a))
        _ = ((conjugacyClassWithin L a).ncard : k) * c := by
          congr 1
          rw [finsum_mem_eq_finite_toFinset_sum _
            (Set.toFinite (conjugacyClassWithin L a))]
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast (Set.ncard_eq_toFinset_card
            (conjugacyClassWithin L a)
            (Set.toFinite (conjugacyClassWithin L a))).symm
        _ = (conjugacyClassWithin L a).ncard • c := by
          rw [nsmul_eq_mul]
    rw [hfactorG, hcoverSum, hclassL]
    let H := DadeSignalizer ddA a
    let CG := centralizerWithin G (Subgroup.zpowers a)
    let CL := centralizerWithin L (Subgroup.zpowers a)
    have hsd : IsInternalSemidirectProductIn H CL CG := by
      simpa [H, CG, CL] using Dade_sdprod ddA ha
    have hHcard : Nat.card (H.subgroupOf CG) = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsd.1).toEquiv
    have hCLcard : Nat.card (CL.subgroupOf CG) = Nat.card CL :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsd.2.1).toEquiv
    have hCGcard : Nat.card H * Nat.card CL = Nat.card CG := by
      rw [← hHcard, ← hCLcard]
      exact hsd.2.2.2.card_mul
    have hCGsubcard : Nat.card (CG.subgroupOf G) = Nat.card CG :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (centralizerWithin_le_left G (Subgroup.zpowers a))).toEquiv
    have hCLsubcard : Nat.card (CL.subgroupOf L) = Nat.card CL :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (centralizerWithin_le_left L (Subgroup.zpowers a))).toEquiv
    have hCGindex : CG.relIndex G * Nat.card CG = Nat.card G := by
      change (CG.subgroupOf G).index * Nat.card CG = Nat.card G
      rw [← hCGsubcard]
      exact (CG.subgroupOf G).index_mul_card
    have hCLindex : CL.relIndex L * Nat.card CL = Nat.card L := by
      change (CL.subgroupOf L).index * Nat.card CL = Nat.card L
      rw [← hCLsubcard]
      exact (CL.subgroupOf L).index_mul_card
    have hCGcardK :
        (Nat.card H : k) * (Nat.card CL : k) = (Nat.card CG : k) := by
      exact_mod_cast hCGcard
    have hCGindexK :
        (CG.relIndex G : k) * (Nat.card CG : k) =
          (Nat.card G : k) := by
      exact_mod_cast hCGindex
    have hCLindexK :
        (CL.relIndex L : k) * (Nat.card CL : k) =
          (Nat.card L : k) := by
      exact_mod_cast hCLindex
    have hpsiStar := congrArg star (hpsi ha)
    simp only [star_mul, star_inv₀, star_natCast, star_sum] at hpsiStar
    rw [ncard_conjugacyClassWithin_eq_relIndex L a]
    change (Nat.card G : k)⁻¹ *
          (alpha ⟨a, ddA.1.1 ha⟩ *
            CG.relIndex G •
              ∑ x : H, star (phi ⟨(x : Γ) * a, _⟩)) =
      (Nat.card L : k)⁻¹ * CL.relIndex L •
        (alpha ⟨a, ddA.1.1 ha⟩ *
          star (psi ⟨a, ddA.1.1 ha⟩))
    rw [hpsiStar]
    simp only [nsmul_eq_mul]
    have hG0 : (Nat.card G : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hL0 : (Nat.card L : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hH0 : (Nat.card H : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    field_simp [hG0, hL0, hH0]
    rw [← hCLindexK, ← hCGindexK, ← hCGcardK]
    ring
  apply Fintype.sum_equiv (Dade_supportBlocksEquiv ddA)
  rintro ⟨B, a, ha, rfl⟩
  rw [Dade_supportBlocksEquiv_mk ddA ha]
  exact hblocks a ha

/-- Peterfalvi 2.7: reciprocity against functions constant on each Dade
signalizer coset. -/
theorem Dade_reciprocity
    {Γ : Type u} [Group Γ] [Fintype Γ]
    {k : Type v} [Field k] [CharZero k] [StarRing k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    (alpha : ClassFunction L k) (phi : ClassFunction G k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A})
    (hphi : ∀ {a : Γ} (ha : a ∈ A)
      (x : DadeSignalizer ddA a),
      phi ⟨(x : Γ) * a,
          G.mul_mem (Dade_signalizer_sub ddA a x.property)
            (ddA.2.1 (ddA.1.1 ha))⟩ =
        phi ⟨a, ddA.2.1 (ddA.1.1 ha)⟩) :
    starCharacterPairing (Dade ddA alpha) phi =
      starCharacterPairing alpha
        (ClassFunction.comap (Subgroup.inclusion ddA.2.1) phi) := by
  apply general_Dade_reciprocity ddA alpha phi
    (ClassFunction.comap (Subgroup.inclusion ddA.2.1) phi) halpha
  intro a ha
  change phi ⟨a, ddA.2.1 (ddA.1.1 ha)⟩ =
    (Nat.card (DadeSignalizer ddA a) : k)⁻¹ *
      ∑ x : DadeSignalizer ddA a,
        phi ⟨(x : Γ) * a,
          G.mul_mem (Dade_signalizer_sub ddA a x.property)
            (ddA.2.1 (ddA.1.1 ha))⟩
  have hsum :
      (∑ x : DadeSignalizer ddA a,
        phi ⟨(x : Γ) * a,
          G.mul_mem (Dade_signalizer_sub ddA a x.property)
            (ddA.2.1 (ddA.1.1 ha))⟩) =
        Nat.card (DadeSignalizer ddA a) •
          phi ⟨a, ddA.2.1 (ddA.1.1 ha)⟩ := by
    calc
      _ = ∑ _x : DadeSignalizer ddA a,
          phi ⟨a, ddA.2.1 (ddA.1.1 ha)⟩ := by
        apply Fintype.sum_congr
        intro x
        exact hphi ha x
      _ = _ := by
        simp [Nat.card_eq_fintype_card]
  rw [hsum, nsmul_eq_mul]
  have hcard : (Nat.card (DadeSignalizer ddA a) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp [hcard]

/-- Peterfalvi 2.6(a): the Dade map is an isometry on class functions
supported on `A`. -/
theorem Dade_isometry
    {Γ : Type u} [Group Γ] [Fintype Γ]
    {k : Type v} [Field k] [CharZero k] [StarRing k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    (alpha beta : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A})
    (hbeta : beta ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A}) :
    starCharacterPairing (Dade ddA alpha) (Dade ddA beta) =
      starCharacterPairing alpha beta := by
  have _hbeta := hbeta
  apply general_Dade_reciprocity ddA alpha (Dade ddA beta) beta halpha
  intro a ha
  have hsum :
      (∑ x : DadeSignalizer ddA a,
        Dade ddA beta ⟨(x : Γ) * a,
          G.mul_mem (Dade_signalizer_sub ddA a x.property)
            (ddA.2.1 (ddA.1.1 ha))⟩) =
        Nat.card (DadeSignalizer ddA a) •
          beta ⟨a, ddA.1.1 ha⟩ := by
    calc
      _ = ∑ _x : DadeSignalizer ddA a,
          beta ⟨a, ddA.1.1 ha⟩ := by
        apply Fintype.sum_congr
        intro x
        exact DadeE ddA beta ha
          ⟨(x : Γ) * a,
            G.mul_mem (Dade_signalizer_sub ddA a x.property)
              (ddA.2.1 (ddA.1.1 ha))⟩
          (mem_Dade_support1 ddA ha x.property)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  rw [hsum, nsmul_eq_mul]
  have hcard : (Nat.card (DadeSignalizer ddA a) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp [hcard]

end

end Submission.OddOrder.PF
