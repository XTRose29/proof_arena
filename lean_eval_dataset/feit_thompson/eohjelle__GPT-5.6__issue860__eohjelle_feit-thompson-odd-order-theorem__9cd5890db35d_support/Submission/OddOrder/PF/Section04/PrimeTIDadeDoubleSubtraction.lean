import Submission.OddOrder.PF.Section04.PrimeTIDadeCoherence
import Submission.OddOrder.PF.Section02.DadeInduction
import Submission.OddOrder.PF.Section02.DadeRestriction

/-!
# The four-term prime-TI subtraction formula

This file ports the final lemma in Peterfalvi's Section 4.10.  The main
argument enlarges the cyclic-TI set by all of its `L`-conjugates, applies
Dade induction on that enlarged normalized-TI set, and then uses transitivity
of ordinary class-function induction.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical
open Submission.OddOrder.MathlibSupport

universe v

variable {Gamma : Type} [Group Gamma]

/-- Saturating a normalized-TI set under an intermediate subgroup replaces
its relative normalizer by that intermediate subgroup. -/
private theorem isNormalizedTI_classSupportWithin
    {S : Set Gamma} {D N M : Subgroup Gamma}
    (hTI : IsNormalizedTI S D N) (hNM : N ≤ M) (hMD : M ≤ D) :
    IsNormalizedTI (classSupportWithin M S) D M := by
  rw [isNormalizedTI_iff_mem_conj]
  refine ⟨?_, hMD, ?_⟩
  · rcases hTI.1 with ⟨a, ha⟩
    exact ⟨a, a, ha, 1, M.one_mem, by simp⟩
  · intro a ha g hgD
    constructor
    · intro hga
      rcases ha with ⟨s, hs, y, hyM, hya⟩
      rcases hga with ⟨t, ht, z, hzM, hzg⟩
      let q : Gamma := y * g * z⁻¹
      have hqD : q ∈ D :=
        D.mul_mem (D.mul_mem (hMD hyM) hgD) (D.inv_mem (hMD hzM))
      have hqConj : q⁻¹ * s * q = t := by
        change y⁻¹ * s * y = a at hya
        change z⁻¹ * t * z = g⁻¹ * a * g at hzg
        dsimp only [q]
        rw [show (y * g * z⁻¹)⁻¹ * s * (y * g * z⁻¹) =
            z * (g⁻¹ * (y⁻¹ * s * y) * g) * z⁻¹ by group,
          hya, ← hzg]
        group
      have hqN : q ∈ N :=
        ((isNormalizedTI_iff_mem_conj.mp hTI).2.2 hs hqD).mp (by
          rw [hqConj]
          exact ht)
      have hqM : q ∈ M := hNM hqN
      have hgEq : g = y⁻¹ * q * z := by
        dsimp only [q]
        group
      rw [hgEq]
      exact M.mul_mem (M.mul_mem (M.inv_mem hyM) hqM) hzM
    · intro hgM
      exact (classSupportWithin_rightConj_iff
        (G := M) (S := S) (g := g) hgM).2 ha

/-- Induction of a function supported on `S` is supported on the union of
the conjugacy classes meeting `S`.  This is the class-function form of
MathComp's `cfInd_on`. -/
private theorem induce_mem_supportedOn_classSupportWithin
    [Fintype Gamma] {k : Type v} [Field k]
    {W L : Subgroup Gamma} {S : Set Gamma}
    (hWL : W ≤ L) (alpha : ClassFunction W k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : W | (x : Gamma) ∈ S}) :
    ClassFunction.induce (W.subgroupOf L)
        (ClassFunction.toSubgroupOf W L hWL alpha) ∈
      ClassFunction.supportedOn
        {x : L | (x : Gamma) ∈ classSupportWithin L S} := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  rw [ClassFunction.induce_apply_formula]
  suffices hsum :
      (∑ y : L, if hy : y⁻¹ * x * y ∈ W.subgroupOf L then
          ClassFunction.toSubgroupOf W L hWL alpha
            ⟨y⁻¹ * x * y, hy⟩ else 0) = 0 by
    rw [hsum, mul_zero]
  apply Finset.sum_eq_zero
  intro y _hyUniv
  by_cases hy : y⁻¹ * x * y ∈ W.subgroupOf L
  · rw [dif_pos hy, ClassFunction.toSubgroupOf_apply]
    apply ClassFunction.eq_zero_of_mem_supportedOn halpha
    intro hs
    apply hx
    refine ⟨
      ((Subgroup.subgroupOfEquivOfLe hWL
        ⟨y⁻¹ * x * y, hy⟩ : W) : Gamma), hs,
      (y : Gamma)⁻¹, L.inv_mem y.property, ?_⟩
    simp only [inv_inv]
    change (y : Gamma) * ((y : Gamma)⁻¹ * (x : Gamma) * (y : Gamma)) *
        (y : Gamma)⁻¹ = (x : Gamma)
    group
  · rw [dif_neg hy]

/-- Transporting an induction from `W ≤ L` to the copy of `L` in `G`
agrees with inducing inside that copy from the copy of `W`. -/
private theorem toSubgroupOf_induce_eq
    [Fintype Gamma] {k : Type v} [Field k]
    {W L G : Subgroup Gamma}
    (hWL : W ≤ L) (hLG : L ≤ G) (alpha : ClassFunction W k) :
    let WG := W.subgroupOf G
    let LG := L.subgroupOf G
    let hWGLG : WG ≤ LG := by
      intro x hx
      change ((x : G) : Gamma) ∈ W at hx
      change ((x : G) : Gamma) ∈ L
      exact hWL hx
    ClassFunction.toSubgroupOf L G hLG
        (ClassFunction.induce (W.subgroupOf L)
          (ClassFunction.toSubgroupOf W L hWL alpha)) =
      ClassFunction.induce (WG.subgroupOf LG)
        (ClassFunction.toSubgroupOf WG LG hWGLG
          (ClassFunction.toSubgroupOf W G (hWL.trans hLG) alpha)) := by
  dsimp only
  let WG := W.subgroupOf G
  let LG := L.subgroupOf G
  have hWGLG : WG ≤ LG := by
    intro x hx
    change ((x : G) : Gamma) ∈ W at hx
    change ((x : G) : Gamma) ∈ L
    exact hWL hx
  apply ClassFunction.ext
  intro x
  rw [ClassFunction.toSubgroupOf_apply,
    ClassFunction.induce_apply_formula,
    ClassFunction.induce_apply_formula]
  have hcardWL : Nat.card (W.subgroupOf L) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv
  have hcardWG : Nat.card WG = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hWL.trans hLG)).toEquiv
  have hcardNested : Nat.card (WG.subgroupOf LG) = Nat.card WG :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWGLG).toEquiv
  rw [hcardWL, hcardNested, hcardWG]
  apply congrArg ((Nat.card W : k)⁻¹ * ·)
  let e : LG ≃* L := Subgroup.subgroupOfEquivOfLe hLG
  symm
  refine Fintype.sum_equiv e.toEquiv
    (fun y : LG ↦
      if hy : y⁻¹ * x * y ∈ WG.subgroupOf LG then
        ClassFunction.toSubgroupOf WG LG hWGLG
          (ClassFunction.toSubgroupOf W G (hWL.trans hLG) alpha)
          ⟨y⁻¹ * x * y, hy⟩ else 0)
    (fun y : L ↦
      if hy : y⁻¹ *
          Subgroup.subgroupOfEquivOfLe hLG x * y ∈ W.subgroupOf L then
        ClassFunction.toSubgroupOf W L hWL alpha
          ⟨y⁻¹ * Subgroup.subgroupOfEquivOfLe hLG x * y, hy⟩ else 0)
    ?_
  intro y
  have hmem :
      y⁻¹ * x * y ∈ WG.subgroupOf LG ↔
        (e.toEquiv y)⁻¹ * Subgroup.subgroupOfEquivOfLe hLG x *
            e.toEquiv y ∈
          W.subgroupOf L := by
    rfl
  by_cases hy : y⁻¹ * x * y ∈ WG.subgroupOf LG
  · have hy' := hmem.mp hy
    rw [dif_pos hy, dif_pos hy', ClassFunction.toSubgroupOf_apply,
      ClassFunction.toSubgroupOf_apply, ClassFunction.toSubgroupOf_apply]
    apply congrArg alpha
    apply Subtype.ext
    rfl
  · have hy' :
        (e.toEquiv y)⁻¹ * Subgroup.subgroupOfEquivOfLe hLG x *
            e.toEquiv y ∉
          W.subgroupOf L := hmem.not.mp hy
    rw [dif_neg hy, dif_neg hy']

/-- Canonical induction through `L` is transitive even though Lean represents
the three subgroup copies by nested subtype groups. -/
private theorem induceClassFunction_trans
    [Fintype Gamma] {k : Type v} [Field k] [CharZero k]
    {W L G : Subgroup Gamma}
    (hWL : W ≤ L) (hLG : L ≤ G) (alpha : ClassFunction W k) :
    ClassFunction.induce (L.subgroupOf G)
        (ClassFunction.toSubgroupOf L G hLG
          (ClassFunction.induce (W.subgroupOf L)
            (ClassFunction.toSubgroupOf W L hWL alpha))) =
      ClassFunction.induce (W.subgroupOf G)
        (ClassFunction.toSubgroupOf W G (hWL.trans hLG) alpha) := by
  let WG := W.subgroupOf G
  let LG := L.subgroupOf G
  have hWGLG : WG ≤ LG := by
    intro x hx
    change ((x : G) : Gamma) ∈ W at hx
    change ((x : G) : Gamma) ∈ L
    exact hWL hx
  rw [toSubgroupOf_induce_eq hWL hLG alpha]
  exact ClassFunction.induce_trans WG LG hWGLG
    (ClassFunction.toSubgroupOf W G (hWL.trans hLG) alpha)

variable [Fintype Gamma] {G L K H W W₁ W₂ : Subgroup Gamma}
  {A A₀ : Set Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

namespace PrimeDadeHypothesis

variable (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)

/-- Peterfalvi 4.10, `prDade_sub2_TIirr`: the Dade image of the signed
four-term prime-TI rectangle is the corresponding four-term cyclic-TI
rectangle. -/
theorem prDade_sub2_TIirr
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    Dade pd.prDade_hyp
        ((pd.prDade_prTI.primeTISign isoL j : ℂ) •
            pd.prDade_prTI.primeTICharacter isoL i j -
          (pd.prDade_prTI.primeTISign isoL j : ℂ) •
            pd.prDade_prTI.primeTICharacter isoL
              IrreducibleCharacter.trivial j -
          pd.prDade_prTI.primeTICharacter isoL i
            IrreducibleCharacter.trivial +
          pd.prDade_prTI.primeTICharacter isoL
            IrreducibleCharacter.trivial
            IrreducibleCharacter.trivial) =
      isoG.cyclicTIImage (i, j) -
        isoG.cyclicTIImage (IrreducibleCharacter.trivial, j) -
        isoG.cyclicTIImage (i, IrreducibleCharacter.trivial) +
        isoG.cyclicTIImage
          (IrreducibleCharacter.trivial,
            IrreducibleCharacter.trivial) := by
  let pti := pd.prDade_prTI
  let V : Set Gamma := cyclicTISet W W₁ W₂
  let V₀ : Set Gamma := classSupportWithin L V
  let alpha : ClassFunction W ℂ :=
    VirtualCharacter.realize (cyclicTIVirtualCharacter defW i j)
  let beta : ClassFunction L ℂ :=
    (pti.primeTISign isoL j : ℂ) • pti.primeTICharacter isoL i j -
      (pti.primeTISign isoL j : ℂ) •
        pti.primeTICharacter isoL IrreducibleCharacter.trivial j -
      pti.primeTICharacter isoL i IrreducibleCharacter.trivial +
      pti.primeTICharacter isoL IrreducibleCharacter.trivial
        IrreducibleCharacter.trivial
  have hWL : W ≤ L := pti.directProduct_le_group
  have hLG : L ≤ G := pd.prDade_hyp.2.1
  have hV₀A₀ : V₀ ⊆ A₀ := by
    intro x hx
    rw [pd.prDade_def.dadeSet_eq]
    exact Or.inr hx
  have hV₀norm : L ≤ Subgroup.normalizer V₀ :=
    le_normalizer_classSupportWithin L V
  have hV₀TI : IsNormalizedTI V₀ G L := by
    exact isNormalizedTI_classSupportWithin pd.prDade_cycTI.normedTI
      hWL hLG
  have halpha : alpha ∈
      ClassFunction.supportedOn (cyclicTISetInW W W₁ W₂) := by
    exact pd.prDade_cycTI.cyclicTIVirtualCharacter_mem_supportedOn i j
  have halphaEq : alpha =
      VirtualCharacter.realize (primeTIDifference defW i j) -
        VirtualCharacter.realize
          (primeTIDifference defW i
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) := by
    dsimp only [alpha]
    rw [realize_cyclicTIVirtualCharacter,
      realize_primeTIDifference, realize_primeTIDifference]
    simp only [IrreducibleCharacter.cyclicTICharacter_trivial]
    abel
  have hbetaInd : beta =
      pti.prime_cycTIhyp.induceClassFunction alpha := by
    have hj := (pti.primeTIirr_spec isoL).2.1 i j
    have h₀ := (pti.primeTIirr_spec isoL).2.1 i
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
    rw [halphaEq, map_sub, hj, h₀, pti.prTIsign0 isoL]
    dsimp only [beta]
    simp only [Int.cast_one, one_smul, smul_sub]
    abel
  have hbetaSupport : beta ∈
      ClassFunction.supportedOn {x : L | (x : Gamma) ∈ V₀} := by
    rw [hbetaInd]
    exact induce_mem_supportedOn_classSupportWithin hWL alpha halpha
  have hDadeInd : Dade pd.prDade_hyp beta =
      ClassFunction.induce (L.subgroupOf G)
        (ClassFunction.toSubgroupOf L G hLG beta) := by
    let ddV₀ := restr_Dade_hyp pd.prDade_hyp hV₀A₀ hV₀norm
    calc
      Dade pd.prDade_hyp beta =
          restr_Dade pd.prDade_hyp hV₀A₀ hV₀norm beta :=
        (restr_DadeE pd.prDade_hyp hV₀A₀ hV₀norm beta
          hbetaSupport).symm
      _ = ClassFunction.induce (L.subgroupOf G)
          (ClassFunction.toSubgroupOf L G ddV₀.2.1 beta) :=
        Dade_Ind ddV₀ hV₀TI beta hbetaSupport
      _ = ClassFunction.induce (L.subgroupOf G)
          (ClassFunction.toSubgroupOf L G hLG beta) := by
        rfl
  have htrans :
      ClassFunction.induce (L.subgroupOf G)
          (ClassFunction.toSubgroupOf L G hLG beta) =
        pd.prDade_cycTI.induceClassFunction alpha := by
    rw [hbetaInd]
    simpa [CyclicTIHypothesis.induceClassFunction] using
      induceClassFunction_trans hWL hLG alpha
  have hIsoG : pd.prDade_cycTI.induceClassFunction alpha =
      isoG.linearMap alpha :=
    (isoG.induce_supported alpha halpha).symm
  change Dade pd.prDade_hyp beta = _
  rw [hDadeInd, htrans, hIsoG]
  dsimp only [alpha]
  rw [realize_cyclicTIVirtualCharacter, map_add, map_sub, map_sub]
  simp only [CyclicTIIsometryData.cyclicTIImage,
    CyclicTIIsometryData.cyclicTISourceIrreducible,
    IrreducibleCharacter.cyclicTICharacter_trivial]
  abel

end PrimeDadeHypothesis

end

end Submission.OddOrder.PF
