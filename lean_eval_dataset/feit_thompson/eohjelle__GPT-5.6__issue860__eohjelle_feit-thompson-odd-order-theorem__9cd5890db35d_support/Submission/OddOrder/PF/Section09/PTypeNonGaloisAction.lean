import Submission.OddOrder.PF.Section09.PTypeFactorAction
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic

/-!
# Peterfalvi Section 9: the non-Galois factor-action alternative

This module proves Peterfalvi (9.7a) from the canonical factor-action
package.  When the action of `U` on the chief factor is reducible, a minimal
constituent and its `W₁`-translates give a direct-product decomposition.
The associated cyclic coordinate actions then embed the faithful complement
quotient into a row group of length `q - 1`.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped Pointwise

noncomputable section

universe u

namespace PTypeFactorActionData

variable {Hbar U W₁ : Type u}
variable [Group Hbar] [Finite Hbar]
variable [Group U] [Finite U]
variable [Group W₁] [Finite W₁]

/-- The cardinal formula makes the chief factor nontrivial. -/
theorem Hbar_top_ne_bot
    (D : PTypeFactorActionData Hbar U W₁) :
    (⊤ : Subgroup Hbar) ≠ ⊥ := by
  have hcard : 1 < Nat.card Hbar := by
    rw [D.card_Hbar]
    exact one_lt_pow₀ D.p_prime.one_lt D.q_prime.ne_zero
  letI : Nontrivial Hbar :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  exact top_ne_bot

/-- Failure of irreducibility produces a proper nonzero invariant subgroup. -/
theorem exists_proper_U_invariant_of_not_typeP_Galois
    (D : PTypeFactorActionData Hbar U W₁)
    (not_Galois : ¬ typeP_Galois D) :
    ∃ L : Subgroup Hbar,
      IsInvariantSubgroup D.U_action L ∧ L ≠ ⊥ ∧ L ≠ ⊤ := by
  by_contra h
  apply not_Galois
  refine ⟨D.Hbar_top_ne_bot, ?_⟩
  intro L hL
  by_cases hbot : L = ⊥
  · exact Or.inl hbot
  · right
    by_contra htop
    exact h ⟨L, hL, hbot, htop⟩

/-- Choose a minimal nonzero invariant subgroup below `L`. -/
theorem exists_minimal_U_invariant_le
    (D : PTypeFactorActionData Hbar U W₁)
    (L : Subgroup Hbar) (hL_ne : L ≠ ⊥)
    (hL : IsInvariantSubgroup D.U_action L) :
    ∃ B : Subgroup Hbar,
      B ≤ L ∧ B ≠ ⊥ ∧ IsInvariantSubgroup D.U_action B ∧
      ∀ K : Subgroup Hbar, K ≤ B → K ≠ ⊥ →
        IsInvariantSubgroup D.U_action K → K = B := by
  let P : Subgroup Hbar → Prop := fun B ↦
    B ≤ L ∧ B ≠ ⊥ ∧ IsInvariantSubgroup D.U_action B
  have hPL : P L := ⟨le_rfl, hL_ne, hL⟩
  obtain ⟨B, _hBL, hB⟩ := Finite.exists_le_minimal hPL
  refine ⟨B, hB.1.1, hB.1.2.1, hB.1.2.2, ?_⟩
  intro K hKB hK_ne hK
  have hPK : P K := ⟨hKB.trans hB.1.1, hK_ne, hK⟩
  exact le_antisymm hKB (hB.eq_of_ge hPK hKB).le

/-- In the reducible branch, choose a proper minimal constituent. -/
theorem exists_minimal_proper_U_invariant
    (D : PTypeFactorActionData Hbar U W₁)
    (not_Galois : ¬ typeP_Galois D) :
    ∃ H₁ : Subgroup Hbar,
      H₁ ≠ ⊥ ∧ H₁ ≠ ⊤ ∧
      IsInvariantSubgroup D.U_action H₁ ∧
      ∀ K : Subgroup Hbar, K ≤ H₁ → K ≠ ⊥ →
        IsInvariantSubgroup D.U_action K → K = H₁ := by
  obtain ⟨L, hL, hL_ne, hL_top⟩ :=
    D.exists_proper_U_invariant_of_not_typeP_Galois not_Galois
  obtain ⟨H₁, hH₁L, hH₁_ne, hH₁, hmin⟩ :=
    D.exists_minimal_U_invariant_le L hL_ne hL
  have hH₁_top : H₁ ≠ ⊤ := by
    intro htop
    apply hL_top
    apply top_unique
    rw [← htop]
    exact hH₁L
  exact ⟨H₁, hH₁_ne, hH₁_top, hH₁, hmin⟩

/-- Translating a minimal constituent by `W₁` preserves minimality. -/
theorem actionConjugate_minimal_U_invariant
    (D : PTypeFactorActionData Hbar U W₁)
    {L : Subgroup Hbar}
    (hL_ne : L ≠ ⊥)
    (hL : IsInvariantSubgroup D.U_action L)
    (hL_min : ∀ K : Subgroup Hbar, K ≤ L → K ≠ ⊥ →
      IsInvariantSubgroup D.U_action K → K = L)
    (w : W₁) :
    let A := actionConjugate D.W₁_action L w
    A ≠ ⊥ ∧ IsInvariantSubgroup D.U_action A ∧
      ∀ K : Subgroup Hbar, K ≤ A → K ≠ ⊥ →
        IsInvariantSubgroup D.U_action K → K = A := by
  let A := actionConjugate D.W₁_action L w
  have hA_ne : A ≠ ⊥ := by
    intro hA
    apply hL_ne
    calc
      L = actionConjugate D.W₁_action A w⁻¹ := by
        dsimp [A]
        rw [← actionConjugate_mul]
        simp
      _ = ⊥ := by
        rw [hA]
        simpa [actionConjugate] using
          Subgroup.map_bot (D.W₁_action w⁻¹).toMonoidHom
  have hA_inv : IsInvariantSubgroup D.U_action A :=
    D.actionConjugate_U_invariant hL w
  refine ⟨hA_ne, hA_inv, ?_⟩
  intro K hKA hK_ne hK
  let K' := actionConjugate D.W₁_action K w⁻¹
  have hK'L : K' ≤ L := by
    have hm := Subgroup.map_mono hKA
      (f := (D.W₁_action w⁻¹).toMonoidHom)
    change actionConjugate D.W₁_action K w⁻¹ ≤
      actionConjugate D.W₁_action A w⁻¹ at hm
    simpa [A, ← actionConjugate_mul] using hm
  have hK'_ne : K' ≠ ⊥ := by
    intro hK'
    apply hK_ne
    calc
      K = actionConjugate D.W₁_action K' w := by
        dsimp [K']
        rw [← actionConjugate_mul]
        simp
      _ = ⊥ := by
        rw [hK']
        simpa [actionConjugate] using
          Subgroup.map_bot (D.W₁_action w).toMonoidHom
  have hK'_inv : IsInvariantSubgroup D.U_action K' :=
    D.actionConjugate_U_invariant hK w⁻¹
  have hK'_eq : K' = L := hL_min K' hK'L hK'_ne hK'_inv
  calc
    K = actionConjugate D.W₁_action K' w := by
      dsimp [K']
      rw [← actionConjugate_mul]
      simp
    _ = A := by rw [hK'_eq]

/-- A minimal constituent has a full direct orbit, and cardinal arithmetic
forces its order to be `p`. -/
theorem exists_nonGalois_constituent_direct
    (D : PTypeFactorActionData Hbar U W₁)
    (hD : PTypeFactorActionHypotheses D)
    (not_Galois : ¬ typeP_Galois D) :
    ∃ H₁ : Subgroup Hbar,
      Nat.card H₁ = D.p ∧
      IsInvariantSubgroup D.U_action H₁ ∧
      IsInternalDirectProductFamily
        (fun w : W₁ ↦ actionConjugate D.W₁_action H₁ w) := by
  classical
  letI := Fintype.ofFinite W₁
  letI : IsMulCommutative Hbar := hD.elementary.commutative
  obtain ⟨H₁, hH₁_ne, hH₁_top, hH₁_inv, hH₁_min⟩ :=
    D.exists_minimal_proper_U_invariant not_Galois
  let A : W₁ → Subgroup Hbar :=
    fun w ↦ actionConjugate D.W₁_action H₁ w
  have hA_ne (w : W₁) : A w ≠ ⊥ :=
    (D.actionConjugate_minimal_U_invariant
      hH₁_ne hH₁_inv hH₁_min w).1
  have hA_inv (w : W₁) : IsInvariantSubgroup D.U_action (A w) :=
    (D.actionConjugate_minimal_U_invariant
      hH₁_ne hH₁_inv hH₁_min w).2.1
  have hA_min (w : W₁) (K : Subgroup Hbar)
      (hKA : K ≤ A w) (hK_ne : K ≠ ⊥)
      (hK : IsInvariantSubgroup D.U_action K) : K = A w :=
    (D.actionConjugate_minimal_U_invariant
      hH₁_ne hH₁_inv hH₁_min w).2.2 K hKA hK_ne hK
  obtain ⟨s, _hs, hsind, hssup⟩ :=
    exists_supIndep_subfamily_of_minimal_invariant
      D.U_action A hA_ne hA_inv hA_min (Finset.univ : Finset W₁)
  have hfull : (⨆ w : W₁, A w) = ⊤ :=
    D.actionConjugate_iSup_eq_top hD hH₁_inv hH₁_ne
  have hssup_top : s.sup A = ⊤ := by
    rw [hssup, Finset.sup_eq_iSup]
    simpa using hfull
  have hs_iSup : (⨆ w : s, A w) = ⊤ := by
    simpa only [iSup_subtype, Finset.sup_eq_iSup] using hssup_top
  have hs_indep : iSupIndep (fun w : s ↦ A w) :=
    iSupIndep_comp_coe_iff_supIndep.mpr hsind
  have hs_direct : IsInternalDirectProductFamily (fun w : s ↦ A w) := by
    refine ⟨hs_iSup, hs_indep, ?_⟩
    intro i j _hij x _hx y _hy
    exact isMulCommutative_iff.mp
      (inferInstance : IsMulCommutative Hbar) x y
  have hcardA (w : W₁) : Nat.card (A w) = Nat.card H₁ := by
    change Nat.card (H₁.map (D.W₁_action w).toMonoidHom) = Nat.card H₁
    exact (Nat.card_congr
      ((D.W₁_action w).subgroupMap H₁).toEquiv).symm
  have hcard_span : Nat.card Hbar = Nat.card H₁ ^ s.card := by
    rw [natCard_eq_prod_of_isInternalDirectProductFamily
      (fun w : s ↦ A w) hs_direct]
    simp_rw [hcardA]
    simp [Nat.card_eq_finsetCard]
  letI : Fact D.p.Prime := ⟨D.p_prime⟩
  obtain ⟨d, hcardH₁⟩ :=
    (hD.elementary.isPGroup.to_subgroup H₁).exists_card_eq
  have hexponents : D.q = d * s.card := by
    apply Nat.pow_right_injective D.p_prime.two_le
    calc
      D.p ^ D.q = Nat.card Hbar := D.card_Hbar.symm
      _ = Nat.card H₁ ^ s.card := hcard_span
      _ = (D.p ^ d) ^ s.card := by rw [hcardH₁]
      _ = D.p ^ (d * s.card) := by rw [pow_mul]
  have hd_ne_zero : d ≠ 0 := by
    intro hd
    apply hH₁_ne
    rw [Subgroup.eq_bot_iff_card, hcardH₁, hd, pow_zero]
  have hd_ne_q : d ≠ D.q := by
    intro hd
    apply hH₁_top
    apply Subgroup.eq_top_of_card_eq
    rw [hcardH₁, hd, D.card_Hbar]
  have hd_dvd_q : d ∣ D.q := ⟨s.card, hexponents⟩
  have hd_one : d = 1 :=
    (D.q_prime.eq_one_or_self_of_dvd d hd_dvd_q).resolve_right hd_ne_q
  have hs_card : s.card = D.q := by
    simpa [hd_one] using hexponents.symm
  have hs_univ : s = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hs_card]
    simpa [Nat.card_eq_fintype_card] using D.card_W₁.symm
  have hA_indep : iSupIndep A := by
    apply Finset.SupIndep.iSupIndep_of_univ
    simpa [hs_univ] using hsind
  have hA_direct : IsInternalDirectProductFamily A := by
    refine ⟨hfull, hA_indep, ?_⟩
    intro i j _hij x _hx y _hy
    exact isMulCommutative_iff.mp
      (inferInstance : IsMulCommutative Hbar) x y
  have hcardH₁p : Nat.card H₁ = D.p := by
    rw [hcardH₁, hd_one, pow_one]
  exact ⟨H₁, hcardH₁p, hH₁_inv, hA_direct⟩

/-- A nonzero invariant constituent cannot be fixed pointwise by all of `U`. -/
theorem pointwiseActionKernel_ne_top_of_nonzero
    (D : PTypeFactorActionData Hbar U W₁)
    (hD : PTypeFactorActionHypotheses D)
    {L : Subgroup Hbar} (hL : IsInvariantSubgroup D.U_action L)
    (hL_ne : L ≠ ⊥) :
    pointwiseActionKernel D.U_action L ≠ ⊤ := by
  intro hKtop
  apply D.C_ne_top
  rw [D.C_eq_kernel]
  apply top_unique
  intro x _hx
  rw [mem_pointwiseActionKernel_iff]
  intro h _hh
  let Fix : Subgroup Hbar :=
    { carrier := {y | D.U_action x y = y}
      one_mem' := by simp
      mul_mem' := by
        intro y z hy hz
        change D.U_action x (y * z) = y * z
        rw [map_mul, hy, hz]
      inv_mem' := by
        intro y hy
        change D.U_action x y⁻¹ = y⁻¹
        rw [map_inv, hy] }
  have hspan := D.actionConjugate_iSup_eq_top hD hL hL_ne
  have horbitFix :
      (⨆ w : W₁, actionConjugate D.W₁_action L w) ≤ Fix := by
    apply iSup_le
    intro w y hy
    change D.U_action x y = y
    rw [mem_actionConjugate_iff] at hy
    let x' : U := D.W₁_action_U w⁻¹ x
    have hx' : D.W₁_action_U w x' = x := by simp [x']
    have hx'K : x' ∈ pointwiseActionKernel D.U_action L := by
      rw [hKtop]
      exact Subgroup.mem_top x'
    have hfix :
        D.U_action x' ((D.W₁_action w).symm y) =
          (D.W₁_action w).symm y :=
      (mem_pointwiseActionKernel_iff D.U_action L x').mp hx'K _ hy
    simpa [hx', hfix] using
      D.action_compatibility x' w ((D.W₁_action w).symm y)
  have htopFix : (⊤ : Subgroup Hbar) ≤ Fix := by
    rw [← hspan]
    exact horbitFix
  exact htopFix (Subgroup.mem_top h)

/-- The constituent action therefore has nontrivial quotient. -/
theorem pointwiseActionKernel_index_gt_one
    (D : PTypeFactorActionData Hbar U W₁)
    (hD : PTypeFactorActionHypotheses D)
    {L : Subgroup Hbar} (hL : IsInvariantSubgroup D.U_action L)
    (hL_ne : L ≠ ⊥) :
    1 < (pointwiseActionKernel D.U_action L).index :=
  Subgroup.one_lt_index_of_ne_top
    (D.pointwiseActionKernel_ne_top_of_nonzero hD hL hL_ne)

/-- On an order-`p` constituent, the action quotient has order dividing
`p - 1`. -/
theorem pointwiseActionKernel_index_dvd_prime_pred
    (D : PTypeFactorActionData Hbar U W₁)
    {L : Subgroup Hbar} (hL : IsInvariantSubgroup D.U_action L)
    (hcard : Nat.card L = D.p) :
    (pointwiseActionKernel D.U_action L).index ∣ D.p - 1 := by
  let rhoL : U →* MulAut L := restrictMulAutHom L D.U_action hL
  have hker : rhoL.ker = pointwiseActionKernel D.U_action L :=
    restrictMulAutHom_ker_eq_pointwiseActionKernel D.U_action L hL
  letI : Fact D.p.Prime := ⟨D.p_prime⟩
  letI : IsCyclic L := isCyclic_of_prime_card hcard
  have hAutCard : Nat.card (MulAut L) = D.p - 1 := by
    rw [IsCyclic.card_mulAut, hcard, Nat.totient_prime D.p_prime]
  rw [← hker, Subgroup.index_ker, ← hAutCard]
  exact rhoL.range.card_subgroup_dvd_card

/-- The restricted faithful action embeds its quotient in a cyclic
automorphism group. -/
theorem pointwiseActionKernel_quotient_isCyclic
    (D : PTypeFactorActionData Hbar U W₁)
    {L : Subgroup Hbar} (hL : IsInvariantSubgroup D.U_action L)
    (hcard : Nat.card L = D.p) :
    let K := pointwiseActionKernel D.U_action L
    letI : K.Normal := pointwiseActionKernel_normal D.U_action L hL
    IsCyclic (U ⧸ K) := by
  let K := pointwiseActionKernel D.U_action L
  letI : K.Normal := pointwiseActionKernel_normal D.U_action L hL
  let rhoL : U →* MulAut L := restrictMulAutHom L D.U_action hL
  have hker : rhoL.ker = K :=
    restrictMulAutHom_ker_eq_pointwiseActionKernel D.U_action L hL
  letI : Fact D.p.Prime := ⟨D.p_prime⟩
  letI : IsCyclic L := isCyclic_of_prime_card hcard
  letI : Fact (Nat.card L).Prime :=
    ⟨by simpa [hcard] using D.p_prime⟩
  let eAut : MulAut L ≃* (ZMod (Nat.card L))ˣ :=
    IsCyclic.mulAutMulEquiv L
  have hAutCyclic : IsCyclic (MulAut L) := by
    apply eAut.isCyclic.mpr
    infer_instance
  letI : IsCyclic (MulAut L) := hAutCyclic
  have hRangeCyclic : IsCyclic rhoL.range := by infer_instance
  let e : U ⧸ K ≃* rhoL.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange rhoL)
  exact e.isCyclic.mpr hRangeCyclic

/-- The kernel on a translated constituent is transported by the inverse
`W₁`-action on `U`. -/
theorem mem_pointwiseActionKernel_actionConjugate_iff
    (D : PTypeFactorActionData Hbar U W₁)
    (L : Subgroup Hbar) (w : W₁) (x : U) :
    x ∈ pointwiseActionKernel D.U_action
          (actionConjugate D.W₁_action L w) ↔
      D.W₁_action_U w⁻¹ x ∈ pointwiseActionKernel D.U_action L := by
  rw [mem_pointwiseActionKernel_iff, mem_pointwiseActionKernel_iff]
  constructor
  · intro hx h hhL
    let x' : U := D.W₁_action_U w⁻¹ x
    have hxw : D.W₁_action_U w x' = x := by simp [x']
    have hwh : D.W₁_action w h ∈
        actionConjugate D.W₁_action L w := by
      rw [mem_actionConjugate_iff]
      simpa using hhL
    have hfix := hx (D.W₁_action w h) hwh
    have hcompat := D.action_compatibility x' w h
    change D.U_action x' h = h
    apply (D.W₁_action w).injective
    simpa [hxw, hfix] using hcompat.symm
  · intro hx h hh
    rw [mem_actionConjugate_iff] at hh
    let h' : Hbar := (D.W₁_action w).symm h
    let x' : U := D.W₁_action_U w⁻¹ x
    have hxw : D.W₁_action_U w x' = x := by simp [x']
    have hfix : D.U_action x' h' = h' := hx h' hh
    simpa [h', hxw, hfix] using D.action_compatibility x' w h'

/-- If the orbit spans `Hbar`, then `C` is the intersection of all
constituent kernels. -/
theorem C_eq_iInf_pointwiseActionKernel_of_iSup_eq_top
    (D : PTypeFactorActionData Hbar U W₁)
    (L : Subgroup Hbar)
    (hspan : (⨆ w : W₁, actionConjugate D.W₁_action L w) = ⊤) :
    D.C = ⨅ w : W₁,
      pointwiseActionKernel D.U_action
        (actionConjugate D.W₁_action L w) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_iInf]
    intro w
    rw [D.mem_C_iff] at hx
    rw [mem_pointwiseActionKernel_iff]
    intro h _hh
    exact hx h
  · intro x hx
    rw [D.mem_C_iff]
    intro h
    let Fix : Subgroup Hbar :=
      { carrier := {y | D.U_action x y = y}
        one_mem' := by simp
        mul_mem' := by
          intro y z hy hz
          change D.U_action x (y * z) = y * z
          rw [map_mul, hy, hz]
        inv_mem' := by
          intro y hy
          change D.U_action x y⁻¹ = y⁻¹
          rw [map_inv, hy] }
    have horbitFix :
        (⨆ w : W₁, actionConjugate D.W₁_action L w) ≤ Fix := by
      apply iSup_le
      intro w y hy
      have hxw : x ∈ pointwiseActionKernel D.U_action
          (actionConjugate D.W₁_action L w) :=
        (Subgroup.mem_iInf.mp hx) w
      exact (mem_pointwiseActionKernel_iff _ _ _).mp hxw y hy
    have htopFix : (⊤ : Subgroup Hbar) ≤ Fix := by
      rw [← hspan]
      exact horbitFix
    exact htopFix (Subgroup.mem_top h)

/-- A full direct family of conjugates forces the constituent order to be
exactly `p`. -/
theorem card_eq_prime_of_conjugates_direct
    (D : PTypeFactorActionData Hbar U W₁)
    (L : Subgroup Hbar)
    (hdir : IsInternalDirectProductFamily
      (fun w : W₁ ↦ actionConjugate D.W₁_action L w)) :
    Nat.card L = D.p := by
  classical
  letI := Fintype.ofFinite W₁
  let A : W₁ → Subgroup Hbar :=
    fun w ↦ actionConjugate D.W₁_action L w
  have hcardA (w : W₁) : Nat.card (A w) = Nat.card L := by
    change Nat.card (L.map (D.W₁_action w).toMonoidHom) = Nat.card L
    exact (Nat.card_congr
      ((D.W₁_action w).subgroupMap L).toEquiv).symm
  have hcardProduct : Nat.card Hbar = (Nat.card L) ^ D.q := by
    calc
      Nat.card Hbar = ∏ w : W₁, Nat.card (A w) :=
        natCard_eq_prod_of_isInternalDirectProductFamily A hdir
      _ = ∏ _w : W₁, Nat.card L := by
        apply Finset.prod_congr rfl
        intro w _hw
        exact hcardA w
      _ = (Nat.card L) ^ D.q := by
        simp [← Nat.card_eq_fintype_card, D.card_W₁]
  have hpows : D.p ^ D.q = (Nat.card L) ^ D.q := by
    rw [← D.card_Hbar]
    exact hcardProduct
  exact (Nat.pow_left_injective D.q_prime.ne_zero hpows).symm

/-- Differences between the `q` cyclic coordinate characters give a
faithful row representation of `U / C` with `q - 1` coordinates. -/
theorem complement_factor_vector_of_constituent
    (D : PTypeFactorActionData Hbar U W₁)
    (hD : PTypeFactorActionHypotheses D)
    {L : Subgroup Hbar}
    (hL : IsInvariantSubgroup D.U_action L)
    (hcard : Nat.card L = D.p)
    (hspan : (⨆ w : W₁, actionConjugate D.W₁_action L w) = ⊤) :
    let a := (pointwiseActionKernel D.U_action L).index
    letI : D.C.Normal := D.C_normal
    ∃ iota : (U ⧸ D.C) →*
        Multiplicative (Fin (D.q - 1) → ZMod a),
      Function.Injective iota := by
  classical
  letI := Fintype.ofFinite W₁
  let K := pointwiseActionKernel D.U_action L
  let a := K.index
  letI : K.Normal := pointwiseActionKernel_normal D.U_action L hL
  letI : D.C.Normal := D.C_normal
  have hL_ne : L ≠ ⊥ := by
    apply L.one_lt_card_iff_ne_bot.mp
    rw [hcard]
    exact D.p_prime.one_lt
  have ha : 1 < a := D.pointwiseActionKernel_index_gt_one hD hL hL_ne
  letI : NeZero a := ⟨(Nat.zero_lt_one.trans ha).ne'⟩
  letI : IsCyclic (U ⧸ K) :=
    D.pointwiseActionKernel_quotient_isCyclic hL hcard
  let eK : (U ⧸ K) ≃* Multiplicative (ZMod a) := by
    let eCard :=
      (zmodCyclicMulEquiv
        (inferInstance : IsCyclic (U ⧸ K))).symm
    let eMod : Multiplicative (ZMod (Nat.card (U ⧸ K))) ≃*
        Multiplicative (ZMod a) :=
      AddEquiv.toMultiplicative
        (ZMod.ringEquivCongr K.index_eq_card.symm).toAddEquiv
    exact eCard.trans eMod
  let chi : U →* Multiplicative (ZMod a) :=
    eK.toMonoidHom.comp (QuotientGroup.mk' K)
  have hchi_ker : chi.ker = K := by
    change (eK.toMonoidHom.comp (QuotientGroup.mk' K)).ker = K
    rw [MonoidHom.ker_comp_of_injective
      (QuotientGroup.mk' K) eK.toMonoidHom eK.injective,
      QuotientGroup.ker_mk']
  let chiW : W₁ → U →* Multiplicative (ZMod a) := fun w ↦
    chi.comp (D.W₁_action_U w⁻¹).toMonoidHom
  have hchiW_ker (w : W₁) :
      (chiW w).ker = pointwiseActionKernel D.U_action
        (actionConjugate D.W₁_action L w) := by
    ext x
    rw [MonoidHom.mem_ker]
    change chi (D.W₁_action_U w⁻¹ x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hchi_ker]
    exact (D.mem_pointwiseActionKernel_actionConjugate_iff L w x).symm
  have hC_intersection :
      D.C = ⨅ w : W₁, pointwiseActionKernel D.U_action
        (actionConjugate D.W₁_action L w) :=
    D.C_eq_iInf_pointwiseActionKernel_of_iSup_eq_top L hspan
  let W₁nz := {w : W₁ // w ≠ 1}
  have hcardW₁ : Fintype.card W₁ = D.q := by
    simpa [Nat.card_eq_fintype_card] using D.card_W₁
  have hcardW₁nz : Fintype.card W₁nz = D.q - 1 := by
    dsimp [W₁nz]
    calc
      Fintype.card {w : W₁ // w ≠ 1} = Fintype.card W₁ - 1 :=
        Set.card_ne_eq 1
      _ = D.q - 1 := by rw [hcardW₁]
  let enumW₁ : Fin (D.q - 1) ≃ W₁nz :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, hcardW₁nz])
  let row : U →* Multiplicative (Fin (D.q - 1) → ZMod a) :=
    { toFun := fun x ↦ Multiplicative.ofAdd fun i ↦
        (chiW (enumW₁ i).1 x).toAdd - (chi x).toAdd
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        simp [chiW]
      map_mul' := by
        intro x y
        apply Multiplicative.toAdd.injective
        funext i
        change
          (chiW (enumW₁ i).1 (x * y)).toAdd -
              (chi (x * y)).toAdd =
            ((chiW (enumW₁ i).1 x).toAdd - (chi x).toAdd) +
              ((chiW (enumW₁ i).1 y).toAdd - (chi y).toAdd)
        simp only [map_mul, toAdd_mul]
        abel }
  have hrow_ker : row.ker = D.C := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hxrow
      have hcoordinate (w : W₁) (hw : w ≠ 1) :
          chiW w x = chi x := by
        let wnz : W₁nz := ⟨w, hw⟩
        obtain ⟨i, hi⟩ := enumW₁.surjective wnz
        have hxi := congrArg
          (fun z : Multiplicative (Fin (D.q - 1) → ZMod a) ↦
            z.toAdd i) hxrow
        change (chiW (enumW₁ i).1 x).toAdd - (chi x).toAdd = 0 at hxi
        have hi' : (enumW₁ i).1 = w := congrArg Subtype.val hi
        rw [hi'] at hxi
        apply Multiplicative.toAdd.injective
        exact sub_eq_zero.mp hxi
      have hall (w : W₁) : chiW w x = chi x := by
        by_cases hw : w = 1
        · subst w
          simp [chiW]
        · exact hcoordinate w hw
      have hW₁_nontrivial : 1 < Nat.card W₁ := by
        rw [D.card_W₁]
        exact D.q_prime.one_lt
      letI : Nontrivial W₁ :=
        Finite.one_lt_card_iff_nontrivial.mp hW₁_nontrivial
      obtain ⟨w₀, hw₀⟩ := exists_ne (1 : W₁)
      let delta : U := D.W₁_action_U w₀ x * x⁻¹
      have htransport (v : W₁) :
          chiW v (D.W₁_action_U w₀ x) =
            chiW (w₀⁻¹ * v) x := by
        simp [chiW, mul_inv_rev]
      have hdelta_all : delta ∈
          ⨅ v : W₁, pointwiseActionKernel D.U_action
            (actionConjugate D.W₁_action L v) := by
        rw [Subgroup.mem_iInf]
        intro v
        rw [← hchiW_ker v, MonoidHom.mem_ker]
        change chiW v delta = 1
        dsimp [delta]
        rw [map_mul, map_inv, htransport, hall, hall, mul_inv_cancel]
      have hdeltaC : delta ∈ D.C := by
        rw [hC_intersection]
        exact hdelta_all
      exact hD.fixed_coset_trivial w₀ hw₀ x (by
        simpa [delta] using hdeltaC)
    · intro hxC
      apply Multiplicative.toAdd.injective
      funext i
      change (chiW (enumW₁ i).1 x).toAdd - (chi x).toAdd = 0
      have hxall : x ∈
          ⨅ w : W₁, pointwiseActionKernel D.U_action
            (actionConjugate D.W₁_action L w) := by
        rw [← hC_intersection]
        exact hxC
      have hxw : x ∈ (chiW (enumW₁ i).1).ker := by
        rw [hchiW_ker]
        exact (Subgroup.mem_iInf.mp hxall) (enumW₁ i).1
      have hxK : x ∈ K := by
        rw [mem_pointwiseActionKernel_iff]
        intro h _hh
        exact (D.mem_C_iff x).mp hxC h
      have hchiW_one : chiW (enumW₁ i).1 x = 1 :=
        MonoidHom.mem_ker.mp hxw
      have hchi_one : chi x = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [hchi_ker]
        exact hxK
      rw [hchiW_one, hchi_one]
      simp
  let iota : (U ⧸ D.C) →*
      Multiplicative (Fin (D.q - 1) → ZMod a) :=
    QuotientGroup.lift D.C row (by rw [hrow_ker])
  refine ⟨iota, ?_⟩
  apply (QuotientGroup.injective_lift_iff D.C row _).mpr
  exact hrow_ker.symm

end PTypeFactorActionData

/-! ## Peterfalvi (9.7a) -/

/-- The complete non-Galois conclusion for the canonical factor action. -/
structure TypePGaloisNonConclusion
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) where
  H₁ : Subgroup Hbar
  card_H₁ : Nat.card H₁ = D.p
  H₁_normalized : IsInvariantSubgroup D.U_action H₁
  acts_on_H₁ : ∀ (u : U) {h : Hbar}, h ∈ H₁ → D.U_action u h ∈ H₁
  conjugates_direct :
    IsInternalDirectProductFamily
      (fun w : W₁ ↦ actionConjugate D.W₁_action H₁ w)
  actionKernel_normal :
    (pointwiseActionKernel D.U_action H₁).Normal
  index_gt_one :
    1 < (pointwiseActionKernel D.U_action H₁).index
  index_dvd_prime_pred :
    (pointwiseActionKernel D.U_action H₁).index ∣ D.p - 1
  pointwise_factor_cyclic :
    let K := pointwiseActionKernel D.U_action H₁
    letI : K.Normal := actionKernel_normal
    IsCyclic (U ⧸ K)
  complement_factor_vector :
    let a := (pointwiseActionKernel D.U_action H₁).index
    letI : D.C.Normal := D.C_normal
    ∃ iota : (U ⧸ D.C) →*
        Multiplicative (Fin (D.q - 1) → ZMod a),
      Function.Injective iota

/-- `PFsection9.v: typeP_Galois_Pn`, Peterfalvi (9.7a). -/
noncomputable def typeP_Galois_Pn
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (hD : PTypeFactorActionHypotheses D)
    (not_Galois : ¬ typeP_Galois D) :
    TypePGaloisNonConclusion D := by
  let hex := D.exists_nonGalois_constituent_direct hD not_Galois
  let H₁ : Subgroup Hbar := Classical.choose hex
  have hdata := Classical.choose_spec hex
  have hcardH₁ : Nat.card H₁ = D.p := hdata.1
  have hH₁ : IsInvariantSubgroup D.U_action H₁ := hdata.2.1
  have hdirect : IsInternalDirectProductFamily
      (fun w : W₁ ↦ actionConjugate D.W₁_action H₁ w) :=
    hdata.2.2
  let K := pointwiseActionKernel D.U_action H₁
  have hKnormal : K.Normal :=
    pointwiseActionKernel_normal D.U_action H₁ hH₁
  have hH₁ne : H₁ ≠ ⊥ := by
    apply H₁.one_lt_card_iff_ne_bot.mp
    rw [hcardH₁]
    exact D.p_prime.one_lt
  refine
    { H₁ := H₁
      card_H₁ := hcardH₁
      H₁_normalized := hH₁
      acts_on_H₁ := fun u _h hh ↦ hH₁.mem u hh
      conjugates_direct := hdirect
      actionKernel_normal := hKnormal
      index_gt_one :=
        D.pointwiseActionKernel_index_gt_one hD hH₁ hH₁ne
      index_dvd_prime_pred :=
        D.pointwiseActionKernel_index_dvd_prime_pred hH₁ hcardH₁
      pointwise_factor_cyclic :=
        D.pointwiseActionKernel_quotient_isCyclic hH₁ hcardH₁
      complement_factor_vector :=
        D.complement_factor_vector_of_constituent
          hD hH₁ hcardH₁ hdirect.1 }

end

end Submission.OddOrder.PF
