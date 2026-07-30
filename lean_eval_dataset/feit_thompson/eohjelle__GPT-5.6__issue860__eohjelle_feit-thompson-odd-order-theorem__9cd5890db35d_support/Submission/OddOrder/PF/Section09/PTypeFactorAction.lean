import Submission.OddOrder.PF.Section09.PTypeActionInfrastructure

/-!
# Peterfalvi Section 9: the canonical factor action

This module packages the actions on the selected Fitting chief factor and the
four structural properties shared by the two alternatives of Peterfalvi (9.7).
It also records the subgroup formulation of the Galois alternative.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped Pointwise

noncomputable section

universe u

/-! ## Abstract factor-action data -/

/-- The quotient actions and cardinal data used in Peterfalvi (9.7). -/
structure PTypeFactorActionData
    (Hbar U W₁ : Type u)
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁] where
  p : ℕ
  q : ℕ
  p_prime : p.Prime
  q_prime : q.Prime
  U_action : U →* MulAut Hbar
  W₁_action : W₁ →* MulAut Hbar
  W₁_action_U : W₁ →* MulAut U
  action_compatibility : ∀ (u : U) (w : W₁) (h : Hbar),
    U_action (W₁_action_U w u) (W₁_action w h) =
      W₁_action w (U_action u h)
  C : Subgroup U
  C_normal : C.Normal
  C_eq_kernel : C = pointwiseActionKernel U_action ⊤
  C_ne_top : C ≠ ⊤
  W₂bar : Subgroup Hbar
  W₂bar_fixed : ∀ h : Hbar,
    h ∈ W₂bar ↔ ∀ w : W₁, W₁_action w h = h
  card_W₁ : Nat.card W₁ = q
  card_W₂bar : Nat.card W₂bar = p
  card_Hbar : Nat.card Hbar = p ^ q

/-- The structural hypotheses used by both alternatives of Peterfalvi (9.7). -/
structure PTypeFactorActionHypotheses
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) : Prop where
  elementary : IsElementaryAbelianGroup D.p Hbar
  joint_minimal :
    ∀ L : Subgroup Hbar,
      IsInvariantSubgroup D.U_action L →
      IsInvariantSubgroup D.W₁_action L →
      L = ⊥ ∨ L = ⊤
  commutator_le_C : _root_.commutator U ≤ D.C
  fixed_coset_trivial :
    ∀ (w : W₁), w ≠ 1 → ∀ (x : U),
      D.W₁_action_U w x * x⁻¹ ∈ D.C → x ∈ D.C

/-! ## Extraction from the Section 9 context -/

/-- The factor-action data extracted from the selected Fitting chief factor. -/
noncomputable def Ptype_factor_action
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    PTypeFactorActionData (ptypeFCoreFactor ctx) U W₁ := by
  let H₀ := Ptype_Fcore_kernel ctx
  let H := Fitting_core M
  let N : Subgroup H := H₀.subgroupOf H
  have hcommon : of_typeII_IV M U W W₁ W₂ ctx.defW :=
    compl_of_typeII_IV M U W W₁ W₂ ctx.defW ctx.maxM
      ctx.typeP ctx.not_type5
  refine
    { p := ptypeFactorPrime ctx
      q := Nat.card W₁
      p_prime := ptypeFactorPrime_prime ctx
      q_prime := hcommon.2.2.1
      U_action := ptypeFCoreAction ctx
      W₁_action := ptypeW₁FactorAction ctx
      W₁_action_U := ptypeW₁ComplAction ctx
      action_compatibility := ?_
      C := (ptypeFCoreAction ctx).ker
      C_normal := inferInstance
      C_eq_kernel := ?_
      C_ne_top := ?_
      W₂bar := ptypeW₂Factor ctx
      W₂bar_fixed := ?_
      card_W₁ := rfl
      card_W₂bar := facts.fixed_factor_card
      card_Hbar := facts.factor_card }
  · intro u w z
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N z
    simp only [ptypeFCoreAction, ptypeW₁FactorAction]
    apply congrArg (QuotientGroup.mk' N)
    apply Subtype.ext
    change
      ((w : G) * (u : G) * (w : G)⁻¹) *
          ((w : G) * (h : G) * (w : G)⁻¹) *
          ((w : G) * (u : G) * (w : G)⁻¹)⁻¹ =
        (w : G) * ((u : G) * (h : G) * (u : G)⁻¹) * (w : G)⁻¹
    group
  · ext x
    rw [MonoidHom.mem_ker, mem_pointwiseActionKernel_iff]
    constructor
    · intro hx h _
      exact DFunLike.congr_fun hx h
    · intro hx
      apply MulEquiv.ext
      intro h
      exact hx h (Subgroup.mem_top h)
  · intro htop
    apply facts.compl_kernel_ne
    ext g
    constructor
    · intro hg
      exact Ptype_Fcompl_kernel_le ctx hg
    · intro hg
      let gU : U := ⟨g, hg⟩
      refine ⟨gU, ?_, rfl⟩
      rw [htop]
      exact Subgroup.mem_top gU
  · intro h
    letI : MulDistribMulAction W₁ (ptypeFCoreFactor ctx) :=
      MulDistribMulAction.compHom
        (ptypeFCoreFactor ctx) (ptypeW₁FactorAction ctx)
    change h ∈ FixedPoints.subgroup W₁ (ptypeFCoreFactor ctx) ↔ _
    exact FixedPoints.mem_subgroup W₁ (ptypeFCoreFactor ctx) h

@[simp]
theorem Ptype_factor_action_p
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (Ptype_factor_action ctx facts).p = ptypeFactorPrime ctx :=
  rfl

@[simp]
theorem Ptype_factor_action_q
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (Ptype_factor_action ctx facts).q = Nat.card W₁ :=
  rfl

@[simp]
theorem Ptype_factor_action_U_action
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (Ptype_factor_action ctx facts).U_action = ptypeFCoreAction ctx :=
  rfl

@[simp]
theorem Ptype_factor_action_W₁_action
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (Ptype_factor_action ctx facts).W₁_action = ptypeW₁FactorAction ctx :=
  rfl

@[simp]
theorem Ptype_factor_action_W₁_action_U
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (Ptype_factor_action ctx facts).W₁_action_U = ptypeW₁ComplAction ctx :=
  rfl

@[simp]
theorem Ptype_factor_action_C
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (Ptype_factor_action ctx facts).C = (ptypeFCoreAction ctx).ker :=
  rfl

@[simp]
theorem Ptype_factor_action_W₂bar
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (Ptype_factor_action ctx facts).W₂bar = ptypeW₂Factor ctx :=
  rfl

/-- The common structural hypotheses for the canonical factor action. -/
theorem Ptype_factor_action_hypotheses
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    PTypeFactorActionHypotheses (Ptype_factor_action ctx facts) := by
  refine
    { elementary := ?_
      joint_minimal := ?_
      commutator_le_C := ?_
      fixed_coset_trivial := ?_ }
  · simpa only [Ptype_factor_action_p] using
      ptypeFCoreFactor_elementary ctx
  · intro L hU hW
    apply ptypeFCoreFactor_joint_minimal ctx L
    · simpa only [Ptype_factor_action_U_action, IsInvariantSubgroup,
        IsInvariantUnderMulAutAction] using hU
    · simpa only [Ptype_factor_action_W₁_action, IsInvariantSubgroup,
        IsInvariantUnderMulAutAction] using hW
  · simpa only [Ptype_factor_action_C] using
      ptypeFCoreAction_commutator_le_ker ctx
  · intro w hw x hx
    apply ptypeFComplFactor_fixed_coset_trivial ctx w hw x
    simpa only [Ptype_factor_action_W₁_action_U,
      Ptype_factor_action_C] using hx

/-! ## Consequences of the abstract package -/

namespace PTypeFactorActionData

variable {Hbar U W₁ : Type u}
variable [Group Hbar] [Finite Hbar]
variable [Group U] [Finite U]
variable [Group W₁] [Finite W₁]

/-- Membership in `C` means acting trivially on the whole chief factor. -/
theorem mem_C_iff
    (D : PTypeFactorActionData Hbar U W₁) (x : U) :
    x ∈ D.C ↔ ∀ h : Hbar, D.U_action x h = h := by
  rw [D.C_eq_kernel, mem_pointwiseActionKernel_iff]
  constructor
  · intro hx h
    exact hx h (Subgroup.mem_top h)
  · intro hx h _
    exact hx h

/-- The action compatibility makes `C` stable under `W₁`. -/
theorem W₁_action_U_mem_C
    (D : PTypeFactorActionData Hbar U W₁)
    (w : W₁) {x : U} (hx : x ∈ D.C) :
    D.W₁_action_U w x ∈ D.C := by
  rw [D.mem_C_iff] at hx ⊢
  intro h
  have hfix := hx (D.W₁_action w⁻¹ h)
  calc
    D.U_action (D.W₁_action_U w x) h =
        D.U_action (D.W₁_action_U w x)
          (D.W₁_action w (D.W₁_action w⁻¹ h)) := by simp
    _ = D.W₁_action w
        (D.U_action x (D.W₁_action w⁻¹ h)) :=
      D.action_compatibility x w (D.W₁_action w⁻¹ h)
    _ = D.W₁_action w (D.W₁_action w⁻¹ h) := by rw [hfix]
    _ = h := by simp

/-- The kernel `C` is invariant under the `W₁`-action on `U`. -/
theorem C_invariant
    (D : PTypeFactorActionData Hbar U W₁) :
    IsInvariantSubgroup D.W₁_action_U D.C := by
  intro w
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact D.W₁_action_U_mem_C w hx
  · intro x hx
    refine ⟨D.W₁_action_U w⁻¹ x,
      D.W₁_action_U_mem_C w⁻¹ hx, ?_⟩
    simp

/-- A `W₁`-translate of a `U`-invariant subgroup remains `U`-invariant. -/
theorem actionConjugate_U_invariant
    (D : PTypeFactorActionData Hbar U W₁)
    {L : Subgroup Hbar} (hL : IsInvariantSubgroup D.U_action L)
    (w : W₁) :
    IsInvariantSubgroup D.U_action
      (actionConjugate D.W₁_action L w) := by
  intro x
  let T := actionConjugate D.W₁_action L w
  have hforward (z : U) :
      T.map (D.U_action z).toMonoidHom ≤ T := by
    rintro _ ⟨y, hy, rfl⟩
    change y ∈ actionConjugate D.W₁_action L w at hy
    change D.U_action z y ∈ actionConjugate D.W₁_action L w
    unfold actionConjugate at hy ⊢
    rw [Subgroup.mem_map_equiv] at hy ⊢
    let z' : U := D.W₁_action_U w⁻¹ z
    have hz' : D.W₁_action_U w z' = z := by
      simp [z']
    have hcompat := D.action_compatibility z' w
      ((D.W₁_action w).symm y)
    have hyL : (D.W₁_action w).symm y ∈ L := hy
    have hzyL : D.U_action z' ((D.W₁_action w).symm y) ∈ L :=
      hL.mem z' hyL
    have heq := congrArg (D.W₁_action w).symm hcompat
    have heq' :
        (D.W₁_action w).symm (D.U_action z y) =
          D.U_action z' ((D.W₁_action w).symm y) := by
      simpa [hz'] using heq
    rwa [heq']
  apply le_antisymm (hforward x)
  intro h hh
  have hpre : D.U_action x⁻¹ h ∈ T :=
    hforward x⁻¹ ⟨h, hh, rfl⟩
  refine ⟨D.U_action x⁻¹ h, hpre, ?_⟩
  simp

/-- The supremum of a full `W₁`-orbit is `W₁`-invariant. -/
theorem actionConjugate_iSup_W₁_invariant
    (D : PTypeFactorActionData Hbar U W₁)
    (L : Subgroup Hbar) :
    IsInvariantSubgroup D.W₁_action
      (⨆ w : W₁, actionConjugate D.W₁_action L w) := by
  intro w
  let T := ⨆ x : W₁, actionConjugate D.W₁_action L x
  have hforward (z : W₁) :
      T.map (D.W₁_action z).toMonoidHom ≤ T := by
    change
      (⨆ x : W₁, actionConjugate D.W₁_action L x).map
          (D.W₁_action z).toMonoidHom ≤
        ⨆ x : W₁, actionConjugate D.W₁_action L x
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro x
    change
      actionConjugate D.W₁_action
          (actionConjugate D.W₁_action L x) z ≤
        ⨆ x : W₁, actionConjugate D.W₁_action L x
    rw [← actionConjugate_mul]
    exact le_iSup
      (fun y : W₁ ↦ actionConjugate D.W₁_action L y) (z * x)
  apply le_antisymm (hforward w)
  intro h hh
  have hpre : D.W₁_action w⁻¹ h ∈ T :=
    hforward w⁻¹ ⟨h, hh, rfl⟩
  refine ⟨D.W₁_action w⁻¹ h, hpre, ?_⟩
  simp

/-- The orbit supremum of a `U`-invariant subgroup is `U`-invariant. -/
theorem actionConjugate_iSup_U_invariant
    (D : PTypeFactorActionData Hbar U W₁)
    {L : Subgroup Hbar} (hL : IsInvariantSubgroup D.U_action L) :
    IsInvariantSubgroup D.U_action
      (⨆ w : W₁, actionConjugate D.W₁_action L w) :=
  IsInvariantSubgroup.iSup
    (fun w ↦ D.actionConjugate_U_invariant hL w)

/-- Joint minimality makes the orbit of every nontrivial invariant subgroup
generate the whole chief factor. -/
theorem actionConjugate_iSup_eq_top
    (D : PTypeFactorActionData Hbar U W₁)
    (hD : PTypeFactorActionHypotheses D)
    {L : Subgroup Hbar} (hL : IsInvariantSubgroup D.U_action L)
    (hL_ne : L ≠ ⊥) :
    (⨆ w : W₁, actionConjugate D.W₁_action L w) = ⊤ := by
  let T := ⨆ w : W₁, actionConjugate D.W₁_action L w
  have hTU : IsInvariantSubgroup D.U_action T :=
    D.actionConjugate_iSup_U_invariant hL
  have hTW : IsInvariantSubgroup D.W₁_action T :=
    D.actionConjugate_iSup_W₁_invariant L
  rcases hD.joint_minimal T hTU hTW with hT | hT
  · exfalso
    have hLT : L ≤ T := by
      simpa [T] using
        (le_iSup
          (fun w : W₁ ↦ actionConjugate D.W₁_action L w) (1 : W₁))
    rw [hT] at hLT
    exact hL_ne (eq_bot_iff.mpr hLT)
  · exact hT

end PTypeFactorActionData

/-! ## The Galois alternative -/

/-- `PFsection9.v: typeP_Galois`: irreducibility of the `U`-action on the
nontrivial chief factor. -/
def typeP_Galois
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) : Prop :=
  (⊤ : Subgroup Hbar) ≠ ⊥ ∧
    ∀ L : Subgroup Hbar,
      IsInvariantSubgroup D.U_action L → L = ⊥ ∨ L = ⊤

end

end Submission.OddOrder.PF
