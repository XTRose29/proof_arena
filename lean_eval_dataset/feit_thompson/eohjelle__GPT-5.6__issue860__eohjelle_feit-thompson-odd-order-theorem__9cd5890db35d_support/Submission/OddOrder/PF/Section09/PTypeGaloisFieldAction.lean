import Submission.OddOrder.BG.AppendixC.FiniteFieldImage
import Submission.OddOrder.BG.AppendixC.FiniteFieldUnitDecomposition
import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSubmodule
import Submission.OddOrder.MathlibSupport.IrreducibleCenterCharacter
import Submission.OddOrder.MathlibSupport.SchurScalarIrreducible
import Submission.OddOrder.PF.Section09.PTypeFactorAction
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Peterfalvi Section 9: the finite-field alternative

This module proves the Galois branch of Peterfalvi (9.7).  Starting from the
canonical action on the selected Fitting chief factor, it constructs its
Schur field and identifies the complement and `W₁` actions with scalar and
field-automorphism actions.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.BG.AppendixC
open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative MonoidAlgebra

noncomputable section

universe u

/-! The quotient-action helper in the Wielandt support layer is specialized
to a commutative ambient group.  Here only the quotient is commutative, so we
use the elementary general construction directly. -/

private noncomputable def pTypeQuotientMulAut
    {E : Type*} [Group E] (N : Subgroup E) [N.Normal]
    (e : MulAut E) (hN : N.map e.toMonoidHom = N) :
    MulAut (E ⧸ N) := by
  have he : N ≤ N.comap e.toMonoidHom := by
    intro x hx
    change e x ∈ N
    have hx' : e x ∈ N.map e.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hN] at hx'
  have heinv : N ≤ N.comap e.symm.toMonoidHom := by
    intro x hx
    change e.symm x ∈ N
    have hxmap : x ∈ N.map e.toMonoidHom := by
      rw [hN]
      exact hx
    rcases hxmap with ⟨y, hy, rfl⟩
    simpa using hy
  let q := QuotientGroup.map N N e.toMonoidHom he
  let qinv := QuotientGroup.map N N e.symm.toMonoidHom heinv
  exact MonoidHom.toMulEquiv q qinv
    (by
      apply MonoidHom.ext
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
      simp [q, qinv])
    (by
      apply MonoidHom.ext
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
      simp [q, qinv])

@[simp]
private theorem pTypeQuotientMulAut_apply_mk
    {E : Type*} [Group E] (N : Subgroup E) [N.Normal]
    (e : MulAut E) (hN : N.map e.toMonoidHom = N) (x : E) :
    pTypeQuotientMulAut N e hN (QuotientGroup.mk' N x) =
      QuotientGroup.mk' N (e x) := by
  rfl

private noncomputable def pTypeQuotientMulAutHom
    {A E : Type*} [Group A] [Group E]
    (N : Subgroup E) [N.Normal]
    (f : A →* MulAut E)
    (hN : ∀ a, N.map (f a).toMonoidHom = N) :
    A →* MulAut (E ⧸ N) where
  toFun a := pTypeQuotientMulAut N (f a) (hN a)
  map_one' := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    simp only [pTypeQuotientMulAut_apply_mk, map_one, MulAut.one_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    simp only [pTypeQuotientMulAut_apply_mk, map_mul, MulAut.mul_apply]

/-- A permutation preserving zero and addition. -/
def IsAdditivePermutation
    {F : Type*} [Add F] [Zero F] (alpha : Equiv.Perm F) : Prop :=
  alpha 0 = 0 ∧ ∀ x y : F, alpha (x + y) = alpha x + alpha y

/-- A permutation preserving one and multiplication. -/
def IsMultiplicativePermutation
    {F : Type*} [Mul F] [One F] (alpha : Equiv.Perm F) : Prop :=
  alpha 1 = 1 ∧ ∀ x y : F, alpha (x * y) = alpha x * alpha y

/-- The finite-field data and numerical conclusions of Peterfalvi (9.7b). -/
structure TypePGaloisConclusion
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) where
  F : Type u
  [fieldF : Field F]
  [fintypeF : Fintype F]
  phi : Additive Hbar ≃+ F
  psi : U →* Fˣ
  eta : W₁ →* Equiv.Perm F
  field_automorphisms_exact : ∀ alpha : Equiv.Perm F,
    (IsAdditivePermutation alpha ∧ IsMultiplicativePermutation alpha) ↔
      alpha ∈ Set.range (fun w : W₁ ↦ eta w)
  eta_injective : Function.Injective eta
  phi_W₁_compatible : ∀ (h : Hbar) (w : W₁),
    phi (Additive.ofMul (D.W₁_action w h)) =
      eta w (phi (Additive.ofMul h))
  psi_W₁_compatible : ∀ (x : U) (w : W₁),
    ((psi (D.W₁_action_U w x) : F)) = eta w (psi x : F)
  psi_kernel : psi.ker = D.C
  phi_U_compatible : ∀ (h : Hbar) (x : U),
    phi (Additive.ofMul (D.U_action x h)) =
      phi (Additive.ofMul h) * (psi x : F)
  field_card : Nat.card F = D.p ^ D.q
  primeLine_comap :
    (primeAdditiveLine F).comap phi.toAddMonoidHom =
      D.W₂bar.toAddSubgroup
  complement_factor_cyclic :
    letI : D.C.Normal := D.C_normal
    IsCyclic (U ⧸ D.C)
  complement_factor_coprime :
    letI : D.C.Normal := D.C_normal
    Nat.Coprime (Nat.card (U ⧸ D.C)) (D.p - 1)
  complement_factor_dvd :
    letI : D.C.Normal := D.C_normal
    Nat.card (U ⧸ D.C) ∣
      (D.p ^ D.q - 1) / (D.p - 1)

namespace TypePGaloisConclusion

attribute [instance] fieldF fintypeF

/-- The additive model has the same cardinality as the chief factor. -/
theorem card_Hbar_eq_field
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (h : TypePGaloisConclusion D) :
    Nat.card Hbar = Nat.card h.F :=
  Nat.card_congr h.phi.toEquiv

/-- Symmetric cardinality form used by later character arguments. -/
theorem field_card_eq_factor_card
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (h : TypePGaloisConclusion D) :
    Nat.card h.F = Nat.card Hbar :=
  h.card_Hbar_eq_field.symm

end TypePGaloisConclusion

/-- `PFsection9.v: typeP_Galois_P`, Peterfalvi (9.7b). -/
noncomputable def typeP_Galois_P
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (hD : PTypeFactorActionHypotheses D)
    (is_Galois : typeP_Galois D) :
    TypePGaloisConclusion D := by
  classical
  letI : Fact D.p.Prime := ⟨D.p_prime⟩
  letI : Fact D.q.Prime := ⟨D.q_prime⟩
  letI : D.C.Normal := D.C_normal
  letI : IsMulCommutative Hbar := hD.elementary.commutative
  letI pTypeHbarModule : Module (ZMod D.p) (Additive Hbar) :=
    AddCommGroup.zmodModule fun x ↦ by
      change x.toMul ^ D.p = 1
      exact hD.elementary.pow_eq_one x.toMul

  have hHbarCard : 1 < Nat.card Hbar := by
    rw [D.card_Hbar]
    exact one_lt_pow₀ D.p_prime.one_lt D.q_prime.ne_zero
  letI : Nontrivial Hbar :=
    Finite.one_lt_card_iff_nontrivial.mp hHbarCard

  have hUker : D.U_action.ker = D.C := by
    rw [D.C_eq_kernel]
    ext x
    rw [MonoidHom.mem_ker, mem_pointwiseActionKernel_iff]
    constructor
    · intro hx h _
      simpa using DFunLike.congr_fun hx h
    · intro hx
      apply MulEquiv.ext
      intro h
      exact hx h (Subgroup.mem_top h)

  let Q := U ⧸ D.C
  letI : IsMulCommutative Q :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      hD.commutator_le_C
  let rhoQAction : Q →* MulAut Hbar :=
    QuotientGroup.lift D.C D.U_action (by rw [hUker])
  have hrhoQAction : Function.Injective rhoQAction := by
    apply (QuotientGroup.injective_lift_iff
      D.C D.U_action (by rw [hUker])).mpr
    exact hUker.symm
  let rho : Representation (ZMod D.p) Q (Additive Hbar) :=
    elementaryAbelianActionRepresentation Hbar Q D.p rhoQAction
  let rhoCarrier : rho.asModule → Additive Hbar := fun v ↦ v
  have rhoCarrier_injective : Function.Injective rhoCarrier :=
    fun _ _ h ↦ h
  have hrho : Function.Injective rho := by
    intro x y hxy
    apply hrhoQAction
    apply MulEquiv.ext
    intro h
    have hh := LinearMap.congr_fun hxy (Additive.ofMul h)
    exact congrArg Additive.toMul hh

  let alphaQ : W₁ →* MulAut Q :=
    pTypeQuotientMulAutHom D.C D.W₁_action_U D.C_invariant
  let tau : Representation (ZMod D.p) W₁ (Additive Hbar) :=
    elementaryAbelianActionRepresentation Hbar W₁ D.p D.W₁_action
  have hcompatQ (w : W₁) (x : Q) (v : Additive Hbar) :
      (tau w).toFun ((rho x).toFun v) =
        (rho (alphaQ w x)).toFun ((tau w).toFun v) := by
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective D.C x
    change Additive.ofMul
        (D.W₁_action w (D.U_action u v.toMul)) =
      Additive.ofMul
        (D.U_action (D.W₁_action_U w u)
          (D.W₁_action w v.toMul))
    exact congrArg Additive.ofMul
      (D.action_compatibility u w v.toMul).symm

  letI pTypeSubmoduleLE :
      LE (Submodule (ZMod D.p) (Additive Hbar)) :=
    ⟨fun S T ↦ ∀ ⦃x⦄, S.carrier x → T.carrier x⟩
  letI pTypeSubmoduleBot :
      Bot (Submodule (ZMod D.p) (Additive Hbar)) :=
    Submodule.instBot
  letI pTypeSubmoduleTop :
      Top (Submodule (ZMod D.p) (Additive Hbar)) :=
    Submodule.instTop
  letI : OrderBot (Submodule (ZMod D.p) (Additive Hbar)) :=
    Submodule.instOrderBot
  letI : OrderTop (Submodule (ZMod D.p) (Additive Hbar)) :=
    Submodule.instOrderTop
  letI pTypeSubrepLE : LE (Subrepresentation rho) :=
    ⟨fun S T ↦ ∀ ⦃x⦄,
      S.toSubmodule.carrier x → T.toSubmodule.carrier x⟩
  letI pTypeSubrepBounded : BoundedOrder (Subrepresentation rho) :=
    Subrepresentation.instBoundedOrder
  letI : Bot (Subrepresentation rho) :=
    pTypeSubrepBounded.toOrderBot.toBot
  letI : Top (Subrepresentation rho) :=
    pTypeSubrepBounded.toOrderTop.toTop
  have hirr : Representation.IsIrreducible rho := by
    refine @IsSimpleOrder.mk (Subrepresentation rho)
      pTypeSubrepLE pTypeSubrepBounded ?_ ?_
    · refine ⟨(⊥ : Subrepresentation rho),
        (⊤ : Subrepresentation rho), fun h ↦ ?_⟩
      have h' := congrArg Subrepresentation.toSubmodule h
      change pTypeSubmoduleBot.bot =
        pTypeSubmoduleTop.top at h'
      obtain ⟨g, hg⟩ := exists_ne (1 : Hbar)
      have htop :
          pTypeSubmoduleTop.top.carrier (Additive.ofMul g) :=
        True.intro
      have hbot :
          pTypeSubmoduleBot.bot.carrier (Additive.ofMul g) := by
        rw [h']
        exact htop
      change Additive.ofMul g = 0 at hbot
      exact hg (by simpa using congrArg Additive.toMul hbot)
    · intro S
      let eSub :=
        elementaryAbelianGroupSubmoduleSubgroupOrderIso Hbar D.p
      let L : Subgroup Hbar := eSub S.toSubmodule
      have hLinv : IsInvariantSubgroup D.U_action L := by
        intro x
        apply le_antisymm
        · rintro _ ⟨h, hh, rfl⟩
          have hhS : S.toSubmodule.carrier (Additive.ofMul h) := by
            change L.carrier h at hh
            dsimp [L, eSub,
              elementaryAbelianGroupSubmoduleSubgroupOrderIso] at hh
            exact hh
          have hmem :
              S.toSubmodule.carrier
                (Additive.ofMul (D.U_action x h)) := by
            change S.toSubmodule.carrier
              ((rho (QuotientGroup.mk' D.C x)).toFun
                (Additive.ofMul h))
            exact S.apply_mem_toSubmodule _ hhS
          change L.carrier (D.U_action x h)
          dsimp [L, eSub,
            elementaryAbelianGroupSubmoduleSubgroupOrderIso]
          exact hmem
        · intro h hh
          refine ⟨D.U_action x⁻¹ h, ?_, by simp⟩
          have hhS : S.toSubmodule.carrier (Additive.ofMul h) := by
            change L.carrier h at hh
            dsimp [L, eSub,
              elementaryAbelianGroupSubmoduleSubgroupOrderIso] at hh
            exact hh
          have hmem :
              S.toSubmodule.carrier
                (Additive.ofMul (D.U_action x⁻¹ h)) := by
            change S.toSubmodule.carrier
              ((rho (QuotientGroup.mk' D.C x⁻¹)).toFun
                (Additive.ofMul h))
            exact S.apply_mem_toSubmodule _ hhS
          change L.carrier (D.U_action x⁻¹ h)
          dsimp [L, eSub,
            elementaryAbelianGroupSubmoduleSubgroupOrderIso]
          exact hmem
      rcases is_Galois.2 L hLinv with hL | hL
      · left
        apply Subrepresentation.toSubmodule_injective
        change S.toSubmodule = pTypeSubmoduleBot.bot
        apply Submodule.ext
        intro v
        change S.toSubmodule.carrier v ↔
          pTypeSubmoduleBot.bot.carrier v
        constructor
        · intro hv
          have hv' :
              S.toSubmodule.carrier (Additive.ofMul v.toMul) := by
            simpa using hv
          have hgL : L.carrier v.toMul := by
            dsimp [L, eSub,
              elementaryAbelianGroupSubmoduleSubgroupOrderIso]
            exact hv'
          rw [hL] at hgL
          change v = 0
          apply Additive.ext
          simpa using Subgroup.mem_bot.mp hgL
        · intro hv
          change v = 0 at hv
          subst v
          exact S.toSubmodule.zero_mem
      · right
        apply Subrepresentation.toSubmodule_injective
        change S.toSubmodule = pTypeSubmoduleTop.top
        apply Submodule.ext
        intro v
        change S.toSubmodule.carrier v ↔
          pTypeSubmoduleTop.top.carrier v
        constructor
        · intro _
          exact True.intro
        · intro _
          have hgL : L.carrier v.toMul := by
            rw [hL]
            exact True.intro
          dsimp [L, eSub,
            elementaryAbelianGroupSubmoduleSubgroupOrderIso] at hgL
          change S.toSubmodule.carrier
            (Additive.ofMul v.toMul) at hgL
          simpa using hgL
  letI : Representation.IsIrreducible rho := hirr

  letI pTypeRhoAddCommGroup : AddCommGroup rho.asModule :=
    rho.instAddCommGroupAsModule
  letI pTypeRhoAddCommMonoid : AddCommMonoid rho.asModule :=
    rho.instAddCommMonoidAsModule
  letI pTypeRhoAdd : Add rho.asModule := pTypeRhoAddCommMonoid.toAdd
  letI pTypeRhoZero :=
    pTypeRhoAddCommMonoid.toAddMonoid.toAddZeroClass.toAddZero.toZero
  letI pTypeRhoBaseModule := rho.instModuleAsModule
  letI pTypeRhoAsModule := rho.instModuleMonoidAlgebraAsModule
  letI pTypeRhoScalarTower :=
    rho.instIsScalarTowerMonoidAlgebraAsModule
  letI pTypeRhoSMulComm :=
    @IsScalarTower.to_smulCommClass' (ZMod D.p) (inferInstance)
      (MonoidAlgebra (ZMod D.p) Q) (inferInstance) (inferInstance)
      rho.asModule pTypeRhoAddCommMonoid pTypeRhoAsModule
      pTypeRhoBaseModule pTypeRhoScalarTower
  let F := @Module.End (MonoidAlgebra (ZMod D.p) Q) rho.asModule
    (inferInstance) pTypeRhoAddCommMonoid pTypeRhoAsModule
  letI pTypeFField : Field F := finiteSchurField rho
  letI pTypeFSemiring : Semiring F := @Module.End.instSemiring
    (MonoidAlgebra (ZMod D.p) Q) rho.asModule
    (inferInstance) pTypeRhoAddCommMonoid pTypeRhoAsModule
  letI pTypeFAddCommMonoid : AddCommMonoid F :=
    pTypeFSemiring.toAddCommMonoid
  letI pTypeFSelfModule :
      @Module F F pTypeFSemiring pTypeFAddCommMonoid :=
    @Semiring.toModule F pTypeFSemiring
  letI pTypeFAlgebra := @Module.End.instAlgebra (ZMod D.p)
    (MonoidAlgebra (ZMod D.p) Q) rho.asModule
    (inferInstance) (inferInstance) pTypeRhoAddCommMonoid
    pTypeRhoBaseModule pTypeRhoAsModule
    pTypeRhoSMulComm (inferInstance) pTypeRhoScalarTower
  letI pTypeFModule :
      @Module F rho.asModule (inferInstance) pTypeRhoAddCommMonoid :=
    @Module.End.applyModule
      (MonoidAlgebra (ZMod D.p) Q) rho.asModule
      (inferInstance) pTypeRhoAddCommMonoid pTypeRhoAsModule
  letI pTypeFSmul : SMul F rho.asModule := pTypeFModule.toSMul
  letI pTypeRhoFinite : Finite rho.asModule :=
    inferInstanceAs (Finite (Additive Hbar))
  letI : Finite (rho.asModule → rho.asModule) := by infer_instance
  letI : Finite F :=
    Finite.of_injective
      (fun f : F ↦ (f : rho.asModule → rho.asModule))
      (fun _ _ h ↦ DFunLike.coe_injective h)
  letI : Fintype F := Fintype.ofFinite F
  letI pTypeFBaseModule := @Algebra.toModule (ZMod D.p) F
    (inferInstance) (inferInstance) pTypeFAlgebra
  letI pTypeFFiniteDimensional := @Module.Finite.of_finite
    (ZMod D.p) F (inferInstance) (inferInstance) pTypeFBaseModule
    (inferInstance)
  letI pTypeFIsAlgebraic : Algebra.IsAlgebraic (ZMod D.p) F :=
    Algebra.IsAlgebraic.of_finite (ZMod D.p) F
  let rhoF := schurScalarRepresentation rho
  letI pTypeRhoFIrreducible :=
    schurScalarRepresentation_isIrreducible rho

  have hW₂card : 1 < Nat.card D.W₂bar := by
    rw [D.card_W₂bar]
    exact D.p_prime.one_lt
  letI : Nontrivial D.W₂bar :=
    Finite.one_lt_card_iff_nontrivial.mp hW₂card
  have hs₂_nonempty : Nonempty {x : D.W₂bar // x ≠ 1} := by
    rcases exists_ne (1 : D.W₂bar) with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  let s₂w : {x : D.W₂bar // x ≠ 1} :=
    Classical.choice hs₂_nonempty
  let s₂ : D.W₂bar := s₂w.1
  have hs₂ : s₂ ≠ 1 := s₂w.2
  let s : rho.asModule := Additive.ofMul (s₂ : Hbar)
  have hs : s ≠ 0 := by
    intro hs0
    apply hs₂
    apply Subtype.ext
    exact congrArg Additive.toMul hs0
  have hs_fixed (w : W₁) :
      (tau w).toFun s = s := by
    change Additive.ofMul (D.W₁_action w (s₂ : Hbar)) =
      Additive.ofMul (s₂ : Hbar)
    exact congrArg Additive.ofMul
      ((D.W₂bar_fixed (s₂ : Hbar)).mp s₂.property w)

  let spanS :
      @Submodule F rho.asModule (inferInstance)
        pTypeRhoAddCommMonoid pTypeFModule :=
    @Submodule.span F rho.asModule (inferInstance)
      pTypeRhoAddCommMonoid pTypeFModule {s}
  have hspan : spanS = ⊤ := by
    let S : @Subrepresentation F Q rho.asModule
        (inferInstance) (inferInstance) pTypeRhoAddCommMonoid
        pTypeFModule rhoF :=
      @Subrepresentation.mk F Q rho.asModule
        (inferInstance) (inferInstance) pTypeRhoAddCommMonoid
        pTypeFModule rhoF spanS (by
          intro x v hv
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
          let z : Subgroup.center Q :=
            ⟨x, by
              rw [Subgroup.mem_center_iff]
              intro y
              exact (mul_comm' x y).symm⟩
          let d : F := centralActionEnd rho z
          have hd : (rhoF x).toFun s = d.toFun s := by
            apply rhoCarrier_injective
            have hrhoF := schurScalarRepresentation_apply rho x s
            change rhoCarrier ((rhoF x).toFun s) =
              (rho x).toFun (rhoCarrier s) at hrhoF
            have hd' := (centralActionEnd_apply rho z s).symm
            change (rho x).toFun (rhoCarrier s) =
              rhoCarrier (d.toFun s) at hd'
            exact hrhoF.trans hd'
          apply Submodule.mem_span_singleton.mpr
          refine ⟨a * d, ?_⟩
          calc
            (a * d) • s = a • (d • s) := mul_smul a d s
            _ = a • (rhoF x).toFun s :=
              congrArg (fun t : rho.asModule ↦ a • t) hd.symm
            _ = (rhoF x).toFun (a • s) :=
              (map_smul (rhoF x) a s).symm)
    rcases (eq_bot_or_eq_top S) with hSbot | hStop
    · exfalso
      apply hs
      have hsSpan : s ∈ spanS :=
        @Submodule.mem_span_singleton_self F rho.asModule
          (inferInstance) pTypeRhoAddCommMonoid pTypeFModule s
      have hSbotSub := congrArg
        (@Subrepresentation.toSubmodule F Q rho.asModule
          pTypeFSemiring (inferInstance) pTypeRhoAddCommMonoid
          pTypeFModule rhoF) hSbot
      change spanS = (⊥ : @Submodule F rho.asModule pTypeFSemiring
        pTypeRhoAddCommMonoid pTypeFModule) at hSbotSub
      rw [hSbotSub] at hsSpan
      exact (@Submodule.mem_bot F rho.asModule (inferInstance)
        pTypeRhoAddCommMonoid pTypeFModule s).mp hsSpan
    · exact congrArg
        (@Subrepresentation.toSubmodule F Q rho.asModule
          pTypeFSemiring (inferInstance) pTypeRhoAddCommMonoid
          pTypeFModule rhoF) hStop

  let scale : @LinearMap F F pTypeFSemiring pTypeFSemiring
      (@RingHom.id F pTypeFSemiring.toNonAssocSemiring) F rho.asModule
      pTypeFAddCommMonoid pTypeRhoAddCommMonoid
      pTypeFSelfModule pTypeFModule :=
    @LinearMap.mk F F pTypeFSemiring pTypeFSemiring
      (@RingHom.id F pTypeFSemiring.toNonAssocSemiring) F rho.asModule
      pTypeFAddCommMonoid pTypeRhoAddCommMonoid
      pTypeFSelfModule pTypeFModule
      (@AddHom.mk F rho.asModule pTypeFAddCommMonoid.toAdd
        pTypeRhoAddCommMonoid.toAdd
        (fun a ↦ pTypeFModule.smul a s)
        (fun a b ↦ pTypeFModule.add_smul a b s))
      (fun a b ↦ pTypeFModule.mul_smul a b s)
  have hscaleInjective : Function.Injective scale := by
    letI : Module F (Additive Hbar) := pTypeFModule
    intro a b hab
    have hs' : (s : Additive Hbar) ≠ 0 := hs
    change a • (s : Additive Hbar) = b • (s : Additive Hbar) at hab
    exact (smul_left_injective (M := Additive Hbar) F
      (m := (s : Additive Hbar)) hs') hab
  have hscaleSurjective : Function.Surjective scale := by
    intro v
    have hv : v ∈ spanS := by
      rw [hspan]
      exact True.intro
    rcases (@Submodule.mem_span_singleton F rho.asModule
      pTypeFSemiring pTypeRhoAddCommMonoid pTypeFModule v s).mp hv with
      ⟨a, ha⟩
    exact ⟨a, ha⟩
  let eval :=
    @LinearEquiv.ofBijective
      F F F rho.asModule
      pTypeFSemiring pTypeFSemiring
      pTypeFAddCommMonoid pTypeRhoAddCommMonoid
      pTypeFSelfModule pTypeFModule
      (@RingHom.id F pTypeFSemiring.toNonAssocSemiring)
      (@RingHom.id F pTypeFSemiring.toNonAssocSemiring)
      scale (inferInstance) (inferInstance)
      ⟨hscaleInjective, hscaleSurjective⟩
  let evalMap : @LinearMap F F pTypeFSemiring pTypeFSemiring
      (@RingHom.id F pTypeFSemiring.toNonAssocSemiring) F rho.asModule
      pTypeFAddCommMonoid pTypeRhoAddCommMonoid
      pTypeFSelfModule pTypeFModule :=
    @LinearEquiv.toLinearMap F F pTypeFSemiring pTypeFSemiring
      (@RingHom.id F pTypeFSemiring.toNonAssocSemiring)
      (@RingHom.id F pTypeFSemiring.toNonAssocSemiring)
      (inferInstance) (inferInstance) F rho.asModule
      pTypeFAddCommMonoid pTypeRhoAddCommMonoid
      pTypeFSelfModule pTypeFModule eval
  have eval_apply (a : F) : evalMap.toFun a = a • s := by
    change scale.toFun a = a • s
    rfl
  let evalAddEquiv : @AddEquiv F rho.asModule
      pTypeFAddCommMonoid.toAdd pTypeRhoAdd :=
    @LinearEquiv.toAddEquiv F F pTypeFSemiring pTypeFSemiring
      (@RingHom.id F pTypeFSemiring.toNonAssocSemiring)
      (@RingHom.id F pTypeFSemiring.toNonAssocSemiring)
      (inferInstance) (inferInstance) F rho.asModule
      pTypeFAddCommMonoid pTypeRhoAddCommMonoid
      pTypeFSelfModule pTypeFModule eval
  let rhoAddEquiv : @AddEquiv (Additive Hbar) rho.asModule
      (inferInstance) pTypeRhoAdd :=
    { toFun := fun v ↦ v
      invFun := fun v ↦ v
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let phi : Additive Hbar ≃+ F :=
    rhoAddEquiv.trans evalAddEquiv.symm

  let toCenter : Q →* Subgroup.center Q :=
    { toFun := fun x ↦ ⟨x, by
          rw [Subgroup.mem_center_iff]
          intro y
          exact (mul_comm' x y).symm⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have htoCenter : Function.Injective toCenter := by
    intro x y hxy
    exact congrArg Subtype.val hxy
  let psiQ : Q →* Fˣ :=
    (schurCenterCharacter rho).comp toCenter
  have hpsiQ : Function.Injective psiQ :=
    (schurCenterCharacter_injective_of_injective rho hrho).comp htoCenter
  let psi : U →* Fˣ := psiQ.comp (QuotientGroup.mk' D.C)
  have hpsiKernel : psi.ker = D.C := by
    dsimp [psi]
    rw [MonoidHom.ker_comp_of_injective
      (QuotientGroup.mk' D.C) psiQ hpsiQ,
      QuotientGroup.ker_mk']
  have hrho_scalar (x : Q) (v : rho.asModule) :
      (rho x).toFun v =
        (((schurCenterCharacter rho) (toCenter x) : F)).toFun v := by
    apply rhoCarrier_injective
    have h := (schurCenterCharacter_val_apply rho (toCenter x) v).symm
    change (rho x).toFun (rhoCarrier v) =
      rhoCarrier
        ((((schurCenterCharacter rho) (toCenter x) : F)).toFun v) at h
    exact h
  have hphiU (h : Hbar) (x : U) :
      phi (Additive.ofMul (D.U_action x h)) =
        phi (Additive.ofMul h) * (psi x : F) := by
    let v : rho.asModule := Additive.ofMul h
    change evalAddEquiv.symm.toFun
        ((rho (QuotientGroup.mk' D.C x)).toFun v) =
      evalAddEquiv.symm.toFun v *
        (psiQ (QuotientGroup.mk' D.C x) : F)
    have hscalar :
        (rho (QuotientGroup.mk' D.C x)).toFun v =
          ((psiQ (QuotientGroup.mk' D.C x) : F)).toFun v := by
      simpa only [psiQ, MonoidHom.comp_apply] using
        hrho_scalar (QuotientGroup.mk' D.C x) v
    have hscalarExact :
        (show rho.asModule from
          (rho (QuotientGroup.mk' D.C x)).toFun v) =
          pTypeFModule.smul
            (psiQ (QuotientGroup.mk' D.C x) : F) v := by
      exact hscalar
    apply evalAddEquiv.injective
    calc
      evalMap.toFun (evalAddEquiv.symm.toFun
          ((rho (QuotientGroup.mk' D.C x)).toFun v)) =
          pTypeFModule.smul
            (psiQ (QuotientGroup.mk' D.C x) : F) v :=
        (evalAddEquiv.apply_symm_apply _).trans hscalarExact
      _ = pTypeFModule.smul
          (psiQ (QuotientGroup.mk' D.C x) : F)
          (evalMap.toFun
            (evalAddEquiv.symm.toFun v)) :=
        congrArg
          (pTypeFModule.smul
            (psiQ (QuotientGroup.mk' D.C x) : F))
          (evalAddEquiv.apply_symm_apply v).symm
      _ = evalMap.toFun
          ((psiQ (QuotientGroup.mk' D.C x) : F) •
            evalAddEquiv.symm.toFun v) := by
        change pTypeFModule.smul
            (psiQ (QuotientGroup.mk' D.C x) : F)
              (evalMap.toFun (evalAddEquiv.symm.toFun v)) =
          evalMap.toFun (pTypeFSelfModule.smul
            (psiQ (QuotientGroup.mk' D.C x) : F)
              (evalAddEquiv.symm.toFun v))
        rw [eval_apply, eval_apply]
        change pTypeFModule.smul
            (psiQ (QuotientGroup.mk' D.C x) : F)
              (pTypeFModule.smul (evalAddEquiv.symm.toFun v) s) =
          pTypeFModule.smul
            ((psiQ (QuotientGroup.mk' D.C x) : F) *
              evalAddEquiv.symm.toFun v) s
        exact (pTypeFModule.mul_smul
          (psiQ (QuotientGroup.mk' D.C x) : F)
            (evalAddEquiv.symm.toFun v) s).symm
      _ = evalMap.toFun (evalAddEquiv.symm.toFun v *
          (psiQ (QuotientGroup.mk' D.C x) : F)) := by
        rw [smul_eq_mul, mul_comm]

  letI pTypeISemiring :
      Semiring (Representation.IntertwiningMap rho rho) :=
    Representation.IntertwiningMap.instSemiring rho
  letI pTypeIAlgebra :
      @Algebra (ZMod D.p) (Representation.IntertwiningMap rho rho)
        (inferInstance) pTypeISemiring :=
    Representation.IntertwiningMap.instAlgebra rho
  let I := Representation.IntertwiningMap rho rho
  let eI :=
    Representation.IntertwiningMap.equivAlgEnd rho
  let conjI :=
    intertwiningConjugationAlgEquivHom rho tau alphaQ hcompatQ
  let etaAlg :=
    (@AlgEquiv.autCongr (ZMod D.p)
      (Representation.IntertwiningMap rho rho) F
      (inferInstance) pTypeISemiring pTypeFSemiring
      pTypeIAlgebra pTypeFAlgebra eI).toMonoidHom.comp conjI
  let eta : W₁ →* Equiv.Perm F :=
    { toFun := fun w ↦ (etaAlg w).toEquiv
      map_one' := by
        ext a
        simp
      map_mul' := by
        intro w z
        ext a
        simp }
  have heta_end_apply (w : W₁) (a : F) (v : rho.asModule) :
      rhoAddEquiv.symm ((etaAlg w a).toFun v) =
        (tau w).toFun (rhoAddEquiv.symm
          (a.toFun (rhoAddEquiv
            ((tau w⁻¹).toFun
              (rhoAddEquiv.symm v))))) := by
    rfl
  have hphiW (h : Hbar) (w : W₁) :
      phi (Additive.ofMul (D.W₁_action w h)) =
        eta w (phi (Additive.ofMul h)) := by
    let v : rho.asModule := Additive.ofMul h
    let a : F := evalAddEquiv.symm.toFun v
    change evalAddEquiv.symm.toFun
        (rhoAddEquiv ((tau w).toFun (rhoAddEquiv.symm v))) =
      (etaAlg w).toFun a
    apply evalAddEquiv.injective
    have hround :
        evalAddEquiv.toFun
            (evalAddEquiv.symm.toFun
              (rhoAddEquiv
                ((tau w).toFun (rhoAddEquiv.symm v)))) =
          rhoAddEquiv
            ((tau w).toFun (rhoAddEquiv.symm v)) :=
      evalAddEquiv.apply_symm_apply _
    have hmain :
        rhoAddEquiv
            ((tau w).toFun (rhoAddEquiv.symm v)) =
          evalAddEquiv.toFun ((etaAlg w).toFun a) := by
      change rhoAddEquiv
          ((tau w).toFun (rhoAddEquiv.symm v)) =
        evalMap.toFun ((etaAlg w).toFun a)
      rw [eval_apply]
      change rhoAddEquiv
          ((tau w).toFun (rhoAddEquiv.symm v)) =
        ((etaAlg w).toFun a).toFun s
      apply rhoAddEquiv.symm.injective
      rw [rhoAddEquiv.symm_apply_apply]
      have hetaS := heta_end_apply w a s
      have hfixInv :
          (tau w⁻¹).toFun (rhoAddEquiv.symm s) =
            rhoAddEquiv.symm s := by
        change (tau w⁻¹).toFun s = s
        exact hs_fixed w⁻¹
      have haS : a.toFun s = v := by
        change pTypeFModule.smul a s = v
        calc
          pTypeFModule.smul a s = evalMap.toFun a :=
            (eval_apply a).symm
          _ = v := by
            change evalAddEquiv.toFun
              (evalAddEquiv.symm.toFun v) = v
            exact evalAddEquiv.apply_symm_apply v
      calc
        (tau w).toFun (rhoAddEquiv.symm v) =
            (tau w).toFun (rhoAddEquiv.symm
              (a.toFun (rhoAddEquiv
                ((tau w⁻¹).toFun
                  (rhoAddEquiv.symm s))))) := by
          rw [hfixInv, rhoAddEquiv.apply_symm_apply, haS]
        _ = rhoAddEquiv.symm ((etaAlg w a).toFun s) :=
          hetaS.symm
    exact hround.trans hmain
  have hpsiW (x : U) (w : W₁) :
      (psi (D.W₁_action_U w x) : F) =
        eta w (psi x : F) := by
    have hcompat := D.action_compatibility x w (s₂ : Hbar)
    have hs₂w : D.W₁_action w (s₂ : Hbar) = (s₂ : Hbar) :=
      (D.W₂bar_fixed (s₂ : Hbar)).mp s₂.property w
    have hphiS : phi (Additive.ofMul (s₂ : Hbar)) = 1 := by
      change evalAddEquiv.symm.toFun s = 1
      apply evalAddEquiv.injective
      calc
        evalMap.toFun (evalAddEquiv.symm.toFun s) = s :=
          evalAddEquiv.apply_symm_apply s
        _ = evalMap.toFun 1 := by rw [eval_apply, one_smul]
    have h := congrArg (fun z : Hbar ↦ phi (Additive.ofMul z)) hcompat
    rw [hphiU, hs₂w, hphiS, one_mul] at h
    rw [hphiW, hphiU] at h
    simpa [eta, map_mul, hphiS] using h

  have heta_eq_one (w : W₁) (hweta : eta w = 1) : w = 1 := by
    by_contra hw
    have heta_all (z : W₁) : eta z = 1 := by
      have hz : z ∈ Subgroup.zpowers w := by
        rw [zpowers_eq_top_of_prime_card D.card_W₁ hw]
        exact Subgroup.mem_top z
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [map_zpow, hweta, one_zpow]
    have haction_all (z : W₁) : D.W₁_action z = 1 := by
      apply MulEquiv.ext
      intro h
      apply Additive.ofMul.injective
      apply phi.injective
      have hh := hphiW h z
      rw [heta_all z] at hh
      simpa using hh
    have hW₂top : D.W₂bar = ⊤ := by
      apply top_unique
      intro h _
      rw [D.W₂bar_fixed]
      intro z
      rw [haction_all z]
      rfl
    have hcardEq : D.p = D.p ^ D.q := by
      calc
        D.p = Nat.card D.W₂bar := D.card_W₂bar.symm
        _ = Nat.card Hbar := by rw [hW₂top]; simp
        _ = D.p ^ D.q := D.card_Hbar
    have hexp : 1 = D.q := by
      apply Nat.pow_right_injective D.p_prime.two_le
      simpa using hcardEq
    exact D.q_prime.ne_one hexp.symm
  have hetaInjective : Function.Injective eta := by
    intro w z hwz
    have hquot : eta (w * z⁻¹) = 1 := by
      rw [map_mul, map_inv, hwz, mul_inv_cancel]
    exact eq_of_mul_inv_eq_one (heta_eq_one (w * z⁻¹) hquot)
  have hetaAlgInjective : Function.Injective etaAlg := by
    intro w z hwz
    apply hetaInjective
    ext a
    exact DFunLike.congr_fun hwz a

  have hfieldCard : Nat.card F = D.p ^ D.q := by
    calc
      Nat.card F = Nat.card Hbar := (Nat.card_congr phi.toEquiv).symm
      _ = D.p ^ D.q := D.card_Hbar
  have hfinrank : Module.finrank (ZMod D.p) F = D.q := by
    apply Nat.pow_right_injective D.p_prime.two_le
    calc
      D.p ^ Module.finrank (ZMod D.p) F = Nat.card F :=
        FiniteField.pow_finrank_eq_natCard D.p F
      _ = D.p ^ D.q := hfieldCard
  have hetaAlgSurjective : Function.Surjective etaAlg := by
    letI pTypeFAutFinite :
        Finite (@AlgEquiv (ZMod D.p) F F (inferInstance)
          pTypeFSemiring pTypeFSemiring
          pTypeFAlgebra pTypeFAlgebra) :=
      Finite.of_injective (fun e ↦ (e : F → F))
        (fun _ _ h ↦ DFunLike.coe_injective h)
    have hcardAut :
        Nat.card W₁ = Nat.card (F ≃ₐ[ZMod D.p] F) := by
      calc
        Nat.card W₁ = D.q := D.card_W₁
        _ = Module.finrank (ZMod D.p) F := hfinrank.symm
        _ = Nat.card (F ≃ₐ[ZMod D.p] F) :=
          (IsGalois.card_aut_eq_finrank (ZMod D.p) F).symm
    exact ((Nat.bijective_iff_injective_and_card etaAlg).mpr
      ⟨hetaAlgInjective, hcardAut⟩).surjective
  have hfieldAutExact (alpha : Equiv.Perm F) :
      (IsAdditivePermutation alpha ∧
          IsMultiplicativePermutation alpha) ↔
        alpha ∈ Set.range (fun w : W₁ ↦ eta w) := by
    constructor
    · rintro ⟨hadd, hmul⟩
      let alphaRing : F ≃+* F :=
        { toEquiv := alpha
          map_add' := hadd.2
          map_mul' := hmul.2 }
      let alphaAlg : F ≃ₐ[ZMod D.p] F :=
        AlgEquiv.ofRingEquiv (f := alphaRing) (by
          intro c
          rw [← ZMod.natCast_zmod_val c, map_natCast, map_natCast])
      obtain ⟨w, hw⟩ := hetaAlgSurjective alphaAlg
      refine ⟨w, ?_⟩
      ext a
      exact DFunLike.congr_fun hw a
    · rintro ⟨w, rfl⟩
      constructor
      · exact ⟨map_zero (etaAlg w), map_add (etaAlg w)⟩
      · exact ⟨map_one (etaAlg w), map_mul (etaAlg w)⟩

  let primeLineComap : AddSubgroup (Additive Hbar) :=
    (primeAdditiveLine F).comap phi.toAddMonoidHom
  have hprimeLine_le : primeLineComap ≤ D.W₂bar.toAddSubgroup := by
    intro h hh
    change h.toMul ∈ D.W₂bar
    rw [D.W₂bar_fixed]
    intro w
    apply Additive.ofMul.injective
    apply phi.injective
    have hline : phi h ∈ primeAdditiveLine F := hh
    rcases AddSubgroup.mem_zmultiples_iff.mp hline with ⟨n, hn⟩
    have hfix : eta w (phi h) = phi h := by
      rw [← hn]
      change (etaAlg w).toFun (n : F) = (n : F)
      exact map_intCast (etaAlg w) n
    simpa [hfix] using hphiW h.toMul w
  have hchar : CharP F D.p := by
    rw [← Algebra.charP_iff (ZMod D.p) F D.p]
    exact ZMod.charP D.p
  have hprimeLineCard : Nat.card (primeAdditiveLine F) = D.p := by
    calc
      Nat.card (primeAdditiveLine F) =
          Nat.card (AddSubgroup.zmultiples (1 : F)) := rfl
      _ = addOrderOf (1 : F) := Nat.card_zmultiples (1 : F)
      _ = D.p := CharP.eq F (CharP.addOrderOf_one F) hchar
  have hprimeComapCard : Nat.card primeLineComap = D.p := by
    have hmap :
        (primeAdditiveLine F).map phi.symm.toAddMonoidHom =
          primeLineComap := by
      simpa [primeLineComap] using
        (AddSubgroup.map_equiv_eq_comap_symm'
          phi.symm (primeAdditiveLine F))
    calc
      Nat.card primeLineComap =
          Nat.card ((primeAdditiveLine F).map
            phi.symm.toAddMonoidHom) := by rw [hmap]
      _ = Nat.card (primeAdditiveLine F) :=
        (Nat.card_congr
          (phi.symm.addSubgroupMap (primeAdditiveLine F)).toEquiv).symm
      _ = D.p := hprimeLineCard
  have hprimeLineEq :
      (primeAdditiveLine F).comap phi.toAddMonoidHom =
        D.W₂bar.toAddSubgroup := by
    apply AddSubgroup.eq_of_le_of_card_ge hprimeLine_le
    have hW₂addCard : Nat.card D.W₂bar.toAddSubgroup = D.p := by
      calc
        Nat.card D.W₂bar.toAddSubgroup = Nat.card D.W₂bar :=
          Nat.card_congr
            { toFun := fun x ↦ ⟨x.1.toMul, x.2⟩
              invFun := fun x ↦ ⟨Additive.ofMul x.1, x.2⟩
              left_inv := fun x ↦ by ext; rfl
              right_inv := fun x ↦ by ext; rfl }
        _ = D.p := D.card_W₂bar
    rw [hW₂addCard, hprimeComapCard]

  let B : Subgroup Fˣ := psiQ.range
  let A : Subgroup Fˣ := primeFieldUnitRange D.p F
  have hcardB : Nat.card B = Nat.card Q :=
    (Nat.card_congr (psiQ.ofInjective hpsiQ).toEquiv).symm
  have hcardA : Nat.card A = D.p - 1 := by
    let f : (ZMod D.p)ˣ →* Fˣ :=
      Units.map (algebraMap (ZMod D.p) F).toMonoidHom
    have hf : Function.Injective f :=
      Units.map_injective (algebraMap (ZMod D.p) F).injective
    calc
      Nat.card A = Nat.card (ZMod D.p)ˣ :=
        (Nat.card_congr (f.ofInjective hf).toEquiv).symm
      _ = D.p - 1 := by rw [Nat.card_units, Nat.card_zmod]
  have hA_fixed (w : W₁) {a : Fˣ} (ha : a ∈ A) :
      Units.map (etaAlg w).toRingEquiv.toMonoidHom a = a := by
    rcases ha with ⟨c, rfl⟩
    apply Units.ext
    exact (etaAlg w).commutes (c : ZMod D.p)
  have hABdisjoint : Disjoint A B := by
    rw [Subgroup.disjoint_def]
    intro b hbA hbB
    rcases hbB with ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective D.C x
    have hWnontrivial : 1 < Nat.card W₁ := by
      rw [D.card_W₁]
      exact D.q_prime.one_lt
    letI : Nontrivial W₁ :=
      Finite.one_lt_card_iff_nontrivial.mp hWnontrivial
    obtain ⟨w, hw⟩ := exists_ne (1 : W₁)
    have hfix := hA_fixed w hbA
    have hpsiEq : psi (D.W₁_action_U w u) = psi u := by
      apply Units.ext
      change (psi (D.W₁_action_U w u) : F) = (psi u : F)
      rw [hpsiW]
      change (etaAlg w).toFun
          (psiQ (QuotientGroup.mk' D.C u) : F) =
        (psiQ (QuotientGroup.mk' D.C u) : F)
      exact congrArg Units.val hfix
    have hdiff : D.W₁_action_U w u * u⁻¹ ∈ D.C := by
      rw [← hpsiKernel, MonoidHom.mem_ker]
      rw [map_mul, map_inv, hpsiEq, mul_inv_cancel]
    have huC : u ∈ D.C := hD.fixed_coset_trivial w hw u hdiff
    apply Units.ext
    have hpsiOne : psi u = 1 := by
      have huKer : u ∈ psi.ker := by
        rw [hpsiKernel]
        exact huC
      exact MonoidHom.mem_ker.mp huKer
    exact congrArg Units.val hpsiOne

  let mulAB : A × B →* Fˣ :=
    { toFun := fun z ↦ (z.1 : Fˣ) * (z.2 : Fˣ)
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        ac_rfl }
  have hmulAB : Function.Injective mulAB :=
    Subgroup.mul_injective_of_disjoint hABdisjoint
  letI : IsCyclic (A × B) :=
    isCyclic_of_injective mulAB hmulAB
  have hcopAB : Nat.Coprime (Nat.card A) (Nat.card B) :=
    coprime_card_of_isCyclic_prod A B
  have hcopQ : Nat.Coprime (Nat.card Q) (D.p - 1) := by
    rw [← hcardB, ← hcardA]
    exact hcopAB.symm
  have hprodDvd : Nat.card A * Nat.card B ∣ Nat.card Fˣ := by
    calc
      Nat.card A * Nat.card B = Nat.card (A × B) :=
        (Nat.card_prod A B).symm
      _ = Nat.card mulAB.range :=
        Nat.card_congr (mulAB.ofInjective hmulAB).toEquiv
      _ ∣ Nat.card Fˣ := mulAB.range.card_subgroup_dvd_card
  have hQdvdNU : Nat.card Q ∣ nU D.p D.q := by
    apply (Nat.mul_dvd_mul_iff_left
      (Nat.sub_pos_of_lt D.p_prime.one_lt)).mp
    calc
      (D.p - 1) * Nat.card Q = Nat.card A * Nat.card B := by
        rw [hcardA, hcardB]
      _ ∣ Nat.card Fˣ := hprodDvd
      _ = D.p ^ D.q - 1 := by
        rw [Nat.card_units, hfieldCard]
      _ = (D.p - 1) * nU D.p D.q := by
        rw [mul_comm, nU_mul_sub_one D.p D.q D.p_prime.one_lt.le]
  have hcyclicQ : IsCyclic Q :=
    isCyclic_of_injective psiQ hpsiQ

  refine
    { F := F
      phi := phi
      psi := psi
      eta := eta
      field_automorphisms_exact := hfieldAutExact
      eta_injective := hetaInjective
      phi_W₁_compatible := hphiW
      psi_W₁_compatible := hpsiW
      psi_kernel := hpsiKernel
      phi_U_compatible := hphiU
      field_card := hfieldCard
      primeLine_comap := hprimeLineEq
      complement_factor_cyclic := hcyclicQ
      complement_factor_coprime := hcopQ
      complement_factor_dvd := by
        rw [← nU_eq_div_of_prime D.p_prime]
        exact hQdvdNU }

end

end Submission.OddOrder.PF
