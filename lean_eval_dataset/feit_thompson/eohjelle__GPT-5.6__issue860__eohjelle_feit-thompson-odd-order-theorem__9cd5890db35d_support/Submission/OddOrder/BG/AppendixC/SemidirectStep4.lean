import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Submission.OddOrder.BG.AppendixC.SemidirectNormCounting
import Submission.OddOrder.BG.AppendixC.SemidirectTripleFactorization
import Submission.OddOrder.MathlibSupport.InternalSemidirectProjection

/-!
# The Step-4 word calculation in Bender--Glauberman Appendix C

This file ports `BGappendixC.v`, lines 569--749.  The private lemmas below
build the source word calculation toward a public discharge of
`BGappendixC3Step4Obligation`: stability of the pullback of the two-norm
equation set under `a ↦ (a⁻¹) ^ t³`.
-/

namespace Submission.OddOrder.BG.AppendixC

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative commutatorElement

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Source-style right conjugation, `x ^ g = g⁻¹ x g`. -/
private def step4Conj (x g : G) : G :=
  g⁻¹ * x * g

@[simp]
private theorem step4Conj_one_right (x : G) :
    step4Conj x 1 = x := by
  simp [step4Conj]

private theorem step4Conj_mul_right (x g h : G) :
    step4Conj x (g * h) = step4Conj (step4Conj x g) h := by
  simp [step4Conj, mul_assoc]

private theorem step4Conj_inv (x g : G) :
    (step4Conj x g)⁻¹ = step4Conj x⁻¹ g := by
  simp [step4Conj, mul_assoc]

private theorem step4Conj_mul (x z g : G) :
    step4Conj (x * z) g = step4Conj x g * step4Conj z g := by
  simp [step4Conj, mul_assoc]

/-- The abstract abelian-action identity underlying the source calculation
`Dx`.  Isolating it here lets the Appendix-C proof use the genuine
conjugation action on `[Q,P₀]` without a long ambient word shuffle. -/
private theorem step4_discrepancy_identity
    {A B : Type*} [Group A] [Group B]
    [IsMulCommutative A] [IsMulCommutative B]
    (rho : A →* MulAut B) (s s₁ s₃ : A) (y : B) :
    let d := y⁻¹ * rho s y
    let x := (rho s₃⁻¹ y)⁻¹ * rho s y *
      (rho (s * s₁) y)⁻¹ * y
    d * rho (s * s₃ * s₁) d * (rho s₃ d)⁻¹ *
        (rho (s₃ * s) d)⁻¹ =
      (rho s₃ (rho s x * x⁻¹))⁻¹ := by
  let d := y⁻¹ * rho s y
  let x := (rho s₃⁻¹ y)⁻¹ * rho s y *
    (rho (s * s₁) y)⁻¹ * y
  let A0 := s * s₃ * s₁
  let C0 := s₃ * s
  let canon := y⁻¹ * rho s y * (rho A0 y)⁻¹ *
    rho (A0 * s) y * rho s₃ y * (rho (C0 * s) y)⁻¹
  have act_mul (a : A) (u v : B) :
      rho a (u * v) = rho a u * rho a v :=
    (rho a).map_mul u v
  have act_inv (a : A) (u : B) :
      rho a u⁻¹ = (rho a u)⁻¹ :=
    (rho a).map_inv u
  have act_comp (a b : A) (u : B) :
      rho a (rho b u) = rho (a * b) u := by
    rw [rho.map_mul]
    rfl
  have act_one (u : B) : rho (1 : A) u = u := by
    rw [rho.map_one]
    rfl
  have act_d (a : A) :
      rho a d = (rho a y)⁻¹ * rho (a * s) y := by
    dsimp only [d]
    rw [act_mul, act_inv, act_comp]
  have act_x (a : A) :
      rho a x =
        (rho (a * s₃⁻¹) y)⁻¹ * rho (a * s) y *
          (rho (a * (s * s₁)) y)⁻¹ * rho a y := by
    dsimp only [x]
    simp only [act_mul, act_inv, act_comp]
  have hlhs :
      d * rho A0 d * (rho s₃ d)⁻¹ * (rho C0 d)⁻¹ = canon := by
    rw [act_d A0, act_d s₃, act_d C0]
    dsimp only [d]
    simp only [mul_inv_rev, inv_inv]
    calc
      _ = canon * ((rho C0 y)⁻¹ * rho C0 y) := by
        dsimp only [canon, C0]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      _ = canon := by simp
  have h33 : s₃ * s₃⁻¹ = (1 : A) := by simp
  have h3s : s₃ * s = C0 := rfl
  have h3ss₁ : s₃ * (s * s₁) = A0 := by
    dsimp only [A0]
    ac_rfl
  have hCs₃ : C0 * s₃⁻¹ = s := by
    calc
      C0 * s₃⁻¹ = (s₃ * s₃⁻¹) * s := by
        dsimp only [C0]
        ac_rfl
      _ = s := by simp
  have hCss₁ : C0 * (s * s₁) = A0 * s := by
    dsimp only [C0, A0]
    ac_rfl
  have houter :
      rho s₃ (rho s x * x⁻¹) =
        rho C0 x * (rho s₃ x)⁻¹ := by
    rw [act_mul, act_inv, act_comp]
  have hrhs : (rho s₃ (rho s x * x⁻¹))⁻¹ = canon := by
    rw [houter]
    simp only [mul_inv_rev, inv_inv]
    rw [act_x s₃, act_x C0]
    simp only [mul_inv_rev, inv_inv, h33, h3s, h3ss₁,
      hCs₃, hCss₁, act_one]
    calc
      _ = canon * (rho C0 y * (rho C0 y)⁻¹) := by
        dsimp only [canon]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      _ = canon := by simp
  exact hlhs.trans hrhs.symm

namespace FiniteFieldImage

variable {P P0 U : Subgroup G} (h : FiniteFieldImage P P0 U)

/-- The distinguished element `s = σ⁻¹(1)` generates `P₀`. -/
private theorem zpowers_onePreimage_eq_p0 :
    Subgroup.zpowers (h.onePreimage : G) = P0 := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact P0.zpow_mem h.onePreimage_mem_p0 k
  · intro hx
    let xP : P := ⟨x, h.p0_le hx⟩
    have hxadd : Additive.ofMul xP ∈
        AddSubgroup.zmultiples (Additive.ofMul h.onePreimage) := by
      rw [← h.p0_toAddSubgroup_eq_zmultiples_onePreimage]
      exact hx
    have hximage : Additive.ofMul xP ∈
        Additive.ofMul ''
          (Subgroup.zpowers (h.onePreimage : P) : Set P) := by
      rw [ofMul_image_zpowers_eq_zmultiples_ofMul]
      exact hxadd
    obtain ⟨z, hz, hzx⟩ := hximage
    have hzxP : z = xP := congrArg Additive.toMul hzx
    subst z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    exact congrArg Subtype.val hk

private theorem orderOf_onePreimage
    {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) h.F] :
    orderOf (h.onePreimage : G) = p := by
  calc
    orderOf (h.onePreimage : G) =
        Nat.card (Subgroup.zpowers (h.onePreimage : G)) :=
      (Nat.card_zpowers _).symm
    _ = Nat.card P0 := by rw [h.zpowers_onePreimage_eq_p0]
    _ = p := h.natCard_p0_eq_prime

/-- `U` is abelian because its faithful image lies in the unit group of a
field. -/
private theorem isMulCommutative_U
    (h : FiniteFieldImage P P0 U) : IsMulCommutative U := by
  apply isMulCommutative_iff.mpr
  intro a b
  apply FiniteFieldImage.psi_injective h
  simpa only [map_mul] using mul_comm (h.psi a) (h.psi b)

private theorem isMulCommutative_P
    (h : FiniteFieldImage P P0 U) : IsMulCommutative P := by
  apply isMulCommutative_iff.mpr
  intro a b
  apply congrArg Additive.toMul
  apply h.sigma.injective
  change h.sigma (Additive.ofMul (a * b)) =
    h.sigma (Additive.ofMul (b * a))
  rw [h.sigma_mul, h.sigma_mul]
  exact add_comm _ _

private theorem isMulCommutative_P0
    (h : FiniteFieldImage P P0 U) : IsMulCommutative P0 := by
  letI : IsMulCommutative P := h.isMulCommutative_P
  apply isMulCommutative_iff.mpr
  intro a b
  let aP : P := ⟨(a : G), h.p0_le a.property⟩
  let bP : P := ⟨(b : G), h.p0_le b.property⟩
  apply Subtype.ext
  change (aP : G) * (bP : G) = (bP : G) * (aP : G)
  exact congrArg Subtype.val (mul_comm aP bP)
/-- The concrete Step-4 action is source-style right conjugation by `t`. -/
private theorem appendixCStep4Action_apply_step4Conj
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G)) (a : U) :
    ((h.appendixCStep4Action y hP1normU a : U) : G) =
      step4Conj (a : G) (h.appendixCStep4Conjugator y) := by
  simpa only [step4Conj] using
    h.appendixCStep4Action_apply_coe y hP1normU a

/-- Iterating the Step-4 action gives conjugation by the corresponding
power of `t`. -/
private theorem appendixCStep4Action_pow_apply_step4Conj
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G)) (n : ℕ) (a : U) :
    ((((h.appendixCStep4Action y hP1normU) ^ n) a : U) : G) =
      step4Conj (a : G) ((h.appendixCStep4Conjugator y) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change
        (((h.appendixCStep4Action y hP1normU)
          (((h.appendixCStep4Action y hP1normU) ^ n) a) : U) : G) = _
      rw [h.appendixCStep4Action_apply_step4Conj, ih, pow_succ']
      have hpowComm :
          (h.appendixCStep4Conjugator y) ^ n *
              h.appendixCStep4Conjugator y =
            h.appendixCStep4Conjugator y *
              (h.appendixCStep4Conjugator y) ^ n :=
        (pow_succ (h.appendixCStep4Conjugator y) n).symm.trans
          (pow_succ' (h.appendixCStep4Conjugator y) n)
      rw [← hpowComm]
      exact (step4Conj_mul_right (G := G) (a : G)
        ((h.appendixCStep4Conjugator y) ^ n)
        (h.appendixCStep4Conjugator y)).symm

private theorem appendixCStep4Action_inv_apply_step4Conj
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G)) (a : U) :
    (((h.appendixCStep4Action y hP1normU)⁻¹ a : U) : G) =
      step4Conj (a : G) (h.appendixCStep4Conjugator y)⁻¹ := by
  let phi := h.appendixCStep4Action y hP1normU
  have hforward :=
    h.appendixCStep4Action_apply_step4Conj y hP1normU (phi⁻¹ a)
  have hcancel : phi (phi⁻¹ a) = a := phi.apply_symm_apply a
  rw [hcancel] at hforward
  calc
    ((phi⁻¹ a : U) : G) =
        h.appendixCStep4Conjugator y *
          step4Conj ((phi⁻¹ a : U) : G)
            (h.appendixCStep4Conjugator y) *
          (h.appendixCStep4Conjugator y)⁻¹ := by
      simp only [step4Conj]
      group
    _ = h.appendixCStep4Conjugator y * (a : G) *
        (h.appendixCStep4Conjugator y)⁻¹ := by rw [← hforward]
    _ = step4Conj (a : G) (h.appendixCStep4Conjugator y)⁻¹ := by
      simp only [step4Conj, inv_inv]

private theorem appendixCStep4Action_inv_pow_apply_step4Conj
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G)) (n : ℕ) (a : U) :
    (((((h.appendixCStep4Action y hP1normU)⁻¹) ^ n) a : U) : G) =
      step4Conj (a : G)
        ((h.appendixCStep4Conjugator y)⁻¹ ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change
        ((((h.appendixCStep4Action y hP1normU)⁻¹)
          (((((h.appendixCStep4Action y hP1normU)⁻¹) ^ n) a)) : U) : G) = _
      rw [h.appendixCStep4Action_inv_apply_step4Conj, ih, pow_succ']
      have hpowComm :
          (h.appendixCStep4Conjugator y)⁻¹ ^ n *
              (h.appendixCStep4Conjugator y)⁻¹ =
            (h.appendixCStep4Conjugator y)⁻¹ *
              (h.appendixCStep4Conjugator y)⁻¹ ^ n :=
        (pow_succ (h.appendixCStep4Conjugator y)⁻¹ n).symm.trans
          (pow_succ' (h.appendixCStep4Conjugator y)⁻¹ n)
      rw [← hpowComm]
      exact (step4Conj_mul_right (G := G) (a : G)
        ((h.appendixCStep4Conjugator y)⁻¹ ^ n)
        (h.appendixCStep4Conjugator y)⁻¹).symm

/-- The three factors supplied by Step 1 for one of the words used in the
Step-4 calculation.  Keeping the two outer factors in `U` and the middle
factor in `P₀` makes the later membership arguments type-correct by
construction. -/
private structure Step4SUs
    (h : FiniteFieldImage P P0 U) (y : G)
    (m : ℕ) (a : U) (j n : ℕ)
    (u : U) (s₁ : P0) (v : U) : Prop where
  word_eq :
    (h.onePreimage : G) ^ m *
        step4Conj (a : G) ((h.appendixCStep4Conjugator y) ^ j) *
        ((h.onePreimage : G) ^ n)⁻¹ =
      (u : G) * (s₁ : G) * (v : G)

/-- Step 1 applied to a Step-4 word. -/
private theorem exists_step4SUs
    {H : Subgroup G} {p q : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) h.F]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardF : Nat.card h.F = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hcop : (nU p q).Coprime (p - 1))
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G))
    (m : ℕ) (a : U) (j n : ℕ) :
    ∃ u : U, ∃ s₁ : P0, ∃ v : U,
      Step4SUs h y m a j n u s₁ v := by
  let phi := h.appendixCStep4Action y hP1normU
  let aj : U := (phi ^ j) a
  have haj : (aj : G) =
      step4Conj (a : G) ((h.appendixCStep4Conjugator y) ^ j) := by
    exact h.appendixCStep4Action_pow_apply_step4Conj y hP1normU j a
  have hsH : (h.onePreimage : G) ∈ H :=
    hPH (h.p0_le h.onePreimage_mem_p0)
  have hxH :
      (h.onePreimage : G) ^ m *
          step4Conj (a : G) ((h.appendixCStep4Conjugator y) ^ j) *
          ((h.onePreimage : G) ^ n)⁻¹ ∈ H := by
    rw [← haj]
    exact H.mul_mem
      (H.mul_mem (H.pow_mem hsH m) (hUH aj.property))
      (H.inv_mem (H.pow_mem hsH n))
  obtain ⟨u, hu, v, hv, s₁, hs₁, heq⟩ :=
    h.splitH hPH hUH hsemi hUP hcardF hcardU hcop hxH
  exact ⟨⟨u, hu⟩, ⟨s₁, hs₁⟩, ⟨v, hv⟩, ⟨heq⟩⟩

/-- Modulo the normal factor `P`, a Step-4 word says that its conjugated
`U`-letter is the product of the two outer `U`-factors.  This is the
Mathlib replacement for Coq's `sUs_modP`. -/
private theorem Step4SUs.u_mul_v_eq
    {H : Subgroup G}
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G))
    {m : ℕ} {a : U} {j n : ℕ}
    {u : U} {s₁ : P0} {v : U}
    (d : Step4SUs h y m a j n u s₁ v) :
    step4Conj (a : G) ((h.appendixCStep4Conjugator y) ^ j) =
      (u : G) * (v : G) := by
  let PH : Subgroup H := P.subgroupOf H
  let UH : Subgroup H := U.subgroupOf H
  have hHnormP : H ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    let xH : H := ⟨x, hx⟩
    obtain ⟨⟨zH, wH⟩, hzw⟩ := hsemi.2 xH
    have hxzw : x = ((zH : H) : G) * ((wH : H) : G) :=
      (congrArg (fun z : H => (z : G)) hzw).symm
    rw [hxzw]
    exact (Subgroup.normalizer (P : Set G)).mul_mem
      (Subgroup.le_normalizer zH.property) (hUP wH.property)
  letI : PH.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHnormP
  let proj : H →* UH := hsemi.rightProjection
  let sPH : PH :=
    ⟨⟨(h.onePreimage : G), hPH (h.p0_le h.onePreimage_mem_p0)⟩,
      h.p0_le h.onePreimage_mem_p0⟩
  have haU :
      step4Conj (a : G) ((h.appendixCStep4Conjugator y) ^ j) ∈ U := by
    rw [← h.appendixCStep4Action_pow_apply_step4Conj y hP1normU j a]
    exact (((h.appendixCStep4Action y hP1normU) ^ j) a).property
  let aUH : UH :=
    ⟨⟨step4Conj (a : G) ((h.appendixCStep4Conjugator y) ^ j),
      hUH haU⟩, haU⟩
  let uUH : UH := ⟨⟨(u : G), hUH u.property⟩, u.property⟩
  let vUH : UH := ⟨⟨(v : G), hUH v.property⟩, v.property⟩
  let s₁PH : PH :=
    ⟨⟨(s₁ : G), hPH (h.p0_le s₁.property)⟩, h.p0_le s₁.property⟩
  have hdH :
      ((sPH : H) ^ m) * (aUH : H) * ((sPH : H) ^ n)⁻¹ =
        (uUH : H) * (s₁PH : H) * (vUH : H) := by
    apply Subtype.ext
    exact d.word_eq
  have hsProj : proj (sPH : H) = 1 :=
    Subgroup.IsComplement'.rightProjection_apply_left hsemi sPH
  have haProj : proj (aUH : H) = aUH :=
    Subgroup.IsComplement'.rightProjection_apply_right hsemi aUH
  have huProj : proj (uUH : H) = uUH :=
    Subgroup.IsComplement'.rightProjection_apply_right hsemi uUH
  have hvProj : proj (vUH : H) = vUH :=
    Subgroup.IsComplement'.rightProjection_apply_right hsemi vUH
  have hs₁Proj : proj (s₁PH : H) = 1 :=
    Subgroup.IsComplement'.rightProjection_apply_left hsemi s₁PH
  have hdProj := congrArg proj hdH
  have hdAmbient := congrArg (fun z : UH => ((z : H) : G)) hdProj
  simp only [map_mul, map_pow, map_inv, hsProj, haProj, huProj,
    hvProj, hs₁Proj, one_pow, inv_one, one_mul, mul_one] at hdAmbient
  change step4Conj (a : G) ((h.appendixCStep4Conjugator y) ^ j) =
    (u : G) * (v : G) at hdAmbient
  exact hdAmbient

/-- Frobenius fixes the `sigma`-image of `P₀`, because that image is the
prime additive line. -/
private theorem sigma_pow_prime_eq_self_of_mem_p0
    {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) h.F]
    (x : P) (hx : (x : G) ∈ P0) :
    h.sigma (Additive.ofMul x) ^ p =
      h.sigma (Additive.ofMul x) := by
  letI : CharP h.F p :=
    (Algebra.charP_iff (ZMod p) h.F p).mp (ZMod.charP p)
  have hxline := (h.mem_p0_iff_sigma_mem_primeAdditiveLine x).1 hx
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hxline
  rw [← hk]
  simpa only [zsmul_one, frobenius_def] using
    (map_intCast (frobenius h.F p) k)

/-- The middle `P₀` factor of a split word whose two `s`-exponents are
adjacent is nonidentity.  This is Coq's `nt_sUs`. -/
private theorem Step4SUs.middle_ne_one
    {H : Subgroup G} {p q : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) h.F]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardF : Nat.card h.F = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hcop : (nU p q).Coprime (p - 1))
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G))
    {m : ℕ} {a : U} {j n : ℕ}
    {u : U} {s₁ : P0} {v : U}
    (hadj : m = n + 1 ∨ n = m + 1)
    (d : Step4SUs h y m a j n u s₁ v) :
    (s₁ : G) ≠ 1 := by
  let s : G := h.onePreimage
  have hpows_ne : s ^ m ≠ s ^ n := by
    intro heq
    apply h.onePreimage_ne_one
    apply Subtype.ext
    rcases hadj with hmn | hnm
    · subst m
      have heq' : s ^ n * s = s ^ n * 1 := by
        simpa only [pow_succ, mul_one] using heq
      exact mul_left_cancel heq'
    · subst n
      have heq' : s ^ m * 1 = s ^ m * s := by
        simpa only [pow_succ, mul_one] using heq
      exact (mul_left_cancel heq').symm
  intro hs₁
  have haU :
      step4Conj (a : G) ((h.appendixCStep4Conjugator y) ^ j) ∈ U := by
    rw [← h.appendixCStep4Action_pow_apply_step4Conj y hP1normU j a]
    exact (((h.appendixCStep4Action y hP1normU) ^ j) a).property
  have hwordU :
      s ^ m * step4Conj (a : G)
          ((h.appendixCStep4Conjugator y) ^ j) * (s ^ n)⁻¹ ∈ U := by
    rw [d.word_eq, hs₁]
    simpa only [mul_one] using U.mul_mem u.property v.property
  have hsmP0 : s ^ m ∈ P0 := P0.pow_mem h.onePreimage_mem_p0 m
  have hsnP0 : (s ^ n)⁻¹ ∈ P0 :=
    P0.inv_mem (P0.pow_mem h.onePreimage_mem_p0 n)
  rcases h.not_splitU hPH hUH hsemi hUP hcardF hcardU hcop
      hsmP0 hsnP0 haU hwordU with htriv | htriv
  · apply hpows_ne
    calc
      s ^ m = 1 := htriv.1
      _ = s ^ n := (inv_eq_one.mp htriv.2).symm
  · apply hpows_ne
    calc
      s ^ m = (s ^ m * (s ^ n)⁻¹) * s ^ n := by group
      _ = 1 * s ^ n := by rw [htriv.2]
      _ = s ^ n := one_mul _

/-- Raising all three `U`-letters of a split relation to the
characteristic prime preserves the same middle `P₀` factor.  This is
Coq's `sUsXp`. -/
private theorem Step4SUs.pow_prime
    {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) h.F]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G))
    {m : ℕ} {a : U} {j n : ℕ}
    {u : U} {s₁ : P0} {v : U}
    (d : Step4SUs h y m a j n u s₁ v) :
    Step4SUs h y m (a ^ p) j n (u ^ p) s₁ (v ^ p) := by
  letI : CharP h.F p :=
    (Algebra.charP_iff (ZMod p) h.F p).mp (ZMod.charP p)
  let sP : P := h.onePreimage
  let smP : P := sP ^ m
  let snP : P := (sP ^ n)⁻¹
  let s₁P : P := ⟨(s₁ : G), h.p0_le s₁.property⟩
  let cu : P := rightConjugate P U hUP smP u
  let cv : P := rightConjugate P U hUP snP v⁻¹
  have hmod := d.u_mul_v_eq h hPH hUH hsemi hUP y hP1normU
  have hbaseP : cu * cv = s₁P := by
    apply Subtype.ext
    change
      ((rightConjugate P U hUP smP u : P) : G) *
          ((rightConjugate P U hUP snP v⁻¹ : P) : G) = (s₁ : G)
    rw [coe_rightConjugate, coe_rightConjugate]
    dsimp only [smP, snP, sP]
    simp only [Subgroup.coe_pow, Subgroup.coe_inv, inv_inv]
    change (u : G)⁻¹ * (h.onePreimage : G) ^ m * (u : G) *
        ((v : G) * ((h.onePreimage : G) ^ n)⁻¹ * (v : G)⁻¹) =
      (s₁ : G)
    calc
      _ = (u : G)⁻¹ *
          ((h.onePreimage : G) ^ m *
            ((u : G) * (v : G)) *
            ((h.onePreimage : G) ^ n)⁻¹) * (v : G)⁻¹ := by group
      _ = (u : G)⁻¹ *
          ((h.onePreimage : G) ^ m *
            step4Conj (a : G)
              ((h.appendixCStep4Conjugator y) ^ j) *
            ((h.onePreimage : G) ^ n)⁻¹) * (v : G)⁻¹ := by rw [hmod]
      _ = (u : G)⁻¹ * ((u : G) * (s₁ : G) * (v : G)) *
          (v : G)⁻¹ := by rw [d.word_eq]
      _ = (s₁ : G) := by group
  let cup : P := rightConjugate P U hUP smP (u ^ p)
  let cvp : P := rightConjugate P U hUP snP ((v ^ p)⁻¹)
  have hsmP0 : (smP : G) ∈ P0 := by
    exact P0.pow_mem h.onePreimage_mem_p0 m
  have hsnP0 : (snP : G) ∈ P0 := by
    exact P0.inv_mem (P0.pow_mem h.onePreimage_mem_p0 n)
  have hs₁Fix := h.sigma_pow_prime_eq_self_of_mem_p0
    (p := p) s₁P s₁.property
  have hsmFix := h.sigma_pow_prime_eq_self_of_mem_p0
    (p := p) smP hsmP0
  have hsnFix := h.sigma_pow_prime_eq_self_of_mem_p0
    (p := p) snP hsnP0
  have hcuSigma :
      h.sigma (Additive.ofMul cup) =
        h.sigma (Additive.ofMul cu) ^ p := by
    rw [h.sigma_rightConjugate, h.sigma_rightConjugate,
      h.psiValue_pow]
    calc
      h.sigma (Additive.ofMul smP) * h.psiValue u ^ p =
          h.sigma (Additive.ofMul smP) ^ p *
            h.psiValue u ^ p := by rw [hsmFix]
      _ = (h.sigma (Additive.ofMul smP) * h.psiValue u) ^ p :=
        (mul_pow _ _ _).symm
  have hcvSigma :
      h.sigma (Additive.ofMul cvp) =
        h.sigma (Additive.ofMul cv) ^ p := by
    rw [h.sigma_rightConjugate, h.sigma_rightConjugate]
    have hpsi : h.psiValue ((v ^ p)⁻¹) =
        h.psiValue (v⁻¹) ^ p := by simp
    rw [hpsi]
    calc
      h.sigma (Additive.ofMul snP) * h.psiValue v⁻¹ ^ p =
          h.sigma (Additive.ofMul snP) ^ p *
            h.psiValue v⁻¹ ^ p := by rw [hsnFix]
      _ = (h.sigma (Additive.ofMul snP) * h.psiValue v⁻¹) ^ p :=
        (mul_pow _ _ _).symm
  have hpP : cup * cvp = s₁P := by
    apply congrArg Additive.toMul
    apply h.sigma.injective
    calc
      h.sigma (Additive.ofMul (cup * cvp)) =
          h.sigma (Additive.ofMul cup) +
            h.sigma (Additive.ofMul cvp) := h.sigma_mul cup cvp
      _ = h.sigma (Additive.ofMul cu) ^ p +
          h.sigma (Additive.ofMul cv) ^ p := by
        rw [hcuSigma, hcvSigma]
      _ = (h.sigma (Additive.ofMul cu) +
          h.sigma (Additive.ofMul cv)) ^ p :=
        (add_pow_char _ _ p).symm
      _ = h.sigma (Additive.ofMul (cu * cv)) ^ p := by
        rw [h.sigma_mul]
      _ = h.sigma (Additive.ofMul s₁P) ^ p := by rw [hbaseP]
      _ = h.sigma (Additive.ofMul s₁P) := hs₁Fix
  have hpAmbient :
      ((u ^ p : U) : G)⁻¹ * (h.onePreimage : G) ^ m *
          ((u ^ p : U) : G) *
          (((v ^ p : U) : G) * ((h.onePreimage : G) ^ n)⁻¹ *
            ((v ^ p : U) : G)⁻¹) =
        (s₁ : G) := by
    have := congrArg (fun z : P => (z : G)) hpP
    change
      ((rightConjugate P U hUP smP (u ^ p) : P) : G) *
          ((rightConjugate P U hUP snP ((v ^ p)⁻¹) : P) : G) =
        (s₁ : G) at this
    rw [coe_rightConjugate, coe_rightConjugate] at this
    dsimp only [smP, snP, sP] at this
    simp only [Subgroup.coe_pow, Subgroup.coe_inv, inv_inv] at this
    exact this
  have hletter :
      step4Conj ((a ^ p : U) : G)
          ((h.appendixCStep4Conjugator y) ^ j) =
        ((u ^ p : U) : G) * ((v ^ p : U) : G) := by
    let phi := h.appendixCStep4Action y hP1normU
    calc
      step4Conj ((a ^ p : U) : G)
          ((h.appendixCStep4Conjugator y) ^ j) =
          (((phi ^ j) (a ^ p) : U) : G) :=
        (h.appendixCStep4Action_pow_apply_step4Conj
          y hP1normU j (a ^ p)).symm
      _ = ((((phi ^ j) a) ^ p : U) : G) := by rw [map_pow]
      _ = step4Conj (a : G)
          ((h.appendixCStep4Conjugator y) ^ j) ^ p := by
        simp only [Subgroup.coe_pow]
        rw [h.appendixCStep4Action_pow_apply_step4Conj]
      _ = ((u : G) * (v : G)) ^ p := by rw [hmod]
      _ = ((u ^ p : U) : G) * ((v ^ p : U) : G) := by
        letI : IsMulCommutative U := h.actingGroup_isMulCommutative
        exact congrArg Subtype.val (mul_pow u v p)
  constructor
  rw [hletter]
  calc
    (h.onePreimage : G) ^ m *
          (((u ^ p : U) : G) * ((v ^ p : U) : G)) *
          ((h.onePreimage : G) ^ n)⁻¹ =
        ((u ^ p : U) : G) *
          ((((u ^ p : U) : G)⁻¹ * (h.onePreimage : G) ^ m *
            ((u ^ p : U) : G)) *
            (((v ^ p : U) : G) * ((h.onePreimage : G) ^ n)⁻¹ *
              ((v ^ p : U) : G)⁻¹)) *
          ((v ^ p : U) : G) := by group
    _ = ((u ^ p : U) : G) * (s₁ : G) * ((v ^ p : U) : G) := by
      rw [hpAmbient]

/-- The discrepancy `s⁻ⁿtⁿ` lies in `Q`; this is `Qsti` in the source. -/
private theorem step4_difference_mem_Q
    [Finite G] {Q : Subgroup G}
    (hnormQ : P0 ≤ Subgroup.normalizer (Q : Set G))
    {y : G} (hy : y ∈ ⁅Q, P0⁆) (n : ℕ) :
    ((h.onePreimage : G) ^ n)⁻¹ *
        (h.appendixCStep4Conjugator y) ^ n ∈ Q := by
  let s : G := h.onePreimage
  let t : G := h.appendixCStep4Conjugator y
  have hyQ : y ∈ Q := sQP0Q hnormQ hy
  have hsNorm : s ∈ Subgroup.normalizer (Q : Set G) :=
    hnormQ h.onePreimage_mem_p0
  have hc1 : s⁻¹ * t ∈ Q := by
    have hyInvConj : s⁻¹ * y⁻¹ * s ∈ Q :=
      (Subgroup.mem_normalizer_iff''.mp hsNorm y⁻¹).mp (Q.inv_mem hyQ)
    dsimp only [t, s, FiniteFieldImage.appendixCStep4Conjugator]
    simpa only [mul_assoc] using Q.mul_mem hyInvConj hyQ
  induction n with
  | zero => simp
  | succ n ih =>
      have hconj : s⁻¹ * (((s ^ n)⁻¹ * t ^ n)) * s ∈ Q :=
        (Subgroup.mem_normalizer_iff''.mp hsNorm
          ((s ^ n)⁻¹ * t ^ n)).mp ih
      change (s ^ (n + 1))⁻¹ * t ^ (n + 1) ∈ Q
      have heq :
          (s ^ (n + 1))⁻¹ * t ^ (n + 1) =
            (s⁻¹ * ((s ^ n)⁻¹ * t ^ n) * s) * (s⁻¹ * t) := by
        rw [pow_succ, pow_succ]
        group
      rw [heq]
      exact Q.mul_mem hconj hc1

/-- The commuting-discrepancy identity `stXC` used by the central Step-4
word calculation. -/
private theorem step4_stXC
    [Finite G] {Q : Subgroup G} {q : ℕ}
    (hQ : IsElementaryAbelianGroup q Q)
    (hnormQ : P0 ≤ Subgroup.normalizer (Q : Set G))
    {y : G} (hy : y ∈ ⁅Q, P0⁆)
    {m n : ℕ} (hmn : m ≤ n) :
    step4Conj (((h.onePreimage : G) ^ n)⁻¹)
        ((h.appendixCStep4Conjugator y) ^ m) =
      step4Conj (((h.onePreimage : G) ^ m)⁻¹)
          ((h.appendixCStep4Conjugator y) ^ n) *
        ((h.onePreimage : G) ^ (n - m))⁻¹ := by
  let s : G := h.onePreimage
  let t : G := h.appendixCStep4Conjugator y
  let c : ℕ → G := fun k => (s ^ k)⁻¹ * t ^ k
  let d := n - m
  have hmd : m + d = n := Nat.add_sub_of_le hmn
  have hcQ (k : ℕ) : c k ∈ Q :=
    h.step4_difference_mem_Q hnormQ hy k
  letI : IsMulCommutative Q := hQ.commutative
  have hccomm : c d * c n = c n * c d := by
    exact congrArg Subtype.val
      (mul_comm (⟨c d, hcQ d⟩ : Q) ⟨c n, hcQ n⟩)
  change (t ^ m)⁻¹ * (s ^ n)⁻¹ * t ^ m =
    (t ^ n)⁻¹ * (s ^ m)⁻¹ * t ^ n * (s ^ d)⁻¹
  have hbig :
      ((s ^ d)⁻¹ * t ^ n) *
          ((t ^ m)⁻¹ * (s ^ n)⁻¹ * t ^ m) * t ^ d =
        ((s ^ d)⁻¹ * t ^ n) *
          ((t ^ n)⁻¹ * (s ^ m)⁻¹ * t ^ n * (s ^ d)⁻¹) *
          t ^ d := by
    calc
      _ = c d * c n := by
        dsimp [c]
        rw [← hmd]
        group
      _ = c n * c d := hccomm
      _ = _ := by
        dsimp [c]
        rw [← hmd]
        group
  exact mul_left_cancel (mul_right_cancel hbig)

/-- The central `s2def` identity, before the Frobenius comparison kills
the three auxiliary `U`-letters. -/
private theorem step4_s2def
    [Finite G] {H Q : Subgroup G} {p q : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) h.F]
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hQ : IsElementaryAbelianGroup q Q)
    (hnormQ : P0 ≤ Subgroup.normalizer (Q : Set G))
    (y : G) (hy : y ∈ ⁅Q, P0⁆)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G))
    {a b : U} (hab : h.psiValue a + h.psiValue b = 2)
    {u₁ v₁ u₂ v₂ u₃ v₃ : U} {s₁ s₂ s₃ : P0}
    (r₁ : Step4SUs h y 1 a⁻¹ 3 2 u₁ s₁ v₁)
    (r₂ : Step4SUs h y 3 (a * b⁻¹) 2 1 u₂ s₂ v₂)
    (r₃ : Step4SUs h y 2 b 1 3 u₃ s₃ v₃) :
    let phi := h.appendixCStep4Action y hP1normU
    h.appendixCStep4Conjugator y * (s₂ : G)⁻¹ *
        h.appendixCStep4Conjugator y =
      ((((phi⁻¹) v₂) * u₃ : U) : G) * (s₃ : G) *
        ((v₃ * (((phi⁻¹) ^ 2) u₁) : U) : G) *
        h.appendixCStep4Conjugator y ^ 2 * (s₁ : G) *
        ((v₁ * phi u₂ : U) : G) := by
  dsimp only
  let s : G := h.onePreimage
  let t : G := h.appendixCStep4Conjugator y
  let phi := h.appendixCStep4Action y hP1normU
  let sP : P := h.onePreimage
  have hsabP :
      rightConjugate P U hUP sP a * rightConjugate P U hUP sP b =
        sP ^ 2 := by
    apply congrArg Additive.toMul
    apply h.sigma.injective
    change
      h.sigma (Additive.ofMul
        (rightConjugate P U hUP sP a *
          rightConjugate P U hUP sP b)) =
        h.sigma (Additive.ofMul (sP ^ 2))
    rw [h.sigma_mul, h.sigma_rightConjugate,
      h.sigma_rightConjugate, h.sigma_pow, h.sigma_onePreimage]
    simp only [one_mul, two_nsmul]
    calc
      h.psiValue a + h.psiValue b = 2 := hab
      _ = 1 + 1 := by norm_num
  have hsab :
      (a : G)⁻¹ * s * (a : G) *
          ((b : G)⁻¹ * s * (b : G)) = s ^ 2 := by
    have := congrArg (fun z : P => (z : G)) hsabP
    change
      ((rightConjugate P U hUP sP a : P) : G) *
          ((rightConjugate P U hUP sP b : P) : G) =
        ((sP : P) : G) ^ 2 at this
    simpa only [s, sP, coe_rightConjugate] using this
  have hD :
      s * (b : G) * (s ^ 2)⁻¹ * (a : G)⁻¹ * s =
        (b : G) * (a : G)⁻¹ := by
    calc
      _ = s * (b : G) *
          ((a : G)⁻¹ * s * (a : G) *
            ((b : G)⁻¹ * s * (b : G)))⁻¹ *
          (a : G)⁻¹ * s := by rw [hsab]
      _ = (b : G) * (a : G)⁻¹ := by group
  have hst12 := h.step4_stXC hQ hnormQ hy
    (m := 1) (n := 2) (by omega)
  have hst23 := h.step4_stXC hQ hnormQ hy
    (m := 2) (n := 3) (by omega)
  have hst13 := h.step4_stXC hQ hnormQ hy
    (m := 1) (n := 3) (by omega)
  have hst12' : t⁻¹ * (s ^ 2)⁻¹ * t =
      (t ^ 2)⁻¹ * s⁻¹ * t ^ 2 * s⁻¹ := by
    simpa [step4Conj, s, t] using hst12
  have hst23' : (t ^ 2)⁻¹ * (s ^ 3)⁻¹ * t ^ 2 =
      (t ^ 3)⁻¹ * (s ^ 2)⁻¹ * t ^ 3 * s⁻¹ := by
    simpa [step4Conj, s, t] using hst23
  have hst13' : t⁻¹ * (s ^ 3)⁻¹ * t =
      (t ^ 3)⁻¹ * s⁻¹ * t ^ 3 * (s ^ 2)⁻¹ := by
    simpa [step4Conj, s, t] using hst13
  have hA : t⁻¹ * s ^ 2 * t⁻¹ = s * (t ^ 2)⁻¹ * s := by
    calc
      t⁻¹ * s ^ 2 * t⁻¹ =
          (t⁻¹ * s ^ 2 * t) * (t ^ 2)⁻¹ := by group
      _ = (t⁻¹ * (s ^ 2)⁻¹ * t)⁻¹ * (t ^ 2)⁻¹ := by group
      _ = ((t ^ 2)⁻¹ * s⁻¹ * t ^ 2 * s⁻¹)⁻¹ *
          (t ^ 2)⁻¹ := by rw [hst12']
      _ = s * (t ^ 2)⁻¹ * s := by group
  have hC :
      t * (s ^ 3)⁻¹ * t ^ 2 =
        (s ^ 2)⁻¹ * t ^ 3 * s⁻¹ := by
    calc
      t * (s ^ 3)⁻¹ * t ^ 2 =
          t ^ 3 * ((t ^ 2)⁻¹ * (s ^ 3)⁻¹ * t ^ 2) := by group
      _ = t ^ 3 *
          ((t ^ 3)⁻¹ * (s ^ 2)⁻¹ * t ^ 3 * s⁻¹) := by
        rw [hst23']
      _ = (s ^ 2)⁻¹ * t ^ 3 * s⁻¹ := by group
  have h13aux :
      t ^ 2 * (s ^ 3)⁻¹ * t =
        s⁻¹ * t ^ 3 * (s ^ 2)⁻¹ := by
    calc
      t ^ 2 * (s ^ 3)⁻¹ * t =
          t ^ 3 * (t⁻¹ * (s ^ 3)⁻¹ * t) := by group
      _ = t ^ 3 *
          ((t ^ 3)⁻¹ * s⁻¹ * t ^ 3 * (s ^ 2)⁻¹) := by
        rw [hst13']
      _ = s⁻¹ * t ^ 3 * (s ^ 2)⁻¹ := by group
  have hB :
      t ^ 3 * (s ^ 2)⁻¹ * t⁻¹ =
        s * t ^ 2 * (s ^ 3)⁻¹ := by
    calc
      t ^ 3 * (s ^ 2)⁻¹ * t⁻¹ =
          s * (s⁻¹ * t ^ 3 * (s ^ 2)⁻¹) * t⁻¹ := by group
      _ = s * (t ^ 2 * (s ^ 3)⁻¹ * t) * t⁻¹ := by rw [h13aux]
      _ = s * t ^ 2 * (s ^ 3)⁻¹ := by group
  let coreLong : G :=
    t⁻¹ * s ^ 2 * t⁻¹ * (b : G) * t * (s ^ 3)⁻¹ * t ^ 2 * s *
      (t ^ 3)⁻¹ * (a : G)⁻¹ * t ^ 3 * (s ^ 2)⁻¹ * t⁻¹
  let coreShort : G :=
    s * (t ^ 2)⁻¹ * (b : G) * (a : G)⁻¹ * t ^ 2 * (s ^ 3)⁻¹
  have hcore : coreLong = coreShort := by
    dsimp only [coreLong, coreShort]
    calc
      _ = s * (t ^ 2)⁻¹ * s * (b : G) * t * (s ^ 3)⁻¹ *
          t ^ 2 * s * (t ^ 3)⁻¹ * (a : G)⁻¹ * t ^ 3 *
          (s ^ 2)⁻¹ * t⁻¹ := by
        rw [hA]
      _ = s * (t ^ 2)⁻¹ * s * (b : G) * (s ^ 2)⁻¹ *
          t ^ 3 * s⁻¹ * s * (t ^ 3)⁻¹ * (a : G)⁻¹ * t ^ 3 *
          (s ^ 2)⁻¹ * t⁻¹ := by
        have hz := congrArg
          (fun z : G =>
            s * (t ^ 2)⁻¹ * s * (b : G) * z * s *
              (t ^ 3)⁻¹ * (a : G)⁻¹ * t ^ 3 *
              (s ^ 2)⁻¹ * t⁻¹)
          hC
        simpa only [mul_assoc] using hz
      _ = s * (t ^ 2)⁻¹ * s * (b : G) * (s ^ 2)⁻¹ *
          (a : G)⁻¹ * t ^ 3 * (s ^ 2)⁻¹ * t⁻¹ := by group
      _ = s * (t ^ 2)⁻¹ * s * (b : G) * (s ^ 2)⁻¹ *
          (a : G)⁻¹ * s * t ^ 2 * (s ^ 3)⁻¹ := by
        have hz := congrArg
          (fun z : G =>
            s * (t ^ 2)⁻¹ * s * (b : G) * (s ^ 2)⁻¹ *
              (a : G)⁻¹ * z)
          hB
        simpa only [mul_assoc] using hz
      _ = s * (t ^ 2)⁻¹ * (b : G) * (a : G)⁻¹ *
          t ^ 2 * (s ^ 3)⁻¹ := by
        have hz := congrArg
          (fun z : G =>
            s * (t ^ 2)⁻¹ * z * t ^ 2 * (s ^ 3)⁻¹)
          hD
        simpa only [mul_assoc] using hz
  have hs₂inv :
      (s₂ : G)⁻¹ = (v₂ : G) *
        (s ^ 3 * step4Conj ((a * b⁻¹ : U) : G) (t ^ 2) * s⁻¹)⁻¹ *
        (u₂ : G) := by
    have hr₂ :
        s ^ 3 * step4Conj ((a * b⁻¹ : U) : G) (t ^ 2) * s⁻¹ =
          (u₂ : G) * (s₂ : G) * (v₂ : G) := by
      simpa only [s, t, pow_one] using r₂.word_eq
    rw [hr₂]
    group
  have hs₃ :
      (s₃ : G) = (u₃ : G)⁻¹ *
        (s ^ 2 * step4Conj (b : G) t * (s ^ 3)⁻¹) *
        (v₃ : G)⁻¹ := by
    have hr₃ :
        s ^ 2 * step4Conj (b : G) t * (s ^ 3)⁻¹ =
          (u₃ : G) * (s₃ : G) * (v₃ : G) := by
      simpa only [s, t, pow_one] using r₃.word_eq
    rw [hr₃]
    group
  have hs₁ :
      (s₁ : G) = (u₁ : G)⁻¹ *
        (s * step4Conj ((a⁻¹ : U) : G) (t ^ 3) * (s ^ 2)⁻¹) *
        (v₁ : G)⁻¹ := by
    have hr₁ :
        s * step4Conj ((a⁻¹ : U) : G) (t ^ 3) * (s ^ 2)⁻¹ =
          (u₁ : G) * (s₁ : G) * (v₁ : G) := by
      simpa only [s, t, pow_one] using r₁.word_eq
    rw [hr₁]
    group
  have hw₁ : ((((phi⁻¹) v₂) * u₃ : U) : G) =
      t * (v₂ : G) * t⁻¹ * (u₃ : G) := by
    simp only [Subgroup.coe_mul]
    rw [show (((phi⁻¹) v₂ : U) : G) =
      step4Conj (v₂ : G) t⁻¹ by
        exact h.appendixCStep4Action_inv_apply_step4Conj
          y hP1normU v₂]
    simp only [step4Conj, inv_inv]
  have hw₂ : ((v₃ * (((phi⁻¹) ^ 2) u₁) : U) : G) =
      (v₃ : G) * t ^ 2 * (u₁ : G) * (t ^ 2)⁻¹ := by
    simp only [Subgroup.coe_mul]
    rw [show (((((phi⁻¹) ^ 2) u₁) : U) : G) =
      step4Conj (u₁ : G) (t⁻¹ ^ 2) by
        exact h.appendixCStep4Action_inv_pow_apply_step4Conj
          y hP1normU 2 u₁]
    simp only [step4Conj]
    group
  have hw₃ : ((v₁ * phi u₂ : U) : G) =
      (v₁ : G) * t⁻¹ * (u₂ : G) * t := by
    simp only [Subgroup.coe_mul]
    rw [show ((phi u₂ : U) : G) = step4Conj (u₂ : G) t by
      exact h.appendixCStep4Action_apply_step4Conj
        y hP1normU u₂]
    simp only [step4Conj]
    group
  calc
    t * (s₂ : G)⁻¹ * t =
        t * (v₂ : G) * coreShort * (u₂ : G) * t := by
      rw [hs₂inv]
      dsimp only [coreShort, step4Conj]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    _ = t * (v₂ : G) * coreLong * (u₂ : G) * t := by
      rw [hcore]
    _ = ((((phi⁻¹) v₂) * u₃ : U) : G) * (s₃ : G) *
        ((v₃ * (((phi⁻¹) ^ 2) u₁) : U) : G) * t ^ 2 *
        (s₁ : G) * ((v₁ * phi u₂ : U) : G) := by
      rw [hw₁, hw₂, hw₃, hs₃, hs₁]
      dsimp only [coreLong, step4Conj]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group

/-- Frobenius comparison plus Step 3 eliminate the three auxiliary
`U`-letters from `s2def`. -/
private theorem step4_reduced_s2def
    [Finite G] {H Q : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] [Algebra (ZMod p) h.F]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardF : Nat.card h.F = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hcop : (nU p q).Coprime (p - 1))
    (hQ : IsElementaryAbelianGroup q Q)
    (hnormQ : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hqp : q < p)
    (y : G) (hy : y ∈ ⁅Q, P0⁆)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G))
    (hti : ∀ {r : G}, r ∈ appendixCP1 P0 y → r ≠ 1 →
      H ⊓ H.map (MulAut.conj r⁻¹).toMonoidHom = U)
    {a b : U} (hab : h.psiValue a + h.psiValue b = 2)
    {u₁ v₁ u₂ v₂ u₃ v₃ : U} {s₁ s₂ s₃ : P0}
    (r₁ : Step4SUs h y 1 a⁻¹ 3 2 u₁ s₁ v₁)
    (r₂ : Step4SUs h y 3 (a * b⁻¹) 2 1 u₂ s₂ v₂)
    (r₃ : Step4SUs h y 2 b 1 3 u₃ s₃ v₃) :
    h.appendixCStep4Conjugator y * (s₂ : G)⁻¹ *
        h.appendixCStep4Conjugator y =
      (s₃ : G) * h.appendixCStep4Conjugator y ^ 2 * (s₁ : G) := by
  letI : CharP h.F p :=
    (Algebra.charP_iff (ZMod p) h.F p).mp (ZMod.charP p)
  letI : IsMulCommutative U := h.actingGroup_isMulCommutative
  let s : G := h.onePreimage
  let t : G := h.appendixCStep4Conjugator y
  let phi := h.appendixCStep4Action y hP1normU
  let w₁ : U := phi⁻¹ v₂ * u₃
  let w₂ : U := v₃ * ((phi⁻¹) ^ 2) u₁
  let w₃ : U := v₁ * phi u₂
  have hds2 :
      t * (s₂ : G)⁻¹ * t =
        (w₁ : G) * (s₃ : G) * (w₂ : G) * t ^ 2 *
          (s₁ : G) * (w₃ : G) := by
    simpa only [t, phi, w₁, w₂, w₃] using
      h.step4_s2def (p := p) (q := q) (H := H) (Q := Q)
        hUP hQ hnormQ y hy hP1normU hab r₁ r₂ r₃
  have habp :
      h.psiValue (a ^ p) + h.psiValue (b ^ p) = 2 := by
    calc
      _ = h.psiValue a ^ p + h.psiValue b ^ p := by
        rw [h.psiValue_pow, h.psiValue_pow]
      _ = (h.psiValue a + h.psiValue b) ^ p :=
        (add_pow_char _ _ p).symm
      _ = (2 : h.F) ^ p := congrArg (fun z : h.F => z ^ p) hab
      _ = 2 := by
        change frobenius h.F p (2 : h.F) = (2 : h.F)
        simpa using (map_natCast (frobenius h.F p) (2 : ℕ))
  have r₁p0 := r₁.pow_prime (H := H) (p := p)
    h hPH hUH hsemi hUP y hP1normU
  have r₂p0 := r₂.pow_prime (H := H) (p := p)
    h hPH hUH hsemi hUP y hP1normU
  have r₃p := r₃.pow_prime (H := H) (p := p)
    h hPH hUH hsemi hUP y hP1normU
  have r₁p :
      Step4SUs h y 1 (a ^ p)⁻¹ 3 2 (u₁ ^ p) s₁ (v₁ ^ p) := by
    simpa only [inv_pow] using r₁p0
  have r₂p :
      Step4SUs h y 3 (a ^ p * (b ^ p)⁻¹) 2 1
        (u₂ ^ p) s₂ (v₂ ^ p) := by
    simpa only [mul_pow, inv_pow] using r₂p0
  have hds2p0 :=
    h.step4_s2def (p := p) (q := q) (H := H) (Q := Q)
      hUP hQ hnormQ y hy hP1normU habp r₁p r₂p r₃p
  have hds2p :
      t * (s₂ : G)⁻¹ * t =
        ((w₁ ^ p : U) : G) * (s₃ : G) * ((w₂ ^ p : U) : G) *
          t ^ 2 * (s₁ : G) * ((w₃ ^ p : U) : G) := by
    simpa only [t, phi, w₁, w₂, w₃, map_pow, mul_pow] using hds2p0
  let k := p - 1
  have hpk : k + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have hcopU : (Nat.card U).Coprime k := by
    simpa only [hcardU, k] using hcop
  have w_id (w : U) (hw : w ^ k = 1) : w = 1 := by
    apply hcopU.pow_left_bijective.injective
    simpa only [one_pow] using hw
  have heqWords :
      ((w₁ ^ p : U) : G) * (s₃ : G) * ((w₂ ^ p : U) : G) *
          t ^ 2 * (s₁ : G) * ((w₃ ^ p : U) : G) =
        (w₁ : G) * (s₃ : G) * (w₂ : G) * t ^ 2 *
          (s₁ : G) * (w₃ : G) := hds2p.symm.trans hds2
  have htail :
      ((w₁ ^ p : U) : G)⁻¹ *
          ((w₁ : G) * (s₃ : G) * (w₂ : G) * t ^ 2 *
            (s₁ : G) * (w₃ : G)) =
        (s₃ : G) * ((w₂ ^ p : U) : G) * t ^ 2 *
          (s₁ : G) * ((w₃ ^ p : U) : G) := by
    rw [← heqWords]
    group
  let inner : G :=
    ((w₂ ^ p : U) : G)⁻¹ *
      step4Conj (((w₁⁻¹) ^ k : U) : G) (s₃ : G) * (w₂ : G)
  have hcompare :
      step4Conj inner (t ^ 2) =
        step4Conj (((w₃ ^ k : U) : G)) (s₁ : G)⁻¹ := by
    dsimp only [inner, step4Conj]
    simp only [inv_inv]
    calc
      (t ^ 2)⁻¹ *
          (((w₂ ^ p : U) : G)⁻¹ *
            ((s₃ : G)⁻¹ * (((w₁⁻¹) ^ k : U) : G) * (s₃ : G)) *
            (w₂ : G)) * t ^ 2 =
        (t ^ 2)⁻¹ * ((w₂ ^ p : U) : G)⁻¹ * (s₃ : G)⁻¹ *
          ((w₁ ^ p : U) : G)⁻¹ *
          ((w₁ : G) * (s₃ : G) * (w₂ : G) * t ^ 2 *
            (s₁ : G) * (w₃ : G)) *
          (w₃ : G)⁻¹ * (s₁ : G)⁻¹ := by
        simp only [Subgroup.coe_pow, Subgroup.coe_inv]
        rw [← hpk]
        simp only [pow_succ]
        group
      _ = (t ^ 2)⁻¹ * ((w₂ ^ p : U) : G)⁻¹ * (s₃ : G)⁻¹ *
          ((s₃ : G) * ((w₂ ^ p : U) : G) * t ^ 2 *
            (s₁ : G) * ((w₃ ^ p : U) : G)) *
          (w₃ : G)⁻¹ * (s₁ : G)⁻¹ := by
        have hz := congrArg
          (fun z : G =>
            (t ^ 2)⁻¹ * ((w₂ ^ p : U) : G)⁻¹ * (s₃ : G)⁻¹ *
              z * (w₃ : G)⁻¹ * (s₁ : G)⁻¹)
          htail
        simpa only [mul_assoc] using hz
      _ = (s₁ : G) * (((w₃ ^ k : U) : G)) * (s₁ : G)⁻¹ := by
        simp only [Subgroup.coe_pow, Subgroup.coe_inv]
        rw [← hpk]
        simp only [pow_succ]
        group
  have htP1 : t ∈ appendixCP1 P0 y :=
    h.appendixCStep4Conjugator_mem y
  have ht2P1 : t ^ 2 ∈ appendixCP1 P0 y :=
    (appendixCP1 P0 y).pow_mem htP1 2
  have htOrder : orderOf t = p := by
    calc
      orderOf t = orderOf ((h.onePreimage : G)) := by
        dsimp [t, FiniteFieldImage.appendixCStep4Conjugator]
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          inv_inv] using
            orderOf_injective (MulAut.conj y⁻¹).toMonoidHom
              (MulAut.conj y⁻¹).injective (h.onePreimage : G)
      _ = p := h.orderOf_onePreimage
  have htwoP : 2 < p := (Fact.out : q.Prime).two_le.trans_lt hqp
  have ht2ne : t ^ 2 ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (x := t)
    · omega
    · simpa only [htOrder] using htwoP
  have hs₁ne : (s₁ : G) ≠ 1 :=
    r₁.middle_ne_one h hPH hUH hsemi hUP hcardF hcardU hcop
      y hP1normU (by right; rfl)
  have hs₃ne : (s₃ : G) ≠ 1 :=
    r₃.middle_ne_one h hPH hUH hsemi hUP hcardF hcardU hcop
      y hP1normU (by right; rfl)
  have hinnerH : inner ∈ H := by
    dsimp only [inner, step4Conj]
    exact H.mul_mem
      (H.mul_mem
        (H.inv_mem (hUH (U.pow_mem w₂.property p)))
        (H.mul_mem
          (H.mul_mem (H.inv_mem (hPH (h.p0_le s₃.property)))
            (hUH (U.pow_mem (U.inv_mem w₁.property) k)))
          (hPH (h.p0_le s₃.property))))
      (hUH w₂.property)
  let z₃ : G := step4Conj (((w₃ ^ k : U) : G)) (s₁ : G)⁻¹
  have hz₃H : z₃ ∈ H := by
    dsimp only [z₃, step4Conj]
    simp only [inv_inv]
    exact H.mul_mem
      (H.mul_mem (hPH (h.p0_le s₁.property))
        (hUH (U.pow_mem w₃.property k)))
      (H.inv_mem (hPH (h.p0_le s₁.property)))
  have hz₃Map :
      z₃ ∈ H.map (MulAut.conj (t ^ 2)⁻¹).toMonoidHom := by
    dsimp only [z₃]
    rw [← hcompare]
    simpa only [step4Conj, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv] using
      Subgroup.mem_map_of_mem
        (MulAut.conj (t ^ 2)⁻¹).toMonoidHom hinnerH
  have hz₃U : z₃ ∈ U := by
    rw [← hti ht2P1 ht2ne]
    exact ⟨hz₃H, hz₃Map⟩
  have hw₃pow : w₃ ^ k = 1 := by
    have hword :
        (s₁ : G) * (((w₃ ^ k : U) : G)) * (s₁ : G)⁻¹ ∈ U := by
      simpa only [z₃, step4Conj, inv_inv] using hz₃U
    rcases h.not_splitU hPH hUH hsemi hUP hcardF hcardU hcop
      s₁.property (P0.inv_mem s₁.property) (U.pow_mem w₃.property k)
      hword with htriv | htriv
    · exact (hs₁ne htriv.1).elim
    · apply Subtype.ext
      exact htriv.1
  have hw₃ : w₃ = 1 := w_id w₃ hw₃pow
  have hinnerOne : inner = 1 := by
    have hconjOne : step4Conj inner (t ^ 2) = 1 := by
      rw [hcompare, hw₃]
      simp [step4Conj]
    dsimp only [step4Conj] at hconjOne
    calc
      inner = t ^ 2 * ((t ^ 2)⁻¹ * inner * t ^ 2) * (t ^ 2)⁻¹ := by
        group
      _ = 1 := by rw [hconjOne]; group
  have hw₂pow :
      w₂ ^ k = step4Conj (((w₁⁻¹) ^ k : U) : G) (s₃ : G) := by
    dsimp only [inner] at hinnerOne
    have hcword :
        step4Conj (((w₁⁻¹) ^ k : U) : G) (s₃ : G) =
          ((w₂ ^ p : U) : G) * (w₂ : G)⁻¹ := by
      calc
        _ = ((w₂ ^ p : U) : G) *
            (((w₂ ^ p : U) : G)⁻¹ *
              step4Conj (((w₁⁻¹) ^ k : U) : G) (s₃ : G) *
              (w₂ : G)) * (w₂ : G)⁻¹ := by group
        _ = ((w₂ ^ p : U) : G) * (w₂ : G)⁻¹ := by
          rw [hinnerOne]
          group
    calc
      ((w₂ ^ k : U) : G) =
          ((w₂ ^ p : U) : G) * (w₂ : G)⁻¹ := by
        rw [← hpk, pow_succ]
        simp only [Subgroup.coe_mul]
        group
      _ = _ := hcword.symm
  have hw₁invPow : (w₁⁻¹) ^ k = 1 := by
    have hword :
        (s₃ : G)⁻¹ * ((((w₁⁻¹) ^ k : U) : G)) * (s₃ : G) ∈ U := by
      change
        step4Conj (((w₁⁻¹) ^ k : U) : G) (s₃ : G) ∈ U
      rw [← hw₂pow]
      exact U.pow_mem w₂.property k
    rcases h.not_splitU hPH hUH hsemi hUP hcardF hcardU hcop
      (P0.inv_mem s₃.property) s₃.property
      (U.pow_mem (U.inv_mem w₁.property) k) hword with htriv | htriv
    · exact (hs₃ne (inv_eq_one.mp htriv.1)).elim
    · apply Subtype.ext
      exact htriv.1
  have hw₁inv : w₁⁻¹ = 1 := w_id w₁⁻¹ hw₁invPow
  have hw₁ : w₁ = 1 := inv_eq_one.mp hw₁inv
  have hw₂powOne : w₂ ^ k = 1 := by
    apply Subtype.ext
    change ((w₂ ^ k : U) : G) = (1 : G)
    simp only [Subgroup.coe_pow]
    rw [hw₂pow, hw₁]
    simp [step4Conj]
  have hw₂ : w₂ = 1 := w_id w₂ hw₂powOne
  simpa only [t, hw₁, hw₂, hw₃, Subgroup.coe_one,
    one_mul, mul_one] using hds2

/-- Projecting the reduced identity to the `P₀` factor of `Q ⋊ P₀`
gives the source relation `s₃s₁s₂ = 1`. -/
private theorem step4_s3_s1_s2_eq_one
    [Finite G] {Q : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] [Algebra (ZMod p) h.F]
    (hcardP : Nat.card P = p ^ q)
    (hQ : IsElementaryAbelianGroup q Q)
    (hnormQ : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hqp : q < p)
    {y : G} (hy : y ∈ ⁅Q, P0⁆)
    {s₁ s₂ s₃ : P0}
    (hred :
      h.appendixCStep4Conjugator y * (s₂ : G)⁻¹ *
          h.appendixCStep4Conjugator y =
        (s₃ : G) * h.appendixCStep4Conjugator y ^ 2 * (s₁ : G)) :
    (s₃ : G) * (s₁ : G) * (s₂ : G) = 1 := by
  let s : G := h.onePreimage
  let t : G := h.appendixCStep4Conjugator y
  have hyQ : y ∈ Q := sQP0Q hnormQ hy
  let L : Subgroup G := Q ⊔ P0
  let QL : Subgroup L := Q.subgroupOf L
  let P0L : Subgroup L := P0.subgroupOf L
  have hQLcard : Nat.card QL = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show Q ≤ L from le_sup_left)).toEquiv
  have hP0Lcard : Nat.card P0L = Nat.card P0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show P0 ≤ L from le_sup_right)).toEquiv
  have hPp : IsPGroup p P := pP hcardP
  have hP0p : IsPGroup p P0 := hPp.to_le h.p0_le
  have hcopQP0 : (Nat.card Q).Coprime (Nat.card P0) :=
    IsPGroup.coprime_card_of_ne q p (ne_of_lt hqp) Q P0
      hQ.isPGroup hP0p
  have hLnormQ : L ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le Subgroup.le_normalizer hnormQ
  letI : QL.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLnormQ
  have hcomp : QL.IsComplement' P0L := by
    have hdis : Disjoint QL P0L := by
      apply Subgroup.disjoint_of_coprime_natCard
      simpa only [hQLcard, hP0Lcard] using hcopQP0
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
    have htop : QL ⊔ P0L = ⊤ := by
      change Q.subgroupOf L ⊔ P0.subgroupOf L = ⊤
      rw [← Subgroup.subgroupOf_sup
        (show Q ≤ L from le_sup_left) (show P0 ≤ L from le_sup_right)]
      exact Subgroup.subgroupOf_self L
    rw [← Subgroup.normal_mul QL P0L, htop]
    rfl
  let proj : L →* P0L := hcomp.rightProjection
  let yL : L := ⟨y, (show Q ≤ L from le_sup_left) hyQ⟩
  let yQL : QL := ⟨yL, hyQ⟩
  let sL : L :=
    ⟨s, (show P0 ≤ L from le_sup_right) h.onePreimage_mem_p0⟩
  let sP0L : P0L := ⟨sL, h.onePreimage_mem_p0⟩
  let tL : L :=
    ⟨t, L.mul_mem
      (L.mul_mem (L.inv_mem yL.property) sL.property) yL.property⟩
  let s₁L : L := ⟨(s₁ : G), (show P0 ≤ L from le_sup_right) s₁.property⟩
  let s₂L : L := ⟨(s₂ : G), (show P0 ≤ L from le_sup_right) s₂.property⟩
  let s₃L : L := ⟨(s₃ : G), (show P0 ≤ L from le_sup_right) s₃.property⟩
  let s₁P0L : P0L := ⟨s₁L, s₁.property⟩
  let s₂P0L : P0L := ⟨s₂L, s₂.property⟩
  let s₃P0L : P0L := ⟨s₃L, s₃.property⟩
  have hprojY : proj yL = 1 :=
    Subgroup.IsComplement'.rightProjection_apply_left hcomp yQL
  have hprojS : proj sL = sP0L :=
    Subgroup.IsComplement'.rightProjection_apply_right hcomp sP0L
  have hprojS₁ : proj s₁L = s₁P0L :=
    Subgroup.IsComplement'.rightProjection_apply_right hcomp s₁P0L
  have hprojS₂ : proj s₂L = s₂P0L :=
    Subgroup.IsComplement'.rightProjection_apply_right hcomp s₂P0L
  have hprojS₃ : proj s₃L = s₃P0L :=
    Subgroup.IsComplement'.rightProjection_apply_right hcomp s₃P0L
  have htL : tL = yL⁻¹ * sL * yL := by
    apply Subtype.ext
    rfl
  have hprojT : proj tL = sP0L := by
    rw [htL, map_mul, map_mul, map_inv, hprojY, hprojS]
    simp
  have hredL : tL * s₂L⁻¹ * tL = s₃L * tL ^ 2 * s₁L := by
    apply Subtype.ext
    exact hred
  have hredProj := congrArg proj hredL
  simp only [map_mul, map_inv, map_pow, hprojT, hprojS₁,
    hprojS₂, hprojS₃] at hredProj
  letI : IsMulCommutative P := h.isMulCommutative_P
  letI : IsMulCommutative P0L := by
    apply isMulCommutative_iff.mpr
    intro a b
    let aP : P := ⟨((a : L) : G), h.p0_le a.property⟩
    let bP : P := ⟨((b : L) : G), h.p0_le b.property⟩
    apply Subtype.ext
    apply Subtype.ext
    change (aP : G) * (bP : G) = (bP : G) * (aP : G)
    exact congrArg Subtype.val (mul_comm aP bP)
  have hs₂inv : s₂P0L⁻¹ = s₃P0L * s₁P0L := by
    have hp' :
        sP0L ^ 2 * s₂P0L⁻¹ =
          sP0L ^ 2 * (s₃P0L * s₁P0L) := by
      calc
        sP0L ^ 2 * s₂P0L⁻¹ =
            sP0L * s₂P0L⁻¹ * sP0L := by
          simp only [pow_two]
          ac_rfl
        _ = s₃P0L * sP0L ^ 2 * s₁P0L := hredProj
        _ = sP0L ^ 2 * (s₃P0L * s₁P0L) := by ac_rfl
    exact mul_left_cancel hp'
  have hone : s₃P0L * s₁P0L * s₂P0L = 1 := by
    rw [← hs₂inv]
    exact inv_mul_cancel s₂P0L
  exact congrArg (fun z : P0L => (((z : L) : G))) hone

/-- In the coprime decomposition of `Q`, an element of `[Q,P₀]` fixed by
the generator of `P₀` is trivial. -/
private theorem eq_one_of_mem_commutator_fixed_by_onePreimage
    [Finite G] {Q : Subgroup G} {q : ℕ}
    (hQ : IsElementaryAbelianGroup q Q)
    (hnormQ : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hcopQP0 : (Nat.card Q).Coprime (Nat.card P0))
    {x : G} (hxComm : x ∈ ⁅Q, P0⁆)
    (hfix :
      (h.onePreimage : G) * x * (h.onePreimage : G)⁻¹ = x) :
    x = 1 := by
  let s : G := h.onePreimage
  have hsx : Commute s x := by
    rw [Commute]
    calc
      s * x = (s * x * s⁻¹) * s := by group
      _ = x * s := by rw [hfix]
  have hxCent : x ∈ centralizerWithin Q P0 := by
    rw [mem_centralizerWithin]
    refine ⟨sQP0Q hnormQ hxComm, ?_⟩
    intro a ha
    have haZ : a ∈ Subgroup.zpowers s := by
      rw [h.zpowers_onePreimage_eq_p0]
      exact ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haZ
    rw [← hk]
    exact (hsx.zpow_left k).eq
  have hdef := defQ hQ hnormQ hcopQP0
  let xQ : Q := ⟨x, sQP0Q hnormQ hxComm⟩
  have hxQOne : xQ = 1 :=
    Subgroup.disjoint_def.mp hdef.2.disjoint
      (show xQ ∈ (centralizerWithin Q P0).subgroupOf Q from hxCent)
      (show xQ ∈ ((⁅Q, P0⁆ : Subgroup G).subgroupOf Q) from hxComm)
  exact congrArg Subtype.val hxQOne

private theorem step4Conj_mem_appendixCP1
    {y z : G} (hz : z ∈ P0) :
    step4Conj z y ∈ appendixCP1 P0 y := by
  rw [appendixCP1]
  refine ⟨z, hz, ?_⟩
  simp only [step4Conj, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv]

/-- The `Dx`/`Dx1` word argument, expressed through the abelian
conjugation action on `[Q,P₀]`, followed by the source relation `Ds13`. -/
private theorem step4_ds13
    [Finite G] {Q : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] [Algebra (ZMod p) h.F]
    (hcardP : Nat.card P = p ^ q)
    (hQ : IsElementaryAbelianGroup q Q)
    (hnormQ : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hqp : q < p)
    {y : G} (hy : y ∈ ⁅Q, P0⁆)
    {s₁ s₂ s₃ : P0}
    (hred :
      h.appendixCStep4Conjugator y * (s₂ : G)⁻¹ *
          h.appendixCStep4Conjugator y =
        (s₃ : G) * h.appendixCStep4Conjugator y ^ 2 * (s₁ : G))
    (hprod : (s₃ : G) * (s₁ : G) * (s₂ : G) = 1) :
    (s₁ : G) *
        (h.appendixCStep4Conjugator y * step4Conj (s₁ : G) y)⁻¹ =
      (step4Conj (s₃ : G) y * h.appendixCStep4Conjugator y)⁻¹ *
        (s₃ : G) := by
  letI : IsMulCommutative P0 := h.isMulCommutative_P0
  let s : G := h.onePreimage
  let s0 : P0 := ⟨s, h.onePreimage_mem_p0⟩
  let t : G := h.appendixCStep4Conjugator y
  let t₁ : G := step4Conj (s₁ : G) y
  let t₃ : G := step4Conj (s₃ : G) y
  let K : Subgroup G := ⁅Q, P0⁆
  have hKQ : K ≤ Q := sQP0Q hnormQ
  have hP0normK : P0 ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.normalizer_commutator_ge_right Q P0
  let iota : P0 →* Subgroup.normalizer (K : Set G) :=
    Subgroup.inclusion hP0normK
  let rho : P0 →* MulAut K := K.normalizerMonoidHom.comp iota
  have rho_coe (a : P0) (z : K) :
      ((rho a z : K) : G) = (a : G) * (z : G) * (a : G)⁻¹ := by
    simp [rho, iota, Subgroup.normalizerMonoidHom, HSMul.hSMul]
  letI : IsMulCommutative K := by
    apply isMulCommutative_iff.mpr
    intro a b
    let aQ : Q := ⟨(a : G), hKQ a.property⟩
    let bQ : Q := ⟨(b : G), hKQ b.property⟩
    letI : IsMulCommutative Q := hQ.commutative
    apply Subtype.ext
    change (aQ : G) * (bQ : G) = (bQ : G) * (aQ : G)
    exact congrArg Subtype.val (mul_comm aQ bQ)
  let yK : K := ⟨y, hy⟩
  let d : K := yK⁻¹ * rho s0 yK
  let A : P0 := s0 * s₃ * s₁
  let C : P0 := s₃ * s0
  let xK : K := (rho s₃⁻¹ yK)⁻¹ * rho s0 yK *
    (rho (s0 * s₁) yK)⁻¹ * yK
  have hprodP : s₃ * s₁ * s₂ = 1 := by
    apply Subtype.ext
    exact hprod
  have hs₂inv : s₂⁻¹ = s₃ * s₁ := by
    calc
      s₂⁻¹ = (s₃ * s₁ * s₂) * s₂⁻¹ := by rw [hprodP]; simp
      _ = s₃ * s₁ := by group
  have hs12 : s₁ * s₂ = s₃⁻¹ := by
    calc
      s₁ * s₂ = s₃⁻¹ * (s₃ * s₁ * s₂) := by group
      _ = s₃⁻¹ := by rw [hprodP]; simp
  have htailP :
      s₁ * s0⁻¹ * s₂ * s0⁻¹ = s₃⁻¹ * (s0 ^ 2)⁻¹ := by
    calc
      _ = (s₁ * s₂) * (s0 ^ 2)⁻¹ := by
        simp only [pow_two, mul_inv_rev]
        ac_rfl
      _ = s₃⁻¹ * (s0 ^ 2)⁻¹ := by rw [hs12]
  have htail :
      (s₁ : G) * s⁻¹ * (s₂ : G) * s⁻¹ =
        (s₃ : G)⁻¹ * (s ^ 2)⁻¹ := by
    exact congrArg Subtype.val htailP
  have hdcoe : (d : G) = t * s⁻¹ := by
    dsimp only [d]
    change (yK : G)⁻¹ * ((rho s0 yK : K) : G) = t * s⁻¹
    rw [rho_coe]
    dsimp only [t, s, s0, yK,
      FiniteFieldImage.appendixCStep4Conjugator]
    group
  have hAeq : s0 * s₂⁻¹ = A := by
    rw [hs₂inv]
    dsimp only [A]
    ac_rfl
  have hcomm :
      (s₃ : G)⁻¹ * (s ^ 2)⁻¹ = (s ^ 2)⁻¹ * (s₃ : G)⁻¹ := by
    exact congrArg Subtype.val
      (mul_comm s₃⁻¹ (s0 ^ 2)⁻¹)
  have hd0 :
      d * rho (s0 * s₂⁻¹) d = rho s₃ d * rho C d := by
    apply Subtype.ext
    change
      (d : G) * ((rho (s0 * s₂⁻¹) d : K) : G) =
        ((rho s₃ d : K) : G) * ((rho C d : K) : G)
    rw [rho_coe, rho_coe, rho_coe]
    calc
      (d : G) *
          (((s0 * s₂⁻¹ : P0) : G) * (d : G) *
            ((s0 * s₂⁻¹ : P0) : G)⁻¹) =
        t * (s₂ : G)⁻¹ * t * s⁻¹ * (s₂ : G) * s⁻¹ := by
          change
            (d : G) * (s * (s₂ : G)⁻¹ * (d : G) *
              (s * (s₂ : G)⁻¹)⁻¹) = _
          rw [hdcoe]
          group
      _ = (s₃ : G) * t ^ 2 * (s₁ : G) * s⁻¹ *
          (s₂ : G) * s⁻¹ := by rw [hred]
      _ = (s₃ : G) * t ^ 2 *
          ((s₁ : G) * s⁻¹ * (s₂ : G) * s⁻¹) := by group
      _ = (s₃ : G) * t ^ 2 *
          ((s₃ : G)⁻¹ * (s ^ 2)⁻¹) := by rw [htail]
      _ = (s₃ : G) * t ^ 2 *
          ((s ^ 2)⁻¹ * (s₃ : G)⁻¹) := by
        rw [hcomm]
      _ = (s₃ : G) * t ^ 2 * (s ^ 2)⁻¹ * (s₃ : G)⁻¹ := by group
      _ = ((s₃ : G) * (d : G) * (s₃ : G)⁻¹) *
          ((C : G) * (d : G) * (C : G)⁻¹) := by
        change
          (s₃ : G) * t ^ 2 * (s ^ 2)⁻¹ * (s₃ : G)⁻¹ =
            ((s₃ : G) * (d : G) * (s₃ : G)⁻¹) *
              (((s₃ : G) * s) * (d : G) *
                ((s₃ : G) * s)⁻¹)
        rw [hdcoe]
        simp only [pow_two]
        group
  have hd : d * rho A d = rho s₃ d * rho C d := by
    rw [← hAeq]
    exact hd0
  have hleftOne :
      d * rho A d * (rho s₃ d)⁻¹ * (rho C d)⁻¹ = 1 := by
    rw [hd]
    simp [mul_assoc, mul_comm, mul_left_comm]
  have hdisc := step4_discrepancy_identity rho s0 s₁ s₃ yK
  have hdiffInv : (rho s₃ (rho s0 xK * xK⁻¹))⁻¹ = 1 := by
    rw [← hdisc]
    exact hleftOne
  have hdiffImage : rho s₃ (rho s0 xK * xK⁻¹) = 1 :=
    inv_eq_one.mp hdiffInv
  have hdiff : rho s0 xK * xK⁻¹ = 1 := by
    apply (rho s₃).injective
    simpa only [map_one] using hdiffImage
  have hfixK : rho s0 xK = xK := by
    calc
      rho s0 xK = (rho s0 xK * xK⁻¹) * xK := by group
      _ = xK := by rw [hdiff]; simp
  have hfix : s * (xK : G) * s⁻¹ = (xK : G) := by
    have := congrArg Subtype.val hfixK
    change ((rho s0 xK : K) : G) = (xK : G) at this
    rw [rho_coe] at this
    exact this
  have hPp : IsPGroup p P := pP hcardP
  have hP0p : IsPGroup p P0 := hPp.to_le h.p0_le
  have hcopQP0 : (Nat.card Q).Coprime (Nat.card P0) :=
    IsPGroup.coprime_card_of_ne q p (ne_of_lt hqp) Q P0
      hQ.isPGroup hP0p
  have hx1 : (xK : G) = 1 :=
    h.eq_one_of_mem_commutator_fixed_by_onePreimage
      hQ hnormQ hcopQP0 xK.property hfix
  have hxDef :
      (xK : G) = (s₃ : G)⁻¹ * t₃ * t * (s₁ : G) * (t * t₁)⁻¹ := by
    dsimp only [xK]
    change
      ((rho s₃⁻¹ yK : K) : G)⁻¹ * ((rho s0 yK : K) : G) *
          ((rho (s0 * s₁) yK : K) : G)⁻¹ * (yK : G) = _
    rw [rho_coe, rho_coe, rho_coe]
    dsimp only [yK, s0]
    simp only [Subgroup.coe_inv, Subgroup.coe_mul, inv_inv]
    dsimp only [t, t₁, t₃, s,
      FiniteFieldImage.appendixCStep4Conjugator, step4Conj]
    group
  have hw :
      (s₃ : G)⁻¹ * t₃ * t * (s₁ : G) * (t * t₁)⁻¹ = 1 := by
    rw [← hxDef, hx1]
  calc
    (s₁ : G) * (t * t₁)⁻¹ =
        (t₃ * t)⁻¹ * (s₃ : G) *
          ((s₃ : G)⁻¹ * t₃ * t * (s₁ : G) * (t * t₁)⁻¹) := by
      group
    _ = (t₃ * t)⁻¹ * (s₃ : G) := by rw [hw]; simp

/-- The final Step-3 TI argument: the relation `Ds13` forces the first
middle factor to be `s⁻¹`. -/
private theorem step4_s1_eq_inv_of_relation
    [Finite G] {H : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] [Algebra (ZMod p) h.F]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardF : Nat.card h.F = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hcop : (nU p q).Coprime (p - 1))
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G))
    (hti : ∀ {r : G}, r ∈ appendixCP1 P0 y → r ≠ 1 →
      H ⊓ H.map (MulAut.conj r⁻¹).toMonoidHom = U)
    {s₁ s₃ : P0} (hs₁ne : (s₁ : G) ≠ 1)
    (hrel :
      (s₁ : G) *
          (h.appendixCStep4Conjugator y * step4Conj (s₁ : G) y)⁻¹ =
        (step4Conj (s₃ : G) y *
          h.appendixCStep4Conjugator y)⁻¹ * (s₃ : G)) :
    (s₁ : G) = (h.onePreimage : G)⁻¹ := by
  let t : G := h.appendixCStep4Conjugator y
  let t₁ : G := step4Conj (s₁ : G) y
  let t₃ : G := step4Conj (s₃ : G) y
  let g : G := t * t₁
  let k : G := t₃ * t
  have htP1 : t ∈ appendixCP1 P0 y :=
    h.appendixCStep4Conjugator_mem y
  have ht₁P1 : t₁ ∈ appendixCP1 P0 y :=
    step4Conj_mem_appendixCP1 s₁.property
  have ht₃P1 : t₃ ∈ appendixCP1 P0 y :=
    step4Conj_mem_appendixCP1 s₃.property
  have hgP1 : g ∈ appendixCP1 P0 y :=
    (appendixCP1 P0 y).mul_mem htP1 ht₁P1
  have hkP1 : k ∈ appendixCP1 P0 y :=
    (appendixCP1 P0 y).mul_mem ht₃P1 htP1
  by_contra hs₁inv
  have hg_ne : g ≠ 1 := by
    intro hg
    apply hs₁inv
    have hc :
        (MulAut.conj y⁻¹) ((h.onePreimage : G) * (s₁ : G)) =
          (MulAut.conj y⁻¹) 1 := by
      dsimp only [g, t, t₁, step4Conj,
        FiniteFieldImage.appendixCStep4Conjugator] at hg ⊢
      simpa only [map_mul, map_one, MulAut.conj_apply, inv_inv] using hg
    have hsprod : (h.onePreimage : G) * (s₁ : G) = 1 :=
      (MulAut.conj y⁻¹).injective hc
    exact eq_inv_of_mul_eq_one_right hsprod
  let r : G := g⁻¹
  have hrP1 : r ∈ appendixCP1 P0 y :=
    (appendixCP1 P0 y).inv_mem hgP1
  have hr_ne : r ≠ 1 := inv_ne_one.mpr hg_ne
  have hfrob := h.frobH hPH hUH hsemi hUP hcardU
  let UH : Subgroup H := U.subgroupOf H
  letI : Nontrivial UH :=
    UH.nontrivial_iff_ne_bot.mpr hfrob.complement_ne_bot
  obtain ⟨uH, huH⟩ := exists_ne (1 : UH)
  let u : U := ⟨((uH : H) : G), uH.property⟩
  have hu : u ≠ 1 := by
    intro hu1
    apply huH
    apply Subtype.ext
    apply Subtype.ext
    simpa [u] using congrArg (fun v : U => (v : G)) hu1
  let w : G := step4Conj (u : G) (s₁ : G)
  let z : G := step4Conj w r
  have hwH : w ∈ H := by
    dsimp only [w, step4Conj]
    exact H.mul_mem
      (H.mul_mem (H.inv_mem (hPH (h.p0_le s₁.property)))
        (hUH u.property))
      (hPH (h.p0_le s₁.property))
  have hzMap : z ∈ H.map (MulAut.conj r⁻¹).toMonoidHom := by
    simpa only [z, step4Conj, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv] using
      Subgroup.mem_map_of_mem (MulAut.conj r⁻¹).toMonoidHom hwH
  have hrelInv :
      g * (s₁ : G)⁻¹ = (s₃ : G)⁻¹ * k := by
    dsimp only [g, k, t, t₁, t₃] at hrel ⊢
    calc
      (h.appendixCStep4Conjugator y * step4Conj (s₁ : G) y) *
          (s₁ : G)⁻¹ =
        ((s₁ : G) *
          (h.appendixCStep4Conjugator y *
            step4Conj (s₁ : G) y)⁻¹)⁻¹ := by group
      _ = ((step4Conj (s₃ : G) y *
          h.appendixCStep4Conjugator y)⁻¹ * (s₃ : G))⁻¹ := by
        rw [hrel]
      _ = (s₃ : G)⁻¹ *
          (step4Conj (s₃ : G) y *
            h.appendixCStep4Conjugator y) := by group
  have hrelGK : (s₁ : G) * g⁻¹ = k⁻¹ * (s₃ : G) := by
    dsimp only [g, k, t, t₁, t₃]
    exact hrel
  have hkuU : k * (u : G) * k⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (hP1normU hkP1) (u : G)).mp
      u.property
  have hzH : z ∈ H := by
    have hzEq :
        z = (s₃ : G)⁻¹ * (k * (u : G) * k⁻¹) * (s₃ : G) := by
      dsimp only [z, w, r, step4Conj]
      rw [inv_inv]
      calc
        g * ((s₁ : G)⁻¹ * (u : G) * (s₁ : G)) * g⁻¹ =
            (g * (s₁ : G)⁻¹) * (u : G) *
              ((s₁ : G) * g⁻¹) := by group
        _ = ((s₃ : G)⁻¹ * k) * (u : G) *
              (k⁻¹ * (s₃ : G)) := by rw [hrelInv, hrelGK]
        _ = (s₃ : G)⁻¹ * (k * (u : G) * k⁻¹) *
              (s₃ : G) := by group
    rw [hzEq]
    exact H.mul_mem
      (H.mul_mem (H.inv_mem (hPH (h.p0_le s₃.property)))
        (hUH hkuU))
      (hPH (h.p0_le s₃.property))
  have hzU : z ∈ U := by
    rw [← hti hrP1 hr_ne]
    exact ⟨hzH, hzMap⟩
  have hwU : w ∈ U := by
    have hzEq : z = g * w * g⁻¹ := by
      dsimp only [z, r, step4Conj]
      rw [inv_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hP1normU hgP1) w).mpr
      (by simpa only [hzEq] using hzU)
  rcases h.not_splitU hPH hUH hsemi hUP hcardF hcardU hcop
      (P0.inv_mem s₁.property) s₁.property u.property
      (by simpa only [w, step4Conj] using hwU) with htriv | htriv
  · exact (hs₁ne htriv.2).elim
  · exact (hu (by apply Subtype.ext; exact htriv.1)).elim

/-- Bender--Glauberman Appendix C.3, Step 4.  All hypotheses are the
structural data used by the source proof; the conclusion directly
constructs the previously named one-step obligation. -/
theorem BGappendixC3_step4
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Finite G]
    {H P P0 U Q : Subgroup G}
    (h : FiniteFieldImage P P0 U)
    [Algebra (ZMod p) h.F]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardP : Nat.card P = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hcop : (nU p q).Coprime (p - 1))
    (hQ : IsElementaryAbelianGroup q Q)
    (hnormQ : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hqp : q < p) :
    BGappendixC3Step4Obligation
      (p := p) (H := H) (Q := Q) h := by
  intro y hy hP1normU hti
  intro a haE
  have hcardF : Nat.card h.F = p ^ q :=
    h.natCard_P_eq_field.symm.trans hcardP
  obtain ⟨b, hb⟩ :=
    (h.im_psi hcardP hcardU (2 - h.psiValue a)).2 haE.2
  have hab : h.psiValue a + h.psiValue b = 2 := by
    rw [hb]
    ring
  obtain ⟨u₂, s₂, v₂, r₂⟩ :=
    h.exists_step4SUs hPH hUH hsemi hUP hcardF hcardU hcop
      y hP1normU 3 (a * b⁻¹) 2 1
  obtain ⟨u₁, s₁, v₁, r₁⟩ :=
    h.exists_step4SUs hPH hUH hsemi hUP hcardF hcardU hcop
      y hP1normU 1 a⁻¹ 3 2
  obtain ⟨u₃, s₃, v₃, r₃⟩ :=
    h.exists_step4SUs hPH hUH hsemi hUP hcardF hcardU hcop
      y hP1normU 2 b 1 3
  have hred := h.step4_reduced_s2def hPH hUH hsemi hUP hcardF
    hcardU hcop hQ hnormQ hqp y hy hP1normU hti hab r₁ r₂ r₃
  have hprod :=
    h.step4_s3_s1_s2_eq_one hcardP hQ hnormQ hqp hy hred
  have hDs13 :=
    h.step4_ds13 hcardP hQ hnormQ hqp hy hred hprod
  have hs₁ne : (s₁ : G) ≠ 1 :=
    r₁.middle_ne_one h hPH hUH hsemi hUP hcardF hcardU hcop
      y hP1normU (by right; rfl)
  have hs₁inv := h.step4_s1_eq_inv_of_relation hPH hUH hsemi hUP
    hcardF hcardU hcop y hP1normU hti hs₁ne hDs13
  let c : U := h.appendixCStep4Transform y hP1normU a
  let t : G := h.appendixCStep4Conjugator y
  have hc : (c : G) = step4Conj ((a⁻¹ : U) : G) (t ^ 3) := by
    dsimp only [c]
    rw [h.appendixCStep4Transform_apply]
    exact h.appendixCStep4Action_pow_apply_step4Conj
      y hP1normU 3 a⁻¹
  have hmod := r₁.u_mul_v_eq h hPH hUH hsemi hUP y hP1normU
  have hu₁ : (u₁ : G) = (c : G) * (v₁ : G)⁻¹ := by
    rw [← hc] at hmod
    calc
      (u₁ : G) = ((u₁ : G) * (v₁ : G)) * (v₁ : G)⁻¹ := by group
      _ = (c : G) * (v₁ : G)⁻¹ := by rw [← hmod]
  have hword := r₁.word_eq
  simp only [pow_one] at hword
  rw [← hc, hs₁inv] at hword
  have hgroup :
      (h.onePreimage : G) ^ 2 =
        (v₁ : G)⁻¹ * (h.onePreimage : G) * (v₁ : G) *
          ((c : G)⁻¹ * (h.onePreimage : G) * (c : G)) := by
    calc
      (h.onePreimage : G) ^ 2 =
          ((h.onePreimage : G) * (c : G) *
            ((h.onePreimage : G) ^ 2)⁻¹)⁻¹ *
            (h.onePreimage : G) * (c : G) := by group
      _ = ((u₁ : G) * (h.onePreimage : G)⁻¹ * (v₁ : G))⁻¹ *
          (h.onePreimage : G) * (c : G) := by rw [hword]
      _ = (v₁ : G)⁻¹ * (h.onePreimage : G) * (v₁ : G) *
          ((c : G)⁻¹ * (h.onePreimage : G) * (c : G)) := by
        rw [hu₁]
        group
  let sP : P := h.onePreimage
  have hgroupP :
      sP ^ 2 = rightConjugate P U hUP sP v₁ *
        rightConjugate P U hUP sP c := by
    apply Subtype.ext
    change (sP : G) ^ 2 =
      ((rightConjugate P U hUP sP v₁ : P) : G) *
        ((rightConjugate P U hUP sP c : P) : G)
    simpa only [sP, coe_rightConjugate] using hgroup
  have hsum : h.psiValue c + h.psiValue v₁ = 2 := by
    have hsigma := congrArg
      (fun z : P => h.sigma (Additive.ofMul z)) hgroupP
    rw [h.sigma_pow, h.sigma_onePreimage, h.sigma_mul,
      h.sigma_rightConjugate, h.sigma_rightConjugate,
      h.sigma_onePreimage, one_mul, one_mul] at hsigma
    calc
      h.psiValue c + h.psiValue v₁ =
          h.psiValue v₁ + h.psiValue c := add_comm _ _
      _ = 1 + 1 := by simpa only [two_nsmul] using hsigma.symm
      _ = 2 := by norm_num
  show h.psiValue c ∈ normEquationSet (ZMod p) h.F
  refine ⟨(h.im_psi hcardP hcardU (h.psiValue c)).1 ⟨c, rfl⟩, ?_⟩
  have htwo : 2 - h.psiValue c = h.psiValue v₁ := by
    rw [← hsum]
    ring
  rw [htwo]
  exact (h.im_psi hcardP hcardU (h.psiValue v₁)).1 ⟨v₁, rfl⟩

end FiniteFieldImage

end

end Submission.OddOrder.BG.AppendixC
