import Submission.OddOrder.BG.AppendixC.FrobeniusKernelSetup
import Submission.OddOrder.BG.Section03.FrobeniusNormalSubgroup
import Submission.OddOrder.MathlibSupport.PrimeOrderCentralizer
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-!
# The TI intersection in Bender--Glauberman Appendix C.3

This file ports Step 3 of Bender--Glauberman Lemma C.3
(`BGappendixC.v`, lines 513--568).  If `P₁ = P₀ ^ y` normalizes the
Frobenius complement `U`, then every nonidentity `t₁ ∈ P₁` satisfies

`H ∩ H ^ t₁ = U`.

The proof follows the source.  First the finite-field scalar decomposition
makes the action of `U` on `P` irreducible.  Thus a nontrivial intersection
with `P` would force the whole conjugate intersection to equal `H`, making
`t₁` normalize `H`.  Characteristicity of a Frobenius kernel and a Sylow
argument inside `Q ⋊ P₀` then force `P₁ = P₀`, contradicting the
fixed-point-free action on `P`.
-/

namespace Submission.OddOrder.BG.AppendixC

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section03
open scoped IsMulCommutative commutatorElement

noncomputable section

universe u v

variable {G : Type u} [Group G] [Finite G]

/-- MathComp-oriented conjugation of the distinguished prime-line subgroup:
`appendixCP1 P₀ y = P₀ :^ y = y⁻¹ P₀ y`. -/
def appendixCP1 (P0 : Subgroup G) (y : G) : Subgroup G :=
  P0.map (MulAut.conj y⁻¹).toMonoidHom

namespace FiniteFieldImage

variable {H P P0 U Q : Subgroup G} (hfield : FiniteFieldImage P P0 U)

include hfield

private theorem sigma_ne_zero_iff (x : P) :
    hfield.sigma (Additive.ofMul x) ≠ 0 ↔ x ≠ 1 := by
  constructor
  · intro hx hx1
    apply hx
    simp [hx1]
  · intro hx hsigma
    apply hx
    have heq :
        hfield.sigma (Additive.ofMul x) =
          hfield.sigma (Additive.ofMul (1 : P)) := by
      simpa using hsigma
    exact congrArg Additive.toMul (hfield.sigma.injective heq)

/-- The faithful scalar action in Appendix C is irreducible on the additive
group `P`: every nontrivial `U`-invariant subgroup is all of `P`.

This is the `irrPU` subproof in Step 3.  The full unit-group decomposition
is used exactly as in the source: the scalar carrying one nonzero vector to
another is a product of a `U`-scalar and a prime-field scalar. -/
theorem scalarAction_irreducible
    {p q : ℕ} [Fact p.Prime] [Algebra (ZMod p) hfield.F]
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardF : Nat.card hfield.F = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hcop : (nU p q).Coprime (p - 1))
    {V : Subgroup G} (hVP : V ≤ P)
    (hVU : U ≤ Subgroup.normalizer (V : Set G))
    (hVne : V ≠ ⊥) :
    V = P := by
  apply le_antisymm hVP
  intro x hxP
  by_cases hxOne : x = 1
  · simpa [hxOne] using V.one_mem

  letI : Nontrivial V := V.nontrivial_iff_ne_bot.mpr hVne
  obtain ⟨zV, hzVne⟩ := exists_ne (1 : V)
  let zP : P := ⟨(zV : G), hVP zV.property⟩
  let xP : P := ⟨x, hxP⟩
  have hzPne : zP ≠ 1 := by
    intro hz
    apply hzVne
    apply Subtype.ext
    exact congrArg (fun a : P ↦ (a : G)) hz
  have hxPne : xP ≠ 1 := by
    intro hx
    apply hxOne
    exact congrArg (fun a : P ↦ (a : G)) hx
  have hz0 : hfield.sigma (Additive.ofMul zP) ≠ 0 :=
    (sigma_ne_zero_iff hfield zP).2 hzPne
  have hx0 : hfield.sigma (Additive.ofMul xP) ≠ 0 :=
    (sigma_ne_zero_iff hfield xP).2 hxPne

  let w : hfield.Fˣ := Units.mk0
    (hfield.sigma (Additive.ofMul xP) *
      (hfield.sigma (Additive.ofMul zP))⁻¹)
    (mul_ne_zero hx0 (inv_ne_zero hz0))
  have hunits := hfield.defFU hcardF hcardU hcop
  obtain ⟨⟨a, b⟩, hab⟩ := hunits.2 w
  obtain ⟨u, hu⟩ := a.property
  have hbline : ((b : hfield.Fˣ) : hfield.F) ∈
      primeAdditiveLine hfield.F :=
    hfield.val_mem_primeAdditiveLine_of_mem_primeFieldUnitRange b.property
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hbline

  let c : P := rightConjugate P U hUP zP u
  have hcV : (c : G) ∈ V := by
    rw [show (c : G) = (u : G)⁻¹ * (zP : G) * (u : G) by
      simpa only [c] using coe_rightConjugate P U hUP zP u]
    exact (Subgroup.mem_normalizer_iff''.mp (hVU u.property) (zV : G)).mp
      zV.property

  have habval :
      hfield.psiValue u * ((b : hfield.Fˣ) : hfield.F) =
        hfield.sigma (Additive.ofMul xP) *
          (hfield.sigma (Additive.ofMul zP))⁻¹ := by
    have hua : hfield.psiValue u = ((a : hfield.Fˣ) : hfield.F) := by
      simpa [psiValue] using congrArg Units.val hu
    have habv := congrArg Units.val hab
    simpa [w, hua] using habv
  have hsigmax :
      hfield.sigma (Additive.ofMul xP) =
        k • hfield.sigma (Additive.ofMul c) := by
    rw [hfield.sigma_rightConjugate hUP zP u]
    calc
      hfield.sigma (Additive.ofMul xP) =
          (hfield.sigma (Additive.ofMul xP) *
              (hfield.sigma (Additive.ofMul zP))⁻¹) *
            hfield.sigma (Additive.ofMul zP) := by
              rw [mul_assoc, inv_mul_cancel₀ hz0, mul_one]
      _ = (hfield.psiValue u * ((b : hfield.Fˣ) : hfield.F)) *
            hfield.sigma (Additive.ofMul zP) := by rw [← habval]
      _ = k • (hfield.sigma (Additive.ofMul zP) *
            hfield.psiValue u) := by
              rw [← hk, zsmul_eq_mul]
              ring

  let VP : AddSubgroup (Additive P) := (V.subgroupOf P).toAddSubgroup
  let W : AddSubgroup hfield.F := VP.map hfield.sigma.toAddMonoidHom
  have hcW : hfield.sigma (Additive.ofMul c) ∈ W := by
    refine ⟨Additive.ofMul c, ?_, rfl⟩
    exact hcV
  have hxW : hfield.sigma (Additive.ofMul xP) ∈ W := by
    rw [hsigmax]
    exact W.zsmul_mem hcW k
  obtain ⟨z, hzVP, hz⟩ := hxW
  have hzx : z = Additive.ofMul xP :=
    hfield.sigma.injective hz
  change Additive.ofMul xP ∈ VP
  rw [← hzx]
  exact hzVP

end FiniteFieldImage

/-! ### Frobenius-kernel characteristicity inside an ambient normalizer -/

/-- An external element normalizing a finite Frobenius group normalizes its
Frobenius kernel.  This is the Mathlib-native replacement for the source's
`normal_Hall_pcore` step. -/
theorem frobeniusKernel_le_normalizer_of_le_normalizer
    {H P U : Subgroup G} (hPH : P ≤ H)
    (hfrob : IsFrobeniusDecomposition (P.subgroupOf H) (U.subgroupOf H)) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (P : Set G) := by
  intro g hg
  let gN : Subgroup.normalizer (H : Set G) := ⟨g, hg⟩
  let e : MulAut H := H.normalizerMonoidHom gN
  let PH : Subgroup H := P.subgroupOf H
  let N : Subgroup H := PH.map e.toMonoidHom
  letI : N.Normal :=
    Subgroup.Normal.map hfrob.kernel_normal e.toMonoidHom e.surjective
  have hcardN : Nat.card N = Nat.card PH := by
    exact Subgroup.card_map_of_injective (K := PH) e.injective
  have hNPH : N = PH := by
    rcases hfrob.normal_le_kernel_or_kernel_le (N := N) with hle | hle
    · exact Subgroup.eq_of_le_of_card_ge hle hcardN.ge
    · exact (Subgroup.eq_of_le_of_card_ge hle hcardN.le).symm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hxP, rfl⟩
    let xPH : PH := ⟨⟨x, hPH hxP⟩, hxP⟩
    have hex : e (xPH : H) ∈ N :=
      Subgroup.mem_map_of_mem e.toMonoidHom xPH.property
    rw [hNPH] at hex
    have heval : ((e (xPH : H) : H) : G) = g * x * g⁻¹ := by
      rfl
    change ((e (xPH : H) : H) : G) ∈ P at hex
    rwa [heval] at hex
  · exact (Subgroup.card_map_of_injective (K := P)
      (MulAut.conj g).injective).ge

/-! ### The group-theoretic Step 3 argument -/

/-- The group-theoretic core of Step 3, with irreducibility supplied as a
hypothesis. -/
theorem tiH_P1_of_irreducible
    {H P P0 U Q : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hfrob : IsFrobeniusDecomposition
      (P.subgroupOf H) (U.subgroupOf H))
    (hPp : IsPGroup p P) (hQq : IsPGroup q Q)
    (hqp : q ≠ p) (hP0P : P0 ≤ P)
    (hnormQ : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hcardP0 : Nat.card P0 = p)
    (hirr : ∀ V : Subgroup G, V ≤ P →
      U ≤ Subgroup.normalizer (V : Set G) → V ≠ ⊥ → V = P)
    (y : G) (hyQ : y ∈ Q)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G))
    {t1 : G} (ht1P1 : t1 ∈ appendixCP1 P0 y)
    (ht1ne : t1 ≠ 1) :
    H ⊓ H.map (MulAut.conj t1⁻¹).toMonoidHom = U := by
  let P1 : Subgroup G := appendixCP1 P0 y
  let Ht : Subgroup G := H.map (MulAut.conj t1⁻¹).toMonoidHom
  let X : Subgroup G := H ⊓ Ht
  let V : Subgroup G := P ⊓ X

  have ht1normU : t1 ∈ Subgroup.normalizer (U : Set G) :=
    hP1normU ht1P1
  have hUconj : U.map (MulAut.conj t1⁻¹).toMonoidHom = U := by
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (U : Set G)).inv_mem ht1normU)
  have hUX : U ≤ X := by
    apply le_inf hUH
    change U ≤ Ht
    calc
      U = U.map (MulAut.conj t1⁻¹).toMonoidHom := hUconj.symm
      _ ≤ H.map (MulAut.conj t1⁻¹).toMonoidHom :=
        Subgroup.map_mono hUH

  have hVU : U ≤ Subgroup.normalizer (V : Set G) := by
    calc
      U ≤ Subgroup.normalizer (P : Set G) ⊓
          Subgroup.normalizer (X : Set G) :=
        le_inf hUP (hUX.trans Subgroup.le_normalizer)
      _ ≤ Subgroup.normalizer (V : Set G) := by
        simpa only [V] using
          (Subgroup.inf_normalizer_le_normalizer_inf (H := P) (K := X))

  have hXleH : X ≤ H := inf_le_left
  have factor_in_X (x : G) (hxX : x ∈ X) :
      ∃ a : G, a ∈ V ∧ ∃ u : G, u ∈ U ∧ x = a * u := by
    let xH : H := ⟨x, hXleH hxX⟩
    obtain ⟨⟨aH, uH⟩, hau⟩ := hfrob.isComplement.2 xH
    let a : G := ((aH : H) : G)
    let u : G := ((uH : H) : G)
    have hxau : x = a * u :=
      (congrArg (fun z : H ↦ (z : G)) hau).symm
    have huX : u ∈ X := hUX uH.property
    have haX : a ∈ X := by
      rw [hxau] at hxX
      have := X.mul_mem hxX (X.inv_mem huX)
      simpa [a, u, mul_assoc] using this
    exact ⟨a, ⟨aH.property, haX⟩, u, uH.property, hxau⟩

  by_cases hVbot : V = ⊥
  · apply le_antisymm
    · intro x hxX
      obtain ⟨a, haV, u, huU, hx⟩ := factor_in_X x hxX
      have haOne : a = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← hVbot]
        exact haV
      simpa [hx, haOne] using huU
    · exact hUX

  have hVP : V ≤ P := inf_le_left
  have hVP_eq : V = P := hirr V hVP hVU hVbot
  have hPX : P ≤ X := by
    rw [← hVP_eq]
    exact inf_le_right
  have hHX : H ≤ X := by
    intro x hxH
    let xH : H := ⟨x, hxH⟩
    obtain ⟨⟨aH, uH⟩, hau⟩ := hfrob.isComplement.2 xH
    have haX : ((aH : H) : G) ∈ X := hPX aH.property
    have huX : ((uH : H) : G) ∈ X := hUX uH.property
    have hx := X.mul_mem haX huX
    have hauG : ((aH : H) : G) * ((uH : H) : G) = x :=
      congrArg (fun z : H ↦ (z : G)) hau
    rwa [hauG] at hx
  have hXeqH : X = H := le_antisymm hXleH hHX
  have hHtEqH : Ht = H := by
    have hHHt : H ≤ Ht := by
      rw [← hXeqH]
      exact inf_le_right
    exact (Subgroup.eq_of_le_of_card_ge hHHt (by
      rw [show Nat.card Ht = Nat.card H by
        exact Subgroup.card_map_of_injective (K := H)
          (MulAut.conj t1⁻¹).injective])).symm
  have ht1normH : t1 ∈ Subgroup.normalizer (H : Set G) := by
    have ht1inv : t1⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      exact hHtEqH
    simpa only [inv_inv] using
      (Subgroup.normalizer (H : Set G)).inv_mem ht1inv

  have hcardP1 : Nat.card P1 = p := by
    calc
      Nat.card P1 = Nat.card P0 :=
        Subgroup.card_map_of_injective (K := P0)
          (MulAut.conj y⁻¹).injective
      _ = p := hcardP0
  have hP1prime : (Nat.card P1).Prime := by
    rw [hcardP1]
    exact Fact.out
  have hP1normH : P1 ≤ Subgroup.normalizer (H : Set G) := by
    rw [← zpowers_eq_of_mem_subgroup_prime_card P1 hP1prime ht1P1 ht1ne]
    exact Subgroup.zpowers_le.mpr ht1normH
  have hP1normP : P1 ≤ Subgroup.normalizer (P : Set G) :=
    hP1normH.trans
      (frobeniusKernel_le_normalizer_of_le_normalizer hPH hfrob)

  let L : Subgroup G := Q ⊔ P0
  let QL : Subgroup L := Q.subgroupOf L
  let P0L : Subgroup L := P0.subgroupOf L
  have hQLcard : Nat.card QL = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show Q ≤ L from le_sup_left)).toEquiv
  have hP0Lcard : Nat.card P0L = Nat.card P0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show P0 ≤ L from le_sup_right)).toEquiv
  have hP0p : IsPGroup p P0 := hPp.to_le hP0P
  have hcopQP0 : (Nat.card Q).Coprime (Nat.card P0) :=
    IsPGroup.coprime_card_of_ne q p hqp Q P0 hQq hP0p
  have hcopQP : (Nat.card Q).Coprime (Nat.card P) :=
    IsPGroup.coprime_card_of_ne q p hqp Q P hQq hPp
  have hLnormQ : L ≤ Subgroup.normalizer (Q : Set G) := by
    exact sup_le Subgroup.le_normalizer hnormQ
  letI : QL.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLnormQ
  have hQLP0L : QL.IsComplement' P0L := by
    have hdis : Disjoint QL P0L := by
      apply Subgroup.disjoint_of_coprime_natCard
      simpa only [hQLcard, hP0Lcard] using hcopQP0
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
    have htop : QL ⊔ P0L = ⊤ := by
      change Q.subgroupOf L ⊔ P0.subgroupOf L = ⊤
      rw [← Subgroup.subgroupOf_sup
        (show Q ≤ L from le_sup_left) (show P0 ≤ L from le_sup_right)]
      exact Subgroup.subgroupOf_self L
    rw [← Subgroup.normal_mul QL P0L]
    rw [htop]
    rfl

  have hP0Lgroup : IsPGroup p P0L :=
    hP0p.of_equiv
      (Subgroup.subgroupOfEquivOfLe (show P0 ≤ L from le_sup_right)).symm
  have hpNotIndex : ¬ p ∣ P0L.index := by
    rw [hQLP0L.index_eq_card, hQLcard]
    apply (Nat.Prime.coprime_iff_not_dvd Fact.out).mp
    simpa only [hcardP0] using
      (IsPGroup.coprime_card_of_ne p q hqp.symm P0 Q hP0p hQq)
  let S0 : Sylow p L := hP0Lgroup.toSylow hpNotIndex

  have hP1L : P1 ≤ L := by
    rintro x ⟨z, hzP0, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      L.mul_mem (L.mul_mem (L.inv_mem
        ((show Q ≤ L from le_sup_left) hyQ))
        ((show P0 ≤ L from le_sup_right) hzP0))
        ((show Q ≤ L from le_sup_left) hyQ)
  let P1L : Subgroup L := P1.subgroupOf L
  have hP1p : IsPGroup p P1 := hP0p.map (MulAut.conj y⁻¹).toMonoidHom
  have hP1Lgroup : IsPGroup p P1L :=
    hP1p.of_equiv (Subgroup.subgroupOfEquivOfLe hP1L).symm

  have hPcapL : P ⊓ L = P0 := by
    apply le_antisymm
    · intro x hx
      let xL : L := ⟨x, hx.2⟩
      obtain ⟨⟨a, b⟩, hab⟩ := hQLP0L.2 xL
      have hxab : x = ((a : L) : G) * ((b : L) : G) :=
        (congrArg (fun z : L ↦ (z : G)) hab).symm
      have haP : ((a : L) : G) ∈ P := by
        have := P.mul_mem hx.1 (P.inv_mem (hP0P b.property))
        simpa [hxab, mul_assoc] using this
      have haOne : ((a : L) : G) = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← disjoint_iff.mp
          (Subgroup.disjoint_of_coprime_natCard hcopQP)]
        exact ⟨a.property, haP⟩
      rw [hxab, haOne, one_mul]
      exact b.property
    · exact le_inf hP0P le_sup_right

  have hP1normP0 : P1 ≤ Subgroup.normalizer (P0 : Set G) := by
    have hP1normL : P1 ≤ Subgroup.normalizer (L : Set G) :=
      hP1L.trans Subgroup.le_normalizer
    calc
      P1 ≤ Subgroup.normalizer (P : Set G) ⊓
          Subgroup.normalizer (L : Set G) := le_inf hP1normP hP1normL
      _ ≤ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf
      _ = Subgroup.normalizer (P0 : Set G) := by rw [hPcapL]
  have hP1LnormP0L : P1L ≤ Subgroup.normalizer (P0L : Set L) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change ((x : L) : G) ∈ P0 ↔
      ((a : L) : G) * ((x : L) : G) * ((a : L) : G)⁻¹ ∈ P0
    exact Subgroup.mem_normalizer_iff.mp
      (hP1normP0 ha) ((x : L) : G)

  have hP1LS0 : P1L ≤ (S0 : Subgroup L) := by
    have hinf := hP1Lgroup.inf_normalizer_sylow S0
    intro a ha
    have haInf : a ∈ P1L ⊓ Subgroup.normalizer (S0 : Set L) :=
      ⟨ha, hP1LnormP0L ha⟩
    rw [hinf] at haInf
    exact haInf.2
  have hP1P0 : P1 ≤ P0 := by
    intro x hx
    let xL : L := ⟨x, hP1L hx⟩
    have hxP1L : xL ∈ P1L := hx
    have hxS0 : xL ∈ (S0 : Subgroup L) := hP1LS0 hxP1L
    change xL ∈ P0L at hxS0
    change xL ∈ P0L
    exact hxS0
  have hP1eqP0 : P1 = P0 := by
    apply Subgroup.eq_of_le_of_card_ge hP1P0
    rw [hcardP1, hcardP0]
  have hP0normU : P0 ≤ Subgroup.normalizer (U : Set G) := by
    rw [← hP1eqP0]
    exact hP1normU

  have hPUdis : Disjoint P U := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    let xH : H := ⟨x, hPH hx.1⟩
    have hxH : xH ∈ (P.subgroupOf H) ⊓ (U.subgroupOf H) := hx
    have hxBot : xH ∈ (⊥ : Subgroup H) := by
      rw [← disjoint_iff.mp hfrob.disjoint]
      exact hxH
    exact Subgroup.mem_bot.mpr
      (congrArg (fun z : H ↦ (z : G)) (Subgroup.mem_bot.mp hxBot))
  have hcommU : ⁅P0, U⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hP0normU
  have hcommP : ⁅P0, U⁆ ≤ P := by
    rw [Subgroup.commutator_comm P0 U]
    exact (Subgroup.commutator_mono le_rfl hP0P).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hUP)
  have hcommBot : ⁅P0, U⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← disjoint_iff.mp hPUdis]
    exact le_inf hcommP hcommU
  have hP0centU : P0 ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot

  let PH : Subgroup H := P.subgroupOf H
  let UH : Subgroup H := U.subgroupOf H
  letI : Nontrivial UH := UH.nontrivial_iff_ne_bot.mpr hfrob.complement_ne_bot
  obtain ⟨u, hu⟩ := exists_ne (1 : UH)
  have hP0bot : P0 = ⊥ := by
    apply le_bot_iff.mp
    intro x hxP0
    let xPH : PH := ⟨⟨x, hPH (hP0P hxP0)⟩, hP0P hxP0⟩
    have hcomm : (u : H) * (xPH : H) = (xPH : H) * (u : H) := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hP0centU hxP0)
        ((u : H) : G) u.property)
    have hfix : (u : H) * (xPH : H) * (u : H)⁻¹ = (xPH : H) := by
      calc
        (u : H) * (xPH : H) * (u : H)⁻¹ =
            (xPH : H) * (u : H) * (u : H)⁻¹ := by rw [hcomm]
        _ = (xPH : H) := by simp
    have hxOne : xPH = 1 := hfrob.fixedPointFree u hu xPH hfix
    exact Subgroup.mem_bot.mpr
      (congrArg (fun z : PH ↦ ((z : H) : G)) hxOne)
  have hcardOne : Nat.card P0 = 1 := by rw [hP0bot, Subgroup.card_bot]
  exact ((Fact.out : p.Prime).ne_one
    (hcardP0.symm.trans hcardOne)).elim

/-! ### Source-facing finite-field theorem -/

/-- Bender--Glauberman Appendix C, Lemma C.3, Step 3
(`BGappendixC.v: tiH_P1`). -/
theorem FiniteFieldImage.tiH_P1
    {H P P0 U Q : Subgroup G} (hfield : FiniteFieldImage P P0 U)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [Algebra (ZMod p) hfield.F]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardF : Nat.card hfield.F = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hcop : (nU p q).Coprime (p - 1))
    (hQ : IsElementaryAbelianGroup q Q) (hqp : q ≠ p)
    (hnormQ : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hcardP0 : Nat.card P0 = p)
    (y : G) (hyQ : y ∈ Q)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G))
    {t1 : G} (ht1P1 : t1 ∈ appendixCP1 P0 y)
    (ht1ne : t1 ≠ 1) :
    H ⊓ H.map (MulAut.conj t1⁻¹).toMonoidHom = U := by
  have hfrob := hfield.frobH hPH hUH hsemi hUP hcardU
  have hPcard : Nat.card P = p ^ q :=
    hfield.natCard_P_eq_field.trans hcardF
  have hPp : IsPGroup p P := IsPGroup.of_card hPcard
  have hirr : ∀ V : Subgroup G, V ≤ P →
      U ≤ Subgroup.normalizer (V : Set G) → V ≠ ⊥ → V = P := by
    intro V hVP hVU hVne
    exact hfield.scalarAction_irreducible hUP hcardF hcardU hcop
      hVP hVU hVne
  exact tiH_P1_of_irreducible hPH hUH hUP hfrob hPp hQ.isPGroup
    hqp hfield.p0_le hnormQ hcardP0 hirr y hyQ hP1normU ht1P1 ht1ne

end

end Submission.OddOrder.BG.AppendixC
