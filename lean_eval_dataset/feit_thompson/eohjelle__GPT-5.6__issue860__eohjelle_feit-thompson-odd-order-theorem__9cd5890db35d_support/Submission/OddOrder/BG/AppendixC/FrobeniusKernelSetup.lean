import Submission.OddOrder.BG.AppendixC.FiniteFieldUnitDecomposition
import Submission.OddOrder.BG.AppendixC.ElementaryAbelianDecomposition
import Submission.OddOrder.BG.Section03.FrobeniusBasic
import Mathlib.Tactic.Group

/-!
# The Frobenius-kernel setup in Bender--Glauberman Appendix C

This file ports `BGappendixC.v`, lines 208--239 (Remarks IX--XI).  The
faithful finite-field action makes `H = P ⋊ U` a Frobenius group.  The
elementary-abelian `q`-group `Q` is cross-prime to the `p`-group `P`, and
the coprime action of `P₀` splits `Q` into its fixed subgroup and its mixed
commutator.  Finally, a conjugator normalizing `U` can be chosen in that
mixed commutator.

As elsewhere in the Lean port, a decomposition inside `H` is expressed
using `P.subgroupOf H` and `U.subgroupOf H`.  Right conjugation is written
as `S.map (MulAut.conj y⁻¹).toMonoidHom`, matching MathComp's convention
`S :^ y = y⁻¹ S y`.
-/

namespace Submission.OddOrder.BG.AppendixC

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section03
open scoped IsMulCommutative commutatorElement

noncomputable section

universe u v

variable {G : Type u} [Group G] [Finite G]
variable {H P P0 U Q : Subgroup G}

/-! ### Remark IX: the finite-field semidirect product is Frobenius -/

/-- The geometric-series order occurring in Appendix C is nontrivial for
prime parameters. -/
private theorem one_lt_nU_of_primes {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) : 1 < nU p q := by
  have hpTwo : 2 ≤ p := hp.two_le
  have htwo : 2 ≤ q := hq.two_le
  have hmono : nU p 2 ≤ nU p q := by
    unfold nU
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono htwo)
    intro i _ _
    exact Nat.zero_le _
  have hsmall : 1 < nU p 2 := by
    simp only [nU, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one]
    omega
  exact hsmall.trans_le hmono

namespace FiniteFieldImage

variable (hfield : FiniteFieldImage P P0 U)

include hfield

/-- Faithfulness of the unit-valued finite-field action says that
conjugation by a nonidentity element of `U` fixes no nonidentity element of
`P`.  This is the semiregularity calculation in the proof of Coq's
`frobH`.
-/
theorem fixedPointFree_conjugation
    (hUP : U ≤ Subgroup.normalizer (P : Set G)) :
    ∀ u : U, u ≠ 1 → ∀ x : P,
      (u : G) * (x : G) * (u : G)⁻¹ = (x : G) → x = 1 := by
  intro u hu x hfix
  have hcomm : (u : G) * (x : G) = (x : G) * (u : G) := by
    calc
      (u : G) * (x : G) =
          ((u : G) * (x : G) * (u : G)⁻¹) * (u : G) := by group
      _ = (x : G) * (u : G) := by rw [hfix]
  have hright : rightConjugate P U hUP x u = x := by
    apply Subtype.ext
    rw [coe_rightConjugate]
    calc
      (u : G)⁻¹ * (x : G) * (u : G) =
          (u : G)⁻¹ * ((x : G) * (u : G)) := by rw [mul_assoc]
      _ = (u : G)⁻¹ * ((u : G) * (x : G)) := by rw [hcomm]
      _ = (x : G) := by simp
  have hfieldEq :
      hfield.sigma (Additive.ofMul x) =
        hfield.sigma (Additive.ofMul x) * hfield.psiValue u := by
    simpa only [hright] using hfield.sigma_rightConjugate hUP x u
  have hprod :
      hfield.sigma (Additive.ofMul x) * (hfield.psiValue u - 1) = 0 := by
    rw [mul_sub, mul_one, sub_eq_zero]
    exact hfieldEq.symm
  rcases mul_eq_zero.mp hprod with hxzero | hpsi
  · have hxadd : Additive.ofMul x = Additive.ofMul (1 : P) := by
      apply hfield.sigma.injective
      simpa only [hfield.sigma_one] using hxzero
    exact congrArg Additive.toMul hxadd
  · have hpsiOne : hfield.psiValue u = hfield.psiValue 1 := by
      simpa only [sub_eq_zero, hfield.psiValue_one] using hpsi
    exact (hu (hfield.psiValue_injective hpsiOne)).elim

/-- Bender--Glauberman Appendix C, Remark IX (`BGappendixC.v: frobH`).

The semidirect decomposition is stated inside `H`.  The nontriviality of
the kernel comes from the field image, and that of the complement from its
geometric-series order.
-/
theorem frobH
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardU : Nat.card U = nU p q) :
    IsFrobeniusDecomposition (P.subgroupOf H) (U.subgroupOf H) := by
  let PH : Subgroup H := P.subgroupOf H
  let UH : Subgroup H := U.subgroupOf H

  have hHnormP : H ≤ Subgroup.normalizer (P : Set G) := by
    intro a haH
    let aH : H := ⟨a, haH⟩
    obtain ⟨⟨x, y⟩, hxy⟩ := hsemi.2 aH
    have hxyG : a = ((x : H) : G) * ((y : H) : G) := by
      exact (congrArg (fun z : H ↦ (z : G)) hxy).symm
    rw [hxyG]
    exact (Subgroup.normalizer (P : Set G)).mul_mem
      (Subgroup.le_normalizer x.property) (hUP y.property)
  letI : PH.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHnormP

  have hPne : PH ≠ ⊥ := by
    intro hbot
    let sH : H := ⟨(hfield.onePreimage : G), hPH hfield.onePreimage.property⟩
    have hsPH : sH ∈ PH := hfield.onePreimage.property
    have hsOne : sH = 1 := by
      rw [hbot] at hsPH
      exact Subgroup.mem_bot.mp hsPH
    apply hfield.onePreimage_ne_one
    apply Subtype.ext
    exact congrArg (fun z : H ↦ (z : G)) hsOne

  have hUne : UH ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv,
      hcardU]
    exact one_lt_nU_of_primes Fact.out Fact.out

  have hfixed : ∀ u : UH, u ≠ 1 → ∀ x : PH,
      (u : H) * (x : H) * (u : H)⁻¹ = (x : H) → x = 1 := by
    intro u hu x hx
    let uU : U := ⟨((u : H) : G), u.property⟩
    let xP : P := ⟨((x : H) : G), x.property⟩
    have huU : uU ≠ 1 := by
      intro huOne
      have huG : (uU : G) = (1 : G) :=
        congrArg (fun z : U ↦ (z : G)) huOne
      apply hu
      apply Subtype.ext
      apply Subtype.ext
      exact huG
    have hxG : (uU : G) * (xP : G) * (uU : G)⁻¹ = (xP : G) :=
      congrArg (fun z : H ↦ (z : G)) hx
    have hxOne : xP = 1 := hfield.fixedPointFree_conjugation hUP uU huU xP hxG
    have hxGOne : (xP : G) = (1 : G) :=
      congrArg (fun z : P ↦ (z : G)) hxOne
    apply Subtype.ext
    apply Subtype.ext
    exact hxGOne

  exact
    { isComplement := by simpa only [PH, UH] using hsemi
      kernel_normal := inferInstance
      kernel_ne_bot := hPne
      complement_ne_bot := hUne
      fixedPointFree := hfixed }

end FiniteFieldImage

/-! ### The cross-prime facts preceding Remark X -/

/-- Source fact `p'q`: strict inequality of the prime parameters makes
them distinct. -/
theorem q_ne_p {p q : ℕ} (hqp : q < p) : q ≠ p :=
  hqp.ne

/-- Source fact `cQQ`: an elementary-abelian group is commutative. -/
theorem cQQ {q : ℕ} (hQ : IsElementaryAbelianGroup q Q) :
    IsMulCommutative Q :=
  hQ.commutative

/-- Source fact `p'Q`: a `q`-group has order prime to the distinct prime
`p`. -/
theorem pPrimeQ {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hQ : IsElementaryAbelianGroup q Q) (hqp : q ≠ p) :
    Nat.Coprime p (Nat.card Q) := by
  obtain ⟨n, hn⟩ := hQ.isPGroup.exists_card_eq
  rw [hn]
  exact ((Nat.coprime_primes Fact.out Fact.out).mpr hqp.symm).pow_right n

/-- Source fact `pP`: the order formula for `P` makes it a `p`-group. -/
theorem pP {p q : ℕ} (hcardP : Nat.card P = p ^ q) : IsPGroup p P :=
  IsPGroup.of_card hcardP

/-- Source fact `coQP`: the elementary-abelian `q`-group and the
cross-prime `p`-group have coprime orders. -/
theorem coQP {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hQ : IsElementaryAbelianGroup q Q) (hP : IsPGroup p P)
    (hqp : q ≠ p) :
    Nat.Coprime (Nat.card Q) (Nat.card P) :=
  IsPGroup.coprime_card_of_ne q p hqp Q P hQ.isPGroup hP

/-- Source fact `sQP0Q`: normalization of `Q` by `P₀` puts the mixed
commutator inside `Q`. -/
theorem sQP0Q (hnorm : P0 ≤ Subgroup.normalizer (Q : Set G)) :
    ⁅Q, P0⁆ ≤ Q := by
  have hcomm : ⁅P0, Q⁆ ≤ Q :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hnorm
  simpa only [Subgroup.commutator_comm Q P0] using hcomm

/-! ### Remarks X and XI -/

/-- Bender--Glauberman Appendix C, Remark X (`BGappendixC.v: defQ`).

This gives both the ambient factorization
`C_Q(P₀) ⋅ [Q,P₀] = Q` and unique factorization after restricting the
two factors to `Q`.
-/
theorem defQ {q : ℕ}
    (hQ : IsElementaryAbelianGroup q Q)
    (hnorm : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hcop : (Nat.card Q).Coprime (Nat.card P0)) :
    centralizerWithin Q P0 ⊔ ⁅Q, P0⁆ = Q ∧
      ((centralizerWithin Q P0).subgroupOf Q).IsComplement'
        ((⁅Q, P0⁆ : Subgroup G).subgroupOf Q) :=
  elementaryAbelian_centralizer_commutator_decomposition Q P0 hQ hnorm hcop

/-- The source-hypothesis form of `defQ`, deriving coprimality from the
distinct `q`- and `p`-group structures and `P₀ ≤ P`. -/
theorem defQ_of_isPGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hQ : IsElementaryAbelianGroup q Q) (hP : IsPGroup p P)
    (hqp : q ≠ p) (hP0P : P0 ≤ P)
    (hnorm : P0 ≤ Subgroup.normalizer (Q : Set G)) :
    centralizerWithin Q P0 ⊔ ⁅Q, P0⁆ = Q ∧
      ((centralizerWithin Q P0).subgroupOf Q).IsComplement'
        ((⁅Q, P0⁆ : Subgroup G).subgroupOf Q) :=
  elementaryAbelian_centralizer_commutator_decomposition_of_isPGroup
    Q P P0 hQ hP hqp hP0P hnorm

/-- Bender--Glauberman Appendix C, Remark XI
(`BGappendixC.v: nU_P0QP0`).

An existing `Q`-conjugator can be adjusted into `[Q,P₀]` while
preserving the fact that the conjugate of `P₀` normalizes `U`.
-/
theorem nU_P0QP0 {q : ℕ}
    (hQ : IsElementaryAbelianGroup q Q)
    (hnorm : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hcop : (Nat.card Q).Coprime (Nat.card P0))
    (hconj : ∃ y : G, y ∈ Q ∧
      P0.map (MulAut.conj y⁻¹).toMonoidHom ≤
        Subgroup.normalizer (U : Set G)) :
    ∃ y : G, y ∈ ⁅Q, P0⁆ ∧
      P0.map (MulAut.conj y⁻¹).toMonoidHom ≤
        Subgroup.normalizer (U : Set G) := by
  obtain ⟨y, hyQ, hy⟩ := hconj
  exact exists_commutator_conjugator_normalizing
    Q P0 U hQ hnorm hcop hyQ hy

/-- The source-hypothesis form of `nU_P0QP0`, deriving coprimality from
the distinct prime-group structures. -/
theorem nU_P0QP0_of_isPGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hQ : IsElementaryAbelianGroup q Q) (hP : IsPGroup p P)
    (hqp : q ≠ p) (hP0P : P0 ≤ P)
    (hnorm : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hconj : ∃ y : G, y ∈ Q ∧
      P0.map (MulAut.conj y⁻¹).toMonoidHom ≤
        Subgroup.normalizer (U : Set G)) :
    ∃ y : G, y ∈ ⁅Q, P0⁆ ∧
      P0.map (MulAut.conj y⁻¹).toMonoidHom ≤
        Subgroup.normalizer (U : Set G) := by
  obtain ⟨y, hyQ, hy⟩ := hconj
  exact exists_commutator_conjugator_normalizing_of_isPGroup
    Q P P0 U hQ hP hqp hP0P hnorm hyQ hy

end

end Submission.OddOrder.BG.AppendixC
