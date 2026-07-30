import Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect
import Submission.OddOrder.MathlibSupport.CoprimeCommutatorIdempotent
import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Mathlib.Tactic.Group

/-!
# The elementary-abelian decomposition in Appendix C

This is the group-theoretic content of Remarks X and XI in
`BGappendixC.v`.  A coprime action on the elementary-abelian group `Q`
splits `Q` as its `P₀`-fixed subgroup and its mixed commutator.  Consequently
a conjugator in `Q` may be adjusted to lie in the mixed commutator without
changing the conjugate of `P₀` (using the MathComp convention
`P₀ ^ y = y⁻¹ P₀ y`).
-/

namespace Submission.OddOrder.BG.AppendixC

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G]

/-- The fixed subgroup and mixed commutator give the internal direct-product
decomposition of an elementary-abelian group under a coprime action.

The first conjunct is the ambient-subgroup form of
`C_Q(P₀) × [Q,P₀] = Q`; the second records unique factorization inside
the group `Q`.
-/
theorem elementaryAbelian_centralizer_commutator_decomposition
    {q : ℕ} (Q P₀ : Subgroup G)
    (hQ : IsElementaryAbelianGroup q Q)
    (hnorm : P₀ ≤ Subgroup.normalizer (Q : Set G))
    (hcop : (Nat.card Q).Coprime (Nat.card P₀)) :
    centralizerWithin Q P₀ ⊔ ⁅Q, P₀⁆ = Q ∧
      ((centralizerWithin Q P₀).subgroupOf Q).IsComplement'
        ((⁅Q, P₀⁆ : Subgroup G).subgroupOf Q) := by
  classical
  letI : IsMulCommutative Q := hQ.commutative
  let T : Subgroup G := ⁅Q, P₀⁆
  let C : Subgroup G := centralizerWithin Q P₀
  have hTQ : T ≤ Q := by
    have hcomm : ⁅P₀, Q⁆ ≤ Q :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hnorm
    simpa only [T, Subgroup.commutator_comm Q P₀] using hcomm
  have hCQ : C ≤ Q := centralizerWithin_le_left Q P₀
  have hgen : Q ≤ ⁅P₀, Q⁆ ⊔ C :=
    le_commutator_sup_centralizerWithin_of_coprime hnorm hcop
  have hgen' : Q ≤ T ⊔ C := by
    simpa only [T, Subgroup.commutator_comm P₀ Q] using hgen
  have hsup : C ⊔ T = Q := by
    apply le_antisymm
    · exact sup_le hCQ hTQ
    · simpa only [sup_comm] using hgen'

  have hTnorm : P₀ ≤ Subgroup.normalizer (T : Set G) := by
    exact Subgroup.normalizer_commutator_ge_right Q P₀
  have hTcop : (Nat.card T).Coprime (Nat.card P₀) :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hTQ)
  have hidem : ⁅P₀, ⁅P₀, Q⁆⁆ = ⁅P₀, Q⁆ :=
    commutator_commutator_eq_of_coprime hnorm hcop
  have hTperfect : ⁅P₀, T⁆ = T := by
    simpa only [T, Subgroup.commutator_comm Q P₀] using hidem
  letI : IsMulCommutative T := by
    refine ⟨⟨fun x y ↦ ?_⟩⟩
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg Subtype.val
      (mul_comm (⟨(x : G), hTQ x.property⟩ : Q)
        (⟨(y : G), hTQ y.property⟩ : Q))

  have hdisTC : Disjoint (T.subgroupOf Q) (C.subgroupOf Q) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    let xt : T := ⟨((x : Q) : G), hx.1⟩
    have hxC : ((x : Q) : G) ∈ C := hx.2
    have hfix : ∀ a : P₀,
        (a : G) * (xt : G) * (a : G)⁻¹ = (xt : G) := by
      intro a
      calc
        (a : G) * (xt : G) * (a : G)⁻¹ =
            (xt : G) * (a : G) * (a : G)⁻¹ := by
              rw [hxC.2 (a : G) a.property]
        _ = (xt : G) := by simp
    have hxt : xt = 1 :=
      Submission.OddOrder.BG.Section06.fixed_eq_one_of_abelian_perfect_coprime_conjugation
        hTnorm hTcop hTperfect xt hfix
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact congrArg (fun z : T ↦ (z : G)) hxt

  have hsupQ : C.subgroupOf Q ⊔ T.subgroupOf Q = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hCQ hTQ, hsup]
    exact Subgroup.subgroupOf_self Q
  have hcomp : (C.subgroupOf Q).IsComplement' (T.subgroupOf Q) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisTC.symm
    rw [← Subgroup.normal_mul (C.subgroupOf Q) (T.subgroupOf Q), hsupQ]
    rfl
  exact ⟨by simpa only [C, T] using hsup,
    by simpa only [C, T] using hcomp⟩

/-- The Appendix C decomposition when coprimality is supplied by distinct
prime-group structures on `Q` and an overgroup `P ≥ P₀`.-/
theorem elementaryAbelian_centralizer_commutator_decomposition_of_isPGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (Q P P₀ : Subgroup G)
    (hQ : IsElementaryAbelianGroup q Q) (hP : IsPGroup p P)
    (hqp : q ≠ p) (hP₀P : P₀ ≤ P)
    (hnorm : P₀ ≤ Subgroup.normalizer (Q : Set G)) :
    centralizerWithin Q P₀ ⊔ ⁅Q, P₀⁆ = Q ∧
      ((centralizerWithin Q P₀).subgroupOf Q).IsComplement'
        ((⁅Q, P₀⁆ : Subgroup G).subgroupOf Q) := by
  have hcopQP : (Nat.card Q).Coprime (Nat.card P) :=
    IsPGroup.coprime_card_of_ne q p hqp Q P hQ.isPGroup hP
  have hcop : (Nat.card Q).Coprime (Nat.card P₀) :=
    hcopQP.coprime_dvd_right (Subgroup.card_dvd_of_le hP₀P)
  exact elementaryAbelian_centralizer_commutator_decomposition Q P₀ hQ hnorm hcop

/-- Multiplying a conjugator on the left by an element centralizing `P₀`
does not change the MathComp-oriented conjugate `y⁻¹ P₀ y`.-/
private theorem map_conj_inv_mul_centralizer_eq
    (P₀ : Subgroup G) {z t : G}
    (hz : z ∈ Subgroup.centralizer (P₀ : Set G)) :
    P₀.map (MulAut.conj (z * t)⁻¹).toMonoidHom =
      P₀.map (MulAut.conj t⁻¹).toMonoidHom := by
  have hzfix (x : G) (hx : x ∈ P₀) : z⁻¹ * x * z = x := by
    calc
      z⁻¹ * x * z = z⁻¹ * (x * z) := by rw [mul_assoc]
      _ = z⁻¹ * (z * x) := by rw [Subgroup.mem_centralizer_iff.mp hz x hx]
      _ = x := by simp
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc
      t⁻¹ * a * t = t⁻¹ * (z⁻¹ * a * z) * t := by rw [hzfix a ha]
      _ = (z * t)⁻¹ * a * (z * t) := by group
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc
      (z * t)⁻¹ * a * (z * t) = t⁻¹ * (z⁻¹ * a * z) * t := by group
      _ = t⁻¹ * a * t := by rw [hzfix a ha]

/-- Appendix C, Remark XI: a conjugator `y ∈ Q` whose conjugate of `P₀`
normalizes `U` may be replaced by one in the mixed commutator `[Q,P₀]`.

Conjugation is written as `P₀.map (MulAut.conj y⁻¹)` so that it agrees
with MathComp's notation `P₀ :^ y = y⁻¹ P₀ y`.
-/
theorem exists_commutator_conjugator_normalizing
    {q : ℕ} (Q P₀ U : Subgroup G)
    (hQ : IsElementaryAbelianGroup q Q)
    (hnorm : P₀ ≤ Subgroup.normalizer (Q : Set G))
    (hcop : (Nat.card Q).Coprime (Nat.card P₀))
    {y : G} (hyQ : y ∈ Q)
    (hy : P₀.map (MulAut.conj y⁻¹).toMonoidHom ≤
      Subgroup.normalizer (U : Set G)) :
    ∃ y' : G, y' ∈ ⁅Q, P₀⁆ ∧
      P₀.map (MulAut.conj y'⁻¹).toMonoidHom ≤
        Subgroup.normalizer (U : Set G) := by
  let C : Subgroup G := centralizerWithin Q P₀
  let T : Subgroup G := ⁅Q, P₀⁆
  have hcomp : (C.subgroupOf Q).IsComplement' (T.subgroupOf Q) := by
    simpa only [C, T] using
      (elementaryAbelian_centralizer_commutator_decomposition Q P₀ hQ hnorm hcop).2
  let yQ : Q := ⟨y, hyQ⟩
  obtain ⟨⟨z, t⟩, hzt⟩ := hcomp.2 yQ
  let zG : G := ((z : Q) : G)
  let tG : G := ((t : Q) : G)
  have hzC : zG ∈ C := z.property
  have htT : tG ∈ T := t.property
  have hyEq : y = zG * tG := by
    exact (congrArg (fun x : Q ↦ (x : G)) hzt).symm
  have hmap : P₀.map (MulAut.conj y⁻¹).toMonoidHom =
      P₀.map (MulAut.conj tG⁻¹).toMonoidHom := by
    rw [hyEq]
    exact map_conj_inv_mul_centralizer_eq P₀ hzC.2
  refine ⟨tG, by simpa only [T] using htT, ?_⟩
  rw [← hmap]
  exact hy

/-- Prime-group wrapper for `exists_commutator_conjugator_normalizing`, in
the form used by the hypotheses of Appendix C.-/
theorem exists_commutator_conjugator_normalizing_of_isPGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (Q P P₀ U : Subgroup G)
    (hQ : IsElementaryAbelianGroup q Q) (hP : IsPGroup p P)
    (hqp : q ≠ p) (hP₀P : P₀ ≤ P)
    (hnorm : P₀ ≤ Subgroup.normalizer (Q : Set G))
    {y : G} (hyQ : y ∈ Q)
    (hy : P₀.map (MulAut.conj y⁻¹).toMonoidHom ≤
      Subgroup.normalizer (U : Set G)) :
    ∃ y' : G, y' ∈ ⁅Q, P₀⁆ ∧
      P₀.map (MulAut.conj y'⁻¹).toMonoidHom ≤
        Subgroup.normalizer (U : Set G) := by
  have hcopQP : (Nat.card Q).Coprime (Nat.card P) :=
    IsPGroup.coprime_card_of_ne q p hqp Q P hQ.isPGroup hP
  have hcop : (Nat.card Q).Coprime (Nat.card P₀) :=
    hcopQP.coprime_dvd_right (Subgroup.card_dvd_of_le hP₀P)
  exact exists_commutator_conjugator_normalizing Q P₀ U hQ hnorm hcop hyQ hy

end Submission.OddOrder.BG.AppendixC
