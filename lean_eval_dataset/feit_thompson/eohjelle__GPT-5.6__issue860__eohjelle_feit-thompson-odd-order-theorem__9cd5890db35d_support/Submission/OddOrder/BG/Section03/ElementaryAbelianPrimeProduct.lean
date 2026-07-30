import Submission.OddOrder.BG.Section03.PrimeProductRepresentation
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation

/-!
The elementary-abelian reduction in the proof that a semiregular
prime-product group is cyclic.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {A : Type u} [Group A] [Fintype A]
variable {H R : Subgroup A}
variable {p q ell : ℕ}

noncomputable section

local instance : DecidableEq A := Classical.decEq A
local instance : DecidablePred (fun a : A ↦ a ∈ H) := Classical.decPred _
local instance : DecidablePred (fun a : A ↦ a ∈ R) := Classical.decPred _

/-- In the elementary-abelian case of the regular `p*q` lemma, the two Sylow
factors of the acting group centralize one another. -/
theorem elementaryAbelian_primeProduct_sylow_le_centralizer
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Nat.card R = p * q)
    (P : Sylow p R) (Q : Sylow q R)
    [IsMulCommutative H] [Module (ZMod ell) (Additive H)]
    (hell : ell.Prime)
    (hH : H ≠ ⊥)
    (hnorm : R ≤ Subgroup.normalizer (H : Set A))
    (hreg : IsSemiregularConjugation H R)
    (hchar : (Nat.card Q : ZMod ell) ≠ 0) :
    (P : Subgroup R) ≤ Subgroup.centralizer (Q : Set R) := by
  letI : Fact ell.Prime := ⟨hell⟩
  let rhoN := normalizerConjugationRepresentation H ell
  let inclusion : R →* Subgroup.normalizer (H : Set A) :=
    Subgroup.inclusion hnorm
  let rho : _root_.Representation (ZMod ell) R (Additive H) :=
    rhoN.comp inclusion
  have hPcard : Nat.card P = p :=
    sylow_card_eq_left_prime_of_natCard_eq_mul hp hq hpq.ne hcard P
  have hQcard : Nat.card Q = q :=
    sylow_card_eq_left_prime_of_natCard_eq_mul hq hp hpq.ne'
      (hcard.trans (Nat.mul_comm p q)) Q
  have hPne : (P : Subgroup R) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hPcard]
    exact hp.one_lt
  have hQne : (Q : Subgroup R) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hQcard]
    exact hq.one_lt
  have hfix : _root_.Representation.invariants
      (rho.comp (P : Subgroup R).subtype :
        _root_.Representation (ZMod ell) P (Additive H)) = ⊥ := by
    apply le_antisymm
    · intro v hv
      letI : Nontrivial P := P.nontrivial_iff_ne_bot.mpr hPne
      obtain ⟨sP, hsP_ne⟩ := exists_ne (1 : P)
      have hvfix := hv sP
      change rhoN (inclusion (sP : R)) v = v at hvfix
      rw [normalizerConjugationRepresentation_apply] at hvfix
      have hvfix' := congrArg Additive.toMul hvfix
      have hvfix'' := congrArg Subtype.val hvfix'
      change ((sP : R) : A) * (v.toMul : A) * ((sP : R) : A)⁻¹ =
        (v.toMul : A) at hvfix''
      have hsR_ne : (sP : R) ≠ 1 := by
        intro hsOne
        apply hsP_ne
        exact Subtype.ext hsOne
      have hvOne : v.toMul = 1 := hreg (sP : R) hsR_ne v.toMul hvfix''
      exact (Submodule.mem_bot (ZMod ell)).mpr (by
        simpa using congrArg Additive.ofMul hvOne)
    · exact bot_le
  rcases sylow_le_centralizer_or_le_representation_ker
      (G := R) (k := ZMod ell) (V := Additive H)
      hp hq hpq hcard P Q rho hchar hfix with hcentral | hQkernel
  · exact hcentral
  · exfalso
    letI : Nontrivial Q := Q.nontrivial_iff_ne_bot.mpr hQne
    letI : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hH
    obtain ⟨tQ, htQ_ne⟩ := exists_ne (1 : Q)
    obtain ⟨xH, hxH_ne⟩ := exists_ne (1 : H)
    have htker : rho (tQ : R) = 1 :=
      MonoidHom.mem_ker.mp (hQkernel tQ.property)
    have hfixedLinear := LinearMap.congr_fun htker (Additive.ofMul xH)
    change rhoN (inclusion (tQ : R)) (Additive.ofMul xH) =
      Additive.ofMul xH at hfixedLinear
    rw [normalizerConjugationRepresentation_apply] at hfixedLinear
    have hfixedAmbient := congrArg Additive.toMul hfixedLinear
    have hfixedAmbient' := congrArg Subtype.val hfixedAmbient
    change ((tQ : R) : A) * (xH : A) * ((tQ : R) : A)⁻¹ =
      (xH : A) at hfixedAmbient'
    have htR_ne : (tQ : R) ≠ 1 := by
      intro htOne
      apply htQ_ne
      exact Subtype.ext htOne
    exact hxH_ne (hreg (tQ : R) htR_ne xH hfixedAmbient')

end

end Submission.OddOrder.BG.Section03
