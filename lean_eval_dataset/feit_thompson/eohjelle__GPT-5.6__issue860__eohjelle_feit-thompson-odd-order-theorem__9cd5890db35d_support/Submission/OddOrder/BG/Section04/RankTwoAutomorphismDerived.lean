import Submission.OddOrder.BG.Section01.CriticalOdd
import Submission.OddOrder.BG.Section02.OddGL2Characteristic
import Submission.OddOrder.BG.Section04.ExponentOmegaOneRankTwo
import Submission.OddOrder.MathlibSupport.CharacteristicMulAutRestriction
import Submission.OddOrder.MathlibSupport.CoprimeElementaryAbelianComplement
import Submission.OddOrder.MathlibSupport.FrattiniQuotientAutomorphism
import Submission.OddOrder.MathlibSupport.FrattiniQuotientRankTwo
import Submission.OddOrder.MathlibSupport.OneDimensionalEndomorphism
import Submission.OddOrder.MathlibSupport.PGroupMapKernel
import Mathlib.FieldTheory.Finiteness

/-!
Bender--Glauberman Theorem 4.17.

The proof follows the MathComp formalization.  A critical characteristic
subgroup `H` is chosen, the given automorphism group is restricted to `H`,
and then linearized on `H / Φ(H)`.  Both restriction kernels are `p`-groups,
while the faithful image has dimension one or two; the one-dimensional image
is abelian and the two-dimensional image is handled by Section 2.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

noncomputable section

universe u

/-- `BGsection4.v: der1_Aut_rank2_pgroup` (Bender--Glauberman Theorem 4.17). -/
theorem der1_Aut_rank2_pgroup
    {R : Type u} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R)
    (hoddR : Odd (Nat.card R))
    (hRank : ¬ ∃ E : Subgroup R,
      IsElementaryAbelianOfRank p 3 E)
    (A : Subgroup (MulAut R))
    (_hsolA : IsSolvable A)
    (hoddA : Odd (Nat.card A)) :
    IsPGroup p (_root_.commutator A) := by
  classical
  by_cases hRcard : Nat.card R = 1
  · letI : Subsingleton R := (Nat.card_eq_one_iff_unique.mp hRcard).1
    letI : Subsingleton (MulAut R) :=
      ⟨fun a b ↦ MulEquiv.ext fun x ↦ Subsingleton.elim (a x) (b x)⟩
    letI : Subsingleton A := inferInstance
    intro a
    exact ⟨0, Subsingleton.elim _ _⟩
  · obtain ⟨H, hHchar, _hHcomm, _hHclass, hHexp, hHfix⟩ :=
      Submission.OddOrder.BG.Section01.critical_odd hR hoddR hRcard
    letI : H.Characteristic := hHchar
    have hHp : IsPGroup p H := hR.to_subgroup H
    have hHrank : ¬ ∃ E : Subgroup H,
        IsElementaryAbelianOfRank p 3 E :=
      no_elementaryAbelian_rank_descends hRank H
    let V := H ⧸ frattini H
    have hVcard : Nat.card V ≤ p ^ 2 :=
      natCard_quotient_frattini_le_prime_sq_of_exponent_prime_of_no_rank_three
        hHp hHexp hHrank
    let rH : A →* MulAut H :=
      (characteristicRestrictMulAutHom H).comp A.subtype
    let qH : MulAut H →* MulAut V :=
      frattiniQuotientMulAutHom H
    let rV : A →* MulAut V := qH.comp rH
    have hrHker : IsPGroup p rH.ker := by
      let j : rH.ker →* fixingSubgroup (MulAut R) (H : Set R) :=
        { toFun := fun a ↦ ⟨((a : A) : MulAut R), by
              rw [mem_fixingSubgroup_iff]
              intro h hh
              have ha :=
                (mem_characteristicRestrictMulAutHom_comp_ker_iff
                  H A.subtype (a : A)).mp a.property
              exact ha ⟨h, hh⟩⟩
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl }
      exact hHfix.of_injective j (by
        intro a b hab
        have habR :
            (((a : rH.ker) : A) : MulAut R) =
              (((b : rH.ker) : A) : MulAut R) :=
          congrArg
            (fun z : fixingSubgroup (MulAut R) (H : Set R) =>
              (z : MulAut R)) hab
        apply Subtype.ext
        apply Subtype.ext
        exact habR)
    have hqHker : IsPGroup p qH.ker :=
      frattiniQuotientMulAutHom_ker_isPGroup hHp
    have hrVker : IsPGroup p rV.ker := by
      dsimp [rV, qH]
      exact
        (frattiniQuotientMulAutHom_ker_isPGroup hHp).comap_of_ker_isPGroup
          rH hrHker
    have hPhiNeTop : frattini H ≠ ⊤ := by
      intro htop
      have hbotTop : (⊥ : Subgroup H) = ⊤ :=
        frattini_nongenerating (by rw [htop, sup_top_eq])
      letI : Subsingleton (Subgroup H) :=
        subsingleton_iff_bot_eq_top.mp hbotTop
      letI : Subsingleton H := Subgroup.subsingleton_iff.mp inferInstance
      have hpOne : p = 1 := by
        rw [← hHexp]
        exact Monoid.exp_eq_one_of_subsingleton
      exact (Fact.out : p.Prime).ne_one hpOne
    letI : Nontrivial V := QuotientGroup.nontrivial_iff.mpr hPhiNeTop
    letI : IsMulCommutative V :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
        (IsPGroup.commutator_le_frattini hHp)
    have hVpow : ∀ x : V, x ^ p = 1 :=
      IsPGroup.quotient_frattini_pow_prime hHp
    letI hVmodule : Module (ZMod p) (Additive V) :=
      AddCommGroup.zmodModule fun x ↦ by
        change x.toMul ^ p = 1
        exact hVpow x.toMul
    letI hVEndMonoid : Monoid (Module.End (ZMod p) (Additive V)) :=
      @Module.End.instMonoid (ZMod p) (Additive V)
        inferInstance inferInstance hVmodule
    let B : Subgroup (MulAut V) := rV.range
    let rho : Representation (ZMod p) B (Additive V) :=
      elementaryAbelianActionRepresentation V B p B.subtype
    have hrho : Function.Injective rho := by
      intro a b hab
      apply Subtype.ext
      apply MulEquiv.ext
      intro x
      have hx := LinearMap.congr_fun hab (Additive.ofMul x)
      exact congrArg Additive.toMul hx
    have hoddB : Odd (Nat.card B) :=
      hoddA.of_dvd_nat (Subgroup.card_range_dvd rV)
    letI : Fintype (Additive V) := Fintype.ofFinite (Additive V)
    letI hVmoduleFinite : Module.Finite (ZMod p) (Additive V) := by
      infer_instance
    have hAddCard : Nat.card (Additive V) ≤ p ^ 2 := by
      calc
        Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.ofMul
        _ ≤ p ^ 2 := hVcard
    have hAddCardEq :
        Nat.card (Additive V) =
          p ^ Module.finrank (ZMod p) (Additive V) := by
      simpa only [Nat.card_zmod] using
        (@Module.natCard_eq_pow_finrank
          (ZMod p) (Additive V) inferInstance inferInstance
          hVmodule hVmoduleFinite)
    have hdimLe : Module.finrank (ZMod p) (Additive V) ≤ 2 := by
      by_contra hnot
      have hthree : 3 ≤ Module.finrank (ZMod p) (Additive V) := by omega
      have hpows : p ^ 3 ≤
          p ^ Module.finrank (ZMod p) (Additive V) :=
        Nat.pow_le_pow_right (Fact.out : p.Prime).pos hthree
      have hbad : p ^ 3 ≤ p ^ 2 := by
        calc
          p ^ 3 ≤ p ^ Module.finrank (ZMod p) (Additive V) := hpows
          _ = Nat.card (Additive V) := hAddCardEq.symm
          _ ≤ p ^ 2 := hAddCard
      exact (not_lt_of_ge hbad)
        (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega))
    have hdimPos : 0 < Module.finrank (ZMod p) (Additive V) := by
      by_contra hnot
      have hzero : Module.finrank (ZMod p) (Additive V) = 0 :=
        Nat.eq_zero_of_not_pos hnot
      have hcardOne : Nat.card (Additive V) = 1 := by
        rw [hAddCardEq, hzero, pow_zero]
      exact not_subsingleton (Additive V)
        (Nat.card_eq_one_iff_unique.mp hcardOne).1
    have hderivedB : IsPGroup p (_root_.commutator B) := by
      rcases (show Module.finrank (ZMod p) (Additive V) = 1 ∨
          Module.finrank (ZMod p) (Additive V) = 2 by omega) with
        hdimOne | hdimTwo
      · have hBcomm : IsMulCommutative B := by
          apply isMulCommutative_iff.mpr
          intro a b
          apply hrho
          let hVEndMulOne : MulOne
              (Module.End (ZMod p) (Additive V)) :=
            { toOne := @Module.End.instOne (ZMod p) (Additive V)
                inferInstance inferInstance hVmodule
              toMul := @Module.End.instMul (ZMod p) (Additive V)
                inferInstance inferInstance hVmodule }
          let hBMulOne : MulOne B := inferInstance
          have hab := @MonoidHom.map_mul B
            (Module.End (ZMod p) (Additive V))
            hBMulOne hVEndMulOne rho a b
          have hba := @MonoidHom.map_mul B
            (Module.End (ZMod p) (Additive V))
            hBMulOne hVEndMulOne rho b a
          have hcomm :=
            @endomorphisms_commute_of_finrank_eq_one
              (ZMod p) (Additive V) inferInstance inferInstance hVmodule
              hdimOne (rho a) (rho b)
          exact hab.trans (hcomm.trans hba.symm)
        rw [(_root_.commutator_eq_bot_iff B).mpr hBcomm]
        exact IsPGroup.of_bot
      · exact
          @_root_.Submission.OddOrder.BG.Section02.odd_faithful_finrank_two_commutator_isPGroup_charP
            (ZMod p) B (Additive V) inferInstance inferInstance inferInstance
            inferInstance hVmodule hVmoduleFinite p inferInstance
            rho hrho hdimTwo hoddB
    let D : Subgroup A := _root_.commutator A
    have hmapD : D.map rV =
        (_root_.commutator B).map B.subtype := by
      calc
        D.map rV = ⁅rV.range, rV.range⁆ := map_commutator_eq A rV
        _ = (_root_.commutator B).map B.subtype := by
          simpa [B] using (Subgroup.map_subtype_commutator B).symm
    have hmapP : IsPGroup p (D.map rV) := by
      rw [hmapD]
      exact hderivedB.of_equiv
        ((_root_.commutator B).equivMapOfInjective
          B.subtype B.subtype_injective)
    have hrestrictKer : IsPGroup p (rV.restrict D).ker := by
      let j : (rV.restrict D).ker →* rV.ker :=
        { toFun := fun a ↦ ⟨((a : D) : A), a.property⟩
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl }
      exact hrVker.of_injective j (by
        intro a b hab
        have habA : ((a : D) : A) = ((b : D) : A) :=
          congrArg (fun z : rV.ker => (z : A)) hab
        apply Subtype.ext
        apply Subtype.ext
        exact habA)
    exact isPGroup_of_map_and_restrict_ker D rV hmapP hrestrictKer

end

end Submission.OddOrder.BG.Section04
