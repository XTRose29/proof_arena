import Submission.OddOrder.BG.Section04.ExponentOddNil23
import Submission.OddOrder.BG.Section04.RankTwoExponentPrime
import Submission.OddOrder.MathlibSupport.FrattiniPGroup
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial
import Submission.OddOrder.MathlibSupport.SubgroupCardinality
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Bender--Glauberman Proposition 4.8(b).

MathComp states the hypothesis using numerical rank.  We use the equivalent
finite-group-theoretic interface already used for Proposition 4.8(a): there
is no elementary abelian subgroup of rank three.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- Elementary-abelian cardinal rank is preserved by an injective group
homomorphism. -/
theorem isElementaryAbelianOfRank_map_of_injective
    {H K : Type*} [Group H] [Group K]
    {n : ℕ} {E : Subgroup H} (hE : IsElementaryAbelianOfRank p n E)
    (f : H →* K) (hf : Function.Injective f) :
    IsElementaryAbelianOfRank p n (E.map f) := by
  refine
    { isPGroup := hE.isPGroup.map f
      commutative := ?_
      pow_eq_one := ?_
      card_eq := ?_ }
  · letI : IsMulCommutative E := hE.commutative
    infer_instance
  · rintro ⟨x, y, hy, rfl⟩
    apply Subtype.ext
    have hyPow := hE.pow_eq_one ⟨y, hy⟩
    have hyPow' := congrArg f (congrArg Subtype.val hyPow)
    simpa using hyPow'
  · calc
      Nat.card (E.map f) = Nat.card E :=
        Subgroup.card_map_of_injective hf
      _ = p ^ n := hE.card_eq

/-- Absence of an elementary abelian subgroup of a fixed rank descends to
every subgroup. -/
theorem no_elementaryAbelian_rank_descends
    {n : ℕ}
    (hrank : ¬ ∃ E : Subgroup G, IsElementaryAbelianOfRank p n E)
    (H : Subgroup G) :
    ¬ ∃ E : Subgroup H, IsElementaryAbelianOfRank p n E := by
  rintro ⟨E, hE⟩
  exact hrank ⟨E.map H.subtype,
    isElementaryAbelianOfRank_map_of_injective hE H.subtype
      H.subtype_injective⟩

/-- The sharp elementary bound on the nilpotency class of a finite
`p`-group.  Starting at order `p²`, the class is at most one less than the
cardinal exponent. -/
theorem nilpotencyClass_le_pred_of_isPGroup_card_eq_prime_pow
    {n : ℕ} (hG : IsPGroup p G) (hn : 2 ≤ n)
    (hcard : Nat.card G = p ^ n) :
    Group.nilpotencyClass G ≤ n - 1 := by
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
      letI : Group.IsNilpotent G := hG.isNilpotent
      by_cases hn2 : n = 2
      · subst n
        letI : IsMulCommutative G :=
          IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
        exact
          (Group.IsNilpotent.nilpotencyClass_le_one_iff (G := G)).mpr
            (inferInstance : IsMulCommutative G)
      · have hn3 : 3 ≤ n := by omega
        have hcardOne : 1 < Nat.card G := by
          rw [hcard]
          exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
        letI : Nontrivial G :=
          Finite.one_lt_card_iff_nontrivial.mp hcardOne
        let Q := G ⧸ Subgroup.center G
        have hQp : IsPGroup p Q := hG.to_quotient (Subgroup.center G)
        letI : Group.IsNilpotent Q := hQp.isNilpotent
        obtain ⟨m, hQcard⟩ := hQp.exists_card_eq
        have hcenterNe : Subgroup.center G ≠ ⊥ :=
          Group.IsNilpotent.center_ne_bot G
        have hQcardLt : Nat.card Q < Nat.card G :=
          natCard_quotient_lt_of_ne_bot (Subgroup.center G) hcenterNe
        have hm_lt : m < n := by
          apply (Nat.pow_lt_pow_iff_right
            (Fact.out : p.Prime).one_lt).mp
          simpa [Q, hQcard, hcard] using hQcardLt
        have hclassQ : Group.nilpotencyClass Q ≤ n - 2 := by
          by_cases hm : 2 ≤ m
          · exact (ih m hm_lt hQp hm hQcard).trans (by omega)
          · have hm1 : m ≤ 1 := by omega
            have hQcardDvd : Nat.card Q ∣ p := by
              rw [hQcard]
              interval_cases m <;> simp
            letI : IsCyclic Q := isCyclic_of_card_dvd_prime hQcardDvd
            have hQcomm : IsMulCommutative Q := IsCyclic.isMulCommutative
            have hQclass : Group.nilpotencyClass Q ≤ 1 :=
              (Group.IsNilpotent.nilpotencyClass_le_one_iff (G := Q)).mpr
                hQcomm
            exact hQclass.trans (by omega)
        have hclassQ' :
            Group.nilpotencyClass (G ⧸ Subgroup.center G) ≤ n - 2 := by
          simpa [Q] using hclassQ
        rw [Group.nilpotencyClass_eq_quotient_center_plus_one]
        omega

/-- A finite `p`-group of cardinality at most `p⁴` has nilpotency class at
most three. -/
theorem nilpotencyClass_le_three_of_isPGroup_card_le_prime_four
    (hG : IsPGroup p G) (hcard : Nat.card G ≤ p ^ 4) :
    Group.nilpotencyClass G ≤ 3 := by
  obtain ⟨n, hncard⟩ := hG.exists_card_eq
  have hn4 : n ≤ 4 := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    simpa [hncard] using hcard
  by_cases hn : 2 ≤ n
  · exact
      (nilpotencyClass_le_pred_of_isPGroup_card_eq_prime_pow
        hG hn hncard).trans (by omega)
  · letI : Group.IsNilpotent G := hG.isNilpotent
    have hcardDvd : Nat.card G ∣ p := by
      rw [hncard]
      have hn1 : n ≤ 1 := by omega
      interval_cases n <;> simp
    letI : IsCyclic G := isCyclic_of_card_dvd_prime hcardDvd
    have hcomm : IsMulCommutative G := IsCyclic.isMulCommutative
    exact
      ((Group.IsNilpotent.nilpotencyClass_le_one_iff (G := G)).mpr
        hcomm).trans (by omega)

/-- The cardinality-indexed induction statement for Proposition 4.8(b). -/
def ExponentOmegaOneRankTwoStatement (p n : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Nat.card G = n →
    IsPGroup p G →
    (¬ ∃ E : Subgroup G, IsElementaryAbelianOfRank p 3 E) →
    3 < p →
    Monoid.exponent (omegaOne p G) ∣ p

/-- Proposition 4.8(b) holds at every finite cardinality. -/
theorem exponentOmegaOneRankTwoStatement_all (p n : ℕ) [Fact p.Prime] :
    ExponentOmegaOneRankTwoStatement.{u} p n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G _ _ hcard hG hrank hp3
      apply exponent_omegaOne_dvd p
      intro z
      apply omegaOne_pow_eq_one_of_mul_closed p ?_ z.property
      intro x y hx hy
      let P : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers y
      have hxP : x ∈ P :=
        (le_sup_left : Subgroup.zpowers x ≤ P) (Subgroup.mem_zpowers x)
      have hyP : y ∈ P :=
        (le_sup_right : Subgroup.zpowers y ≤ P) (Subgroup.mem_zpowers y)
      by_cases hPtop : P = ⊤
      · by_cases hxTop : Subgroup.zpowers x = ⊤
        · letI : IsCyclic G :=
            isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, hxTop⟩
          letI : IsMulCommutative G := IsCyclic.isMulCommutative
          have hxy : Commute x y := Std.Commutative.comm x y
          simpa [hx, hy] using hxy.mul_pow p
        · have hxlt : Subgroup.zpowers x < (⊤ : Subgroup G) :=
            lt_top_iff_ne_top.mpr hxTop
          obtain ⟨S, hxS, hSmax⟩ := exists_le_covBy_of_lt hxlt
          have hSneTop : S ≠ (⊤ : Subgroup G) := hSmax.lt.ne
          have hSnormal : S.Normal :=
            IsPGroup.isCoatom_normal hG hSmax.isCoatom
          letI : S.Normal := hSnormal
          have hcardSlt : Nat.card S < n := by
            simpa [hcard] using natCard_subgroup_lt_of_ne_top S hSneTop
          have hSp : IsPGroup p S := hG.to_subgroup S
          have hSrank :
              ¬ ∃ E : Subgroup S, IsElementaryAbelianOfRank p 3 E :=
            no_elementaryAbelian_rank_descends hrank S
          have hSexp : Monoid.exponent (omegaOne p S) ∣ p :=
            ih (Nat.card S) hcardSlt S rfl hSp hSrank hp3
          have hOmegaP : IsPGroup p (omegaOne p S) :=
            omegaOne_isPGroup p hSp
          have hOmegaRank :
              ¬ ∃ E : Subgroup (omegaOne p S),
                IsElementaryAbelianOfRank p 3 E :=
            no_elementaryAbelian_rank_descends hSrank (omegaOne p S)
          have hOmegaCard : Nat.card (omegaOne p S) ≤ p ^ 3 :=
            natCard_le_prime_cube_of_exponent_prime_of_no_elementaryAbelian_rank_three
              hOmegaP hOmegaRank hSexp
          let W : Subgroup G := (omegaOne p S).map S.subtype
          have hWnormal : W.Normal := by
            dsimp [W]
            infer_instance
          letI : W.Normal := hWnormal
          have hWcard : Nat.card W = Nat.card (omegaOne p S) :=
            Subgroup.card_map_of_injective S.subtype_injective
          have hWcardLe : Nat.card W ≤ p ^ 3 := by
            rw [hWcard]
            exact hOmegaCard
          have hxS' : x ∈ S := Subgroup.zpowers_le.mp hxS
          let xS : S := ⟨x, hxS'⟩
          have hxSpow : xS ^ p = 1 := by
            apply Subtype.ext
            exact hx
          have hxOmega : xS ∈ omegaOne p S :=
            mem_omegaOne_of_pow_eq_one p hxSpow
          have hxW : x ∈ W := by
            exact ⟨xS, hxOmega, rfl⟩
          let q : G →* G ⧸ W := QuotientGroup.mk' W
          have hqx : q x = 1 := by
            exact (QuotientGroup.eq_one_iff x).mpr hxW
          have hqGen : Subgroup.zpowers (q y) = ⊤ := by
            calc
              Subgroup.zpowers (q y) =
                  Subgroup.zpowers (q x) ⊔ Subgroup.zpowers (q y) := by
                rw [hqx]
                simp
              _ = P.map q := by
                dsimp [P]
                rw [Subgroup.map_sup, MonoidHom.map_zpowers,
                  MonoidHom.map_zpowers]
              _ = ⊤ := by
                rw [hPtop]
                exact Subgroup.map_top_of_surjective q
                  (QuotientGroup.mk'_surjective W)
          have hqypow : (q y) ^ p = 1 := by
            simpa using congrArg q hy
          have hqOrder : orderOf (q y) ∣ p :=
            orderOf_dvd_of_pow_eq_one hqypow
          have hqOrderCard : orderOf (q y) = Nat.card (G ⧸ W) :=
            orderOf_eq_card_of_forall_mem_zpowers fun a ↦
              hqGen.symm.le (Subgroup.mem_top a)
          have hQcardLe : Nat.card (G ⧸ W) ≤ p := by
            rw [← hqOrderCard]
            exact Nat.le_of_dvd (Fact.out : p.Prime).pos hqOrder
          have hGcardLe : Nat.card G ≤ p ^ 4 := by
            calc
              Nat.card G = Nat.card (G ⧸ W) * Nat.card W :=
                Subgroup.card_eq_card_quotient_mul_card_subgroup W
              _ ≤ p * p ^ 3 := Nat.mul_le_mul hQcardLe hWcardLe
              _ = p ^ 4 := by ring
          have hclass : Group.nilpotencyClass G ≤ 3 :=
            nilpotencyClass_le_three_of_isPGroup_card_le_prime_four
              hG hGcardLe
          have hpodd : Odd p :=
            (Fact.out : p.Prime).odd_of_ne_two (by omega)
          have hxyOmega : x * y ∈ omegaOne p G :=
            (omegaOne p G).mul_mem
              (mem_omegaOne_of_pow_eq_one p hx)
              (mem_omegaOne_of_pow_eq_one p hy)
          exact omegaOne_pow_eq_one_of_small_nilpotencyClass
            p Fact.out hpodd hG (by simpa [hp3] using hclass)
              (x * y) hxyOmega
      · have hcardPlt : Nat.card P < n := by
          simpa [hcard] using natCard_subgroup_lt_of_ne_top P hPtop
        have hPp : IsPGroup p P := hG.to_subgroup P
        have hPrank :
            ¬ ∃ E : Subgroup P, IsElementaryAbelianOfRank p 3 E :=
          no_elementaryAbelian_rank_descends hrank P
        have hPexp : Monoid.exponent (omegaOne p P) ∣ p :=
          ih (Nat.card P) hcardPlt P rfl hPp hPrank hp3
        let xP : P := ⟨x, hxP⟩
        let yP : P := ⟨y, hyP⟩
        have hxPpow : xP ^ p = 1 := by
          apply Subtype.ext
          exact hx
        have hyPpow : yP ^ p = 1 := by
          apply Subtype.ext
          exact hy
        let xyOmega : omegaOne p P :=
          ⟨xP * yP,
            (omegaOne p P).mul_mem
              (mem_omegaOne_of_pow_eq_one p hxPpow)
              (mem_omegaOne_of_pow_eq_one p hyPpow)⟩
        have hxyPow :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hPexp xyOmega
        simpa [xyOmega, xP, yP] using
          congrArg (fun a : omegaOne p P ↦ ((a : P) : G)) hxyPow

/-- `BGsection4.v: exponent_Ohm1_rank2` (Bender--Glauberman Proposition
4.8(b)). -/
theorem exponent_omegaOne_dvd_prime_of_no_elementaryAbelian_rank_three
    (hG : IsPGroup p G)
    (hrank : ¬ ∃ E : Subgroup G, IsElementaryAbelianOfRank p 3 E)
    (hp3 : 3 < p) :
    Monoid.exponent (omegaOne p G) ∣ p :=
  exponentOmegaOneRankTwoStatement_all p (Nat.card G)
    G rfl hG hrank hp3

end Submission.OddOrder.BG.Section04
