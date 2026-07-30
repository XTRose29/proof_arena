import Mathlib.GroupTheory.Frattini
import Submission.OddOrder.MathlibSupport.NilpotencyClassPowerMaps
import Submission.OddOrder.MathlibSupport.OmegaOne

/-!
The first omega subgroup of an odd small-class finite `p`-group has exponent
dividing `p`.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- The cardinality-indexed induction statement for the first half of
`BGsection4.v: exponent_odd_nil23`. -/
def OmegaOneSmallNilpotencyStatement (p n : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Nat.card G = n →
    ∀ (_hp : p.Prime) (_hpodd : Odd p) (_hP : IsPGroup p G),
      Group.nilpotencyClass G ≤ (if 3 < p then 3 else 2) →
      ∀ z : G, z ∈ omegaOne p G → z ^ p = 1

/-- The omega-one exponent statement holds at every finite cardinality. -/
theorem omegaOneSmallNilpotencyStatement_all (p n : ℕ) :
    OmegaOneSmallNilpotencyStatement.{u} p n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G _ _ hcard hp hpodd hP hclass z hz
      letI : Fact p.Prime := ⟨hp⟩
      letI : Group.IsNilpotent G := hP.isNilpotent
      apply omegaOne_pow_eq_one_of_mul_closed p ?_ hz
      intro x y hx hy
      by_cases hxTop : Subgroup.zpowers x = ⊤
      · letI : IsCyclic G :=
          isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, hxTop⟩
        letI : IsMulCommutative G := IsCyclic.isMulCommutative
        have hxy : Commute x y := Std.Commutative.comm x y
        simpa [hx, hy] using hxy.mul_pow p
      · have hzpowersLt : Subgroup.zpowers x < (⊤ : Subgroup G) :=
          lt_top_iff_ne_top.mpr hxTop
        obtain ⟨S, hxS, hSmax⟩ := exists_le_covBy_of_lt hzpowersLt
        have hxMem : x ∈ S := Subgroup.zpowers_le.mp hxS
        have hSneTop : S ≠ ⊤ := hSmax.lt.ne
        have hSnormal : S.Normal := by
          have hmaxNormal : ∀ H : Subgroup G, IsCoatom H → H.Normal :=
            ((Group.isNilpotent_of_finite_tfae (G := G)).out 0 2 rfl rfl).mp
              (inferInstance : Group.IsNilpotent G)
          exact hmaxNormal S hSmax.isCoatom
        letI : S.Normal := hSnormal
        have hcardS : Nat.card S < Nat.card G := by
          rw [← S.index_mul_card]
          exact lt_mul_of_one_lt_left Nat.card_pos
            (Subgroup.one_lt_index_of_ne_top hSneTop)
        have hcardSn : Nat.card S < n := by simpa [hcard] using hcardS
        have hPS : IsPGroup p S := hP.to_subgroup S
        have hclassS :
            Group.nilpotencyClass S ≤ if 3 < p then 3 else 2 :=
          (Subgroup.nilpotencyClass_le S).trans hclass
        have ihS : ∀ s : S, s ∈ omegaOne p S → s ^ p = 1 :=
          ih (Nat.card S) hcardSn S rfl hp hpodd hPS hclassS
        have hmulS : ∀ {a b : G},
            a ∈ S → b ∈ S → a ^ p = 1 → b ^ p = 1 →
              (a * b) ^ p = 1 := by
          intro a b haS hbS hap hbp
          let aS : S := ⟨a, haS⟩
          let bS : S := ⟨b, hbS⟩
          have hapS : aS ^ p = 1 := by
            apply Subtype.ext
            exact hap
          have hbpS : bS ^ p = 1 := by
            apply Subtype.ext
            exact hbp
          have haOmega : aS ∈ omegaOne p S :=
            mem_omegaOne_of_pow_eq_one p hapS
          have hbOmega : bS ∈ omegaOne p S :=
            mem_omegaOne_of_pow_eq_one p hbpS
          have habPow := ihS (aS * bS)
            ((omegaOne p S).mul_mem haOmega hbOmega)
          simpa [aS, bS] using congrArg Subtype.val habPow
        have hconjPow (g t : G) (htp : t ^ p = 1) :
            (g * t * g⁻¹) ^ p = 1 := by
          rw [conj_pow, htp]
          simp
        have hcommRight (g t : G) (htS : t ∈ S) (htp : t ^ p = 1) :
            ssrCommutatorElement g t ∈ S ∧
              ssrCommutatorElement g t ^ p = 1 := by
          let c := g⁻¹ * t⁻¹ * g
          have hcS : c ∈ S := by
            simpa [c] using
              hSnormal.conj_mem t⁻¹ (S.inv_mem htS) g⁻¹
          have htpInv : t⁻¹ ^ p = 1 := by
            rw [inv_pow, htp, inv_one]
          have hcp : c ^ p = 1 := by
            simpa [c] using hconjPow g⁻¹ t⁻¹ htpInv
          constructor
          · simpa [ssrCommutatorElement, c, mul_assoc] using S.mul_mem hcS htS
          · simpa [ssrCommutatorElement, c, mul_assoc] using
              hmulS hcS htS hcp htp
        have hcommLeft (t g : G) (htS : t ∈ S) (htp : t ^ p = 1) :
            ssrCommutatorElement t g ∈ S ∧
              ssrCommutatorElement t g ^ p = 1 := by
          let c := g⁻¹ * t * g
          have hcS : c ∈ S := by
            simpa [c] using hSnormal.conj_mem t htS g⁻¹
          have hcp : c ^ p = 1 := by
            simpa [c] using hconjPow g⁻¹ t htp
          have htpInv : t⁻¹ ^ p = 1 := by
            rw [inv_pow, htp, inv_one]
          constructor
          · simpa [ssrCommutatorElement, c, mul_assoc] using
              S.mul_mem (S.inv_mem htS) hcS
          · simpa [ssrCommutatorElement, c, mul_assoc] using
              hmulS (S.inv_mem htS) hcS htpInv hcp
        let r := ssrCommutatorElement y x
        let a := ssrCommutatorElement r x
        let b := ssrCommutatorElement r y
        have hr : r ∈ S ∧ r ^ p = 1 := hcommRight y x hxMem hx
        have ha : a ∈ S ∧ a ^ p = 1 := hcommLeft r x hr.1 hr.2
        have hb : b ∈ S ∧ b ^ p = 1 := hcommLeft r y hr.1 hr.2
        have hclassThree : Group.nilpotencyClass G ≤ 3 := by
          by_cases hp3 : 3 < p
          · simpa [hp3] using hclass
          · have hclassTwo : Group.nilpotencyClass G ≤ 2 := by
              simpa [hp3] using hclass
            omega
        have htripleCentral : ∀ q t : G,
            Commute q (ssrCommutatorElement r t) := by
          intro q t
          exact tripleCommutators_central_of_nilpotencyClass_le_three
            hclassThree x y q t
        rw [mul_pow_of_tripleCommutators_central x y htripleCentral p]
        change x ^ p * y ^ p * r ^ (p.choose 2) * a ^ (p.choose 3) *
            b ^ (2 * p.choose 3 + p.choose 2) = 1
        by_cases hp3 : 3 < p
        · obtain ⟨kr, hkr⟩ := prime_dvd_choose_two p hp hpodd
          obtain ⟨ka, hka⟩ := prime_dvd_choose_three p hp hp3
          obtain ⟨kb, hkb⟩ := prime_dvd_classThree_correction p hp hp3
          rw [hkb, hka, hkr, pow_mul, pow_mul, pow_mul,
            hx, hy, hr.2, ha.2, hb.2]
          simp
        · have hclassTwo : Group.nilpotencyClass G ≤ 2 := by
            simpa [hp3] using hclass
          have haOne : a = 1 :=
            tripleCommutator_eq_one_of_nilpotencyClass_le_two
              hclassTwo x y x
          have hbOne : b = 1 :=
            tripleCommutator_eq_one_of_nilpotencyClass_le_two
              hclassTwo x y y
          obtain ⟨kr, hkr⟩ := prime_dvd_choose_two p hp hpodd
          rw [hkr, pow_mul, hx, hy, hr.2, haOne, hbOne]
          simp

/-- Every element of the first omega subgroup has trivial `p`th power under
the class bound from Bender-Glauberman Proposition 4.3. -/
theorem omegaOne_pow_eq_one_of_small_nilpotencyClass
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) (hP : IsPGroup p G)
    (hclass : Group.nilpotencyClass G ≤ if 3 < p then 3 else 2)
    (z : G) (hz : z ∈ omegaOne p G) :
    z ^ p = 1 :=
  omegaOneSmallNilpotencyStatement_all p (Nat.card G)
    G rfl hp hpodd hP hclass z hz

/-- `BGsection4.v: exponent_odd_nil23`, part (a), in exponent form. -/
theorem exponent_omegaOne_dvd_of_small_nilpotencyClass
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) (hP : IsPGroup p G)
    (hclass : Group.nilpotencyClass G ≤ if 3 < p then 3 else 2) :
    Monoid.exponent (omegaOne p G) ∣ p := by
  apply exponent_omegaOne_dvd p
  intro z
  exact omegaOne_pow_eq_one_of_small_nilpotencyClass
    p hp hpodd hP hclass z z.property

end Submission.OddOrder.MathlibSupport
