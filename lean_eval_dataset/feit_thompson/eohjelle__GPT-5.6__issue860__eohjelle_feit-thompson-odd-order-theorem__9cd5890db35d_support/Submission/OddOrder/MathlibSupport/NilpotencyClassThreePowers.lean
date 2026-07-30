import Submission.OddOrder.MathlibSupport.NilpotencyClassTwoPowers

/-!
Power collection with the triple-commutator corrections needed in
nilpotency class three.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- MathComp's element commutator convention, `x^-1 * y^-1 * x * y`. -/
def ssrCommutatorElement (x y : G) : G := x⁻¹ * y⁻¹ * x * y

theorem mul_ssrCommutatorElement_eq_swap (x y : G) :
    y * x * ssrCommutatorElement x y = x * y := by
  simp [ssrCommutatorElement, mul_assoc]

theorem swap_eq_mul_ssrCommutatorElement (x y : G) :
    x * y = y * x * ssrCommutatorElement x y := by
  rw [mul_ssrCommutatorElement_eq_swap]

/-- Collection of one element past a power when the relevant MathComp
commutator is central. -/
theorem pow_mul_eq_mul_pow_mul_ssrCommutator_pow
    (x y : G)
    (hcentral : ssrCommutatorElement x y ∈ Subgroup.center G) :
    ∀ n : ℕ, x ^ n * y =
      y * x ^ n * ssrCommutatorElement x y ^ n
  | 0 => by simp
  | n + 1 => by
      let c := ssrCommutatorElement x y
      have hcPow (m : ℕ) : c ^ m ∈ Subgroup.center G :=
        (Subgroup.center G).pow_mem hcentral m
      rw [pow_succ, pow_succ (ssrCommutatorElement x y)]
      change (x ^ n * x) * y = y * (x ^ n * x) * (c ^ n * c)
      have hcx : Commute (c ^ n) x :=
        (Subgroup.mem_center_iff.mp (hcPow n) x).symm
      calc
        (x ^ n * x) * y = x ^ n * (x * y) := by group
        _ = x ^ n * (y * x * c) := by
          rw [swap_eq_mul_ssrCommutatorElement x y]
        _ = (x ^ n * y) * x * c := by
          group
        _ = (y * x ^ n * c ^ n) * x * c := by
          rw [pow_mul_eq_mul_pow_mul_ssrCommutator_pow x y hcentral n]
        _ = y * (x ^ n * x) * (c ^ n * c) := by
          rw [mul_assoc (y * x ^ n), hcx.eq]
          group

/-- The right-power companion of
`pow_mul_eq_mul_pow_mul_ssrCommutator_pow`. -/
theorem mul_pow_eq_pow_mul_mul_ssrCommutator_pow
    (x y : G)
    (hcentral : ssrCommutatorElement x y ∈ Subgroup.center G) :
    ∀ n : ℕ, x * y ^ n =
      y ^ n * x * ssrCommutatorElement x y ^ n
  | 0 => by simp
  | n + 1 => by
      let c := ssrCommutatorElement x y
      have hcPow (m : ℕ) : c ^ m ∈ Subgroup.center G :=
        (Subgroup.center G).pow_mem hcentral m
      rw [pow_succ, pow_succ (ssrCommutatorElement x y)]
      change x * (y ^ n * y) = (y ^ n * y) * x * (c ^ n * c)
      have hcy : Commute (c ^ n) y :=
        (Subgroup.mem_center_iff.mp (hcPow n) y).symm
      calc
        x * (y ^ n * y) = (x * y ^ n) * y := by group
        _ = (y ^ n * x * c ^ n) * y := by
          rw [mul_pow_eq_pow_mul_mul_ssrCommutator_pow x y hcentral n]
        _ = y ^ n * (x * y) * c ^ n := by
          rw [mul_assoc (y ^ n * x), hcy.eq]
          group
        _ = y ^ n * (y * x * c) * c ^ n := by
          rw [swap_eq_mul_ssrCommutatorElement x y]
        _ = (y ^ n * y) * x * (c ^ n * c) := by group

/-- In class three, collecting `v^n` past `u` produces the first
triple-commutator binomial correction. -/
theorem pow_mul_classThree_collection
    (u v : G)
    (htripleCentral : ∀ x y : G,
      Commute x (ssrCommutatorElement (ssrCommutatorElement v u) y)) :
    ∀ n : ℕ, v ^ n * u =
      u * v ^ n * ssrCommutatorElement v u ^ n *
        ssrCommutatorElement (ssrCommutatorElement v u) v ^ (n.choose 2)
  | 0 => by simp
  | n + 1 => by
      let r := ssrCommutatorElement v u
      let b := ssrCommutatorElement r v
      have hbcenter : b ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro x
        exact (htripleCentral x v).eq
      have hbPow (m : ℕ) : b ^ m ∈ Subgroup.center G :=
        (Subgroup.center G).pow_mem hbcenter m
      rw [pow_succ]
      change (v ^ n * v) * u =
        u * (v ^ n * v) * r ^ (n + 1) * b ^ ((n + 1).choose 2)
      have hbTail : Commute (b ^ (n.choose 2)) (v * r) :=
        (Subgroup.mem_center_iff.mp (hbPow (n.choose 2)) (v * r)).symm
      calc
        (v ^ n * v) * u = v ^ n * (v * u) := by group
        _ = v ^ n * (u * v * r) := by
          rw [swap_eq_mul_ssrCommutatorElement v u]
        _ = (v ^ n * u) * v * r := by
          group
        _ = (u * v ^ n * r ^ n * b ^ (n.choose 2)) * v * r := by
          rw [pow_mul_classThree_collection u v htripleCentral n]
        _ = u * v ^ n * r ^ n * (b ^ (n.choose 2) * (v * r)) := by group
        _ = u * v ^ n * r ^ n * ((v * r) * b ^ (n.choose 2)) := by
          rw [hbTail.eq]
        _ = u * v ^ n * r ^ n * (v * r) * b ^ (n.choose 2) := by group
        _ = u * v ^ n * (r ^ n * v) * r * b ^ (n.choose 2) := by group
        _ = u * v ^ n * (v * r ^ n * b ^ n) * r *
            b ^ (n.choose 2) := by
          rw [pow_mul_eq_mul_pow_mul_ssrCommutator_pow r v hbcenter n]
        _ = u * (v ^ n * v) * r ^ n * (b ^ n * r) *
            b ^ (n.choose 2) := by group
        _ = u * (v ^ n * v) * r ^ n * (r * b ^ n) *
            b ^ (n.choose 2) := by
          have hbCommR : Commute (b ^ n) r :=
            (Subgroup.mem_center_iff.mp (hbPow n) r).symm
          rw [hbCommR.eq]
        _ = u * (v ^ n * v) * (r ^ n * r) *
            (b ^ n * b ^ (n.choose 2)) := by
          group
        _ = u * (v ^ n * v) * r ^ (n + 1) *
            b ^ ((n + 1).choose 2) := by
          rw [← pow_succ r n, ← pow_add, Nat.choose_succ_succ]
          simp

/-- The class-three Hall-Petresco formula, in MathComp's commutator
orientation. The two weight-three commutators are central by hypothesis. -/
theorem mul_pow_of_tripleCommutators_central
    (u v : G)
    (htripleCentral : ∀ x y : G,
      Commute x (ssrCommutatorElement (ssrCommutatorElement v u) y)) :
    ∀ n : ℕ, (u * v) ^ n =
      u ^ n * v ^ n * ssrCommutatorElement v u ^ (n.choose 2) *
        ssrCommutatorElement (ssrCommutatorElement v u) u ^ (n.choose 3) *
        ssrCommutatorElement (ssrCommutatorElement v u) v ^
          (2 * (n.choose 3) + n.choose 2)
  | 0 => by simp
  | n + 1 => by
      let r := ssrCommutatorElement v u
      let a := ssrCommutatorElement r u
      let b := ssrCommutatorElement r v
      have hacenter : a ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro x
        exact (htripleCentral x u).eq
      have hbcenter : b ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro x
        exact (htripleCentral x v).eq
      have haPow (m : ℕ) : a ^ m ∈ Subgroup.center G :=
        (Subgroup.center G).pow_mem hacenter m
      have hbPow (m : ℕ) : b ^ m ∈ Subgroup.center G :=
        (Subgroup.center G).pow_mem hbcenter m
      have hchooseTwo : (n + 1).choose 2 = n + n.choose 2 := by
        rw [Nat.choose_succ_succ]
        simp
      have hchooseThree : (n + 1).choose 3 = n.choose 2 + n.choose 3 := by
        rw [Nat.choose_succ_succ]
      have hchooseB :
          (n + n.choose 2) + n.choose 2 +
              (2 * n.choose 3 + n.choose 2) =
            2 * ((n + 1).choose 3) + (n + 1).choose 2 := by
        rw [hchooseTwo, hchooseThree]
        omega
      have htailCenter :
          a ^ (n.choose 3) * b ^ (2 * n.choose 3 + n.choose 2) ∈
            Subgroup.center G :=
        (Subgroup.center G).mul_mem
          (haPow (n.choose 3)) (hbPow (2 * n.choose 3 + n.choose 2))
      have htailComm : Commute
          (a ^ (n.choose 3) * b ^ (2 * n.choose 3 + n.choose 2)) (u * v) :=
        (Subgroup.mem_center_iff.mp htailCenter (u * v)).symm
      have hbChooseCommR : Commute (b ^ (n.choose 2)) (r ^ (n.choose 2)) :=
        (Subgroup.mem_center_iff.mp
          (hbPow (n.choose 2)) (r ^ (n.choose 2))).symm
      have hbChooseCommA : Commute (b ^ (n.choose 2)) (a ^ (n.choose 2)) :=
        (Subgroup.mem_center_iff.mp
          (hbPow (n.choose 2)) (a ^ (n.choose 2))).symm
      have haBCommV : Commute
          (a ^ (n.choose 2) * b ^ (n.choose 2)) v :=
        (Subgroup.mem_center_iff.mp
          ((Subgroup.center G).mul_mem
            (haPow (n.choose 2)) (hbPow (n.choose 2))) v).symm
      have hbChooseCommAOld : Commute
          (b ^ (n.choose 2)) (a ^ (n.choose 3)) :=
        (Subgroup.mem_center_iff.mp
          (hbPow (n.choose 2)) (a ^ (n.choose 3))).symm
      rw [pow_succ,
        mul_pow_of_tripleCommutators_central u v htripleCentral n]
      change
        (u ^ n * v ^ n * r ^ (n.choose 2) * a ^ (n.choose 3) *
            b ^ (2 * n.choose 3 + n.choose 2)) * (u * v) =
          u ^ (n + 1) * v ^ (n + 1) * r ^ ((n + 1).choose 2) *
            a ^ ((n + 1).choose 3) *
            b ^ (2 * ((n + 1).choose 3) + (n + 1).choose 2)
      calc
        (u ^ n * v ^ n * r ^ (n.choose 2) * a ^ (n.choose 3) *
            b ^ (2 * n.choose 3 + n.choose 2)) * (u * v) =
            (u ^ n * v ^ n * r ^ (n.choose 2)) *
              (a ^ (n.choose 3) * b ^ (2 * n.choose 3 + n.choose 2)) *
                (u * v) := by group
        _ = (u ^ n * v ^ n * r ^ (n.choose 2)) *
              ((a ^ (n.choose 3) * b ^ (2 * n.choose 3 + n.choose 2)) *
                (u * v)) := by group
        _ = (u ^ n * v ^ n * r ^ (n.choose 2)) *
              ((u * v) *
                (a ^ (n.choose 3) * b ^ (2 * n.choose 3 + n.choose 2))) := by
          rw [htailComm.eq]
        _ = (u ^ n * v ^ n * r ^ (n.choose 2)) * (u * v) *
              (a ^ (n.choose 3) * b ^ (2 * n.choose 3 + n.choose 2)) := by
          group
        _ = u ^ n * v ^ n * (r ^ (n.choose 2) * u) * v *
              (a ^ (n.choose 3) * b ^ (2 * n.choose 3 + n.choose 2)) := by
          group
        _ = u ^ n * v ^ n *
              (u * r ^ (n.choose 2) * a ^ (n.choose 2)) * v *
                (a ^ (n.choose 3) * b ^ (2 * n.choose 3 + n.choose 2)) := by
          rw [pow_mul_eq_mul_pow_mul_ssrCommutator_pow
            r u hacenter (n.choose 2)]
        _ = u ^ n * (v ^ n * u) * r ^ (n.choose 2) *
              a ^ (n.choose 2) * v *
                (a ^ (n.choose 3) * b ^ (2 * n.choose 3 + n.choose 2)) := by
          group
        _ = u ^ n *
              (u * v ^ n * r ^ n * b ^ (n.choose 2)) *
                r ^ (n.choose 2) * a ^ (n.choose 2) * v *
                  (a ^ (n.choose 3) * b ^
                    (2 * n.choose 3 + n.choose 2)) := by
          rw [pow_mul_classThree_collection u v htripleCentral n]
        _ = (u ^ n * u) * v ^ n * r ^ n *
              (b ^ (n.choose 2) * r ^ (n.choose 2)) *
                a ^ (n.choose 2) * v *
                  (a ^ (n.choose 3) * b ^
                    (2 * n.choose 3 + n.choose 2)) := by group
        _ = (u ^ n * u) * v ^ n * r ^ n *
              (r ^ (n.choose 2) * b ^ (n.choose 2)) *
                a ^ (n.choose 2) * v *
                  (a ^ (n.choose 3) * b ^
                    (2 * n.choose 3 + n.choose 2)) := by
          rw [hbChooseCommR.eq]
        _ = (u ^ n * u) * v ^ n * r ^ n * r ^ (n.choose 2) *
              (b ^ (n.choose 2) * a ^ (n.choose 2)) * v *
                (a ^ (n.choose 3) * b ^
                  (2 * n.choose 3 + n.choose 2)) := by group
        _ = (u ^ n * u) * v ^ n * r ^ n * r ^ (n.choose 2) *
              (a ^ (n.choose 2) * b ^ (n.choose 2)) * v *
                (a ^ (n.choose 3) * b ^
                  (2 * n.choose 3 + n.choose 2)) := by
          rw [hbChooseCommA.eq]
        _ = (u ^ n * u) * v ^ n * (r ^ n * r ^ (n.choose 2)) *
              ((a ^ (n.choose 2) * b ^ (n.choose 2)) * v) *
                (a ^ (n.choose 3) * b ^
                  (2 * n.choose 3 + n.choose 2)) := by
          group
        _ = (u ^ n * u) * v ^ n * (r ^ n * r ^ (n.choose 2)) *
              (v * (a ^ (n.choose 2) * b ^ (n.choose 2))) *
                (a ^ (n.choose 3) * b ^
                  (2 * n.choose 3 + n.choose 2)) := by
          rw [haBCommV.eq]
        _ = (u ^ n * u) * v ^ n * (r ^ n * r ^ (n.choose 2)) *
              v * (a ^ (n.choose 2) * b ^ (n.choose 2)) *
                (a ^ (n.choose 3) * b ^
                  (2 * n.choose 3 + n.choose 2)) := by
          group
        _ = (u ^ n * u) * v ^ n * (r ^ (n + n.choose 2) * v) *
              (a ^ (n.choose 2) * b ^ (n.choose 2)) *
                (a ^ (n.choose 3) * b ^
                  (2 * n.choose 3 + n.choose 2)) := by
          rw [← pow_add r n (n.choose 2)]
          group
        _ = (u ^ n * u) * v ^ n *
              (v * r ^ (n + n.choose 2) * b ^ (n + n.choose 2)) *
                (a ^ (n.choose 2) * b ^ (n.choose 2)) *
                  (a ^ (n.choose 3) * b ^
                    (2 * n.choose 3 + n.choose 2)) := by
          rw [pow_mul_eq_mul_pow_mul_ssrCommutator_pow
            r v hbcenter (n + n.choose 2)]
        _ = (u ^ n * u) * (v ^ n * v) * r ^ (n + n.choose 2) *
              (b ^ (n + n.choose 2) * a ^ (n.choose 2)) *
                b ^ (n.choose 2) * a ^ (n.choose 3) *
                  b ^ (2 * n.choose 3 + n.choose 2) := by group
        _ = (u ^ n * u) * (v ^ n * v) * r ^ (n + n.choose 2) *
              (a ^ (n.choose 2) * b ^ (n + n.choose 2)) *
                b ^ (n.choose 2) * a ^ (n.choose 3) *
                  b ^ (2 * n.choose 3 + n.choose 2) := by
          have hbAccumCommAChoose : Commute
              (b ^ (n + n.choose 2)) (a ^ (n.choose 2)) :=
            (Subgroup.mem_center_iff.mp
              (hbPow (n + n.choose 2)) (a ^ (n.choose 2))).symm
          rw [hbAccumCommAChoose.eq]
        _ = (u ^ n * u) * (v ^ n * v) * r ^ (n + n.choose 2) *
              a ^ (n.choose 2) * b ^ (n + n.choose 2) *
                (b ^ (n.choose 2) * a ^ (n.choose 3)) *
                  b ^ (2 * n.choose 3 + n.choose 2) := by group
        _ = (u ^ n * u) * (v ^ n * v) * r ^ (n + n.choose 2) *
              a ^ (n.choose 2) * b ^ (n + n.choose 2) *
                (a ^ (n.choose 3) * b ^ (n.choose 2)) *
                  b ^ (2 * n.choose 3 + n.choose 2) := by
          rw [hbChooseCommAOld.eq]
        _ = (u ^ n * u) * (v ^ n * v) * r ^ (n + n.choose 2) *
              a ^ (n.choose 2) *
                (b ^ (n + n.choose 2) * a ^ (n.choose 3)) *
                  b ^ (n.choose 2) *
                    b ^ (2 * n.choose 3 + n.choose 2) := by group
        _ = (u ^ n * u) * (v ^ n * v) * r ^ (n + n.choose 2) *
              a ^ (n.choose 2) *
                (a ^ (n.choose 3) * b ^ (n + n.choose 2)) *
                  b ^ (n.choose 2) *
                    b ^ (2 * n.choose 3 + n.choose 2) := by
          have hbAccumCommAOld : Commute
              (b ^ (n + n.choose 2)) (a ^ (n.choose 3)) :=
            (Subgroup.mem_center_iff.mp
              (hbPow (n + n.choose 2)) (a ^ (n.choose 3))).symm
          rw [hbAccumCommAOld.eq]
        _ = (u ^ n * u) * (v ^ n * v) * r ^ (n + n.choose 2) *
              (a ^ (n.choose 2) * a ^ (n.choose 3)) *
                ((b ^ (n + n.choose 2) * b ^ (n.choose 2)) *
                  b ^ (2 * n.choose 3 + n.choose 2)) := by
          group
        _ = (u ^ n * u) * (v ^ n * v) * r ^ (n + n.choose 2) *
              a ^ (n.choose 2 + n.choose 3) *
                b ^ ((n + n.choose 2) + n.choose 2 +
                  (2 * n.choose 3 + n.choose 2)) := by
          rw [← pow_add a (n.choose 2) (n.choose 3),
            ← pow_add b (n + n.choose 2) (n.choose 2),
            ← pow_add b ((n + n.choose 2) + n.choose 2)
              (2 * n.choose 3 + n.choose 2)]
        _ = u ^ (n + 1) * v ^ (n + 1) * r ^ ((n + 1).choose 2) *
              a ^ ((n + 1).choose 3) *
                b ^ (2 * ((n + 1).choose 3) + (n + 1).choose 2) := by
          rw [pow_succ u n, pow_succ v n]
          simp only [hchooseTwo, hchooseThree]
          rw [show
            n + n.choose 2 + n.choose 2 +
                (2 * n.choose 3 + n.choose 2) =
              2 * (n.choose 2 + n.choose 3) + (n + n.choose 2) by omega]

theorem prime_dvd_choose_three (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    p ∣ p.choose 3 := by
  exact hp.dvd_choose_self (by norm_num) (by omega)

theorem prime_dvd_classThree_correction
    (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    p ∣ 2 * (p.choose 3) + p.choose 2 := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  exact Nat.dvd_add
    (dvd_mul_of_dvd_right (prime_dvd_choose_three p hp hp3) 2)
    (prime_dvd_choose_two p hp hpodd)

/-- For a prime greater than three, the `p`th-power map is multiplicative
when all weight-three commutators are central and all commutators have
exponent dividing `p`. -/
noncomputable def primePowerMonoidHomOfTripleCommutatorsCentral
    (p : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (htripleCentral : ∀ u v x y : G,
      Commute x (ssrCommutatorElement (ssrCommutatorElement v u) y))
    (hcommPow : ∀ x y : G, ssrCommutatorElement x y ^ p = 1) : G →* G where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' u v := by
    rw [mul_pow_of_tripleCommutators_central u v
      (htripleCentral u v) p]
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    obtain ⟨kr, hkr⟩ := prime_dvd_choose_two p hp hpodd
    obtain ⟨ka, hka⟩ := prime_dvd_choose_three p hp hp3
    obtain ⟨kb, hkb⟩ := prime_dvd_classThree_correction p hp hp3
    rw [hkb, hka, hkr, pow_mul, pow_mul, pow_mul,
      hcommPow v u,
      hcommPow (ssrCommutatorElement v u) u,
      hcommPow (ssrCommutatorElement v u) v]
    simp

@[simp]
theorem primePowerMonoidHomOfTripleCommutatorsCentral_apply
    (p : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (htripleCentral : ∀ u v x y : G,
      Commute x (ssrCommutatorElement (ssrCommutatorElement v u) y))
    (hcommPow : ∀ x y : G, ssrCommutatorElement x y ^ p = 1)
    (x : G) :
    primePowerMonoidHomOfTripleCommutatorsCentral
      p hp hp3 htripleCentral hcommPow x = x ^ p :=
  rfl

end Submission.OddOrder.MathlibSupport
