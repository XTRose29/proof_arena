import Submission.OddOrder.MathlibSupport.OmegaOneSmallNilpotency

/-!
The Hall-Petresco part of Bender-Glauberman Proposition 4.3.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- The power homomorphism used in `BGsection4.v: exponent_odd_nil23`.
The exponent bound for the first omega subgroup is established separately;
this definition packages part (b) once the derived subgroup has exponent
dividing `p`. -/
noncomputable def exponentOddNil23PowerMap
    [Group.IsNilpotent G]
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hclass : Group.nilpotencyClass G ≤ if 3 < p then 3 else 2)
    (hderivedPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1) : G →* G :=
  primePowerMonoidHomOfSmallNilpotencyClass
    p hp hpodd hclass hderivedPow

@[simp]
theorem exponentOddNil23PowerMap_apply
    [Group.IsNilpotent G]
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hclass : Group.nilpotencyClass G ≤ if 3 < p then 3 else 2)
    (hderivedPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1)
    (x : G) :
    exponentOddNil23PowerMap p hp hpodd hclass hderivedPow x = x ^ p := by
  simp [exponentOddNil23PowerMap]

/-- `BGsection4.v: exponent_odd_nil23`, part (b), in mathlib-facing form. -/
theorem exponent_odd_nil23_part_b
    [Group.IsNilpotent G]
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hclass : Group.nilpotencyClass G ≤ if 3 < p then 3 else 2)
    (hderivedPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1)
    (x y : G) :
    (x * y) ^ p = x ^ p * y ^ p := by
  let f := exponentOddNil23PowerMap p hp hpodd hclass hderivedPow
  calc
    (x * y) ^ p = f (x * y) := by simp [f]
    _ = f x * f y := f.map_mul x y
    _ = x ^ p * y ^ p := by simp [f]

/-- `BGsection4.v: exponent_odd_nil23` (Bender-Glauberman Proposition 4.3).
Part (a) controls the exponent of the first omega subgroup. Part (b) says
that `p`th powers are multiplicative when the derived subgroup is contained
in omega one. -/
theorem exponent_odd_nil23
    [Finite G]
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) (hP : IsPGroup p G)
    (hclass : Group.nilpotencyClass G ≤ if 3 < p then 3 else 2) :
    Monoid.exponent (omegaOne p G) ∣ p ∧
      (_root_.commutator G ≤ omegaOne p G →
        ∀ x y : G, (x * y) ^ p = x ^ p * y ^ p) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Group.IsNilpotent G := hP.isNilpotent
  have hOmegaPow : ∀ z : G, z ∈ omegaOne p G → z ^ p = 1 :=
    omegaOne_pow_eq_one_of_small_nilpotencyClass p hp hpodd hP hclass
  refine ⟨exponent_omegaOne_dvd p (fun z => hOmegaPow z z.property), ?_⟩
  intro hderived x y
  exact exponent_odd_nil23_part_b p hp hpodd hclass
    (fun r hr => hOmegaPow r (hderived hr)) x y

end Submission.OddOrder.BG.Section04
