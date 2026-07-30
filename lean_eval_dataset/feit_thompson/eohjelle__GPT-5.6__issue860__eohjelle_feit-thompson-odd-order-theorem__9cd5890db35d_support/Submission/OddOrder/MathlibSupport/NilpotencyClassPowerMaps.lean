import Mathlib.GroupTheory.Nilpotent
import Submission.OddOrder.MathlibSupport.NilpotencyClassThreePowers

/-!
Power maps obtained from small nilpotency-class bounds.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- A MathComp-convention commutator belongs to the corresponding mathlib
subgroup commutator. -/
theorem ssrCommutatorElement_mem_commutator
    {H K : Subgroup G} {x y : G} (hx : x ∈ H) (hy : y ∈ K) :
    ssrCommutatorElement x y ∈ ⁅H, K⁆ := by
  simpa [ssrCommutatorElement, commutatorElement_def] using
    Subgroup.commutator_mem_commutator (H.inv_mem hx) (K.inv_mem hy)

/-- If the nilpotency class is at most `n + 1`, the `n`th lower-central
subgroup is central. -/
theorem lowerCentralSeries_le_center_of_nilpotencyClass_le_succ
    [Group.IsNilpotent G] (n : ℕ)
    (hclass : Group.nilpotencyClass G ≤ n + 1) :
    (⊤ : Subgroup G).lowerCentralSeries n ≤ Subgroup.center G := by
  have hbot : (⊤ : Subgroup G).lowerCentralSeries (n + 1) = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hclass
  have hcomm : ⁅(⊤ : Subgroup G).lowerCentralSeries n, (⊤ : Subgroup G)⁆ = ⊥ := by
    simpa [Subgroup.lowerCentralSeries_succ] using hbot
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro x
  exact Subgroup.mem_centralizer_iff.mp (hcomm hz) x (Subgroup.mem_top x)

theorem commutator_le_center_of_nilpotencyClass_le_two
    [Group.IsNilpotent G] (hclass : Group.nilpotencyClass G ≤ 2) :
    _root_.commutator G ≤ Subgroup.center G := by
  rw [← Subgroup.top_lowerCentralSeries_one]
  exact lowerCentralSeries_le_center_of_nilpotencyClass_le_succ 1 hclass

/-- In a group of nilpotency class at most three, every commutator of a
commutator is central. -/
theorem tripleCommutators_central_of_nilpotencyClass_le_three
    [Group.IsNilpotent G] (hclass : Group.nilpotencyClass G ≤ 3)
    (u v x y : G) :
    Commute x (ssrCommutatorElement (ssrCommutatorElement v u) y) := by
  have hr : ssrCommutatorElement v u ∈
      (⊤ : Subgroup G).lowerCentralSeries 1 := by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact ssrCommutatorElement_mem_commutator
      (Subgroup.mem_top v) (Subgroup.mem_top u)
  have htriple : ssrCommutatorElement (ssrCommutatorElement v u) y ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 := by
    change ssrCommutatorElement (ssrCommutatorElement v u) y ∈
      ⁅(⊤ : Subgroup G).lowerCentralSeries 1, (⊤ : Subgroup G)⁆
    exact ssrCommutatorElement_mem_commutator hr (Subgroup.mem_top y)
  exact Subgroup.mem_center_iff.mp
    (lowerCentralSeries_le_center_of_nilpotencyClass_le_succ 2 hclass htriple) x

/-- In nilpotency class at most two, every weight-three commutator is
trivial. -/
theorem tripleCommutator_eq_one_of_nilpotencyClass_le_two
    [Group.IsNilpotent G] (hclass : Group.nilpotencyClass G ≤ 2)
    (u v y : G) :
    ssrCommutatorElement (ssrCommutatorElement v u) y = 1 := by
  have hr : ssrCommutatorElement v u ∈
      (⊤ : Subgroup G).lowerCentralSeries 1 := by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact ssrCommutatorElement_mem_commutator
      (Subgroup.mem_top v) (Subgroup.mem_top u)
  have htriple : ssrCommutatorElement (ssrCommutatorElement v u) y ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 := by
    change ssrCommutatorElement (ssrCommutatorElement v u) y ∈
      ⁅(⊤ : Subgroup G).lowerCentralSeries 1, (⊤ : Subgroup G)⁆
    exact ssrCommutatorElement_mem_commutator hr (Subgroup.mem_top y)
  have hbot : (⊤ : Subgroup G).lowerCentralSeries 2 = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hclass
  rw [hbot] at htriple
  exact Subgroup.mem_bot.mp htriple

/-- The odd-prime power map in nilpotency class at most two. -/
noncomputable def primePowerMonoidHomOfNilpotencyClassLETwo
    [Group.IsNilpotent G]
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hclass : Group.nilpotencyClass G ≤ 2)
    (hcommPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1) : G →* G :=
  primePowerMonoidHomOfCommutatorLeCenter p hp hpodd
    (commutator_le_center_of_nilpotencyClass_le_two hclass) hcommPow

@[simp]
theorem primePowerMonoidHomOfNilpotencyClassLETwo_apply
    [Group.IsNilpotent G]
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hclass : Group.nilpotencyClass G ≤ 2)
    (hcommPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1)
    (x : G) :
    primePowerMonoidHomOfNilpotencyClassLETwo
      p hp hpodd hclass hcommPow x = x ^ p :=
  rfl

/-- The prime power map in nilpotency class at most three, for primes greater
than three. -/
noncomputable def primePowerMonoidHomOfNilpotencyClassLEThree
    [Group.IsNilpotent G]
    (p : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (hclass : Group.nilpotencyClass G ≤ 3)
    (hcommPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1) : G →* G :=
  primePowerMonoidHomOfTripleCommutatorsCentral p hp hp3
    (fun u v x y =>
      tripleCommutators_central_of_nilpotencyClass_le_three hclass u v x y)
    (fun x y => hcommPow _
      (ssrCommutatorElement_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y)))

@[simp]
theorem primePowerMonoidHomOfNilpotencyClassLEThree_apply
    [Group.IsNilpotent G]
    (p : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (hclass : Group.nilpotencyClass G ≤ 3)
    (hcommPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1)
    (x : G) :
    primePowerMonoidHomOfNilpotencyClassLEThree
      p hp hp3 hclass hcommPow x = x ^ p :=
  rfl

/-- The two branches of Bender-Glauberman Proposition 4.3(b), packaged with
the same class bound: class at most two for small odd primes, and class at
most three above three. -/
noncomputable def primePowerMonoidHomOfSmallNilpotencyClass
    [Group.IsNilpotent G]
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hclass : Group.nilpotencyClass G ≤ if 3 < p then 3 else 2)
    (hcommPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1) : G →* G := by
  classical
  by_cases hp3 : 3 < p
  · exact primePowerMonoidHomOfNilpotencyClassLEThree p hp hp3
      (by simpa [hp3] using hclass) hcommPow
  · exact primePowerMonoidHomOfNilpotencyClassLETwo p hp hpodd
      (by simpa [hp3] using hclass) hcommPow

@[simp]
theorem primePowerMonoidHomOfSmallNilpotencyClass_apply
    [Group.IsNilpotent G]
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hclass : Group.nilpotencyClass G ≤ if 3 < p then 3 else 2)
    (hcommPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1)
    (x : G) :
    primePowerMonoidHomOfSmallNilpotencyClass
      p hp hpodd hclass hcommPow x = x ^ p := by
  classical
  by_cases hp3 : 3 < p
  · simp [primePowerMonoidHomOfSmallNilpotencyClass, hp3]
  · simp [primePowerMonoidHomOfSmallNilpotencyClass, hp3]

end Submission.OddOrder.MathlibSupport
