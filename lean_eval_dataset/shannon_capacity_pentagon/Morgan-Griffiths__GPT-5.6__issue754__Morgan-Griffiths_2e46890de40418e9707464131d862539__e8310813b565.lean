import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/shannon_capacity_pentagon_cf29d4694a/Foundation.lean

open scoped BigOperators
open BigOperators

namespace ShannonCap5Support

/-- the positive golden inverse -/
noncomputable def a : ℝ := (Real.sqrt 5 - 1) / 2
noncomputable def b : ℝ := Real.sqrt a

lemma sqrt5_nonneg : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg _
lemma sqrt5_pos : (0:ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
lemma sqrt5_sq : (Real.sqrt 5)^2 = (5:ℝ) := by norm_num
lemma sqrt5_gt_one : (1:ℝ) < Real.sqrt 5 := by nlinarith [sqrt5_sq, sqrt5_nonneg]

lemma a_pos : 0 < a := by
  unfold a
  nlinarith [sqrt5_gt_one]
lemma a_nonneg : 0 ≤ a := le_of_lt a_pos
lemma a_sq : a^2 + a = 1 := by
  unfold a
  nlinarith [sqrt5_sq]
lemma b_nonneg : 0 ≤ b := Real.sqrt_nonneg _
lemma b_pos : 0 < b := Real.sqrt_pos.2 a_pos
lemma b_sq : b^2 = a := by
  unfold b
  exact Real.sq_sqrt a_nonneg
lemma aa_compl : 1 - a = a^2 := by nlinarith [a_sq]
lemma one_sub_asq : 1 - a^2 = a := by nlinarith [a_sq]
lemma two_a_sub_a3 : 2*a - a^3 = 1 := by
  nlinarith [a_sq]
lemma two_add_a3 : 2 + a^3 = Real.sqrt 5 := by
  -- express sqrt5 = 2*a+1 from definition
  have ha : Real.sqrt 5 = 2*a + 1 := by
    unfold a; ring
  rw [ha]
  nlinarith [a_sq]

/- explicit orthogonal representation -/
noncomputable def u : Fin 5 → Fin 3 → ℝ :=
  ![ ![(1:ℝ), 0, 0],
     ![a, b, 0],
     ![0, b, a],
     ![0, 0, 1],
     ![a, -(a*b), a] ]

noncomputable def handle : Fin 3 → ℝ := ![(1:ℝ), a*b, 1]

def conf (v w : Fin 5) : Prop := v = w ∨ (SimpleGraph.cycleGraph 5).Adj v w

instance conf_dec (v w : Fin 5) : Decidable (conf v w) := by
  unfold conf
  infer_instance


lemma u_norm (v : Fin 5) :
    (∑ j : Fin 3, u v j * u v j) = (1:ℝ) := by
  fin_cases v <;>
    simp [u, Fin.sum_univ_three] <;>
    nlinarith [a_sq, b_sq]

lemma hu (v : Fin 5) :
    (∑ j : Fin 3, handle j * u v j) = (1:ℝ) := by
  fin_cases v <;>
    simp [u, handle, Fin.sum_univ_three] <;>
    nlinarith [a_sq, b_sq, two_a_sub_a3]

lemma h_norm : (∑ j : Fin 3, handle j * handle j) = Real.sqrt 5 := by
  have hab : a*b*(a*b) = a^3 := by
    calc a*b*(a*b) = a^2 * b^2 := by ring
         _ = a^3 := by rw [b_sq]; ring
  simp [handle, Fin.sum_univ_three]
  rw [hab]
  nlinarith [two_add_a3]

lemma u_orth {v w : Fin 5} (h : ¬ conf v w) :
    (∑ j : Fin 3, u v j * u w j) = (0:ℝ) := by
  -- only ten pairs; split finite values and discharge impossibles
  fin_cases v <;> fin_cases w <;>
    simp [conf, SimpleGraph.cycleGraph, u, Fin.sum_univ_three] at h ⊢ <;>
    try { contradiction } <;>
    nlinarith [a_sq, b_sq]

-- factorization of sums over functions
lemma sum_prod_functions {n m : ℕ} (g : Fin n → Fin m → ℝ) :
    (∑ f : (Fin n → Fin m), ∏ i : Fin n, g i (f i))
      = ∏ i : Fin n, ∑ j : Fin m, g i j := by
  classical
  simpa using
    (Finset.sum_prod_piFinset (R:=ℝ) (ι:=Fin n) (κ:=Fin m)
      (s:= (Finset.univ : Finset (Fin m))) g)

noncomputable def wordVec {n : ℕ} (x : Fin n → Fin 5) : (Fin n → Fin 3) → ℝ :=
  fun f => ∏ i : Fin n, u (x i) (f i)
noncomputable def Hvec (n : ℕ) : (Fin n → Fin 3) → ℝ :=
  fun f => ∏ i : Fin n, handle (f i)

lemma prod_mul_prod {n : ℕ} (p q : Fin n → ℝ) :
    (∏ i, p i) * (∏ i, q i) = ∏ i, (p i * q i) := by
  classical
  exact (Finset.prod_mul_distrib).symm

lemma word_dot_formula {n : ℕ} (x y : Fin n → Fin 5) :
   (∑ f : (Fin n → Fin 3), wordVec x f * wordVec y f)
      = ∏ i : Fin n, (∑ j : Fin 3, u (x i) j * u (y i) j) := by
  classical
  unfold wordVec
  simp_rw [prod_mul_prod]
  exact sum_prod_functions (fun i j => u (x i) j * u (y i) j)

lemma H_dot_word {n : ℕ} (x : Fin n → Fin 5) :
   (∑ f : (Fin n → Fin 3), Hvec n f * wordVec x f) = (1:ℝ) := by
  classical
  unfold Hvec wordVec
  simp_rw [prod_mul_prod]
  convert (sum_prod_functions (n:=n) (m:=3) (fun i j => handle j * u (x i) j)) using 1 <;>
    simp [hu]

lemma H_norm (n : ℕ) :
   (∑ f : (Fin n → Fin 3), Hvec n f * Hvec n f)
       = (Real.sqrt 5)^n := by
  classical
  unfold Hvec
  simp_rw [prod_mul_prod]
  convert (sum_prod_functions (n:=n) (m:=3) (fun (_i : Fin n) j => handle j * handle j)) using 1 <;>
    simp [h_norm]

lemma word_dot_self {n : ℕ} (x : Fin n → Fin 5) :
   (∑ f : (Fin n → Fin 3), wordVec x f * wordVec x f) = (1:ℝ) := by
  classical
  rw [word_dot_formula]
  simp [u_norm]

lemma word_dot_zero {n : ℕ} {x y : Fin n → Fin 5}
    (hex : ∃ i : Fin n, ¬ conf (x i) (y i)) :
   (∑ f : (Fin n → Fin 3), wordVec x f * wordVec y f) = (0:ℝ) := by
  classical
  rw [word_dot_formula]
  rcases hex with ⟨i, hi⟩
  -- product vanishes
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact u_orth hi

/-- purely real Bessel inequality for a finite orthogonal family with handle dots 1 -/
lemma card_le_norm
    {X D : Type*} [DecidableEq X] [Fintype D]
    (s : Finset X)
    (v : X → D → ℝ) (h : D → ℝ) (R : ℝ)
    (hR : (∑ d : D, h d * h d) = R)
    (hv : ∀ x ∈ s, (∑ d : D, h d * v x d) = 1)
    (hvv : ∀ x ∈ s, ∀ y ∈ s,
       (∑ d : D, v x d * v y d) = if x = y then 1 else 0) :
    (s.card : ℝ) ≤ R := by
  classical
  have hsquares : 0 ≤ ∑ d : D, (h d - ∑ x ∈ s, v x d)^2 := by
    exact Finset.sum_nonneg (fun d _ => sq_nonneg _)
  -- expand the nonnegative sum
  have hexpand :
      (∑ d : D, (h d - ∑ x ∈ s, v x d)^2)
       = R - (s.card : ℝ) := by
    -- first rearrange finite sums; ring with sums
    have comm1 : (∑ d : D, ∑ x ∈ s, h d * v x d * 2)
        = ∑ x ∈ s, ∑ d : D, h d * v x d * 2 := by
      rw [Finset.sum_comm]
    have comm2 : (∑ d : D, ∑ x ∈ s, ∑ y ∈ s, v y d * v x d)
        = ∑ x ∈ s, ∑ y ∈ s, ∑ d : D, v x d * v y d := by
      calc
        (∑ d : D, ∑ x ∈ s, ∑ y ∈ s, v y d * v x d)
            = ∑ x ∈ s, ∑ d : D, ∑ y ∈ s, v y d * v x d := by
              rw [Finset.sum_comm]
        _ = ∑ x ∈ s, ∑ y ∈ s, ∑ d : D, v y d * v x d := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_comm]
        _ = ∑ x ∈ s, ∑ y ∈ s, ∑ d : D, v x d * v y d := by
              -- just commute scalar factors
              simp only [mul_comm]

    calc
      (∑ d : D, (h d - ∑ x ∈ s, v x d)^2)
          = (∑ d : D, h d * h d)
              - 2 * (∑ x ∈ s, (∑ d : D, h d * v x d))
              + (∑ x ∈ s, ∑ y ∈ s, (∑ d : D, v x d * v y d)) := by
                -- use sum manipulation
                simp_rw [sub_sq]
                -- maybe sub_sq gives a^2 -2ab + b^2
                -- normalize squares as multiplication and distribute
                simp_rw [pow_two]
                -- grind sums
                simp_rw [Finset.mul_sum]
                simp_rw [Finset.sum_mul]
                -- at this point try ring with sum linearity
                simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                      mul_add, add_mul, mul_sub, sub_mul]
                rw [comm2]
                congr 1
                congr 1
                rw [Finset.sum_comm]
                simp [mul_assoc]
      _ = R - (s.card : ℝ) := by
            rw [hR]
            -- evaluate handle terms with hv and orthogonality
            have hsum1 : (∑ x ∈ s, (∑ d : D, h d * v x d)) = (s.card : ℝ) := by
              -- each equals 1
              calc
                (∑ x ∈ s, (∑ d : D, h d * v x d)) = ∑ _x ∈ s, (1:ℝ) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  exact hv x hx
                _ = (s.card : ℝ) := by simp
            rw [hsum1]
            have hsum2 : (∑ x ∈ s, ∑ y ∈ s, (∑ d : D, v x d * v y d)) = (s.card : ℝ) := by
              calc
                (∑ x ∈ s, ∑ y ∈ s, (∑ d : D, v x d * v y d)) =
                    ∑ x ∈ s, ∑ y ∈ s, (if x = y then (1:ℝ) else 0) := by
                      apply Finset.sum_congr rfl; intro x hx
                      apply Finset.sum_congr rfl; intro y hy
                      exact hvv x hx y hy
                _ = (s.card : ℝ) := by
                  -- inner sum has one nonzero at y=x
                  simp
            rw [hsum2]
            ring
  rw [hexpand] at hsquares
  linarith

/-- Upper bound for any independent word code in the pentagon. -/
theorem upper_bound {n : ℕ} (s : Finset (Fin n → Fin 5))
    (hind : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∃ i : Fin n, ¬ conf (x i) (y i)) :
    (s.card : ℝ) ≤ (Real.sqrt 5)^n := by
  classical
  apply card_le_norm s (fun x => wordVec x) (Hvec n) ((Real.sqrt 5)^n) (H_norm n)
  · intro x hx
    exact H_dot_word x
  · intro x hx y hy
    split_ifs with hxy
    · subst y
      exact word_dot_self x
    · exact word_dot_zero (hind x hx y hy hxy)

end ShannonCap5Support

-- END INLINED FILE: Mathlib/Support/shannon_capacity_pentagon_cf29d4694a/Foundation.lean

-- BEGIN INLINED FILE: Mathlib/Support/shannon_capacity_pentagon_cf29d4694a/Lower.lean

open scoped BigOperators
namespace ShannonCap5Support

/-- doubling map used in the five independent words of the square. -/
def twice : Fin 5 → Fin 5 := ![0, 2, 4, 1, 3]

/-- the five pairs `(t,2t)` are mutually distinguishable in the pentagon. -/
lemma block_distinct (v w : Fin 5) (h : v ≠ w) :
    (¬ conf v w) ∨ (¬ conf (twice v) (twice w)) := by
  revert v w
  decide

/-- concatenate the pair code in `m` disjoint blocks. -/
def pairWord {m : ℕ} (z : Fin m → Fin 5) : Fin (m*2) → Fin 5 :=
  fun i =>
    let p : Fin m × Fin 2 := finProdFinEquiv.symm i
    if p.2 = (0:Fin 2) then z p.1 else twice (z p.1)

@[simp] lemma pairWord_left {m} (z : Fin m → Fin 5) (j : Fin m) :
    pairWord z (finProdFinEquiv (j, (0:Fin 2))) = z j := by
  simp [pairWord]
@[simp] lemma pairWord_right {m} (z : Fin m → Fin 5) (j : Fin m) :
    pairWord z (finProdFinEquiv (j, (1:Fin 2))) = twice (z j) := by
  simp [pairWord]

lemma pairWord_injective {m : ℕ} : Function.Injective (@pairWord m) := by
  intro z z' h
  funext j
  have := congrFun h (finProdFinEquiv (j, (0:Fin 2)))
  simpa using this

lemma pairWord_separated {m : ℕ} {z z' : Fin m → Fin 5} (hzz : z ≠ z') :
    ∃ i : Fin (m*2), ¬ conf (pairWord z i) (pairWord z' i) := by
  rcases (Function.ne_iff.mp hzz) with ⟨j, hj⟩
  rcases block_distinct (z j) (z' j) hj with h | h
  · refine ⟨finProdFinEquiv (j, (0:Fin 2)), ?_⟩
    simpa using h
  · refine ⟨finProdFinEquiv (j, (1:Fin 2)), ?_⟩
    simpa using h

/-- pad a word with zeros to any longer length. -/
def extend {l n : ℕ} (hn : l ≤ n) (x : Fin l → Fin 5) : Fin n → Fin 5 :=
  fun i => if hi : i.val < l then x ⟨i.val, hi⟩ else 0

@[simp] lemma extend_cast {l n : ℕ} (hn : l ≤ n) (x : Fin l → Fin 5) (i : Fin l) :
    extend hn x (Fin.castLE hn i) = x i := by
  simp [extend, Fin.castLE]

lemma extend_injective {l n : ℕ} (hn : l ≤ n) : Function.Injective (@extend l n hn) := by
  intro x y h
  funext i
  have h' := congrFun h (Fin.castLE hn i)
  simpa using h'

lemma extend_separated {l n : ℕ} (hn : l ≤ n) {x y : Fin l → Fin 5}
    (h : ∃ i : Fin l, ¬ conf (x i) (y i)) :
    ∃ i : Fin n, ¬ conf (extend hn x i) (extend hn y i) := by
  rcases h with ⟨i, hi⟩
  exact ⟨Fin.castLE hn i, by simpa using hi⟩

/-- words of arbitrary length obtained by taking `⌊n/2⌋` good pairs and padding. -/
theorem exists_large_code (n : ℕ) :
   ∃ s : Finset (Fin n → Fin 5),
      s.card = 5^(n/2) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        ∃ i : Fin n, ¬ conf (x i) (y i) := by
  classical
  let m : ℕ := n/2
  have hle : m*2 ≤ n := by
    simpa [m] using (Nat.div_mul_le_self n 2)
  let F : (Fin m → Fin 5) → (Fin n → Fin 5) := fun z => extend hle (pairWord z)
  have hFinj : Function.Injective F :=
    (extend_injective hle).comp pairWord_injective
  let s : Finset (Fin n → Fin 5) := Finset.image F Finset.univ
  refine ⟨s, ?_, ?_⟩
  · -- card
    dsimp [s]
    rw [Finset.card_image_of_injective _ hFinj]
    simp [m]
  · intro x hx y hy hxy
    rcases (Finset.mem_image.mp hx) with ⟨z, -, rfl⟩
    rcases (Finset.mem_image.mp hy) with ⟨z', -, rfl⟩
    dsimp [F] at hxy ⊢
    have hzz : z ≠ z' := by
      intro hh
      subst z'
      exact hxy rfl
    exact extend_separated hle (pairWord_separated hzz)

end ShannonCap5Support

-- END INLINED FILE: Mathlib/Support/shannon_capacity_pentagon_cf29d4694a/Lower.lean

-- BEGIN INLINED FILE: Mathlib/Support/shannon_capacity_pentagon_cf29d4694a/Limit.lean

open Filter
open scoped Topology
namespace ShannonCap5Support

lemma floor_half_real (n : ℕ) : (n:ℝ)/2 - 1 ≤ (↑(n/2) : ℝ) := by
  have h : n < n/2*2 + 2 := by omega
  have hc : (n:ℝ) < ((n/2*2+2 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hc
  linarith

/-- elementary squeeze used for the capacity definition (we avoid any abstract
supermultiplicativity/limits). -/
theorem limit_from_bounds (A : ℕ → ℕ)
    (hlo : ∀ n, 5^(n/2) ≤ A n)
    (hhi : ∀ n, (A n : ℝ) ≤ (Real.sqrt 5)^n) :
    Tendsto (fun k : ℕ => Real.rpow (A (k+1) : ℝ) ((k+1 : ℝ)⁻¹))
      atTop (𝓝 (Real.sqrt 5)) := by
  -- a convenient lower sequence
  let low : ℕ → ℝ := fun k =>
        Real.rpow 5 ((1/2:ℝ) - ((k+1:ℝ))⁻¹)
  have tn : Tendsto (fun k : ℕ => ((k+1 : ℕ):ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have ti : Tendsto (fun k : ℕ => ((k+1:ℝ))⁻¹) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.comp tn using 1 <;>
      ext k <;> push_cast <;> simp [Nat.cast_add]
  have te : Tendsto (fun k : ℕ => (1/2:ℝ) - ((k+1:ℝ))⁻¹) atTop (𝓝 (1/2:ℝ)) := by
    convert tendsto_const_nhds.sub ti using 1 <;> norm_num
  have tlow : Tendsto low atTop (𝓝 (Real.sqrt 5)) := by
    have tc := (Real.continuous_const_rpow (by norm_num : (5:ℝ) ≠ 0)).tendsto (1/2:ℝ)
    have tt := tc.comp te
    -- sqrt is rpow one-half
    convert tt using 1 <;>
      simp [low, Real.sqrt_eq_rpow, Function.comp_def]
  have huconst : Tendsto (fun _k : ℕ => Real.sqrt 5) atTop (𝓝 (Real.sqrt 5)) :=
    tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tlow huconst ?_ ?_
  · filter_upwards [] with k
    -- compare lower bound
    let n : ℕ := k+1
    have hn : 0 < n := by dsimp [n]; omega
    have hcastpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hfloor := floor_half_real n
    have hexp : (1/2:ℝ) - ((n:ℝ))⁻¹ ≤ (↑(n/2) : ℝ) * ((n:ℝ))⁻¹ := by
      have := hfloor
      -- divide by n
      have := (div_le_div_of_nonneg_right hfloor (le_of_lt hcastpos))
      -- simplify
      field_simp at this ⊢
      linarith
    have hpowlow :
        Real.rpow 5 ((1/2:ℝ) - ((n:ℝ))⁻¹)
          ≤ Real.rpow (A n : ℝ) ((n:ℝ)⁻¹) := by
      calc
        _ ≤ Real.rpow 5 ((↑(n/2):ℝ) * ((n:ℝ)⁻¹)) :=
           Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = Real.rpow ((5:ℝ)^(n/2)) ((n:ℝ)⁻¹) := by
              exact Real.rpow_natCast_mul (x := (5:ℝ)) (by norm_num) (n/2) ((n:ℝ)⁻¹)
        _ ≤ _ := by
              apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
              exact_mod_cast (hlo n)
    simpa [low, n] using hpowlow
  · filter_upwards [] with k
    let n : ℕ := k+1
    have hn : n ≠ 0 := by dsimp [n]; omega
    have hcast : (n:ℝ) ≠ 0 := by exact_mod_cast hn
    have hp : Real.rpow (A n : ℝ) ((n:ℝ)⁻¹)
          ≤ Real.rpow ((Real.sqrt 5)^n) ((n:ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) (hhi n) (by positivity)
    calc
      Real.rpow (A (k+1) : ℝ) ((k+1:ℝ)⁻¹)
          = Real.rpow (A n : ℝ) ((n:ℝ)⁻¹) := by simp [n, Nat.cast_add, Nat.cast_one]
      _ ≤ Real.rpow ((Real.sqrt 5)^n) ((n:ℝ)⁻¹) := hp
      _ = Real.sqrt 5 := by
        calc
          Real.rpow ((Real.sqrt 5)^n) ((n:ℝ)⁻¹) =
              Real.rpow (Real.sqrt 5) ((n:ℝ) * ((n:ℝ)⁻¹)) := by
                exact (Real.rpow_natCast_mul (x:=Real.sqrt 5) (Real.sqrt_nonneg _) n ((n:ℝ)⁻¹)).symm
          _ = Real.sqrt 5 := by
            have hh : (n:ℝ) * (n:ℝ)⁻¹ = 1 := by simp [hcast]
            rw [hh]
            simp

end ShannonCap5Support

-- END INLINED FILE: Mathlib/Support/shannon_capacity_pentagon_cf29d4694a/Limit.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval.Combinatorics.ShannonCapacityPentagon

/-!
# Shannon capacity of the pentagon (Lovász)

`shannon_capacity_pentagon`: the Shannon capacity of the five-cycle `C₅` is
`√5`. Trusted helpers `IsIndependent`, `independenceNumber`, `strongPower`,
`HasShannonCapacity` (non-holes). Mathlib has simple graphs and cycle graphs but
no Shannon capacity, strong graph powers, or Lovász number. Category-(b)
candidate from §238 of the Knill survey.
-/

open Filter
open scoped Topology

/-- A finite set of vertices is independent if no two distinct members are adjacent. -/
def IsIndependent {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ ⦃v⦄, v ∈ s → ∀ ⦃w⦄, w ∈ s → v ≠ w → ¬ G.Adj v w

/-- The independence number of a finite simple graph. -/
noncomputable def independenceNumber (V : Type*) [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup {m : ℕ | ∃ s : Finset V, IsIndependent G s ∧ s.card = m}

/-- The strong graph power on length-`k` words.  Two words are confusable
when they are distinct and every coordinate is either equal or confusable in
the base graph. -/
def strongPower {V : Type*} (G : SimpleGraph V) (k : ℕ) : SimpleGraph (Fin k → V) where
  Adj x y := x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)
  symm.symm x y := by
    rintro ⟨hxy, hcoord⟩
    exact ⟨hxy.symm, fun i => (hcoord i).imp Eq.symm SimpleGraph.Adj.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- The Shannon capacity of `G` is `θ` if the normalized independence
numbers of the strong powers tend to `θ`. -/
noncomputable def HasShannonCapacity {V : Type*} [Fintype V] (G : SimpleGraph V) (θ : ℝ) :
    Prop :=
  Tendsto
    (fun k : ℕ =>
      Real.rpow
        (independenceNumber (Fin (k + 1) → V) (strongPower G (k + 1)) : ℝ)
        ((k + 1 : ℝ)⁻¹))
    atTop (𝓝 θ)



end LeanEval.Combinatorics.ShannonCapacityPentagon

open LeanEval.Combinatorics.ShannonCapacityPentagon
open Filter
open scoped Topology
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem shannon_capacity_pentagon :
    HasShannonCapacity (SimpleGraph.cycleGraph 5) (Real.sqrt 5) :=
/-ResultProofBegin-/by
  classical
  -- abbreviate the independence numbers of words of length `n`
  let A : ℕ → ℕ := fun n =>
    independenceNumber (Fin n → Fin 5)
      (strongPower (SimpleGraph.cycleGraph 5) n)
  have bdd (n : ℕ) :
      BddAbove {m : ℕ | ∃ s : Finset (Fin n → Fin 5),
        IsIndependent (strongPower (SimpleGraph.cycleGraph 5) n) s ∧ s.card = m} := by
    refine ⟨Fintype.card (Fin n → Fin 5), ?_⟩
    intro t ht
    rcases ht with ⟨s, hs, rfl⟩
    exact Finset.card_le_univ s
  have nonemptyS (n : ℕ) :
      ({m : ℕ | ∃ s : Finset (Fin n → Fin 5),
        IsIndependent (strongPower (SimpleGraph.cycleGraph 5) n) s ∧ s.card = m} : Set ℕ).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, ?_, rfl⟩
    intro v hv
    simp at hv
  have memmax (n : ℕ) :
      A n ∈ {m : ℕ | ∃ s : Finset (Fin n → Fin 5),
        IsIndependent (strongPower (SimpleGraph.cycleGraph 5) n) s ∧ s.card = m} := by
    -- a supremum of a nonempty bounded set of naturals is attained
    change sSup _ ∈ _
    exact Nat.sSup_mem (nonemptyS n) (bdd n)
  have hlo : ∀ n : ℕ, 5^(n/2) ≤ A n := by
    intro n
    rcases ShannonCap5Support.exists_large_code n with ⟨s, hcard, hsep⟩
    have hs : IsIndependent (strongPower (SimpleGraph.cycleGraph 5) n) s := by
      intro x hx y hy hxy
      intro hadj
      rcases hsep x hx y hy hxy with ⟨i, hi⟩
      exact hi (hadj.2 i)
    -- this cardinality is one of the elements defining the supremum
    have helem : 5^(n/2) ∈ {m : ℕ | ∃ s : Finset (Fin n → Fin 5),
        IsIndependent (strongPower (SimpleGraph.cycleGraph 5) n) s ∧ s.card = m} := by
      exact ⟨s, hs, hcard⟩
    change 5^(n/2) ≤ sSup _
    exact le_csSup (bdd n) helem
  have hhi : ∀ n : ℕ, (A n : ℝ) ≤ (Real.sqrt 5)^n := by
    intro n
    rcases memmax n with ⟨s, hs, hc⟩
    have hind : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
          ∃ i : Fin n, ¬ ShannonCap5Support.conf (x i) (y i) := by
      intro x hx y hy hxy
      by_contra h
      push_neg at h
      have hadj : (strongPower (SimpleGraph.cycleGraph 5) n).Adj x y :=
        ⟨hxy, h⟩
      exact hs hx hy hxy hadj
    have hb := ShannonCap5Support.upper_bound s hind
    rw [hc] at hb
    exact hb
  -- our elementary squeeze lemma now has exactly the sequence in the definition
  unfold HasShannonCapacity
  exact ShannonCap5Support.limit_from_bounds A hlo hhi
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
