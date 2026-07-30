import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/Dyadic.lean

/-! Elementary analytic reduction for Brun-style estimates. -/
namespace BrunSupport
open Filter Finset MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- The finite dyadic interval `[2^k,2^(k+1))` in the natural numbers. -/
def block (k : ℕ) : Finset ℕ := Finset.Ico (2^k) (2^(k+1))

/-- Elements in a dyadic block satisfying a predicate. -/
def blockSet (P : ℕ → Prop) [DecidablePred P] (k : ℕ) : Finset ℕ :=
  (block k).filter P

@[simp] lemma mem_block {k p : ℕ} : p ∈ block k ↔ 2^k ≤ p ∧ p < 2^(k+1) := by
  simp [block]

@[simp] lemma mem_blockSet {P : ℕ → Prop} [DecidablePred P] {k p : ℕ} :
    p ∈ blockSet P k ↔ p ∈ block k ∧ P p := by
  simp [blockSet]

lemma succ_mem_own_block (i : ℕ) : i+1 ∈ block (Nat.log 2 (i+1)) := by
  have hp : i+1 ≠ 0 := Nat.succ_ne_zero _
  -- the standard defining inequalities for the natural logarithm
  rw [mem_block]
  constructor
  · simpa using (Nat.pow_log_le_self 2 hp)
  · have h := Nat.lt_pow_succ_log_self (by decide : 1 < (2:ℕ)) (i+1)
    -- `succ` and `+1` in the exponent are the same
    simpa [Nat.succ_eq_add_one] using h

/-- On a block, nonzero terms may be summed only over the satisfying set. -/
lemma sum_block_eq_filter {P : ℕ → Prop} [DecidablePred P] (f : ℕ → ℝ)
    (hz : ∀ n, ¬ P n → f n = 0) (k : ℕ) :
    ∑ p ∈ block k, f p = ∑ p ∈ blockSet P k, f p := by
  classical
  symm
  apply Finset.sum_subset (by
    intro p hp
    exact (Finset.mem_filter.1 hp).1)
  intro p hp hp'
  have hnp : ¬ P p := by
    intro hP
    exact hp' (Finset.mem_filter.2 ⟨hp, hP⟩)
  exact hz p hnp

/-- Summing a nonnegative function over a block is bounded by the cardinality of
its support there times a uniform bound. -/
lemma sum_block_le_card {P : ℕ → Prop} [DecidablePred P] (f : ℕ → ℝ)
    (hz : ∀ n, ¬ P n → f n = 0) {k : ℕ} {a : ℝ}
    (ha : ∀ p ∈ block k, P p → f p ≤ a) :
    ∑ p ∈ block k, f p ≤ (blockSet P k).card * a := by
  classical
  rw [sum_block_eq_filter f hz k]
  -- all elements of the filtered block satisfy the pointwise estimate
  calc
    ∑ p ∈ blockSet P k, f p ≤ (blockSet P k).card • a :=
      Finset.sum_le_card_nsmul _ _ _ (by
        intro p hp
        have hp' := (mem_blockSet.mp hp)
        exact ha p hp'.1 hp'.2)
    _ = (blockSet P k).card * a := by simp [nsmul_eq_mul]

/-- Sending indices to their logarithmic block splits any finite partial sum
into fibres.  Each fibre over `k` injects into the whole block `k`. -/
lemma sum_range_succ_le_sum_blocks {P : ℕ → Prop} [DecidablePred P]
    (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (n : ℕ) :
    ∑ i ∈ Finset.range n, f (i+1)
      ≤ ∑ k ∈ Finset.range (n+1), (∑ p ∈ block k, f p) := by
  classical
  let e : ℕ ↪ ℕ := ⟨(fun i : ℕ => i+1), by
    intro a b hab
    exact Nat.add_right_cancel hab⟩
  -- all logarithms of the indices of the partial sum lie in `range (n+1)`
  have maps : ∀ i ∈ Finset.range n, Nat.log 2 (i+1) ∈ Finset.range (n+1) := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hle : Nat.log 2 (i+1) ≤ i+1 := Nat.log_le_self _ _
    apply Finset.mem_range.mpr
    exact lt_of_le_of_lt hle (by omega)
  have split := Finset.sum_fiberwise_of_maps_to (s := Finset.range n)
      (t := Finset.range (n+1)) (g := fun i : ℕ => Nat.log 2 (i+1))
      maps (fun i : ℕ => f (i+1))
  -- it remains to bound each fibre by the full block
  calc
    ∑ i ∈ Finset.range n, f (i+1)
        = ∑ k ∈ Finset.range (n+1),
            ∑ i ∈ (Finset.range n).filter (fun i => Nat.log 2 (i+1) = k),
              f (i+1) := by simpa using split.symm
    _ ≤ ∑ k ∈ Finset.range (n+1), (∑ p ∈ block k, f p) := by
      apply Finset.sum_le_sum
      intro k hk
      let t : Finset ℕ := (Finset.range n).filter (fun i => Nat.log 2 (i+1) = k)
      have sub : t.map e ⊆ block k := by
        intro p hp
        rcases (Finset.mem_map.mp hp) with ⟨i, hi, rfl⟩
        have hlog : Nat.log 2 (i+1) = k := (Finset.mem_filter.mp hi).2
        simpa [e, hlog] using (succ_mem_own_block i)
      -- first replace the fibre by its mapped copy, then enlarge it
      calc
        ∑ i ∈ (Finset.range n).filter (fun i => Nat.log 2 (i+1) = k), f (i+1)
            = ∑ p ∈ t.map e, f p := by
                -- `sum_map` is stated with the sum over the mapped set first
                symm
                simpa [t, e] using
                  (Finset.sum_map (s := t) e (fun p : ℕ => f p))
        _ ≤ ∑ p ∈ block k, f p := by
          exact Finset.sum_le_sum_of_subset_of_nonneg sub (by
            intro p hp hp'
            exact hf p)

/-- The elementary analytic part of the dyadic argument.

If the number of surviving elements in the `k`th dyadic block is at most
`C * 2^k / (k+1)^2`, and a surviving element contributes at most `2 / 2^k`,
then the series of contributions converges.  This lemma deliberately contains
no number theory. -/
theorem summable_of_card_bound
    (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (hz : ∀ n, ¬ P n → f n = 0)
    (hle : ∀ k p, p ∈ block k → P p → f p ≤ 2 / ((2:ℝ)^k))
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ k, ((blockSet P k).card : ℝ)
          ≤ C * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2)) :
    Summable f := by
  classical
  -- a convenient summable majorant for the totals of the blocks
  let g : ℕ → ℝ := fun k => (2*C) * ((((k+1:ℕ):ℝ)^2)⁻¹)
  have hg : Summable g := by
    have hs0 : Summable (fun k : ℕ => (((k:ℝ)^ (2:ℝ))⁻¹)) :=
      (Real.summable_nat_rpow_inv.2 (by norm_num : (1:ℝ) < 2))
    -- translate from `n` to `n+1`, and integer squares to rpow
    have hs1 : Summable (fun k : ℕ => ((((k+1:ℕ):ℝ) ^ (2:ℝ))⁻¹)) :=
      (summable_nat_add_iff 1).2 hs0
    have hs2 : Summable (fun k : ℕ => ((((k+1:ℕ):ℝ)^ (2:ℕ))⁻¹)) := by
      simpa [Real.rpow_natCast_mul, Real.rpow_natCast] using hs1
    -- `Real.rpow_natCast` simplification is sometimes just `zpow`; a direct
    -- `convert` below keeps the normalization local.
    exact (by
      -- scalar multiplication of a summable real series
      simpa [g] using hs2.mul_left (2*C))
  have hg0 : ∀ k, 0 ≤ g k := by
    intro k
    dsimp [g]
    positivity
  have hblock : ∀ k, (∑ p ∈ block k, f p) ≤ g k := by
    intro k
    calc
      ∑ p ∈ block k, f p
          ≤ ((blockSet P k).card : ℝ) * (2 / ((2:ℝ)^k)) :=
            sum_block_le_card f hz (k:=k) (a:=2 / ((2:ℝ)^k)) (hle k)
      _ ≤ (C * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2)) * (2 / ((2:ℝ)^k)) := by
            gcongr
            exact hc k
      _ = g k := by
          dsimp [g]
          have hpow : ( (2:ℝ)^k) ≠ 0 := by positivity
          field_simp
          <;> ring
  -- bounded partial sums of the tail beginning at one
  have tail : Summable (fun i : ℕ => f (i+1)) := by
    refine summable_of_sum_range_le (c := ∑' k : ℕ, g k) (fun i => hf _) ?_
    intro n
    calc
      ∑ i ∈ Finset.range n, f (i+1)
          ≤ ∑ k ∈ Finset.range (n+1), (∑ p ∈ block k, f p) :=
            sum_range_succ_le_sum_blocks (P:=P) f hf n
      _ ≤ ∑ k ∈ Finset.range (n+1), g k := by
            exact Finset.sum_le_sum (by
              intro k hk
              exact hblock k)
      _ ≤ ∑' k : ℕ, g k :=
            Summable.sum_le_tsum _ (by
              intro k hk
              exact hg0 k) hg
  -- adding/removing the initial term is immaterial
  exact (summable_nat_add_iff 1).1 (by simpa [Nat.add_comm] using tail)

end
end BrunSupport

-- END INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/Dyadic.lean

-- BEGIN INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/Avoid.lean

/-! The elementary reduction from twin primes to the usual residue-class
upper-bound sieve problem.  Nothing here is a sieve estimate. -/
namespace BrunSupport
open Finset
open scoped BigOperators Topology
noncomputable section

/-- `Avoid z n` is the condition seen by the (upper-bound) sieve: no prime
smaller than `z` divides either `n` or `n+2`.  It is intentionally formulated
with divisibility rather than primality of `n`. -/
def Avoid (z n : ℕ) : Prop :=
  ∀ q : ℕ, q < z → q.Prime → ¬ q ∣ n ∧ ¬ q ∣ (n+2)

instance (z : ℕ) : DecidablePred (Avoid z) := Classical.decPred _

@[simp] lemma mem_avoidBlock {z k p : ℕ} :
    p ∈ (block k).filter (Avoid z) ↔ p ∈ block k ∧ Avoid z p := by
  classical simp

/-- A divisor of a prime natural number which is itself prime must equal it. -/
lemma eq_prime_of_prime_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : q ∣ p) : q = p := by
  rcases ((Nat.dvd_prime hp).mp h) with h1 | hqp
  · exact (hq.ne_one h1).elim
  · exact hqp

-- a version using only the standard `dvd_prime` lemma (the name
-- `Prime.dvd_nat` has changed over time) is below; `simp` fixes the interface.

/-- If `n,n+2` are primes and both exceed `q`, the prime `q` is a forbidden
local divisor. -/
lemma avoid_of_twins_of_le {X n : ℕ}
    (hX : X ≤ n) (hn : n.Prime ∧ (n+2).Prime) : Avoid X n := by
  intro q hq hprime
  constructor
  · intro hd
    have hEq : q = n := eq_prime_of_prime_dvd hn.1 hprime hd
    omega
  · intro hd
    have hEq : q = n + 2 := eq_prime_of_prime_dvd hn.2 hprime hd
    omega

/-- The elementary form of the sift: it is just coprimality of the
polynomial `n(n+2)` with a primorial.  This is the interface to an
upper-bound Selberg sieve (whose support consists of the values `n(n+2)`). -/
lemma avoid_iff_coprime_primorial (z n : ℕ) :
    Avoid z n ↔ Nat.Coprime (primorial (z-1)) (n*(n+2)) := by
  classical
  cases z with
  | zero =>
      constructor
      · intro h
        simpa using (Nat.one_coprime (n*(n+2)))
      · intro h q hq
        omega
  | succ z =>
      constructor
      · intro h
        -- expand the primorial and ask separately for each prime factor
        unfold primorial
        apply (Nat.coprime_prod_left_iff).2
        intro q hq
        have hmem := (Finset.mem_filter.mp hq)
        have hlt : q < z + 1 := Finset.mem_range.mp hmem.1
        have ha := h q (by simpa using hlt) hmem.2
        exact (hmem.2.coprime_iff_not_dvd).2 (by
          intro hd
          exact (hmem.2.dvd_mul.mp hd).elim ha.1 ha.2)
      · intro h q hlt hq
        have h' : (∏ p ∈ (Finset.range (z+1)).filter Nat.Prime, p).Coprime
            (n*(n+2)) := by
          simpa [primorial] using h
        have H : ∀ p ∈ (Finset.range (z+1)).filter Nat.Prime,
            Nat.Coprime p (n*(n+2)) :=
          (Nat.coprime_prod_left_iff).1 h' 
        have hc := H q (Finset.mem_filter.mpr ⟨by simpa using hlt, hq⟩)
        have hn : ¬ q ∣ n*(n+2) := (hq.coprime_iff_not_dvd).1 hc
        constructor
        · intro hnq; exact hn (dvd_mul_of_dvd_left hnq _)
        · intro hnq; exact hn (dvd_mul_of_dvd_right hnq _)

lemma avoid_iff_forbidden_product (z n : ℕ) :
    Avoid z n ↔ Nat.Coprime (primorial (z-1)) (n*(n+2)) :=
  avoid_iff_coprime_primorial z n

/-- The small cutoff used below.  Any fixed positive fraction of the
logarithm is suitable for an upper-bound sieve; using powers of two keeps it
integral and avoids floors of logarithms. -/
def cutoff (k : ℕ) : ℕ := 2 ^ (k / 4)

lemma cutoff_le_main (k : ℕ) : cutoff k ≤ 2^k := by
  unfold cutoff
  exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (Nat.div_le_self k 4)

/-- Every twin-prime start in the `k`th block survives all the local tests up
to `cutoff k`. -/
lemma twin_block_subset_avoid (k : ℕ) :
    (block k).filter (fun p : ℕ => p.Prime ∧ (p+2).Prime)
       ⊆ (block k).filter (Avoid (cutoff k)) := by
  classical
  intro p hp
  have h := Finset.mem_filter.mp hp
  refine Finset.mem_filter.mpr ⟨h.1, ?_⟩
  have hbase : 2^k ≤ p := (mem_block.mp h.1).1
  have hbig : cutoff k ≤ p := le_trans (cutoff_le_main k) hbase
  exact avoid_of_twins_of_le hbig h.2

lemma twin_block_card_le_avoid (k : ℕ) :
    ((blockSet (fun p : ℕ => p.Prime ∧ (p+2).Prime) k).card : ℝ)
      ≤ (((block k).filter (Avoid (cutoff k))).card : ℝ) := by
  classical
  exact_mod_cast (Finset.card_le_card (twin_block_subset_avoid k))

/-- The purely upper-bound-sieve statement which suffices from this point on.
It mentions no primality of the sifted number, only forbidden residue
classes. -/
def survivorCount (k : ℕ) : ℕ :=
  ((block k).filter (Avoid (cutoff k))).card

@[simp] lemma twin_card_le_survivor (k : ℕ) :
    ((blockSet (fun p : ℕ => p.Prime ∧ (p+2).Prime) k).card : ℝ)
      ≤ (survivorCount k : ℝ) := by
  simpa [survivorCount] using (twin_block_card_le_avoid k)

end
end BrunSupport

-- END INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/Avoid.lean

-- BEGIN INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/Polynomial.lean

namespace BrunSupport
open Finset
open scoped BigOperators Topology
noncomputable section

/-- The polynomial to which the ordinary one-dimensional Selberg sieve is
applied for twin primes.  It is injective on the naturals. -/
def poly (n : ℕ) : ℕ := n * (n+2)

lemma poly_injective : Function.Injective poly := by
  intro a b h
  unfold poly at h
  nlinarith

/-- We can therefore use the values of `n(n+2)` as the support of the
one-dimensional sieve without multiplicities. -/
def polyEmb : ℕ ↪ ℕ := ⟨poly, poly_injective⟩

def valueBlock (k : ℕ) : Finset ℕ := (block k).map polyEmb

@[simp] lemma mem_valueBlock {k m : ℕ} :
    m ∈ valueBlock k ↔ ∃ n ∈ block k, poly n = m := by
  classical
  simp [valueBlock, polyEmb]

/-- The sifted version, now literally a gcd condition with the product of
small primes.  This is the `siftedSum` of the associated `BoundingSieve`
with all weights equal to one. -/
def coprimeValueCount (k : ℕ) : ℕ :=
  ((valueBlock k).filter
    (fun m : ℕ => Nat.Coprime (primorial (cutoff k - 1)) m)).card

/-- The two finite cardinalities agree.  Injectivity of `n(n+2)` is the small
point which permits use of a `Finset` (rather than a multiset) as the support
of a Selberg sieve. -/
lemma survivorCount_eq_coprimeValueCount (k : ℕ) :
    survivorCount k = coprimeValueCount k := by
  classical
  unfold survivorCount coprimeValueCount valueBlock
  -- commute the filter with the injective map
  rw [Finset.filter_map]
  rw [Finset.card_map]
  -- the predicates on the original interval are the same (`p ∘ poly`)
  congr 1
  ext n
  simp [Function.comp_def, polyEmb, poly, avoid_iff_coprime_primorial]

end
end BrunSupport

namespace BrunSupport
open Finset
open scoped BigOperators Topology

lemma block_card (k : ℕ) : (block k).card = 2^k := by
  unfold block
  rw [Nat.card_Ico]
  rw [Nat.two_pow_succ]
  have hpos : 0 < 2^k := Nat.two_pow_pos k
  omega

lemma valueBlock_card (k : ℕ) : (valueBlock k).card = 2^k := by
  classical
  unfold valueBlock
  rw [Finset.card_map, block_card]

lemma coprimeValueCount_le_pow (k : ℕ) : coprimeValueCount k ≤ 2^k := by
  classical
  unfold coprimeValueCount
  exact (Finset.card_filter_le _ _).trans_eq (valueBlock_card k)

/-- A tail estimate is enough. The first four dyadic blocks are absorbed into
one universal constant; this keeps floors in the sieve level away from the
Selberg-sieve input. -/
lemma all_coprimeValue_bound_of_tail
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ k, 4 ≤ k → (coprimeValueCount k : ℝ)
          ≤ C * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2)) :
    let D := max C 16
    0 ≤ D ∧ ∀ k, (coprimeValueCount k : ℝ)
          ≤ D * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2) := by
  classical
  dsimp
  constructor
  · exact le_trans hC (le_max_left ..)
  intro k
  by_cases hk : 4 ≤ k
  · have H := h k hk
    have pos : 0 ≤ (2:ℝ)^k / (((k+1:ℕ):ℝ)^2) := by positivity
    calc
      (coprimeValueCount k : ℝ)
          ≤ C * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2) := H
      _ ≤ max C 16 * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2) := by
            have hcmax : C ≤ max C 16 := le_max_left _ _
            convert (mul_le_mul_of_nonneg_right hcmax pos) using 1 <;> first | rfl | ring
  · have hk' : k ≤ 3 := by omega
    have hf : (coprimeValueCount k : ℝ) ≤ (2:ℝ)^k := by
      exact_mod_cast (coprimeValueCount_le_pow k)
    have hs : (((k+1:ℕ):ℝ)^2) ≤ 16 := by
      interval_cases k <;> norm_num at *
    have hden : 0 < (((k+1:ℕ):ℝ)^2) := by positivity
    calc
      (coprimeValueCount k : ℝ) ≤ (2:ℝ)^k := hf
      _ ≤ (16:ℝ) * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2) := by
        apply (le_div_iff₀ hden).2
        nlinarith [show 0 ≤ (2:ℝ)^k by positivity]
      _ ≤ max C 16 * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2) := by
        have H : (16:ℝ) ≤ max C 16 := le_max_right _ _
        have pos : 0 ≤ (2:ℝ)^k / (((k+1:ℕ):ℝ)^2) := by positivity
        calc
          (16:ℝ) * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2)
              = 16 * ((2:ℝ)^k / (((k+1:ℕ):ℝ)^2)) := by ring
          _ ≤ max C 16 * ((2:ℝ)^k / (((k+1:ℕ):ℝ)^2)) :=
                mul_le_mul_of_nonneg_right H pos
          _ = _ := by ring
end BrunSupport

-- END INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/Polynomial.lean

-- BEGIN INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/SelbergStart.lean

/-! Elementary, completely finite pieces of the Selberg-sieve reduction.
In particular the interval error `<= number of residues` is uniform in the
left endpoint.  This is the often useful little periodicity lemma; it is
separate from any analytic estimate in the sieve. -/
namespace BrunSupport
open Finset
open Function
open scoped BigOperators

/-- Breaking up an interval into complete periods.  Notice that no
probability/counting estimate is involved: the last, incomplete period is
literally a subinterval of a complete period with the same starting point.
This version is in `Nat`, hence is convenient for applying it to divisor
counts before taking a real coercion in a bounding sieve. -/
lemma periodic_Ico_decompose {d : ℕ} (hd : 0 < d)
    (p : ℕ → Prop) [DecidablePred p] (hp : Function.Periodic p d)
    (a N : ℕ) : ∃ t : ℕ, t ≤ d.count p ∧
      ((Finset.Ico a (a + N)).filter p).card =
        (N / d) * (d.count p) + t := by
  classical
  let c : ℕ := d.count p
  have hc (x : ℕ) :
      ((Finset.Ico x (x + d)).filter p).card = c := by
    simpa [c] using (Nat.filter_Ico_card_eq_of_periodic x d p hp)
  have split (x u v : ℕ) :
      ((Finset.Ico x (x + (u + v))).filter p).card =
        ((Finset.Ico x (x + u)).filter p).card +
        ((Finset.Ico (x + u) (x + u + v)).filter p).card := by
    have Hunion :
        Finset.Ico x (x + (u + v)) =
          Finset.Ico x (x + u) ∪ Finset.Ico (x + u) (x + u + v) := by
      -- the library lemma uses a middle end point and two inequalities
      have U := Finset.Ico_union_Ico_eq_Ico (α:=ℕ)
        (a:=x) (b:=x+u) (c:=x+u+v) (by omega) (by omega)
      have E : x + (u+v) = x+u+v := by omega
      rw [E]
      exact U.symm
    have hdis :
        Disjoint (Finset.Ico x (x + u))
          (Finset.Ico (x + u) (x + u + v)) := by
      exact Finset.disjoint_left.mpr (by
        intro n h1 h2
        have h1' := (Finset.mem_Ico.mp h1).2
        have h2' := (Finset.mem_Ico.mp h2).1
        omega)
    have fd : Disjoint ((Finset.Ico x (x+u)).filter p)
          ((Finset.Ico (x+u) (x+u+v)).filter p) :=
      Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdis
    rw [Hunion, Finset.filter_union, Finset.card_union_of_disjoint fd]
  -- first do the division algorithm by hand.  This form lets the induction
  -- be independent of the left end point.
  have tile : ∀ q : ℕ, ∀ x r : ℕ, r < d → ∃ t : ℕ, t ≤ c ∧
      ((Finset.Ico x (x + (q*d + r))).filter p).card = q*c + t := by
    intro q
    induction q with
    | zero =>
      intro x r hr
      refine ⟨((Finset.Ico x (x+r)).filter p).card, ?_, ?_⟩
      · -- enlarge the incomplete piece to a full period
        have sub : (Finset.Ico x (x+r)).filter p ⊆
            (Finset.Ico x (x+d)).filter p := by
          intro z hz
          have h := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨(Finset.mem_Ico.mp h.1 |>.elim (fun h0 h1 =>
            Finset.mem_Ico.mpr ⟨h0, by omega⟩)), h.2⟩
        simpa [hc x] using (Finset.card_le_card sub)
      · simp
    | succ q ih =>
      intro x r hr
      obtain ⟨t, ht, he⟩ := ih (x+d) r hr
      refine ⟨t, ht, ?_⟩
      -- split off the first complete period
      have Htail :
          ((Finset.Ico (x+d) (x+d + (q*d+r))).filter p).card = q*c + t := he
      calc
        ((Finset.Ico x (x + ((Nat.succ q)*d+r))).filter p).card
            = ((Finset.Ico x (x + (d + (q*d+r)))).filter p).card := by
                congr 4
                simp [Nat.succ_eq_add_one, Nat.add_mul]
                omega
        _ = ((Finset.Ico x (x+d)).filter p).card +
              ((Finset.Ico (x+d) (x+d+(q*d+r))).filter p).card :=
                 split x d (q*d+r)
        _ = c + (q*c+t) := by rw [hc x, Htail]
        _ = (Nat.succ q)*c + t := by
              simp [Nat.succ_eq_add_one, Nat.add_mul]
              omega
  let q := N / d
  let r := N % d
  have hr : r < d := by simpa [r] using (Nat.mod_lt N hd)
  obtain ⟨t, ht, he⟩ := tile q a r hr
  refine ⟨t, ?_, ?_⟩
  · simpa [c] using ht
  have eN : q*d + r = N := by
    simpa [q, r, Nat.mul_comm] using (Nat.div_add_mod N d)
  simpa [q, r, c, eN] using he

/-- In particular the count in an interval is at most the expected number
of complete boxes plus one box of residues.  This innocuous lemma is useful
on its own: the error does not depend on the (possibly enormous) endpoint. -/
lemma periodic_Ico_card_le {d : ℕ} (hd : 0 < d)
    (p : ℕ → Prop) [DecidablePred p] (hp : Function.Periodic p d)
    (a N : ℕ) :
      ((Finset.Ico a (a + N)).filter p).card ≤
        (N / d + 1) * (d.count p) := by
  classical
  obtain ⟨t, ht, he⟩ := periodic_Ico_decompose hd p hp a N
  -- deliberately state the bound this way, without fractions
  calc
    ((Finset.Ico a (a+N)).filter p).card = (N/d) * (d.count p) + t := he
    _ ≤ (N/d) * (d.count p) + (d.count p) := Nat.add_le_add_left ht _
    _ = (N/d+1) * (d.count p) := by
      simp [Nat.add_mul]

/-- The corresponding real error is at most one complete residue box.  This
is the exact remainder used by a one-dimensional Selberg sieve. -/
lemma periodic_Ico_abs_error {d : ℕ} (hd : 0 < d)
    (p : ℕ → Prop) [DecidablePred p] (hp : Function.Periodic p d)
    (a N : ℕ) :
      |(((Finset.Ico a (a + N)).filter p).card : ℝ) -
          (N:ℝ) * (d.count p : ℝ) / d| ≤ (d.count p : ℝ) := by
  classical
  obtain ⟨t, ht, he⟩ := periodic_Ico_decompose hd p hp a N
  have natdecomp : N = (N/d)*d + N%d := by
    simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div N d).symm
  have castdecomp : (N:ℝ) = (N/d:ℕ) * (d:ℕ) + (N%d:ℕ) := by
    exact_mod_cast natdecomp
  have hformula : (((Finset.Ico a (a+N)).filter p).card:ℝ) =
        (N/d:ℕ) * (d.count p:ℕ) + (t:ℕ) := by exact_mod_cast he
  rw [hformula, castdecomp]
  push_cast
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hlt : ((↑(N%d):ℝ)) < (d:ℝ) := by
    exact_mod_cast (Nat.mod_lt N hd)
  have hrd : ((↑(N%d):ℝ)) / d ≤ 1 := by
    apply (div_le_iff₀ (by exact_mod_cast hd : (0:ℝ)<d)).2
    linarith
  have hrd0 : 0 ≤ ((↑(N%d):ℝ)) / d := by
    exact div_nonneg (by positivity) (by positivity)
  have ht' : (t:ℝ) ≤ (d.count p:ℝ) := by exact_mod_cast ht
  have ht0 : 0 ≤ (t:ℝ) := by positivity
  have cd0 : 0 ≤ (d.count p:ℝ) := by positivity
  have alg :
      (((N / d : ℕ) : ℝ) * (d.count p:ℝ) + (t:ℝ)) -
        ((((N / d : ℕ):ℝ) * d + (↑(N%d):ℝ)) * (d.count p:ℝ) / d)
       = (t:ℝ) - (((↑(N%d):ℝ)) / d) * (d.count p:ℝ) := by
        field_simp
        ring
  rw [alg]
  rw [abs_le]
  constructor <;> nlinarith

/-- Divisibility for an integral polynomial is periodic with period the
modulus.  This keeps later residue estimates completely free of endpoints. -/
lemma periodic_dvd_poly (d : ℕ) :
    Function.Periodic (fun n : ℕ => d ∣ n * (n+2)) d := by
  -- `a | b` is unchanged after adding a multiple of `a` to each occurrence
  intro n
  have h : (n+d) * (n+d+2) = n*(n+2) + d * (2*n + d + 2) := by ring
  change (d ∣ (n+d)*(n+d+2)) = (d ∣ n*(n+2))
  rw [h]
  have hm : d ∣ d*(2*n+d+2) := dvd_mul_right d _
  exact propext (Nat.dvd_add_iff_left (m:=n*(n+2)) hm).symm
  
/-- Write the residue-box error for the actual twin polynomial.  The box is
`range d`; no estimate for its size (or factorisation) is needed here. -/
def polyResidues (d : ℕ) : ℕ := d.count (fun n : ℕ => d ∣ n*(n+2))

lemma block_multiples_abs_error {k d : ℕ} (hd : 0 < d) :
      |(((block k).filter (fun n : ℕ => d ∣ poly n)).card : ℝ) -
          ((2^k:ℕ):ℝ) * (polyResidues d : ℝ) / d|
        ≤ (polyResidues d : ℝ) := by
  classical
  -- our convention for the dyadic interval
  have hend : 2^(k+1) = (2^k:ℕ) + 2^k := by
    rw [pow_succ]
    omega
  unfold block
  -- switch to the version of the polynomial used by the periodic lemma
  have H := periodic_Ico_abs_error hd (fun n : ℕ => d ∣ n*(n+2))
      (periodic_dvd_poly d) (2^k) (2^k)
  simpa [polyResidues, poly, hend] using H

lemma polyResidues_le (d : ℕ) : polyResidues d ≤ d := by
  classical
  unfold polyResidues
  exact Nat.count_le _

/-- There are at least the two obvious roots, modulo an odd prime.  The
statement is an inequality rather than an equality, which is all the
Selberg denominator needs. -/
lemma two_le_polyResidues_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 ≤ polyResidues p := by
  classical
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rw [polyResidues, Nat.count_eq_card_filter_range]
  let S : Finset ℕ := {0, p-2}
  have hne : (p-2) ≠ 0 := by omega
  have hScard : S.card = 2 := by
    have h0ne : (0:ℕ) ≠ p-2 := Ne.symm hne
    simp [S, h0ne]
  have sub : S ⊆ (Finset.range p).filter (fun n : ℕ => p ∣ n*(n+2)) := by
    intro n hn
    have hor : n = 0 ∨ n = p-2 := by simpa [S] using hn
    rcases hor with rfl | rfl
    · simp [hp.pos]
    · have hlt : p-2 < p := by omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, ?_⟩
      have he : p-2+2 = p := by omega
      rw [he]
      exact dvd_mul_left _ _
  have L := Finset.card_le_card sub
  simpa [hScard] using (show S.card ≤ ((Finset.range p).filter (fun n : ℕ => p ∣ n*(n+2))).card from L)

/-- But not all residues are roots modulo a prime. This supplies the strict
`nu < 1` required by `BoundingSieve`. -/
lemma polyResidues_lt_prime {p : ℕ} (hp : p.Prime) :
    polyResidues p < p := by
  classical
  have hsmall : p = 2 ∨ p = 3 ∨ 5 ≤ p := by
    have h2 : 2 ≤ p := hp.two_le
    have h4 : p ≠ 4 := by intro h4; norm_num [h4] at hp
    omega
  rcases hsmall with rfl | rfl | hp5
  · decide
  · decide
  rw [polyResidues, Nat.count_eq_card_filter_range]
  let T : Finset ℕ := (Finset.range p).filter (fun n : ℕ => p ∣ n*(n+2))
  have sub : T ⊆ Finset.range p := Finset.filter_subset _ _
  have oneMem : 1 ∈ Finset.range p := Finset.mem_range.mpr (by omega)
  have oneNot : 1 ∉ T := by
    intro h
    have hh := (Finset.mem_filter.mp h).2
    norm_num at hh
    have : ¬ p ∣ 3 := by
      intro hdiv
      have hle : p ≤ 3 := Nat.le_of_dvd (by decide) hdiv
      omega
    exact this hh
  have proper : T ⊂ Finset.range p :=
    (Finset.ssubset_iff_subset_ne).2 ⟨sub, by
      intro eqn
      have : 1 ∈ T := eqn ▸ oneMem
      exact oneNot this⟩
  have L := Finset.card_lt_card proper
  simpa [T] using L


/-- The local-density arithmetic function for the twin polynomial.  Only
its values on square-free numbers enter the sieve; defining it by
`prodPrimeFactors` makes multiplicativity available without any coercion
bookkeeping. -/
noncomputable def twinNu : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p : ℕ => (polyResidues p : ℝ) / p)

lemma twinNu_mult : twinNu.IsMultiplicative := by
  unfold twinNu
  exact ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

lemma twinNu_prime {p : ℕ} (hp : p.Prime) :
    twinNu p = (polyResidues p : ℝ) / p := by
  classical
  unfold twinNu
  rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero]
  have PF : p.primeFactors = {p} := by
    simp [Nat.primeFactors, Nat.primeFactorsList_prime hp]
  rw [PF]
  simp

lemma twinNu_pos_prime {p : ℕ} (hp : p.Prime) : 0 < twinNu p := by
  rw [twinNu_prime hp]
  have one : 0 < polyResidues p := by
    by_cases h : p = 2
    · subst p
      decide
    · exact lt_of_lt_of_le (by decide : 0 < 2) (two_le_polyResidues_prime hp h)
  exact div_pos (by exact_mod_cast one) (by exact_mod_cast hp.pos)

lemma twinNu_lt_one_prime {p : ℕ} (hp : p.Prime) : twinNu p < 1 := by
  rw [twinNu_prime hp]
  apply (div_lt_iff₀ (by exact_mod_cast hp.pos : (0:ℝ)<p)).2
  norm_num
  exact_mod_cast (polyResidues_lt_prime hp)

/-- The primorial really is square-free; this small packaging fact is needed
to form the `BoundingSieve` record. -/
lemma primorial_squarefree' (z : ℕ) : Squarefree (primorial z) := by
  classical
  unfold primorial
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hne
    have pp : p.Prime := (Finset.mem_filter.mp hp).2
    have pq : q.Prime := (Finset.mem_filter.mp hq).2
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes pp pq).2 hne)
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.prime.squarefree


/-- The actual `BoundingSieve` datum.  No estimates are hypotheses of this
record: it is the plain, finitely supported weight-one problem, with the exact
local densities of the twin polynomial at primes. -/
noncomputable def twinSieve (k : ℕ) : BoundingSieve where
  support := valueBlock k
  prodPrimes := primorial (cutoff k - 1)
  prodPrimes_squarefree := primorial_squarefree' _
  weights := fun _ => 1
  weights_nonneg := by intro; exact zero_le_one
  totalMass := (2^k : ℕ)
  nu := twinNu
  nu_mult := twinNu_mult
  nu_pos_of_prime := by
    intro p hp hdiv
    exact twinNu_pos_prime hp
  nu_lt_one_of_prime := by
    intro p hp hdiv
    exact twinNu_lt_one_prime hp

lemma twinSieve_siftedSum (k : ℕ) :
    (twinSieve k).siftedSum = (coprimeValueCount k : ℝ) := by
  classical
  change (∑ d ∈ valueBlock k,
        if Nat.Coprime (primorial (cutoff k - 1)) d then (1:ℝ) else 0) =
      (((valueBlock k).filter
        (fun m : ℕ => Nat.Coprime (primorial (cutoff k - 1)) m)).card:ℕ)
  -- The elementary identity `sum_boole`; we write it via the filter to avoid
  -- any convention about indicators.
  rw [← Finset.sum_filter]
  push_cast
  simp


lemma filter_valueBlock_dvd_card (k d : ℕ) :
    ((valueBlock k).filter (fun m : ℕ => d ∣ m)).card =
      ((block k).filter (fun n : ℕ => d ∣ poly n)).card := by
  classical
  unfold valueBlock
  rw [Finset.filter_map, Finset.card_map]
  rfl

lemma twinSieve_multSum_abs_error (k : ℕ) {d : ℕ} (hd : 0 < d) :
    |(twinSieve k).multSum d -
          ((2^k:ℕ):ℝ) * (polyResidues d : ℝ) / d|
       ≤ (polyResidues d : ℝ) := by
  classical
  have he := block_multiples_abs_error (k:=k) hd
  have cnt := filter_valueBlock_dvd_card k d
  have sumid : (twinSieve k).multSum d =
          (((valueBlock k).filter (fun m : ℕ => d ∣ m)).card : ℕ) := by
    change (∑ n ∈ valueBlock k, if d ∣ n then (1:ℝ) else 0) = _
    rw [← Finset.sum_filter]
    simp
  rw [sumid, cnt]
  exact he


/-- Separation of the combinatorial error from the local CRT identity.  On a
square-free `d` the needed hypothesis is exactly multiplicativity of the
root count; this lemma records that there is no other endpoint term to pay. -/
lemma twinSieve_rem_of_local (k : ℕ) {d : ℕ} (hd : 0 < d)
    (hlocal : twinNu d = (polyResidues d : ℝ) / d) :
    |(twinSieve k).rem d| ≤ (polyResidues d : ℝ) := by
  classical
  have H := twinSieve_multSum_abs_error k hd
  change |(twinSieve k).multSum d -
      (twinSieve k).nu d * (twinSieve k).totalMass| ≤ _
  change |(twinSieve k).multSum d - twinNu d * ( (2^k:ℕ) : ℝ)| ≤ _
  rw [hlocal]
  convert H using 1 <;> ring

end BrunSupport

-- END INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/SelbergStart.lean

-- BEGIN INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/LocalCRT.lean

/-! Multiplicativity of the exact root count for `n(n+2)`.  The sieve
uses the root count on square-free divisors, not just on primes.  It is
convenient to make the Chinese remainder step a literal equivalence of
finite types; this avoids any asymptotic/rounding assertion. -/
set_option maxRecDepth 3000

namespace BrunSupport
open scoped BigOperators
open Finset

/-- Roots in one residue ring. -/
def twinRoots (d : ℕ) := {x : ZMod d // x * (x + 2) = 0}

noncomputable section


/-- Residues in `[0,d)` satisfying the divisibility condition are roots in
`ZMod d`.  We state this for `d>0` so that `val` is the inverse to casting. -/
noncomputable def residueEquivRoots (d : ℕ) (hd : 0 < d) :
    {k : ℕ // k < d ∧ d ∣ k * (k+2)} ≃ twinRoots d := by
  classical
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  -- record the casting calculation in both directions
  have cast_poly (k : ℕ) :
      ((k * (k+2) : ℕ) : ZMod d) =
        (k : ZMod d) * ((k : ZMod d) + 2) := by
    push_cast
    rfl
  refine
    { toFun := fun k => ⟨(k.1 : ZMod d), ?_⟩
      invFun := fun x => ⟨x.1.val, ZMod.val_lt x.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hzero : ((k.1 * (k.1+2) : ℕ) : ZMod d) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 k.2.2
    simpa [cast_poly] using hzero
  · have hzero : ((x.1.val : ZMod d) * ((x.1.val : ZMod d) + 2)) = 0 := by
      simpa [ZMod.natCast_zmod_val] using x.2
    have hzero' : ((x.1.val * (x.1.val+2) : ℕ) : ZMod d) = 0 := by
      simpa [cast_poly] using hzero
    exact (ZMod.natCast_eq_zero_iff _ _).1 hzero'
  · intro k
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt k.2.1
  · intro x
    apply Subtype.ext
    exact ZMod.natCast_zmod_val x.1

lemma polyResidues_eq_card_roots {d : ℕ} (hd : 0 < d) :
    polyResidues d = Nat.card (twinRoots d) := by
  classical
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  letI : Fintype (ZMod d) := by classical infer_instance
  letI : Fintype (twinRoots d) := by
    unfold twinRoots
    classical infer_instance
  letI : Fintype {k : ℕ // k < d ∧ d ∣ k*(k+2)} :=
    Nat.CountSet.fintype (fun k : ℕ => d ∣ k*(k+2)) d
  -- `Nat.count` counts the subtype of representatives below `d`.
  unfold polyResidues
  rw [Nat.count_eq_card_fintype]
  -- change both sides to `Nat.card`; this avoids committing to a global
  -- instance at modulus zero.
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (residueEquivRoots d hd)

/-- The polynomial condition is transported componentwise by any ring map.
The version for the CRT map gives a convenient equivalence of root types. -/
noncomputable def rootsCRT (a b : ℕ) (h : a.Coprime b) :
    twinRoots (a*b) ≃ twinRoots a × twinRoots b := by
  classical
  let e := ZMod.chineseRemainder h
  have e2 : e (2 : ZMod (a*b)) = (2 : ZMod a × ZMod b) := map_ofNat e 2
  have emap (x : ZMod (a*b)) :
      e (x * (x + 2)) =
        ( (e x).1 * ((e x).1 + 2),
          (e x).2 * ((e x).2 + 2) ) := by
    change _ = (_, _)
    simp [map_mul, map_add, e2]
    ext <;> rfl
  refine
    { toFun := fun x =>
        ⟨⟨(e x.1).1, ?_⟩, ⟨(e x.1).2, ?_⟩⟩
      invFun := fun y => ⟨e.symm (y.1.1,y.2.1), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hz := congrArg (fun u : ZMod a × ZMod b => u.1)
        (show e (x.1 * (x.1 + 2)) = (0 : ZMod a × ZMod b) by rw [x.2]; simp)
    simpa [emap] using hz
  · have hz := congrArg (fun u : ZMod a × ZMod b => u.2)
        (show e (x.1 * (x.1 + 2)) = (0 : ZMod a × ZMod b) by rw [x.2]; simp)
    simpa [emap] using hz
  · -- equality in the product is equality of the two component equations
    have hz :
        ( ( (y.1.1 : ZMod a) * (y.1.1 + 2),
            (y.2.1 : ZMod b) * (y.2.1 + 2) ) ) = (0 : ZMod a × ZMod b) := by
      ext <;> simp [y.1.2, y.2.2]
    apply e.injective
    -- applying the equivalence changes polynomial evaluation componentwise
    simpa [emap] using hz
  · intro x
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  · intro y
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.apply_symm_apply (y.1.1,y.2.1))
    · apply Subtype.ext
      exact congrArg Prod.snd (e.apply_symm_apply (y.1.1,y.2.1))

lemma polyResidues_mul_of_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a.Coprime b) :
    polyResidues (a*b) = polyResidues a * polyResidues b := by
  classical
  letI : NeZero a := ⟨Nat.ne_of_gt ha⟩
  letI : NeZero b := ⟨Nat.ne_of_gt hb⟩
  letI : NeZero (a*b) := ⟨Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  rw [polyResidues_eq_card_roots (Nat.mul_pos ha hb),
      polyResidues_eq_card_roots ha, polyResidues_eq_card_roots hb]
  exact (Nat.card_congr (rootsCRT a b h)).trans (Nat.card_prod _ _)

@[simp] lemma polyResidues_one : polyResidues 1 = 1 := by
  classical
  -- the single residue is a root
  norm_num [polyResidues, Nat.count_eq_card_filter_range]

/-- Multiplying distinct primes multiplies the number of roots. -/
lemma polyResidues_prod_primes (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    polyResidues (∏ p ∈ s, p) = ∏ p ∈ s, polyResidues p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyResidues_one]
  | @insert p s hpnot ih =>
      have pp : Nat.Prime p := hs p (by simp)
      have hrest : ∀ q ∈ s, Nat.Prime q := by
        intro q hq; exact hs q (by simp [hq])
      have ih' := ih hrest
      have hc : p.Coprime (∏ q ∈ s, q) := by
        apply (Nat.coprime_prod_right_iff).2
        intro q hq
        exact (Nat.coprime_primes pp (hrest q hq)).2 (by
          intro e; subst q; exact hpnot hq)
      have hp0 : 0 < p := pp.pos
      have hprod0 : 0 < ∏ q ∈ s, q := by
        exact Finset.prod_pos (fun q hq => (hrest q hq).pos)
      simpa [hpnot, ih'] using
        (polyResidues_mul_of_coprime hp0 hprod0 hc)

/-- On a square-free divisor the artificial multiplicative density `twinNu`
is exactly the true root density.  In particular the remainder estimate of
`twinSieve_rem_of_local` applies to all the lcms in a lambda-square sieve. -/
lemma twinNu_eq_polyResidues_div {d : ℕ} (hd : Squarefree d) :
    twinNu d = (polyResidues d : ℝ) / d := by
  classical
  have h0 : d ≠ 0 := hd.ne_zero
  unfold twinNu
  rw [ArithmeticFunction.prodPrimeFactors_apply h0]
  have HN : polyResidues d = ∏ p ∈ d.primeFactors, polyResidues p := by
    calc
      polyResidues d = polyResidues (∏ p ∈ d.primeFactors, p) :=
        congrArg polyResidues (Nat.prod_primeFactors_of_squarefree hd).symm
      _ = _ := polyResidues_prod_primes _
        (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have HD : (∏ p ∈ d.primeFactors, (polyResidues p : ℝ) / p) =
        ((∏ p ∈ d.primeFactors, polyResidues p : ℕ) : ℝ) /
          ((∏ p ∈ d.primeFactors, p : ℕ) : ℝ) := by
    -- distribute the fraction over the finite product
    simp_rw [div_eq_mul_inv]
    push_cast
    rw [Finset.prod_mul_distrib]
    simp
  rw [HD, ← HN, Nat.prod_primeFactors_of_squarefree hd]

lemma twinSieve_rem_bound (k : ℕ) {d : ℕ} (hd : 0 < d)
    (hsq : Squarefree d) :
    |(twinSieve k).rem d| ≤ (polyResidues d : ℝ) :=
  twinSieve_rem_of_local k hd (twinNu_eq_polyResidues_div hsq)

end
end BrunSupport

-- END INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/LocalCRT.lean

-- BEGIN INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/LambdaCrude.lean

/-! Two useful, very cheap estimates for the error side of the Selberg
argument.  They don't involve choosing the weights.  On square-free
divisors the remainder is the periodic root-box remainder (`LocalCRT`).
If lambda is supported below `L` and `|lambda_d| ≤ L`, the lambda-squared
error is polynomial (`L^8` suffices).  Consequently an exponentially small
level can be used in the main-term optimisation. -/
namespace BrunSupport
open Finset
open scoped BigOperators
open BoundingSieve

lemma twinSieve_err_bound (k : ℕ) (mu : ℕ → ℝ) :
    (twinSieve k).errSum mu ≤
       ∑ d ∈ (twinSieve k).prodPrimes.divisors,
          |mu d| * (d : ℝ) := by
  classical
  unfold BoundingSieve.errSum
  apply Finset.sum_le_sum
  intro d hd
  gcongr
  have hdP : d ∣ (twinSieve k).prodPrimes := (Nat.mem_divisors.mp hd).1
  have hd0 : 0 < d := Nat.pos_of_ne_zero
    (ne_zero_of_dvd_ne_zero (twinSieve k).prodPrimes_ne_zero hdP)
  calc
    |(twinSieve k).rem d| ≤ (polyResidues d : ℝ) :=
      twinSieve_rem_bound k hd0
        ((twinSieve k).squarefree_of_dvd_prodPrimes hdP)
    _ ≤ (d : ℝ) := by exact_mod_cast polyResidues_le d

/-- A finite-form bound for a lambda-square coefficient.  `L` here bounds
both the support and the absolute size of a lambda.  It is intentionally
wasteful (`L^6`); only polynomial growth is needed in the application. -/
lemma lambdaSquared_abs_le_pow (L d : ℕ) (w : ℕ → ℝ)
    (hsize : ∀ i, |w i| ≤ (L : ℝ)) :
    |BoundingSieve.lambdaSquared w d| ≤
       ((d.divisors.card : ℕ) : ℝ)^2 * (L:ℝ)^2 := by
  classical
  unfold BoundingSieve.lambdaSquared
  calc
    |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
        (if d = Nat.lcm d1 d2 then w d1 * w d2 else 0)|
        ≤ ∑ d1 ∈ d.divisors, |∑ d2 ∈ d.divisors,
            (if d = Nat.lcm d1 d2 then w d1 * w d2 else 0)| := by
              exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d1 ∈ d.divisors, ∑ _d2 ∈ d.divisors, (L:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        |∑ j ∈ d.divisors, (if d = Nat.lcm i j then w i * w j else 0)|
            ≤ ∑ j ∈ d.divisors,
                |(if d = Nat.lcm i j then w i * w j else 0)| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ d.divisors, (L:ℝ)^2 := by
              apply Finset.sum_le_sum
              intro j hj
              split_ifs
              · rw [abs_mul, pow_two]
                exact mul_le_mul (hsize i) (hsize j)
                  (abs_nonneg _) (by positivity)
              · have hz : (0:ℝ) ≤ (L:ℝ)^2 := sq_nonneg _
                simpa using hz
    _ = ((d.divisors.card : ℕ) : ℝ)^2 * (L:ℝ)^2 := by
      simp
      ring

/-- Outside `L^2` the coefficient vanishes if the lambda support is `≤L`.
This is often a simpler way to truncate the remainder sum than enumerating
lcm divisors. -/
lemma lambdaSquared_eq_zero_of_lt (L d : ℕ) (w : ℕ → ℝ)
    (hsupp : ∀ i, L < i → w i = 0)
    (hd : L*L < d) :
    BoundingSieve.lambdaSquared w d = 0 := by
  classical
  unfold BoundingSieve.lambdaSquared
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases h : d = Nat.lcm i j
  · -- at least one of the two indices exceeds the support
    by_cases hiL : i ≤ L
    · by_cases hjL : j ≤ L
      · have hdpos : 0 < d := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hi).2
        have hipos : 0 < i := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hi).1 hdpos
        have hjpos : 0 < j := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hj).1 hdpos
        have hl : Nat.lcm i j ≤ i*j := Nat.lcm_le_mul hipos hjpos
        have hbad : d ≤ L*L := by
          rw [h]
          exact le_trans hl (Nat.mul_le_mul hiL hjL)
        exact False.elim ((Nat.not_le.mpr hd) hbad)
      · simp [h, hsupp j (Nat.lt_of_not_ge hjL)]
    · simp [h, hsupp i (Nat.lt_of_not_ge hiL)]
  · simp [h]


end BrunSupport

namespace BrunSupport
open Finset BoundingSieve
open scoped BigOperators
/-- Every odd prime in the sieve supplies at least the usual `2/p`
Selberg term.  Only the two obvious roots are needed. -/
lemma twin_selbergTerms_prime_lower (k p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hP : p ∣ (twinSieve k).prodPrimes) :
    (2:ℝ) / p ≤ (twinSieve k).selbergTerms p := by
  classical
  rw [BoundingSieve.selbergTerms_apply]
  have pf : p.primeFactors = {p} := by
    simp [Nat.primeFactors, Nat.primeFactorsList_prime hp]
  rw [pf]
  simp only [Finset.prod_singleton]
  have hnu : (twinSieve k).nu p = (polyResidues p : ℝ) / p := by
    change twinNu p = _
    exact twinNu_prime hp
  have ppos : (0:ℝ) < p := by exact_mod_cast hp.pos
  have roots : (2:ℝ) / p ≤ (twinSieve k).nu p := by
    rw [hnu]
    apply (div_le_div_iff_of_pos_right ppos).2
    exact_mod_cast (two_le_polyResidues_prime hp hp2)
  have nu0 : 0 ≤ (twinSieve k).nu p := le_trans (by positivity : (0:ℝ) ≤ 2 / (p:ℝ)) roots
  have nu1 : (twinSieve k).nu p < 1 :=
    (twinSieve k).nu_lt_one_of_prime p hp hP
  -- multiplying by `(1-ν)⁻¹` only enlarges a nonnegative `ν`.
  calc
    (2:ℝ) / p ≤ (twinSieve k).nu p := roots
    _ ≤ (twinSieve k).nu p * (1 - (twinSieve k).nu p)⁻¹ := by
      have hpos : 0 < 1 - (twinSieve k).nu p := sub_pos.mpr nu1
      have hinv : 1 ≤ (1 - (twinSieve k).nu p)⁻¹ := by
        apply (one_le_inv₀ hpos).2
        linarith
      simpa using (mul_le_mul_of_nonneg_left hinv nu0)
end BrunSupport

-- END INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/LambdaCrude.lean

-- BEGIN INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/SelbergWeights.lean

/-! A finite choice of Selberg weights. -/
namespace BrunSupport
noncomputable section
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators ArithmeticFunction.Moebius

/-- Divisors below a (natural) level. -/
def levelDivs (s : BoundingSieve) (R : ℕ) : Finset ℕ :=
  s.prodPrimes.divisors.filter (fun d => d ≤ R)

/-- The Selberg denominator at level `R`. -/
def sgDen (s : BoundingSieve) (R : ℕ) : ℝ :=
  ∑ d ∈ levelDivs s R, s.selbergTerms d

/-- The standard minimizing real Selberg weights, written only with finite sums.
Outside the squarefree product their value is irrelevant and set to zero. -/
def sgWeight (s : BoundingSieve) (R : ℕ) (d : ℕ) : ℝ :=
  if hd : d ∣ s.prodPrimes then
    ((μ d : ℝ) / (s.nu d * sgDen s R)) *
      (∑ l ∈ levelDivs s R, if d ∣ l then s.selbergTerms l else 0)
  else 0

lemma one_mem_levelDivs (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    1 ∈ levelDivs s R := by
  classical
  simp [levelDivs, hR, BoundingSieve.prodPrimes_ne_zero]

lemma levelDivs_subset (s : BoundingSieve) (R : ℕ) :
    levelDivs s R ⊆ s.prodPrimes.divisors := by
  classical exact Finset.filter_subset _ _

lemma mem_levelDivs_dvd (s : BoundingSieve) {R l : ℕ}
    (hl : l ∈ levelDivs s R) : l ∣ s.prodPrimes :=
  (Nat.mem_divisors.mp ((levelDivs_subset s R) hl)).1

lemma mem_levelDivs_le (s : BoundingSieve) {R l : ℕ}
    (hl : l ∈ levelDivs s R) : l ≤ R :=
  (Finset.mem_filter.mp hl).2

lemma levelDivs_down {s : BoundingSieve} {R a b : ℕ}
    (hb : b ∈ levelDivs s R) (ha : a ∣ b) : a ∈ levelDivs s R := by
  classical
  have hbP : b ∣ s.prodPrimes := mem_levelDivs_dvd s hb
  have hb0 : 0 < b := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hbP)
  have haP : a ∣ s.prodPrimes := dvd_trans ha hbP
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hb0
  have ale : a ≤ R := le_trans (Nat.le_of_dvd hb0 ha) (mem_levelDivs_le s hb)
  exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨haP, s.prodPrimes_ne_zero⟩, ale⟩

lemma sgDen_pos (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    0 < sgDen s R := by
  classical
  unfold sgDen
  have hmem : 1 ∈ levelDivs s R := one_mem_levelDivs s hR
  have hterm : 0 < s.selbergTerms 1 :=
    BoundingSieve.selbergTerms_pos (s:=s) (one_dvd _)
  have hnon : ∀ l ∈ levelDivs s R, 0 ≤ s.selbergTerms l := by
    intro l hl
    exact le_of_lt (BoundingSieve.selbergTerms_pos (s:=s) (mem_levelDivs_dvd s hl))
  have := Finset.single_le_sum (s:=levelDivs s R) (f:=fun l => s.selbergTerms l)
    hnon hmem
  exact lt_of_lt_of_le hterm this

@[simp] lemma sgWeight_one (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    sgWeight s R 1 = 1 := by
  classical
  unfold sgWeight
  simp [sgDen_pos s hR |>.ne']
  rw [s.nu_mult.map_one]
  have hne : sgDen s R ≠ 0 := (sgDen_pos s hR).ne'
  unfold sgDen
  have hn : (∑ x ∈ levelDivs s R, s.selbergTerms x) ≠ 0 := by simpa [sgDen] using hne
  simp [hn]

end
end BrunSupport

namespace BrunSupport
noncomputable section
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators ArithmeticFunction.Moebius

/-- Sum of the integer Moebius over all divisors. -/
lemma sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, μ d) = if n = 1 then 1 else 0 := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  have H := congrArg (fun F : ArithmeticFunction ℤ => F n)
      (ArithmeticFunction.moebius_mul_coe_zeta)
  -- convolution with zeta is precisely a divisor sum
  have H' : ((μ : ArithmeticFunction ℤ) * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n =
        (1 : ArithmeticFunction ℤ) n := H
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at H'
  exact H' 

lemma sum_moebius_multiples_squarefree {l t : ℕ}
    (ht : Squarefree t) (hlt : l ∣ t) :
    (∑ d ∈ t.divisors, if l ∣ d then (μ d : ℤ) else 0) =
      if t = l then (μ l : ℤ) else 0 := by
  classical
  have t0 : t ≠ 0 := ht.ne_zero
  have l0 : l ≠ 0 := ne_zero_of_dvd_ne_zero t0 hlt
  let u := t / l
  have tu : l * u = t := by simp [u, Nat.mul_div_cancel' hlt]
  have hu0 : u ≠ 0 := by
    intro h; have : l * u = 0 := by simp [h]
    exact t0 (tu ▸ this)
  have hsf : Squarefree (l * u) := tu ▸ ht
  have hcop : l.Coprime u := Nat.coprime_of_squarefree_mul hsf
  -- parameterise the divisors which are multiples of l
  have bijsum :
      (∑ x ∈ u.divisors, (μ (l*x) : ℤ)) =
        ∑ d ∈ t.divisors.filter (fun d => l ∣ d), (μ d : ℤ) := by
    classical
    -- use `x ↦ l*x`
    apply Finset.sum_bij (fun x _ => l*x)
    · intro x hx
      have hx' : x ∣ u := (Nat.mem_divisors.mp hx).1
      have hd : l*x ∣ t := by
        rw [← tu]
        exact Nat.mul_dvd_mul_left l hx'
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, t0⟩, by exact dvd_mul_right l x⟩
    · intro a ha b hb eqn
      exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero l0) eqn)
    · intro d hd
      have hd' := Finset.mem_filter.mp hd
      rcases hd'.2 with ⟨x, rfl⟩
      refine ⟨x, ?_, ?_⟩
      · have hdiv : l*x ∣ t := (Nat.mem_divisors.mp hd'.1).1
        have hx : x ∣ u := by
          -- cancel l in l*x ∣ l*u
          rw [← tu] at hdiv
          exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero l0) hdiv
        exact Nat.mem_divisors.mpr ⟨hx, hu0⟩
      · rfl
    · intro a ha
      rfl
  calc
    (∑ d ∈ t.divisors, if l ∣ d then (μ d : ℤ) else 0)
        = ∑ d ∈ t.divisors.filter (fun d => l ∣ d), (μ d : ℤ) := by
            rw [← Finset.sum_filter]
    _ = ∑ x ∈ u.divisors, (μ (l*x) : ℤ) := by rw [bijsum]
    _ = (μ l : ℤ) * ∑ x ∈ u.divisors, (μ x : ℤ) := by
      apply Eq.symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hxdiv : x ∣ u := (Nat.mem_divisors.mp hx).1
      have hcx : l.Coprime x := hcop.coprime_dvd_right hxdiv
      exact (ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcx).symm
    _ = if t = l then (μ l : ℤ) else 0 := by
      rw [sum_moebius_divisors]
      by_cases h : t = l
      · have hu : u = 1 := by
          dsimp [u]
          rw [h]
          exact Nat.div_self (Nat.pos_of_ne_zero l0)
        simp [hu, h]
      · have hu : u ≠ 1 := by
          intro hu1
          apply h
          simpa [hu1] using tu.symm
        simp [hu, h]


/-- Transform of the weights which occurs in the diagonal quadratic form. -/
lemma sg_transform (s : BoundingSieve) {R l : ℕ} (hR : 1 ≤ R)
    (hlP : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then s.nu d * sgWeight s R d else 0) =
      if hl : l ∈ levelDivs s R then
        (μ l : ℝ) * s.selbergTerms l / sgDen s R
      else 0 := by
  classical
  have den0 : sgDen s R ≠ 0 := (sgDen_pos s hR).ne'
  -- substitute the definition of a weight.  Only divisors of the product occur.
  have expand (d : ℕ) (hd : d ∈ s.prodPrimes.divisors) :
      s.nu d * sgWeight s R d =
        (1 / sgDen s R) * (μ d : ℝ) *
          (∑ t ∈ levelDivs s R, if d ∣ t then s.selbergTerms t else 0) := by
    have hdP : d ∣ s.prodPrimes := (Nat.mem_divisors.mp hd).1
    have nup : 0 < s.nu d := BoundingSieve.nu_pos_of_dvd_prodPrimes (s:=s) hdP
    unfold sgWeight
    rw [dif_pos hdP]
    field_simp
  calc
    (∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then s.nu d * sgWeight s R d else 0)
      = (1 / sgDen s R) *
          (∑ d ∈ s.prodPrimes.divisors, ∑ t ∈ levelDivs s R,
             if l ∣ d ∧ d ∣ t then (μ d : ℝ) * s.selbergTerms t else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mul_sum]
        by_cases hld : l ∣ d
        · rw [if_pos hld, expand d hd]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          by_cases hdt : d ∣ t <;> simp [hdt, hld] <;> ring
        · simp [hld]
    _ = (1 / sgDen s R) *
          (∑ t ∈ levelDivs s R,
            s.selbergTerms t *
              (∑ d ∈ t.divisors, if l ∣ d then (μ d : ℝ) else 0)) := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t ht
        have htP : t ∣ s.prodPrimes := mem_levelDivs_dvd s ht
        -- among product-divisors, the condition d|t is the divisor set of t
        calc
          (∑ d ∈ s.prodPrimes.divisors,
              if l ∣ d ∧ d ∣ t then (μ d : ℝ) * s.selbergTerms t else 0)
            = ∑ d ∈ t.divisors,
                 if l ∣ d then (μ d : ℝ) * s.selbergTerms t else 0 := by
                rw [← Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero htP]
                simp_rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro d hd
                by_cases hdt : d ∣ t <;> by_cases hld : l ∣ d <;> simp [hdt, hld]
          _ = s.selbergTerms t *
                (∑ d ∈ t.divisors, if l ∣ d then (μ d : ℝ) else 0) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro d hd
                by_cases h : l ∣ d <;> simp [h] <;> ring
    _ = (if hl : l ∈ levelDivs s R then
             (μ l : ℝ) * s.selbergTerms l / sgDen s R else 0) := by
        by_cases hl : l ∈ levelDivs s R
        · simp [hl]
          -- the Möbius inner sum kills every term except t=l
          have kill (t : ℕ) (ht : t ∈ levelDivs s R) :
              (∑ d ∈ t.divisors, if l ∣ d then (μ d : ℝ) else 0) =
                 if t = l then (μ l : ℝ) else 0 := by
            by_cases hx : l ∣ t
            · have hsft : Squarefree t := s.squarefree_of_dvd_prodPrimes (mem_levelDivs_dvd s ht)
              exact_mod_cast (sum_moebius_multiples_squarefree hsft hx)
            · have zero : ∀ d ∈ t.divisors, ¬ l ∣ d := by
                intro d hd hdiv
                exact hx (dvd_trans hdiv (Nat.mem_divisors.mp hd).1)
              have tn : t ≠ l := by intro e; apply hx; simp [e]
              rw [if_neg tn]
              apply Finset.sum_eq_zero
              intro d hd
              simp [zero d hd]
          -- evaluate the one surviving finite summand
          have conv : (∑ t ∈ levelDivs s R,
              s.selbergTerms t * (∑ d ∈ t.divisors, if l ∣ d then (μ d : ℝ) else 0)) =
              ∑ t ∈ levelDivs s R, s.selbergTerms t * (if t = l then (μ l : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [kill t ht]
          rw [conv]
          rw [Finset.sum_eq_single l]
          · simp [hl, div_eq_mul_inv]
            ring
          · intro b hb hne
            simp [hne]
          · intro hn
            exact (hn hl).elim
        · rw [dif_neg hl]
          -- if l is above the level it divides no element of the level
          have nod (t : ℕ) (ht : t ∈ levelDivs s R) : ¬ l ∣ t := by
            intro h
            exact hl (levelDivs_down ht h)
          have z (t : ℕ) (ht : t ∈ levelDivs s R) :
              (∑ d ∈ t.divisors, if l ∣ d then (μ d : ℝ) else 0) = 0 := by
            have nd : ∀ d ∈ t.divisors, ¬ l ∣ d := by
              intro d hd hdiv; exact nod t ht (dvd_trans hdiv (Nat.mem_divisors.mp hd).1)
            apply Finset.sum_eq_zero
            intro d hd
            simp [nd d hd]
          have out : ∑ t ∈ levelDivs s R,
              s.selbergTerms t * (∑ d ∈ t.divisors, if l ∣ d then (μ d : ℝ) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro t ht
            rw [z t ht]
            ring
          rw [out]
          norm_num


lemma moebius_sq_one {n : ℕ} (h : Squarefree n) : (μ n : ℝ)^2 = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree h]
  push_cast
  -- (-1) raised to any power has square one
  have : ((-1 : ℝ) ^ ArithmeticFunction.cardFactors n) ^ 2 = 1 := by
    rw [pow_two, ← mul_pow]
    norm_num
  simpa using this

lemma sg_main (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    s.mainSum (BoundingSieve.lambdaSquared (sgWeight s R)) = (sgDen s R)⁻¹ := by
  classical
  have den0 : sgDen s R ≠ 0 := (sgDen_pos s hR).ne'
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  -- evaluate each divisor by the transform
  calc
    (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * sgWeight s R d else 0)^2)
      = ∑ l ∈ levelDivs s R,
          (s.selbergTerms l)⁻¹ *
            (((μ l : ℝ) * s.selbergTerms l / sgDen s R)^2) := by
          unfold levelDivs
          -- the terms outside the filtered set are zero
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro l hl
          have hlP : l ∣ s.prodPrimes := (Nat.mem_divisors.mp hl).1
          rw [sg_transform s hR hlP]
          by_cases hlev : l ∈ (s.prodPrimes.divisors.filter (fun d => d ≤ R))
          · have le : l ≤ R := (Finset.mem_filter.mp hlev).2
            simp [hlev, le, levelDivs]
          · have hn : ¬ l ≤ R := by
              intro le; exact hlev (Finset.mem_filter.mpr ⟨hl, le⟩)
            simp [hlev, hn, levelDivs]
    _ = (sgDen s R)⁻¹ := by
      have each (l : ℕ) (hl : l ∈ levelDivs s R) :
          (s.selbergTerms l)⁻¹ * (((μ l : ℝ) * s.selbergTerms l / sgDen s R)^2) =
             s.selbergTerms l / (sgDen s R)^2 := by
        have gp : 0 < s.selbergTerms l :=
          BoundingSieve.selbergTerms_pos (s:=s) (mem_levelDivs_dvd s hl)
        have hsfree : Squarefree l := s.squarefree_of_dvd_prodPrimes (mem_levelDivs_dvd s hl)
        have mus : (μ l : ℝ)^2 = 1 := moebius_sq_one hsfree
        field_simp
        nlinarith
      calc
        _ = ∑ l ∈ levelDivs s R, s.selbergTerms l / (sgDen s R)^2 := by
            apply Finset.sum_congr rfl
            intro l hl; exact each l hl
        _ = _ := by
          unfold sgDen
          rw [← Finset.sum_div]
          field_simp

/-- Above the level the optimal weight vanishes. -/
lemma sgWeight_zero {s : BoundingSieve} {R d : ℕ} (hd : R < d) :
    sgWeight s R d = 0 := by
  classical
  unfold sgWeight
  split_ifs with hp
  · have nod (l : ℕ) (hl : l ∈ levelDivs s R) : ¬ d ∣ l := by
      intro h; have le := Nat.le_of_dvd
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero
          (mem_levelDivs_dvd s hl))) h
      exact (Nat.not_le_of_gt hd) (le_trans le (mem_levelDivs_le s hl))
    have sum0 : (∑ l ∈ levelDivs s R, if d ∣ l then s.selbergTerms l else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      simp [nod l hl]
    rw [sum0]
    ring
  · rfl


lemma sg_sifted (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    s.siftedSum ≤ s.totalMass / sgDen s R +
      s.errSum (BoundingSieve.lambdaSquared (sgWeight s R)) := by
  have h := BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
      (s:=s) (BoundingSieve.lambdaSquared (sgWeight s R))
      (BoundingSieve.upperMoebius_lambdaSquared _ (sgWeight_one s hR))
  rw [sg_main s hR] at h
  simpa [div_eq_mul_inv] using h

lemma polyResidues_pos {d : ℕ} (hd : 0 < d) : 0 < polyResidues d := by
  classical
  unfold polyResidues
  rw [Nat.count_eq_card_filter_range]
  have mem : 0 ∈ (Finset.range d).filter (fun n : ℕ => d ∣ n * (n+2)) := by
    simp [hd]
  exact Finset.card_pos.mpr ⟨0, mem⟩

lemma twinNu_lower {k d : ℕ} (hd : d ∣ (twinSieve k).prodPrimes) :
    (1:ℝ) / d ≤ (twinSieve k).nu d := by
  have hsfree : Squarefree d := (twinSieve k).squarefree_of_dvd_prodPrimes hd
  have posd : 0 < d := Nat.pos_of_ne_zero
      (ne_zero_of_dvd_ne_zero (twinSieve k).prodPrimes_ne_zero hd)
  change _ ≤ twinNu d
  rw [twinNu_eq_polyResidues_div hsfree]
  apply (div_le_div_iff_of_pos_right (by exact_mod_cast posd : (0:ℝ)<d)).2
  exact_mod_cast (polyResidues_pos posd)

lemma mob_abs_le (d : ℕ) : |(μ d : ℝ)| ≤ 1 := by
  rw [ArithmeticFunction.moebius]
  dsimp
  split_ifs
  · rw [Int.cast_pow]
    rw [abs_pow]
    norm_num
  · norm_num

end
end BrunSupport

-- END INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/SelbergWeights.lean

-- BEGIN INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/SelbergEstimate.lean
namespace BrunSupport
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators ArithmeticFunction.Moebius
noncomputable section

/-- The optimal Selberg lambda at level `R` has a very crude pointwise
bound.  This is useful since it leaves the whole remainder with no
logarithms at all. -/
lemma twin_sgWeight_abs_le (k R d : ℕ) (hR : 1 ≤ R) :
    |sgWeight (twinSieve k) R d| ≤ (R : ℝ) := by
  classical
  let s : BoundingSieve := twinSieve k
  change |sgWeight s R d| ≤ (R:ℝ)
  by_cases hhi : R < d
  · rw [sgWeight_zero hhi]
    simp [Nat.zero_le]
  have hdle : d ≤ R := Nat.le_of_not_gt hhi
  by_cases hdP : d ∣ s.prodPrimes
  · have dpos : 0 < d := Nat.pos_of_ne_zero
        (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP)
    have nupos : 0 < s.nu d := BoundingSieve.nu_pos_of_dvd_prodPrimes hdP
    have denpos : 0 < sgDen s R := sgDen_pos s hR
    let T : ℝ := ∑ l ∈ levelDivs s R,
                 if d ∣ l then s.selbergTerms l else 0
    have Tnon : 0 ≤ T := by
      dsimp [T]
      apply Finset.sum_nonneg
      intro l hl
      split_ifs
      · exact le_of_lt (BoundingSieve.selbergTerms_pos
          (s:=s) (mem_levelDivs_dvd s hl))
      · exact le_rfl
    have Tle : T ≤ sgDen s R := by
      dsimp [T, sgDen]
      apply Finset.sum_le_sum
      intro l hl
      by_cases h : d ∣ l
      · simp [h]
      · simp [h, le_of_lt (BoundingSieve.selbergTerms_pos
          (s:=s) (mem_levelDivs_dvd s hl))]
    have nulow : (1:ℝ) / d ≤ s.nu d := by
      change (1:ℝ)/d ≤ (twinSieve k).nu d
      exact twinNu_lower hdP
    unfold sgWeight
    rw [dif_pos hdP]
    change |((μ d : ℝ) / (s.nu d * sgDen s R)) * T| ≤ (R:ℝ)
    have mob : |(μ d : ℝ)| ≤ 1 := mob_abs_le d
    rw [abs_mul, abs_div]
    have nden : |s.nu d * sgDen s R| = s.nu d * sgDen s R :=
      abs_of_pos (mul_pos nupos denpos)
    have Tabs : |T| = T := abs_of_nonneg Tnon
    rw [nden, Tabs]
    have dd : (0:ℝ) < d := by exact_mod_cast dpos
    have dle : (d:ℝ) ≤ (R:ℝ) := by exact_mod_cast hdle
    -- each weight is at most `1/nu_d`, since its numerator is a
    -- part of the denominator.
    have step1 : |(μ d : ℝ)| / (s.nu d * sgDen s R) * T
          ≤ (1:ℝ) / s.nu d := by
      calc
        |(μ d : ℝ)| / (s.nu d * sgDen s R) * T
            ≤ (1:ℝ) / (s.nu d * sgDen s R) * (sgDen s R) := by
                apply mul_le_mul
                · exact div_le_div_of_nonneg_right mob (le_of_lt (mul_pos nupos denpos))
                · exact Tle
                · exact Tnon
                · exact div_nonneg (by norm_num) (le_of_lt (mul_pos nupos denpos))
        _ = (1:ℝ) / s.nu d := by
              field_simp
    calc
      |(μ d : ℝ)| / (s.nu d * sgDen s R) * T
          ≤ (1:ℝ) / s.nu d := step1
      _ ≤ (d:ℝ) := by
        apply (div_le_iff₀ nupos).2
        convert (div_le_iff₀ dd).1 nulow using 1 <;> ring
      _ ≤ (R:ℝ) := dle
  · unfold sgWeight
    rw [dif_neg hdP]
    simp

end
end BrunSupport

namespace BrunSupport
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators ArithmeticFunction.Moebius
noncomputable section

/-- A deliberately wasteful form of the Selberg remainder.  The exponent
is immaterial: the level used below is a very small power of the length of
an interval.  Notice that this estimate uses the *exact periodic* local
remainder, so it is independent of the left endpoint. -/
lemma twin_sg_err_crude (k R : ℕ) (hR : 1 ≤ R) :
    (twinSieve k).errSum
       (BoundingSieve.lambdaSquared (sgWeight (twinSieve k) R))
       ≤ (R : ℝ)^10 := by
  classical
  let s : BoundingSieve := twinSieve k
  let w : ℕ → ℝ := sgWeight (twinSieve k) R
  let M : ℕ := R*R
  have ws : ∀ i, |w i| ≤ (R:ℝ) := by
    intro i; dsimp [w]; exact twin_sgWeight_abs_le k R i hR
  have wz : ∀ i, R < i → w i = 0 := by
    intro i hi
    dsimp [w]
    exact sgWeight_zero hi
  have start :
      (twinSieve k).errSum (BoundingSieve.lambdaSquared w) ≤
        ∑ d ∈ (twinSieve k).prodPrimes.divisors,
          |BoundingSieve.lambdaSquared w d| * (d:ℝ) :=
    twinSieve_err_bound k _
  let U : Finset ℕ := (twinSieve k).prodPrimes.divisors.filter (fun d => d ≤ M)
  have trunc :
      (∑ d ∈ (twinSieve k).prodPrimes.divisors,
          |BoundingSieve.lambdaSquared w d| * (d:ℝ)) =
        ∑ d ∈ U, |BoundingSieve.lambdaSquared w d| * (d:ℝ) := by
    classical
    unfold U
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases he : d ≤ M
    · simp [he]
    · have z := lambdaSquared_eq_zero_of_lt R d w wz
          (show R*R < d from (Nat.lt_of_not_ge he : M < d))
      simp [he, z]
  have cardU : U.card ≤ M := by
    have sub : U ⊆ Finset.Icc 1 M := by
      intro d hd
      have hh := Finset.mem_filter.mp hd
      have dp : d ∣ (twinSieve k).prodPrimes := (Nat.mem_divisors.mp hh.1).1
      have d0 : 0 < d := Nat.pos_of_ne_zero
        (ne_zero_of_dvd_ne_zero (twinSieve k).prodPrimes_ne_zero dp)
      exact Finset.mem_Icc.mpr ⟨d0, hh.2⟩
    have c := Finset.card_le_card sub
    simpa using c
  have each (d : ℕ) (hd : d ∈ U) :
      |BoundingSieve.lambdaSquared w d| * (d:ℝ)
          ≤ (R:ℝ)^8 := by
    have leM : d ≤ M := (Finset.mem_filter.mp hd).2
    have dM : (d:ℝ) ≤ (R:ℝ)^2 := by
      have : (d:ℝ) ≤ (M:ℝ) := by exact_mod_cast leM
      simpa [M, pow_two] using this
    have cardd : (d.divisors.card : ℝ) ≤ (d:ℝ) := by
      exact_mod_cast (Nat.card_divisors_le_self d)
    have lam := lambdaSquared_abs_le_pow R d w ws
    calc
      |BoundingSieve.lambdaSquared w d| * (d:ℝ)
          ≤ ((d.divisors.card : ℕ):ℝ)^2 * (R:ℝ)^2 * (d:ℝ) := by
            exact mul_le_mul_of_nonneg_right lam (by positivity)
      _ ≤ (d:ℝ)^2 * (R:ℝ)^2 * (d:ℝ) := by
            gcongr
      _ ≤ ((R:ℝ)^2)^2 * (R:ℝ)^2 * ((R:ℝ)^2) := by
            gcongr <;> positivity
      _ = (R:ℝ)^8 := by ring
  calc
    (twinSieve k).errSum
       (BoundingSieve.lambdaSquared (sgWeight (twinSieve k) R))
        ≤ ∑ d ∈ (twinSieve k).prodPrimes.divisors,
          |BoundingSieve.lambdaSquared w d| * (d:ℝ) := by
            simpa [w] using start
    _ = ∑ d ∈ U, |BoundingSieve.lambdaSquared w d| * (d:ℝ) := trunc
    _ ≤ ∑ _d ∈ U, (R:ℝ)^8 := by
          exact Finset.sum_le_sum fun d hd => each d hd
    _ ≤ (M:ℝ) * (R:ℝ)^8 := by
          simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast cardU)
            (by positivity)
    _ = (R:ℝ)^10 := by simp [M]; ring
end
end BrunSupport
namespace BrunSupport
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators ArithmeticFunction.Moebius
noncomputable section

/-- The exceptional prime 2 supplies the same `2/p` term: the root count
is one and `nu/(1-nu)=1`. -/
lemma twin_selbergTerms_prime_lower_all (k p : ℕ) (hp : p.Prime)
    (hP : p ∣ (twinSieve k).prodPrimes) :
    (2:ℝ) / p ≤ (twinSieve k).selbergTerms p := by
  classical
  by_cases h2 : p = 2
  · subst p
    rw [BoundingSieve.selbergTerms_apply]
    have pf : (2:ℕ).primeFactors = {2} := by
      simp [Nat.primeFactors, Nat.primeFactorsList_prime (by decide : (2:ℕ).Prime)]
    rw [pf]
    -- both factors are explicit in this case
    have hn : (twinSieve k).nu 2 = (1:ℝ)/2 := by
      change twinNu 2 = _
      rw [twinNu_prime (by decide : (2:ℕ).Prime)]
      have hc : polyResidues 2 = 1 := by decide
      rw [hc]
      norm_num
    norm_num [hn]
  · exact twin_selbergTerms_prime_lower k p hp h2 hP

/-- On a square-free modulus made out of sieving primes the denominator
term dominates the square-free divisor weight `2^ω(d)/d`.  This is a
convenient form not involving residues any more. -/
lemma twin_selbergTerms_squarefree_lower (k d : ℕ)
    (hd : d ∣ (twinSieve k).prodPrimes) :
    ((2:ℝ) ^ d.primeFactors.card) / (d:ℝ)
       ≤ (twinSieve k).selbergTerms d := by
  classical
  have hsf : Squarefree d := (twinSieve k).squarefree_of_dvd_prodPrimes hd
  have d0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (twinSieve k).prodPrimes_ne_zero hd
  have rep : (twinSieve k).selbergTerms d =
      ∏ p ∈ d.primeFactors,
        ((twinSieve k).nu p * (1 - (twinSieve k).nu p)⁻¹) := by
    rw [BoundingSieve.selbergTerms_apply,
      ← BoundingSieve.prod_primeFactors_nu hd,
      ← Finset.prod_mul_distrib]
  rw [rep]
  have lowerProd :
      ∏ p ∈ d.primeFactors, ((2:ℝ)/(p:ℝ)) ≤
        ∏ p ∈ d.primeFactors,
          ((twinSieve k).nu p * (1-(twinSieve k).nu p)⁻¹) := by
    apply Finset.prod_le_prod
    · intro i hi; positivity
    intro p hp
    have pp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have pd : p ∣ (twinSieve k).prodPrimes :=
      (Nat.dvd_of_mem_primeFactors hp).trans hd
    have H := twin_selbergTerms_prime_lower_all k p pp pd
    have onep : (twinSieve k).selbergTerms p =
        ((twinSieve k).nu p * (1-(twinSieve k).nu p)⁻¹) := by
      rw [BoundingSieve.selbergTerms_apply]
      have pf : p.primeFactors = {p} := by
        simp [Nat.primeFactors, Nat.primeFactorsList_prime pp]
      rw [pf]
      simp
    simpa [onep] using H
  calc
    ((2:ℝ)^d.primeFactors.card) / (d:ℝ)
        = ∏ p ∈ d.primeFactors, ((2:ℝ)/(p:ℝ)) := by
            rw [Finset.prod_div_distrib]
            simp
            have rr := Nat.prod_primeFactors_of_squarefree hsf
            norm_cast at rr ⊢
            rw [← Nat.cast_prod]
            rw [rr]
    _ ≤ _ := lowerProd

/-- For a square-free number the number of divisors is exactly
`2^card(primeFactors)`. -/
lemma card_divisors_squarefree {d : ℕ} (hd : Squarefree d) :
    d.divisors.card = 2 ^ d.primeFactors.card := by
  classical
  rw [Nat.card_divisors hd.ne_zero]
  -- Each exponent in a square-free factorisation is one.
  calc
    d.primeFactors.prod (fun p => d.factorization p + 1)
        = ∏ _p ∈ d.primeFactors, (2:ℕ) := by
            apply Finset.prod_congr rfl
            intro p hp
            have pp : p.Prime := Nat.prime_of_mem_primeFactors hp
            have pd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
            rw [Nat.factorization_eq_one_of_squarefree hd pp pd]
    _ = _ := by simp

lemma twin_selbergTerms_divisors_lower (k d : ℕ)
    (hd : d ∣ (twinSieve k).prodPrimes) :
    (d.divisors.card : ℝ) / (d:ℝ)
       ≤ (twinSieve k).selbergTerms d := by
  have hsf : Squarefree d := (twinSieve k).squarefree_of_dvd_prodPrimes hd
  simpa [card_divisors_squarefree hsf] using
    (twin_selbergTerms_squarefree_lower k d hd)
end
end BrunSupport

-- END INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/SelbergEstimate.lean

-- BEGIN INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/Denominator.lean
namespace BrunSupport
open Finset Nat BoundingSieve ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius
noncomputable section

def sfset (X : ℕ) : Finset ℕ := (Finset.Icc 1 X).filter Squarefree
def har (C : Finset ℕ) : ℝ := ∑ n ∈ C, (1:ℝ) / n
def HX (X : ℕ) : ℝ := har (Finset.Icc 1 X)

lemma wnon (n:ℕ) : 0 ≤ (1:ℝ)/n := by positivity

/-- finite union bound in the slightly convenient weighted form -/
lemma union_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (u : Finset α) (v : Finset β) (Q : α → Prop) (T : β → α → Prop)
    [DecidablePred Q] [∀ b, DecidablePred (T b)]
    (w : α → ℝ) (hw : ∀ a ∈ u, 0 ≤ w a)
    (cover : ∀ a ∈ u, Q a → ∃ b ∈ v, T b a) :
    (∑ a ∈ u.filter Q, w a) ≤
       ∑ b ∈ v, ∑ a ∈ u.filter (T b), w a := by
  classical
  rw [Finset.sum_filter]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hq : Q a
  · simp [hq]
    obtain ⟨b,hb,ht⟩ := cover a ha hq
    have hn : ∀ i ∈ v, 0 ≤ (if T i a then w a else 0) := by
      intro i hi; split_ifs <;> simp [hw a ha]
    have one := Finset.single_le_sum (fun i hi => hn i hi) hb
    simpa [ht] using one
  · simp [hq]
    exact Finset.sum_nonneg (fun i hi => by split_ifs <;> simp [hw a ha])

/-- Multiples in a division-closed finite set have at most `1/m` of its harmonic mass. -/
lemma multiples_le (C : Finset ℕ) (m : ℕ) (hm : 0 < m)
    (hcpos : ∀ n ∈ C, 0 < n)
    (hdown : ∀ n ∈ C, m ∣ n → n / m ∈ C) :
    (∑ n ∈ C.filter (fun n => m ∣ n), (1:ℝ)/n) ≤ har C / (m:ℝ) := by
  classical
  let A := C.filter (fun n => m ∣ n)
  let g : ℕ → ℕ := fun n => n / m
  let h : ℕ → ℝ := fun u => (1:ℝ)/u / m
  have inj : Set.InjOn g (↑A : Set ℕ) := by
    intro x hx y hy he
    have hx' : m ∣ x := (Finset.mem_filter.mp hx).2
    have hy' : m ∣ y := (Finset.mem_filter.mp hy).2
    have ex : x / m * m = x := Nat.div_mul_cancel hx'
    have ey : y / m * m = y := Nat.div_mul_cancel hy'
    calc
      x = x/m*m := ex.symm
      _ = y/m*m := by change g x * m = g y * m; rw [he]
      _ = y := ey
  have sub : A.image g ⊆ C := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n,hn,rfl⟩
    exact hdown n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
  have eqw (n : ℕ) (hn : n ∈ A) : (1:ℝ)/n = h (g n) := by
    have hd : m ∣ n := (Finset.mem_filter.mp hn).2
    have en : m * (n/m) = n := Nat.mul_div_cancel' hd
    have mm : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    have uu : ((n/m:ℕ):ℝ) ≠ 0 := by
      have npos : 0 < n := hcpos n (Finset.mem_filter.mp hn).1
      have pos : 0 < n/m := Nat.div_pos (Nat.le_of_dvd npos hd) hm
      exact_mod_cast (Nat.ne_of_gt pos)
    change (1:ℝ)/(n:ℝ) = (1:ℝ)/( (n/m:ℕ):ℝ) / (m:ℝ)
    have ec : (n:ℝ) = (m:ℝ) * ((n/m:ℕ):ℝ) := by exact_mod_cast en.symm
    rw [ec]
    field_simp
    <;> ring

  have imgEq : ∑ z ∈ A.image g, h z = ∑ n ∈ A, h (g n) :=
    Finset.sum_image inj
  calc
    (∑ n ∈ C.filter (fun n => m ∣ n), (1:ℝ)/n)
        = ∑ n ∈ A, h (g n) := by
            apply Finset.sum_congr rfl
            intro n hn; exact eqw n hn
    _ = ∑ z ∈ A.image g, h z := imgEq.symm
    _ ≤ ∑ z ∈ C, h z := by
          apply Finset.sum_le_sum_of_subset_of_nonneg sub
          intro i hi hnot
          dsimp [h]; positivity
    _ = har C / (m:ℝ) := by
          simp [har, h, Finset.sum_div]

end
end BrunSupport
namespace BrunSupport
open Finset Nat BoundingSieve ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius
noncomputable section
lemma har_non (C:Finset ℕ) : 0 ≤ har C := by
  unfold har; exact Finset.sum_nonneg (fun n hn => by positivity)

lemma reciprocal_sq_aux (n:ℕ) (hn: 1 ≤ n) :
    (1:ℝ)/((n+1:ℕ):ℝ)^2 ≤ (1:ℝ)/(n:ℝ) - (1:ℝ)/((n+1:ℕ):ℝ) := by
  have np : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<1) hn)
  have n1 : (0:ℝ) < n+1 := by positivity
  calc
    (1:ℝ)/((n+1:ℕ):ℝ)^2
        ≤ (1:ℝ)/((n:ℝ)*(n+1)) := by
            apply one_div_le_one_div_of_le (by positivity)
            push_cast
            nlinarith
    _ = (1:ℝ)/(n:ℝ) - (1:ℝ)/((n+1:ℕ):ℝ) := by
          push_cast
          field_simp
          ring

lemma sqsum_bound (X:ℕ) :
    (∑ m ∈ Finset.Icc 2 X, (1:ℝ)/(m:ℝ)^2) ≤ 3/4 := by
  by_cases hx : 2 ≤ X
  · -- stronger telescoping invariant
    have strong : ∀ n : ℕ, 2 ≤ n →
        (∑ m ∈ Finset.Icc 2 n, (1:ℝ)/(m:ℝ)^2) ≤ 3/4 - (1:ℝ)/n := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n+1)]
        have addb := reciprocal_sq_aux n (by omega : 1 ≤ n)
        push_cast at addb ⊢
        calc
          (∑ m ∈ Finset.Icc 2 n, (1:ℝ)/(m:ℝ)^2) + 1 / ((n:ℝ)+1)^2
             ≤ (3/4 - (1:ℝ)/n) + ((1:ℝ)/n - 1/((n:ℝ)+1)) :=
               add_le_add ih addb
          _ = 3/4 - (1:ℝ)/(n+1) := by push_cast; ring
    have H := strong X hx
    have non : 0 ≤ (1:ℝ)/X := by positivity
    linarith
  · have hlt : X < 2 := Nat.lt_of_not_ge hx
    have empty : Finset.Icc 2 X = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      rcases hne with ⟨a,ha⟩
      have hh := Finset.mem_Icc.mp ha
      omega
    rw [empty]
    norm_num

lemma nonsquare_cover (X n:ℕ) (hn : n ∈ Finset.Icc 1 X)
    (hbad : ¬ Squarefree n) :
    ∃ m ∈ Finset.Icc 2 X, m*m ∣ n := by
  have h := (not_congr Nat.squarefree_iff_prime_squarefree).mp hbad
  push_neg at h
  rcases h with ⟨p,hp,hd⟩
  refine ⟨p, Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩, hd⟩
  have le : p ≤ n := Nat.le_of_dvd (by have := (Finset.mem_Icc.mp hn).1; omega : 0 < n) (dvd_trans (by exact dvd_mul_right p p) hd)
  exact le_trans le (Finset.mem_Icc.mp hn).2

lemma icc_down_square (X m n:ℕ) (hn : n ∈ Finset.Icc 1 X) (hd : m*m ∣ n)
    (hm : 0 < m) : n / (m*m) ∈ Finset.Icc 1 X := by
  have npos : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  have mm : 0 < m*m := Nat.mul_pos hm hm
  apply Finset.mem_Icc.mpr
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd npos hd) mm))
  · exact le_trans (Nat.div_le_self _ _) (Finset.mem_Icc.mp hn).2

lemma sf_mass (X:ℕ) : HX X / 4 ≤ har (sfset X) := by
  classical
  let U := Finset.Icc 1 X
  let V := Finset.Icc 2 X
  let B := sfset X
  let Bad := U.filter (fun n => ¬ Squarefree n)
  have posU : ∀ n∈U, 0 < n := by intro n hn; exact (Finset.mem_Icc.mp hn).1
  have cov := union_bound U V (fun n => ¬ Squarefree n)
      (fun m n => m*m ∣ n) (fun n => (1:ℝ)/n)
      (by intro n hn; positivity)
      (by intro n hn h; exact nonsquare_cover X n hn h)
  have each (m : ℕ) (hmV : m ∈ V) :
      (∑ n ∈ U.filter (fun n => m*m ∣ n), (1:ℝ)/n) ≤ HX X / ((m:ℝ)^2) := by
    have mm : 0 < m*m := Nat.mul_pos (by have := (Finset.mem_Icc.mp hmV).1; omega)
       (by have := (Finset.mem_Icc.mp hmV).1; omega)
    have H := multiples_le U (m*m) mm posU (by
      intro n hn hd
      exact icc_down_square X m n hn hd (by have := (Finset.mem_Icc.mp hmV).1; omega))
    simpa [HX, pow_two, Nat.cast_mul] using H
  have badle : (∑ n ∈ Bad, (1:ℝ)/n) ≤ HX X * (3/4:ℝ) := by
    calc
      (∑ n ∈ Bad, (1:ℝ)/n)
        ≤ ∑ m ∈ V, ∑ n ∈ U.filter (fun n => m*m ∣ n), (1:ℝ)/n := cov
      _ ≤ ∑ m ∈ V, HX X / ((m:ℝ)^2) := Finset.sum_le_sum (fun m hm => each m hm)
      _ = HX X * (∑ m ∈ V, (1:ℝ)/(m:ℝ)^2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm; ring
      _ ≤ HX X * (3/4:ℝ) :=
            mul_le_mul_of_nonneg_left (sqsum_bound X) (by unfold HX; exact har_non _)
  have split : har B + har Bad = HX X := by
    have := Finset.sum_filter_add_sum_filter_not U (fun n => Squarefree n) (fun n => (1:ℝ)/n)
    -- second filter uses ¬ Squarefree already
    simpa [har, HX, B, Bad, sfset, U] using this
  dsimp [B, Bad, U] at split badle ⊢
  change har ((Finset.Icc 1 X).filter (fun n => ¬ Squarefree n)) ≤ HX X * (3/4:ℝ) at badle
  linarith
end
end BrunSupport
namespace BrunSupport
open Finset Nat BoundingSieve ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius
noncomputable section

def goodpairs (X:ℕ) : Finset (ℕ × ℕ) :=
  ((sfset X) ×ˢ (sfset X)).filter (fun z => Nat.Coprime z.1 z.2)
def wp (z : ℕ × ℕ) : ℝ := (1:ℝ) / (z.1*z.2 : ℕ)

lemma sf_pos {X n:ℕ} (hn : n ∈ sfset X) : 0 < n :=
  (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
lemma sf_le {X n:ℕ} (hn : n ∈ sfset X) : n ≤ X :=
  (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
lemma sf_down (X m n : ℕ) (hm : 0 < m) (hn : n ∈ sfset X) (hd : m ∣ n) : n/m ∈ sfset X := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt
       (Nat.div_pos (Nat.le_of_dvd (sf_pos hn) hd) hm)),
       le_trans (Nat.div_le_self _ _) (sf_le hn)⟩
  · exact Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hd)
       (Finset.mem_filter.mp hn).2

lemma pair_weight_mul (a b:ℕ) :
    wp (a,b) = ((1:ℝ)/a) * ((1:ℝ)/b) := by
  dsimp [wp]
  push_cast
  simp [div_eq_mul_inv, mul_inv_rev]
  <;> ring

lemma div_pair_sum (X m:ℕ) :
    (∑ z ∈ ((sfset X) ×ˢ (sfset X)).filter
          (fun z => m ∣ z.1 ∧ m ∣ z.2), wp z)
      = (∑ a ∈ (sfset X).filter (fun a => m ∣ a), (1:ℝ)/a)^2 := by
  classical
  let C := (sfset X).filter (fun a => m ∣ a)
  have seteq : ((sfset X) ×ˢ (sfset X)).filter
          (fun z => m ∣ z.1 ∧ m ∣ z.2) = C ×ˢ C := by
    ext z
    simp [C]
    aesop
  rw [seteq, Finset.sum_product]
  have eq1 : (∑ a ∈ C, ∑ b ∈ C, wp (a,b)) =
      (∑ a ∈ C, (1:ℝ)/a) * (∑ b ∈ C, (1:ℝ)/b) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact (pair_weight_mul a b)
  simpa [C, pow_two] using eq1

lemma goodpairs_mass (X:ℕ) :
    (har (sfset X))^2 / 4 ≤ ∑ z ∈ goodpairs X, wp z := by
  classical
  let B := sfset X
  let U := B ×ˢ B
  let V := Finset.Icc 2 X
  let Bad := U.filter (fun z => ¬ Nat.Coprime z.1 z.2)
  have posB : ∀ n∈B, 0<n := by intro n hn; exact sf_pos hn
  have cov := union_bound U V (fun z => ¬ Nat.Coprime z.1 z.2)
      (fun m z => m.Prime ∧ m ∣ z.1 ∧ m ∣ z.2) wp
      (by intro z hz; dsimp [wp]; positivity)
      (by
        intro z hz hbad
        rcases (Nat.Prime.not_coprime_iff_dvd.mp hbad) with ⟨p,hp,ha,hb⟩
        refine ⟨p, Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩, hp, ha, hb⟩
        have az : z.1 ∈ B := (Finset.mem_product.mp hz).1
        exact le_trans (Nat.le_of_dvd (sf_pos az) ha) (sf_le az))
  have term (m:ℕ) (hmV : m ∈ V) :
      (∑ z ∈ U.filter (fun z => m.Prime ∧ m ∣ z.1 ∧ m ∣ z.2), wp z)
           ≤ (har B)^2 / (m:ℝ)^2 := by
    by_cases hp : m.Prime
    · have remove : U.filter (fun z => m.Prime ∧ m ∣ z.1 ∧ m ∣ z.2) =
            U.filter (fun z => m ∣ z.1 ∧ m ∣ z.2) := by
          ext z; simp [hp]
      rw [remove]
      have formula := div_pair_sum X m
      change (∑ z ∈ ((sfset X) ×ˢ (sfset X)).filter _, wp z) ≤ _
      rw [formula]
      have one := multiples_le B m hp.pos posB (by
        intro n hn hd
        dsimp [B] at hn ⊢
        exact sf_down X m n hp.pos hn hd)
      have hnon : 0 ≤ ∑ a ∈ B.filter (fun a => m ∣ a), (1:ℝ)/a :=
        Finset.sum_nonneg (fun i hi => by positivity)
      have Hnon : 0 ≤ har B / (m:ℝ) := div_nonneg (har_non _) (by positivity)
      calc
        (∑ a ∈ B.filter (fun a => m ∣ a), (1:ℝ)/a)^2
           ≤ (har B / (m:ℝ))^2 := by nlinarith
        _ = (har B)^2 / (m:ℝ)^2 := by ring
    · have emp : U.filter (fun z => m.Prime ∧ m ∣ z.1 ∧ m ∣ z.2) = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hn
          rcases hn with ⟨z,hz⟩
          exact hp (Finset.mem_filter.mp hz).2.1
      rw [emp]
      simp
      positivity
  have badle : (∑ z ∈ Bad, wp z) ≤ (har B)^2 * (3/4:ℝ) := by
    calc
      (∑ z ∈ Bad, wp z)
       ≤ ∑ m ∈ V, ∑ z ∈ U.filter (fun z => m.Prime ∧ m ∣ z.1 ∧ m ∣ z.2), wp z := cov
      _ ≤ ∑ m ∈ V, (har B)^2 / (m:ℝ)^2 := Finset.sum_le_sum (fun m hm => term m hm)
      _ = (har B)^2 * (∑ m ∈ V, (1:ℝ)/(m:ℝ)^2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm; ring
      _ ≤ (har B)^2 * (3/4:ℝ) := by
            exact mul_le_mul_of_nonneg_left (sqsum_bound X) (sq_nonneg _)
  have total : (∑ z ∈ U, wp z) = (har B)^2 := by
    rw [Finset.sum_product]
    change (∑ a ∈ B, ∑ b ∈ B, wp (a,b)) = _
    simp only [har, pow_two]
    change (∑ a ∈ B, ∑ b ∈ B, wp (a,b)) = (∑ a ∈ B, (1:ℝ)/a) * (∑ b ∈ B, (1:ℝ)/b)
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact (pair_weight_mul a b)
  have split : (∑ z ∈ goodpairs X, wp z) + (∑ z ∈ Bad, wp z) = (har B)^2 := by
    have h := Finset.sum_filter_add_sum_filter_not U (fun z => Nat.Coprime z.1 z.2) wp
    simpa [goodpairs, Bad, U, total, B] using h
  dsimp [Bad] at badle
  change (∑ z ∈ U.filter (fun z => ¬ Nat.Coprime z.1 z.2), wp z) ≤
       (har B)^2 * (3/4:ℝ) at badle
  linarith
end
end BrunSupport
namespace BrunSupport
open Finset Nat BoundingSieve ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius
noncomputable section
lemma hx_pow (r:ℕ) : (r:ℝ)/2 ≤ HX (2^r) := by
  induction r with
  | zero => simp [HX, har]
  | succ r ih =>
    let a : ℕ := 2^r
    have apos : 0 < a := by dsimp [a]; positivity
    let J := Finset.Icc (a+1) (a+a)
    have union : Finset.Icc 1 (2^(r+1)) = Finset.Icc 1 a ∪ J := by
      ext n
      have pow : 2^(r+1) = a+a := by dsimp [a]; simp [pow_succ]; omega
      simp only [Finset.mem_Icc, Finset.mem_union, J]
      rw [pow]
      omega
    have dis : Disjoint (Finset.Icc 1 a) J := by
      apply Finset.disjoint_left.mpr
      intro n hn hk
      have one := (Finset.mem_Icc.mp hn).2
      have two := (Finset.mem_Icc.mp hk).1
      omega
    have Jbound : (1/2:ℝ) ≤ ∑ n ∈ J, (1:ℝ)/n := by
      have ec : J.card = a := by simp [J, Nat.card_Icc]
      calc
        (1/2:ℝ) = (a:ℝ) * ((1:ℝ)/( (a+a:ℕ):ℝ)) := by
              push_cast
              have : (0:ℝ) < a := by exact_mod_cast apos
              field_simp; ring
        _ = ∑ _n ∈ J, (1:ℝ)/((a+a:ℕ):ℝ) := by simp [ec]
        _ ≤ ∑ n ∈ J, (1:ℝ)/n := by
              apply Finset.sum_le_sum
              intro n hn
              have np : 0 < n := lt_of_lt_of_le (by omega : 0 < a+1) (Finset.mem_Icc.mp hn).1
              apply one_div_le_one_div_of_le (by exact_mod_cast np : (0:ℝ)< n)
              exact_mod_cast (Finset.mem_Icc.mp hn).2
    unfold HX har at ih ⊢
    rw [union, Finset.sum_union dis]
    push_cast
    linarith
end
end BrunSupport
namespace BrunSupport
open Finset Nat BoundingSieve ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius
noncomputable section
lemma pair_maps (k m:ℕ) (small : 2^(2*m) < cutoff k) {z:ℕ×ℕ}
    (hz : z ∈ goodpairs (2^m)) :
    z.1*z.2 ∈ levelDivs (twinSieve k) (2^(2*m)) := by
  have a := (Finset.mem_filter.mp hz).1
  have ac : z.1 ∈ sfset (2^m) := (Finset.mem_product.mp a).1
  have bc : z.2 ∈ sfset (2^m) := (Finset.mem_product.mp a).2
  have cp : Nat.Coprime z.1 z.2 := (Finset.mem_filter.mp hz).2
  have hsfree : Squarefree (z.1*z.2) :=
    (Nat.squarefree_mul cp).2 ⟨(Finset.mem_filter.mp ac).2,
      (Finset.mem_filter.mp bc).2⟩
  have le : z.1*z.2 ≤ 2^(2*m) := by
    have aa := sf_le ac
    have bb := sf_le bc
    calc
      z.1*z.2 ≤ (2^m)*(2^m) := Nat.mul_le_mul aa bb
      _ = 2^(2*m) := by ring
  have lecut : z.1*z.2 ≤ cutoff k - 1 := by omega
  have dvd : z.1*z.2 ∣ (twinSieve k).prodPrimes := by
    change z.1*z.2 ∣ primorial (cutoff k - 1)
    exact dvd_trans (Squarefree.dvd_primorial hsfree) (primorial_dvd_primorial lecut)
  exact Finset.mem_filter.mpr ⟨(Nat.mem_divisors.mpr ⟨dvd, (twinSieve k).prodPrimes_ne_zero⟩), le⟩

lemma denominator_pairs (k m:ℕ) (small : 2^(2*m) < cutoff k) :
    (∑ d ∈ levelDivs (twinSieve k) (2^(2*m)), (d.divisors.card:ℝ)/(d:ℝ))
      ≥ ∑ z ∈ goodpairs (2^m), wp z := by
  classical
  let G := goodpairs (2^m)
  let L := levelDivs (twinSieve k) (2^(2*m))
  let g : ℕ×ℕ → ℕ := fun z => z.1*z.2
  have maps : ∀ z ∈ G, g z ∈ L := by
    intro z hz; exact pair_maps k m small hz
  have fibercard (d:ℕ) : (G.filter (fun z => g z = d)).card ≤ d.divisors.card := by
    let F := G.filter (fun z => g z = d)
    have dpos' {z} (hz : z ∈ F) : 0 < z.1 := by
      have hG : z ∈ G := (Finset.mem_filter.mp hz).1
      exact sf_pos ((Finset.mem_product.mp ((Finset.mem_filter.mp hG).1)).1)
    apply Finset.card_le_card_of_injOn (fun z : ℕ×ℕ => z.1)
    · intro z hz
      have e : z.1*z.2 = d := (Finset.mem_filter.mp hz).2
      apply Nat.mem_divisors.mpr
      exact ⟨by rw [← e]; exact dvd_mul_right _ _, by
        rw [← e]; exact Nat.mul_ne_zero (Nat.ne_of_gt (dpos' hz))
             (Nat.ne_of_gt (sf_pos ((Finset.mem_product.mp
                ((Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1)).2)))⟩
    · intro x hx y hy hxy
      have ex : x.1*x.2 = d := (Finset.mem_filter.mp hx).2
      have ey : y.1*y.2 = d := (Finset.mem_filter.mp hy).2
      cases x with | mk a b =>
        cases y with | mk c e =>
          simp at hxy ⊢
          simp at ex ey
          subst c
          exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (dpos' hx) (ex.trans ey.symm)⟩
  have fiberle (d:ℕ) (hd:d∈L) :
      (∑ z ∈ G.filter (fun z => g z = d), wp z) ≤ (d.divisors.card:ℝ)/d := by
    have fc := fibercard d
    calc
      (∑ z ∈ G.filter (fun z => g z = d), wp z)
        = ∑ _z ∈ G.filter (fun z => g z = d), (1:ℝ)/d := by
            apply Finset.sum_congr rfl
            intro z hz
            have e := (Finset.mem_filter.mp hz).2
            dsimp [wp, g] at e ⊢
            rw [e]
      _ = ((G.filter (fun z => g z = d)).card:ℝ) / d := by simp [div_eq_mul_inv]
      _ ≤ (d.divisors.card:ℝ)/d := by
            gcongr
  calc
    (∑ d ∈ levelDivs (twinSieve k) (2^(2*m)), (d.divisors.card:ℝ)/(d:ℝ))
       ≥ ∑ d ∈ L, ∑ z ∈ G.filter (fun z => g z = d), wp z := by
          exact Finset.sum_le_sum (fun d hd => fiberle d hd)
    _ = ∑ z ∈ G, wp z := Finset.sum_fiberwise_of_maps_to maps _
    _ = _ := rfl

lemma sgDen_growth (k m:ℕ) (small : 2^(2*m) < cutoff k) :
    ( (m:ℝ)^2 / 256) ≤ sgDen (twinSieve k) (2^(2*m)) := by
  have denlocal : (∑ d ∈ levelDivs (twinSieve k) (2^(2*m)),
       (d.divisors.card:ℝ)/d) ≤ sgDen (twinSieve k) (2^(2*m)) := by
    unfold sgDen
    apply Finset.sum_le_sum
    intro d hd
    exact twin_selbergTerms_divisors_lower k d (mem_levelDivs_dvd _ hd)
  have pairs := denominator_pairs k m small
  have gp := goodpairs_mass (2^m)
  have mass := sf_mass (2^m)
  have hh := hx_pow m
  have non : 0 ≤ HX (2^m) := by unfold HX; exact har_non _
  have hb : 0 ≤ har (sfset (2^m)) := har_non _
  have mr : 0 ≤ (m:ℝ) := by positivity
  calc
    (m:ℝ)^2 / 256 ≤ (har (sfset (2^m)))^2 / 4 := by nlinarith [mass]
    _ ≤ ∑ z ∈ goodpairs (2^m), wp z := gp
    _ ≤ ∑ d ∈ levelDivs (twinSieve k) (2^(2*m)), (d.divisors.card:ℝ)/d := pairs
    _ ≤ _ := denlocal
end
end BrunSupport

-- END INLINED FILE: Mathlib/Support/brun_constant_converges_a2e6449355/Denominator.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval.NumberTheory.BrunConstant

/-!
# Brun's theorem (convergence of the twin-prime reciprocal sum)

§224 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. Brun's
theorem states that the sum of the reciprocals of the twin primes converges,
to a value now known as Brun's constant.

mathlib has `Nat.Prime`, `Summable`, and prime-counting estimates, but no
Brun sieve and hence no proof of this convergence.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

/-- A twin-prime start is a prime `p` such that `p + 2` is also prime. -/
def IsTwinPrimeStart (p : ℕ) : Prop :=
  p.Prime ∧ (p + 2).Prime

/-- The reciprocal contribution of the twin pair beginning at `p`.

This counts each pair once, by its smaller prime. -/
noncomputable def twinPrimeReciprocalTerm (p : ℕ) : ℝ :=
  by
    classical
    exact if IsTwinPrimeStart p then (1 / (p : ℝ)) + (1 / ((p + 2 : ℕ) : ℝ)) else 0



end LeanEval.NumberTheory.BrunConstant

open LeanEval.NumberTheory.BrunConstant
open Filter Finset MeasureTheory
open scoped BigOperators Topology
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem brun_constant_converges :
    Summable twinPrimeReciprocalTerm :=
/-ResultProofBegin-/by
  classical
  -- nonnegativity and the elementary dyadic estimate for an individual pair
  let P : ℕ → Prop := IsTwinPrimeStart
  let f : ℕ → ℝ := twinPrimeReciprocalTerm
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f, twinPrimeReciprocalTerm]
    split_ifs
    · positivity
    · exact le_rfl
  have hz : ∀ n, ¬ P n → f n = 0 := by
    intro n hn
    simp [f, P, twinPrimeReciprocalTerm, hn]
  have hle : ∀ k p, p ∈ BrunSupport.block k → P p →
      f p ≤ 2 / ((2:ℝ)^k) := by
    intro k p hp hP
    have hp' : 2^k ≤ p := (BrunSupport.mem_block.mp hp).1
    have basepos : 0 < (2:ℝ)^k := by positivity
    have cp : (2:ℝ)^k ≤ (p:ℝ) := by
      exact_mod_cast hp'
    have cp2 : (2:ℝ)^k ≤ ((p+2:ℕ):ℝ) := by
      exact_mod_cast (le_trans hp' (Nat.le_add_right _ _))
    have t1 : 1 / (p:ℝ) ≤ 1 / ((2:ℝ)^k) :=
      one_div_le_one_div_of_le basepos cp
    have t2 : 1 / ((p+2:ℕ):ℝ) ≤ 1 / ((2:ℝ)^k) :=
      one_div_le_one_div_of_le basepos cp2
    dsimp [f, twinPrimeReciprocalTerm]
    rw [if_pos hP]
    calc
      1 / (p:ℝ) + 1 / ((p+2:ℕ):ℝ)
          ≤ 1 / ((2:ℝ)^k) + 1 / ((2:ℝ)^k) := add_le_add t1 t2
      _ = 2 / ((2:ℝ)^k) := by ring
  -- This is the number theoretic (sieve) component of Brun's theorem.
  have finite_selberg_sieve : ∃ A : ℕ, ∀ k, 4 ≤ k →
      (k+1)^2 * BrunSupport.coprimeValueCount k ≤ A * 2^k := by
    -- The exact local data (and, in particular, the **uniform** residue
    -- error which is the nuisance with translating the sieve to intervals)
    -- are finite rather than asymptotic.  We put them in this format before
    -- the still analytic Selberg optimisation below.
    let S : ℕ → BoundingSieve := BrunSupport.twinSieve
    have Smult (k d : ℕ) (hd : 0 < d) :
        |(S k).multSum d -
             ((2^k:ℕ):ℝ) * (BrunSupport.polyResidues d:ℝ) / d|
          ≤ (BrunSupport.polyResidues d:ℝ) := by
      exact BrunSupport.twinSieve_multSum_abs_error k hd
    have Sval (k : ℕ) :
        (S k).siftedSum = (BrunSupport.coprimeValueCount k:ℝ) := by
      exact BrunSupport.twinSieve_siftedSum k
    have Ssquare (k : ℕ) : Squarefree (S k).prodPrimes :=
      (S k).prodPrimes_squarefree
    have Sdensity (q : ℕ) (hq : q.Prime) :
        0 < BrunSupport.twinNu q ∧ BrunSupport.twinNu q < 1 :=
      ⟨BrunSupport.twinNu_pos_prime hq,
       BrunSupport.twinNu_lt_one_prime hq⟩
    -- CRT is needed here: `nu` is not merely the prescribed prime
    -- density. All lcms appearing in a lambda-square are *square-free*
    -- divisors of `prodPrimes`; on them it is the actual root density.
    have Slocal {d : ℕ} (hd : Squarefree d) :
        BrunSupport.twinNu d =
          (BrunSupport.polyResidues d : ℝ) / d :=
      BrunSupport.twinNu_eq_polyResidues_div hd
    have Srem (k d : ℕ) (hdP : d ∣ (S k).prodPrimes) :
        |(S k).rem d| ≤ (d : ℝ) := by
      have dpos : 0 < d := Nat.pos_of_ne_zero
        (ne_zero_of_dvd_ne_zero (S k).prodPrimes_ne_zero hdP)
      calc
        |(S k).rem d| ≤ (BrunSupport.polyResidues d : ℝ) := by
          change |(BrunSupport.twinSieve k).rem d| ≤ _
          exact BrunSupport.twinSieve_rem_bound k dpos
            ((S k).squarefree_of_dvd_prodPrimes hdP)
        _ ≤ (d : ℝ) := by exact_mod_cast BrunSupport.polyResidues_le d
    have Serr (k : ℕ) (mu : ℕ → ℝ) :
        (S k).errSum mu ≤ ∑ d ∈ (S k).prodPrimes.divisors,
            |mu d| * (d : ℝ) := by
      exact BrunSupport.twinSieve_err_bound k mu
    -- For any future (finite) lambda choice the error calculation now has
    -- no analytic content.  A lambda supported and bounded by `L` has
    -- coefficients of size at most `#divisors(d)^2 L^2`, and they vanish
    -- unless `d ≤ L^2`.  Thus a sufficiently small exponential level
    -- makes this whole remainder polynomially negligible.
    have Slam (L d : ℕ) (w : ℕ → ℝ)
        (hw : ∀ i, |w i| ≤ (L : ℝ)) :
        |BoundingSieve.lambdaSquared w d| ≤
          (d.divisors.card : ℝ)^2 * (L : ℝ)^2 := by
      exact BrunSupport.lambdaSquared_abs_le_pow L d w hw
    have Strunc (L d : ℕ) (w : ℕ → ℝ)
        (hw : ∀ i, L < i → w i = 0) (hL : L*L < d) :
        BoundingSieve.lambdaSquared w d = 0 :=
      BrunSupport.lambdaSquared_eq_zero_of_lt L d w hw hL
    -- On odd primes a denominator term costs at least `2/q`; this is the
    -- elementary start of the remaining lower-bound argument.
    have Sodd (k q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
        (hdiv : q ∣ (S k).prodPrimes) :
        (2:ℝ)/q ≤ (S k).selbergTerms q := by
      exact BrunSupport.twin_selbergTerms_prime_lower k q hq hq2 hdiv
    -- What remains here is the (upper-bound) Selberg choice of
    -- square-free lambda-weights and its denominator estimate.  The
    -- preceding exact error is the endpoint-sensitive part and no longer an
    -- implicit rounding assumption.
    -- Unlike an existential invocation of the quadratic form, these are now
    -- actual finite weights.  They have lambda_1=1; their multiples transform
    -- by Möbius inversion.  Thus the main quadratic form is exactly the
    -- reciprocal of the positive finite denominator.  The remaining open
    -- part is only a lower estimate for this denominator.
    have chosen_one (k R : ℕ) (hR : 1 ≤ R) :
        BrunSupport.sgWeight (S k) R 1 = 1 := by
      exact BrunSupport.sgWeight_one (S k) hR
    have chosen_main (k R : ℕ) (hR : 1 ≤ R) :
        (S k).mainSum
            (BoundingSieve.lambdaSquared (BrunSupport.sgWeight (S k) R)) =
          (BrunSupport.sgDen (S k) R)⁻¹ := by
      exact BrunSupport.sg_main (S k) hR
    have chosen_sift (k R : ℕ) (hR : 1 ≤ R) :
        (BrunSupport.coprimeValueCount k : ℝ) ≤
          (S k).totalMass / BrunSupport.sgDen (S k) R +
            (S k).errSum
              (BoundingSieve.lambdaSquared (BrunSupport.sgWeight (S k) R)) := by
      rw [← Sval]
      exact BrunSupport.sg_sifted (S k) hR
    have chosen_truncated (k R d : ℕ) (hd : R < d) :
        BrunSupport.sgWeight (S k) R d = 0 :=
      BrunSupport.sgWeight_zero hd
    -- Uniform control of these particular weights is elementary: a
    -- numerator is a subsum of the denominator and `nu d ≥ 1/d`.
    -- Consequently the complete remainder at level `R` is at most the
    -- fixed polynomial `R^10`.  Also the exceptional prime two has the
    -- same local term, so on *every* square-free modulus the denominator
    -- contains at least `#divisors d / d`.  Thus the missing estimate is
    -- now precisely the classical truncated square-free harmonic sum,
    -- rather than any endpoint or choice of lambdas.
    have chosen_size (k R d : ℕ) (hR : 1 ≤ R) :
        |BrunSupport.sgWeight (S k) R d| ≤ (R:ℝ) := by
      change |BrunSupport.sgWeight (BrunSupport.twinSieve k) R d| ≤ _
      exact BrunSupport.twin_sgWeight_abs_le k R d hR
    have chosen_error (k R : ℕ) (hR : 1 ≤ R) :
        (S k).errSum
          (BoundingSieve.lambdaSquared (BrunSupport.sgWeight (S k) R))
          ≤ (R:ℝ)^10 := by
      exact BrunSupport.twin_sg_err_crude k R hR
    have every_local (k d : ℕ) (hd : d ∣ (S k).prodPrimes) :
        (d.divisors.card : ℝ) / d ≤ (S k).selbergTerms d := by
      exact BrunSupport.twin_selbergTerms_divisors_lower k d hd
    refine ⟨10280000, ?_⟩
    intro k hk
    by_cases big : 200 ≤ k
    · let m := k / 100
      let R := 2^(2*m)
      have mp : 1 ≤ m := by dsimp [m]; omega
      have expcut : 2*m < k/4 := by dsimp [m]; omega
      have small : R < BrunSupport.cutoff k := by
        unfold R BrunSupport.cutoff
        exact Nat.pow_lt_pow_right (by decide) expcut
      have dl : (m:ℝ)^2 / 256 ≤ BrunSupport.sgDen (S k) R := by
        change (m:ℝ)^2 / 256 ≤ BrunSupport.sgDen (BrunSupport.twinSieve k) (2^(2*m))
        exact BrunSupport.sgDen_growth k m (by simpa [R] using small)
      have dp : 0 < (m:ℝ)^2 / 256 := by
        have : 0 < m := lt_of_lt_of_le (by decide) mp
        positivity
      have sift := chosen_sift k R (by
        dsimp [R]
        exact Nat.one_le_pow (2*m) 2 (by decide))
      have err := chosen_error k R (by
        dsimp [R]
        exact Nat.one_le_pow (2*m) 2 (by decide))
      have ct : (S k).totalMass = ((2:ℕ)^k:ℝ) := by
        dsimp [S, BrunSupport.twinSieve]
        exact Nat.cast_pow 2 k
      have step : (BrunSupport.coprimeValueCount k : ℝ) ≤
           (256:ℝ) * (2:ℝ)^k / (m:ℝ)^2 + (R:ℝ)^10 := by
        calc
          (BrunSupport.coprimeValueCount k : ℝ)
             ≤ (S k).totalMass / BrunSupport.sgDen (S k) R +
                 (S k).errSum (BoundingSieve.lambdaSquared
                    (BrunSupport.sgWeight (S k) R)) := sift
          _ ≤ ((2:ℕ)^k:ℝ) / ((m:ℝ)^2 / 256) + (R:ℝ)^10 := by
                apply add_le_add
                · rw [ct]
                  exact div_le_div_of_nonneg_left (by positivity) dp dl
                · exact err
          _ = (256:ℝ) * (2:ℝ)^k / (m:ℝ)^2 + (R:ℝ)^10 := by
                push_cast
                field_simp
      have mexp : m*m * R^10 ≤ 2^k := by
        calc
          m*m * R^10 ≤ (2^(2*m)) * R^10 := by
            gcongr
            calc
              m*m ≤ (2^m)*(2^m) := Nat.mul_le_mul (Nat.lt_two_pow_self.le) (Nat.lt_two_pow_self.le)
              _ = 2^(2*m) := by ring
          _ = 2^(22*m) := by simp [R, ← pow_mul]; ring
          _ ≤ 2^k := by
            exact pow_le_pow_right₀ (by decide) (by dsimp [m]; omega)
      have mexp' : m^2 * R^10 ≤ 2^k := by
        simpa [pow_two] using mexp
      have exer : (m:ℝ)^2 * (R:ℝ)^10 ≤ (2:ℝ)^k := by
        exact_mod_cast mexp' 
      have cr : (0:ℝ) < (m:ℝ)^2 := by
        have : 0 < m := lt_of_lt_of_le (by decide) mp
        positivity
      have cm : (m:ℝ)^2 * (BrunSupport.coprimeValueCount k:ℝ)
           ≤ 257 * (2:ℝ)^k := by
        calc
          (m:ℝ)^2 * (BrunSupport.coprimeValueCount k:ℝ)
            ≤ (m:ℝ)^2 * ((256:ℝ) * (2:ℝ)^k / (m:ℝ)^2 + (R:ℝ)^10) :=
                mul_le_mul_of_nonneg_left step (by positivity)
          _ ≤ 257 * (2:ℝ)^k := by
                calc
                  _ = 256 * (2:ℝ)^k + (m:ℝ)^2 * (R:ℝ)^10 := by field_simp
                  _ ≤ _ := by linarith
      have kr : k+1 ≤ 200*m := by dsimp [m]; omega
      have finalr : (((k+1)^2 * BrunSupport.coprimeValueCount k : ℕ) : ℝ)
           ≤ ((10280000 * 2^k : ℕ) : ℝ) := by
        push_cast
        have kk : (((k+1:ℕ):ℝ)^2) ≤ 40000 * (m:ℝ)^2 := by
          exact_mod_cast (show (k+1)^2 ≤ 40000 * m^2 by nlinarith)
        calc
          ((k:ℝ)+1)^2 * (BrunSupport.coprimeValueCount k : ℝ)
             ≤ (40000 * (m:ℝ)^2) * (BrunSupport.coprimeValueCount k : ℝ) := by
                 have kk' : ((k:ℝ)+1)^2 ≤ 40000 * (m:ℝ)^2 := by
                   simpa [Nat.cast_add, Nat.cast_one] using kk
                 exact mul_le_mul_of_nonneg_right kk'
                   (by exact_mod_cast (Nat.zero_le (BrunSupport.coprimeValueCount k)))
          _ ≤ 40000 * (257 * (2:ℝ)^k) := by nlinarith
          _ = (10280000:ℝ) * (2:ℝ)^k := by ring
      exact_mod_cast finalr
    · have kl : k < 200 := Nat.lt_of_not_ge big
      have cnt := BrunSupport.coprimeValueCount_le_pow k
      calc
        (k+1)^2 * BrunSupport.coprimeValueCount k ≤ (k+1)^2 * 2^k := Nat.mul_le_mul_left _ cnt
        _ ≤ 10280000 * 2^k := by
          apply Nat.mul_le_mul_right _
          nlinarith
  have selberg_tail : ∃ C : ℝ, 0 ≤ C ∧
      ∀ k, 4 ≤ k → (BrunSupport.coprimeValueCount k : ℝ)
          ≤ C * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2) := by
    rcases finite_selberg_sieve with ⟨A, hA⟩
    refine ⟨(A:ℝ), by exact_mod_cast (Nat.zero_le A), ?_⟩
    intro k hk
    have H := hA k hk
    have HR : ((((k+1:ℕ):ℝ)^2) *
          (BrunSupport.coprimeValueCount k : ℝ))
          ≤ (A:ℝ) * (2:ℝ)^k := by
      exact_mod_cast H
    have hp : 0 < (((k+1:ℕ):ℝ)^2) := by positivity
    apply (le_div_iff₀ hp).2
    nlinarith
  have selberg_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ k, (BrunSupport.coprimeValueCount k : ℝ)
          ≤ C * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2) := by
    rcases selberg_tail with ⟨C, hC, htail⟩
    refine ⟨max C 16, ?_⟩
    simpa using
      (BrunSupport.all_coprimeValue_bound_of_tail C hC htail)
  have upper_bound_sieve : ∃ C : ℝ, 0 ≤ C ∧
      ∀ k, (BrunSupport.survivorCount k : ℝ)
          ≤ C * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2) := by
    rcases selberg_bound with ⟨C, hC, hS⟩
    refine ⟨C, hC, ?_⟩
    intro k
    simpa [BrunSupport.survivorCount_eq_coprimeValueCount] using (hS k)
  have sieve : ∃ C : ℝ, 0 ≤ C ∧
      ∀ k, ((BrunSupport.blockSet P k).card : ℝ)
          ≤ C * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2) := by
    rcases upper_bound_sieve with ⟨C, hC, hU⟩
    refine ⟨C, hC, ?_⟩
    intro k
    calc
      ((BrunSupport.blockSet P k).card : ℝ)
          ≤ (BrunSupport.survivorCount k : ℝ) := by
            have sub : BrunSupport.blockSet P k ⊆
                (BrunSupport.block k).filter
                  (BrunSupport.Avoid (BrunSupport.cutoff k)) := by
              intro p hp
              have hp' := (BrunSupport.mem_blockSet.mp hp)
              refine Finset.mem_filter.mpr ⟨hp'.1, ?_⟩
              have hbase : 2^k ≤ p := (BrunSupport.mem_block.mp hp'.1).1
              have hbig : BrunSupport.cutoff k ≤ p :=
                le_trans (BrunSupport.cutoff_le_main k) hbase
              apply BrunSupport.avoid_of_twins_of_le hbig
              exact hp'.2
            exact_mod_cast (Finset.card_le_card sub)
      _ ≤ C * (2:ℝ)^k / (((k+1:ℕ):ℝ)^2) := hU k
  rcases sieve with ⟨C, hC, hcount⟩
  have hs := BrunSupport.summable_of_card_bound P f hf hz hle C hC hcount
  simpa [f] using hs
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
