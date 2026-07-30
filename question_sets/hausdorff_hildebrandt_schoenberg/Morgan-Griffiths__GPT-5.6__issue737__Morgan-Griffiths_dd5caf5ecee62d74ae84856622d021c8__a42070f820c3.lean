import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/hausdorff_hildebrandt_schoenberg_fd451ce1ab/Combin.lean

namespace HHSCombin
open scoped BigOperators
lemma flip_le {ι : Type*} (n k : ι → ℕ) : n - k ≤ n := by
  intro i; exact Nat.sub_le ..
lemma arr_flip_flip {ι : Type*} (n k : ι → ℕ) (h : k ≤ n) : n - (n - k) = k := by
  funext i
  specialize h i
  change k i ≤ n i at h
  change n i - (n i - k i) = k i
  omega
lemma flip_le_flip {ι : Type*} {n k j : ι → ℕ} (hk : k ≤ n) (hj : j ≤ n) :
 n - k ≤ n - j ↔ j ≤ k := by
 constructor
 · intro h i; specialize h i
   specialize hk i; specialize hj i
   change k i ≤ n i at hk
   change j i ≤ n i at hj
   change n i - k i ≤ n i - j i at h
   change j i ≤ k i
   omega
 · intro h i
   specialize h i
   have hki := hk i; have hji := hj i
   change k i ≤ n i at hki
   change j i ≤ n i at hji
   change j i ≤ k i at h
   change n i - k i ≤ n i - j i
   omega
lemma sum_flip {ι : Type*} [Fintype ι] [DecidableEq ι]
  {R : Type*} [AddCommMonoid R] (n : ι → ℕ) (f : (ι → ℕ) → R) :
 ∑ k ∈ Finset.Iic n, f k = ∑ k ∈ Finset.Iic n, f (n-k) := by
 classical
 -- use sum_bij
 refine Finset.sum_bij (fun k hk => n-k) ?_ ?_ ?_ ?_
 · intro k hk
   exact Finset.mem_Iic.mpr (flip_le n k)
 · intro a ha b hb hab
   have ha' : a ≤ n := Finset.mem_Iic.mp ha
   have hb' : b ≤ n := Finset.mem_Iic.mp hb
   have := congrArg (fun t => n - t) hab
   simpa [arr_flip_flip n a ha', arr_flip_flip n b hb'] using this
 · intro b hb
   refine ⟨n-b, Finset.mem_Iic.mpr (flip_le n b), ?_⟩
   exact arr_flip_flip n b (Finset.mem_Iic.mp hb)
 · intro a ha
   congr 1
   exact (arr_flip_flip n a (Finset.mem_Iic.mp ha)).symm
noncomputable section
attribute [local instance] Classical.propDecidable
lemma sum_sub_Iic {ι : Type*} [Fintype ι] [DecidableEq ι]
 {R : Type*} [AddCommMonoid R]
 (n k : ι → ℕ) (hk : k ≤ n) (f : (ι→ℕ)→R) :
  ∑ j ∈ Finset.Iic k, f j = ∑ j ∈ Finset.Iic n, if j ≤ k then f j else 0 := by
 classical
 rw [← Finset.sum_filter]
 congr 1
 ext j
 simp only [Finset.mem_filter, Finset.mem_Iic]
 constructor
 · intro hj; exact ⟨le_trans hj hk, hj⟩
 · intro ⟨hj1, hj2⟩; exact hj2
lemma sum_triangle_flip {ι : Type*} [Fintype ι] [DecidableEq ι]
 {R : Type*} [AddCommMonoid R]
 (n : ι → ℕ) (H : (ι→ℕ)→(ι→ℕ)→R) :
 ∑ k ∈ Finset.Iic n, ∑ j ∈ Finset.Iic k, H k j =
 ∑ l ∈ Finset.Iic n, ∑ t ∈ Finset.Iic l, H (n-t) (n-l) := by
 classical
 calc
 _ = ∑ k ∈ Finset.Iic n, ∑ j ∈ Finset.Iic n, if j ≤ k then H k j else 0 := by
   apply Finset.sum_congr rfl
   intro k hk
   exact sum_sub_Iic n k (Finset.mem_Iic.mp hk) (H k)
 _ = ∑ t ∈ Finset.Iic n, ∑ j ∈ Finset.Iic n,
      if j ≤ n - t then H (n-t) j else 0 := by
   rw [sum_flip n]
 _ = ∑ t ∈ Finset.Iic n, ∑ l ∈ Finset.Iic n,
      if n-l ≤ n - t then H (n-t) (n-l) else 0 := by
   apply Finset.sum_congr rfl; intro t ht
   rw [sum_flip n]
 _ = ∑ t ∈ Finset.Iic n, ∑ l ∈ Finset.Iic n,
      if t ≤ l then H (n-t) (n-l) else 0 := by
   apply Finset.sum_congr rfl; intro t ht
   apply Finset.sum_congr rfl; intro l hl
   have ht' : t ≤ n := Finset.mem_Iic.mp ht
   have hl' : l ≤ n := Finset.mem_Iic.mp hl
   have iff : n-l ≤ n-t ↔ t ≤ l := flip_le_flip hl' ht'
   by_cases h : t ≤ l <;> simp [h, iff]
 _ = ∑ l ∈ Finset.Iic n, ∑ t ∈ Finset.Iic l, H (n-t) (n-l) := by
   -- commute rectangular sums
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro l hl
   rw [sum_sub_Iic n l (Finset.mem_Iic.mp hl) (fun t => H (n-t) (n-l))]
lemma choose_triangle (N L T : ℕ) (hT : T ≤ L) (hL : L ≤ N) :
 N.choose (N-T) * (N-T).choose (N-L) = N.choose L * L.choose T := by
 have htn : T ≤ N := le_trans hT hL
 rw [Nat.choose_symm htn]
 have heq : N - L = (N-T) - (L-T) := by omega
 rw [heq, Nat.choose_symm (by omega : L-T ≤ N-T)]
 exact Nat.choose_mul hT |>.symm
-- sign finite difference basic vanish

lemma alternating_choose (L : ℕ) :
 (∑ t ∈ Finset.Iic L, (-1:ℝ)^(L-t) * (Nat.choose L t : ℝ)) =
   if L = 0 then 1 else 0 := by
  classical
  have hr : (Finset.Iic L : Finset ℕ) = Finset.range (L+1) := by
    ext t; simp
  rw [hr]
  by_cases h : L = 0
  · subst L; simp
  · have hp : ((1:ℝ) + (-1)) ^ L = 0 := by simp [h]
    rw [add_pow] at hp
    rw [if_neg h]
    -- the binomial theorem already carries the same summands in reversed
    -- monomial order
    convert hp using 1 <;>
      · apply Finset.sum_congr rfl
        intro t ht
        simp

end

end HHSCombin

-- END INLINED FILE: Mathlib/Support/hausdorff_hildebrandt_schoenberg_fd451ce1ab/Combin.lean

-- BEGIN INLINED FILE: Mathlib/Support/hausdorff_hildebrandt_schoenberg_fd451ce1ab/BernsteinAux.lean

namespace HHSAux
open scoped BigOperators
open Filter Topology

lemma iic_nat (n:ℕ) : (Finset.Iic n : Finset ℕ) = Finset.range (n+1) := by
  ext t; simp

noncomputable def dsum (L M : ℕ) : ℝ :=
  ∑ t ∈ Finset.Iic L, (-1:ℝ)^(L-t) * (Nat.choose L t : ℝ) * (t:ℝ)^M

-- recursion for the forward differences
lemma dsum_succ (L M : ℕ) :
    dsum (L+1) M = ∑ r ∈ Finset.range M, (Nat.choose M r : ℝ) * dsum L r := by
  classical
  unfold dsum
  rw [iic_nat (L+1), iic_nat L]
  -- names: range (L+2) split t=0 and t=u+1
  -- first rewrite the left sum by `sum_range_succ` at the *front* using an auxiliary identity
  have hsplit (F : ℕ → ℝ) :
    (∑ t ∈ Finset.range (L+1+1),
       (-1:ℝ)^((L+1)-t) * (Nat.choose (L+1) t : ℝ) * F t) =
      (∑ u ∈ Finset.range (L+1),
        (-1:ℝ)^(L-u) * (Nat.choose L u : ℝ) * (F (u+1) - F u)) := by
    -- peel off `0` on the left; the other terms use Pascal
    rw [Finset.sum_range_succ']
    let A : ℕ → ℝ := fun u => (-1:ℝ)^(L-u) * (Nat.choose L u : ℝ)
    let B : ℕ → ℝ := fun u => (-1:ℝ)^(L-u) * (Nat.choose L (u+1) : ℝ) * F (u+1)
    have hterm (u : ℕ) (hu : u ∈ Finset.range (L+1)) :
        (-1:ℝ)^((L+1)-(u+1)) * (Nat.choose (L+1) (u+1) : ℝ) * F (u+1)
          = A u * F (u+1) + B u := by
      have hle : u ≤ L := by simpa using (Finset.mem_range.mp hu)
      have hs : L+1-(u+1) = L-u := by omega
      have hc : Nat.choose (L+1) (u+1) = Nat.choose L u + Nat.choose L (u+1) := by
        simpa [Nat.succ_eq_add_one] using (Nat.choose_succ_succ L u)
      dsimp [A, B]
      rw [hs, hc, Nat.cast_add]
      ring
    have hdecomp :
       (∑ u ∈ Finset.range (L+1),
          (-1:ℝ)^((L+1)-(u+1)) * (Nat.choose (L+1) (u+1) : ℝ) * F (u+1)) =
       (∑ u ∈ Finset.range (L+1), A u * F (u+1)) +
       (∑ u ∈ Finset.range (L+1), B u) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      exact hterm u hu
    rw [hdecomp]
    have hB_last : B L = 0 := by
      dsimp [B]
      simp
    have hB : (∑ u ∈ Finset.range (L+1), B u)
          = - (∑ u ∈ Finset.range L, A (u+1) * F (u+1)) := by
      rw [Finset.sum_range_succ, hB_last, add_zero]
      -- pointwise change the sign
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      have hu' : u < L := Finset.mem_range.mp hu
      have hrel : L-u = (L-(u+1))+1 := by omega
      have hc : (-( A (u+1) * F (u+1))) = B u := by
        dsimp [A, B]
        have hs : L - (u+1) = L - u - 1 := by omega
        rw [hrel, pow_succ]
        ring
      exact hc.symm
    rw [hB]
    have hz :
        (-1:ℝ)^((L+1)-0) * (Nat.choose (L+1) 0 : ℝ) * F 0
          = - (A 0 * F 0) := by
      dsimp [A]
      simp [pow_succ]
    rw [hz]
    -- split the missing zero term in the negative sum
    have hshift : (∑ u ∈ Finset.range (L+1), A u * F u) =
        (∑ u ∈ Finset.range L, A (u+1) * F (u+1)) + A 0 * F 0 := by
      rw [Finset.sum_range_succ']
    have hminus :
        - (∑ u ∈ Finset.range L, A (u+1) * F (u+1)) - A 0 * F 0 =
        - (∑ u ∈ Finset.range (L+1), A u * F u) := by
      rw [hshift]
      ring
    have hrhs :
       (∑ u ∈ Finset.range (L+1),
          (-1:ℝ)^(L-u) * (Nat.choose L u : ℝ) * (F (u+1) - F u)) =
       (∑ u ∈ Finset.range (L+1), A u * F (u+1)) -
       (∑ u ∈ Finset.range (L+1), A u * F u) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      dsimp [A]
      ring
    rw [hrhs]
    rw [hshift]
    ring
  rw [hsplit (fun t => (t:ℝ)^M)]
  -- expand F(u+1)-F u by the binomial theorem = sum r<M choose M r u^r
  -- commute finite sums
  have hp (u:ℕ) : (((u+1:ℕ):ℝ)^M - (u:ℝ)^M) =
       ∑ r ∈ Finset.range M, (Nat.choose M r : ℝ) * (u:ℝ)^r := by
    have h := add_pow (u:ℝ) (1:ℝ) M
    rw [Finset.sum_range_succ] at h
    norm_num at h
    have hsum :
       (∑ r ∈ Finset.range M, (u:ℝ)^r * (Nat.choose M r : ℝ)) =
       ∑ r ∈ Finset.range M, (Nat.choose M r : ℝ) * (u:ℝ)^r := by
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [hsum] at h
    have hc : ((u+1:ℕ):ℝ) = (u:ℝ)+1 := by norm_num
    rw [hc]
    nlinarith [h]

  simp_rw [hp]
  -- distribute sums: outer u, inner r
  simp_rw [Finset.mul_sum]
  -- note big sum notation nested range with binder includes ∑ r∈range M
  -- expand products: coefficient choose M r factors
  -- aim sum over r outside
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro u hu
  ring

end HHSAux

namespace HHSAux
open scoped BigOperators
open Filter Topology
lemma dsum_zero (M : ℕ) : dsum 0 M = (0:ℝ)^M := by
  unfold dsum
  rw [iic_nat 0]
  simp

lemma dsum_eq_zero_of_lt : ∀ (L M : ℕ), M < L → dsum L M = 0 := by
  intro L
  induction L with
  | zero =>
      intro M h
      omega
  | succ L ih =>
      intro M h
      have hML : M ≤ L := by omega
      rw [show L+1 = L+1 by rfl, dsum_succ]
      apply Finset.sum_eq_zero
      intro r hr
      have hr' : r < M := Finset.mem_range.mp hr
      have hz : dsum L r = 0 := ih r (by omega)
      rw [hz]
      simp

lemma dsum_self : ∀ L : ℕ, dsum L L = (Nat.factorial L : ℝ) := by
  intro L
  induction L with
  | zero => simpa using (dsum_zero 0)
  | succ L ih =>
    rw [dsum_succ]
    rw [Finset.sum_range_succ]
    have hz : (∑ r ∈ Finset.range L, (Nat.choose (L+1) r : ℝ) * dsum L r) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hr' : r < L := Finset.mem_range.mp hr
      rw [dsum_eq_zero_of_lt L r hr']
      simp
    rw [hz, zero_add, ih]
    rw [Nat.choose_succ_self_right]
    simp [Nat.factorial_succ]

end HHSAux

namespace HHSAux
open scoped BigOperators
open Filter Topology
lemma dsum_div (L M : ℕ) (Q : ℝ) :
  (∑ t ∈ Finset.Iic L, (-1:ℝ)^(L-t) * (Nat.choose L t : ℝ) *
      (((t:ℕ):ℝ)/Q)^M) = dsum L M / Q^M := by
  unfold dsum
  simp_rw [div_pow]
  calc
    _ = ∑ t ∈ Finset.Iic L,
          ((-1:ℝ)^(L-t) * (Nat.choose L t : ℝ) * (t:ℝ)^M) / Q^M := by
            apply Finset.sum_congr rfl
            intro t ht
            ring
    _ = _ := (Finset.sum_div _ _ _).symm
end HHSAux

namespace HHSAux
open scoped BigOperators
open Filter Topology
lemma tendsto_sub_ratio (c : ℕ) :
  Tendsto (fun N : ℕ => (((N+1-c:ℕ):ℕ):ℝ) / (N+1:ℕ)) atTop (𝓝 (1:ℝ)) := by
  have hzero : Tendsto (fun N : ℕ => (c:ℝ) / (N+1:ℕ)) atTop (𝓝 (0:ℝ)) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (c:ℝ)).comp
       (Filter.tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  have hlim : Tendsto (fun N : ℕ => (1:ℝ) - (c:ℝ)/(N+1:ℕ)) atTop (𝓝 (1:ℝ)) := by
    convert tendsto_const_nhds.sub hzero using 1 <;> simp
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop c] with N hN
  have hle : c ≤ N+1 := by omega
  rw [Nat.cast_sub hle]
  push_cast
  have hpos : (0:ℝ) < (N:ℝ) + 1 := by positivity
  field_simp

lemma choose_ratio_formula (q L : ℕ) :
   (Nat.choose q L : ℝ) / (q:ℝ)^L =
     (∏ i ∈ Finset.range L, (((q-i:ℕ):ℕ):ℝ)/(q:ℝ)) /
        (Nat.factorial L : ℝ) := by
  have hdesc : (q.descFactorial L : ℝ) =
      ∏ i ∈ Finset.range L, (((q-i:ℕ):ℕ):ℝ) := by
    rw [Nat.descFactorial_eq_prod_range]
    simp
  have hdf : (q.descFactorial L : ℝ) =
       (Nat.factorial L : ℝ) * (Nat.choose q L : ℝ) := by
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose q L)
  have hf : (Nat.factorial L : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero L)
  have hqprod :
       (∏ i ∈ Finset.range L, (((q-i:ℕ):ℕ):ℝ)/(q:ℝ)) =
       (q.descFactorial L : ℝ) / (q:ℝ)^L := by
    rw [Finset.prod_div_distrib]
    simp [Finset.prod_const, hdesc]
  rw [hqprod, hdf]
  field_simp

lemma tendsto_choose_ratio (L : ℕ) :
  Tendsto (fun N : ℕ => (Nat.choose (N+1) L : ℝ) /
       ((N+1:ℕ):ℝ)^L) atTop (𝓝 ((1:ℝ) / (Nat.factorial L : ℝ))) := by
  have hp : Tendsto
      (fun N : ℕ => ∏ i ∈ Finset.range L,
          (((N+1-i:ℕ):ℕ):ℝ)/((N+1:ℕ):ℝ)) atTop (𝓝 (1:ℝ)) := by
    have hh := tendsto_finset_prod (Finset.range L)
       (f := fun i (N:ℕ) => (((N+1-i:ℕ):ℕ):ℝ)/((N+1:ℕ):ℝ))
       (a := fun _ => (1:ℝ))
       (fun i hi => tendsto_sub_ratio i)
    simpa using hh
  have hdiv := hp.div_const (Nat.factorial L : ℝ)
  apply hdiv.congr'
  exact Filter.Eventually.of_forall (fun N => (choose_ratio_formula (N+1) L).symm)

-- the coefficient for one coordinate, before products
noncomputable def coeff (q L M : ℕ) : ℝ :=
     (Nat.choose q L : ℝ) * dsum L M / ((q:ℕ):ℝ)^M

lemma tendsto_coeff_of_le {L M : ℕ} (hLM : L ≤ M) :
  Tendsto (fun N : ℕ => coeff (N+1) L M) atTop
     (𝓝 (if L = M then (1:ℝ) else 0)) := by
  classical
  have hfac : (Nat.factorial L : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero L)
  have hratio := tendsto_choose_ratio L
  by_cases h : L = M
  · subst M
    simp [coeff, dsum_self]
    -- show tendsto product ratio times factorial
    have hh := hratio.mul_const (Nat.factorial L : ℝ)
    convert hh using 1 <;> simp [hfac]
    · funext N
      ring
  · have hlt : L < M := lt_of_le_of_ne hLM h
    let r : ℕ := M - L
    have hr : 0 < r := by dsimp [r]; omega
    have hinv : Tendsto (fun N : ℕ => ((1:ℝ)/((N+1:ℕ):ℝ))^r)
         atTop (𝓝 (0:ℝ)) := by
      have hbase : Tendsto (fun N : ℕ => (1:ℝ)/((N+1:ℕ):ℝ))
          atTop (𝓝 (0:ℝ)) := by
        simpa [Nat.cast_add, Nat.cast_one] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
      convert hbase.pow r using 1 <;> simp [hr.ne']
    have hmul := (hratio.mul_const (dsum L M)).mul hinv
    -- limit is zero; rewrite functions
    have hev : (fun N : ℕ => coeff (N+1) L M) =ᶠ[atTop]
        (fun N : ℕ =>
          (((Nat.choose (N+1) L : ℝ) / (((N+1:ℕ):ℝ)^L)) * dsum L M) *
             ((1:ℝ)/((N+1:ℕ):ℝ))^r) := by
       filter_upwards with N
       dsimp [coeff, r]
       have hpos : (0:ℝ) < ((N+1:ℕ):ℝ) := by positivity
       have hpow : M = L + (M-L) := by omega
       rw [hpow, pow_add]
       rw [Nat.add_sub_cancel_left]
       rw [one_div, inv_pow]
       field_simp
    have hmul' : Tendsto
         (fun N : ℕ => ((((Nat.choose (N+1) L : ℝ) / (((N+1:ℕ):ℝ)^L)) * dsum L M) *
             ((1:ℝ)/((N+1:ℕ):ℝ))^r)) atTop (𝓝 (0:ℝ)) := by
       convert hmul using 1 <;> simp
    have hlim : Tendsto (fun N : ℕ => coeff (N+1) L M) atTop (𝓝 (0:ℝ)) :=
       hmul'.congr' hev.symm
    simpa [h] using hlim

lemma coeff_zero_of_lt {q L M : ℕ} (h : M < L) : coeff q L M = 0 := by
   simp [coeff, dsum_eq_zero_of_lt L M h]

end HHSAux

namespace HHSAux
open scoped BigOperators
open Filter Topology
lemma iic_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
 (n : ι → ℕ) : Finset.Iic n = Fintype.piFinset (fun i => Finset.Iic (n i)) := by
  ext f; simp [Finset.mem_Iic, Fintype.mem_piFinset, Pi.le_def]

lemma triangle_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
   (a : (ι → ℕ) → ℝ) (m : ι → ℕ) (q : ℕ) :
 (∑ k ∈ Finset.Iic (fun _ : ι => q),
    (((∏ i : ι, (q.choose (k i))) : ℕ) : ℝ) *
    (∑ j ∈ Finset.Iic k,
       (-1 : ℝ) ^ (∑ i, (k i - j i)) *
       (((∏ i : ι, ((k i).choose (j i))) : ℕ) : ℝ) *
       a ((fun _ : ι => q) - j)) *
    (∏ i : ι, (((q-k i : ℕ) : ℝ) / (q:ℕ)) ^ (m i))) =
    ∑ l ∈ Finset.Iic (fun _ : ι => q),
       a l * ∏ i : ι, coeff q (l i) (m i) := by
 classical
 let n : ι → ℕ := fun _ => q
 let H : (ι → ℕ) → (ι → ℕ) → ℝ := fun k j =>
     (((∏ i : ι, q.choose (k i)) : ℕ) : ℝ) *
       ((-1:ℝ)^(∑ i, (k i - j i)) *
        (((∏ i : ι, (k i).choose (j i)) : ℕ) : ℝ) * a (n-j)) *
       (∏ i : ι, (((q-k i:ℕ):ℝ)/(q:ℕ))^(m i))
 have expand :
   (∑ k ∈ Finset.Iic n,
    (((∏ i : ι, (q.choose (k i))) : ℕ) : ℝ) *
    (∑ j ∈ Finset.Iic k,
       (-1 : ℝ) ^ (∑ i, (k i - j i)) *
       (((∏ i : ι, ((k i).choose (j i))) : ℕ) : ℝ) *
       a (n - j)) *
    (∏ i : ι, (((q-k i : ℕ) : ℝ) / (q:ℕ)) ^ (m i)))
     = ∑ k ∈ Finset.Iic n, ∑ j ∈ Finset.Iic k, H k j := by
       apply Finset.sum_congr rfl
       intro k hk
       simp_rw [Finset.mul_sum, Finset.sum_mul]
       apply Finset.sum_congr rfl
       intro j hj
       dsimp [H]
 -- cast initial n
 change (∑ k ∈ Finset.Iic n,
    (((∏ i : ι, (q.choose (k i))) : ℕ) : ℝ) *
    (∑ j ∈ Finset.Iic k,
       (-1 : ℝ) ^ (∑ i, (k i - j i)) *
       (((∏ i : ι, ((k i).choose (j i))) : ℕ) : ℝ) *
       a (n - j)) *
    (∏ i : ι, (((q-k i : ℕ) : ℝ) / (q:ℕ)) ^ (m i))) = _
 rw [expand]
 rw [HHSCombin.sum_triangle_flip n H]
 -- now pointwise compute inner sum
 apply Finset.sum_congr rfl
 intro l hl
 have hl' : l ≤ n := Finset.mem_Iic.mp hl
 -- we prove the inner t sum factors by coordinates
 -- first simplify each term after substitution
 have hterm (t : ι → ℕ) (ht : t ∈ Finset.Iic l) :
    H (n-t) (n-l) =
      a l * ∏ i : ι,
        ((q.choose (l i) : ℝ) *
          ((-1:ℝ)^(l i - t i) * (Nat.choose (l i) (t i) : ℝ) *
              ((((t i : ℕ):ℝ)/(q:ℕ))^(m i)))) := by
    have ht' : t ≤ l := Finset.mem_Iic.mp ht
    have htn : t ≤ n := le_trans ht' hl'
    have choosei (i : ι) :
      (n i).choose ((n-t) i) * ((n-t) i).choose ((n-l) i) =
        (n i).choose (l i) * (l i).choose (t i) := by
          simpa using (HHSCombin.choose_triangle (n i) (l i) (t i) (ht' i) (hl' i))
    have sub1 : n - (n-l) = l := HHSCombin.arr_flip_flip n l hl'
    have subt (i:ι) : q - (n-t) i = t i := by
       change q - (q - t i) = t i
       exact Nat.sub_sub_self (htn i)
    have subs (i:ι) : (n-t) i - (n-l) i = l i - t i := by
       change q - t i - (q - l i) = l i - t i
       have htq : t i ≤ q := htn i
       have hlq : l i ≤ q := hl' i
       exact (by omega)
    dsimp [H]
    rw [sub1]
    -- split sign product and casts and use choosei under products
    rw [← Finset.prod_pow_eq_pow_sum]
    have subs' (i:ι) : n i - t i - (n i - l i) = l i - t i := by
      simpa using subs i
    simp_rw [subs']
    -- cast naturals products to real
    push_cast
    -- combine all products
    have subt' (i:ι) : q - (n i - t i) = t i := by simpa using subt i
    simp_rw [subt']
    -- combine the two binomial coefficients in each coordinate
    have choosei' (i:ι) :
        (q.choose (n i - t i) : ℝ) * ((n i - t i).choose (n i - l i) : ℝ) =
          (q.choose (l i) : ℝ) * ((l i).choose (t i) : ℝ) := by
      exact_mod_cast (choosei i)
    have hp1 :
       (∏ i : ι, (q.choose (n i - t i) : ℝ)) *
         (∏ i : ι, (-1:ℝ)^(l i - t i) *
                         ((n i - t i).choose (n i-l i) : ℝ)) =
       ∏ i : ι, (-1:ℝ)^(l i-t i) *
              ((q.choose (l i) : ℝ) * ((l i).choose (t i) : ℝ)) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        calc
         _ = (-1:ℝ)^(l i - t i) *
               ((q.choose (n i-t i) : ℝ) *
                 ((n i-t i).choose (n i-l i) : ℝ)) := by ring
         _ = _ := by rw [choosei' i]
    -- make the same rewriting of the two products visible
    simp_rw [← Finset.prod_mul_distrib]
    calc
      _ = a l *
           (((∏ i : ι, (q.choose (n i-t i) : ℝ)) *
               (∏ i : ι, (-1:ℝ)^(l i-t i) *
                         ((n i-t i).choose (n i-l i) : ℝ))) *
                 (∏ i : ι, (((t i:ℕ):ℝ)/(q:ℕ))^(m i))) := by ring
      _ = a l * ((∏ i : ι, (-1:ℝ)^(l i-t i) *
               ((q.choose (l i) : ℝ) * ((l i).choose (t i) : ℝ))) *
                 (∏ i : ι, (((t i:ℕ):ℝ)/(q:ℕ))^(m i))) := by rw [hp1]
      _ = _ := by
        congr 1
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        ring

 -- rewrite inner sum with hterm
 calc
  (∑ t ∈ Finset.Iic l, H (n-t) (n-l)) =
     ∑ t ∈ Finset.Iic l, a l * ∏ i : ι,
        ((q.choose (l i) : ℝ) *
          ((-1:ℝ)^(l i - t i) * (Nat.choose (l i) (t i) : ℝ) *
              ((((t i : ℕ):ℝ)/(q:ℕ))^(m i)))) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hterm t ht
  _ = a l * ∏ i : ι, coeff q (l i) (m i) := by
    -- pull constants choose out; then factor the coordinate sums
    rw [← Finset.mul_sum]
    rw [iic_pi l]
    -- interchange independent coordinates
    rw [← Finset.prod_univ_sum (fun i : ι => Finset.Iic (l i))
       (fun i (t:ℕ) => (q.choose (l i) : ℝ) *
          ((-1:ℝ)^(l i-t) * (Nat.choose (l i) t : ℝ) *
            ((((t:ℕ):ℝ)/(q:ℕ))^(m i))))]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    -- identify dsum_div
    dsimp [coeff]
    -- constant choose out
    rw [← Finset.mul_sum]
    rw [dsum_div]
    ring
end HHSAux

namespace HHSAux
open scoped BigOperators
open Filter Topology
lemma sum_restrict_box {ι : Type*} [Fintype ι] [DecidableEq ι]
  (a : (ι → ℕ) → ℝ) (m : ι → ℕ) (q : ℕ) (hq : ∀ i, m i ≤ q) :
 (∑ l ∈ Finset.Iic (fun _ : ι => q), a l * ∏ i : ι, coeff q (l i) (m i)) =
 (∑ l ∈ Finset.Iic m, a l * ∏ i : ι, coeff q (l i) (m i)) := by
 classical
 let n : ι → ℕ := fun _ => q
 have sub : Finset.Iic m ⊆ Finset.Iic n := by
   intro l hl
   have hle : l ≤ m := Finset.mem_Iic.mp hl
   exact Finset.mem_Iic.mpr (le_trans hle (fun i => hq i))
 symm
 apply Finset.sum_subset sub
 intro l hl hn
 have hnle : ¬ l ≤ m := by simpa using hn
 have hex : ∃ i, m i < l i := by
   simp [Pi.le_def] at hnle
   exact hnle
 obtain ⟨i, hi⟩ := hex
 have hz : coeff q (l i) (m i) = 0 := coeff_zero_of_lt hi
 have hprod : (∏ i : ι, coeff q (l i) (m i)) = 0 :=
   Finset.prod_eq_zero (Finset.mem_univ i) hz
 rw [hprod, mul_zero]

lemma tendsto_prod_coeff {ι : Type*} [Fintype ι] [DecidableEq ι]
   (l m : ι → ℕ) (hle : l ≤ m) :
 Tendsto (fun N : ℕ => ∏ i : ι, coeff (N+1) (l i) (m i)) atTop
    (𝓝 (if l = m then (1:ℝ) else 0)) := by
 classical
 have hp := tendsto_finset_prod (Finset.univ : Finset ι)
   (f := fun i (N:ℕ) => coeff (N+1) (l i) (m i))
   (a := fun i => if l i = m i then (1:ℝ) else 0)
   (fun i hi => tendsto_coeff_of_le (hle i))
 have hval : (∏ i : ι, (if l i = m i then (1:ℝ) else 0)) =
      (if l = m then (1:ℝ) else 0) := by
   by_cases h : l = m
   · subst l; simp
   · have ex : ∃ i, l i ≠ m i := by
        by_contra hn
        push_neg at hn
        exact h (funext hn)
     obtain ⟨i, hi⟩ := ex
     rw [if_neg h]
     exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
 rw [hval] at hp
 exact hp

lemma fixed_sum_limit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : (ι → ℕ) → ℝ) (m : ι → ℕ) :
 Tendsto
   (fun N : ℕ => ∑ l ∈ Finset.Iic m,
           a l * ∏ i : ι, coeff (N+1) (l i) (m i)) atTop
       (𝓝 (a m)) := by
 classical
 let target : (ι → ℕ) → ℝ := fun l => a l * (if l = m then (1:ℝ) else 0)
 have hsum := tendsto_finset_sum (Finset.Iic m)
    (f := fun l (N:ℕ) => a l * ∏ i : ι, coeff (N+1) (l i) (m i))
    (a := target)
    (fun l hl => (tendsto_prod_coeff l m (Finset.mem_Iic.mp hl)).const_mul (a l))
 have val : (∑ l ∈ Finset.Iic m, target l) = a m := by
   have hm : m ∈ Finset.Iic m := Finset.mem_Iic.mpr (le_refl m)
   rw [Finset.sum_eq_single m]
   · simp [target]
   · intro b hb hne
     simp [target, hne]
   · intro hn
     exact (hn hm).elim
 rw [val] at hsum
 exact hsum

lemma triangle_limit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : (ι → ℕ) → ℝ) (m : ι → ℕ) :
 Tendsto
 (fun N : ℕ =>
 (∑ k ∈ Finset.Iic (fun _ : ι => N+1),
    (((∏ i : ι, ((N+1).choose (k i))) : ℕ) : ℝ) *
    (∑ j ∈ Finset.Iic k,
       (-1 : ℝ) ^ (∑ i, (k i - j i)) *
       (((∏ i : ι, ((k i).choose (j i))) : ℕ) : ℝ) *
       a ((fun _ : ι => N+1) - j)) *
    (∏ i : ι, (((N+1-k i : ℕ) : ℝ) / (N+1 : ℕ)) ^ (m i))))
 atTop (𝓝 (a m)) := by
 classical
 -- first rewrite to the triangular coefficient form
 have hf := fixed_sum_limit a m
 have hev :
   (fun N : ℕ => ∑ k ∈ Finset.Iic (fun _ : ι => N+1),
    (((∏ i : ι, ((N+1).choose (k i))) : ℕ) : ℝ) *
    (∑ j ∈ Finset.Iic k,
       (-1 : ℝ) ^ (∑ i, (k i - j i)) *
       (((∏ i : ι, ((k i).choose (j i))) : ℕ) : ℝ) *
       a ((fun _ : ι => N+1) - j)) *
    (∏ i : ι, (((N+1-k i : ℕ) : ℝ) / (N+1 : ℕ)) ^ (m i))) =ᶠ[atTop]
     (fun N : ℕ => ∑ l ∈ Finset.Iic m,
          a l * ∏ i : ι, coeff (N+1) (l i) (m i)) := by
    -- past a single bound every `m i` is below the box
    filter_upwards [Filter.eventually_ge_atTop (∑ i, m i)] with N hN
    rw [triangle_eq a m (N+1)]
    apply sum_restrict_box a m (N+1)
    intro i
    have hmle : m i ≤ ∑ i, m i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
 exact hf.congr' hev.symm
end HHSAux

-- END INLINED FILE: Mathlib/Support/hausdorff_hildebrandt_schoenberg_fd451ce1ab/BernsteinAux.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval
namespace Analysis

/-!
# The Hausdorff moment problem on the cube

`hausdorff_hildebrandt_schoenberg` is the Hausdorff–Hildebrandt–Schoenberg
theorem (1933): a multi-indexed real sequence is the moment sequence of a
signed bounded-variation Borel measure on the unit cube `Iᵈ = [0,1]ᵈ` iff it is
*Hausdorff bounded*. `hausdorff_positivity` is the Hausdorff positivity
criterion (1921): it comes from a *positive* finite measure iff it is completely
monotone (all iterated backward differences nonnegative).

A signed bounded-variation measure is encoded by its Jordan decomposition (a
difference of two finite positive measures); the moment integrals are taken over
the cube, so only the restriction to `Iᵈ` matters; the iterated backward
difference `Δᵏ` is given in closed form (the `ℕ`-subtraction `n − j` is genuine
in the `k ≤ n` regime the criteria use).

Mathlib has `SignedMeasure`, Jordan decomposition, finite measures, and set
integrals — enough to *state* the theorem — but no moment-problem machinery
(no Hausdorff/Hamburger/Stieltjes moment problem, no completely-monotone
sequences). The helper definitions below (`cube`, `monomial`, `momentOf`,
`IsMomentConfiguration`, `multiChoose`, `diff`, `HausdorffBounded`,
`IsPositiveMomentConfiguration`) are trusted (non-holes).

These are category-(b) candidates from §115 of the Knill survey
(`sections/115-moments.md`).
-/

open MeasureTheory
open scoped BigOperators NNReal

/-- The closed unit cube `Iᵈ = [0,1]ᵈ ⊆ ℝᵈ`. -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The monomial `xⁿ = ∏ᵢ xᵢ^{nᵢ}` indexed by a multi-index `n ∈ ℕᵈ`. -/
def monomial {d : ℕ} (n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := ∏ i, (x i) ^ (n i)

/-- The `n`-th moment `∫_{Iᵈ} xⁿ dμ` of a (positive) measure `μ`, integrated
over the cube. -/
noncomputable def momentOf {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (n : Fin d → ℕ) : ℝ :=
  ∫ x in cube d, monomial n x ∂μ

/-- `a` is a **moment configuration** of a signed (bounded-variation) measure on
the cube: there are finite positive measures `μ, ν` with
`aₙ = ∫ xⁿ dμ − ∫ xⁿ dν` for all `n` (the Jordan decomposition of the realizing
signed measure). -/
def IsMomentConfiguration {d : ℕ} (a : (Fin d → ℕ) → ℝ) : Prop :=
  ∃ μ ν : Measure (EuclideanSpace ℝ (Fin d)), IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧
    ∀ n, a n = momentOf μ n - momentOf ν n

/-- The multi-index binomial coefficient `C(n,k) = ∏ᵢ C(nᵢ, kᵢ)`. -/
def multiChoose {d : ℕ} (n k : Fin d → ℕ) : ℕ := ∏ i, (n i).choose (k i)

/-- The iterated **backward** partial difference `(Δᵏa)ₙ`, in closed form
`∑_{0 ≤ j ≤ k} (−1)^{|k−j|} C(k,j) a_{n−j}` — the iterate of
`(Δᵢa)ₙ = a_{n−eᵢ} − aₙ`. The `ℕ`-subtraction `n − j` is genuine whenever
`k ≤ n` (the regime used below). -/
noncomputable def diff {d : ℕ} (a : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) : ℝ :=
  ∑ j ∈ Finset.Iic k,
    (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * a (n - j)

/-- The moments `a` are **Hausdorff bounded**: there is `C` with
`∑_{0 ≤ k ≤ n} |C(n,k) · (Δᵏa)ₙ| ≤ C` for every `n`. -/
def HausdorffBounded {d : ℕ} (a : (Fin d → ℕ) → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : Fin d → ℕ,
    ∑ k ∈ Finset.Iic n, |(multiChoose n k : ℝ) * diff a k n| ≤ C



end Analysis
end LeanEval

open LeanEval.Analysis
open MeasureTheory
open scoped BigOperators NNReal
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
namespace LeanEval.Analysis

lemma Iic_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
 (n : ι → ℕ) : Finset.Iic n = Fintype.piFinset (fun i => Finset.Iic (n i)) := by
  ext f
  simp [Finset.mem_Iic, Fintype.mem_piFinset, Pi.le_def]

/-- The (nonnegative) Bernstein kernel, without its binomial coefficient. -/
noncomputable def bkernel {d : ℕ} (n k : Fin d → ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, (x i) ^ (n i - k i) * (1 - x i) ^ (k i)

lemma isClosed_cube (d : ℕ) : IsClosed (cube d) := by
  change IsClosed {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ Set.Icc (0:ℝ) 1}
  rw [show {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ Set.Icc (0:ℝ) 1} =
      ⋂ i, (fun x : EuclideanSpace ℝ (Fin d) => x i) ⁻¹' (Set.Icc 0 1) by ext x; simp]
  exact isClosed_iInter (fun i => isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i))

lemma isCompact_cube (d : ℕ) : IsCompact (cube d) := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_cube d)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Real.sqrt d, ?_⟩
  intro x hx
  have hcoord : ∀ i : Fin d, |x i| ≤ 1 := by
    intro i
    have hi := hx i
    exact (abs_le.2 ⟨(by linarith [hi.1]), hi.2⟩)
  have hnormsq : ‖x‖ ^ (2:ℕ) ≤ (d:ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    have h : ∀ i : Fin d, x i ^ (2:ℕ) ≤ (1:ℝ) := by
      intro i
      nlinarith [abs_nonneg (x i), hcoord i, sq_abs (x i)]
    simpa using (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun i _ => h i))
  have hd : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
  nlinarith [Real.sq_sqrt hd, Real.sqrt_nonneg (d:ℝ), norm_nonneg x]

lemma measurableSet_cube (d : ℕ) : MeasurableSet (cube d) :=
  (isClosed_cube d).measurableSet

lemma continuous_monomial {d : ℕ} (n : Fin d → ℕ) :
    Continuous (monomial n) := by
  unfold monomial
  fun_prop

lemma continuous_bkernel {d : ℕ} (n k : Fin d → ℕ) :
    Continuous (bkernel n k) := by
  unfold bkernel
  fun_prop

lemma integrableOn_monomial {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (n : Fin d → ℕ) :
    IntegrableOn (monomial n) (cube d) μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => lt_of_le_of_lt (measure_mono (Set.subset_univ _)) IsFiniteMeasure.measure_univ_lt_top⟩
  exact (continuous_monomial n).continuousOn.integrableOn_compact (isCompact_cube d)

lemma integrableOn_bkernel {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (n k : Fin d → ℕ) :
    IntegrableOn (bkernel n k) (cube d) μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => lt_of_le_of_lt (measure_mono (Set.subset_univ _)) IsFiniteMeasure.measure_univ_lt_top⟩
  exact (continuous_bkernel n k).continuousOn.integrableOn_compact (isCompact_cube d)


lemma multiChoose_cast {d : ℕ} (k j : Fin d → ℕ) :
    (multiChoose k j : ℝ) = ∏ i, (Nat.choose (k i) (j i) : ℝ) := by
  unfold multiChoose
  simp

lemma summand_product {d : ℕ} (n k j : Fin d → ℕ)
    (x : EuclideanSpace ℝ (Fin d)) :
    (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * monomial (n-j) x =
      ∏ i, ((-1:ℝ) ^ (k i - j i) * (Nat.choose (k i) (j i) : ℝ) *
        (x i) ^ (n i - j i)) := by
  unfold monomial
  have hn : (n - j) = fun i => n i - j i := rfl
  -- all three factors split coordinatewise
  rw [multiChoose_cast]
  rw [← Finset.prod_pow_eq_pow_sum]
  -- combine the three products
  simp_rw [hn]
  -- simp for pointwise evaluation
  change (∏ i : Fin d, (-1:ℝ) ^ (k i - j i)) *
        (∏ i : Fin d, (Nat.choose (k i) (j i) : ℝ)) *
        (∏ i : Fin d, (x i) ^ (n i - j i)) = _
  simp_rw [← Finset.prod_mul_distrib]

lemma one_dim_diff_sum (x : ℝ) (N K : ℕ) (hK : K ≤ N) :
    ∑ J ∈ Finset.Iic K,
       ((-1:ℝ) ^ (K-J) * (Nat.choose K J : ℝ) * x ^ (N-J)) =
       x^(N-K) * (1-x)^K := by
  -- pull out `x^(N-K)` and use `(1-x)^K`
  have hNJ (J : ℕ) (hJ : J ≤ K) : N - J = (N-K) + (K-J) := by omega
  have hxpow (J : ℕ) (hJ : J ≤ K) :
      x ^ (N-J) = x^(N-K) * x^(K-J) := by
        rw [hNJ J hJ, pow_add]
  calc
    _ = ∑ J ∈ Finset.Iic K, x^(N-K) *
          ((-1:ℝ)^(K-J) * (Nat.choose K J : ℝ) * x^(K-J)) := by
          apply Finset.sum_congr rfl
          intro J hJm
          have hJ : J ≤ K := Finset.mem_Iic.mp hJm
          rw [hxpow J hJ]
          ring
    _ = x^(N-K) * ∑ J ∈ Finset.Iic K,
          ((-1:ℝ)^(K-J) * (Nat.choose K J : ℝ) * x^(K-J)) := by
          rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      have hr : (Finset.Iic K : Finset ℕ) = Finset.range (K+1) := by
        ext t; simp
      rw [hr]
      -- binomial expansion of `1 + (-x)`
      conv_rhs => rw [show (1-x:ℝ) = 1 + (-x) by ring, add_pow]
      apply Finset.sum_congr rfl
      intro J hJ
      -- `1^J = 1` and `(-x)^m = (-1)^m * x^m`
      rw [neg_pow]
      simp
      ring


lemma diff_monomial {d : ℕ} (n k : Fin d → ℕ) (hk : k ≤ n)
    (x : EuclideanSpace ℝ (Fin d)) :
    diff (fun m => monomial m x) k n = bkernel n k x := by
  unfold diff bkernel
  -- the large sum factors into a product of one dimensional binomial sums
  simp_rw [summand_product n k]
  rw [Iic_pi]
  change
    (∑ j ∈ Fintype.piFinset (fun i : Fin d => Finset.Iic (k i)),
       ∏ i, ((-1:ℝ)^(k i - j i) * (Nat.choose (k i) (j i) : ℝ) *
             (x i)^(n i - j i))) = _
  rw [← Finset.prod_univ_sum (fun i : Fin d => Finset.Iic (k i))
       (fun i (j : ℕ) => ((-1:ℝ)^(k i - j) * (Nat.choose (k i) j : ℝ) *
             (x i)^(n i - j)))]
  apply Finset.prod_congr rfl
  intro i hi
  exact one_dim_diff_sum (x i) (n i) (k i) (hk i)


lemma diff_moment_pos {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (n k : Fin d → ℕ) (hk : k ≤ n) :
    diff (fun m => momentOf μ m) k n =
       ∫ x in cube d, bkernel n k x ∂μ := by
  classical
  unfold diff momentOf
  -- move the finite sum through the integral
  have h_int (j : Fin d → ℕ) :
      IntegrableOn (fun x : EuclideanSpace ℝ (Fin d) =>
        (-1:ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * monomial (n-j) x)
        (cube d) μ := by
    have h := integrableOn_monomial μ (n-j)
    -- both scalar factors can be combined
    change Integrable _ (μ.restrict (cube d))
    change Integrable _ (μ.restrict (cube d)) at h
    convert h.const_mul (((-1:ℝ) ^ (∑ i, (k i - j i))) *
      (multiChoose k j : ℝ)) using 1 <;> simp [mul_assoc]
  simp_rw [← MeasureTheory.integral_const_mul]
  -- on the restricted measure every summand is integrable
  rw [← MeasureTheory.integral_finset_sum]
  · congr 1
    funext x
    simpa [diff] using (diff_monomial n k hk x)
  · intro j hj
    exact h_int j


lemma diff_sub' {d : ℕ} (u v : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) :
    diff (fun m => u m - v m) k n = diff u k n - diff v k n := by
  classical
  unfold diff
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma bkernel_nonneg {d : ℕ} {n k : Fin d → ℕ}
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cube d) :
    0 ≤ bkernel n k x := by
  unfold bkernel
  apply Finset.prod_nonneg
  intro i hi
  exact mul_nonneg (pow_nonneg (hx i).1 _) (pow_nonneg (sub_nonneg.mpr (hx i).2) _)

/-- The multivariate Bernstein kernels form a partition of unity. -/
lemma bernstein_partition {d : ℕ} (n : Fin d → ℕ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ∑ k ∈ Finset.Iic n, (multiChoose n k : ℝ) * bkernel n k x = 1 := by
  unfold bkernel
  -- again separate the coordinates
  simp_rw [multiChoose_cast]
  simp_rw [← Finset.prod_mul_distrib]
  rw [Iic_pi]
  change
    (∑ k ∈ Fintype.piFinset (fun i : Fin d => Finset.Iic (n i)),
      ∏ i, ((Nat.choose (n i) (k i) : ℝ) *
        ((x i)^(n i-k i) * (1-x i)^(k i)))) = _
  rw [← Finset.prod_univ_sum (fun i : Fin d => Finset.Iic (n i))
       (fun i (k : ℕ) => (Nat.choose (n i) k : ℝ) *
        ((x i)^(n i-k) * (1-x i)^k))]
  -- each coordinate is the binomial theorem `(x+(1-x))^n=1`
  have hcoord (i : Fin d) :
      ∑ k ∈ Finset.Iic (n i), (Nat.choose (n i) k : ℝ) *
        ((x i)^(n i-k) * (1-x i)^k) = 1 := by
    have hr : (Finset.Iic (n i) : Finset ℕ) = Finset.range (n i + 1) := by
      ext t; simp
    rw [hr]
    calc
      _ = ((1-x i) + x i)^(n i) := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 1 := by simp
  simp_rw [hcoord]
  simp


lemma sum_integral_bkernel {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (n : Fin d → ℕ) :
    (∑ k ∈ Finset.Iic n,
       (multiChoose n k : ℝ) * (∫ x in cube d, bkernel n k x ∂μ)) =
        (μ (cube d)).toReal := by
  classical
  simp_rw [← MeasureTheory.integral_const_mul]
  rw [← MeasureTheory.integral_finset_sum]
  · have hfun : (fun x : EuclideanSpace ℝ (Fin d) =>
          ∑ k ∈ Finset.Iic n,
            (multiChoose n k : ℝ) * bkernel n k x) = (fun _ => (1 : ℝ)) := by
        funext x
        exact bernstein_partition n x
    rw [hfun]
    simp [MeasureTheory.Measure.real]
  · intro k hk
    have h := integrableOn_bkernel μ n k
    change Integrable _ (μ.restrict (cube d))
    change Integrable _ (μ.restrict (cube d)) at h
    exact h.const_mul _

lemma integral_bkernel_nonneg {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (n k : Fin d → ℕ) :
    0 ≤ ∫ x in cube d, bkernel n k x ∂μ := by
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (measurableSet_cube d) (μ := μ)] with x hx
  exact bkernel_nonneg hx


lemma hausdorff_of_moments {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    HausdorffBounded (fun n => momentOf μ n - momentOf ν n) := by
  classical
  refine ⟨(μ (cube d)).toReal + (ν (cube d)).toReal, ?_⟩
  intro n
  have hk_formula (k : Fin d → ℕ) (hk : k ∈ Finset.Iic n) :
      diff (fun m => momentOf μ m - momentOf ν m) k n =
        (∫ x in cube d, bkernel n k x ∂μ) -
        (∫ x in cube d, bkernel n k x ∂ν) := by
    have hle : k ≤ n := Finset.mem_Iic.mp hk
    rw [diff_sub']
    rw [diff_moment_pos μ n k hle, diff_moment_pos ν n k hle]
  calc
    ∑ k ∈ Finset.Iic n,
        |(multiChoose n k : ℝ) * diff
           (fun m => momentOf μ m - momentOf ν m) k n| ≤
      ∑ k ∈ Finset.Iic n,
        ((multiChoose n k : ℝ) * (∫ x in cube d, bkernel n k x ∂μ) +
         (multiChoose n k : ℝ) * (∫ x in cube d, bkernel n k x ∂ν)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [hk_formula k hk]
        have hc : 0 ≤ (multiChoose n k : ℝ) := Nat.cast_nonneg _
        have hu := integral_bkernel_nonneg μ n k
        have hv := integral_bkernel_nonneg ν n k
        rw [mul_sub]
        -- each product is nonnegative
        have h1 : 0 ≤ (multiChoose n k : ℝ) * (∫ x in cube d, bkernel n k x ∂μ) :=
          mul_nonneg hc hu
        have h2 : 0 ≤ (multiChoose n k : ℝ) * (∫ x in cube d, bkernel n k x ∂ν) :=
          mul_nonneg hc hv
        rw [abs_le]
        constructor <;> linarith
    _ = (μ (cube d)).toReal + (ν (cube d)).toReal := by
      rw [Finset.sum_add_distrib]
      rw [sum_integral_bkernel μ n, sum_integral_bkernel ν n]
    _ ≤ _ := le_rfl


open Filter Topology
open scoped BoundedContinuousFunction
/-- A useful compactness step for the converse.  A uniformly bounded sequence of
Jordan parts on a compact space has a subnet whose difference integrates every
bounded continuous function with its (ordinary) limiting value.  We formulate
it with an arbitrary collection of test functions; this avoids any
sequential/metrizability assumption on the space of measures. -/
lemma exists_measures_of_bounded_approx
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
    [BorelSpace X] [CompactSpace X]
    (B : ℝ≥0) (u v : ℕ → FiniteMeasure X)
    (hm : ∀ n, (u n).mass ≤ B ∧ (v n).mass ≤ B)
    {ι : Type*} (f : ι → BoundedContinuousFunction X ℝ) (A : ι → ℝ)
    (hlim : ∀ i, Tendsto (fun n : ℕ =>
       (∫ x, f i x ∂(u n : Measure X)) - (∫ x, f i x ∂(v n : Measure X)))
       atTop (𝓝 (A i))) :
    ∃ μ ν : FiniteMeasure X, ∀ i,
       (∫ x, f i x ∂(μ : Measure X)) - (∫ x, f i x ∂(ν : Measure X)) = A i := by
  classical
  let S : Set (FiniteMeasure X) := {ρ | ρ.mass ≤ B}
  have hS : IsCompact S := isCompact_setOf_finiteMeasure_le_of_compactSpace X B
  let w : ℕ → (FiniteMeasure X × FiniteMeasure X) := fun n => (u n, v n)
  let F : Filter (FiniteMeasure X × FiniteMeasure X) := Filter.map w atTop
  have hFn : F.NeBot := (inferInstance : (atTop : Filter ℕ).NeBot).map w
  obtain ⟨q, hq⟩ := Ultrafilter.exists_le F
  have hmemF : (S ×ˢ S) ∈ F := by
    change ∀ᶠ n : ℕ in atTop, w n ∈ (S ×ˢ S)
    exact Filter.Eventually.of_forall (fun n => ⟨(hm n).1, (hm n).2⟩)
  have hmemq : (S ×ˢ S) ∈ (q : Filter _) := hq hmemF
  obtain ⟨p, hpS, hp⟩ := (hS.prod hS).ultrafilter_le_nhds' q hmemq
  refine ⟨p.1, p.2, ?_⟩
  intro i
  let g : (FiniteMeasure X × FiniteMeasure X) → ℝ := fun p =>
       (∫ x, f i x ∂(p.1 : Measure X)) - (∫ x, f i x ∂(p.2 : Measure X))
  have hg : Continuous g :=
    (FiniteMeasure.continuous_integral_boundedContinuousFunction (f i)).comp continuous_fst |>.sub
      ((FiniteMeasure.continuous_integral_boundedContinuousFunction (f i)).comp continuous_snd)
  have hp' : Tendsto g (q : Filter _) (𝓝 (g p)) := hg.continuousAt.mono_left hp
  have hA_F : Tendsto g F (𝓝 (A i)) := by
    -- this is the given ordinary limit, written on the image filter
    rw [show F = Filter.map w atTop from rfl, tendsto_map'_iff]
    exact hlim i
  have hAq : Tendsto g (q : Filter _) (𝓝 (A i)) := hA_F.mono_left hq
  -- real limits are unique on a non-trivial ultrafilter
  have he : g p = A i := tendsto_nhds_unique hp' hAq
  exact he


/-- Measures obtained on the cube as a subtype can be pushed to ambient
Euclidean space; their ordinary integrals are exactly the `momentOf`s. -/

lemma cube_compactSpace (d : ℕ) : CompactSpace {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d} :=
  isCompact_iff_compactSpace.mp (isCompact_cube d)

lemma configuration_of_subtype
    {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    (μ' ν' : FiniteMeasure {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d})
    (h : ∀ n, a n =
       (∫ x : {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d}, monomial n x.1 ∂(μ' : Measure _)) -
       (∫ x : {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d}, monomial n x.1 ∂(ν' : Measure _))) :
    IsMomentConfiguration a := by
  classical
  let val : {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d} →
      EuclideanSpace ℝ (Fin d) := fun x => x.1
  have hval : Measurable val := measurable_subtype_coe
  let μ : Measure (EuclideanSpace ℝ (Fin d)) :=
      Measure.map val (μ' : Measure {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d})
  let ν : Measure (EuclideanSpace ℝ (Fin d)) :=
      Measure.map val (ν' : Measure {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d})
  haveI : IsFiniteMeasure μ := Measure.isFiniteMeasure_map _ _
  haveI : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have hμ_mem : ∀ᵐ x ∂μ, x ∈ cube d := by
    change ∀ᵐ x ∂(Measure.map val (μ' : Measure _)), x ∈ cube d
    refine (ae_map_iff hval.aemeasurable (measurableSet_cube d)).2 ?_
    exact Filter.Eventually.of_forall (fun x => x.2)
  have hν_mem : ∀ᵐ x ∂ν, x ∈ cube d := by
    change ∀ᵐ x ∂(Measure.map val (ν' : Measure _)), x ∈ cube d
    refine (ae_map_iff hval.aemeasurable (measurableSet_cube d)).2 ?_
    exact Filter.Eventually.of_forall (fun x => x.2)
  refine ⟨μ, ν, inferInstance, inferInstance, ?_⟩
  intro n
  rw [h n]
  unfold momentOf
  -- first remove the restrictions; these measures live on the cube
  change (∫ x : {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d}, monomial n x.1 ∂(μ' : Measure _)) -
         (∫ x : {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d}, monomial n x.1 ∂(ν' : Measure _)) = _
  have hμr : μ.restrict (cube d) = μ := Measure.restrict_eq_self_of_ae_mem hμ_mem
  have hνr : ν.restrict (cube d) = ν := Measure.restrict_eq_self_of_ae_mem hν_mem
  change _ = (∫ x, monomial n x ∂(μ.restrict (cube d))) -
       ∫ x, monomial n x ∂(ν.restrict (cube d))
  rw [hμr, hνr]
  have hm : AEStronglyMeasurable (monomial n)
      (Measure.map val (μ' : Measure _)) :=
      (continuous_monomial n).measurable.aestronglyMeasurable
  have hn : AEStronglyMeasurable (monomial n)
      (Measure.map val (ν' : Measure _)) :=
      (continuous_monomial n).measurable.aestronglyMeasurable
  dsimp [μ, ν]
  rw [MeasureTheory.integral_map hval.aemeasurable hm,
      MeasureTheory.integral_map hval.aemeasurable hn]



/-- Bernstein grid on the compact cube. We use level `N+1` to avoid a
zero denominator. Coefficients outside the box never occur. -/
noncomputable def gridPt (d N : ℕ) (k : Fin d → ℕ) :
    {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d} :=
  ⟨WithLp.toLp 2 (fun i => ((N+1-k i : ℕ) : ℝ) / (N+1 : ℕ)), by
    intro i
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · have hn : (0:ℝ) < (N+1:ℕ) := by exact_mod_cast (Nat.zero_lt_succ N)
      apply (div_le_one hn).2
      exact_mod_cast (Nat.sub_le _ _) ⟩

noncomputable def diracFinite {X : Type*} [MeasurableSpace X] (x : X) :
    FiniteMeasure X := ⟨Measure.dirac x, inferInstance⟩

/-- The two positive parts of a signed atomic grid. -/
noncomputable def gridPos {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ) :
    FiniteMeasure {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d} :=
  ∑ k ∈ Finset.Iic (fun _ : Fin d => N+1),
    (Real.toNNReal ((multiChoose (fun _ : Fin d => N+1) k : ℝ) *
      diff a k (fun _ : Fin d => N+1))) • diracFinite (gridPt d N k)
noncomputable def gridNeg {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ) :
    FiniteMeasure {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d} :=
  ∑ k ∈ Finset.Iic (fun _ : Fin d => N+1),
    (Real.toNNReal (- ((multiChoose (fun _ : Fin d => N+1) k : ℝ) *
      diff a k (fun _ : Fin d => N+1)))) • diracFinite (gridPt d N k)

lemma mass_diracFinite {X : Type*} [MeasurableSpace X] (x : X) :
    (diracFinite x).mass = 1 := by
  change (Measure.dirac x Set.univ).toNNReal = 1
  simp
lemma mass_sum {X : Type*} [MeasurableSpace X]
    {ι : Type*} {s : Finset ι} (f : ι → FiniteMeasure X) :
    (∑ i ∈ s, f i).mass = ∑ i ∈ s, (f i).mass := by
  apply_fun (fun x : ℝ≥0 => (x : ENNReal))
  · simp [FiniteMeasure.ennreal_mass]
  · exact ENNReal.coe_injective
lemma mass_smul {X : Type*} [MeasurableSpace X]
    (c : ℝ≥0) (μ : FiniteMeasure X) : (c • μ).mass = c * μ.mass := by
  apply_fun (fun x : ℝ≥0 => (x : ENNReal))
  · simp [FiniteMeasure.ennreal_mass]
  · exact ENNReal.coe_injective

lemma mass_gridPos {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ) :
    ((gridPos a N).mass : ℝ) =
      ∑ k ∈ Finset.Iic (fun _ : Fin d => N+1),
        max ((multiChoose (fun _ : Fin d => N+1) k : ℝ) *
          diff a k (fun _ : Fin d => N+1)) 0 := by
  classical
  unfold gridPos
  rw [mass_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [mass_smul, mass_diracFinite]
  simp [Real.coe_toNNReal]
lemma mass_gridNeg {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ) :
    ((gridNeg a N).mass : ℝ) =
      ∑ k ∈ Finset.Iic (fun _ : Fin d => N+1),
        max (- ((multiChoose (fun _ : Fin d => N+1) k : ℝ) *
          diff a k (fun _ : Fin d => N+1))) 0 := by
  classical
  unfold gridNeg
  rw [mass_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [mass_smul, mass_diracFinite]
  simp [Real.coe_toNNReal]

lemma grid_masses_le {d : ℕ} {a : (Fin d → ℕ) → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ n : Fin d → ℕ,
      ∑ k ∈ Finset.Iic n,
        |(multiChoose n k : ℝ) * diff a k n| ≤ C) (N : ℕ) :
    (gridPos a N).mass ≤ ⟨C, hC0⟩ ∧
    (gridNeg a N).mass ≤ ⟨C, hC0⟩ := by
  classical
  -- work with their real masses
  apply And.intro
  · apply (NNReal.coe_le_coe).mp
    change ((gridPos a N).mass : ℝ) ≤ C
    rw [mass_gridPos]
    refine (Finset.sum_le_sum (s := Finset.Iic (fun _ : Fin d => N+1)) ?_).trans (hC _)
    intro k hk
    exact (by rcases le_total 0 ((multiChoose (fun _ : Fin d => N+1) k : ℝ) * diff a k (fun _ : Fin d => N+1)) with hz | hz <;> simp [hz, abs_of_nonneg, abs_of_nonpos])
  · apply (NNReal.coe_le_coe).mp
    change ((gridNeg a N).mass : ℝ) ≤ C
    rw [mass_gridNeg]
    refine (Finset.sum_le_sum (s := Finset.Iic (fun _ : Fin d => N+1)) ?_).trans (hC _)
    intro k hk
    rcases le_total 0 ((multiChoose (fun _ : Fin d => N+1) k : ℝ) * diff a k (fun _ : Fin d => N+1)) with hz | hz <;> simp [hz, abs_of_nonneg, abs_of_nonpos]

lemma integrable_finite_cont {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [CompactSpace X]
    (f : BoundedContinuousFunction X ℝ) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable f μ :=
  BoundedContinuousFunction.integrable μ f

lemma grid_integrals {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    (f : BoundedContinuousFunction
      {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d} ℝ) (N : ℕ) :
    (∫ x, f x ∂((gridPos a N) : Measure _)) -
       (∫ x, f x ∂((gridNeg a N) : Measure _)) =
      ∑ k ∈ Finset.Iic (fun _ : Fin d => N+1),
        (((multiChoose (fun _ : Fin d => N+1) k : ℝ) *
           diff a k (fun _ : Fin d => N+1)) * f (gridPt d N k)) := by
  classical
  letI : CompactSpace {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d} := cube_compactSpace d
  -- integrals of the atoms
  have hint (c : ℝ≥0) (p : {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d}) :
      (∫ x, f x ∂((c • diracFinite p) : Measure _)) = (c:ℝ) * f p := by
    change (∫ x, f x ∂((c : ENNReal) • (Measure.dirac p))) = _
    rw [MeasureTheory.integral_smul_measure]
    rw [MeasureTheory.integral_dirac]
    simp
  unfold gridPos gridNeg
  -- coercions of finite sums commute
  simp only [FiniteMeasure.toMeasure_sum]
  rw [MeasureTheory.integral_finset_sum_measure]
  · rw [MeasureTheory.integral_finset_sum_measure]
    · rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hint, hint]
      push_cast
      -- positive and negative parts subtract to the real number
      have hid (z : ℝ) : max z 0 - max (-z) 0 = z := by
        rcases le_total 0 z with hz | hz <;> simp [max_eq_left, max_eq_right, hz]
      simp_rw [Real.coe_toNNReal']
      rw [← sub_mul]
      rw [hid]
    · intro k hk
      -- all atoms integrable
      exact integrable_finite_cont f _
  · intro k hk
    exact integrable_finite_cont f _


/-- The remaining, entirely scalar, Bernstein coefficient lemma. The formulation
contains neither measures nor the cube. In one coordinate it is the familiar
identity obtained by interchanging the triangular binomial sums; terms with
`l>m` vanish by finite differences of a polynomial of degree `m`. -/
lemma scalar_bernstein_limit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : (ι → ℕ) → ℝ) (m : ι → ℕ) :
 Filter.Tendsto
  (fun N : ℕ => ∑ k ∈ Finset.Iic (fun _ : ι => N+1),
    (((∏ i : ι, ((N+1).choose (k i))) : ℕ) : ℝ) *
    (∑ j ∈ Finset.Iic k,
       (-1 : ℝ) ^ (∑ i, (k i - j i)) *
       (((∏ i : ι, ((k i).choose (j i))) : ℕ) : ℝ) *
       a ((fun _ : ι => N+1) - j)) *
    (∏ i : ι, (((N+1-k i : ℕ) : ℝ) / (N+1 : ℕ)) ^ (m i)))
  Filter.atTop (nhds (a m)) := by
 classical
 cases isEmpty_or_nonempty ι with
 | inl hempty =>
   let z : ι → ℕ := fun _ => 0
   have hsub : ∀ u : ι → ℕ, u = z := fun u => Subsingleton.elim _ _
   have hic (u : ι → ℕ) : Finset.Iic u = {z} := by
     ext t
     have ht : t = z := hsub t
     subst t
     simp
   have haeq : a z = a m := by rw [hsub m]
   have hconst :
     (fun N : ℕ => ∑ k ∈ Finset.Iic (fun _ : ι => N+1),
       (((∏ i : ι, ((N+1).choose (k i))) : ℕ) : ℝ) *
       (∑ j ∈ Finset.Iic k,
          (-1 : ℝ) ^ (∑ i, (k i - j i)) *
          (((∏ i : ι, ((k i).choose (j i))) : ℕ) : ℝ) *
          a ((fun _ : ι => N+1) - j)) *
       (∏ i : ι, (((N+1-k i : ℕ) : ℝ) / (N+1 : ℕ)) ^ (m i))) =
       (fun _ : ℕ => a m) := by
         funext N
         simp [hic, hsub, z, ← haeq]
   rw [hconst]
   exact tendsto_const_nhds
 | inr hnon =>
   exact HHSAux.triangle_limit a m

/-- Algebraic part of the Bernstein construction. For a fixed monomial the
usual multivariate Bernstein polynomial tends coefficientwise to that
monomial. Applying the coefficient functional `b ↦ a` and the finite
backward-difference formula gives this useful formulation: no continuity of
that functional is used here (only finitely many of its coefficients occur). -/
lemma bernstein_moment_limit {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    (m : Fin d → ℕ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.Iic (fun _ : Fin d => N+1),
        (((multiChoose (fun _ : Fin d => N+1) k : ℝ) *
          diff a k (fun _ : Fin d => N+1)) *
          monomial m (gridPt d N k).1))
      Filter.atTop (nhds (a m)) := by
  classical
  have h := scalar_bernstein_limit (ι := Fin d) a m
  simpa [multiChoose, diff, monomial, gridPt, mul_assoc] using h

end LeanEval.Analysis
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem hausdorff_hildebrandt_schoenberg {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    IsMomentConfiguration a ↔ HausdorffBounded a :=
/-ResultProofBegin-/by
  classical
  constructor
  · rintro ⟨μ, ν, hμ, hν, ha⟩
    letI : IsFiniteMeasure μ := hμ
    letI : IsFiniteMeasure ν := hν
    have h := LeanEval.Analysis.hausdorff_of_moments (d:=d) μ ν
    have heq : a = (fun n => momentOf μ n - momentOf ν n) := funext ha
    simpa [heq] using h
  · intro ha
    rcases ha with ⟨C, hC⟩
    have hC0 : 0 ≤ C := by
      have hh := hC (fun _ : Fin d => 0)
      have hn : 0 ≤ ∑ k ∈ Finset.Iic (fun _ : Fin d => 0),
          |(multiChoose (fun _ : Fin d => 0) k : ℝ) *
           diff a k (fun _ : Fin d => 0)| := by positivity
      exact le_trans hn hh
    letI : CompactSpace {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d} :=
      LeanEval.Analysis.cube_compactSpace d
    let fm : (Fin d → ℕ) → BoundedContinuousFunction
        {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d} ℝ := fun m =>
      BoundedContinuousFunction.mkOfCompact
        ⟨(fun x => monomial m x.1),
          (LeanEval.Analysis.continuous_monomial m).comp continuous_subtype_val⟩
    obtain ⟨μ', ν', hμν⟩ :=
      LeanEval.Analysis.exists_measures_of_bounded_approx
        (X := {x : EuclideanSpace ℝ (Fin d) // x ∈ cube d})
        (⟨C, hC0⟩ : ℝ≥0) (LeanEval.Analysis.gridPos a)
        (LeanEval.Analysis.gridNeg a)
        (fun N => LeanEval.Analysis.grid_masses_le hC0 hC N)
        fm a (by
          intro m
          have he := LeanEval.Analysis.bernstein_moment_limit a m
          have heq :
            (fun N : ℕ =>
              (∫ x, fm m x ∂(LeanEval.Analysis.gridPos a N : Measure _)) -
              (∫ x, fm m x ∂(LeanEval.Analysis.gridNeg a N : Measure _))) =
            (fun N : ℕ => ∑ k ∈ Finset.Iic (fun _ : Fin d => N+1),
              (((multiChoose (fun _ : Fin d => N+1) k : ℝ) *
                diff a k (fun _ : Fin d => N+1)) *
                monomial m (LeanEval.Analysis.gridPt d N k).1)) := by
                  funext N
                  simpa [fm] using
                    (LeanEval.Analysis.grid_integrals a (fm m) N)
          rw [heq]
          exact he)
    exact LeanEval.Analysis.configuration_of_subtype a μ' ν'
      (fun n => (hμν n).symm)
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
