import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Approx.lean

open Set Function

namespace NashSupport

/-- On a compact metric set, approximate fixed points for every positive
error automatically give an actual fixed point. This is often the analytic
(last) part of the Brouwer argument; the remaining difficulty is the
combinatorial approximate theorem. The map is allowed to be ambient. -/
lemma fixed_of_approx {E : Type*} [MetricSpace E]
    [T2Space E]
    (K : Set E) (hne : K.Nonempty) (hc : IsCompact K)
    (f : E → E) (hf : Continuous f)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ x ∈ K, dist (f x) x < ε) :
    ∃ x ∈ K, f x = x := by
  classical
  have hg : Continuous (fun x : E => dist (f x) x) := hf.dist continuous_id
  obtain ⟨z, hzK, hzmin⟩ := hc.exists_isMinOn hne hg.continuousOn
  have hz0 : dist (f z) z = 0 := by
    have hn : 0 ≤ dist (f z) z := dist_nonneg
    apply le_antisymm ?_ hn
    by_contra hposnot
    have hpos : 0 < dist (f z) z := lt_of_not_ge hposnot
    obtain ⟨y, hyK, hy⟩ := ha (dist (f z) z) hpos
    have hle := hzmin hyK
    exact (not_le_of_gt hy) hle
  exact ⟨z, hzK, dist_eq_zero.mp hz0⟩

end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Approx.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Cube.lean
open Set Function
open scoped BigOperators
namespace NashSupport
variable {α : Type*} [Fintype α] [Nonempty α]
noncomputable def cubeRet (x : α → ℝ) : α → ℝ := fun i =>
  if (∑ j, x j) ≤ 1 then
    x i + (1 - ∑ j, x j) / (Fintype.card α : ℝ)
  else x i / (∑ j, x j)
def cube : Set (α → ℝ) := {x | ∀ i, x i ∈ Set.Icc (0:ℝ) 1}
lemma card_pos : (0:ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
lemma cubeRet_mem {x : α → ℝ} (hx : x ∈ cube (α:=α)) : cubeRet x ∈ stdSimplex ℝ α := by
 classical
 have hc := card_pos (α:=α)
 have xpos (i:α) : 0 ≤ x i := (hx i).1
 have tsum0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => xpos i)
 by_cases h : (∑ i, x i) ≤ 1
 · have dpos : 0 ≤ 1 - ∑ i, x i := sub_nonneg.mpr h
   constructor
   · intro i
     simp [cubeRet, h]
     exact add_nonneg (xpos i) (div_nonneg dpos (le_of_lt hc))
   · simp [cubeRet, h, Finset.sum_add_distrib]
     -- want sum x + (#*(1-sum)/card)=1
     have hn : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hc
     field_simp
     ring
 · have tpos : 0 < ∑ i, x i := lt_of_le_of_lt (by linarith) (lt_of_not_ge h)
   have tne : (∑ i, x i) ≠ 0 := ne_of_gt tpos
   constructor
   · intro i
     simp [cubeRet, h]
     exact div_nonneg (xpos i) (le_of_lt tpos)
   · simp [cubeRet, h, ← Finset.sum_div]
     exact tne
lemma cubeRet_eq {x : α → ℝ} (hx : x ∈ stdSimplex ℝ α) : cubeRet x = x := by
 classical
 funext i
 simp [cubeRet, hx.2]
lemma continuous_cubeRet : Continuous (cubeRet : (α → ℝ) → (α → ℝ)) := by
 classical
 let t : (α → ℝ) → ℝ := fun x => ∑ j, x j
 have ht : Continuous t := by
   exact continuous_finsetSum _ (fun i _ => continuous_apply i)
 let p : (α → ℝ) → (α → ℝ) := fun x i => x i + (1-t x)/(Fintype.card α : ℝ)
 let q : (α → ℝ) → (α → ℝ) := fun x i => x i / max (t x) 1
 have hc := card_pos (α:=α)
 have hp : Continuous p := by
   apply continuous_pi; intro i
   exact (continuous_apply i).add ((continuous_const.sub ht).div_const _)
 have hq : Continuous q := by
   apply continuous_pi; intro i
   exact (continuous_apply i).div
     (ht.max continuous_const)
     (by intro x hzero
         have hh : (1:ℝ) ≤ max (t x) 1 := le_max_right _ _
         linarith)
 have hif : Continuous (fun x : α → ℝ => if t x ≤ (1:ℝ) then p x else q x) := by
   exact hp.if_le hq ht continuous_const (by
     intro x hx
     have hmax : max (t x) 1 = 1 := by simp [hx]
     funext i
     simp [p, q, hx, hmax])
 convert hif using 1
 funext x i
 by_cases h : t x ≤ 1
 · simp [cubeRet, t, p, h]
 · have he : max (t x) 1 = t x := max_eq_left (le_of_lt (lt_of_not_ge h))
   simp [cubeRet, t, p, q, h, he]

end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Cube.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Multiaffine.lean

open scoped BigOperators
open Function Set

namespace NashSupport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- contribution of a pure profile with player `i` removed. -/
noncomputable def otherCoeff (w : (∀ i, A i) → ℝ)
    (x : ∀ i, A i → ℝ) (i : ι) (s : ∀ i, A i) : ℝ :=
  (∏ j ∈ (Finset.univ.erase i), x j (s j)) * w s

noncomputable def payoff (w : (∀ i, A i) → ℝ)
    (x : ∀ i, A i → ℝ) : ℝ :=
  ∑ s : (∀ i, A i), (∏ j, x j (s j)) * w s

lemma prod_update_erase (w : (∀ i, A i) → ℝ)
    (x : ∀ i, A i → ℝ) (i : ι) (q : A i → ℝ) (s : ∀ i, A i) :
    (∏ j, (Function.update x i q) j (s j)) * w s =
      q (s i) * otherCoeff w x i s := by
  classical
  have hsplit := (Finset.mul_prod_erase Finset.univ
    (fun j => (Function.update x i q) j (s j)) (Finset.mem_univ i))
  -- hsplit : value at i * rest = product
  have hrest :
      (∏ j ∈ (Finset.univ.erase i), (Function.update x i q) j (s j)) =
        ∏ j ∈ (Finset.univ.erase i), x j (s j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    simp [hne]
  dsimp [otherCoeff]
  -- substitute the separated product
  rw [← hsplit]
  simp [hrest]
  -- `simp` associates multiplication
  ac_rfl

lemma payoff_update_eq
    (w : (∀ i, A i) → ℝ) (x : ∀ i, A i → ℝ)
    (i : ι) (q : A i → ℝ) :
    payoff w (Function.update x i q) =
      ∑ s : (∀ j, A j), q (s i) * otherCoeff w x i s := by
  classical
  unfold payoff
  apply Finset.sum_congr rfl
  intro s hs
  exact prod_update_erase w x i q s

/-- Expected payoff is linear in the probabilities of any one coordinate;
explicitly it is the mixture of the corresponding pure-coordinate payoffs. -/
lemma payoff_update_eq_sum_pure
    (w : (∀ i, A i) → ℝ) (x : ∀ i, A i → ℝ)
    (i : ι) (q : A i → ℝ) :
    payoff w (Function.update x i q) =
      ∑ a : A i, q a * payoff w (Function.update x i (Pi.single a 1)) := by
  classical
  rw [payoff_update_eq (w:=w) (x:=x) (i:=i) (q:=q)]
  -- expose the other occurrences as well
  simp_rw [payoff_update_eq (w:=w) (x:=x) (i:=i)]
  -- Move all scalars inside and switch the two finite sums.
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  -- for this fixed profile exactly one basis vector is nonzero
  -- simplify the inner Fintype sum
  simp [Pi.single_apply, mul_assoc]

/-- The value of the current vector itself is the mixture of its pure
coordinate values. -/
lemma payoff_eq_sum_pure
    (w : (∀ i, A i) → ℝ) (x : ∀ i, A i → ℝ) (i : ι) :
    payoff w x =
      ∑ a : A i, x i a * payoff w (Function.update x i (Pi.single a 1)) := by
  classical
  simpa using (payoff_update_eq_sum_pure (w:=w) (x:=x) (i:=i) (q:=x i))

/-- pure-coordinate values do not depend on the old value in that coordinate. -/
lemma payoff_update_update_pure
    (w : (∀ i, A i) → ℝ) (x : ∀ i, A i → ℝ)
    (i : ι) (q : A i → ℝ) (a : A i) :
    payoff w (Function.update (Function.update x i q) i (Pi.single a 1)) =
      payoff w (Function.update x i (Pi.single a 1)) := by
  classical
  congr 1
  -- equality of the updated dependent functions
  funext j b
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

end NashSupport

namespace NashSupport
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

lemma continuous_payoff (w : (∀ i, A i) → ℝ) :
    Continuous (fun x : (∀ i, A i → ℝ) => payoff w x) := by
  classical
  unfold payoff
  fun_prop

lemma continuous_payoff_pure (w : (∀ i, A i) → ℝ) (i : ι) (a : A i) :
    Continuous (fun x : (∀ i, A i → ℝ) =>
      payoff w (Function.update x i (Pi.single a 1))) := by
  classical
  -- can also let `fun_prop` look through the finite polynomial
  unfold payoff
  fun_prop

end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Multiaffine.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Product.lean

open Set
namespace NashSupport

variable {ι : Type*} [Fintype ι]
variable {A : ι → Type*} [∀ i, Fintype (A i)]

def productSimplex : Set (∀ i, A i → ℝ) :=
  {x | ∀ i, x i ∈ stdSimplex ℝ (A i)}

lemma productSimplex_nonempty [∀ i, Nonempty (A i)] :
    (productSimplex (A:=A)).Nonempty := by
  classical
  let a : ∀ i, A i := fun i => Classical.choice (inferInstance : Nonempty (A i))
  refine ⟨(fun i => Pi.single (a i) 1), ?_⟩
  intro i
  exact single_mem_stdSimplex ℝ (a i)

lemma productSimplex_convex : Convex ℝ (productSimplex (A:=A)) := by
  classical
  -- use the convenient set-of form of the pi lemma
  have hp : productSimplex (A:=A) = (Set.univ.pi (fun i => stdSimplex ℝ (A i))) := by
    ext x; simp [productSimplex]
  rw [hp]
  exact convex_pi (fun _ _ => convex_stdSimplex ℝ _)

lemma productSimplex_compact : IsCompact (productSimplex (A:=A)) := by
  classical
  exact isCompact_pi_infinite (fun i => isCompact_stdSimplex ℝ (A i))

end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Product.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Reduction.lean

open scoped BigOperators
open Set Function

namespace NashSupport

variable {A : Type*} [Fintype A]

/-- Elementary finite dimensional part of Nash's fixed point proof.
If the usual positive-gain normalisation fixes a probability vector, every
pure value is at most its average. This lemma deliberately has no topological
content. -/
lemma values_le_of_fixed
    (p v : A → ℝ) (U : ℝ)
    (hp : p ∈ stdSimplex ℝ A)
    (hav : (∑ a : A, p a * v a) = U)
    (hfix : ∀ a : A,
      p a = (p a + max 0 (v a - U)) /
        (1 + ∑ b : A, max 0 (v b - U))) :
    ∀ a : A, v a ≤ U := by
  classical
  let d : A → ℝ := fun a => max 0 (v a - U)
  let D : ℝ := ∑ a : A, d a
  have hd (a : A) : 0 ≤ d a := by dsimp [d]; exact le_max_left _ _
  have hD : 0 ≤ D := Finset.sum_nonneg (fun a _ => hd a)
  have hden : 0 < 1 + D := by linarith
  have hda (a : A) : d a = p a * D := by
    have hf := hfix a
    change p a = (p a + d a) / (1 + D) at hf
    -- multiply by the strictly positive denominator
    have hm := (eq_div_iff (ne_of_gt hden)).mp hf
    linarith
  have hp0 (a : A) : 0 ≤ p a := hp.1 a
  -- First show the total positive gain vanishes. If it did not, every
  -- strategy in the support would be strictly better than the average.
  have hDz : D = 0 := by
    by_contra hne
    have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hne)
    have hex : ∃ a : A, 0 < p a := by
      by_contra hn
      push_neg at hn
      have hz : (∑ a : A, p a) = 0 := by
        have hall : ∀ a : A, p a = 0 := fun a => le_antisymm (hn a) (hp0 a)
        simp [hall]
      have hone := hp.2
      -- membership is transparent
      linarith
    -- the weighted deviations have nonnegative terms and one positive term
    have hnterm (a : A) : 0 ≤ p a * (v a - U) := by
      by_cases ha : p a = 0
      · simp [ha]
      · have hpa : 0 < p a := lt_of_le_of_ne (hp0 a) (Ne.symm ha)
        have hdpos : 0 < d a := by rw [hda]; exact mul_pos hpa hDp
        have hva : 0 < v a - U := by
          dsimp [d] at hdpos
          exact (lt_max_iff.mp hdpos).resolve_left (lt_irrefl _)
        exact mul_nonneg (le_of_lt hpa) (le_of_lt hva)
    -- easier local facts for positive support
    have hpos_term {a : A} (ha : 0 < p a) : 0 < p a * (v a - U) := by
      have hdpos : 0 < d a := by rw [hda]; exact mul_pos ha hDp
      have hva : 0 < v a - U := by
        dsimp [d] at hdpos
        -- `max 0 t > 0` implies `t > 0`
        exact (lt_max_iff.mp hdpos).resolve_left (by exact lt_irrefl 0)
      exact mul_pos ha hva
    have hsumpos : 0 < ∑ a : A, p a * (v a - U) := by
      classical
      let a0 := Classical.choose hex
      have ha0 := Classical.choose_spec hex
      exact Finset.sum_pos'
        (fun a _ => hnterm a)
        ⟨a0, Finset.mem_univ _, hpos_term ha0⟩
    have hsumzero : (∑ a : A, p a * (v a - U)) = 0 := by
      -- expand using the average identity
      calc
        (∑ a : A, p a * (v a - U)) =
            (∑ a : A, p a * v a) - (∑ a : A, p a) * U := by
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib]
              rw [Finset.sum_mul]
        _ = 0 := by rw [hav, hp.2]; ring
    linarith
  intro a
  have hdz' := hda a
  rw [hDz, mul_zero] at hdz'
  have hz : max 0 (v a - U) = 0 := hdz'
  have : v a - U ≤ 0 := by
    -- from max = 0
    have := le_max_right 0 (v a - U)
    linarith
  linarith

/-- Consequence for an arbitrary probability mixture. -/
lemma mixture_le_of_values_le
    (v : A → ℝ) (U : ℝ) (h : ∀ a, v a ≤ U)
    (q : A → ℝ) (hq : q ∈ stdSimplex ℝ A) :
    (∑ a : A, q a * v a) ≤ U := by
  classical
  calc
    (∑ a : A, q a * v a) ≤ ∑ a : A, q a * U :=
      Finset.sum_le_sum (fun a _ => (mul_le_mul_of_nonneg_left (h a) (hq.1 a)))
    _ = U := by rw [← Finset.sum_mul, hq.2, one_mul]

lemma mixture_le_of_fixed
    (p v : A → ℝ) (U : ℝ)
    (hp : p ∈ stdSimplex ℝ A)
    (hav : (∑ a : A, p a * v a) = U)
    (hfix : ∀ a : A, p a = (p a + max 0 (v a - U)) /
        (1 + ∑ b : A, max 0 (v b - U)))
    (q : A → ℝ) (hq : q ∈ stdSimplex ℝ A) :
    (∑ a : A, q a * v a) ≤ U :=
  mixture_le_of_values_le v U (values_le_of_fixed p v U hp hav hfix) q hq

end NashSupport

namespace NashSupport
variable {A : Type*} [Fintype A]

/-- Normalising by the sum of nonnegative increments stays in the simplex. -/
lemma normalize_mem_simplex (p : A → ℝ) (hp : p ∈ stdSimplex ℝ A)
    (d : A → ℝ) (hd : ∀ a, 0 ≤ d a) :
    (fun a => (p a + d a) / (1 + ∑ b : A, d b)) ∈ stdSimplex ℝ A := by
  classical
  have hD : 0 ≤ ∑ b : A, d b := Finset.sum_nonneg (fun a _ => hd a)
  have hden : 0 < 1 + ∑ b : A, d b := by linarith
  constructor
  · intro a; exact div_nonneg (add_nonneg (hp.1 a) (hd a)) (le_of_lt hden)
  · -- finite additivity
    calc
      (∑ a : A, (p a + d a) / (1 + ∑ b : A, d b)) =
          ( (∑ a : A, p a) + (∑ a : A, d a)) /
            (1 + ∑ b : A, d b) := by
              rw [← Finset.sum_add_distrib]
              -- division by a fixed scalar distributes over a sum
              rw [Finset.sum_div]
      _ = 1 := by rw [hp.2]; field_simp

end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Reduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/CubeTransfer.lean
open Set Function
namespace NashSupport
variable {α : Type*} [Fintype α] [Nonempty α]
-- transfer approximate theorem on the cube to the simplex
lemma simplexApprox_of_cube
 (cube_core : ∀ (h : (α → ℝ) → (α → ℝ)), Continuous h →
    MapsTo h (cube (α:=α)) (cube (α:=α)) →
    ∀ d : ℝ, 0 < d → ∃ x ∈ cube (α:=α), dist (h x) x < d) :
 ∀ (g : (α → ℝ) → (α → ℝ)), Continuous g →
   MapsTo g (stdSimplex ℝ α) (stdSimplex ℝ α) →
   ∀ d : ℝ, 0 < d → ∃ x ∈ stdSimplex ℝ α, dist (g x) x < d := by
 classical
 intro g hg hgm
 let h : (α → ℝ) → (α → ℝ) := fun x => g (cubeRet x)
 have hcubene : (cube (α:=α)).Nonempty := by
   refine ⟨(fun _ => 0), ?_⟩
   exact fun i => ⟨le_rfl, zero_le_one⟩
 have hcubecompact : IsCompact (cube (α:=α)) := by
   -- pi compact
   -- isCompact_pi_infinite
   exact isCompact_pi_infinite (fun i => isCompact_Icc)
 have hr : ∀ {x : α → ℝ}, x ∈ cube (α:=α) → cubeRet x ∈ stdSimplex ℝ α :=
   fun {x} hx => cubeRet_mem hx
 have hm_simple_cube {z : α → ℝ} (hz : z ∈ stdSimplex ℝ α) : z ∈ cube (α:=α) := by
   intro i
   exact mem_Icc_of_mem_stdSimplex hz i
 have hhC : Continuous h := hg.comp continuous_cubeRet
 have hhmap : MapsTo h (cube (α:=α)) (cube (α:=α)) := by
   intro x hx
   exact hm_simple_cube (hgm (hr hx))
 obtain ⟨z, hz, hzfix⟩ := fixed_of_approx (cube (α:=α)) hcubene hcubecompact h hhC
   (cube_core h hhC hhmap)
 have hzS : z ∈ stdSimplex ℝ α := by
   have : g (cubeRet z) ∈ stdSimplex ℝ α := hgm (hr hz)
   change g (cubeRet z) = z at hzfix
   rw [hzfix] at this
   exact this
 have hzfix' : g z = z := by
   have hret := cubeRet_eq hzS
   -- hzfix : h z = z
   simpa [h, hret] using hzfix
 intro d hd
 exact ⟨z, hzS, by simpa [hzfix'] using hd⟩
end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/CubeTransfer.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/FinTransfer.lean
open Set Function
namespace NashSupport
lemma cubeApprox_of_fin {α : Type*} [Fintype α]
 (core : ∀ (k : ℕ), ∀ (h : (Fin k → ℝ) → (Fin k → ℝ)), Continuous h →
   MapsTo h (cube (α:=Fin k)) (cube (α:=Fin k)) →
   ∀ d : ℝ, 0 < d → ∃ z ∈ cube (α:=Fin k), dist (h z) z < d) :
 ∀ (h : (α → ℝ) → (α → ℝ)), Continuous h →
   MapsTo h (cube (α:=α)) (cube (α:=α)) →
   ∀ d : ℝ, 0 < d → ∃ z ∈ cube (α:=α), dist (h z) z < d := by
 classical
 let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
 let push : (α → ℝ) → (Fin (Fintype.card α) → ℝ) := fun x i => x (e.symm i)
 let pull : (Fin (Fintype.card α) → ℝ) → (α → ℝ) := fun y a => y (e a)
 have hpC : Continuous push := by
   dsimp [push]
   apply continuous_pi
   intro i
   exact continuous_apply _
 have hlC : Continuous pull := by
   dsimp [pull]
   apply continuous_pi
   intro a
   exact continuous_apply _
 have hpl (x : α → ℝ) : pull (push x) = x := by
   funext a; simp [push, pull, e]
 have hlp (y : Fin (Fintype.card α) → ℝ) : push (pull y) = y := by
   funext i; simp [push, pull, e]
 have hp_mem {x : α → ℝ} (hx : x ∈ cube (α:=α)) : push x ∈ cube (α:=Fin (Fintype.card α)) := by
   intro i
   exact hx (e.symm i)
 have hl_mem {y : Fin (Fintype.card α) → ℝ} (hy : y ∈ cube (α:=Fin (Fintype.card α))) : pull y ∈ cube (α:=α) := by
   intro a
   exact hy (e a)
 intro h hh hmaps
 let H : (Fin (Fintype.card α) → ℝ) → (Fin (Fintype.card α) → ℝ) :=
   fun y => push (h (pull y))
 have hHC : Continuous H := hpC.comp (hh.comp hlC)
 have hHmap : MapsTo H (cube (α:=Fin (Fintype.card α))) (cube (α:=Fin (Fintype.card α))) := by
   intro y hy
   exact hp_mem (hmaps (hl_mem hy))
 have hne : (cube (α:=Fin (Fintype.card α))).Nonempty := by
   exact ⟨(fun _ => 0), fun i => ⟨le_rfl, zero_le_one⟩⟩
 have hcp : IsCompact (cube (α:=Fin (Fintype.card α))) :=
   isCompact_pi_infinite (fun i => isCompact_Icc)
 obtain ⟨y, hy, hyfix⟩ := fixed_of_approx _ hne hcp H hHC
   (core (Fintype.card α) H hHC hHmap)
 have hxfix : h (pull y) = pull y := by
   have := congrArg pull hyfix
   simpa [H, hpl, hlp] using this
 intro d hd
 exact ⟨pull y, hl_mem hy, by simpa [hxfix] using hd⟩
end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/FinTransfer.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Grid.lean
open Set Function
namespace NashSupport
/-- The analytic part of the cubical lemma.  A cell on a sufficiently
fine grid on which every component of the vector field has both signs
already gives an approximate zero.  This formulation (with witnesses
near a centre) is convenient for any of the usual cubical Sperner
lemmas. -/
lemma cube_approx_of_crossing (k : ℕ)
    (H : (Fin k → ℝ) → (Fin k → ℝ)) (hH : Continuous H)
    (cross : ∀ r : ℝ, 0 < r → ∃ z ∈ cube (α:=Fin k),
      ∀ i : Fin k,
        (∃ y ∈ cube (α:=Fin k), dist y z < r ∧ 0 ≤ H y i - y i) ∧
        (∃ y ∈ cube (α:=Fin k), dist y z < r ∧ H y i - y i ≤ 0)) :
    ∀ d : ℝ, 0 < d → ∃ z ∈ cube (α:=Fin k), dist (H z) z < d := by
  classical
  let F : (Fin k → ℝ) → (Fin k → ℝ) := fun x i => H x i - x i
  have hFC : Continuous F := by
    dsimp [F]
    exact hH.sub continuous_id
  have hc : IsCompact (cube (α:=Fin k)) :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  have hu : UniformContinuousOn F (cube (α:=Fin k)) :=
    hc.uniformContinuousOn_of_continuous hFC.continuousOn
  intro d hd
  obtain ⟨r, hr, hmod⟩ :=
    (Metric.uniformContinuousOn_iff.mp hu) (d/2) (by linarith)
  obtain ⟨z, hz, hzsign⟩ := cross r hr
  refine ⟨z, hz, ?_⟩
  -- The product metric here is the sup metric.
  apply (dist_pi_lt_iff hd).2
  intro i
  obtain ⟨yp, hyp, hpnear, hpsign⟩ := (hzsign i).1
  obtain ⟨ym, hym, hmnear, hmsign⟩ := (hzsign i).2
  have hp := hmod yp hyp z hz hpnear
  have hm := hmod ym hym z hz hmnear
  have hpi := (dist_pi_lt_iff (by linarith : 0 < d/2)).1 hp i
  have hmi := (dist_pi_lt_iff (by linarith : 0 < d/2)).1 hm i
  change dist (H z i) (z i) < d
  rw [Real.dist_eq]
  have hpi' : |(H yp i - yp i) - (H z i - z i)| < d/2 := by
    convert (hpi) using 1 <;> dsimp [F] <;> simp [Real.dist_eq] <;> ring
  have hmi' : |(H ym i - ym i) - (H z i - z i)| < d/2 := by
    convert (hmi) using 1 <;> dsimp [F] <;> simp [Real.dist_eq] <;> ring
  have hlow : -(d/2) < H z i - z i := by
    have h := (abs_lt.mp hpi').2
    -- hpnear compares a nonnegative value at `yp` with `z`.
    linarith
  have hupp : H z i - z i < d/2 := by
    have h := (abs_lt.mp hmi').1
    linarith
  exact lt_trans (abs_lt.mpr ⟨hlow, hupp⟩) (by linarith)
end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Grid.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Lift.lean

open Set Function
open scoped BigOperators
namespace NashSupport

/- A small finite Fubini identity in the convenient (dependent) form.  The
library's `Finset.prod_univ_sum` has the same statement with `piFinset`;
taking all the finsets to be `univ` gives this version. -/
lemma sum_prod_pi {ι : Type*} [DecidableEq ι] [Fintype ι]
 {A : ι → Type*} [∀ i, Fintype (A i)]
 (g : ∀ i, A i → ℝ) :
 (∑ x : (∀ i, A i), ∏ i, g i (x i)) = ∏ i, ∑ a, g i a := by
 classical
 have h := Finset.prod_univ_sum
   (R:=ℝ) (ι:=ι)
   (t:= fun i => (Finset.univ : Finset (A i)))
   (f:= fun i a => g i a)
 symm
 simpa [Fintype.piFinset_univ] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

noncomputable def indep (x : ∀ i, A i → ℝ) : ((∀ i, A i) → ℝ) :=
  fun s => ∏ i, x i (s i)

noncomputable def marg (p : ((∀ i, A i) → ℝ)) : ∀ i, A i → ℝ := by
  classical
  exact fun i a => ∑ s : (∀ i, A i), if s i = a then p s else 0

lemma continuous_indep : Continuous (fun x : (∀ i, A i → ℝ) => indep x) := by
  classical
  unfold indep
  apply continuous_pi
  intro s
  exact continuous_finset_prod _ (fun i _ =>
    (continuous_apply (s i)).comp (continuous_apply i))

lemma continuous_marg : Continuous (fun p : ((∀ i, A i) → ℝ) => marg p) := by
  classical
  unfold marg
  apply continuous_pi
  intro i
  apply continuous_pi
  intro a
  apply continuous_finsetSum
  intro s hs
  by_cases h : s i = a
  · simpa [h] using (continuous_apply s :
        Continuous (fun p : ((∀ i, A i) → ℝ) => p s))
  · simpa [h] using (continuous_const :
        Continuous (fun _p : ((∀ i, A i) → ℝ) => (0:ℝ)))

lemma marg_mem (p : ((∀ i, A i) → ℝ)) (hp : p ∈ stdSimplex ℝ (∀ i, A i)) :
    marg p ∈ productSimplex (A:=A) := by
  classical
  intro i
  constructor
  · intro a
    unfold marg
    apply Finset.sum_nonneg
    intro s hs
    by_cases h : s i = a
    · simp [h, hp.1 s]
    · simp [h]
  · unfold marg
    calc
      (∑ a : A i, ∑ s : (∀ j, A j), if s i = a then p s else 0)
          = ∑ s : (∀ j, A j), ∑ a : A i, if s i = a then p s else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ s : (∀ j, A j), p s := by
            apply Finset.sum_congr rfl
            intro s hs
            calc
              (∑ a : A i, if s i = a then p s else 0)
                  = ∑ a : A i, if a = s i then p s else 0 := by
                      apply Finset.sum_congr rfl
                      intro a ha
                      by_cases h : s i = a
                      · simp [h]
                      · have h' : a ≠ s i := Ne.symm h
                        simp [h, h']
              _ = p s := by simp
      _ = 1 := hp.2

lemma indep_mem (x : ∀ i, A i → ℝ)
    (hx : x ∈ productSimplex (A:=A)) :
    indep x ∈ stdSimplex ℝ (∀ i, A i) := by
  classical
  constructor
  · intro s
    unfold indep
    exact Finset.prod_nonneg (fun i _ => (hx i).1 _)
  · unfold indep
    rw [sum_prod_pi]
    have h1 : ∀ i, (∑ a : A i, x i a) = 1 := fun i => (hx i).2
    simp [h1]

lemma marg_indep (x : ∀ i, A i → ℝ)
    (hx : x ∈ productSimplex (A:=A)) : marg (indep x) = x := by
  classical
  funext i a
  unfold marg indep
  -- insert an indicator in the i-th factor
  let g : ∀ j, A j → ℝ := Function.update x i (fun b => if b = a then x i b else 0)
  have gi (b : A i) : g i b = (if b = a then x i b else 0) := by
    simp [g]
  have gj {j : ι} (h : j ≠ i) (b : A j) : g j b = x j b := by
    simp [g, h]
  have hprod (s : ∀ j, A j) :
      (∏ j, g j (s j)) = if s i = a then ∏ j, x j (s j) else 0 := by
    classical
    by_cases hsi : s i = a
    · rw [if_pos hsi]
      apply Finset.prod_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j
        simp [gi, hsi]
      · exact gj hji (s j)
    · rw [if_neg hsi]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa [gi, hsi])
  have hd :
      (∑ s : (∀ j, A j), ∏ j, g j (s j)) =
        ∏ j : ι, (∑ b : A j, g j b) := sum_prod_pi g
  have hsum_i : (∑ b : A i, g i b) = x i a := by
    calc
      (∑ b : A i, g i b) = ∑ b : A i, if b = a then x i b else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact gi b
      _ = x i a := by simp
  have hsum_ne {j : ι} (h : j ≠ i) : (∑ b : A j, g j b) = 1 := by
    calc
      (∑ b : A j, g j b) = ∑ b : A j, x j b := by
        apply Finset.sum_congr rfl
        intro b hb
        exact gj h b
      _ = 1 := (hx j).2
  calc
    (∑ s : (∀ j, A j), if s i = a then ∏ j, x j (s j) else 0)
        = ∑ s : (∀ j, A j), ∏ j, g j (s j) := by
            apply Finset.sum_congr rfl
            intro s hs
            symm
            exact hprod s
    _ = ∏ j : ι, (∑ b : A j, g j b) := hd
    _ = x i a := by
          classical
          -- only the distinguished factor is different from 1
          have hp := Finset.prod_eq_single (s:= (Finset.univ : Finset ι))
            (f:= fun j : ι => ∑ b : A j, g j b) i
            (by
              intro j hj hne
              exact hsum_ne hne)
            (by simp)
          -- expand the univ products
          -- lemma uses bounded form `∏ x ∈ s`
          simpa [hsum_i] using hp

end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Lift.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Low.lean
open Set Function
namespace NashSupport
-- cases
lemma cube0 (H : (Fin 0 → ℝ) → (Fin 0 → ℝ)) (hh : Continuous H)
 (hm : MapsTo H (cube (α:=Fin 0)) (cube (α:=Fin 0))) :
 ∀ d : ℝ, 0 < d → ∃ z ∈ cube (α:=Fin 0), dist (H z) z < d := by
 classical
 intro d hd
 let z : Fin 0 → ℝ := fun i => Fin.elim0 i
 have hz : z ∈ cube (α:=Fin 0) := by intro i; exact Fin.elim0 i
 have he (w : Fin 0 → ℝ) : w = z := Subsingleton.elim _ _
 refine ⟨z, hz, ?_⟩
 rw [he (H z), dist_self]
 exact hd

lemma cube1 (H : (Fin 1 → ℝ) → (Fin 1 → ℝ)) (hh : Continuous H)
 (hm : MapsTo H (cube (α:=Fin 1)) (cube (α:=Fin 1))) :
 ∀ d : ℝ, 0 < d → ∃ z ∈ cube (α:=Fin 1), dist (H z) z < d := by
 classical
 -- identify functions on a singleton with their zeroth coordinate
 let embed : ℝ → (Fin 1 → ℝ) := fun t _ => t
 let eval : (Fin 1 → ℝ) → ℝ := fun z => z (0 : Fin 1)
 let h : ℝ → ℝ := fun t => eval (H (embed t))
 have hembed : Continuous embed := by
   apply continuous_pi
   intro i; exact continuous_id
 have heval : Continuous eval := continuous_apply 0
 have hh' : Continuous h := heval.comp (hh.comp hembed)
 have heq (z : Fin 1 → ℝ) : embed (eval z) = z := by
   funext i
   have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
   subst i
   rfl
 have he_mem {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : embed t ∈ cube (α:=Fin 1) := by
   intro i
   simpa [embed] using ht
 have hv_mem {z : Fin 1 → ℝ} (hz : z ∈ cube (α:=Fin 1)) : eval z ∈ Set.Icc (0:ℝ) 1 := hz 0
 have hm' : MapsTo h (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := by
   intro t ht
   exact hv_mem (hm (he_mem ht))
 obtain ⟨t, ht, htfix⟩ := exists_mem_Icc_isFixedPt_of_mapsTo
    hh'.continuousOn (show (0:ℝ) ≤ 1 by norm_num) hm'
 -- note IsFixedPt h t = h t = t
 have hfix : H (embed t) = embed t := by
   have := congrArg embed htfix
   -- heq
   simpa [h, heq] using this
 intro d hd
 exact ⟨embed t, he_mem ht, by simpa [hfix] using hd⟩
end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Low.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/GridReduce.lean
open Set Function
open scoped BigOperators
namespace NashSupport
/-- A vertex of a small box, with lower corner `c`. Boolean true means its
upper endpoint in that coordinate. Keeping this definition separate makes the
residual part of cubical Sperner entirely finite. -/
def smallVertex {k m : ℕ} (c : Fin k → Fin m) (t : Fin k → Bool) :
    Fin k → Fin (m+1) := fun i =>
  ⟨(c i).val + (if t i then 1 else 0), by
    have h := (c i).isLt
    split <;> omega⟩

noncomputable def gridPoint {k : ℕ} (m : ℕ) (v : Fin k → Fin (m+1)) : Fin k → ℝ :=
  fun i => (v i : ℝ) / (m:ℝ)

/-- The precise finite cubical lemma needed for Brouwer. There is no
analysis in this assertion: all the types quantified over after `m` are
finite, and a labelling is a Boolean table. On the two opposite faces its
`i`th bit is prescribed. -/
def CubicalLabelLemma (k : ℕ) : Prop :=
  ∀ (m : ℕ), 0 < m →
   ∀ L : (Fin k → Fin (m+1)) → Fin k → Bool,
    (∀ v i, (v i).val = 0 → L v i = false) →
    (∀ v i, (v i).val = m → L v i = true) →
    ∃ c : Fin k → Fin m, ∀ i : Fin k,
      (∃ t : Fin k → Bool, L (smallVertex c t) i = false) ∧
      (∃ t : Fin k → Bool, L (smallVertex c t) i = true)

lemma gridPoint_mem {k m : ℕ} (hm : 0 < m) (v : Fin k → Fin (m+1)) :
    gridPoint m v ∈ cube (α:=Fin k) := by
  intro i
  dsimp [gridPoint]
  constructor
  · exact div_nonneg (by exact_mod_cast (Nat.zero_le (v i).val))
      (by exact_mod_cast (Nat.zero_le m))
  · apply (div_le_iff₀ (by exact_mod_cast hm : (0:ℝ) < m)).2
    simpa using (by exact_mod_cast (Nat.le_of_lt_succ (v i).isLt) : (v i : ℝ) ≤ (m:ℝ))

lemma gridPoint_vertex_near {k m : ℕ} (hm : 0 < m)
    (c : Fin k → Fin m) (t t' : Fin k → Bool) :
    dist (gridPoint m (smallVertex c t))
      (gridPoint m (smallVertex c t')) ≤ (1:ℝ) / m := by
  classical
  apply (dist_pi_le_iff (by positivity : (0:ℝ) ≤ (1:ℝ)/m)).2
  intro i
  rw [Real.dist_eq]
  dsimp [gridPoint, smallVertex]
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  -- only two endpoints in a coordinate; enumerate the booleans.
  have hne : (m:ℝ) ≠ 0 := ne_of_gt hmr
  cases h1 : t i <;> cases h2 : t' i
  · simp [h1, h2]
  · simp [h1, h2]
    rw [div_sub_div_same]
    have he : ( (c i : ℝ) - ((c i : ℝ) + 1)) = -1 := by ring
    rw [he, abs_div, abs_of_nonpos (by norm_num : (-1:ℝ) ≤ 0), abs_of_pos hmr]
    simp
  · simp [h1, h2]
    rw [div_sub_div_same]
    have he : ( (c i : ℝ) + 1 - (c i : ℝ)) = 1 := by ring
    rw [he, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1), abs_of_pos hmr]
    simp
  · simp [h1, h2]

/-- Reduction of the cubical analytic theorem to the finite Boolean labelling
lemma. In particular, ties (a zero component on a vertex) cause no genericity
issue: it can be given either label; the choice below fixes the far face. -/
lemma cube_crossing_of_labels (lab : ∀ k : ℕ, CubicalLabelLemma k)
    (k : ℕ) (H : (Fin k → ℝ) → (Fin k → ℝ))
    (hmaps : MapsTo H (cube (α:=Fin k)) (cube (α:=Fin k))) :
    ∀ r : ℝ, 0 < r → ∃ z ∈ cube (α:=Fin k),
      ∀ i : Fin k,
        (∃ y ∈ cube (α:=Fin k), dist y z < r ∧ 0 ≤ H y i - y i) ∧
        (∃ y ∈ cube (α:=Fin k), dist y z < r ∧ H y i - y i ≤ 0) := by
  classical
  intro r hr
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
  let m : ℕ := n+1
  have hm : 0 < m := by dsimp [m]; omega
  have hfine : (1:ℝ) / m < r := by
    simpa [m, Nat.cast_add, Nat.cast_one] using hn
  let L : (Fin k → Fin (m+1)) → Fin k → Bool := fun v i =>
    if H (gridPoint m v) i - gridPoint m v i < 0 then true
    else if 0 < H (gridPoint m v) i - gridPoint m v i then false
    else decide ((v i).val ≠ 0)
  have Llo : ∀ v i, (v i).val = 0 → L v i = false := by
    intro v i hi
    have hz : gridPoint m v i = 0 := by simp [gridPoint, hi]
    have hp := (hmaps (gridPoint_mem hm v) i).1
    have hnon : 0 ≤ H (gridPoint m v) i - gridPoint m v i := by rw [hz]; linarith
    unfold L
    rw [if_neg (not_lt_of_ge hnon)]
    by_cases hpos : 0 < H (gridPoint m v) i - gridPoint m v i
    · simp [hpos]
    · have hv : ¬ (v i).val ≠ 0 := by simp [hi]
      simp [hpos, hv]
  have Lhi : ∀ v i, (v i).val = m → L v i = true := by
    intro v i hi
    have hmr : (0:ℝ) < m := by exact_mod_cast hm
    have hz : gridPoint m v i = 1 := by
      dsimp [gridPoint]; simp [hi, ne_of_gt hmr]
    have hp := (hmaps (gridPoint_mem hm v) i).2
    have hnon : H (gridPoint m v) i - gridPoint m v i ≤ 0 := by rw [hz]; linarith
    unfold L
    by_cases hneg : H (gridPoint m v) i - gridPoint m v i < 0
    · simp [hneg]
    · have hnpos : ¬ 0 < H (gridPoint m v) i - gridPoint m v i := not_lt_of_ge hnon
      have hv : (v i).val ≠ 0 := by omega
      simp [hneg, hnpos, hv]
  obtain ⟨c, hc⟩ := lab k m hm L Llo Lhi
  let t0 : Fin k → Bool := fun _ => false
  let z := gridPoint m (smallVertex c t0)
  have zmem : z ∈ cube (α:=Fin k) := gridPoint_mem hm _
  refine ⟨z, zmem, ?_⟩
  intro i
  obtain ⟨tp, htp⟩ := (hc i).1
  obtain ⟨tn, htn⟩ := (hc i).2
  have near (t : Fin k → Bool) : dist (gridPoint m (smallVertex c t)) z < r :=
    lt_of_le_of_lt (gridPoint_vertex_near hm c t t0) hfine
  have signfalse {v : Fin k → Fin (m+1)} {i : Fin k}
      (h : L v i = false) : 0 ≤ H (gridPoint m v) i - gridPoint m v i := by
    dsimp [L] at h
    split at h <;> rename_i h' 
    · contradiction
    · exact le_of_not_gt h'
  have signtrue {v : Fin k → Fin (m+1)} {i : Fin k}
      (h : L v i = true) : H (gridPoint m v) i - gridPoint m v i ≤ 0 := by
    dsimp [L] at h
    split at h <;> rename_i h'
    · exact le_of_lt h'
    · split at h <;> rename_i h''
      · contradiction
      · exact le_of_not_gt h''
  exact ⟨⟨_, gridPoint_mem hm _, near tp, signfalse htp⟩,
    ⟨_, gridPoint_mem hm _, near tn, signtrue htn⟩⟩
end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/GridReduce.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/CubicalParity.lean
open Set Function
open scoped BigOperators
namespace NashSupport
local notation "B" => ZMod 2
open CharTwo
lemma tel {N : ℕ} (R : Fin (N+1) → B) :
 ((∑ j : Fin N, (R j.castSucc + R j.succ)) + R (Fin.last N)) = R 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    -- inspect
    have h := ih (fun x : Fin (N+1) => R x.castSucc)
    -- simplify cast
    have hlast : (Fin.last N).succ = (Fin.last (N+1)) := rfl
    -- normalize using h and characteristic two
    change (∑ j : Fin N, (R j.castSucc.castSucc + R j.castSucc.succ)) +
        R (Fin.last N).castSucc = R (0 : Fin (N+2)) at h
    rw [← h]
    -- assoc and cancel; lastN succ definally final
    have heq : R (Fin.last N).succ = R (Fin.last (N+1)) := rfl
    rw [heq]
    have hc (x y : B) : x + y + y = x := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    -- reassociate
    simp [add_assoc, CharTwo.add_self_eq_zero]


def parityTop {k : ℕ} {V : Type*} (a : V → Fin k → B) (v : ℕ → V) : B :=
 ∏ i : Fin k, (a (v i.val) i + a (v (i.val+1)) i)
def parityTail {k : ℕ} {V : Type*} (a : V → Fin (k+1) → B) : V → Fin k → B :=
 fun x i => a x i.succ
def paritySkip {N : ℕ} {V : Type*} (v : ℕ → V) (j : Fin (N+1)) : ℕ → V :=
 fun r => if r < j.val then v r else v (r+1)
lemma parityTop_succ {k} {V : Type*} (a : V → Fin (k+1) → B) (v : ℕ → V) :
 parityTop a v = (a (v 0) 0 + a (v 1) 0) * parityTop (parityTail a) (fun r => v (r+1)) := by
 unfold parityTop parityTail
 rw [Fin.prod_univ_succ]
 rfl
lemma paritySkip_zero {N} {V : Type*} (v : ℕ → V) : paritySkip (N:=N) v (0 : Fin (N+1)) = (fun r => v (r+1)) := by
 funext r; simp [paritySkip]
lemma paritySkip_one0 {N} {V : Type*} (v : ℕ → V) (hN : 0 < N) :
 paritySkip (N:=N) v (⟨1, Nat.lt_succ_iff.2 hN⟩ : Fin (N+1)) 0 = v 0 := by simp [paritySkip]
-- general nested shift
lemma paritySkip_shift {N : ℕ} {V : Type*} (v : ℕ → V)
 (j : Fin (N+1)) :
 (fun r => paritySkip (N:=N+1) v j.succ (r+1)) =
   paritySkip (N:=N) (fun r => v (r+1)) j := by
 funext r
 simp [paritySkip]

-- cocycle experiment
lemma parityTop_cocycle {k : ℕ} {V : Type*} (a : V → Fin k → B) (v : ℕ → V) :
 (∑ j : Fin (k+2), parityTop a (paritySkip (N:=k+1) v j)) = 0 := by
 induction k generalizing V with
 | zero =>
   simp [parityTop]
 | succ k ih =>
   rw [Fin.sum_univ_succ]
   rw [Fin.sum_univ_succ]
   simp_rw [parityTop_succ]
   -- normalize skipped coordinates
   simp [paritySkip]
   let u : ℕ → V := fun r => v (r+1)
   have hseq (x : Fin (k+1)) :
       (fun r : ℕ => if r ≤ x.val then v (r+1) else v (r+1+1)) =
         paritySkip (N:=k+1) u x.succ := by
     funext r
     simp [paritySkip, u]
   simp_rw [hseq]

   rw [← Finset.mul_sum]
   have hh := ih (parityTail a) u
   rw [Fin.sum_univ_succ] at hh
   rw [paritySkip_zero] at hh
   change parityTop (parityTail a) (fun r => v (r+1+1)) +
     (∑ x : Fin (k+1), parityTop (parityTail a) (paritySkip (N:=k+1) u x.succ)) = 0 at hh
   -- elementary algebra: d12*T + d02*T + d01*sum; sum = T
   have hrel : (∑ x : Fin (k+1), parityTop (parityTail a) (paritySkip (N:=k+1) u x.succ)) =
       parityTop (parityTail a) (fun r => v (r+1+1)) := by
     -- from T+S=0 in char2
     have := hh
     -- add T; simp
     have hcancel (x y : B) (h:x+y=0) : y=x := by
       calc y = y + 0 := (add_zero y).symm
            _ = y + (x+x) := by rw [CharTwo.add_self_eq_zero]
            _ = x + y + x := by ac_rfl
            _ = 0 + x := by rw [h]
            _ = x := zero_add x
     exact hcancel _ _ hh
   rw [hrel]
   -- distributivity, char2
   ring_nf
   simp [CharTwo.two_eq_zero]

def parityFace {n} {V : Type*} (a : V → Fin (n+1) → B) (v:ℕ→V) : B :=
 a (v 0) 0 * parityTop (parityTail a) v
lemma weight_boundary_identity {n} {V : Type*} (a : V → Fin (n+1) → B) (v:ℕ→V) :
 parityTop a v = ∑ j:Fin (n+2), parityFace a (paritySkip (N:=n+1) v j) := by
 rw [Fin.sum_univ_succ]
 unfold parityFace
 rw [parityTop_succ]
 -- simp skip values
 simp [paritySkip]
 rw [paritySkip_zero]
 rw [← Finset.mul_sum]
 have h := parityTop_cocycle (parityTail a) v
 rw [Fin.sum_univ_succ] at h
 rw [paritySkip_zero] at h
 have hcancel (x y : B) (h:x+y=0) : y=x := by
       calc y = y + 0 := (add_zero y).symm
            _ = y + (x+x) := by rw [CharTwo.add_self_eq_zero]
            _ = x + y + x := by ac_rfl
            _ = 0 + x := by rw [h]
            _ = x := zero_add x
 have hs : (∑ i : Fin (n+1), parityTop (parityTail a) (paritySkip (N:=n+1) v i.succ)) =
     parityTop (parityTail a) (fun r => v (r+1)) := hcancel _ _ h
 rw [hs]
 ring
lemma swap_adj_lt {k r : ℕ} (hr0 : 0 < r) (hrk : r < k)
 (q : Fin k) (z : ℕ) (hz : z ≠ r) :
   (((Equiv.swap (⟨r-1, by omega⟩ : Fin k) (⟨r, hrk⟩ : Fin k)) q).val < z) =
     (q.val < z) := by
 let l : Fin k := ⟨r-1, by omega⟩
 let h : Fin k := ⟨r, hrk⟩
 change (((Equiv.swap l h) q).val < z) = _
 rw [Equiv.swap_apply_def]
 split <;> rename_i hq
 · subst q
   change (r < z) = (r-1 < z)
   apply propext
   omega
 · split <;> rename_i hq'
   · subst q
     change (r-1 < z) = (r < z)
     apply propext
     omega
   · rfl
open Function
-- import actual defs? pathVert from file not Scratch. define pathVert
 def pathVert {k m : ℕ} (c : Fin k → Fin m) (p : Equiv.Perm (Fin k))
    (r : ℕ) : Fin k → Fin (m+1) := fun i =>
  ⟨(c i).val + (if (p.symm i).val < r then 1 else 0), by
    have h := (c i).isLt
    split <;> omega⟩
lemma skip_path_swap {k m r : ℕ} (hr0:0<r) (hrk:r<k)
 (c : Fin k → Fin m) (p : Equiv.Perm (Fin k)) :
 paritySkip (N:=k) (pathVert c p)
    (⟨r, by omega⟩ : Fin (k+1)) =
 paritySkip (N:=k) (pathVert c ((Equiv.swap
       (⟨r-1, by omega⟩ : Fin k) (⟨r, hrk⟩ : Fin k)).trans p))
    (⟨r, by omega⟩ : Fin (k+1)) := by
 funext s i
 unfold paritySkip pathVert
 dsimp
 -- compare cutoff index t
 have ht : (if s < r then s else s+1) ≠ r := by
   split <;> omega
 -- simp paritySkip if
 split <;> rename_i hs <;> dsimp
 · have key := swap_adj_lt hr0 hrk (p.symm i) s (by omega)
   -- need composite symm
   simp at key ⊢
   -- try
   have := key
   by_cases hq : (p.symm i).val < s
   · have hq' : ((Equiv.swap (⟨r-1, by omega⟩ : Fin k) ⟨r, hrk⟩) (p.symm i)).val < s := key.mpr hq
     simp [hq, hq']
   · have hq' : ¬ ((Equiv.swap (⟨r-1, by omega⟩ : Fin k) ⟨r, hrk⟩) (p.symm i)).val < s := fun t => hq (key.mp t)
     simp [hq, hq']
 · have key := swap_adj_lt hr0 hrk (p.symm i) (s+1) (by omega)
   simp at key ⊢
   by_cases hq : (p.symm i).val ≤ s
   · have hq' : ((Equiv.swap (⟨r-1, by omega⟩ : Fin k) ⟨r, hrk⟩) (p.symm i)).val ≤ s := key.mpr hq
     simp [hq, hq']
   · have hq' : ¬ ((Equiv.swap (⟨r-1, by omega⟩ : Fin k) ⟨r, hrk⟩) (p.symm i)).val ≤ s := fun t => hq (key.mp t)
     simp [hq, hq']
lemma paired_sum {k m r : ℕ} (hr0:0<r) (hrk:r<k)
 (c : Fin k → Fin m) (F : (ℕ → (Fin k → Fin (m+1))) → B) :
 (∑ p : Equiv.Perm (Fin k),
      F (paritySkip (N:=k) (pathVert c p) (⟨r, by omega⟩ : Fin (k+1)))) = 0 := by
 classical
 let τ : Equiv.Perm (Fin k) := Equiv.swap
       (⟨r-1, by omega⟩ : Fin k) (⟨r, hrk⟩ : Fin k)
 let g : Equiv.Perm (Fin k) → Equiv.Perm (Fin k) := fun p => τ.trans p
 let f : Equiv.Perm (Fin k) → B := fun p =>
      F (paritySkip (N:=k) (pathVert c p) (⟨r, by omega⟩ : Fin (k+1)))
 -- convert to finset
 classical
 change Finset.univ.sum f = 0
 apply Finset.sum_involution (s:= Finset.univ)
    (fun p _ => g p)
 · intro p hp
   have he : f p = f (g p) := by
     apply congrArg F
     exact skip_path_swap hr0 hrk c p
   change f p + f (g p) = 0
   rw [← he]
   exact CharTwo.add_self_eq_zero _
 · intro p hp hn
   intro eq
   have e0 : τ.trans p = p := eq
   have e1 : τ = Equiv.refl _ := by
     apply Equiv.ext
     intro x
     have ee := DFunLike.congr_fun e0 x
     exact p.injective (by simpa using ee)
   have diff : τ (⟨r-1, by omega⟩ : Fin k) = (⟨r, hrk⟩ : Fin k) := by
     change (Equiv.swap (⟨r-1, by omega⟩ : Fin k) ⟨r, hrk⟩) _ = _
     simp
   rw [e1] at diff
   have valbad := congrArg Fin.val diff
   simp at valbad
   omega
 · intro p hp; simp
 · intro p hp
   change τ.trans (τ.trans p) = p
   -- swap involution
   apply Equiv.ext
   intro x
   change p (τ (τ x)) = p x
   rw [show τ (τ x) = x by exact (Equiv.swap_apply_self _ _ _)]


/-- Cup degree, one weight per monotone simplex in every small cube. -/
def gridDegree {k m : ℕ}
 (a : (Fin k → Fin (m+1)) → Fin k → ZMod 2) : ZMod 2 :=
 ∑ c : (Fin k → Fin m), ∑ p : Equiv.Perm (Fin k),
    parityTop a (pathVert c p)

/-- Stokes on the triangulation before the cancellations. This clean form is
 often convenient: interior faces are paired by `paired_sum` below. -/
lemma gridDegree_boundary {n m : ℕ}
 (a : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → ZMod 2) :
 gridDegree a =
   ∑ c : (Fin (n+1) → Fin m), ∑ p : Equiv.Perm (Fin (n+1)),
      ∑ j : Fin (n+2),
        parityFace a (paritySkip (N:=n+1) (pathVert c p) j) := by
 unfold gridDegree
 apply Finset.sum_congr rfl
 intro c hc
 apply Finset.sum_congr rfl
 intro p hp
 exact weight_boundary_identity _ _

/-- Every interior (non-end) face in one little cube occurs twice. The
 transposition of the two adjacent steps fixes the face. -/
lemma gridInteriorFaces {k m r : ℕ} (hr0 : 0 < r) (hrk : r < k)
 (c : Fin k → Fin m) (F : (ℕ → (Fin k → Fin (m+1))) → ZMod 2) :
 (∑ p : Equiv.Perm (Fin k),
      F (paritySkip (N:=k) (pathVert c p)
          (⟨r, by omega⟩ : Fin (k+1)))) = 0 :=
 paired_sum hr0 hrk c F

lemma boolBit_false {b : Bool} : (if b then (1 : ZMod 2) else 0) = 0 ↔ b = false := by
 cases b <;> decide
lemma boolBit_true {b : Bool} : (if b then (1 : ZMod 2) else 0) = 1 ↔ b = true := by
 cases b <;> decide

def bitsOf {k m : ℕ} (L : (Fin k → Fin (m+1)) → Fin k → Bool) :
 (Fin k → Fin (m+1)) → Fin k → ZMod 2 :=
 fun v i => if L v i then 1 else 0

/-- A nonzero simplex cup weight already gives the cell required in the
 cubical lemma. The vertices on its monotone path are small vertices. -/
lemma cell_of_weight {k m : ℕ}
 (L : (Fin k → Fin (m+1)) → Fin k → Bool)
 {c : Fin k → Fin m} {p : Equiv.Perm (Fin k)}
 (h : parityTop (bitsOf L) (pathVert c p) ≠ 0) :
 ∀ i : Fin k,
      (∃ t : Fin k → Bool, L (smallVertex c t) i = false) ∧
      (∃ t : Fin k → Bool, L (smallVertex c t) i = true) := by
 classical
 unfold parityTop at h
 have hn (i : Fin k) :
    bitsOf L (pathVert c p i.val) i +
        bitsOf L (pathVert c p (i.val+1)) i ≠ 0 := by
   intro hi
   apply h
   rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
 intro i
 have hn' := hn i
 have diff : L (pathVert c p i.val) i ≠
                L (pathVert c p (i.val+1)) i := by
   intro eq
   have beq : bitsOf L (pathVert c p i.val) i =
       bitsOf L (pathVert c p (i.val+1)) i := by simp [bitsOf, eq]
   rw [beq, CharTwo.add_self_eq_zero] at hn'
   exact hn' rfl
 have hv (r : ℕ) : pathVert c p r =
      smallVertex c (fun q => decide ((p.symm q).val < r)) := by
   funext q
   simp [pathVert, smallVertex]
 rcases h1 : L (pathVert c p i.val) i with _ | _
 · refine ⟨⟨(fun q => decide ((p.symm q).val < i.val)), ?_⟩, ⟨(fun q => decide ((p.symm q).val < (i.val+1))), ?_⟩⟩
   · simpa [hv i.val] using h1
   · have h2 : L (pathVert c p (i.val+1)) i = true := by
       cases hx : L (pathVert c p (i.val+1)) i
       · exact False.elim (diff (h1.trans hx.symm))
       · rfl
     simpa [hv (i.val+1)] using h2
 · refine ⟨⟨(fun q => decide ((p.symm q).val < (i.val+1))), ?_⟩, ⟨(fun q => decide ((p.symm q).val < i.val)), ?_⟩⟩
   · have h2 : L (pathVert c p (i.val+1)) i = false := by
       cases hx : L (pathVert c p (i.val+1)) i
       · rfl
       · exact False.elim (diff (h1.trans hx.symm))
     simpa [hv (i.val+1)] using h2
   · simpa [hv i.val] using h1

/-- The un-subdivided cube (`m=1`) is immediate. Useful endpoint for
 the parity argument and for checking the convention on booleans. -/
lemma cubicalLabel_unit (k : ℕ)
 (L : (Fin k → Fin (1+1)) → Fin k → Bool)
 (lo : ∀ v i, (v i).val = 0 → L v i = false)
 (hi : ∀ v i, (v i).val = 1 → L v i = true) :
 ∃ c : Fin k → Fin 1, ∀ i : Fin k,
      (∃ t : Fin k → Bool, L (smallVertex c t) i = false) ∧
      (∃ t : Fin k → Bool, L (smallVertex c t) i = true) := by
 let c : Fin k → Fin 1 := fun _ => 0
 refine ⟨c, ?_⟩
 intro i
 constructor
 · refine ⟨(fun _ => false), ?_⟩
   apply lo
   simp [smallVertex, c]
 · refine ⟨(fun _ => true), ?_⟩
   apply hi
   simp [smallVertex, c]

lemma cubicalLabel_zero : CubicalLabelLemma 0 := by
 intro m hm L lo hi
 let c : Fin 0 → Fin m := fun i => Fin.elim0 i
 exact ⟨c, fun i => Fin.elim0 i⟩

end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/CubicalParity.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/CubicalComplete.lean
open Set Function
open scoped BigOperators
namespace NashSupport
local notation "B" => ZMod 2
open CharTwo

/-- `parityFace` in dimension `n` only looks at its first `n+1`
arguments. Keeping this as a lemma rather than extending an equality of the
infinite lists makes exchanges of neighbouring small cubes painless. -/
lemma parityFace_congr_prefix {n : ℕ} {V : Type*}
    (a : V → Fin (n+1) → B) (v w : ℕ → V)
    (h : ∀ r : ℕ, r < n+1 → v r = w r) :
    parityFace a v = parityFace a w := by
  unfold parityFace
  rw [h 0 (by omega)]
  congr 1
  unfold parityTop parityTail
  apply Finset.prod_congr rfl
  intro i hi
  -- the tail has `n` factors
  rw [h i.val (by have := i.isLt; omega)]
  rw [h (i.val+1) (by have := i.isLt; omega)]

/-- A constant non-first coordinate kills a boundary cup. -/
lemma parityFace_zero_of_const {n : ℕ} {V : Type*}
    (a : V → Fin (n+1) → B) (v : ℕ → V)
    (q : Fin (n+1)) (hq : q ≠ 0) (z : B)
    (hz : ∀ r : ℕ, r < n+1 → a (v r) q = z) :
    parityFace a v = 0 := by
  have hpos : 0 < q.val := by
    by_contra hh
    have hv : q.val = 0 := Nat.eq_zero_of_not_pos hh
    have he : q = (⟨0, by omega⟩ : Fin (n+1)) := Fin.ext hv
    have he' : q = 0 := he
    exact hq he'
  have hlt : q.val - 1 < n := by
    have h := q.isLt
    omega
  let i : Fin n := ⟨q.val-1, hlt⟩
  have hiq : i.succ = q := by
    apply Fin.ext
    dsimp [i]
    omega
  unfold parityFace
  have hf : (parityTop (parityTail a) v) = 0 := by
    unfold parityTop parityTail
    have hz' :
        (a (v i.val) i.succ + a (v (i.val+1)) i.succ) = 0 := by
      rw [hiq, hz i.val (by dsimp [i]; omega),
          hz (i.val+1) (by dsimp [i]; omega),
          CharTwo.add_self_eq_zero]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hz']
  rw [hf, mul_zero]

/-- Values of the inverse rotation of a nonempty `Fin`. -/
lemma rot_inv_zero (n : ℕ) :
    (finRotate (n+1)).symm (0 : Fin (n+1)) = Fin.last n := by
  apply (finRotate (n+1)).injective
  simp [finRotate_last]

lemma rot_inv_succ (n t : ℕ) (ht : t < n) :
    (finRotate (n+1)).symm (⟨t+1, by omega⟩ : Fin (n+1)) =
      (⟨t, by omega⟩ : Fin (n+1)) := by
  apply (finRotate (n+1)).injective
  have h := finRotate_of_lt ht
  -- inverse/cast bounds in that lemma are definitionally the same `Fin`
  simpa using h.symm

lemma rot_zero (n : ℕ) :
    finRotate (n+1) (Fin.last n) = (0 : Fin (n+1)) := by
  exact finRotate_last
lemma rot_of_not_last (n t : ℕ) (ht : t < n) :
    finRotate (n+1) (⟨t, by omega⟩ : Fin (n+1)) =
      (⟨t+1, by omega⟩ : Fin (n+1)) := by
  simpa using (finRotate_of_lt ht)

/-- Moving the first direction of a monotone path to the end gives the same
face after crossing to the next little cube.  Only the prefix of length `k`
is asserted, exactly the part read by a face. -/
lemma face_first_next {n m : ℕ}
    (c c' : Fin (n+1) → Fin m) (p : Equiv.Perm (Fin (n+1)))
    (q : Fin (n+1)) (hq : q = p 0)
    (hcq : (c q).val + 1 < m)
    (hc' : c' = Function.update c q ⟨(c q).val+1, hcq⟩) :
    ∀ r : ℕ, r < n+1 →
      paritySkip (N:=n+1) (pathVert c p) (0 : Fin (n+2)) r =
      paritySkip (N:=n+1)
        (pathVert c' ((finRotate (n+1)).trans p)) (Fin.last (n+1)) r := by
  subst q
  subst c'
  intro r hr
  -- removing the first / last vertex
  simp [paritySkip, Fin.last, pathVert]
  -- the preceding simp leaves equality of dependent functions
  funext i
  -- position of this direction in the old word
  let t : Fin (n+1) := p.symm i
  have hp_back : p t = i := p.apply_symm_apply i
  have hqeq : (i = p 0) ↔ t.val = 0 := by
    constructor
    · intro h
      -- injectivity of p
      have : t = (0 : Fin (n+1)) := by
        apply p.injective
        simpa [hp_back] using h
      simpa [this]
    · intro h
      have ht0 : t = (0 : Fin (n+1)) := Fin.ext h
      simpa [t] using (congrArg (fun x => p x) ht0.symm).symm
  -- compare values as naturals
  apply Fin.ext
  have hrle : r ≤ n := by omega
  simp [hrle]
  change (c i).val + (if (p.symm i).val < r+1 then 1 else 0) =
    ((Function.update c (p 0) ⟨(c (p 0)).val+1, hcq⟩) i).val +
      (if ((((finRotate (n+1)).trans p).symm) i).val < r then 1 else 0)
  -- expose the inverse of the rotated word
  have hinv : (((finRotate (n+1)).trans p).symm i) =
        (finRotate (n+1)).symm t := by
    rfl
  rw [hinv]
  change (c i).val + (if t.val < r+1 then 1 else 0) =
    ((Function.update c (p 0) _) i).val +
      (if ((finRotate (n+1)).symm t).val < r then 1 else 0)
  by_cases ht0 : t.val = 0
  · have hiq : i = p 0 := (hqeq).2 ht0
    have ht' := rot_inv_zero n
    have htfin : t = (0 : Fin (n+1)) := Fin.ext ht0
    rw [htfin, rot_inv_zero]
    -- update at the moving coordinate
    simp [hiq]
    -- old indicator is on, the new last one is off on the retained prefix
    have : r ≤ n := by omega
    omega
  · have htp : 0 < t.val := by omega
    have hu : t.val - 1 < n := by have := t.isLt; omega
    let s : ℕ := t.val - 1
    have hslt : s < n := hu
    have htval : t.val = s+1 := by dsimp [s]; omega
    have htfin : t = (⟨s+1, by omega⟩ : Fin (n+1)) := Fin.ext htval
    rw [htfin, rot_inv_succ n s hslt]
    have hneq : i ≠ p 0 := fun hbad => ht0 ((hqeq).1 hbad)
    simp [hneq]
    -- remaining directions keep their lower endpoint; their old position is
    -- one later.

/-- The inverse move (last direction to first) across the preceding cube. -/
lemma face_last_prev {n m : ℕ}
    (c c' : Fin (n+1) → Fin m) (p : Equiv.Perm (Fin (n+1)))
    (q : Fin (n+1)) (hq : q = p (Fin.last n))
    (hcq : 0 < (c q).val)
    (hc' : c' = Function.update c q
          ⟨(c q).val-1, by have := hcq; have hm := (c q).isLt; omega⟩) :
    ∀ r : ℕ, r < n+1 →
      paritySkip (N:=n+1) (pathVert c p) (Fin.last (n+1)) r =
      paritySkip (N:=n+1)
        (pathVert c' ((finRotate (n+1)).symm.trans p)) (0 : Fin (n+2)) r := by
  subst q
  subst c'
  intro r hr
  -- now left keeps prefix, right drops first
  simp [paritySkip, Fin.last, pathVert]
  funext i
  let t : Fin (n+1) := p.symm i
  have hp_back : p t = i := p.apply_symm_apply i
  have hqeq : (i = p (Fin.last n)) ↔ t.val = n := by
    constructor
    · intro h
      have : t = Fin.last n := by
        apply p.injective
        simpa [hp_back] using h
      simpa [this, Fin.last]
    · intro h
      have ht0 : t = Fin.last n := by
        apply Fin.ext
        simpa [Fin.last] using h
      simpa [t] using (congrArg (fun x => p x) ht0.symm).symm
  apply Fin.ext
  have hrle : r ≤ n := by omega
  simp [hrle]
  change (c i).val + (if (p.symm i).val < r then 1 else 0) =
    ((Function.update c (p (Fin.last n)) _) i).val +
      (if (((((finRotate (n+1)).symm.trans p).symm) i).val < r+1) then 1 else 0)
  have hinv : ((((finRotate (n+1)).symm.trans p).symm) i) =
        finRotate (n+1) t := by
    rfl
  rw [hinv]
  change (c i).val + (if t.val < r then 1 else 0) =
    ((Function.update c (p (Fin.last n)) _) i).val +
      (if ((finRotate (n+1) t).val < r+1) then 1 else 0)
  by_cases htlast : t.val = n
  · have hiq : i = p (Fin.last n) := (hqeq).2 htlast
    have htfin : t = Fin.last n := by apply Fin.ext; simpa [Fin.last] using htlast
    rw [htfin, finRotate_last]
    have ha : 0 < (c (p (⟨n, by omega⟩ : Fin (n+1)))).val := by simpa [Fin.last] using hcq
    simp [hiq, Fin.last]
    have hz : ¬ n < r := by omega
    simp [hz]
    omega
  · have htless : t.val < n := by have := t.isLt; omega
    let s := t.val
    have htfin : t = (⟨s, by dsimp [s]; omega⟩ : Fin (n+1)) := rfl
    -- rotate sends a non-last slot up
    rw [htfin, rot_of_not_last n s (by dsimp [s]; omega)]
    have hneq : i ≠ p (Fin.last n) := fun hbad => htlast ((hqeq).1 hbad)
    simp [hneq]
    -- both lower corners agree here

end NashSupport
namespace NashSupport
/-- The one-dimensional row is the intermediate-value principle for a finite
word of Booleans. It is handy separately from the higher-dimensional parity
argument. -/
lemma cubicalLabel_one : CubicalLabelLemma 1 := by
  classical
  intro m hm L lo hi
  let v : (r : ℕ) → r < m+1 → (Fin 1 → Fin (m+1)) :=
    fun r h _ => ⟨r,h⟩
  have hex : ∃ r : ℕ, ∃ h : r < m+1, L (v r h) 0 = true := by
    refine ⟨m, ?_, ?_⟩
    · omega
    · apply hi
      rfl
  let r : ℕ := Nat.find hex
  have hrprop := Nat.find_spec hex
  obtain ⟨hrlt0, hrtrue0⟩ := hrprop
  have hrlt : r < m+1 := by simpa [r] using hrlt0
  have hrtrue : L (v r hrlt) 0 = true := by simpa [r] using hrtrue0
  clear hrtrue0 hrlt0
  have hrpos : 0 < r := by
    by_contra hh
    have hz : r = 0 := by omega
    have hrltz : 0 < m+1 := by omega
    have hvEq : v r hrlt = v 0 hrltz := by
      funext i
      apply Fin.ext
      exact hz
    have hf0 : L (v 0 hrltz) 0 = false := lo _ _ rfl
    have hf : L (v r hrlt) 0 = false := by rw [hvEq]; exact hf0
    rw [hf] at hrtrue
    contradiction
  have hrle : r ≤ m := by omega
  have hpredlt : r-1 < m := by omega
  let c : Fin 1 → Fin m := fun _ => ⟨r-1, hpredlt⟩
  refine ⟨c, ?_⟩
  intro i
  have ii : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  let t0 : Fin 1 → Bool := fun _ => false
  let t1 : Fin 1 → Bool := fun _ => true
  have he0 : smallVertex c t0 = v (r-1) (by omega) := by
    funext q
    apply Fin.ext
    simp [smallVertex, c, t0, v]
  have he1 : smallVertex c t1 = v r (by omega) := by
    funext q
    apply Fin.ext
    simp [smallVertex, c, t1, v]
    omega
  have hprev : L (v (r-1) (by omega)) 0 = false := by
    cases hx : L (v (r-1) (by omega)) 0 with
    | false => rfl
    | true =>
      have hless : r-1 < r := by omega
      have hx' : ∃ h : r-1 < m+1, L (v (r-1) h) 0 = true := by
        refine ⟨by omega, ?_⟩
        simpa using hx
      have hmin := Nat.find_min' hex hx'
      exfalso; omega
  refine ⟨⟨t0, ?_⟩, ⟨t1, ?_⟩⟩
  · rw [he0]
    exact hprev
  · rw [he1]
    exact hrtrue
end NashSupport
namespace NashSupport
local notation "B" => ZMod 2
lemma faceWeight_first_next {n m : ℕ}
    (a : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → B)
    (c : Fin (n+1) → Fin m) (p : Equiv.Perm (Fin (n+1)))
    (h : (c (p 0)).val + 1 < m) :
    parityFace a (paritySkip (N:=n+1) (pathVert c p) 0) =
    parityFace a
       (paritySkip (N:=n+1)
        (pathVert (Function.update c (p 0) ⟨(c (p 0)).val+1, h⟩)
          ((finRotate (n+1)).trans p)) (Fin.last (n+1))) := by
  apply parityFace_congr_prefix
  intro r hr
  exact face_first_next c
      (Function.update c (p 0) ⟨(c (p 0)).val+1, h⟩)
      p (p 0) rfl h rfl r hr

lemma faceWeight_last_prev {n m : ℕ}
    (a : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → B)
    (c : Fin (n+1) → Fin m) (p : Equiv.Perm (Fin (n+1)))
    (h : 0 < (c (p (Fin.last n))).val) :
    parityFace a (paritySkip (N:=n+1) (pathVert c p) (Fin.last (n+1))) =
    parityFace a
       (paritySkip (N:=n+1)
        (pathVert (Function.update c (p (Fin.last n))
              ⟨(c (p (Fin.last n))).val-1,
                by have := (c (p (Fin.last n))).isLt; omega⟩)
          ((finRotate (n+1)).symm.trans p)) 0) := by
  apply parityFace_congr_prefix
  intro r hr
  exact face_last_prev c
      (Function.update c (p (Fin.last n))
              ⟨(c (p (Fin.last n))).val-1,
                by have := (c (p (Fin.last n))).isLt; omega⟩)
      p (p (Fin.last n)) rfl h rfl r hr

/-- Every outside first face except the distinguished first coordinate has
zero cup weight. -/
lemma bits_first_outside_zero {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (hi : ∀ v i, (v i).val = m → L v i = true)
    (c : Fin (n+1) → Fin m) (p : Equiv.Perm (Fin (n+1)))
    (hout : (c (p 0)).val + 1 = m)
    (hne : p 0 ≠ (0 : Fin (n+1))) :
    parityFace (bitsOf L)
       (paritySkip (N:=n+1) (pathVert c p) 0) = 0 := by
  let q := p (0 : Fin (n+1))
  apply parityFace_zero_of_const (q:=q) (z:=1)
  · exact hne
  intro r hr
  have hpos : (p.symm q).val = 0 := by simp [q]
  have hv :
      ((paritySkip (N:=n+1) (pathVert c p) 0 r) q).val = m := by
    simp [paritySkip, pathVert, hpos]
    omega
  unfold bitsOf
  simp [hi _ _ hv]

/-- On a bottom last face the first bit on its starting vertex is zero when
that face is perpendicular to the first coordinate. Other perpendiculars
are killed in `bits_last_outside_zero` below. -/
lemma bits_last0_outside_zero {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (lo : ∀ v i, (v i).val = 0 → L v i = false)
    (c : Fin (n+1) → Fin m) (p : Equiv.Perm (Fin (n+1)))
    (hq : p (Fin.last n) = (0 : Fin (n+1)))
    (hout : (c (p (Fin.last n))).val = 0) :
    parityFace (bitsOf L)
       (paritySkip (N:=n+1) (pathVert c p) (Fin.last (n+1))) = 0 := by
  unfold parityFace
  have hpos : (p.symm (0 : Fin (n+1))).val = n := by
    have he : p.symm (0 : Fin (n+1)) = Fin.last n := by
      apply p.injective
      simp [hq]
    simpa [he, Fin.last]
  have hv :
      ((paritySkip (N:=n+1) (pathVert c p) (Fin.last (n+1)) 0)
         (0 : Fin (n+1))).val = 0 := by
    simp [paritySkip, pathVert, hpos, Fin.last, hq]
    -- the lower corner is the one retained
    simpa [hq] using hout
  have hbit : bitsOf L
      (paritySkip (N:=n+1) (pathVert c p) (Fin.last (n+1)) 0)
       (0 : Fin (n+1)) = 0 := by
    unfold bitsOf
    simp [lo _ _ hv]
  rw [hbit, zero_mul]

lemma bits_last_outside_zero {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (lo : ∀ v i, (v i).val = 0 → L v i = false)
    (c : Fin (n+1) → Fin m) (p : Equiv.Perm (Fin (n+1)))
    (hne : p (Fin.last n) ≠ (0 : Fin (n+1)))
    (hout : (c (p (Fin.last n))).val = 0) :
    parityFace (bitsOf L)
       (paritySkip (N:=n+1) (pathVert c p) (Fin.last (n+1))) = 0 := by
  let q := p (Fin.last n)
  apply parityFace_zero_of_const (q:=q) (z:=0)
  · exact hne
  intro r hr
  have hpos : (p.symm q).val = n := by
    have : p.symm q = Fin.last n := by simp [q]
    simpa [this, Fin.last]
  have hrle : r ≤ n := by omega
  have hv :
      ((paritySkip (N:=n+1) (pathVert c p) (Fin.last (n+1)) r) q).val = 0 := by
    simp [paritySkip, pathVert, hpos, Fin.last, hrle]
    simpa [q] using hout
  unfold bitsOf
  simp [lo _ _ hv]
end NashSupport
namespace NashSupport
local notation "B" => ZMod 2
/-- All the non-end faces in a fixed little cube cancel, even with the
non-symmetric cup weight. The transposition leaves the retained vertices
literally identical. This packages the part of Stokes which needs no
adjacent cube. -/
lemma faceWeights_mid_cancel {n m r : ℕ} (hr0 : 0 < r) (hrn : r < n+1)
    (a : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → B)
    (c : Fin (n+1) → Fin m) :
    (∑ p : Equiv.Perm (Fin (n+1)),
       parityFace a (paritySkip (N:=n+1) (pathVert c p)
                  (⟨r, by omega⟩ : Fin (n+2)))) = 0 := by
  exact paired_sum hr0 hrn c (parityFace a)

/-- A useful form of the last bottom case with no disjunction. -/
lemma bits_last_boundary_zero {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (lo : ∀ v i, (v i).val = 0 → L v i = false)
    (c : Fin (n+1) → Fin m) (p : Equiv.Perm (Fin (n+1)))
    (hout : (c (p (Fin.last n))).val = 0) :
    parityFace (bitsOf L)
       (paritySkip (N:=n+1) (pathVert c p) (Fin.last (n+1))) = 0 := by
  classical
  by_cases h : p (Fin.last n) = (0 : Fin (n+1))
  · exact bits_last0_outside_zero L lo c p h hout
  · exact bits_last_outside_zero L lo c p h hout
end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/CubicalComplete.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/CubicalFinish.lean
open Set Function
open scoped BigOperators
namespace NashSupport
local notation "B" => ZMod 2
open CharTwo
-- Cell together with a monotone ordering, in dimension `n+1`.
abbrev CP (n m : ℕ) := (Fin (n+1) → Fin m) × Equiv.Perm (Fin (n+1))

def firstW {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (z : CP n m) : B :=
  parityFace (bitsOf L)
    (paritySkip (N:=n+1) (pathVert z.1 z.2) (0 : Fin (n+2)))

def lastW {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (z : CP n m) : B :=
  parityFace (bitsOf L)
    (paritySkip (N:=n+1) (pathVert z.1 z.2) (Fin.last (n+1)))

def intFirst {n m : ℕ} (z : CP n m) : Prop :=
  (z.1 (z.2 (0 : Fin (n+1)))).val + 1 < m

def intLast {n m : ℕ} (z : CP n m) : Prop :=
  0 < (z.1 (z.2 (Fin.last n))).val

instance instDecidableIntFirst {n m} (z : CP n m) : Decidable (intFirst z) := by
  unfold intFirst; infer_instance
instance instDecidableIntLast {n m} (z : CP n m) : Decidable (intLast z) := by
  unfold intLast; infer_instance

-- Moving an upper (first) internal face to the lower (last) face of the
-- neighbouring little box.
def advanceCP {n m : ℕ} (z : {z : CP n m // intFirst z}) : {z : CP n m // intLast z} := by
  classical
  let c := z.1.1
  let p := z.1.2
  have h : (c (p (0 : Fin (n+1)))).val + 1 < m := z.2
  let c' : Fin (n+1) → Fin m :=
    Function.update c (p 0) ⟨(c (p 0)).val + 1, h⟩
  let p' : Equiv.Perm (Fin (n+1)) := (finRotate (n+1)).trans p
  refine ⟨(c', p'), ?_⟩
  unfold intLast
  have hp : p' (Fin.last n) = p 0 := by
    dsimp [p']
    simp [finRotate_last]
  rw [hp]
  simp [c']

def retreatCP {n m : ℕ} (z : {z : CP n m // intLast z}) : {z : CP n m // intFirst z} := by
  classical
  let c := z.1.1
  let p := z.1.2
  have h : 0 < (c (p (Fin.last n))).val := z.2
  have hlt : (c (p (Fin.last n))).val - 1 < m := by
    have := (c (p (Fin.last n))).isLt
    omega
  let c' : Fin (n+1) → Fin m :=
    Function.update c (p (Fin.last n)) ⟨(c (p (Fin.last n))).val - 1, hlt⟩
  let p' : Equiv.Perm (Fin (n+1)) := (finRotate (n+1)).symm.trans p
  refine ⟨(c', p'), ?_⟩
  unfold intFirst
  have hp : p' (0 : Fin (n+1)) = p (Fin.last n) := by
    dsimp [p']
    -- inverse rotation sends zero to last
    rw [rot_inv_zero n]
  rw [hp]
  dsimp [c']
  simp
  have hc := (c (p (Fin.last n))).isLt
  omega

lemma retreat_advance {n m : ℕ} (z : {z : CP n m // intFirst z}) :
    retreatCP (advanceCP z) = z := by
  classical
  -- equality of subtypes, then of pair
  apply Subtype.ext
  cases z with
  | mk z hz =>
    -- expose components
    cases z with
    | mk c p =>
      change (_, _) = (c, p)
      -- second component: inverse rotation followed by rotation
      have hp : ((finRotate (n+1)).symm.trans ((finRotate (n+1)).trans p)) = p := by
        ext i
        simp
      apply Prod.ext
      · funext i
        -- after increasing and then decreasing at coordinate p 0
        by_cases hi : i = p (0 : Fin (n+1))
        · subst i
          apply Fin.ext
          simp [advanceCP, retreatCP]
        · apply Fin.ext
          simp [advanceCP, retreatCP, hi]
      · exact hp

lemma advance_retreat {n m : ℕ} (z : {z : CP n m // intLast z}) :
    advanceCP (retreatCP z) = z := by
  classical
  apply Subtype.ext
  cases z with
  | mk z hz =>
    cases z with
    | mk c p =>
      change (_, _) = (c, p)
      have hp : ((finRotate (n+1)).trans ((finRotate (n+1)).symm.trans p)) = p := by
        ext i
        simp
      apply Prod.ext
      · have hidx : (((finRotate (n+1)).symm.trans p) (0 : Fin (n+1))) =
              p (Fin.last n) := by
            change p ((finRotate (n+1)).symm (0 : Fin (n+1))) = _
            rw [rot_inv_zero n]
        have hlt :
            ((Function.update c (p (Fin.last n))
                ⟨(c (p (Fin.last n))).val-1, by
                   have := (c (p (Fin.last n))).isLt; omega⟩)
               (((finRotate (n+1)).symm.trans p) 0)).val + 1 < m := by
          rw [hidx]
          simp
          have hh : 0 < (c (p (Fin.last n))).val := hz
          have hhm := (c (p (Fin.last n))).isLt
          omega
        change
          (Function.update
             (Function.update c (p (Fin.last n))
                ⟨(c (p (Fin.last n))).val - 1, _⟩)
             (((finRotate (n+1)).symm.trans p) 0)
                ⟨((Function.update c (p (Fin.last n))
                   ⟨(c (p (Fin.last n))).val-1, by
                     have := (c (p (Fin.last n))).isLt; omega⟩)
                    (((finRotate (n+1)).symm.trans p) 0)).val + 1, hlt⟩) = c
        simp [hidx]
        apply Fin.ext
        have hpos : 0 < (c (p (Fin.last n))).val := hz
        simp
        omega

      · exact hp

def faceEquiv {n m : ℕ} : {z : CP n m // intFirst z} ≃ {z : CP n m // intLast z} where
  toFun := advanceCP
  invFun := retreatCP
  left_inv := retreat_advance
  right_inv := advance_retreat

lemma first_to_last {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (z : {z : CP n m // intFirst z}) :
    firstW L z.1 = lastW L (advanceCP z).1 := by
  classical
  rcases z with ⟨⟨c,p⟩, h⟩
  -- the geometric common face
  exact faceWeight_first_next (bitsOf L) c p h

/-- The sum of all first internal-face weights is the sum of all last
internal-face weights. -/
lemma sum_int_faces {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool) :
    (∑ z : {z : CP n m // intFirst z}, firstW L z.1) =
    (∑ z : {z : CP n m // intLast z}, lastW L z.1) := by
  classical
  exact Fintype.sum_equiv (faceEquiv (n:=n) (m:=m))
    _ _ (fun z => first_to_last L z)

-- After summing over the permutations, the middle faces in each cube
-- disappear.  This is the clean endpoint form of Stokes on the grid.
lemma gridDegree_end {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool) :
    gridDegree (bitsOf L) =
      ∑ z : CP n m, (firstW L z + lastW L z) := by
  classical
  rw [gridDegree_boundary (a:=bitsOf L)]
  -- work cube by cube, commuting the permutation and face sums
  -- then each middle face sum is zero.
  have each (c : Fin (n+1) → Fin m) :
      (∑ p : Equiv.Perm (Fin (n+1)),
        ∑ j : Fin (n+2),
          parityFace (bitsOf L)
             (paritySkip (N:=n+1) (pathVert c p) j)) =
      (∑ p : Equiv.Perm (Fin (n+1)),
          (firstW L (c,p) + lastW L (c,p))) := by
    -- put faces outside: sum j, sum p
    rw [Finset.sum_comm]
    -- split j=0 and the rest, then split the last among the rest
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_castSucc]
    -- middle indices are the succ r with r : Fin n
    have hzmid :
        (∑ i : Fin n,
          (∑ p : Equiv.Perm (Fin (n+1)),
            parityFace (bitsOf L)
              (paritySkip (N:=n+1) (pathVert c p) (i.castSucc.succ)))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      -- value of this successor is between 0 and n+1
      have h0 : 0 < i.val + 1 := by omega
      have h1 : i.val + 1 < n+1 := by have := i.isLt; omega
      have he : (⟨i.val+1, by omega⟩ : Fin (n+2)) = i.castSucc.succ := by
        apply Fin.ext
        rfl
      have hh := (faceWeights_mid_cancel (n:=n) (m:=m)
          (r:=i.val+1) h0 h1 (bitsOf L) c)
      rw [he] at hh
      exact hh
    rw [hzmid]
    -- now only the endpoint sums
    simp [firstW, lastW, Fin.last, Finset.sum_add_distrib,
      add_assoc, add_left_comm, add_comm]
  -- replace every cube by its endpoint expression
  simp_rw [each]
  -- and fold the pair into the product type
  symm
  apply Fintype.sum_prod_type

/-- Endpoint cancellations leave, for a nonempty subdivision, just the
upper faces perpendicular to coordinate zero. We keep the remaining sum
as a subtype; this avoids any choice of enumeration. -/
lemma gridDegree_top {n m : ℕ} (hm : 0 < m)
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (lo : ∀ v i, (v i).val = 0 → L v i = false)
    (hi : ∀ v i, (v i).val = m → L v i = true) :
    gridDegree (bitsOf L) =
      ∑ z : {z : CP n m // ¬ intFirst z}, firstW L z.1 := by
  classical
  rw [gridDegree_end L]
  rw [Finset.sum_add_distrib]
  -- split the first and last sums into internal and external parts
  have hf := Fintype.sum_subtype_add_sum_subtype
      (intFirst (n:=n) (m:=m)) (firstW L)
  have hb := Fintype.sum_subtype_add_sum_subtype
      (intLast (n:=n) (m:=m)) (lastW L)
  -- every external last face is a bottom face, hence zero
  have hzero : (∑ z : {z : CP n m // ¬ intLast z}, lastW L z.1) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    rcases z with ⟨⟨c,p⟩, hn⟩
    have hh : (c (p (Fin.last n))).val = 0 := by
      unfold intLast at hn
      simp at hn
      omega
    exact bits_last_boundary_zero L lo c p hh
  rw [hzero, add_zero] at hb
  have hsame := sum_int_faces L
  -- all sums live in characteristic two, so the two identical internal
  -- pieces cancel.
  calc
    (∑ z : CP n m, firstW L z) + ∑ z : CP n m, lastW L z =
        ((∑ z : {z : CP n m // intFirst z}, firstW L z.1) +
          (∑ z : {z : CP n m // ¬ intFirst z}, firstW L z.1)) +
          (∑ z : {z : CP n m // intLast z}, lastW L z.1) := by rw [hf, hb]
    _ = ∑ z : {z : CP n m // ¬ intFirst z}, firstW L z.1 := by
      rw [hsame]
      -- x + t + x = t in characteristic two
      have hc (x y : B) : (x + y) + x = y := by
        rw [add_assoc]
        rw [add_comm y x]
        simp [CharTwo.add_self_eq_zero]
      apply hc

lemma gridDegree_top_zero {n m : ℕ} (hm : 0 < m)
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (lo : ∀ v i, (v i).val = 0 → L v i = false)
    (hi : ∀ v i, (v i).val = m → L v i = true) :
    gridDegree (bitsOf L) =
      ∑ z : {z : CP n m // ¬ intFirst z ∧ z.2 (0 : Fin (n+1)) = 0},
        firstW L z.1 := by
  classical
  rw [gridDegree_top hm L lo hi]
  -- split that subtype once more according to the first direction
  let X := {z : CP n m // ¬ intFirst z}
  let P : X → Prop := fun z => z.1.2 (0 : Fin (n+1)) = 0
  have hs := Fintype.sum_subtype_add_sum_subtype P
       (fun z : X => firstW L z.1)
  have hbad : (∑ z : {z : X // ¬ P z}, firstW L z.1.1) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    rcases z with ⟨⟨⟨c,p⟩, houter⟩, hp⟩
    have htop : (c (p (0 : Fin (n+1)))).val + 1 = m := by
      unfold intFirst at houter
      simp at houter
      have hc := (c (p (0 : Fin (n+1)))).isLt
      omega
    have hne : p (0 : Fin (n+1)) ≠ 0 := by
      unfold P at hp
      simp at hp
      exact hp
    exact bits_first_outside_zero L hi c p htop hne
  rw [hbad, add_zero] at hs
  -- identify the nested subtype with the displayed conjunction
  let e : {z : X // P z} ≃
      {z : CP n m // ¬ intFirst z ∧ z.2 (0 : Fin (n+1)) = 0} :=
    { toFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      left_inv := by intro z; cases z with | mk z h => cases z; rfl
      right_inv := by intro z; cases z; rfl }
  -- hs reads small + 0 = the original sum
  symm at hs
  calc
    _ = ∑ z : {z : X // P z}, firstW L z.1.1 := hs
    _ = _ := Fintype.sum_equiv e _ _ (by intro z; rfl)

lemma label_of_degree {k m : ℕ}
    (L : (Fin k → Fin (m+1)) → Fin k → Bool)
    (h : gridDegree (bitsOf L) ≠ 0) :
    ∃ c : Fin k → Fin m, ∀ i : Fin k,
      (∃ t : Fin k → Bool, L (smallVertex c t) i = false) ∧
      (∃ t : Fin k → Bool, L (smallVertex c t) i = true) := by
  classical
  unfold gridDegree at h
  -- if every simplex had zero weight the finite sum would vanish
  have hn : ∃ c : Fin k → Fin m, ∃ p : Equiv.Perm (Fin k),
      parityTop (bitsOf L) (pathVert c p) ≠ 0 := by
    by_contra hh
    push_neg at hh
    apply h
    simp [hh]
  obtain ⟨c,p,hp⟩ := hn
  exact ⟨c, cell_of_weight L hp⟩

/-- The surviving first face really is the ordinary tail weight on that
upper facet.  This explicit version is useful for passing to dimension `n`:
the path is simply the old path with its first (coordinate-zero) step
removed. -/
lemma firstW_top_tail {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (hi : ∀ v i, (v i).val = m → L v i = true)
    (c : Fin (n+1) → Fin m) (p : Equiv.Perm (Fin (n+1)))
    (ht : (c (p 0)).val + 1 = m)
    (h0 : p (0 : Fin (n+1)) = 0) :
    firstW L (c,p) =
      parityTop (parityTail (bitsOf L)) (fun r => pathVert c p (r+1)) := by
  classical
  unfold firstW parityFace
  -- removing vertex zero gives the shifted path
  rw [paritySkip_zero]
  have hp : (p.symm (0 : Fin (n+1))).val = 0 := by
    have hh : p.symm (0 : Fin (n+1)) = 0 := by
      apply p.injective
      simp [h0]
    simp [hh]
  have hv : ((pathVert c p 1) (0 : Fin (n+1))).val = m := by
    simp [pathVert, hp, h0]
    simpa [h0] using ht
  have hb : bitsOf L (pathVert c p 1) (0 : Fin (n+1)) = 1 := by
    unfold bitsOf
    simp [hi _ _ hv]
  rw [hb, one_mul]

/-- Insert the fixed top coordinate. The other coordinates are enumerated
by successors, so that no casts occur in the next induction step. -/
def topEmbed {n m : ℕ} (v : Fin n → Fin (m+1)) :
    Fin (n+1) → Fin (m+1) :=
  Fin.cases ⟨m, Nat.lt_succ_self _⟩ v

def topLabel {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool) :
    (Fin n → Fin (m+1)) → Fin n → Bool :=
  fun v i => L (topEmbed v) i.succ

lemma topEmbed_succ {n m : ℕ} (v : Fin n → Fin (m+1)) (i : Fin n) :
    topEmbed v i.succ = v i := by
  simp [topEmbed]
lemma topEmbed_zero {n m : ℕ} (v : Fin n → Fin (m+1)) :
    topEmbed v 0 = (⟨m, Nat.lt_succ_self _⟩ : Fin (m+1)) := by
  simp [topEmbed]

lemma topLabel_faces {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (lo : ∀ v i, (v i).val = 0 → L v i = false)
    (hi : ∀ v i, (v i).val = m → L v i = true) :
    (∀ v i, (v i).val = 0 → topLabel L v i = false) ∧
    (∀ v i, (v i).val = m → topLabel L v i = true) := by
  constructor
  · intro v i h
    apply lo
    simpa [topEmbed_succ] using h
  · intro v i h
    apply hi
    simpa [topEmbed_succ] using h

end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/CubicalFinish.lean

-- BEGIN INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Tail.lean
open Set Function
open scoped BigOperators
namespace NashSupport
local notation "B" => ZMod 2
open CharTwo

/-- A permutation with a new fixed element in the zero position.  We use
`decomposeFin` so that the remaining positions are literally successors. -/
def tailLift {n : ℕ} (q : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  Equiv.Perm.decomposeFin.symm ((0 : Fin (n+1)), q)

@[simp] lemma tailLift_zero {n} (q : Equiv.Perm (Fin n)) :
    tailLift q (0 : Fin (n+1)) = 0 := by
  simp [tailLift]
@[simp] lemma tailLift_succ {n} (q : Equiv.Perm (Fin n)) (i : Fin n) :
    tailLift q i.succ = (q i).succ := by
  simpa [tailLift] using
    (Equiv.Perm.decomposeFin_symm_apply_succ q (0 : Fin (n+1)) i)

@[simp] lemma tailLift_symm {n} (q : Equiv.Perm (Fin n)) :
    (tailLift q).symm = tailLift q.symm := by
  apply Equiv.ext
  intro x
  refine Fin.cases ?_ ?_ x
  · -- zero
    have hz := tailLift_zero (q:=q.symm)
    -- inverse also fixes zero
    apply (tailLift q).injective
    simp
  · intro i
    apply (tailLift q).injective
    simp

@[simp] lemma decomp_zero {n} (q : Equiv.Perm (Fin n)) :
    Equiv.Perm.decomposeFin (tailLift q) = ((0 : Fin (n+1)), q) := by
  simp [tailLift]

/-- The lower corner of a top facet: zero coordinate is `m-1`. -/
def tailCorner {n m : ℕ} (hm : 0 < m) (d : Fin n → Fin m) :
    Fin (n+1) → Fin m :=
  Fin.cases ⟨m-1, by omega⟩ d
@[simp] lemma tailCorner_zero {n m} (hm:0 < m) (d:Fin n → Fin m) :
    tailCorner hm d 0 = (⟨m-1, by omega⟩ : Fin m) := by
  simp [tailCorner]
@[simp] lemma tailCorner_succ {n m} (hm:0 < m) (d:Fin n → Fin m) (i:Fin n) :
    tailCorner hm d i.succ = d i := by simp [tailCorner]

/-- Cells of the surviving top facet. -/
abbrev TopCells (n m : ℕ) :=
  {z : CP n m // ¬ intFirst z ∧ z.2 (0 : Fin (n+1)) = 0}

/-- Build a surviving cell from a tail cell. -/
def packTop {n m : ℕ} (hm:0 < m)
    (w : (Fin n → Fin m) × Equiv.Perm (Fin n)) : TopCells n m := by
  classical
  let c := tailCorner hm w.1
  let p := tailLift w.2
  refine ⟨(c,p), ?_, ?_⟩
  · intro hbad
    unfold intFirst at hbad
    have hp : p (0 : Fin (n+1)) = 0 := by simp [p]
    -- first coordinate equals m-1
    rw [hp] at hbad
    change (c (0 : Fin (n+1))).val + 1 < m at hbad
    simp [c, tailCorner] at hbad
    omega
  · simp [p]

/-- Reading the zero value of a decomposed permutation. -/
lemma decompose_zero_eq {n} (p : Equiv.Perm (Fin (n+1))) :
    (Equiv.Perm.decomposeFin p).1 = p (0 : Fin (n+1)) := by
  let z := Equiv.Perm.decomposeFin p
  have hz : Equiv.Perm.decomposeFin.symm (z.1,z.2) = p := by
    exact (Equiv.Perm.decomposeFin).symm_apply_apply p
  have h0 := Equiv.Perm.decomposeFin_symm_apply_zero z.1 z.2
  -- `h0` evaluates the inverse word at zero
  calc
    (Equiv.Perm.decomposeFin p).1 = z.1 := rfl
    _ = (Equiv.Perm.decomposeFin.symm (z.1,z.2))
          (0 : Fin (n+1)) := h0.symm
    _ = p (0 : Fin (n+1)) := by rw [hz]

/-- Strip the first, fixed, coordinate and direction. -/
def unpackTop {n m : ℕ} (z : TopCells n m) :
    (Fin n → Fin m) × Equiv.Perm (Fin n) :=
  (fun i => z.1.1 i.succ, (Equiv.Perm.decomposeFin z.1.2).2)

lemma decompose_of_fix {n} (p : Equiv.Perm (Fin (n+1)))
    (hp : p (0 : Fin (n+1)) = 0) :
    tailLift ((Equiv.Perm.decomposeFin p).2) = p := by
  have h1 : (Equiv.Perm.decomposeFin p).1 = (0 : Fin (n+1)) := by
    rw [decompose_zero_eq p, hp]
  -- compare after `decomposeFin`
  apply (Equiv.Perm.decomposeFin).injective
  -- eta the pair
  apply Prod.ext
  · exact h1.symm
  · rfl

lemma pack_unpackTop {n m} (hm:0 < m) (z : TopCells n m) :
    packTop hm (unpackTop z) = z := by
  classical
  apply Subtype.ext
  rcases z with ⟨⟨c,p⟩, hn, hp⟩
  change (_ , _) = (c,p)
  have pp : tailLift (Equiv.Perm.decomposeFin p).2 = p :=
    decompose_of_fix p hp
  apply Prod.ext
  · -- corners; first coordinate is forced to be m-1
    funext i
    refine Fin.cases ?_ ?_ i
    · apply Fin.ext
      -- external means the first lower coordinate is the last cell
      have htop : (c (0 : Fin (n+1))).val + 1 = m := by
        unfold intFirst at hn
        simp at hn
        -- rewrite p0
        rw [hp] at hn
        have hc := (c (0 : Fin (n+1))).isLt
        omega
      simp [packTop, unpackTop, tailCorner]
      omega
    · intro j
      simp [packTop, unpackTop, tailCorner]
  · simpa [packTop, unpackTop] using pp

lemma unpack_packTop {n m} (hm:0 < m)
    (w : (Fin n → Fin m) × Equiv.Perm (Fin n)) :
    unpackTop (packTop hm w) = w := by
  classical
  rcases w with ⟨d,q⟩
  apply Prod.ext
  · funext i
    simp [unpackTop, packTop, tailCorner]
  · simp [unpackTop, packTop, tailLift]

/-- Equivalence between top cells and ordinary cells on the tail. -/
def topEquiv {n m : ℕ} (hm:0 < m) :
    ((Fin n → Fin m) × Equiv.Perm (Fin n)) ≃ TopCells n m where
  toFun := packTop hm
  invFun := unpackTop
  left_inv := unpack_packTop hm
  right_inv := pack_unpackTop hm

/-- The shifted vertex of a packed path is the embedded top-facet vertex. -/
lemma path_pack {n m : ℕ} (hm:0 < m) (d : Fin n → Fin m)
    (q : Equiv.Perm (Fin n)) (r : ℕ) :
    pathVert (tailCorner hm d) (tailLift q) (r+1) =
      topEmbed (pathVert d q r) := by
  classical
  funext i
  refine Fin.cases ?_ ?_ i
  · apply Fin.ext
    have hz : (((tailLift q).symm (0 : Fin (n+1))).val) = 0 := by
      rw [tailLift_symm]
      simp
    -- unfold the cutoff at coordinate zero
    simp [pathVert, topEmbed, tailCorner, hz]
    omega
  · intro j
    apply Fin.ext
    have hs : ((tailLift q).symm j.succ).val = ((q.symm j).succ).val := by
      rw [tailLift_symm]
      simp
    change (d j).val + (if ((tailLift q).symm j.succ).val < r+1 then 1 else 0) =
      (pathVert d q r j).val
    rw [hs]
    change (d j).val + (if (q.symm j).val + 1 < r+1 then 1 else 0) = _
    simp [pathVert]

/-- On a top vertex the tail bits are exactly the bits of `topLabel`. -/
lemma bits_top {n m : ℕ}
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (v : Fin n → Fin (m+1)) :
    (fun i : Fin n => parityTail (bitsOf L) (topEmbed v) i) =
      bitsOf (topLabel L) v := by
  funext i
  rfl

/-- Weight of a top path written as the ordinary degree weight of the
induced labelling. -/
lemma weight_pack {n m : ℕ} (hm:0 < m)
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool)
    (d : Fin n → Fin m) (q : Equiv.Perm (Fin n)) :
    parityTop (parityTail (bitsOf L))
       (fun r => pathVert (tailCorner hm d) (tailLift q) (r+1)) =
      parityTop (bitsOf (topLabel L)) (pathVert d q) := by
  classical
  -- identify the paths, then their bit maps
  have hp : (fun r => pathVert (tailCorner hm d) (tailLift q) (r+1)) =
      (fun r => topEmbed (pathVert d q r)) := by
    funext r
    exact path_pack hm d q r
  rw [hp]
  unfold parityTop
  apply Finset.prod_congr rfl
  intro i hi
  -- the factors use the same tail bit
  rfl

/-- The surviving top-facet sum is just the grid degree of the induced
labelling in one less dimension.  This is the reindexing step in the
cubical parity proof. -/
lemma top_sum_eq_degree {n m : ℕ} (hm:0 < m)
    (L : (Fin (n+1) → Fin (m+1)) → Fin (n+1) → Bool) :
    (∑ z : TopCells n m,
       parityTop (parityTail (bitsOf L))
          (fun r => pathVert z.1.1 z.1.2 (r+1))) =
      gridDegree (bitsOf (topLabel L)) := by
  classical
  -- sum over ordinary cells via the equivalence
  symm
  unfold gridDegree
  calc
    (∑ c : Fin n → Fin m, ∑ p : Equiv.Perm (Fin n),
        parityTop (bitsOf (topLabel L)) (pathVert c p)) =
      ∑ w : (Fin n → Fin m) × Equiv.Perm (Fin n),
        parityTop (bitsOf (topLabel L)) (pathVert w.1 w.2) := by
          symm
          exact Fintype.sum_prod_type _
    _ = _ := Fintype.sum_equiv (topEquiv hm) _ _ (by
      intro w
      rcases w with ⟨d,q⟩
      exact (weight_pack hm L d q).symm)



/-- The cup degree of a cubical Sperner labelling is one.  Proved by
repeatedly exposing the top zero-coordinate facet; `top_sum_eq_degree`
is the concrete reindexing of this facet. -/
theorem gridDegree_one :
    ∀ (k m : ℕ), 0 < m →
      ∀ L : (Fin k → Fin (m+1)) → Fin k → Bool,
       (∀ v i, (v i).val = 0 → L v i = false) →
       (∀ v i, (v i).val = m → L v i = true) →
       gridDegree (bitsOf L) = 1 := by
  classical
  intro k
  induction k with
  | zero =>
      intro m hm L lo hi
      simp [gridDegree, parityTop]
  | succ n ih =>
      intro m hm L lo hi
      rw [gridDegree_top_zero (n:=n) (m:=m) hm L lo hi]
      have hclean :
        (∑ z : TopCells n m, firstW L z.1) =
          (∑ z : TopCells n m,
            parityTop (parityTail (bitsOf L))
              (fun r => pathVert z.1.1 z.1.2 (r+1))) := by
        apply Finset.sum_congr rfl
        intro z hz
        rcases z with ⟨⟨c,p⟩, hout, hp⟩
        have ht : (c (p (0 : Fin (n+1)))).val + 1 = m := by
          unfold intFirst at hout
          simp at hout
          have hc := (c (p (0 : Fin (n+1)))).isLt
          omega
        exact firstW_top_tail L hi c p ht hp
      rw [hclean]
      rw [top_sum_eq_degree hm L]
      have hf := topLabel_faces (L:=L) lo hi
      exact ih m hm (topLabel L) hf.1 hf.2

end NashSupport

-- END INLINED FILE: Mathlib/Support/nash_equilibrium_exists_66a9baff3c/Tail.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval
namespace GameTheory

/-!
# Nash equilibrium existence theorem

§33 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. Every
finite `n`-player game in mixed strategies admits at least one Nash
equilibrium.

Nash gave two proofs: the 1950 one uses Brouwer's fixed-point theorem; the
1951 one uses Kakutani's set-valued generalization.

mathlib has `stdSimplex ℝ S` (the natural model of a mixed strategy) and the
standard finite-sum/product machinery, but **no game theory at all** —
there is no `Mathlib/GameTheory/` module, and `grep -ri nash`,
`mixed.strategy`, `best.response` returns nothing relevant. No formalization
of Nash equilibrium existence was found in any major proof assistant.
-/

open Set Function

/-- A **mixed strategy** for a player with finite pure-strategy set `S` is a
probability distribution on `S`: a non-negative function summing to `1`. -/
abbrev MixedStrategy (S : Type*) [Fintype S] : Set (S → ℝ) := stdSimplex ℝ S

/-- A **strategy profile** is a tuple assigning each of the `n` players a
pure strategy from their own set. -/
abbrev StrategyProfile (n : ℕ) (S : Fin n → Type*) : Type _ := ∀ i, S i

/-- The **expected payoff** to a player with payoff function `u` when each
player `j` plays the mixed strategy `σ j`. Sum over all pure-strategy
profiles, weighted by the product of marginal probabilities. -/
noncomputable def expectedPayoff {n : ℕ} {S : Fin n → Type*}
    [∀ i, Fintype (S i)]
    (u : StrategyProfile n S → ℝ) (σ : ∀ i, S i → ℝ) : ℝ :=
  ∑ s : StrategyProfile n S, (∏ i, σ i (s i)) * u s

/-- A profile of mixed strategies `σ` is a **Nash equilibrium** for the
payoff functions `u₀, …, uₙ₋₁` if (i) each `σ i` is a probability
distribution on `S i`, and (ii) no player `i` can strictly improve their
expected payoff by switching to a different mixed strategy `τ`, holding the
other players' strategies fixed. -/
def IsNashEquilibrium {n : ℕ} {S : Fin n → Type*} [∀ i, Fintype (S i)]
    (u : Fin n → StrategyProfile n S → ℝ) (σ : ∀ i, S i → ℝ) : Prop :=
  (∀ i, σ i ∈ MixedStrategy (S i)) ∧
    ∀ (i : Fin n) (τ : S i → ℝ), τ ∈ MixedStrategy (S i) →
      expectedPayoff (u i) (Function.update σ i τ) ≤
        expectedPayoff (u i) σ



end GameTheory
end LeanEval

open LeanEval.GameTheory
open Set Function
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem nash_equilibrium_exists {n : ℕ} {S : Fin n → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (u : Fin n → StrategyProfile n S → ℝ) :
    ∃ σ : ∀ i, S i → ℝ, IsNashEquilibrium u σ :=
/-ResultProofBegin-/by
  classical
  -- Work in the product of the affine simplexes as a subset of the ambient
  -- finite product vector space. Later the only topological input is a fixed
  -- point for this explicitly written continuous self map.
  let K : Set (∀ i, S i → ℝ) := {x | ∀ i, x i ∈ stdSimplex ℝ (S i)}
  let W (i : Fin n) (x : ∀ i, S i → ℝ) : ℝ := NashSupport.payoff (u i) x
  let V (i : Fin n) (x : ∀ i, S i → ℝ) (a : S i) : ℝ :=
    NashSupport.payoff (u i) (Function.update x i (Pi.single a 1))
  let T : (∀ i, S i → ℝ) → (∀ i, S i → ℝ) := fun x i a =>
    (x i a + max 0 (V i x a - W i x)) /
      (1 + ∑ b : S i, max 0 (V i x b - W i x))
  have hKne : K.Nonempty := by
    exact NashSupport.productSimplex_nonempty (A:=S)
  have hKco : Convex ℝ K := by
    exact NashSupport.productSimplex_convex (A:=S)
  have hKcp : IsCompact K := by
    exact NashSupport.productSimplex_compact (A:=S)
  have hmap : MapsTo T K K := by
    intro x hx i
    apply NashSupport.normalize_mem_simplex (p:=x i) (hp:=hx i)
       (d:= fun a : S i => max 0 (V i x a - W i x))
    intro a
    exact le_max_left _ _
  have hcon : Continuous T := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro a
    dsimp [T]
    have hW : Continuous (fun x : (∀ i, S i → ℝ) => W i x) := by
      dsimp [W]
      exact NashSupport.continuous_payoff (u i)
    have hV (b : S i) :
        Continuous (fun x : (∀ i, S i → ℝ) => V i x b) := by
      dsimp [V]
      exact NashSupport.continuous_payoff_pure (u i) i b
    have hd (b : S i) :
        Continuous (fun x : (∀ i, S i → ℝ) => max 0 (V i x b - W i x)) :=
      continuous_const.max ((hV b).sub hW)
    -- both numerator and denominator are finite continuous expressions
    have hxa : Continuous (fun x : (∀ i, S i → ℝ) => x i a) :=
      (continuous_apply a).comp (continuous_apply i)
    have hnum : Continuous (fun x : (∀ i, S i → ℝ) =>
        x i a + max 0 (V i x a - W i x)) := hxa.add (hd a)
    have hsum : Continuous (fun x : (∀ i, S i → ℝ) =>
        ∑ b : S i, max 0 (V i x b - W i x)) := by
      simpa using
        (continuous_finsetSum (Finset.univ : Finset (S i))
          (fun b _ => hd b))
    have hc : Continuous (fun _ : (∀ i, S i → ℝ) => (1:ℝ)) := continuous_const
    have hden : Continuous (fun x : (∀ i, S i → ℝ) =>
        1 + ∑ b : S i, max 0 (V i x b - W i x)) := hc.add hsum
    exact hnum.div hden (by
      intro x
      have hnon : 0 ≤ ∑ b : S i, max 0 (V i x b - W i x) :=
        Finset.sum_nonneg (fun b _ => le_max_left _ _)
      linarith)

  have h_exists : ∃ x : (∀ i, S i → ℝ), x ∈ K ∧ T x = x := by
    -- The remaining topological core is Brouwer in a finite-dimensional
    -- real vector space.  Everything above and below is the elementary
    -- reduction specific to games.
    have approx_on_product_simplex :
        ∀ (f : (∀ i, S i → ℝ) → (∀ i, S i → ℝ)),
          Continuous f → MapsTo f K K →
          ∀ ε : ℝ, 0 < ε → ∃ x ∈ K, dist (f x) x < ε := by
      -- Lift the product to the single standard simplex on the finite set of
      -- pure profiles.  Only Brouwer on an *ordinary* simplex remains.
      classical
      let Ω : Type _ := (∀ i, S i)
      let Δ : Set (Ω → ℝ) := stdSimplex ℝ Ω
      have simplex_core :
          ∀ (g : (Ω → ℝ) → (Ω → ℝ)),
            Continuous g → MapsTo g Δ Δ →
            ∀ δ : ℝ, 0 < δ → ∃ y ∈ Δ, dist (g y) y < δ := by
        have cube_core :
            ∀ (h : (Ω → ℝ) → (Ω → ℝ)), Continuous h →
              MapsTo h (NashSupport.cube (α:=Ω)) (NashSupport.cube (α:=Ω)) →
              ∀ d : ℝ, 0 < d → ∃ z ∈ NashSupport.cube (α:=Ω), dist (h z) z < d := by
          have fin_core :
              ∀ (k : ℕ), ∀ (H : (Fin k → ℝ) → (Fin k → ℝ)), Continuous H →
                MapsTo H (NashSupport.cube (α:=Fin k))
                  (NashSupport.cube (α:=Fin k)) →
                ∀ d : ℝ, 0 < d → ∃ z ∈ NashSupport.cube (α:=Fin k),
                  dist (H z) z < d := by
            intro k
            cases k with
            | zero =>
              intro H hH hm
              exact NashSupport.cube0 H hH hm
            | succ k =>
              cases k with
              | zero =>
                intro H hH hm
                exact NashSupport.cube1 H hH hm
              | succ k =>
                -- dimensions at least two: the residual cubical Sperner
                -- parity/path lemma
                intro H hH hm
                apply NashSupport.cube_approx_of_crossing _ H hH
                apply NashSupport.cube_crossing_of_labels (k:=Nat.succ (Nat.succ k)) ?_ H hm
                -- the remaining part is the finite cubical labelling lemma
                intro j
                cases j with
                | zero => exact NashSupport.cubicalLabel_zero
                | succ j =>
                  intro m hm L hlo hhi
                  cases m with
                  | zero => simp at hm
                  | succ m =>
                    cases m with
                    | zero =>
                      exact NashSupport.cubicalLabel_unit _ L hlo hhi
                    | succ m =>
                      -- Dimension one is an actual finite intermediate-value lemma;
                      -- removing it here leaves only the genuine parity dimensions.
                      cases j with
                      | zero =>
                        exact NashSupport.cubicalLabel_one (Nat.succ (Nat.succ m)) hm L hlo hhi
                      | succ j =>
                        apply NashSupport.label_of_degree L
                        rw [NashSupport.gridDegree_top_zero (n:=Nat.succ j)
                          (m:=Nat.succ (Nat.succ m)) (by omega) L hlo hhi]
                        -- On the one remaining facet the first bit is one. Its
                        -- tail is the degree on the facet.
                        classical
                        -- spell out the tail cup weight on the one surviving
                        -- kind of face (the upper zero-coordinate facet).
                        have clean :
                          (∑ z : {z : NashSupport.CP (Nat.succ j) (Nat.succ (Nat.succ m)) //
                              ¬ NashSupport.intFirst z ∧
                                z.2 (0 : Fin (Nat.succ j + 1)) = 0},
                              NashSupport.firstW L z.1) =
                          (∑ z : {z : NashSupport.CP (Nat.succ j) (Nat.succ (Nat.succ m)) //
                              ¬ NashSupport.intFirst z ∧
                                z.2 (0 : Fin (Nat.succ j + 1)) = 0},
                             NashSupport.parityTop
                               (NashSupport.parityTail (NashSupport.bitsOf L))
                               (fun r => NashSupport.pathVert z.1.1 z.1.2 (r+1))) := by
                          apply Finset.sum_congr rfl
                          intro z hz
                          rcases z with ⟨⟨c,p⟩, hout, hp⟩
                          have ht : (c (p (0 : Fin (Nat.succ j + 1)))).val + 1 =
                              Nat.succ (Nat.succ m) := by
                            unfold NashSupport.intFirst at hout
                            simp at hout
                            have hc := (c (p (0 : Fin (Nat.succ j + 1)))).isLt
                            omega
                          exact NashSupport.firstW_top_tail L hhi c p ht hp
                        rw [clean]
                        -- Reindex this facet by dropping its fixed zero
                        -- direction.  On successors this is `topLabel L`.
                        rw [NashSupport.top_sum_eq_degree
                          (n:=Nat.succ j) (m:=Nat.succ (Nat.succ m))
                          (by omega : 0 < Nat.succ (Nat.succ m)) L]
                        have hf := NashSupport.topLabel_faces (L:=L) hlo hhi
                        rw [NashSupport.gridDegree_one (Nat.succ j)
                          (Nat.succ (Nat.succ m)) (by omega)
                          (NashSupport.topLabel L) hf.1 hf.2]
                        decide
          exact NashSupport.cubeApprox_of_fin (α:=Ω) fin_core
        exact NashSupport.simplexApprox_of_cube (α:=Ω) cube_core
      intro f hf hfm ε hε
      let m : (Ω → ℝ) → (∀ i, S i → ℝ) :=
        fun p => NashSupport.marg (ι:=Fin n) (A:=S) p
      let j : (∀ i, S i → ℝ) → (Ω → ℝ) :=
        fun z => NashSupport.indep (ι:=Fin n) (A:=S) z
      let g : (Ω → ℝ) → (Ω → ℝ) := fun p => j (f (m p))
      have hmC : Continuous m := by
        dsimp [m, Ω]
        exact NashSupport.continuous_marg (ι:=Fin n) (A:=S)
      have hjC : Continuous j := by
        dsimp [j, Ω]
        exact NashSupport.continuous_indep (ι:=Fin n) (A:=S)
      have hmK {p : Ω → ℝ} (hp : p ∈ Δ) : m p ∈ K := by
        change NashSupport.marg (ι:=Fin n) (A:=S) p ∈ K
        have h := NashSupport.marg_mem (ι:=Fin n) (A:=S) p hp
        simpa [K, NashSupport.productSimplex] using h
      have hjK {z : (∀ i, S i → ℝ)} (hz : z ∈ K) : j z ∈ Δ := by
        change NashSupport.indep (ι:=Fin n) (A:=S) z ∈ Δ
        apply NashSupport.indep_mem (ι:=Fin n) (A:=S) z
        simpa [K, NashSupport.productSimplex] using hz
      have hgC : Continuous g := by
        exact hjC.comp (hf.comp hmC)
      have hgK : MapsTo g Δ Δ := by
        intro p hp
        exact hjK (hfm (hmK hp))
      have hΔne : Δ.Nonempty := by
        classical
        let s₀ : Ω := fun i => Classical.choice (inferInstance : Nonempty (S i))
        exact ⟨Pi.single s₀ 1, single_mem_stdSimplex ℝ s₀⟩
      have hΔcp : IsCompact Δ := by
        classical
        exact isCompact_stdSimplex ℝ Ω
      obtain ⟨y, hy, hyfix⟩ := NashSupport.fixed_of_approx Δ hΔne hΔcp g hgC
        (simplex_core g hgC hgK)
      refine ⟨m y, hmK hy, ?_⟩
      have hz : f (m y) ∈ K := hfm (hmK hy)
      have hret : m (j (f (m y))) = f (m y) := by
        dsimp [m, j, Ω]
        apply NashSupport.marg_indep (ι:=Fin n) (A:=S)
        simpa [K, NashSupport.productSimplex] using hz
      have hfix : f (m y) = m y := by
        have hb : m (g y) = m y := congrArg m hyfix
        -- the section/retraction identity for independent laws
        rw [hret] at hb
        exact hb
      rw [hfix, dist_self]
      exact hε
    have brouwer_on_product_simplex :
        ∀ (f : (∀ i, S i → ℝ) → (∀ i, S i → ℝ)),
          Continuous f → MapsTo f K K →
          ∃ x, x ∈ K ∧ f x = x := by
      intro f hf hfm
      exact NashSupport.fixed_of_approx K hKne hKcp f hf
        (approx_on_product_simplex f hf hfm)
    exact brouwer_on_product_simplex T hcon hmap
  rcases h_exists with ⟨x, hxK, hxfix⟩
  refine ⟨x, ?_, ?_⟩
  · intro i
    exact hxK i
  · intro i τ hτ
    -- isolate this player's pure values
    have hav : (∑ a : S i, x i a * V i x a) = W i x := by
      dsimp [V, W]
      exact (NashSupport.payoff_eq_sum_pure (w:=u i) (x:=x) i).symm
    have hcoord (a : S i) :
        x i a = (x i a + max 0 (V i x a - W i x)) /
          (1 + ∑ b : S i, max 0 (V i x b - W i x)) := by
      have := congrFun (congrFun hxfix i) a
      -- hxfix is equality of functions `T x = x`
      simpa [T] using this.symm
    have hmix := NashSupport.mixture_le_of_fixed
      (p:=x i) (v:=V i x) (U:=W i x) (hxK i) hav hcoord τ hτ
    have hlin := NashSupport.payoff_update_eq_sum_pure
      (w:=u i) (x:=x) (i:=i) (q:=τ)
    -- This expression is exactly the expected payoff in the statement.
    change NashSupport.payoff (u i) (Function.update x i τ) ≤
      NashSupport.payoff (u i) x
    rw [hlin]
    exact hmix
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
