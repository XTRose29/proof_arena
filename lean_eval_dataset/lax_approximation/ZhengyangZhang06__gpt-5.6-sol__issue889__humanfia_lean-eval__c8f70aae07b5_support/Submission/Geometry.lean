import Submission.Grid
import Submission.Helpers

open LeanEval.Dynamics.LaxApproximation
open Set
open Submission.Grid
open Submission.Helpers

namespace Submission.Geometry

private lemma circle_dist_coe_le (r s : ℝ) :
    dist (r : AddCircle (1 : ℝ)) (s : AddCircle (1 : ℝ)) ≤ |r - s| := by
  rw [dist_eq_norm_vsub]
  change ‖((r - s : ℝ) : AddCircle (1 : ℝ))‖ ≤ |r - s|
  simpa only [Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ)) (m := r - s))

private lemma circle_dist_same_interval (n : ℕ) (_hn : 0 < n) (a : Fin n)
    {x y : AddCircle (1 : ℝ)}
    (hx : ∃ r : ℝ, (a : ℝ) / n ≤ r ∧ r < ((a : ℝ) + 1) / n ∧
      x = (r : AddCircle (1 : ℝ)))
    (hy : ∃ s : ℝ, (a : ℝ) / n ≤ s ∧ s < ((a : ℝ) + 1) / n ∧
      y = (s : AddCircle (1 : ℝ))) :
    dist x y ≤ 1 / (n : ℝ) := by
  obtain ⟨r, har, hra, rfl⟩ := hx
  obtain ⟨s, has, hsa, rfl⟩ := hy
  refine (circle_dist_coe_le r s).trans ?_
  rw [abs_le]
  have hwidth : ((a : ℝ) + 1) / n - (a : ℝ) / n = 1 / (n : ℝ) := by ring
  constructor <;> linarith

private lemma circle_dist_rotate_interval (n : ℕ) (hn : 0 < n) (a : Fin n)
    {x y : AddCircle (1 : ℝ)}
    (hx : ∃ r : ℝ, (a : ℝ) / n ≤ r ∧ r < ((a : ℝ) + 1) / n ∧
      x = (r : AddCircle (1 : ℝ)))
    (hy : ∃ s : ℝ, (finRotate n a : ℝ) / n ≤ s ∧
      s < ((finRotate n a : ℝ) + 1) / n ∧ y = (s : AddCircle (1 : ℝ))) :
    dist x y ≤ 2 / (n : ℝ) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨r, har, hra, rfl⟩ := hx
  obtain ⟨s, has, hsa, rfl⟩ := hy
  have hcast : (q.succ : ℝ) = (q : ℝ) + 1 := by norm_num
  rw [hcast] at har hra has hsa ⊢
  have hden : 0 < (q : ℝ) + 1 := by positivity
  by_cases ha : a = Fin.last q
  · subst a
    have hrotate : finRotate (q + 1) (Fin.last q) = 0 := finRotate_last
    simp [hrotate] at has hsa
    have hsa' : s < 1 / ((q : ℝ) + 1) := by simpa only [one_div] using hsa
    have hperiod : ((s + 1 : ℝ) : AddCircle (1 : ℝ)) = (s : AddCircle (1 : ℝ)) := by
      rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
    rw [← hperiod]
    refine (circle_dist_coe_le r (s + 1)).trans ?_
    rw [abs_le]
    have hlast : ((Fin.last q : Fin (q + 1)) : ℝ) = q := by norm_num
    rw [hlast] at har hra
    have hratio : (q : ℝ) / ((q : ℝ) + 1) = 1 - 1 / ((q : ℝ) + 1) := by
      field_simp
      ring
    have hone : ((q : ℝ) + 1) / ((q : ℝ) + 1) = 1 := div_self hden.ne'
    rw [hratio] at har
    rw [hone] at hra
    have hwidth : (2 : ℝ) / ((q : ℝ) + 1) =
        (1 / ((q : ℝ) + 1) + 1) - (1 - 1 / ((q : ℝ) + 1)) := by
      ring
    have hnonneg : 0 ≤ (2 : ℝ) / ((q : ℝ) + 1) := by positivity
    constructor <;> linarith
  · have hrotate : ((finRotate (q + 1) a : Fin (q + 1)) : ℕ) = a + 1 :=
      coe_finRotate_of_ne_last ha
    have hrotate' : (finRotate (q + 1) a : ℝ) = (a : ℝ) + 1 := by
      exact_mod_cast hrotate
    rw [hrotate'] at has hsa
    refine (circle_dist_coe_le r s).trans ?_
    rw [abs_le]
    have hsa' : s < ((a : ℝ) + 2) / ((q : ℝ) + 1) := by
      convert hsa using 1
      ring
    have hwidth : ((a : ℝ) + 2) / ((q : ℝ) + 1) -
        (a : ℝ) / ((q : ℝ) + 1) = 2 / ((q : ℝ) + 1) := by
      field_simp
      ring
    have hnonneg : 0 ≤ (2 : ℝ) / ((q : ℝ) + 1) := by positivity
    constructor <;> linarith

/-- Two grid indices are coordinatewise equal or cyclic neighbors. -/
def Near {d n : ℕ} (k l : Fin d → Fin n) : Prop :=
  ∀ i, k i = l i ∨ l i = finRotate n (k i) ∨ k i = finRotate n (l i)

lemma near_refl {d n : ℕ} (k : Fin d → Fin n) : Near k k := fun _ => Or.inl rfl

lemma dist_mem_same_cube (n : ℕ) (hn : 0 < n) {d : ℕ} {k : Fin d → Fin n}
    {x y : Torus d} (hx : x ∈ cube n k) (hy : y ∈ cube n k) :
    dist x y ≤ 1 / (n : ℝ) := by
  apply (dist_pi_le_iff (by positivity)).2
  intro i
  exact circle_dist_same_interval n hn (k i) (hx i) (hy i)

lemma dist_mem_cubes_of_near (n : ℕ) (hn : 0 < n) {d : ℕ}
    {k l : Fin d → Fin n} (hkl : Near k l) {x y : Torus d}
    (hx : x ∈ cube n k) (hy : y ∈ cube n l) :
    dist x y ≤ 2 / (n : ℝ) := by
  apply (dist_pi_le_iff (by positivity)).2
  intro i
  have hxi := hx i
  have hyi := hy i
  rcases hkl i with hsame | hforward | hbackward
  · rw [hsame] at hxi
    refine (circle_dist_same_interval n hn (l i) hxi hyi).trans ?_
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    exact (div_le_div_iff₀ hn' hn').2 (by nlinarith)
  · rw [hforward] at hyi
    exact circle_dist_rotate_interval n hn (k i) hxi hyi
  · rw [hbackward] at hxi
    rw [dist_comm]
    exact circle_dist_rotate_interval n hn (l i) hyi hxi

lemma mem_layers_near {d m : ℕ} (a : Equiv.Perm (Fin d → Fin (m * 2)))
    (ha : a ∈ layers d m) (k : Fin d → Fin (m * 2)) : Near k (a k) := by
  simp only [layers, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨i, rfl | rfl⟩ := ha
  · intro j
    by_cases hji : j = i
    · subst j
      rcases evenPair_neighbor m (k i) with h | h
      · exact Or.inr (Or.inl (by simpa using h))
      · exact Or.inr (Or.inr (by simpa using h))
    · exact Or.inl (by simp [hji])
  · intro j
    by_cases hji : j = i
    · subst j
      rcases oddPair_neighbor m (k i) with h | h
      · exact Or.inr (Or.inl (by simpa using h))
      · exact Or.inr (Or.inr (by simpa using h))
    · exact Or.inl (by simp [hji])

lemma dist_mem_cubes_of_steps (n : ℕ) (hn : 0 < n) {d t : ℕ}
    {k l : Fin d → Fin n} (hsteps : Submission.Combinatorics.Steps Near t k l)
    {x y : Torus d} (hx : x ∈ cube n k) (hy : y ∈ cube n l) :
    dist x y ≤ (2 * t + 1 : ℝ) / n := by
  induction hsteps generalizing x y with
  | zero k =>
      simpa using dist_mem_same_cube n hn hx hy
  | @succ t k u l hku hul ih =>
      let z := gridTranslate n k u x
      have hz : z ∈ cube n u := gridTranslate_mem_cube (n := n) hx
      calc
        dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
        _ ≤ 2 / (n : ℝ) + (2 * t + 1 : ℝ) / n :=
          add_le_add (dist_mem_cubes_of_near n hn hku hx hz) (ih hz hy)
        _ = (2 * ((t + 1 : ℕ) : ℝ) + 1) / n := by
          push_cast
          ring

lemma cyclicize_factor_steps {d m : ℕ} (p : Equiv.Perm (Fin d → Fin (m * 2))) :
    ∃ r : Equiv.Perm (Fin d → Fin (m * 2)),
      cyclicize p = p * r ∧
      ∀ k, Submission.Combinatorics.Steps Near (2 * d) k (r k) := by
  obtain ⟨r, hr, hsteps⟩ := Submission.Combinatorics.mergeLayers_factor_steps
    Near near_refl (layers d m) (fun a ha => mem_layers_involutive a ha)
      (fun a ha k => mem_layers_near a ha k) p
  refine ⟨r, hr, ?_⟩
  intro k
  simpa using hsteps k

end Submission.Geometry
