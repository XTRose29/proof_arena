import Submission.Combinatorics

open Equiv Function

namespace Submission.Grid

private def conjugate {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α) : Equiv.Perm β :=
  e.symm.trans (p.trans e)

private lemma conjugate_involutive {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α)
    (hp : Involutive p) : Involutive (conjugate e p) := by
  intro x
  change e (p (e.symm (e (p (e.symm x))))) = x
  rw [e.symm_apply_apply, hp, e.apply_symm_apply]

/-- Swap the two points in each consecutive pair of `Fin (m * 2)`. -/
def evenPair (m : ℕ) : Equiv.Perm (Fin (m * 2)) :=
  let e : Fin m × Fin 2 ≃ Fin (m * 2) := finProdFinEquiv
  conjugate e (Equiv.prodCongr (Equiv.refl _) (Equiv.swap 0 1))

/-- The complementary matching, obtained by shifting `evenPair` once around the cyclic order. -/
def oddPair (m : ℕ) : Equiv.Perm (Fin (m * 2)) :=
  conjugate (finRotate (m * 2)) (evenPair m)

lemma evenPair_involutive (m : ℕ) : Involutive (evenPair m) := by
  apply conjugate_involutive
  intro x
  rcases x with ⟨a, b⟩
  fin_cases b <;> rfl

lemma oddPair_involutive (m : ℕ) : Involutive (oddPair m) := by
  exact conjugate_involutive _ _ (evenPair_involutive m)

private lemma evenPair_apply_zero (m : ℕ) (a : Fin m) :
    evenPair m (finProdFinEquiv (a, (0 : Fin 2))) = finProdFinEquiv (a, (1 : Fin 2)) := by
  simp [evenPair, conjugate]

private lemma evenPair_apply_one (m : ℕ) (a : Fin m) :
    evenPair m (finProdFinEquiv (a, (1 : Fin 2))) = finProdFinEquiv (a, (0 : Fin 2)) := by
  have h := congrArg (evenPair m) (evenPair_apply_zero m a)
  rw [evenPair_involutive] at h
  exact h.symm

@[simp] private lemma finProd_zero_val (m : ℕ) (a : Fin m) :
    (finProdFinEquiv (a, (0 : Fin 2)) : Fin (m * 2)).val = 2 * a.val := by
  simp [finProdFinEquiv]

@[simp] private lemma finProd_one_val (m : ℕ) (a : Fin m) :
    (finProdFinEquiv (a, (1 : Fin 2)) : Fin (m * 2)).val = 1 + 2 * a.val := by
  simp [finProdFinEquiv]

private lemma rotate_apply_zero (m : ℕ) (a : Fin m) :
    finRotate (m * 2) (finProdFinEquiv (a, (0 : Fin 2))) =
      finProdFinEquiv (a, (1 : Fin 2)) := by
  apply Fin.ext
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  letI : NeZero (m * 2) := ⟨Nat.mul_ne_zero hm.ne' (by norm_num)⟩
  have hn2 : 1 < m * 2 := by omega
  rw [finRotate_apply]
  simp only [Fin.add_def, finProd_zero_val, finProd_one_val, Fin.val_one']
  rw [Nat.mod_eq_of_lt hn2]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private lemma rotate_symm_apply_one (m : ℕ) (a : Fin m) :
    (finRotate (m * 2)).symm (finProdFinEquiv (a, (1 : Fin 2))) =
      finProdFinEquiv (a, (0 : Fin 2)) := by
  apply Fin.ext
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  letI : NeZero (m * 2) := ⟨Nat.mul_ne_zero hm.ne' (by norm_num)⟩
  have hne : finProdFinEquiv (a, (1 : Fin 2)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    change 1 + 2 * (a : ℕ) = 0 at this
    omega
  rw [coe_finRotate_symm_of_ne_zero hne]
  simp only [finProd_one_val, finProd_zero_val]
  omega

lemma pair_eq_rotate (m : ℕ) (x : Fin (m * 2)) :
    evenPair m x = finRotate (m * 2) x ∨ oddPair m x = finRotate (m * 2) x := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)).surjective x
  fin_cases b
  · left
    exact (evenPair_apply_zero m a).trans (rotate_apply_zero m a).symm
  · right
    change finRotate (m * 2)
      (evenPair m ((finRotate (m * 2)).symm (finProdFinEquiv (a, (1 : Fin 2))))) = _
    rw [rotate_symm_apply_one, evenPair_apply_zero]
    rfl

lemma evenPair_neighbor (m : ℕ) (x : Fin (m * 2)) :
    evenPair m x = finRotate (m * 2) x ∨ x = finRotate (m * 2) (evenPair m x) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)).surjective x
  fin_cases b
  · left
    exact (evenPair_apply_zero m a).trans (rotate_apply_zero m a).symm
  · right
    change finProdFinEquiv (a, (1 : Fin 2)) =
      finRotate (m * 2) (evenPair m (finProdFinEquiv (a, (1 : Fin 2))))
    rw [evenPair_apply_one, rotate_apply_zero]

lemma oddPair_neighbor (m : ℕ) (x : Fin (m * 2)) :
    oddPair m x = finRotate (m * 2) x ∨ x = finRotate (m * 2) (oddPair m x) := by
  let r := finRotate (m * 2)
  let z := r.symm x
  have hx : r z = x := r.apply_symm_apply x
  rcases evenPair_neighbor m z with hforward | hbackward
  · left
    change r (evenPair m z) = r x
    rw [hforward, hx]
  · right
    change x = r (r (evenPair m z))
    rw [← hbackward, hx]

/-- Apply a permutation in one coordinate of a grid index. -/
def coordPerm {d n : ℕ} (i : Fin d) (a : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin d → Fin n) :=
  Equiv.piCongrRight fun j => if j = i then a else Equiv.refl _

@[simp]
lemma coordPerm_apply_same {d n : ℕ} (i : Fin d) (a : Equiv.Perm (Fin n))
    (k : Fin d → Fin n) : coordPerm i a k i = a (k i) := by
  simp [coordPerm]

@[simp]
lemma coordPerm_apply_ne {d n : ℕ} {i j : Fin d} (hji : j ≠ i)
    (a : Equiv.Perm (Fin n)) (k : Fin d → Fin n) : coordPerm i a k j = k j := by
  simp [coordPerm, hji]

lemma coordPerm_involutive {d n : ℕ} (i : Fin d) (a : Equiv.Perm (Fin n))
    (ha : Involutive a) : Involutive (coordPerm i a) := by
  intro k
  funext j
  by_cases hji : j = i
  · subst j
    simp only [coordPerm_apply_same]
    exact ha (k i)
  · simp [hji]

lemma coordPerm_pow_apply {d n : ℕ} (i : Fin d) (a : Equiv.Perm (Fin n))
    (k : Fin d → Fin n) (r : ℕ) (j : Fin d) :
    ((coordPerm i a) ^ r) k j = if j = i then (a ^ r) (k j) else k j := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      by_cases hji : j = i
      · subst j
        simp [ih, pow_succ', Equiv.Perm.mul_apply]
      · simp [ih, hji]

/-- Two local matching layers in every torus coordinate. -/
noncomputable def layers (d m : ℕ) : List (Equiv.Perm (Fin d → Fin (m * 2))) :=
  Finset.univ.toList.flatMap fun i => [coordPerm i (evenPair m), coordPerm i (oddPair m)]

@[simp]
lemma layers_length (d m : ℕ) : (layers d m).length = 2 * d := by
  simp [layers, mul_comm]

lemma even_mem_layers {d m : ℕ} (i : Fin d) : coordPerm i (evenPair m) ∈ layers d m := by
  apply List.mem_flatMap.2
  exact ⟨i, by simp, by simp⟩

lemma odd_mem_layers {d m : ℕ} (i : Fin d) : coordPerm i (oddPair m) ∈ layers d m := by
  apply List.mem_flatMap.2
  exact ⟨i, by simp, by simp⟩

lemma mem_layers_involutive {d m : ℕ} (a : Equiv.Perm (Fin d → Fin (m * 2)))
    (ha : a ∈ layers d m) : Involutive a := by
  simp only [layers, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨i, rfl | rfl⟩ := ha
  · exact coordPerm_involutive i _ (evenPair_involutive m)
  · exact coordPerm_involutive i _ (oddPair_involutive m)

/-- Merge all cycles of `p` using the local matching layers. -/
noncomputable def cyclicize {d m : ℕ} (p : Equiv.Perm (Fin d → Fin (m * 2))) :
    Equiv.Perm (Fin d → Fin (m * 2)) :=
  Submission.Combinatorics.mergeLayers (layers d m) p

lemma cyclicize_connects_rotate {d m : ℕ} (p : Equiv.Perm (Fin d → Fin (m * 2)))
    (k : Fin d → Fin (m * 2)) (i : Fin d) :
    (cyclicize p).SameCycle k (coordPerm i (finRotate (m * 2)) k) := by
  rcases pair_eq_rotate m (k i) with h | h
  · have hc := Submission.Combinatorics.mergeLayers_connects_of_mem
      (even_mem_layers (m := m) i) p k
    change (cyclicize p).SameCycle k _ at hc
    convert hc using 1
    funext j
    by_cases hji : j = i
    · subst j
      simpa using h.symm
    · simp [hji]
  · have hc := Submission.Combinatorics.mergeLayers_connects_of_mem
      (odd_mem_layers (m := m) i) p k
    change (cyclicize p).SameCycle k _ at hc
    convert hc using 1
    funext j
    by_cases hji : j = i
    · subst j
      simpa using h.symm
    · simp [hji]

private lemma sameCycle_iterate {α : Type*} (q a : Equiv.Perm α)
    (hstep : ∀ x, q.SameCycle x (a x)) (x : α) (r : ℕ) :
    q.SameCycle x ((a ^ r) x) := by
  induction r with
  | zero => simpa using Equiv.Perm.SameCycle.refl q x
  | succ r ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.trans (hstep ((a ^ r) x))

lemma cyclicize_connects_update {d m : ℕ} (hm : 0 < m)
    (p : Equiv.Perm (Fin d → Fin (m * 2))) (k : Fin d → Fin (m * 2))
    (i : Fin d) (y : Fin (m * 2)) :
    (cyclicize p).SameCycle k (Function.update k i y) := by
  have hn : 2 ≤ m * 2 := by omega
  have hsupp := support_finRotate_of_le hn
  have hk : finRotate (m * 2) (k i) ≠ k i := by
    have : k i ∈ (finRotate (m * 2)).support := by rw [hsupp]; simp
    simpa using this
  have hy : finRotate (m * 2) y ≠ y := by
    have : y ∈ (finRotate (m * 2)).support := by rw [hsupp]; simp
    simpa using this
  obtain ⟨r, hr⟩ := (isCycle_finRotate_of_le hn).exists_pow_eq hk hy
  have hiter := sameCycle_iterate (cyclicize p) (coordPerm i (finRotate (m * 2)))
    (cyclicize_connects_rotate p · i) k r
  convert hiter using 1
  funext j
  rw [coordPerm_pow_apply]
  by_cases hji : j = i
  · subst j
    simp [hr]
  · simp [hji]

lemma cyclicize_sameCycle_all {d m : ℕ} (hm : 0 < m)
    (p : Equiv.Perm (Fin d → Fin (m * 2))) (k l : Fin d → Fin (m * 2)) :
    (cyclicize p).SameCycle k l := by
  let patch : Finset (Fin d) → (Fin d → Fin (m * 2)) := fun s i => if i ∈ s then l i else k i
  have hpatch : ∀ s : Finset (Fin d), (cyclicize p).SameCycle k (patch s) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simpa [patch] using Equiv.Perm.SameCycle.refl (cyclicize p) k
    | @insert i s hi ih =>
        refine ih.trans ?_
        have hu := cyclicize_connects_update hm p (patch s) i (l i)
        convert hu using 1
        funext j
        by_cases hji : j = i
        · subst j
          simp [patch, hi]
        · simp [patch, hji]
  simpa [patch] using hpatch Finset.univ

lemma cyclicize_isCycle_support {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (p : Equiv.Perm (Fin d → Fin (m * 2))) :
    (cyclicize p).IsCycle ∧ (cyclicize p).support = Finset.univ := by
  let i : Fin d := ⟨0, hd⟩
  let k : Fin d → Fin (m * 2) := fun _ => ⟨0, by omega⟩
  let l := coordPerm i (finRotate (m * 2)) k
  have hn : 2 ≤ m * 2 := by omega
  have hrot : finRotate (m * 2) (k i) ≠ k i := by
    have hsupp := support_finRotate_of_le hn
    have : k i ∈ (finRotate (m * 2)).support := by rw [hsupp]; simp
    simpa using this
  have hkl : l ≠ k := by
    intro h
    apply hrot
    have := congrFun h i
    simpa [l] using this
  have hsupport : (cyclicize p).support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    intro hx
    have hsc := cyclicize_sameCycle_all hm p x l
    have hxl : x = l := hsc.eq_of_left hx
    have hsc' := cyclicize_sameCycle_all hm p x k
    have hxk : x = k := hsc'.eq_of_left hx
    exact hkl (hxl.symm.trans hxk)
  refine ⟨?_, hsupport⟩
  have hk : cyclicize p k ≠ k := by
    have : k ∈ (cyclicize p).support := by rw [hsupport]; simp
    simpa using this
  exact ⟨k, hk, fun y _ => cyclicize_sameCycle_all hm p k y⟩

end Submission.Grid
