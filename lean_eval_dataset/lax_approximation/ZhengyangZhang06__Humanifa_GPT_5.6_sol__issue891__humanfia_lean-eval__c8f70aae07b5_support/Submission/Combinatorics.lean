import ChallengeDeps

open Equiv Function

namespace Submission.Combinatorics

variable {α : Type*} [Fintype α] [DecidableEq α]

private lemma mul_swap_connects {p : Equiv.Perm α} {a b : α}
    (hab : ¬p.SameCycle a b) : (p * Equiv.swap a b).SameCycle a b := by
  let q := p * Equiv.swap a b
  let P : ℕ → Prop := fun m => 0 < m ∧ (p ^ m) b = b
  have hex : ∃ m, P m := by
    refine ⟨orderOf p, orderOf_pos p, ?_⟩
    simp
  let m := Nat.find hex
  have hm : P m := Nat.find_spec hex
  have hpow : ∀ j : ℕ, 0 < j → j ≤ m → (q ^ j) a = (p ^ j) b := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      intro _hjpos hle
      by_cases hj0 : j = 0
      · subst j
        change q a = p b
        rw [show q = p * Equiv.swap a b by rfl, Equiv.Perm.mul_apply,
          Equiv.swap_apply_left]
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        have hjlt : j < m := Nat.lt_of_succ_le hle
        have hjb : (p ^ j) b ≠ b := by
          intro heq
          have hPj : P j := ⟨hjpos, heq⟩
          exact (not_le_of_gt hjlt) (Nat.find_min' hex hPj)
        have hja : (p ^ j) b ≠ a := by
          intro heq
          apply hab
          exact (show p.SameCycle b a from
            ⟨(j : ℤ), by simpa [zpow_natCast] using heq⟩).symm
        calc
          (q ^ (j + 1)) a = q ((q ^ j) a) := by rw [pow_succ']; rfl
          _ = q ((p ^ j) b) := congrArg q (ih hjpos hjlt.le)
          _ = p (Equiv.swap a b ((p ^ j) b)) := by
            rw [show q = p * Equiv.swap a b by rfl, Equiv.Perm.mul_apply]
          _ = p ((p ^ j) b) := by rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
          _ = (p ^ (j + 1)) b := by rw [pow_succ']; rfl
  refine ⟨(m : ℤ), ?_⟩
  rw [zpow_natCast]
  exact (hpow m hm.1 le_rfl).trans hm.2

private lemma mul_swap_preserves {p : Equiv.Perm α} {a b x y : α}
    (hab : ¬p.SameCycle a b) (hxy : p.SameCycle x y) :
    (p * Equiv.swap a b).SameCycle x y := by
  let q := p * Equiv.swap a b
  have habq : q.SameCycle a b := by
    simpa only [q] using mul_swap_connects hab
  have hstep : ∀ z : α, q.SameCycle z (p z) := by
    intro z
    by_cases hza : z = a
    · subst z
      refine habq.trans ?_
      refine ⟨1, ?_⟩
      rw [zpow_one, show q = p * Equiv.swap a b by rfl, Equiv.Perm.mul_apply,
        Equiv.swap_apply_right]
    · by_cases hzb : z = b
      · subst z
        refine habq.symm.trans ?_
        refine ⟨1, ?_⟩
        rw [zpow_one, show q = p * Equiv.swap a b by rfl, Equiv.Perm.mul_apply,
          Equiv.swap_apply_left]
      · refine ⟨1, ?_⟩
        rw [zpow_one, show q = p * Equiv.swap a b by rfl, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne hza hzb]
  have hnat : ∀ (z : α) (j : ℕ), q.SameCycle z ((p ^ j) z) := by
    intro z j
    induction j with
    | zero => exact Equiv.Perm.SameCycle.refl q z
    | succ j ih =>
      exact ih.trans (by simpa [pow_succ'] using hstep ((p ^ j) z))
  have hinvstep : ∀ z : α, q.SameCycle z (p⁻¹ z) := by
    intro z
    have := (hstep (p⁻¹ z)).symm
    simpa using this
  have hinvnat : ∀ (z : α) (j : ℕ), q.SameCycle z ((p⁻¹ ^ j) z) := by
    intro z j
    induction j with
    | zero => exact Equiv.Perm.SameCycle.refl q z
    | succ j ih =>
      exact ih.trans (by simpa [pow_succ'] using hinvstep ((p⁻¹ ^ j) z))
  obtain ⟨j, rfl⟩ := hxy
  cases j with
  | ofNat j => simpa [q, zpow_natCast] using hnat x j
  | negSucc j => simpa [q, zpow_negSucc, ← inv_pow] using hinvnat x (j + 1)

/-- Merge the cycles through `x` and `a x`, leaving the permutation unchanged if they are
already the same cycle. -/
noncomputable def mergeOne (p a : Equiv.Perm α) (x : α) : Equiv.Perm α :=
  if p.SameCycle x (a x) then p else p * Equiv.swap x (a x)

lemma mergeOne_preserves (p a : Equiv.Perm α) (x : α) {u v : α}
    (huv : p.SameCycle u v) : (mergeOne p a x).SameCycle u v := by
  by_cases h : p.SameCycle x (a x)
  · simpa [mergeOne, h] using huv
  · simpa [mergeOne, h] using mul_swap_preserves h huv

lemma mergeOne_connects (p a : Equiv.Perm α) (x : α) :
    (mergeOne p a x).SameCycle x (a x) := by
  by_cases h : p.SameCycle x (a x)
  · rw [mergeOne, if_pos h]
    exact h
  · simpa [mergeOne, h] using mul_swap_connects h

/-- Process a list of disjoint-pair candidates, joining two cycles whenever the current candidate
has endpoints in distinct cycles. -/
noncomputable def mergeList (a : Equiv.Perm α) : List α → Equiv.Perm α → Equiv.Perm α
  | [], p => p
  | x :: xs, p => mergeList a xs (mergeOne p a x)

lemma mergeList_preserves (a : Equiv.Perm α) (xs : List α) (p : Equiv.Perm α) {u v : α}
    (huv : p.SameCycle u v) : (mergeList a xs p).SameCycle u v := by
  induction xs generalizing p with
  | nil => exact huv
  | cons x xs ih =>
    exact ih (mergeOne p a x) (mergeOne_preserves p a x huv)

lemma mergeList_connects_of_mem (a : Equiv.Perm α) {xs : List α} {x : α}
    (hx : x ∈ xs) (p : Equiv.Perm α) : (mergeList a xs p).SameCycle x (a x) := by
  induction xs generalizing p with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact mergeList_preserves a ys _ (mergeOne_connects p a x)
    · exact ih hx (mergeOne p a y)

private lemma mergeOne_factor (p a : Equiv.Perm α) (ha : Involutive a) (x : α) :
    ∃ r : Equiv.Perm α, mergeOne p a x = p * r ∧ ∀ z, r z = z ∨ r z = a z := by
  by_cases h : p.SameCycle x (a x)
  · refine ⟨1, by simp [mergeOne, h], ?_⟩
    intro z
    exact Or.inl rfl
  · refine ⟨Equiv.swap x (a x), by simp [mergeOne, h], ?_⟩
    intro z
    by_cases hzx : z = x
    · subst z
      exact Or.inr (Equiv.swap_apply_left x (a x))
    · by_cases hza : z = a x
      · subst z
        exact Or.inr ((Equiv.swap_apply_right x (a x)).trans (ha x).symm)
      · exact Or.inl (Equiv.swap_apply_of_ne_of_ne hzx hza)

omit [Fintype α] [DecidableEq α] in
private lemma local_mul (a r s : Equiv.Perm α) (ha : Involutive a)
    (hr : ∀ z, r z = z ∨ r z = a z) (hs : ∀ z, s z = z ∨ s z = a z) :
    ∀ z, (r * s) z = z ∨ (r * s) z = a z := by
  intro z
  rw [Equiv.Perm.mul_apply]
  rcases hs z with hsz | hsz
  · rw [hsz]
    exact hr z
  · rw [hsz]
    rcases hr (a z) with hrz | hrz
    · exact Or.inr hrz
    · rw [ha z] at hrz
      exact Or.inl hrz

lemma mergeList_factor (a : Equiv.Perm α) (ha : Involutive a) (xs : List α)
    (p : Equiv.Perm α) :
    ∃ r : Equiv.Perm α, mergeList a xs p = p * r ∧ ∀ z, r z = z ∨ r z = a z := by
  induction xs generalizing p with
  | nil =>
    refine ⟨1, by simp [mergeList], ?_⟩
    intro z
    exact Or.inl rfl
  | cons x xs ih =>
    obtain ⟨r, hr, hrlocal⟩ := mergeOne_factor p a ha x
    obtain ⟨s, hs, hslocal⟩ := ih (mergeOne p a x)
    refine ⟨r * s, ?_, local_mul a r s ha hrlocal hslocal⟩
    rw [mergeList, hs, hr, mul_assoc]

/-- One complete matching layer. -/
noncomputable def mergeLayer (p a : Equiv.Perm α) : Equiv.Perm α :=
  mergeList a Finset.univ.toList p

lemma mergeLayer_preserves (p a : Equiv.Perm α) {u v : α} (huv : p.SameCycle u v) :
    (mergeLayer p a).SameCycle u v :=
  mergeList_preserves a _ p huv

lemma mergeLayer_connects (p a : Equiv.Perm α) (x : α) :
    (mergeLayer p a).SameCycle x (a x) :=
  mergeList_connects_of_mem a (by simp) p

lemma mergeLayer_factor (p a : Equiv.Perm α) (ha : Involutive a) :
    ∃ r : Equiv.Perm α, mergeLayer p a = p * r ∧ ∀ z, r z = z ∨ r z = a z :=
  mergeList_factor a ha _ p

/-- Apply all matching layers in the given list. -/
noncomputable def mergeLayers : List (Equiv.Perm α) → Equiv.Perm α → Equiv.Perm α
  | [], p => p
  | a :: as, p => mergeLayers as (mergeLayer p a)

lemma mergeLayers_preserves (as : List (Equiv.Perm α)) (p : Equiv.Perm α) {u v : α}
    (huv : p.SameCycle u v) : (mergeLayers as p).SameCycle u v := by
  induction as generalizing p with
  | nil => exact huv
  | cons a as ih => exact ih (mergeLayer p a) (mergeLayer_preserves p a huv)

lemma mergeLayers_connects_of_mem {as : List (Equiv.Perm α)} {a : Equiv.Perm α}
    (ha : a ∈ as) (p : Equiv.Perm α) (x : α) :
    (mergeLayers as p).SameCycle x (a x) := by
  induction as generalizing p with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact mergeLayers_preserves bs _ (mergeLayer_connects p a x)
    · exact ih ha (mergeLayer p b)

/-- A path of exactly `n` steps in a reflexive adjacency relation. -/
inductive Steps (R : α → α → Prop) : ℕ → α → α → Prop
  | zero (x : α) : Steps R 0 x x
  | succ {n : ℕ} {x y z : α} (hxy : R x y) (hyz : Steps R n y z) :
      Steps R (n + 1) x z

omit [Fintype α] [DecidableEq α] in
lemma Steps.trans {R : α → α → Prop} {m n : ℕ} {x y z : α}
    (hxy : Steps R m x y) (hyz : Steps R n y z) : Steps R (m + n) x z := by
  induction hxy with
  | zero => simpa using hyz
  | @succ m x w y hxw hwy ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.succ hxw (ih hyz)

lemma mergeLayers_factor_steps (R : α → α → Prop) (hrefl : ∀ x, R x x)
    (as : List (Equiv.Perm α)) (hinv : ∀ a ∈ as, Involutive a)
    (hadj : ∀ a ∈ as, ∀ x, R x (a x)) (p : Equiv.Perm α) :
    ∃ r : Equiv.Perm α, mergeLayers as p = p * r ∧ ∀ x, Steps R as.length x (r x) := by
  induction as generalizing p with
  | nil =>
    refine ⟨1, by simp [mergeLayers], ?_⟩
    intro x
    exact Steps.zero x
  | cons a as ih =>
    obtain ⟨r, hr, hrlocal⟩ := mergeLayer_factor p a (hinv a (by simp))
    obtain ⟨s, hs, hssteps⟩ := ih (fun b hb => hinv b (by simp [hb]))
      (fun b hb => hadj b (by simp [hb])) (mergeLayer p a)
    refine ⟨r * s, ?_, ?_⟩
    · rw [mergeLayers, hs, hr, mul_assoc]
    · intro x
      rw [Equiv.Perm.mul_apply]
      have hrs : R (s x) (r (s x)) := by
        rcases hrlocal (s x) with h | h
        · rw [h]
          exact hrefl (s x)
        · rw [h]
          exact hadj a (by simp) (s x)
      have hone : Steps R 1 (s x) (r (s x)) := by
        simpa using Steps.succ hrs (Steps.zero (r (s x)))
      simpa [Nat.add_comm] using (hssteps x).trans hone

end Submission.Combinatorics
