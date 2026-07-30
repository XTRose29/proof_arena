import ChallengeDeps
import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/lax_approximation_c30dd8dbf7/FullCycle.lean
section

open Equiv Finset
namespace LeanEval.LaxSupport

/-- Every finite type with at least two elements admits a cycle supported on
all of it.  Writing it as `univ.toList.formPerm` is a convenient way of
avoiding any numbering choices. -/
lemma exists_full_cycle (α : Type*) [Fintype α] [DecidableEq α]
    (h2 : 2 ≤ Fintype.card α) :
    ∃ c : Equiv.Perm α, c.IsCycle ∧ c.support = Finset.univ := by
  let l : List α := (Finset.univ : Finset α).toList
  have hn : l.Nodup := Finset.nodup_toList _
  have hl : l.length = Fintype.card α := by simp [l]
  refine ⟨l.formPerm, List.isCycle_formPerm hn (by simpa [hl] using h2), ?_⟩
  -- for a non-trivial duplicate-free list the support is precisely its entries
  ext a
  have ha : a ∈ l := by simp [l]
  have hh : 1 < Fintype.card α := lt_of_lt_of_le (by decide) h2
  simp [Equiv.Perm.mem_support, List.formPerm_apply_mem_eq_self_iff _ hn _ ha, hl, hh]
end LeanEval.LaxSupport

end
-- END INLINED FILE: Mathlib/Support/lax_approximation_c30dd8dbf7/FullCycle.lean

-- BEGIN INLINED FILE: Mathlib/Support/lax_approximation_c30dd8dbf7/GridConnectivity.lean
section

/- Pure combinatorial connectedness of a rectangular grid.  We use the non-
  wrapping grid: consecutive entries in one coordinate give edges. -/
open Function Equiv

namespace LeanEval.LaxSupport

/-- One (unoriented) elementary step in a finite rectangular grid. -/
def GridStep {d N : ℕ} (u v : Fin d → Fin N) : Prop :=
  ∃ i : Fin d,
    (((u i).val + 1 = (v i).val) ∨ ((v i).val + 1 = (u i).val)) ∧
    ∀ j : Fin d, j ≠ i → u j = v j

lemma GridStep.symm {d N : ℕ} {u v : Fin d → Fin N}
    (h : GridStep u v) : GridStep v u := by
  rcases h with ⟨i, h, hrest⟩
  exact ⟨i, h.symm, fun j hj => (hrest j hj).symm⟩

lemma GridStep.ne {d N : ℕ} {u v : Fin d → Fin N}
    (h : GridStep u v) : u ≠ v := by
  rcases h with ⟨i, h, _⟩
  intro e
  have he : (u i).val = (v i).val := congrArg (fun t => (t i).val) e
  omega

/-- Changing one coordinate to any other value is a chain of elementary
steps. This version is formulated for an arbitrary equivalence relation,
which is particularly convenient for permutation orbits. -/
lemma rel_update
    {d N : ℕ} (hN : 0 < N)
    (R : (Fin d → Fin N) → (Fin d → Fin N) → Prop)
    (hrefl : ∀ u, R u u) (hsymm : ∀ {u v}, R u v → R v u)
    (htrans : ∀ {u v w}, R u v → R v w → R u w)
    (hedge : ∀ {u v}, GridStep u v → R u v)
    (u : Fin d → Fin N) (i : Fin d) (a : Fin N) :
    R u (Function.update u i a) := by
  classical
  -- First connect zero to any entry in coordinate `i`.
  let z : Fin N := ⟨0, hN⟩
  have chain : ∀ t : Nat, ∀ ht : t < N,
      R (Function.update u i z)
        (Function.update u i (⟨t, ht⟩ : Fin N)) := by
    intro t
    induction t with
    | zero =>
        intro ht
        have e : (⟨0, ht⟩ : Fin N) = z := by apply Fin.ext; rfl
        rw [e]
        exact hrefl _
    | succ t ih =>
        intro ht
        have ht' : t < N := lt_trans (Nat.lt_succ_self _) ht
        let b : Fin N := ⟨t, ht'⟩
        let c : Fin N := ⟨t+1, ht⟩
        have hs : GridStep (Function.update u i b)
              (Function.update u i c) := by
          refine ⟨i, Or.inl ?_, ?_⟩
          · simp [b, c, Function.update_self]
          · intro j hj
            simp [Function.update, hj]
        have h1 := ih ht'
        have h2 : R (Function.update u i b)
              (Function.update u i c) := hedge hs
        exact htrans h1 h2
  have hzero_a : R (Function.update u i z) (Function.update u i a) := by
    simpa using chain a.val a.isLt
  have hzero_u : R (Function.update u i z)
        (Function.update u i (u i)) := by
    simpa using chain (u i).val (u i).isLt
  have heq : Function.update u i (u i) = u := Function.update_eq_self _ _
  -- go from the current value to zero and then to the requested value
  exact htrans (by simpa [heq] using (hsymm hzero_u)) hzero_a

/-- The undirected finite grid is connected.  If an equivalence relation
contains all elementary coordinate steps, it contains every pair. -/
lemma rel_all_of_gridStep
    {d N : ℕ} (hN : 0 < N)
    (R : (Fin d → Fin N) → (Fin d → Fin N) → Prop)
    (hrefl : ∀ u, R u u) (hsymm : ∀ {u v}, R u v → R v u)
    (htrans : ∀ {u v w}, R u v → R v w → R u w)
    (hedge : ∀ {u v}, GridStep u v → R u v) :
    ∀ u v, R u v := by
  classical
  intro u v
  -- set the coordinates in a finite set one after another
  let w : Finset (Fin d) → (Fin d → Fin N) := fun s j =>
    if j ∈ s then v j else u j
  have go : ∀ s : Finset (Fin d), R u (w s) := by
    intro s
    classical
    induction s using Finset.induction with
    | empty =>
        have h : w ∅ = u := by funext j; simp [w]
        rw [h]; exact hrefl _
    | @insert i s hi ih =>
        have hjoin : w (insert i s) = Function.update (w s) i (v i) := by
          funext j
          by_cases hj : j = i
          · subst j; simp [w, hi]
          · simp [w, hj]
        have hs : R (w s) (Function.update (w s) i (v i)) :=
          rel_update hN R hrefl (@hsymm) (@htrans) (@hedge) (w s) i (v i)
        rw [hjoin]
        exact htrans ih hs
  have hv : w Finset.univ = v := by funext j; simp [w]
  simpa [hv] using go Finset.univ

/-- In particular, a permutation of a nonempty non-singleton grid whose
orbits contain each elementary edge is a full cycle as soon as it moves
every point. -/
lemma perm_isCycle_of_edges {d N : ℕ} (hN : 0 < N)
    (f : Equiv.Perm (Fin d → Fin N))
    (hmov : ∀ u, f u ≠ u)
    (hedge : ∀ {u v}, GridStep u v → f.SameCycle u v)
    [Nonempty (Fin d → Fin N)] : f.IsCycle := by
  classical
  let u0 : Fin d → Fin N := Classical.choice ‹Nonempty (Fin d → Fin N)›
  refine ⟨u0, hmov _, ?_⟩
  intro v hv
  exact rel_all_of_gridStep hN (fun a b => f.SameCycle a b)
    (fun a => Equiv.Perm.SameCycle.refl f a)
    (fun {_ _} h => Equiv.Perm.SameCycle.symm h)
    (fun {_ _ _} h h' => Equiv.Perm.SameCycle.trans h h')
    (fun {_ _} h => hedge h) u0 v

/-- Contrapositive form used in the cycle-joining procedure. -/
lemma exists_edge_not_sameCycle {d N : ℕ} (hN : 0 < N)
    (f : Equiv.Perm (Fin d → Fin N))
    (hmov : ∀ u, f u ≠ u)
    [Nonempty (Fin d → Fin N)] (hnot : ¬ f.IsCycle) :
    ∃ u v, GridStep u v ∧ ¬ f.SameCycle u v := by
  classical
  by_contra h
  push_neg at h
  exact hnot (perm_isCycle_of_edges hN f hmov (by
    intro u v huv
    exact h u v huv))

end LeanEval.LaxSupport

end
-- END INLINED FILE: Mathlib/Support/lax_approximation_c30dd8dbf7/GridConnectivity.lean

-- BEGIN INLINED FILE: Mathlib/Support/lax_approximation_c30dd8dbf7/CutJoin.lean
section

open Equiv Function Finset
namespace LeanEval.LaxSupport

/- The finite orbit count of a permutation (including fixed point orbits). -/
noncomputable def orbitCount {α : Type*} [Fintype α]
    (f : Equiv.Perm α) : ℕ := by
  classical
  exact @Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid f))
    (Quotient.fintype _)

lemma orbitCount_pos {α : Type*} [Fintype α] [Nonempty α]
    (f : Equiv.Perm α) : 0 < orbitCount f := by
  classical
  unfold orbitCount
  exact Fintype.card_pos_iff.mpr ⟨Quotient.mk _ (Classical.choice (inferInstance : Nonempty α))⟩

variable {α : Type*} [Fintype α] [DecidableEq α]

@[simp] lemma swap_mul_apply_formula (f : Equiv.Perm α) (a b x : α) :
    ((Equiv.swap a b) * f) x = if f x = a then b else if f x = b then a else f x := by
  classical
  rw [Equiv.Perm.mul_apply]
  by_cases h : f x = a
  · simp [h]
  by_cases h' : f x = b
  · -- if a=b this clashes with h
    have hab : b ≠ a := by intro e; exact h (h'.trans e)
    simp [h, h', hab]
  · simpa [h, h'] using (Equiv.swap_apply_of_ne_of_ne h h')

lemma sameCycle_self_apply_perm (f : Equiv.Perm α) (x : α) :
    f.SameCycle x (f x) := by
  refine ⟨1, ?_⟩
  simp

/- If two points are in different `f`--orbits, swapping their images joins
these orbits.  This small finite lemma is the useful form of the usual
cut--join observation: first we show the two cut labels themselves are in
one new orbit. -/
lemma sameCycle_swap_mul_between {f : Equiv.Perm α} {a b : α}
    (haborb : ¬ f.SameCycle a b) :
    ((Equiv.swap a b) * f).SameCycle a b := by
  classical
  let g : Equiv.Perm α := (Equiv.swap a b) * f
  -- The two labels are distinct.
  have hab : a ≠ b := by
    intro h; apply haborb; simpa [h] using (Equiv.Perm.SameCycle.refl f a)
  -- Look at the first return time of `b` in its old orbit.
  let P : ℕ → Prop := fun t => 0 < t ∧ (f ^ t) b = b
  have hex : ∃ t, P t := by
    refine ⟨orderOf f, orderOf_pos f, ?_⟩
    rw [pow_orderOf_eq_one]
    rfl
  let L : ℕ := Nat.find hex
  have hL0 : 0 < L := (Nat.find_spec hex).1
  have hLret : (f ^ L) b = b := (Nat.find_spec hex).2
  have hmin : ∀ t : ℕ, 0 < t → t < L → (f ^ t) b ≠ b := by
    intro t ht htL hret
    exact (Nat.not_lt_of_ge (Nat.find_min' hex ⟨ht, hret⟩)) htL
  -- Along the b-cycle before its return the swapped permutation agrees with f.
  have hpath : ∀ t : ℕ, t < L → (g ^ t) b = (f ^ t) b := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      have ht' : t < L := Nat.lt_of_succ_lt ht
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih ht']
      -- it suffices that the next point is neither a nor b
      have hna : f ((f ^ t) b) ≠ a := by
        intro he
        -- a and b would then have been in the same old orbit
        apply haborb
        -- exhibit an integer power carrying a to b (symmetry)
        have hbtoa : f.SameCycle b a := by
          refine ⟨((t+1 : ℕ) : ℤ), ?_⟩
          -- powers are composed on the right
          change (f ^ (t+1 : ℕ)) b = a
          simpa [pow_succ', Equiv.Perm.mul_apply] using he
        exact Equiv.Perm.SameCycle.symm hbtoa
      have hnb : f ((f ^ t) b) ≠ b := by
        intro he
        have hret' : (f ^ (t+1)) b = b := by
          simpa [pow_succ', Equiv.Perm.mul_apply] using he
        exact hmin (t+1) (Nat.succ_pos _) ht hret'
      change (Equiv.swap a b) (f ((f ^ t) b)) = f ((f ^ t) b)
      exact Equiv.swap_apply_of_ne_of_ne hna hnb
  -- At the last step the old return to b is sent to a.
  have hlast : (g ^ L) b = a := by
    obtain ⟨t, htL⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL0)
    have ht : t < L := by omega
    have ih := hpath t ht
    rw [htL, pow_succ', Equiv.Perm.mul_apply, ih]
    have hfb : f ((f ^ t) b) = b := by
      have hh := hLret
      rw [htL] at hh
      simpa [pow_succ', Equiv.Perm.mul_apply] using hh
    -- the swap sends b to a
    change (Equiv.swap a b) (f ((f ^ t) b)) = a
    simp [hfb, hab]
  -- powers by naturals are allowed in SameCycle (an integer power)
  exact Equiv.Perm.SameCycle.symm <| by
    refine ⟨(L : ℤ), ?_⟩
    simpa [g] using hlast

/- `SameCycle f` is refined by the orbit relation after the join. -/
lemma sameCycle_le_swap_mul {f : Equiv.Perm α} {a b : α}
    (haborb : ¬ f.SameCycle a b) :
    ∀ {x y : α}, f.SameCycle x y →
      ((Equiv.swap a b) * f).SameCycle x y := by
  classical
  intro x y hxy
  let g : Equiv.Perm α := (Equiv.swap a b) * f
  have habg : g.SameCycle a b := sameCycle_swap_mul_between haborb
  -- Every old generator edge is an edge in the new equivalence relation.
  have hedge : ∀ u : α, g.SameCycle u (f u) := by
    intro u
    by_cases ha : f u = a
    · have hgb : g u = b := by
        simp [g, swap_mul_apply_formula, ha,
          (show (if True then b else if a = b then a else a) = b by simp)]
      -- shorter just note equality, then compose with a~b
      have h1 : g.SameCycle u b := by
        rw [← hgb]
        exact sameCycle_self_apply_perm g u
      have h2 := Equiv.Perm.SameCycle.trans h1 (Equiv.Perm.SameCycle.symm habg)
      simpa [ha] using h2
    · by_cases hb : f u = b
      · have hga : g u = a := by simp [g, swap_mul_apply_formula, ha, hb]
        have h1 : g.SameCycle u a := by
          rw [← hga]; exact sameCycle_self_apply_perm g u
        have h2 := Equiv.Perm.SameCycle.trans h1 habg
        simpa [hb] using h2
      · have heq : g u = f u := by simp [g, swap_mul_apply_formula, ha, hb]
        rw [← heq]
        exact sameCycle_self_apply_perm g u
  -- relations generated by the `f` edges (and their reverses)
  obtain ⟨z, hz⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hxy
  have hall : ∀ n : ℕ, g.SameCycle x ((f ^ n) x) := by
    intro n
    induction n with
    | zero => simp; exact Equiv.Perm.SameCycle.refl g x
    | succ n ih =>
      have hs : g.SameCycle ((f ^ n) x) (f ((f ^ n) x)) := hedge _
      have ht := Equiv.Perm.SameCycle.trans ih hs
      simpa [pow_succ', Equiv.Perm.mul_apply] using ht
  rw [← hz]
  exact hall z


lemma swap_mul_moved {f : Equiv.Perm α} {a b : α}
    (hmov : ∀ x, f x ≠ x) (haborb : ¬ f.SameCycle a b) :
    ∀ x, ((Equiv.swap a b) * f) x ≠ x := by
  classical
  intro x hx
  by_cases ha : f x = a
  · have he : x = b := by
      have hh : ((Equiv.swap a b) * f) x = b := by
        simp [swap_mul_apply_formula, ha]
      exact (hx.symm.trans hh)
    subst x
    apply haborb
    have hba : f.SameCycle b a := by
      rw [← ha]
      exact sameCycle_self_apply_perm f b
    exact Equiv.Perm.SameCycle.symm hba
  · by_cases hb : f x = b
    · have he : x = a := by
        have hh : ((Equiv.swap a b) * f) x = a := by
          simp [swap_mul_apply_formula, ha, hb]
        exact hx.symm.trans hh
      subst x
      apply haborb
      rw [← hb]
      exact sameCycle_self_apply_perm f a
    · have he : ((Equiv.swap a b) * f) x = f x := by
        simp [swap_mul_apply_formula, ha, hb]
      exact hmov x (he.symm.trans hx)

lemma orbitCount_swap_mul_lt {f : Equiv.Perm α} {a b : α}
    (haborb : ¬ f.SameCycle a b) :
    orbitCount ((Equiv.swap a b) * f) < orbitCount f := by
  classical
  let g : Equiv.Perm α := (Equiv.swap a b) * f
  let F : Quotient (Equiv.Perm.SameCycle.setoid f) →
      Quotient (Equiv.Perm.SameCycle.setoid g) :=
    Quotient.lift (fun x : α => Quotient.mk _ x)
      (by
        intro x y h
        exact Quotient.sound (sameCycle_le_swap_mul haborb h))
  have hsur : Function.Surjective F := by
    intro z
    refine Quotient.inductionOn z ?_
    intro x
    exact ⟨Quotient.mk _ x, rfl⟩
  have hnot : ¬ Function.Injective F := by
    intro hi
    have heq : F (Quotient.mk _ a) = F (Quotient.mk _ b) := by
      exact Quotient.sound (sameCycle_swap_mul_between haborb)
    have hold := hi heq
    exact haborb (Quotient.exact hold)
  exact Fintype.card_lt_of_surjective_not_injective F hsur hnot

/- Joining adjacent different cycles on a positive rectangular grid.  The
length is strictly below the initial number of orbits. -/
theorem exists_joins_to_cycle {d N : ℕ} (hN : 0 < N)
    (f : Equiv.Perm (Fin d → Fin N))
    (hmov : ∀ u, f u ≠ u) [Nonempty (Fin d → Fin N)] :
    ∃ l : List ((Fin d → Fin N) × (Fin d → Fin N)),
      (∀ p ∈ l, GridStep p.1 p.2) ∧
      l.length < orbitCount f ∧
      (l.foldl (fun g p => (Equiv.swap p.1 p.2) * g) f).IsCycle ∧
      (l.foldl (fun g p => (Equiv.swap p.1 p.2) * g) f).support = Finset.univ := by
  classical
  -- strong induction on the finite number of old orbits
  induction hcnt : orbitCount f using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hc : f.IsCycle
    · refine ⟨[], ?_, ?_, ?_, ?_⟩
      · simp
      · simpa [hcnt] using (orbitCount_pos f)
      · simpa using hc
      · ext x
        simp [Equiv.Perm.mem_support, hmov x]
    · obtain ⟨a,b,hab,hdiff⟩ := exists_edge_not_sameCycle hN f hmov hc
      let g : Equiv.Perm (Fin d → Fin N) := (Equiv.swap a b) * f
      have hgmov : ∀ u, g u ≠ u := swap_mul_moved hmov hdiff
      have hglt0 : orbitCount g < orbitCount f := orbitCount_swap_mul_lt hdiff
      have hglt : orbitCount g < n := by simpa [hcnt] using hglt0
      obtain ⟨l, hl, hlen, hcy, hsup⟩ := ih (orbitCount g) hglt g hgmov rfl
      refine ⟨(a,b)::l, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases (List.mem_cons.1 hp) with h | h
        · simpa [h] using hab
        · exact hl p h
      · simp only [List.length_cons]
        omega
      · simpa [g] using hcy
      · simpa [g] using hsup


/- Orbit bound for the independent lift on a product.  Every orbit meets the
slice with one fixed second coordinate.  Formulated after any equivalence so
it applies directly to the split grid. -/
theorem moved_pull_prod
    {A B X : Type*} [DecidableEq X]
    (e : X ≃ A × B) (t : Equiv.Perm A) (c : Equiv.Perm B)
    (hc : ∀ b, c b ≠ b) :
    ∀ x, (e.trans ((Equiv.prodCongr t c).trans e.symm)) x ≠ x := by
  intro x hx
  have hh := congrArg (fun z => (e z).2) hx
  have hev : e ((e.trans ((Equiv.prodCongr t c).trans e.symm)) x) =
      (t (e x).1, c (e x).2) := by
    rcases h : e x with ⟨a,b⟩
    simp [Equiv.trans_apply, Prod.map, h]
  rw [hev] at hh
  change c (e x).2 = (e x).2 at hh
  exact hc _ hh

theorem orbitCount_pull_prod_le
    {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
    [DecidableEq A] [DecidableEq B] [DecidableEq X] [Nonempty B]
    (e : X ≃ A × B) (t : Equiv.Perm A) (c : Equiv.Perm B)
    (hcy : c.IsCycle) (hc : ∀ b, c b ≠ b) :
    orbitCount (e.trans ((Equiv.prodCongr t c).trans e.symm)) ≤ Fintype.card A := by
  classical
  let p : Equiv.Perm (A × B) := Equiv.prodCongr t c
  let g : Equiv.Perm X := e.trans (p.trans e.symm)
  let b0 : B := Classical.choice (inferInstance : Nonempty B)
  -- powers of the pullback act by applying the same power on coordinates
  have hp : ∀ n : ℕ, ∀ z : A × B,
      (p ^ n) z = ((t ^ n) z.1, (c ^ n) z.2) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      simp only [pow_succ', Equiv.Perm.mul_apply, ih]
      rfl
  have geval : ∀ x : X, g x = e.symm (t (e x).1, c (e x).2) := by
    intro x
    dsimp [g, p]
    rcases h : e x with ⟨a,b⟩
    simp [Equiv.trans_apply, Prod.map, h]
  have hg : ∀ n : ℕ, ∀ x : X,
      (g ^ n) x = e.symm ((t ^ n) (e x).1, (c ^ n) (e x).2) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      rw [geval]
      simp [pow_succ', Equiv.Perm.mul_apply]
  let F : A → Quotient (Equiv.Perm.SameCycle.setoid g) :=
    fun a => Quotient.mk _ (e.symm (a,b0))
  have hsur : Function.Surjective F := by
    intro z
    refine Quotient.inductionOn z ?_
    intro x
    -- transitivity of a full second-coordinate cycle
    have hcb : c.SameCycle b0 (e x).2 :=
      hcy.sameCycle (hc b0) (hc (e x).2)
    obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hcb
    let a : A := (t ^ n).symm (e x).1
    refine ⟨a, Quotient.sound ?_⟩
    change g.SameCycle (e.symm (a,b0)) x
    refine ⟨(n:ℤ), ?_⟩
    change (g ^ n) (e.symm (a,b0)) = x
    rw [hg n]
    apply e.injective
    simp [a, hn]
  -- the quotient has a surjection from A
  change Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid g)) ≤ _
  exact Fintype.card_le_of_surjective F hsur

end LeanEval.LaxSupport

end
-- END INLINED FILE: Mathlib/Support/lax_approximation_c30dd8dbf7/CutJoin.lean

-- BEGIN INLINED MAIN PRELUDE

open LeanEval.Dynamics.LaxApproximation
open MeasureTheory
open scoped ENNReal
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

/-- A harmless but useful reduction: for an arbitrary positive `ℝ≥0∞`
 tolerance one can first work with a (strictly smaller) honest real
 tolerance.  In particular no top/infinite special case is required when
 estimating the grid error. -/
lemma exists_pos_real_ofReal_lt {e : ℝ≥0∞} (he : 0 < e) :
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < e := by
  rcases (ENNReal.lt_iff_exists_nnreal_btwn).1 he with ⟨r, hr0, hre⟩
  refine ⟨(r : ℝ), ?_, ?_⟩
  · exact_mod_cast hr0
  · simpa using hre

/-- To check a uniform error bound it suffices to check the ordinary
pointwise bound.  This little `essSup` wrapper is convenient because our
cube calculations never have to mention measurability/almost-everywhere
issues. -/
lemma deltaDist_le_of_forall {d : ℕ} (U V : VolumePreservingEquiv d)
    {c : ℝ≥0∞}
    (h : ∀ x : Torus d,
      edist (U.toMeasurableEquiv x) (V.toMeasurableEquiv x) ≤ c) :
    deltaDist U V ≤ c := by
  unfold deltaDist
  refine essSup_le_of_ae_le c ?_ ?_
  · filter_upwards [] with x
    exact h x
  · exact Filter.isCoboundedUnder_le_of_le _ (fun x => (bot_le : (0 : ℝ≥0∞) ≤ _))


open Set

/-- The half-open grid cubes really cover the torus.  We use the canonical
representative in `[0,1)` of each AddCircle coordinate and take a floor after
multiplying by `n`.  This formulation avoids any boundary choices, a small
point which is quite important for the (invertible) cube permutation later. -/
lemma exists_mem_cube {d : ℕ} (n : ℕ) (hn : 0 < n) (x : Torus d) :
    ∃ k : Fin d → Fin n, x ∈ cube n k := by
  classical
  -- canonical representatives of the coordinates
  let r : Fin d → ℝ := fun i =>
    ((AddCircle.equivIco (1 : ℝ) (0 : ℝ)) (x i) : Set.Ico (0 : ℝ) (0 + 1 : ℝ))
  have r0 (i : Fin d) : 0 ≤ r i := by
    exact ((AddCircle.equivIco (1 : ℝ) (0 : ℝ)) (x i)).property.1
  have r1 (i : Fin d) : r i < 1 := by
    have h := ((AddCircle.equivIco (1 : ℝ) (0 : ℝ)) (x i)).property.2
    simpa using h
  let m : Fin d → ℕ := fun i => ⌊r i * (n : ℝ)⌋₊
  have mn (i : Fin d) : m i < n := by
    have ha : 0 ≤ r i * (n : ℝ) :=
      mul_nonneg (r0 i) (by exact_mod_cast (Nat.zero_le n))
    apply (Nat.floor_lt ha).2
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    nlinarith [r1 i]
  let k : Fin d → Fin n := fun i => ⟨m i, mn i⟩
  refine ⟨k, ?_⟩
  intro i
  refine ⟨r i, ?_, ?_, ?_⟩
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    -- floor is the lower endpoint of its small interval
    have hle : (m i : ℝ) ≤ r i * (n : ℝ) := by
      simpa [m] using (Nat.floor_le (mul_nonneg (r0 i)
        (by exact_mod_cast (Nat.zero_le n) : (0:ℝ) ≤ (n:ℝ))))
    change ((m i : ℕ) : ℝ) / (n : ℝ) ≤ r i
    exact (div_le_iff₀ hn').2 (by simpa [mul_comm] using hle)
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlt : r i * (n : ℝ) < (m i : ℝ) + 1 := by
      simpa [m] using (Nat.lt_floor_add_one (r i * (n : ℝ)))
    change r i < (((m i : ℕ) : ℝ) + 1) / (n : ℝ)
    exact (lt_div_iff₀ hn').2 (by simpa [mul_comm] using hlt)
  · -- and this representative is indeed the original point of AddCircle
    have hcoe : ((r i : ℝ) : AddCircle (1 : ℝ)) = x i := by
      exact AddCircle.coe_equivIco
    exact hcoe.symm


/-- With `n>0` the same half-open convention also makes the cube containing a
point unique.  Thus in definitions of piecewise translations there is no
choice on faces of the grid. -/
lemma mem_cube_unique {d n : ℕ} (hn : 0 < n) (x : Torus d)
    {k l : Fin d → Fin n} (hk : x ∈ cube n k) (hl : x ∈ cube n l) :
    k = l := by
  classical
  funext i
  rcases hk i with ⟨a, hka, hka', ha⟩
  rcases hl i with ⟨b, hlb, hlb', hb⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- both real representatives of this coordinate lie in the fundamental
  -- half-open interval, so equality in AddCircle is equality in `ℝ`.
  have ha0 : (0 : ℝ) ≤ a :=
    le_trans (by positivity : (0:ℝ) ≤ (k i : ℝ) / (n:ℝ)) hka
  have hb0 : (0 : ℝ) ≤ b :=
    le_trans (by positivity : (0:ℝ) ≤ (l i : ℝ) / (n:ℝ)) hlb
  have hkn : ((k i : ℝ) + 1) ≤ (n : ℝ) := by
    have hv : (k i : ℕ) < n := (k i).isLt
    exact_mod_cast hv
  have hln : ((l i : ℝ) + 1) ≤ (n : ℝ) := by
    have hv : (l i : ℕ) < n := (l i).isLt
    exact_mod_cast hv
  have ha1 : a < 1 := by
    have hq : ((k i : ℝ) + 1) / (n : ℝ) ≤ (1 : ℝ) := by
      apply (div_le_iff₀ hn').2
      simpa using hkn
    exact lt_of_lt_of_le hka' hq
  have hb1 : b < 1 := by
    have hq : ((l i : ℝ) + 1) / (n : ℝ) ≤ (1 : ℝ) := by
      apply (div_le_iff₀ hn').2
      simpa using hln
    exact lt_of_lt_of_le hlb' hq
  have hab : a = b := by
    have hea := AddCircle.equivIco_coe_eq (p := (1:ℝ)) (a := (0:ℝ))
      (x := a) (by exact ⟨ha0, by simpa using ha1⟩ : a ∈ Set.Ico (0:ℝ) (0+1))
    have heb := AddCircle.equivIco_coe_eq (p := (1:ℝ)) (a := (0:ℝ))
      (x := b) (by exact ⟨hb0, by simpa using hb1⟩ : b ∈ Set.Ico (0:ℝ) (0+1))
    have hc : ((a : ℝ) : AddCircle (1:ℝ)) = (b : AddCircle (1:ℝ)) :=
      ha.symm.trans hb
    have he : (⟨a, (by exact ⟨ha0, by simpa using ha1⟩ : a ∈ Set.Ico (0:ℝ) (0+1))⟩ :
          Set.Ico (0:ℝ) (0+1)) =
        ⟨b, (by exact ⟨hb0, by simpa using hb1⟩ : b ∈ Set.Ico (0:ℝ) (0+1))⟩ := by
      -- apply the equivalence to equality in the quotient
      simpa [hea, heb] using
        congrArg (AddCircle.equivIco (1:ℝ) (0:ℝ)) hc
    exact congrArg Subtype.val he
  have hval : (k i : ℕ) = (l i : ℕ) := by
    -- two disjoint half-open intervals of the same mesh cannot both
    -- contain `a`.
    have hle1 : (k i : ℝ) ≤ (l i : ℝ) := by
      by_contra hnot
      have hltN : (l i : ℕ) < (k i : ℕ) := by
        exact_mod_cast (lt_of_not_ge hnot)
      have hstep : ((l i : ℝ) + 1) / (n:ℝ) ≤ (k i : ℝ) / (n:ℝ) := by
        apply (div_le_div_iff_of_pos_right hn').2
        exact_mod_cast hltN
      have bad : b < ((k i : ℝ) / (n:ℝ)) := lt_of_lt_of_le hlb' hstep
      have good : ((k i : ℝ) / (n:ℝ)) ≤ b := by simpa [hab] using hka
      linarith
    have hle2 : (l i : ℝ) ≤ (k i : ℝ) := by
      by_contra hnot
      have hltN : (k i : ℕ) < (l i : ℕ) := by
        exact_mod_cast (lt_of_not_ge hnot)
      have hstep : ((k i : ℝ) + 1) / (n:ℝ) ≤ (l i : ℝ) / (n:ℝ) := by
        apply (div_le_div_iff_of_pos_right hn').2
        exact_mod_cast hltN
      have bad : a < ((l i : ℝ) / (n:ℝ)) := lt_of_lt_of_le hka' hstep
      have good : ((l i : ℝ) / (n:ℝ)) ≤ a := by simpa [hab] using hlb
      linarith
    exact_mod_cast (le_antisymm hle1 hle2)
  exact Fin.ext hval


/-- The unique index of the (positive mesh) half-open cube containing a
 torus point. We keep it noncomputable; all the equations used later are the
 covering and uniqueness lemmas, not the particular floor formula. -/
noncomputable def cubeIndex {d : ℕ} (n : ℕ) (hn : 0 < n) (x : Torus d) :
    Fin d → Fin n :=
  Classical.choose (exists_mem_cube n hn x)

lemma mem_cubeIndex {d : ℕ} (n : ℕ) (hn : 0 < n) (x : Torus d) :
    x ∈ cube n (cubeIndex n hn x) :=
  Classical.choose_spec (exists_mem_cube n hn x)

lemma cubeIndex_eq_of_mem {d : ℕ} (n : ℕ) (hn : 0 < n)
    {x : Torus d} {k : Fin d → Fin n} (h : x ∈ cube n k) :
    cubeIndex n hn x = k :=
  mem_cube_unique hn x (mem_cubeIndex n hn x) h

@[simp] lemma mem_cube_iff_index_eq {d : ℕ} (n : ℕ) (hn : 0 < n)
    {x : Torus d} {k : Fin d → Fin n} :
    x ∈ cube n k ↔ cubeIndex n hn x = k := by
  constructor
  · exact cubeIndex_eq_of_mem n hn
  · intro h
    simpa [h] using (mem_cubeIndex n hn x)



/-- Translation by the grid displacement really sends a point of one
half-open cube to the indicated target cube.  The proof uses real lifts; the
target lift is still in `[0,1)` so no modular-boundary case is needed. -/
lemma mem_cube_add_cubeShift {d n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) (k : Fin d → Fin n)
    {x : Torus d} (hx : x ∈ cube n k) :
    (fun i => x i + cubeShift n σ k i) ∈ cube n (σ k) := by
  intro i
  rcases hx i with ⟨a, ha0, ha1, ha⟩
  let t : ℝ := (((σ k) i : ℕ) : ℝ) / (n:ℝ) - ((k i : ℕ) : ℝ) / (n:ℝ)
  refine ⟨a + t, ?_, ?_, ?_⟩
  · -- it is exactly the old interval translated by its difference of
    -- lower endpoints
    have heq : (((σ k) i : ℝ) / (n:ℝ)) =
        ((k i : ℝ) / (n:ℝ)) + t := by
      dsimp [t]
      ring
    -- spelling the identity out is a little more robust than asking
    -- `linarith` to normalise all divisions.
    rw [heq]
    linarith
  · have heq : (((σ k) i : ℝ) + 1) / (n:ℝ) =
        (((k i : ℝ) + 1) / (n:ℝ)) + t := by
      dsimp [t]
      ring
    rw [heq]
    linarith
  · -- Addition on AddCircle is induced from addition on ℝ.
    have ht : cubeShift n σ k i = (t : AddCircle (1:ℝ)) := by
      -- converting the integer subtraction in `cubeShift` to reals
      simp [cubeShift, t]
      congr 1
      push_cast
      ring
    change x i + cubeShift n σ k i = _
    rw [ht, ha]
    rfl


/-- The point map which translates each positive-mesh cube onto the cube
specified by a permutation. The index lemmas make its inverse entirely
formal. -/
noncomputable def gridFun {d : ℕ} (n : ℕ) (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) (x : Torus d) : Torus d :=
  fun i => x i + cubeShift n σ (cubeIndex n hn x) i

lemma gridFun_mem_cube {d n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) {k : Fin d → Fin n}
    {x : Torus d} (hx : x ∈ cube n k) :
    gridFun n hn σ x ∈ cube n (σ k) := by
  have hi : cubeIndex n hn x = k := cubeIndex_eq_of_mem n hn hx
  change (fun i => x i + cubeShift n σ (cubeIndex n hn x) i) ∈ cube n (σ k)
  rw [hi]
  exact mem_cube_add_cubeShift hn σ k hx

@[simp] lemma cubeIndex_gridFun {d n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) (x : Torus d) :
    cubeIndex n hn (gridFun n hn σ x) = σ (cubeIndex n hn x) := by
  apply cubeIndex_eq_of_mem n hn
  exact gridFun_mem_cube hn σ (mem_cubeIndex n hn x)

lemma gridFun_left_inv {d n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) (x : Torus d) :
    gridFun n hn σ.symm (gridFun n hn σ x) = x := by
  classical
  funext i
  -- after the first translation the cube index is `σ k`; the inverse
  -- translation has the opposite real displacement.
  simp only [gridFun, cubeIndex_gridFun]
  have hcancel : cubeShift n σ (cubeIndex n hn x) i +
        cubeShift n σ.symm (σ (cubeIndex n hn x)) i =
        (0 : AddCircle (1:ℝ)) := by
    -- equality follows already over ℝ
    -- the simplification of the inverse permutation removes its `σ`.
    simp [cubeShift]
    -- rewrite addition of quotient points as the quotient of a sum
    change QuotientAddGroup.mk' _ _ + QuotientAddGroup.mk' _ _ = _
    rw [← map_add]
    congr 1
    push_cast
    ring_nf
    rfl
  simpa [add_assoc, hcancel]

/-- As a plain equivalence (before supplying measurability/measure
 preservation), grid permutations are genuine mutually inverse bijections
 of the torus. -/
noncomputable def gridEquiv {d : ℕ} (n : ℕ) (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) : Torus d ≃ Torus d where
  toFun := gridFun n hn σ
  invFun := gridFun n hn σ.symm
  left_inv := gridFun_left_inv hn σ
  right_inv := by
    intro x
    simpa using (gridFun_left_inv hn σ.symm x)

@[simp] lemma gridEquiv_apply {d n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) (x : Torus d) :
    gridEquiv n hn σ x = gridFun n hn σ x := rfl


/-- The positive-mesh half-open cubes are measurable.  Express them using the
measurable canonical lift `equivIco`; the only care is checking that every
lift appearing in the original, existential definition is already in
`[0,1)`. -/
lemma measurableSet_cube {d n : ℕ} (hn : 0 < n) (k : Fin d → Fin n) :
    MeasurableSet (cube n k : Set (Torus d)) := by
  classical
  let A : Fin d → Set (AddCircle (1:ℝ)) := fun i =>
    (fun z : AddCircle (1:ℝ) =>
      (((AddCircle.equivIco (1:ℝ) (0:ℝ)) z) : ℝ)) ⁻¹'
        Set.Ico ((k i : ℝ)/(n:ℝ)) (((k i : ℝ)+1)/(n:ℝ))
  have hA (i : Fin d) : MeasurableSet (A i) := by
    dsimp [A]
    apply MeasurableSet.preimage measurableSet_Ico
    have hme : Measurable (AddCircle.equivIco (1:ℝ) (0:ℝ)) :=
      (AddCircle.measurableEquivIco (1:ℝ) (0:ℝ)).measurable
    exact hme.subtype_val
  have heq : (cube n k : Set (Torus d)) = (Set.univ.pi A) := by
    ext x
    constructor
    · intro hx
      -- the canonical `[0,1)` lift of each coordinate is the witness
      -- from the half-open cube definition.
      have hxi : ∀ i : Fin d, x i ∈ A i := by
        intro i
        rcases hx i with ⟨a, ha0, ha1, ha⟩
        have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
        have a0 : (0:ℝ) ≤ a :=
          le_trans (by positivity : (0:ℝ) ≤ (k i : ℝ)/(n:ℝ)) ha0
        have hkn : ((k i : ℝ) + 1) ≤ (n : ℝ) := by
          exact_mod_cast (k i).isLt
        have a1 : a < 1 := by
          have hq : ((k i : ℝ)+1)/(n:ℝ) ≤ (1:ℝ) := by
            apply (div_le_iff₀ hn').2
            simpa using hkn
          exact lt_of_lt_of_le ha1 hq
        have hea := AddCircle.equivIco_coe_eq (p := (1:ℝ)) (a := (0:ℝ))
          (x := a) (by exact ⟨a0, by simpa using a1⟩ : a ∈ Set.Ico (0:ℝ) (0+1))
        change (((AddCircle.equivIco (1:ℝ) (0:ℝ)) (x i) : ℝ)) ∈
          Set.Ico ((k i : ℝ)/(n:ℝ)) (((k i : ℝ)+1)/(n:ℝ))
        rw [ha, hea]
        exact ⟨ha0, ha1⟩
      exact Set.mem_pi.mpr (fun j hj => hxi j)
    · intro hx
      have hh : ∀ i : Fin d, x i ∈ A i := fun i =>
        (Set.mem_pi.mp hx i (by simp))
      intro i
      have hi : (((AddCircle.equivIco (1:ℝ) (0:ℝ)) (x i) : ℝ)) ∈
          Set.Ico ((k i : ℝ)/(n:ℝ)) (((k i : ℝ)+1)/(n:ℝ)) := hh i
      refine ⟨(((AddCircle.equivIco (1:ℝ) (0:ℝ)) (x i) : ℝ)), hi.1, hi.2, ?_⟩
      exact (AddCircle.coe_equivIco).symm
  rw [heq]
  exact MeasurableSet.pi (Set.countable_univ) (fun j _ => hA j)


lemma measurable_cubeIndex {d n : ℕ} (hn : 0 < n) :
    Measurable (cubeIndex n hn : Torus d → (Fin d → Fin n)) := by
  classical
  apply measurable_to_countable'
  intro k
  have heq : (cubeIndex n hn : Torus d → (Fin d → Fin n)) ⁻¹' ({k} : Set _) =
      cube n k := by
    ext x
    change (cubeIndex n hn x = k) ↔ _
    symm
    exact mem_cube_iff_index_eq n hn
  rw [heq]
  exact measurableSet_cube hn k

lemma measurable_gridFun {d n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) :
    Measurable (gridFun n hn σ : Torus d → Torus d) := by
  classical
  apply measurable_pi_lambda
  intro i
  change Measurable (fun x : Torus d => x i +
      cubeShift n σ (cubeIndex n hn x) i)
  apply Measurable.add (measurable_pi_apply i)
  exact (measurable_of_finite (fun k : (Fin d → Fin n) =>
    cubeShift n σ k i)).comp (measurable_cubeIndex hn)

/-- Grid permutations, in particular, are measurable equivalences before any
measure calculation. -/
noncomputable def gridMeasurableEquiv {d : ℕ} (n : ℕ) (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) : Torus d ≃ᵐ Torus d where
  toEquiv := gridEquiv n hn σ
  measurable_toFun := measurable_gridFun hn σ
  measurable_invFun := measurable_gridFun hn σ.symm


/-- Packaging lemma: once measure preservation of the (measurable)
piecewise permutation is checked, it has exactly the `VolumePreservingEquiv`
expected by the problem. -/
noncomputable def gridVPE {d n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n))
    (hmp : MeasurePreserving (gridFun n hn σ)
      (volume : Measure (Torus d)) volume) : VolumePreservingEquiv d where
  toMeasurableEquiv := gridMeasurableEquiv n hn σ
  measurePreserving := hmp

lemma gridVPE_isCyclic {d n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n))
    (hmp : MeasurePreserving (gridFun n hn σ)
      (volume : Measure (Torus d)) volume)
    (hc : σ.IsCycle) (hs : σ.support = Finset.univ) :
    IsCyclicCubeExchange (gridVPE hn σ hmp) n := by
  refine ⟨σ, hc, hs, ?_⟩
  intro k x hx i
  have hi : cubeIndex n hn x = k := cubeIndex_eq_of_mem n hn hx
  change gridFun n hn σ x i = _
  simp [gridFun, hi]


/-- The finite half-open partition can be used to integrate/measure a set by
its pieces. -/
lemma measure_eq_sum_inter_cube {d n : ℕ} (hn : 0 < n)
    (A : Set (Torus d)) (hA : MeasurableSet A) :
    volume A = ∑ k : (Fin d → Fin n), volume (A ∩ cube n k) := by
  classical
  have hcover : A = ⋃ k : (Fin d → Fin n), (A ∩ cube n k) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := exists_mem_cube n hn x
      exact ⟨k, hx, hk⟩
    · exact fun ⟨k, hx, hk⟩ => hx
  have hp : (Set.univ : Set (Fin d → Fin n)).PairwiseDisjoint
      (fun k => A ∩ cube n k) := by
    intro k hk l hl hkl
    change Disjoint (A ∩ cube n k) (A ∩ cube n l)
    rw [Set.disjoint_left]
    intro x hx hxl
    have he := mem_cube_unique hn x hx.2 hxl.2
    exact hkl he
  calc
    volume A = volume (⋃ k : (Fin d → Fin n), (A ∩ cube n k)) := congrArg _ hcover
    _ = _ := by simpa using
      (measure_biUnion_finset (μ := (volume : Measure (Torus d)))
      (s := (Finset.univ : Finset (Fin d → Fin n)))
      (f := fun k => A ∩ cube n k)
        (by simpa using hp)
        (fun k _ => hA.inter (measurableSet_cube hn k)))

lemma cubeShift_cancel {d n : ℕ} (σ : Equiv.Perm (Fin d → Fin n))
    (k : Fin d → Fin n) (i : Fin d) :
    cubeShift n σ k i + cubeShift n σ.symm (σ k) i =
      (0 : AddCircle (1:ℝ)) := by
  classical
  simp [cubeShift]
  change QuotientAddGroup.mk' _ _ + QuotientAddGroup.mk' _ _ = _
  rw [← map_add]
  ring_nf
  rfl

lemma preimage_cube_addVec {d n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) (k : Fin d → Fin n) :
    (fun x : Torus d => x + (fun i => cubeShift n σ k i)) ⁻¹'
        cube n (σ k) = cube n k := by
  classical
  ext x
  constructor
  · intro hx
    have hback := mem_cube_add_cubeShift hn σ.symm (σ k) hx
    have heq : (fun i =>
        (x + (fun i => cubeShift n σ k i)) i +
          cubeShift n σ.symm (σ k) i) = x := by
      funext i
      change (x i + cubeShift n σ k i) +
        cubeShift n σ.symm (σ k) i = x i
      rw [add_assoc, cubeShift_cancel σ k i]
      simp
    -- unfold application notation in the previous membership
    have : (fun i =>
        (x + (fun i => cubeShift n σ k i)) i +
          cubeShift n σ.symm (σ k) i) ∈ cube n k := by
      simpa using hback
    rw [heq] at this
    exact this
  · intro hx
    exact mem_cube_add_cubeShift hn σ k hx

lemma inter_preimage_grid_eq {d n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) (k : Fin d → Fin n)
    (A : Set (Torus d)) :
    (gridFun n hn σ ⁻¹' A) ∩ cube n k =
      (fun x : Torus d => x + (fun i => cubeShift n σ k i)) ⁻¹'
        (A ∩ cube n (σ k)) := by
  classical
  ext x
  constructor
  · intro hx
    have hi := cubeIndex_eq_of_mem n hn hx.2
    have hfun : gridFun n hn σ x =
        (x + (fun i => cubeShift n σ k i)) := by
      funext i; change x i + cubeShift n σ (cubeIndex n hn x) i = _
      -- pointwise addition in the Pi group
      change x i + cubeShift n σ (cubeIndex n hn x) i =
        x i + cubeShift n σ k i
      simp [hi]
    constructor
    · simpa [hfun] using hx.1
    · exact mem_cube_add_cubeShift hn σ k hx.2
  · intro hx
    have hk : x ∈ cube n k := by
      have : x ∈ (fun z : Torus d => z + (fun i => cubeShift n σ k i)) ⁻¹'
          (cube n (σ k)) := hx.2
      rw [preimage_cube_addVec hn σ k] at this
      exact this
    have hi := cubeIndex_eq_of_mem n hn hk
    have hfun : gridFun n hn σ x =
        (x + (fun i => cubeShift n σ k i)) := by
      funext i
      change x i + cubeShift n σ (cubeIndex n hn x) i =
        x i + cubeShift n σ k i
      simp [hi]
    exact ⟨by simpa [hfun] using hx.1, hk⟩

lemma measurePreserving_gridFun {d n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) :
    MeasurePreserving (gridFun n hn σ)
      (volume : Measure (Torus d)) volume := by
  classical
  refine ⟨measurable_gridFun hn σ, ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_gridFun hn σ) hA]
  -- partition both sides into cubes
  rw [measure_eq_sum_inter_cube hn _
      (MeasurableSet.preimage hA (measurable_gridFun hn σ)),
      measure_eq_sum_inter_cube hn _ hA]
  -- each piece is a translate of its target piece
  have hpiece (k : Fin d → Fin n) :
      volume ((gridFun n hn σ ⁻¹' A) ∩ cube n k) =
        volume (A ∩ cube n (σ k)) := by
    rw [inter_preimage_grid_eq hn σ k A]
    let v : Torus d := fun i => cubeShift n σ k i
    have mp := measurePreserving_add_right (volume : Measure (Torus d)) v
    have hh : MeasurableSet (A ∩ cube n (σ k)) :=
      hA.inter (measurableSet_cube hn (σ k))
    have heval := Measure.map_apply (μ := (volume : Measure (Torus d))) mp.measurable hh
    -- use invariance of Haar measure for this constant translation
    have hm := mp.map_eq
    change volume ((fun x : Torus d => x + v) ⁻¹' (A ∩ cube n (σ k))) = _
    rw [hm] at heval
    exact heval.symm
  simp_rw [hpiece]
  -- σ just reindexes the finite sum
  exact Equiv.sum_comp σ (fun k => volume (A ∩ cube n k))


/-- All pieces of a positive finite grid have the same Haar mass.  This
uses only translation invariance; no formula for the mass is needed in
Hall's counting argument. -/
lemma measure_cube_eq {d n : ℕ} (hn : 0 < n)
    (k l : Fin d → Fin n) :
    (volume : Measure (Torus d)) (cube n k) = volume (cube n l) := by
  classical
  let σ : Equiv.Perm (Fin d → Fin n) := Equiv.swap k l
  let v : Torus d := fun i => cubeShift n σ k i
  have hsig : σ k = l := by
    dsimp [σ]
    exact Equiv.swap_apply_left k l
  have hpre :
      (fun x : Torus d => x + v) ⁻¹' cube n l = cube n k := by
    simpa [v, hsig] using (preimage_cube_addVec hn σ k)
  have mp := measurePreserving_add_right (volume : Measure (Torus d)) v
  have hh : MeasurableSet (cube n l : Set (Torus d)) :=
    measurableSet_cube hn l
  have heval := Measure.map_apply (μ := (volume : Measure (Torus d)))
    mp.measurable hh
  rw [mp.map_eq] at heval
  rw [← hpre]
  exact heval.symm

/-- Haar mass of a grid cube is nonzero.  It is convenient to keep this
qualitative fact separate; it avoids division in ENNReal Hall arguments. -/
lemma measure_cube_ne_zero {d n : ℕ} (hn : 0 < n)
    (k : Fin d → Fin n) :
    (volume : Measure (Torus d)) (cube n k) ≠ 0 := by
  classical
  -- if one cube vanished, equal mass would make every cube vanish,
  -- contradicting the mass of the full compact group.
  intro hk
  have hall (j : Fin d → Fin n) :
      (volume : Measure (Torus d)) (cube n j) = 0 := by
    calc
      (volume : Measure (Torus d)) (cube n j) =
          (volume : Measure (Torus d)) (cube n k) := measure_cube_eq hn j k
      _ = 0 := hk
  have hu : (volume : Measure (Torus d)) (Set.univ : Set (Torus d)) = 0 := by
    -- same finite disjoint partition as in `measure_eq_sum_inter_cube`
    have h := measure_eq_sum_inter_cube (d:=d) hn
      (Set.univ : Set (Torus d)) MeasurableSet.univ
    simpa [hall] using h
  -- The Haar/volume measure of this nonempty compact group is not zero.
  -- Mathlib supplies this through positivity of open sets; no normalization
  -- of Haar measure is used here.
  have hv : (volume : Measure (Torus d)) ≠ 0 :=
    NeZero.ne (volume : Measure (Torus d))
  exact hv ((Measure.measure_univ_eq_zero).1 hu)


/-- A volume preserving homeomorphism gives the same mass to the image of
one measurable cube. -/
lemma measure_image_cube {d n : ℕ} (hn : 0 < n)
    (T : ToralDynamicalSystem d) (k : Fin d → Fin n) :
    (volume : Measure (Torus d)) (T.toHomeomorph '' cube n k) =
      (volume : Measure (Torus d)) (cube n k) := by
  classical
  have hme : Measurable (T.toHomeomorph : Torus d → Torus d) :=
    T.toHomeomorph.continuous.measurable
  have himg : MeasurableSet (T.toHomeomorph '' (cube n k : Set (Torus d))) := by
    -- use the continuous inverse to express the image as a preimage
    have heq : T.toHomeomorph '' (cube n k : Set (Torus d)) =
        T.toHomeomorph.symm ⁻¹' (cube n k : Set (Torus d)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hy
        refine ⟨T.toHomeomorph.symm y, hy, ?_⟩
        simp
    rw [heq]
    exact (measurableSet_cube hn k).preimage
      T.toHomeomorph.symm.continuous.measurable
  have happ := Measure.map_apply
    (μ := (volume : Measure (Torus d))) hme himg
  rw [T.measurePreserving.map_eq] at happ
  have hpre : T.toHomeomorph ⁻¹' (T.toHomeomorph '' (cube n k : Set (Torus d))) =
        cube n k := by
    exact (Equiv.preimage_image T.toHomeomorph.toEquiv (cube n k))
  rw [hpre] at happ
  exact happ

lemma disjoint_cube {d n : ℕ} (hn : 0 < n)
    {k l : Fin d → Fin n} (hkl : k ≠ l) :
    Disjoint (cube n k : Set (Torus d)) (cube n l) := by
  rw [Set.disjoint_left]
  intro x hk hl
  exact hkl (mem_cube_unique hn x hk hl)

lemma disjoint_image_cube {d n : ℕ} (hn : 0 < n)
    (T : ToralDynamicalSystem d)
    {k l : Fin d → Fin n} (hkl : k ≠ l) :
    Disjoint (T.toHomeomorph '' (cube n k) : Set (Torus d))
      (T.toHomeomorph '' (cube n l)) := by
  rw [Set.disjoint_left]
  intro y hy hz
  rcases hy with ⟨x, hx, rfl⟩
  rcases hz with ⟨z, hz, heq⟩
  have he : x = z := T.toHomeomorph.injective heq.symm
  subst z
  exact (Set.disjoint_left.1 (disjoint_cube hn hkl)) hx hz

/-- Mass of a finite union of cubes.  Keeping the answer as a finite sum is
usually friendlier than a division by `n^d`. -/
lemma measure_union_cubes_finset {d n : ℕ} (hn : 0 < n)
    (s : Finset (Fin d → Fin n)) :
    (volume : Measure (Torus d)) (⋃ k ∈ s, (cube n k : Set (Torus d))) =
      ∑ k ∈ s, (volume : Measure (Torus d)) (cube n k) := by
  classical
  have hp : (s : Set (Fin d → Fin n)).PairwiseDisjoint
      (fun k => (cube n k : Set (Torus d))) := by
    intro k hk l hl hkl
    exact disjoint_cube hn hkl
  simpa using
    (measure_biUnion_finset (μ := (volume : Measure (Torus d)))
      (s := s) (f := fun k => (cube n k : Set (Torus d))) hp
      (fun k _ => measurableSet_cube hn k))

lemma measure_union_image_cubes_finset {d n : ℕ} (hn : 0 < n)
    (T : ToralDynamicalSystem d) (s : Finset (Fin d → Fin n)) :
    (volume : Measure (Torus d))
        (⋃ k ∈ s, (T.toHomeomorph '' (cube n k) : Set (Torus d))) =
      ∑ k ∈ s, (volume : Measure (Torus d)) (cube n k) := by
  classical
  have himg (k : Fin d → Fin n) :
      MeasurableSet (T.toHomeomorph '' (cube n k : Set (Torus d))) := by
    have heq : T.toHomeomorph '' (cube n k : Set (Torus d)) =
        T.toHomeomorph.symm ⁻¹' (cube n k : Set (Torus d)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hy
        refine ⟨T.toHomeomorph.symm y, hy, ?_⟩
        simp
    rw [heq]
    exact (measurableSet_cube hn k).preimage
      T.toHomeomorph.symm.continuous.measurable
  have hp : (s : Set (Fin d → Fin n)).PairwiseDisjoint
      (fun k => (T.toHomeomorph '' (cube n k) : Set (Torus d))) := by
    intro k hk l hl hkl
    exact disjoint_image_cube hn T hkl
  rw [measure_biUnion_finset (μ := (volume : Measure (Torus d)))
      (s := s) (f := fun k => (T.toHomeomorph '' (cube n k) : Set (Torus d)))
      hp (fun k _ => himg k)]
  apply Finset.sum_congr rfl
  intro k hk
  exact measure_image_cube hn T k

/-- Neighbor cubes for Hall: only nonempty intersection is needed. -/
noncomputable def cubeNeighbors {d n : ℕ} (T : ToralDynamicalSystem d)
    (k : Fin d → Fin n) : Finset (Fin d → Fin n) := by
  classical
  exact Finset.univ.filter (fun l =>
    ∃ x : Torus d, x ∈ cube n k ∧ T.toHomeomorph x ∈ cube n l)

@[simp] lemma mem_cubeNeighbors {d n : ℕ} (T : ToralDynamicalSystem d)
    (k l : Fin d → Fin n) :
    l ∈ cubeNeighbors T k ↔
      ∃ x : Torus d, x ∈ cube n k ∧ T.toHomeomorph x ∈ cube n l := by
  classical
  simp [cubeNeighbors]

lemma image_union_subset_neighbors {d n : ℕ} (hn : 0 < n)
    (T : ToralDynamicalSystem d)
    (s : Finset (Fin d → Fin n)) :
    (⋃ k ∈ s, (T.toHomeomorph '' (cube n k) : Set (Torus d))) ⊆
      (⋃ l ∈ s.biUnion (cubeNeighbors T), (cube n l : Set (Torus d))) := by
  classical
  intro y hy
  simp only [Set.mem_iUnion] at hy ⊢
  rcases hy with ⟨k, hk⟩
  rcases hk with ⟨hks, hyim⟩
  rcases hyim with ⟨x, hx, rfl⟩
  obtain ⟨l, hl⟩ := exists_mem_cube n hn (T.toHomeomorph x)
  refine ⟨l, ?_, hl⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨k, hks, (mem_cubeNeighbors T k l).2 ⟨x, hx, hl⟩⟩

lemma sum_measure_cube_card {d n : ℕ} (hn : 0 < n)
    (k0 : Fin d → Fin n) (s : Finset (Fin d → Fin n)) :
    (∑ k ∈ s, (volume : Measure (Torus d)) (cube n k)) =
      (s.card : ℝ≥0∞) * (volume : Measure (Torus d)) (cube n k0) := by
  classical
  calc
    (∑ k ∈ s, (volume : Measure (Torus d)) (cube n k)) =
        ∑ _k ∈ s, (volume : Measure (Torus d)) (cube n k0) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact measure_cube_eq hn i k0
    _ = _ := by simp [nsmul_eq_mul]

/-- The measure pigeon-hole argument underlying Hall's condition.  Notice
that neighbors are defined by mere nonempty intersection, hence no boundary-
zero facts are necessary. -/
lemma card_le_biUnion_cubeNeighbors {d n : ℕ} (hn : 0 < n)
    (T : ToralDynamicalSystem d)
    (s : Finset (Fin d → Fin n)) :
    s.card ≤ (s.biUnion (cubeNeighbors T)).card := by
  classical
  let k0 : Fin d → Fin n := fun _ => ⟨0, hn⟩
  let w : ℝ≥0∞ := (volume : Measure (Torus d)) (cube n k0)
  have hw0 : w ≠ 0 := measure_cube_ne_zero hn k0
  have hwtop : w ≠ ∞ :=
    measure_ne_top (volume : Measure (Torus d)) (cube n k0)
  have hμ :
      (volume : Measure (Torus d))
          (⋃ k ∈ s, (T.toHomeomorph '' (cube n k) : Set (Torus d))) ≤
        (volume : Measure (Torus d))
          (⋃ l ∈ s.biUnion (cubeNeighbors T),
            (cube n l : Set (Torus d))) :=
    measure_mono (image_union_subset_neighbors hn T s)
  rw [measure_union_image_cubes_finset hn T s,
      measure_union_cubes_finset hn (s.biUnion (cubeNeighbors T)),
      sum_measure_cube_card hn k0 s,
      sum_measure_cube_card hn k0 (s.biUnion (cubeNeighbors T))] at hμ
  change (s.card : ℝ≥0∞) * w ≤
      ((s.biUnion (cubeNeighbors T)).card : ℝ≥0∞) * w at hμ
  by_contra hnot
  have hltNat : (s.biUnion (cubeNeighbors T)).card < s.card :=
    Nat.lt_of_not_ge hnot
  have hlt :
      ((s.biUnion (cubeNeighbors T)).card : ℝ≥0∞) <
        (s.card : ℝ≥0∞) := by exact_mod_cast hltNat
  have hmul :
      ((s.biUnion (cubeNeighbors T)).card : ℝ≥0∞) * w <
        (s.card : ℝ≥0∞) * w :=
    ENNReal.mul_lt_mul_left hw0 hwtop hlt
  exact (not_lt_of_ge hμ) hmul

/-- Hall's permutation: a (not yet cyclic) permutation of the cubes such that
for each source cube some point of its image lies in its allotted target.
This is the genuinely useful finite output of the measure argument. -/
lemma exists_matchingPerm {d n : ℕ} (hn : 0 < n)
    (T : ToralDynamicalSystem d) :
    ∃ σ : Equiv.Perm (Fin d → Fin n),
      ∀ k : Fin d → Fin n,
        ∃ x : Torus d, x ∈ cube n k ∧ T.toHomeomorph x ∈ cube n (σ k) := by
  classical
  have hhall :
      ∀ s : Finset (Fin d → Fin n),
        s.card ≤ (s.biUnion (cubeNeighbors T)).card :=
    card_le_biUnion_cubeNeighbors hn T
  rcases (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (cubeNeighbors T)).1 hhall with ⟨f, hf, hfmem⟩
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, rfl⟩
  let σ : Equiv.Perm (Fin d → Fin n) := Equiv.ofBijective f hbij
  refine ⟨σ, ?_⟩
  intro k
  have hk := hfmem k
  have hk' :
      ∃ x : Torus d, x ∈ cube n k ∧ T.toHomeomorph x ∈ cube n (f k) :=
    (mem_cubeNeighbors T k (f k)).1 hk
  simpa [σ] using hk'

lemma dist_addCircle_coe_le_abs (a b : ℝ) :
    dist ( (a:AddCircle (1:ℝ))) ( (b:AddCircle (1:ℝ))) ≤ |a-b| := by
  rw [dist_eq_norm]
  change ‖(QuotientAddGroup.mk' _ a - QuotientAddGroup.mk' _ b)‖ ≤ _
  rw [← map_sub]
  exact QuotientAddGroup.norm_mk_le_norm

/-- Diameter bound with the product metric (the product in Mathlib is the
sup metric). -/
lemma edist_cube_le {d n : ℕ} (hn : 0 < n)
    {k : Fin d → Fin n} {x y : Torus d}
    (hx : x ∈ cube n k) (hy : y ∈ cube n k) :
    edist x y ≤ ENNReal.ofReal (1 / (n:ℝ)) := by
  classical
  apply edist_pi_le_iff.2
  intro i
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rcases hx i with ⟨a, ha0, ha1, hxa⟩
  rcases hy i with ⟨b, hb0, hb1, hyb⟩
  have he : (((k i : ℝ)+1)/(n:ℝ)) - ((k i : ℝ)/(n:ℝ)) =
      1/(n:ℝ) := by ring
  have hab : |a-b| ≤ (1/(n:ℝ)) := by
    rw [abs_le]
    constructor <;> linarith
  apply (edist_le_ofReal (by positivity : (0:ℝ) ≤ 1/(n:ℝ))).2
  rw [hxa, hyb]
  exact le_trans (dist_addCircle_coe_le_abs a b) hab

lemma dist_cube_le {d n : ℕ} (hn : 0 < n)
    {k : Fin d → Fin n} {x y : Torus d}
    (hx : x ∈ cube n k) (hy : y ∈ cube n k) :
    dist x y ≤ 1 / (n:ℝ) := by
  exact (edist_le_ofReal (by positivity : (0:ℝ) ≤ 1/(n:ℝ))).1
    (edist_cube_le hn hx hy)

/-- A non-cyclic Hall permutation already approximates the homeomorphism on
one grid.  This is often called the finite Lax lemma. -/
lemma exists_matching_small {d : ℕ} (T : ToralDynamicalSystem d)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hu : ∀ ⦃x y : Torus d⦄, dist x y < δ ->
      dist (T.toHomeomorph x) (T.toHomeomorph y) < η)
    {n : ℕ} (hn : 0 < n)
    (hnδ : 1 / (n:ℝ) < δ) :
    ∃ σ : Equiv.Perm (Fin d → Fin n),
      ∀ x : Torus d,
        dist (T.toHomeomorph x) (gridFun n hn σ x) ≤
          η + 1/(n:ℝ) := by
  classical
  rcases exists_matchingPerm hn T with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro x
  let k : Fin d → Fin n := cubeIndex n hn x
  have hx : x ∈ cube n k := mem_cubeIndex n hn x
  rcases hσ k with ⟨z, hz, hzT⟩
  have hclose : dist (T.toHomeomorph x) (T.toHomeomorph z) < η := by
    apply hu
    exact lt_of_le_of_lt (dist_cube_le hn hx hz) hnδ
  have hgrid : gridFun n hn σ x ∈ cube n (σ k) :=
    gridFun_mem_cube hn σ hx
  have htarget : dist (T.toHomeomorph z) (gridFun n hn σ x) ≤
      1/(n:ℝ) :=
    dist_cube_le hn hzT hgrid
  exact le_trans (dist_triangle _ (T.toHomeomorph z) _)
    (by linarith)

lemma dist_target_gridFun {d n : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (Fin d → Fin n)) (x y : Torus d)
    (hy : y ∈ cube n (σ (cubeIndex n hn x))) :
    dist y (gridFun n hn σ x) ≤ 1/(n:ℝ) := by
  have hx : x ∈ cube n (cubeIndex n hn x) := mem_cubeIndex n hn x
  exact dist_cube_le hn hy (gridFun_mem_cube hn σ hx)


/-- Coarse label of a refined grid.  `q` is the number of pieces in each
axis of a coarse cube. -/
def downIndex {d m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (k : Fin d → Fin (m*q)) : Fin d → Fin m := fun i =>
  ⟨((k i : ℕ) / q), by
    exact Nat.div_lt_of_lt_mul
      (by simpa [Nat.mul_comm] using (k i).isLt)⟩

lemma cube_subset_downIndex {d m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (k : Fin d → Fin (m*q)) :
    (cube (m*q) k : Set (Torus d)) ⊆ cube m (downIndex hm hq k) := by
  intro x hx i
  rcases hx i with ⟨a, ha0, ha1, ha⟩
  refine ⟨a, ?_, ?_, ha⟩
  · have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
    have hq' : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
    have heN := Nat.mod_add_div' (k i : ℕ) q
    have heN' : (k i : ℕ) = (k i : ℕ) / q * q + (k i : ℕ) % q := by
      omega
    have he : (((k i : ℕ) : ℝ)) =
        (((k i : ℕ) / q : ℕ) : ℝ) * (q:ℝ) +
          (((k i : ℕ) % q : ℕ) : ℝ) := by
      exact_mod_cast heN'
    have hb : (0:ℝ) ≤ (((k i : ℕ) % q : ℕ) : ℝ) := by positivity
    have hcomp :
        ((((k i : ℕ) / q : ℕ) : ℝ) / (m:ℝ)) ≤
          (((k i : ℕ) : ℝ) / ((m*q:ℕ) : ℝ)) := by
      push_cast
      rw [he]
      -- the remainder is nonnegative
      calc
        (((((k i : ℕ) / q : ℕ) : ℝ) / (m:ℝ))) =
            ((((k i : ℕ) / q : ℕ) : ℝ) * (q:ℝ)) /
              ((m:ℝ)*(q:ℝ)) := by field_simp
        _ ≤ (((((k i : ℕ) / q : ℕ) : ℝ) * (q:ℝ) +
            (((k i : ℕ) % q : ℕ) : ℝ))) /
              ((m:ℝ)*(q:ℝ)) := by
              exact (div_le_div_iff_of_pos_right (mul_pos hm' hq')).2
                (by linarith)
    exact le_trans hcomp ha0
  · have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
    have hq' : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
    have heN := Nat.mod_add_div' (k i : ℕ) q
    have heN' : (k i : ℕ) = (k i : ℕ) / q * q + (k i : ℕ) % q := by
      omega
    have he : (((k i : ℕ) : ℝ)) =
        (((k i : ℕ) / q : ℕ) : ℝ) * (q:ℝ) +
          (((k i : ℕ) % q : ℕ) : ℝ) := by
      exact_mod_cast heN'
    have hbN := Nat.mod_lt (k i : ℕ) hq
    have hb : (((k i : ℕ) % q : ℕ) : ℝ) < (q:ℝ) := by
      exact_mod_cast hbN
    have hcomp :
        ((((k i : ℕ) : ℝ) + 1) / ((m*q:ℕ) : ℝ)) ≤
          (((((k i : ℕ) / q : ℕ) : ℝ) + 1) / (m:ℝ)) := by
      push_cast
      rw [he]
      apply (div_le_div_iff₀ (mul_pos hm' hq') hm').2
      have hb' : (((k i : ℕ) % q : ℕ) : ℝ) + 1 ≤ (q:ℝ) := by
        exact_mod_cast hbN
      nlinarith
    exact lt_of_lt_of_le ha1 hcomp


/-- Mixed-radix identification of a subdivision. -/
noncomputable def splitGrid (d m q : ℕ) :
    (Fin d → Fin (m*q)) ≃
      (Fin d → Fin m) × (Fin d → Fin q) where
  toFun k := ((fun i => (finProdFinEquiv.symm (k i)).1),
              (fun i => (finProdFinEquiv.symm (k i)).2))
  invFun kl := (fun i => finProdFinEquiv (kl.1 i, kl.2 i))
  left_inv k := by
    funext i
    exact finProdFinEquiv.apply_symm_apply (k i)
  right_inv kl := by
    rcases kl with ⟨k,l⟩
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (k i, l i))
    · exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (k i, l i))

lemma splitGrid_fst {d m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (k : Fin d → Fin (m*q)) :
    (splitGrid d m q k).1 = downIndex hm hq k := by
  funext i
  have hh := finProdFinEquiv_symm_apply (x := k i)
  apply Fin.ext
  change ((finProdFinEquiv.symm (k i)).1).val = (k i).val / q
  have hb := congrArg (fun z : (Fin m × Fin q) => (z.1.val)) hh
  exact hb

/-- Lift a coarse permutation by any permutation of the sublabels.  The
projected source/target equation is definitional; this lemma avoids every
boundary convention when using refinements.  Taking a long sublabel cycle
is the usual starting point for concatenating the coarse orbits. -/
noncomputable def liftGridPerm {d m q : ℕ}
    (τ : Equiv.Perm (Fin d → Fin m)) (γ : Equiv.Perm (Fin d → Fin q)) :
    Equiv.Perm (Fin d → Fin (m*q)) :=
  (splitGrid d m q).trans
    ((Equiv.prodCongr τ γ).trans (splitGrid d m q).symm)

lemma downIndex_liftGridPerm {d m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (τ : Equiv.Perm (Fin d → Fin m)) (γ : Equiv.Perm (Fin d → Fin q))
    (k : Fin d → Fin (m*q)) :
    downIndex hm hq (liftGridPerm τ γ k) = τ (downIndex hm hq k) := by
  rw [← splitGrid_fst hm hq]
  -- inspect in product coordinates
  change ((splitGrid d m q) ((splitGrid d m q).symm
      ( (τ ((splitGrid d m q k).1)),
        (γ ((splitGrid d m q k).2))))).1 = _
  simp
  exact splitGrid_fst hm hq k

/-- Before the final orbit concatenations, every lifted permutation stays in
exactly the intended coarse target cube. In particular its point maps are
uniformly `1/m` close. -/
lemma dist_gridFun_lift_le {d m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (τ : Equiv.Perm (Fin d → Fin m)) (γ : Equiv.Perm (Fin d → Fin q))
    (x : Torus d) :
    dist (gridFun m hm τ x)
      (gridFun (m*q) (Nat.mul_pos hm hq) (liftGridPerm τ γ) x) ≤
        1/(m:ℝ) := by
  let hn : 0 < m*q := Nat.mul_pos hm hq
  let j : Fin d → Fin (m*q) := cubeIndex (m*q) hn x
  have hxj : x ∈ cube (m*q) j := mem_cubeIndex (m*q) hn x
  have hxc : x ∈ cube m (downIndex hm hq j) :=
    cube_subset_downIndex hm hq j hxj
  have hdown : downIndex hm hq j = cubeIndex m hm x :=
    (cubeIndex_eq_of_mem m hm hxc).symm
  have hyf0 : gridFun (m*q) hn (liftGridPerm τ γ) x ∈
        cube (m*q) (liftGridPerm τ γ j) := by
    simpa [j] using
      (gridFun_mem_cube hn (liftGridPerm τ γ)
        (mem_cubeIndex (m*q) hn x))
  have hyf : gridFun (m*q) hn (liftGridPerm τ γ) x ∈
        cube m (τ (cubeIndex m hm x)) := by
    have := cube_subset_downIndex hm hq (liftGridPerm τ γ j) hyf0
    simpa [downIndex_liftGridPerm hm hq τ γ j, hdown] using this
  have hyc : gridFun m hm τ x ∈ cube m (τ (cubeIndex m hm x)) :=
    gridFun_mem_cube hm τ (mem_cubeIndex m hm x)
  exact dist_cube_le hm hyc hyf

/-- Two cubes meeting across one face of the non-wrapping fine grid
have diameter at most twice the mesh.  This elementary estimate is useful
when splicing permutation orbits. -/
lemma dist_gridStep_le {d n : ℕ} (hn : 0 < n)
    {a b : Fin d → Fin n}
    (hab : LeanEval.LaxSupport.GridStep a b)
    {y z : Torus d} (hy : y ∈ cube n a) (hz : z ∈ cube n b) :
    dist y z ≤ 2 / (n:ℝ) := by
  classical
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rcases hab with ⟨j, hj, hrest⟩
  apply (dist_pi_le_iff (by positivity : (0:ℝ) ≤ 2/(n:ℝ))).2
  intro i
  rcases hy i with ⟨u, hu0, hu1, huy⟩
  rcases hz i with ⟨v, hv0, hv1, hvz⟩
  rw [huy, hvz]
  refine le_trans (dist_addCircle_coe_le_abs u v) ?_
  by_cases hi : i = j
  · subst i
    have hgap : |u-v| ≤ 2/(n:ℝ) := by
      rcases hj with hj | hj
      · have e : ((b j : ℝ)) = (a j : ℝ) + 1 := by
          exact_mod_cast hj.symm
        rw [e] at hv0 hv1
        have ea : (((a j : ℝ)+1)/(n:ℝ)) = (a j : ℝ)/(n:ℝ) + 1/(n:ℝ) := by ring
        have ea2 : (((a j : ℝ)+1+1)/(n:ℝ)) =
              (a j : ℝ)/(n:ℝ) + 2/(n:ℝ) := by ring
        rw [ea] at hu1 hv0
        rw [ea2] at hv1
        rw [abs_le]
        constructor <;> linarith
      · have e : ((a j : ℝ)) = (b j : ℝ) + 1 := by
          exact_mod_cast hj.symm
        rw [e] at hu0 hu1
        have eb : (((b j : ℝ)+1)/(n:ℝ)) = (b j : ℝ)/(n:ℝ) + 1/(n:ℝ) := by ring
        have eb2 : (((b j : ℝ)+1+1)/(n:ℝ)) =
              (b j : ℝ)/(n:ℝ) + 2/(n:ℝ) := by ring
        rw [eb] at hv1 hu0
        rw [eb2] at hu1
        rw [abs_le]
        constructor <;> linarith
    exact hgap
  · have hsame : a i = b i := hrest i hi
    rw [hsame] at hu0 hu1
    have eb : (((b i : ℝ)+1)/(n:ℝ)) = (b i : ℝ)/(n:ℝ) + 1/(n:ℝ) := by ring
    rw [eb] at hu1 hv1
    have hdiff : |u-v| ≤ 1/(n:ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    calc |u-v| ≤ 1/(n:ℝ) := hdiff
         _ ≤ 2/(n:ℝ) := by apply (div_le_div_iff_of_pos_right hn').2; norm_num

lemma dist_gridFun_swap_le {d n : ℕ} (hn : 0 < n)
    (f : Equiv.Perm (Fin d → Fin n)) {a b : Fin d → Fin n}
    (hab : LeanEval.LaxSupport.GridStep a b) (x : Torus d) :
    dist (gridFun n hn f x)
      (gridFun n hn ((Equiv.swap a b) * f) x) ≤ 2/(n:ℝ) := by
  classical
  let k : Fin d → Fin n := cubeIndex n hn x
  have h0 : gridFun n hn f x ∈ cube n (f k) :=
    gridFun_mem_cube hn f (mem_cubeIndex n hn x)
  have h1 : gridFun n hn ((Equiv.swap a b) * f) x ∈
      cube n (((Equiv.swap a b) * f) k) :=
    gridFun_mem_cube hn _ (mem_cubeIndex n hn x)
  by_cases ha : f k = a
  · have he : (((Equiv.swap a b) * f) k) = b := by
      rw [Equiv.Perm.mul_apply, ha]; exact Equiv.swap_apply_left _ _
    simpa [ha, he] using
      (dist_gridStep_le hn hab (by simpa [ha] using h0)
        (by simpa [he] using h1))
  by_cases hb : f k = b
  · have he : (((Equiv.swap a b) * f) k) = a := by
      rw [Equiv.Perm.mul_apply, hb]; exact Equiv.swap_apply_right _ _
    simpa [hb, he] using
      (dist_gridStep_le hn hab.symm (by simpa [hb] using h0)
        (by simpa [he] using h1))
  have he : (((Equiv.swap a b) * f) k) = f k := by
    rw [Equiv.Perm.mul_apply]
    exact Equiv.swap_apply_of_ne_of_ne ha hb
  -- outside the two fibres both permutations give the same cube;
  -- its diameter is only one fine mesh
  have hs := dist_cube_le hn h0 (by simpa [he] using h1)
  exact le_trans hs (by
    apply (div_le_div_iff_of_pos_right (by exact_mod_cast hn : (0:ℝ) < n)).2
    norm_num)


/-- Uniform estimate for a list of output-splices. Only the combinatorics of
finding a short list which joins all orbits remains; the analytic price of a
list is exactly two fine meshes for each edge. -/
lemma dist_fold_gridStep_le {d n : ℕ} (hn : 0 < n)
    (l : List ((Fin d → Fin n) × (Fin d → Fin n)))
    (hl : ∀ p ∈ l, LeanEval.LaxSupport.GridStep p.1 p.2)
    (f : Equiv.Perm (Fin d → Fin n)) (x : Torus d) :
    dist (gridFun n hn f x)
      (gridFun n hn
        (l.foldl (fun g p => (Equiv.swap p.1 p.2) * g) f) x) ≤
      (l.length : ℝ) * (2/(n:ℝ)) := by
  classical
  induction l generalizing f with
  | nil => simp
  | cons p l ih =>
    have hp : LeanEval.LaxSupport.GridStep p.1 p.2 := hl p (by simp)
    have htail : ∀ t ∈ l, LeanEval.LaxSupport.GridStep t.1 t.2 := by
      intro t ht; exact hl t (by simp [ht])
    have hfirst := dist_gridFun_swap_le hn f hp x
    have hnext := ih htail ((Equiv.swap p.1 p.2) * f)
    simp only [List.foldl] -- expose the first splice
    have htri := dist_triangle (gridFun n hn f x)
      (gridFun n hn ((Equiv.swap p.1 p.2) * f) x)
      (gridFun n hn
        (List.foldl (fun g p => (Equiv.swap p.1 p.2) * g)
          ((Equiv.swap p.1 p.2) * f) l) x)
    calc
      _ ≤ dist (gridFun n hn f x)
            (gridFun n hn ((Equiv.swap p.1 p.2) * f) x) +
          dist (gridFun n hn ((Equiv.swap p.1 p.2) * f) x)
            (gridFun n hn (List.foldl
              (fun g p => (Equiv.swap p.1 p.2) * g)
              ((Equiv.swap p.1 p.2) * f) l) x) := htri
      _ ≤ 2/(n:ℝ) + (l.length:ℝ) * (2/(n:ℝ)) := add_le_add hfirst hnext
      _ = ((p :: l).length:ℕ) * (2/(n:ℝ)) := by
        push_cast
        simp
        ring

lemma dist_torus_le_one {d : ℕ} (x y : Torus d) : dist x y ≤ 1 := by
  have hn : 0 < (1:ℕ) := by decide
  obtain ⟨k, hx⟩ := exists_mem_cube 1 hn x
  obtain ⟨l, hy⟩ := exists_mem_cube 1 hn y
  have hkl : k = l := Subsingleton.elim _ _
  subst l
  simpa using (dist_cube_le hn hx hy)
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem lax_approximation {d : ℕ} (hd : 0 < d) (T : ToralDynamicalSystem d)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (S : VolumePreservingEquiv d),
      IsCyclicCubeExchange S n ∧ deltaDist T.toVolumePreservingEquiv S < ε :=
/-ResultProofBegin-/by
  -- Work strictly below the requested (possibly infinite) `ℝ≥0∞`
  -- tolerance.  This separates all `WithTop` issues from the geometric
  -- approximation on the torus.
  obtain ⟨r, hr, hrε⟩ := exists_pos_real_ofReal_lt hε
  -- The remaining task is the grid/cyclic matching estimate at a finite
  -- real scale.  Keeping the scale as a real number makes all subsequent
  -- cube-diameter estimates coercion-free; a non-strict bound at this scale
  -- suffices since it lies strictly below `ε`.
  -- Cubes with positive mesh form an actual measurable partition; the
  -- helper `gridVPE_isCyclic` above now reduces the theorem to choosing the
  -- combinatorial cycle (and its measure/error estimates).  In particular
  -- no issues about representatives, inverses, measurability of the
  -- piecewise map, or packaging into an equivalence remain in this step.
  obtain ⟨n, hn, σ, hcycle, hsupp, hpoint⟩ :
      ∃ (n : ℕ) (hn : 0 < n) (σ : Equiv.Perm (Fin d → Fin n)),
        σ.IsCycle ∧ σ.support = Finset.univ ∧
        (∀ x : Torus d, edist (T.toVolumePreservingEquiv.toMeasurableEquiv x)
            (gridFun n hn σ x) ≤ ENNReal.ofReal r) := by
    -- First take a coarse grid where uniform continuity controls `T` on
    -- each source cube.  All measure theory in choosing its matching has
    -- been isolated in `exists_matchingPerm`.
    have hu0 : UniformContinuous (T.toHomeomorph : Torus d → Torus d) :=
      CompactSpace.uniformContinuous_of_continuous
        T.toHomeomorph.continuous
    have heta : (0:ℝ) < r/4 := by linarith
    rcases (Metric.uniformContinuous_iff.1 hu0 (r/4) (by linarith)) with
      ⟨δ, hδ, hu⟩
    have hδr : 0 < min δ (r/8) := lt_min hδ (by linarith)
    obtain ⟨m0 : ℕ, hm0 : (1:ℝ) / ((m0:ℝ)+1) < min δ (r/8)⟩ :=
      exists_nat_one_div_lt hδr
    let m : ℕ := m0 + 1
    have hm : 0 < m := by dsimp [m]; omega
    have hmδr : (1:ℝ) / (m:ℝ) < min δ (r/8) := by
      simpa [m, Nat.cast_add, Nat.cast_one] using hm0
    have hmδ : (1:ℝ) / (m:ℝ) < δ := lt_of_lt_of_le hmδr (min_le_left _ _)
    have hmr8 : (1:ℝ) / (m:ℝ) < r/8 := lt_of_lt_of_le hmδr (min_le_right _ _)
    rcases exists_matchingPerm (d:=d) hm T with ⟨τ, hτ⟩
    -- The last combinatorial lemma is naturally stated as a refinement of
    -- one *fixed* finite permutation.  Subdivide its cubes and join its
    -- orbits using adjacent subcubes.  There is no measure theory, and no
    -- homeomorphism, in this residue: `gridFun m τ` is any finite cube
    -- permutation.  Its approximation can be made cyclic at every positive
    -- uniform tolerance on a nonzero-dimensional torus.
    -- On a subdivision, `liftGridPerm τ γ` already lands in the exact
    -- coarse target.  Thus it is `1/m` from `gridFun m τ` by
    -- `dist_gridFun_lift_le`.  The only discretion left is the purely
    -- finite orbit-joining perturbation of this lift.  It uses a long
    -- sublabel cycle `γ`; adjacent fine output labels from different orbits
    -- may be interchanged.  Crucially the number of its unjoined orbits is
    -- bounded by the *coarse* cardinal, independently of the subdivision.
    obtain ⟨q, hq, γ, ρ, hρcyc, hρsup, hρlift⟩ :
        ∃ (q : ℕ) (hq : 0 < q)
          (γ : Equiv.Perm (Fin d → Fin q))
          (ρ : Equiv.Perm (Fin d → Fin (m*q))),
          ρ.IsCycle ∧ ρ.support = Finset.univ ∧
          (∀ x : Torus d,
            dist
              (gridFun (m*q) (Nat.mul_pos hm hq) (liftGridPerm τ γ) x)
              (gridFun (m*q) (Nat.mul_pos hm hq) ρ x) < r/8) := by
      -- The continuous part of the orbit joining can be stripped off
      -- entirely. Multiplying on the left by a transposition of two
      -- neighbouring *target* labels has price at most two fine meshes
      -- (even on the two exceptional source fibres); see
      -- `dist_fold_gridStep_le`. Thus what is left is the genuinely finite
      -- Hamilton/cut-and-join assertion. Stating it with the splicing list
      -- also records the quantitative bound one needs: the list must have
      -- bounded length independently of the subdivision. Forgetting this
      -- bound (or using all q^d labels) is the tempting but invalid step in
      -- this reduction.
      obtain ⟨q, hq, γ, joins, hjedge, hjlen, hjcyc, hjsup⟩ :
          ∃ (q : ℕ) (hq : 0 < q)
            (γ : Equiv.Perm (Fin d → Fin q))
            (joins : List
              ((Fin d → Fin (m*q)) × (Fin d → Fin (m*q)))),
            (∀ p ∈ joins, LeanEval.LaxSupport.GridStep p.1 p.2) ∧
            (joins.length : ℝ) * (2 / ((m*q:ℕ):ℝ)) < r/8 ∧
            (joins.foldl (fun g p => (Equiv.swap p.1 p.2) * g)
                (liftGridPerm τ γ)).IsCycle ∧
            (joins.foldl (fun g p => (Equiv.swap p.1 p.2) * g)
                (liftGridPerm τ γ)).support = Finset.univ := by
          classical
          let M : ℕ := Fintype.card (Fin d → Fin m)
          have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
          -- take many more fine pieces than the (fixed) number of coarse cubes
          obtain ⟨q, hqbig⟩ := exists_nat_gt
            ((16 * (M:ℝ)) / ((m:ℝ)*r) + 2 : ℝ)
          have hnon : 0 ≤ (16 * (M:ℝ)) / ((m:ℝ)*r) := by positivity
          have hq2 : 2 < (q:ℝ) := lt_of_le_of_lt (by linarith : (2:ℝ) ≤
            (16 * (M:ℝ)) / ((m:ℝ)*r) + 2) hqbig
          have hq : 0 < q := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ)<2) hq2)
          have hq' : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
          have hbndM : (M:ℝ) * (2 / ((m*q:ℕ):ℝ)) < r/8 := by
            have hh : (16*(M:ℝ)) / ((m:ℝ)*r) < (q:ℝ) :=
              lt_trans (by linarith : (16*(M:ℝ))/((m:ℝ)*r) <
                (16*(M:ℝ))/((m:ℝ)*r)+2) hqbig
            have hh' : (16*(M:ℝ)) < (q:ℝ)*((m:ℝ)*r) :=
              (div_lt_iff₀ (mul_pos hm' hr)).1 hh
            have den : (0:ℝ) < ((m*q:ℕ):ℝ) := by exact_mod_cast (Nat.mul_pos hm hq)
            rw [← mul_div_assoc]
            apply (div_lt_iff₀ den).2
            push_cast
            nlinarith
          have hcard : 2 ≤ Fintype.card (Fin d → Fin q) := by
            classical
            rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
            have h2n : 2 ≤ q := by exact_mod_cast (le_of_lt hq2)
            exact le_trans h2n (Nat.le_pow hd)
          obtain ⟨γ, hγcy, hγsup⟩ :=
            LeanEval.LaxSupport.exists_full_cycle (Fin d → Fin q) hcard
          have hγmov : ∀ b : (Fin d → Fin q), γ b ≠ b := by
            intro b
            exact Equiv.Perm.mem_support.mp (by rw [hγsup]; simp)
          letI : Nonempty (Fin d → Fin q) :=
            ⟨fun _ => (⟨0, hq⟩ : Fin q)⟩
          letI : Nonempty (Fin d → Fin (m*q)) :=
            ⟨fun _ => (⟨0, Nat.mul_pos hm hq⟩ : Fin (m*q))⟩
          have hmov : ∀ z, (liftGridPerm τ γ) z ≠ z := by
            exact LeanEval.LaxSupport.moved_pull_prod
              (splitGrid d m q) τ γ hγmov
          have hcnt : LeanEval.LaxSupport.orbitCount (liftGridPerm τ γ) ≤ M := by
            exact LeanEval.LaxSupport.orbitCount_pull_prod_le
              (splitGrid d m q) τ γ hγcy hγmov
          obtain ⟨joins, hedge, hlenNat, hcy, hsup⟩ :=
            LeanEval.LaxSupport.exists_joins_to_cycle
              (d:=d) (N:=m*q) (Nat.mul_pos hm hq)
              (liftGridPerm τ γ) hmov
          have hlenR : (joins.length:ℝ) * (2 / ((m*q:ℕ):ℝ)) < r/8 := by
            have hlenNR : (joins.length:ℝ) ≤ (M:ℝ) := by
              exact_mod_cast (le_trans (Nat.le_of_lt hlenNat) hcnt)
            have hnoncoef : 0 ≤ (2 / ((m*q:ℕ):ℝ)) := by positivity
            exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hlenNR hnoncoef) hbndM
          exact ⟨q, hq, γ, joins, hedge, hlenR, hcy, hsup⟩
      let ρ : Equiv.Perm (Fin d → Fin (m*q)) :=
        joins.foldl (fun g p => (Equiv.swap p.1 p.2) * g)
          (liftGridPerm τ γ)
      refine ⟨q, hq, γ, ρ, ?_, ?_, ?_⟩
      · exact hjcyc
      · exact hjsup
      intro x
      exact lt_of_le_of_lt
        (dist_fold_gridStep_le (Nat.mul_pos hm hq) joins hjedge
          (liftGridPerm τ γ) x) hjlen
    let N : ℕ := m*q
    have hN : 0 < N := Nat.mul_pos hm hq
    have hρapprox : ∀ x : Torus d,
          dist (gridFun m hm τ x) (gridFun N hN ρ x) < r/4 := by
      intro x
      have hL := dist_gridFun_lift_le hm hq τ γ x
      have hJ := hρlift x
      have hh := dist_triangle (gridFun m hm τ x)
        (gridFun (m*q) (Nat.mul_pos hm hq) (liftGridPerm τ γ) x)
        (gridFun N hN ρ x)
      change dist (gridFun m hm τ x) (gridFun N hN ρ x) < r/4
      change dist (gridFun m hm τ x) (gridFun (m*q)
        (Nat.mul_pos hm hq) ρ x) < r/4
      change dist (gridFun m hm τ x) (gridFun (m*q)
        (Nat.mul_pos hm hq) ρ x) ≤ _ at hh
      linarith
    refine ⟨N, hN, ρ, hρcyc, hρsup, ?_⟩
    intro x
    let K : Fin d → Fin m := cubeIndex m hm x
    have hx : x ∈ cube m K := mem_cubeIndex m hm x
    rcases hτ K with ⟨z, hz, hTz⟩
    have hxz : dist (T.toHomeomorph x) (T.toHomeomorph z) < r/4 := by
      apply hu
      exact lt_of_le_of_lt (dist_cube_le hm hx hz) hmδ
    have hcoarse : dist (T.toHomeomorph z) (gridFun m hm τ x) ≤
        1/(m:ℝ) := by
      exact dist_target_gridFun hm τ x (T.toHomeomorph z)
        (by simpa [K] using hTz)
    have hnear : dist (T.toHomeomorph z) (gridFun N hN ρ x) < r/2 := by
      have hh := dist_triangle (T.toHomeomorph z)
        (gridFun m hm τ x) (gridFun N hN ρ x)
      have ha := hρapprox x
      linarith
    apply (edist_le_ofReal (le_of_lt hr)).2
    change dist (T.toHomeomorph x) (gridFun N hN ρ x) ≤ r
    have htri := dist_triangle (T.toHomeomorph x)
      (T.toHomeomorph z) (gridFun N hN ρ x)
    linarith
  have hmp : MeasurePreserving (gridFun n hn σ)
      (volume : Measure (Torus d)) volume := measurePreserving_gridFun hn σ

  let S : VolumePreservingEquiv d := gridVPE hn σ hmp
  have hS : IsCyclicCubeExchange S n := by
    exact gridVPE_isCyclic hn σ hmp hcycle hsupp
  have hpoint' : ∀ x : Torus d,
      edist (T.toVolumePreservingEquiv.toMeasurableEquiv x)
        (S.toMeasurableEquiv x) ≤ ENNReal.ofReal r := by
    intro x
    exact hpoint x
  have hdist : deltaDist T.toVolumePreservingEquiv S ≤ ENNReal.ofReal r :=
    deltaDist_le_of_forall _ _ hpoint'
  exact ⟨n, S, hS, lt_of_le_of_lt hdist hrε⟩
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
