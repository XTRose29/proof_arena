import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/CompactApprox.lean
section

open Set Topology

namespace BrouwerSupport

/-- A standard compactness reduction in analytic proofs of the finite dimensional
fixed point theorem.  No Brouwer argument is involved here: on a compact set
arbitrarily good approximate fixed points of a continuous map have an exact
one.  We use a minimum of `‖g x-x‖`, avoiding sequential compactness choices. -/
lemma fixed_of_approx
    {F : Type*} [NormedAddCommGroup F]
    {C : Set F} (hC : IsCompact C) (hne : C.Nonempty)
    (g : F → F) (hg : ContinuousOn g C)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ x ∈ C, ‖g x - x‖ < ε) :
    ∃ x ∈ C, g x = x := by
  have hnorm : ContinuousOn (fun x : F => ‖g x - x‖) C :=
    (hg.sub continuousOn_id).norm
  obtain ⟨p, hpC, hp⟩ := hC.exists_isMinOn hne hnorm
  have hzero : ‖g p - p‖ = 0 := by
    have hn : 0 ≤ ‖g p - p‖ := norm_nonneg _
    by_contra hz
    have hpos : 0 < ‖g p - p‖ := lt_of_le_of_ne hn (Ne.symm hz)
    obtain ⟨x, hxC, hx⟩ := ha _ hpos
    have hle : ‖g p - p‖ ≤ ‖g x - x‖ := hp hxC
    linarith
  exact ⟨p, hpC, sub_eq_zero.mp (norm_eq_zero.mp hzero)⟩

end BrouwerSupport

end
-- END INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/CompactApprox.lean

-- BEGIN INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/GridCochain.lean
section

open Finset

/-!
A little piece of the combinatorics behind the cubical proof, in characteristic two.
It is pleasant to use cubical (rather than simplicial) cochains here.  A path
through a cube is an ordering of its free coordinates.  The product of the
increments of vertex-functions, summed over all the paths, is the cup product
`db₁ ... dbᵣ` on that cube.
-/
namespace BrouwerSupport.Grid

-- We use `ZMod 2`: consequently orientations can simply be forgotten.
abbrev F2 := ZMod 2

variable {A : Type*} [DecidableEq A]

/-- `paths b s t` is the value of `db₁⋯dbᵣ` on the face with lower
corner `s` and free coordinates `t`.  This recursive definition sums over
orders of the free coordinates.  It also has the useful convention that it is
zero in the wrong dimension. -/
def paths : List (Finset A → F2) → Finset A → Finset A → F2
  | [], _, t => if t = ∅ then 1 else 0
  | b :: l, s, t => ∑ a ∈ t, (b (insert a s) + b s) * paths l (insert a s) (t.erase a)

@[simp] lemma paths_nil (s t : Finset A) :
    paths ([] : List (Finset A → F2)) s t = if t = ∅ then 1 else 0 := rfl
@[simp] lemma paths_cons (b : Finset A → F2) (l) (s t : Finset A) :
    paths (b::l) s t = ∑ a ∈ t, (b (insert a s) + b s) * paths l (insert a s) (t.erase a) := rfl
@[simp] lemma paths_nil_empty (s : Finset A) : paths ([] : List (Finset A → F2)) s ∅ = 1 := by
  simp [paths]

-- characteristic two facts, in a form convenient for `ring`-style rearranging
@[simp] lemma two_mul_F2 (x : F2) : x + x = 0 := by
  have h : (2 : F2) = 0 := by decide
  simpa [two_mul] using congrArg (fun z : F2 => z * x) h
@[simp] lemma neg_F2 (x : F2) : -x = x := by
  -- `x+x=0`
  apply (neg_eq_iff_add_eq_zero).2
  exact two_mul_F2 x
lemma add_eq_zero_eq_F2 {x y : F2} : x + y = 0 ↔ x = y := by
  rw [add_eq_zero_iff_eq_neg]
  simp

/-- Cubical coboundary. On an un-oriented cube its boundary is the sum of its
lower and upper faces in each free coordinate (we are in characteristic two). -/
def boundary (u : Finset A → Finset A → F2) (s t : Finset A) : F2 :=
  ∑ a ∈ t, (u (insert a s) (t.erase a) + u s (t.erase a))

@[simp] lemma boundary_empty (u : Finset A → Finset A → F2) (s : Finset A) :
    boundary u s ∅ = 0 := by simp [boundary]


private lemma __GridCochain_erase_erase' (t : Finset A) (a b : A) :
    (t.erase a).erase b = (t.erase b).erase a := by
  ext x
  by_cases hx : x = a
  · subst x; simp
  · by_cases hy : x = b
    · subst x; simp
    · simp [hx, hy]

/-- The sum of a symmetric function over ordered unequal pairs is zero in
characteristic two. -/
lemma sum_pairs_symm_zero (t : Finset A) (h : A → A → F2)
    (hh : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → h a b = h b a) :
    (∑ a ∈ t, ∑ b ∈ t.erase a, h a b) = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert c u hcu ih =>
    have ih' : (∑ a ∈ u, ∑ b ∈ u.erase a, h a b) = 0 :=
      ih (by
        intro a ha b hb hab
        exact hh a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab)
    -- split off the pairs involving `c`
    rw [Finset.sum_insert hcu]
    simp [Finset.erase_insert hcu]
    -- `simp` expanded the outer `sum`; do the other erases one by one.
    have hrest : (∑ a ∈ u, ∑ b ∈ (insert c u).erase a, h a b) =
        (∑ a ∈ u, (h a c + ∑ b ∈ u.erase a, h a b)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hac : c ≠ a := by
        intro e
        subst a
        exact hcu ha
      rw [Finset.erase_insert_of_ne hac]
      rw [Finset.sum_insert]
      exact not_mem_subset (Finset.erase_subset _ _) hcu
    rw [hrest]
    rw [Finset.sum_add_distrib]
    -- the two copies with `c` cancel, and so do all old pairs
    have hp : (∑ a ∈ u, h a c) = (∑ a ∈ u, h c a) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply hh a (Finset.mem_insert_of_mem ha) c (Finset.mem_insert_self _ _)
      intro e
      subst a
      exact hcu ha
    rw [hp, ih']
    simp

lemma boundary_boundary (u : Finset A → Finset A → F2) (s t : Finset A) :
    boundary (fun s t => boundary u s t) s t = 0 := by
  classical
  let h : A → A → F2 := fun a b =>
    u (insert b (insert a s)) ((t.erase a).erase b) +
    u (insert a s) ((t.erase a).erase b) +
    u (insert b s) ((t.erase a).erase b) +
    u s ((t.erase a).erase b)
  have heq : boundary (fun s t => boundary u s t) s t =
        ∑ a ∈ t, ∑ b ∈ t.erase a, h a b := by
    unfold boundary
    dsimp [h]
    -- just distribute the finite sums
    simp_rw [Finset.sum_add_distrib]
    -- associativity/commutativity of addition
    ac_rfl
  rw [heq]
  apply sum_pairs_symm_zero t h
  intro a ha b hb hab
  dsimp [h]
  have her : (t.erase a).erase b = (t.erase b).erase a := __GridCochain_erase_erase' t a b
  rw [her]
  -- the second and third entries are interchanged
  rw [insert_comm b a]
  ac_rfl

-- The elementary cup calculation and the cocycle calculation are mutually
-- inductive.  We phrase them together below.

private lemma __GridCochain_paths_cup_of_zero (b : Finset A → F2)
    (l : List (Finset A → F2)) (s t : Finset A)
    (hz : boundary (fun s t => paths l s t) s t = 0) :
    paths (b::l) s t = boundary (fun s t => b s * paths l s t) s t := by
  classical
  let up : A → F2 := fun a => paths l (insert a s) (t.erase a)
  let dn : A → F2 := fun a => paths l s (t.erase a)
  have hsum : (∑ a ∈ t, up a) = (∑ a ∈ t, dn a) := by
    have z : (∑ a ∈ t, up a) + (∑ a ∈ t, dn a) = 0 := by
      simpa [boundary, up, dn, Finset.sum_add_distrib] using hz
    exact add_eq_zero_eq_F2.mp z
  -- pull the terms not depending on the summation variable out of the sum
  change (∑ a ∈ t, (b (insert a s) + b s) * up a) =
    ∑ a ∈ t, (b (insert a s) * up a + b s * dn a)
  simp_rw [add_mul]
  simp_rw [Finset.sum_add_distrib]
  -- extract the common constant factor
  have hf (w : A → F2) : (∑ a ∈ t, b s * w a) = b s * ∑ a ∈ t, w a := by
    exact (Finset.mul_sum _ _ _).symm
  rw [hf up, hf dn, hsum]

/-- Products of coboundaries are cubical cocycles. -/
lemma paths_cocycle : ∀ l : List (Finset A → F2), ∀ s t : Finset A,
    t.card = l.length + 1 →
    boundary (fun s t => paths l s t) s t = 0 := by
  intro l
  induction l with
  | nil =>
      intro s t ht
      have ht1 : t.card = 1 := by simpa using ht
      classical
      -- on a singleton face both vertices have value one
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp ht1
      simp [boundary, paths]
  | cons b l ih =>
      intro s t ht
      classical
      -- on every face the preceding cup calculation applies (the induction
      -- hypothesis says that the tail is a cocycle there)
      have hface (s' : Finset A) (a : A) (ha : a ∈ t) :
          paths (b::l) s' (t.erase a) =
            boundary (fun s u => b s * paths l s u) s' (t.erase a) := by
        apply __GridCochain_paths_cup_of_zero
        apply ih
        have hc : (t.erase a).card = t.card - 1 := Finset.card_erase_of_mem ha
        -- `card` of the face is the right one
        have ht' : t.card = l.length + 2 := by simpa using ht
        omega
      -- rewrite the two occurrences on each face using `hface`; this is d²
      change (∑ a ∈ t, (paths (b::l) (insert a s) (t.erase a) +
                           paths (b::l) s (t.erase a))) = 0
      have he : (∑ a ∈ t, (paths (b::l) (insert a s) (t.erase a) +
                           paths (b::l) s (t.erase a))) =
                   ∑ a ∈ t, (boundary (fun s u => b s * paths l s u)
                                (insert a s) (t.erase a) +
                               boundary (fun s u => b s * paths l s u)
                                s (t.erase a)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hface (insert a s) a ha, hface s a ha]
      rw [he]
      exact boundary_boundary (A:=A) (fun s u => b s * paths l s u) s t

/-- The little Stokes formula useful in practice: `db₁⋯dbᵣ` is the
coboundary of `b₁ db₂⋯dbᵣ` in the correct dimension. -/
lemma paths_eq_boundary (b : Finset A → F2)
    (l : List (Finset A → F2)) (s t : Finset A)
    (ht : t.card = l.length + 1) :
    paths (b::l) s t = boundary (fun s t => b s * paths l s t) s t := by
  apply __GridCochain_paths_cup_of_zero
  exact paths_cocycle l s t ht

/-- If one of the vertex functions is constant along all the remaining
coordinate directions, its differential is zero, and so is the product of
paths.  The slightly stronger hypothesis with arbitrary `s` is often handy
for faces of a big grid. -/
lemma paths_eq_zero_of_mem_flat
    (l : List (Finset A → F2)) (b : Finset A → F2)
    (hb : b ∈ l) (t : Finset A)
    (flat : ∀ (s : Finset A) a, a ∈ t → b (insert a s) = b s) :
    ∀ s : Finset A, paths l s t = 0 := by
  classical
  -- a version allowing a subset of the original set is what the recursion uses
  suffices H : ∀ (l : List (Finset A → F2)) (u : Finset A), u ⊆ t → b ∈ l →
      ∀ s, paths l s u = 0 by
    exact H l t (by intro a; exact id) hb
  intro l'
  induction l' with
  | nil => intro u hu h; simp at h
  | cons c q ih =>
    intro u hu hmem s
    rcases (List.mem_cons.mp hmem) with e | e
    · subst c
      dsimp [paths]
      apply Finset.sum_eq_zero
      intro a ha
      have z : b (insert a s) + b s = 0 := by
        rw [flat s a (hu ha)]
        exact two_mul_F2 _
      rw [z]
      simp
    · dsimp [paths]
      apply Finset.sum_eq_zero
      intro a ha
      have sub : u.erase a ⊆ t := Finset.Subset.trans (Finset.erase_subset _ _) hu
      have hrec : paths q (insert a s) (u.erase a) = 0 := ih (u.erase a) sub e (insert a s)
      simp [hrec]

end BrouwerSupport.Grid

end
-- END INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/GridCochain.lean

-- BEGIN INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/GridGeometry.lean
section

open Set
namespace BrouwerSupport

/-- vertices of the regular subdivision of `[-1,1]^d` into `n` pieces
in each direction.  The harmless `n=0` value is not used. -/
noncomputable def gridPoint {d : ℕ} (n : ℕ) (a : Fin d → Fin (n+1)) :
    EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm
    (fun i => -1 + 2 * (a i : ℕ) / (n:ℝ))

@[simp] lemma gridPoint_apply {d n} (a : Fin d → Fin (n+1)) (i : Fin d) :
    gridPoint n a i = -1 + 2 * (a i : ℕ) / (n:ℝ) := by
  simp [gridPoint]

lemma gridPoint_mem_cube' {d n} (hn : 0 < n) (a : Fin d → Fin (n+1)) :
    ∀ i : Fin d, |gridPoint n a i| ≤ (1:ℝ) := by
  intro i
  rw [gridPoint_apply]
  apply (abs_le).2
  have hl : (0:ℝ) ≤ (a i : ℕ) := by exact_mod_cast (Nat.zero_le _)
  have hu_nat : (a i : ℕ) ≤ n := Nat.le_of_lt_succ (a i).isLt
  have hu : (a i : ℕ) ≤ (n:ℝ) := by exact_mod_cast hu_nat
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  constructor
  · have : 0 ≤ 2 * (a i : ℕ) / (n:ℝ) := by positivity
    linarith
  · have hbound : 2 * (a i : ℕ) / (n:ℝ) ≤ 2 := by
      apply (div_le_iff₀ hn').2
      nlinarith
    linarith

@[simp] lemma gridPoint_zero_face {d n} (hn : 0 < n)
    (a : Fin d → Fin (n+1)) (i : Fin d) (h : (a i : ℕ) = 0) :
    gridPoint n a i = (-1:ℝ) := by
  simp [gridPoint_apply, h]

@[simp] lemma gridPoint_top_face {d n} (hn : 0 < n)
    (a : Fin d → Fin (n+1)) (i : Fin d) (h : (a i : ℕ) = n) :
    gridPoint n a i = (1:ℝ) := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  norm_num [gridPoint_apply, h, hn']

/-- Two vertices whose integer coordinates differ by at most one are within
one cell diameter. The slightly spacious bound `2*(d+1)/n` avoids square
roots and is often more convenient than `sqrt d`. -/
lemma dist_gridPoint_lt {d n : ℕ} (hn : 0 < n)
    (a b : Fin d → Fin (n+1))
    (hab : ∀ i : Fin d, ((a i : ℤ) - (b i : ℤ)) ∈ Set.Icc (-1 : ℤ) 1) :
    dist (gridPoint n a) (gridPoint n b)
      < (2:ℝ) * ((d:ℝ) + 1) / n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have coord (i : Fin d) :
      |(gridPoint n a - gridPoint n b) i| ≤ (2:ℝ) / n := by
    change |gridPoint n a i - gridPoint n b i| ≤ _
    rw [gridPoint_apply, gridPoint_apply]
    have H := hab i
    have hlowz := H.1
    have hhiz := H.2
    have hz : |((a i : ℤ) - (b i : ℤ) : ℤ)| ≤ (1:ℤ) := (abs_le).2 ⟨hlowz, hhiz⟩
    have hr : |((a i : ℕ) : ℝ) - ((b i : ℕ) : ℝ)| ≤ (1:ℝ) := by
      exact_mod_cast hz
    calc
      |(-1 + 2 * (a i : ℕ) / (n:ℝ)) -
          (-1 + 2 * (b i : ℕ) / (n:ℝ))| =
          (2/(n:ℝ)) * |((a i : ℕ):ℝ) - ((b i : ℕ):ℝ)| := by
            calc
              |(-1 + 2 * (a i : ℕ) / (n:ℝ)) -
                  (-1 + 2 * (b i : ℕ) / (n:ℝ))| =
                  |(2/(n:ℝ)) * (((a i:ℕ):ℝ) - ((b i:ℕ):ℝ))| := by
                    congr 1 <;> ring
              _ = _ := by rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2/(n:ℝ))]
      _ ≤ (2/(n:ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (2:ℝ) / n := by ring
  have hs : ‖(gridPoint n a - gridPoint n b)‖^2 ≤
        (d:ℝ) * ((2:ℝ) / n)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ i : Fin d, ((gridPoint n a - gridPoint n b) i)^2) ≤
          ∑ _i : Fin d, ((2:ℝ)/n)^2 := by
            apply Finset.sum_le_sum
            intro i hi
            have := (sq_le_sq₀ (abs_nonneg _) (by positivity : (0:ℝ) ≤ 2/(n:ℝ))).2 (coord i)
            simpa [sq_abs] using this
      _ = (d:ℝ) * ((2:ℝ)/n)^2 := by simp
  rw [dist_eq_norm]
  have hnon : 0 ≤ ‖gridPoint n a - gridPoint n b‖ := norm_nonneg _
  have hd0 : (0:ℝ) ≤ d := by exact_mod_cast (Nat.zero_le d)
  have hlt : (d:ℝ) < ((d:ℝ)+1)^2 := by nlinarith
  have hq : (0:ℝ) < 2 / n := by positivity
  have hscale : (d:ℝ) * ((2:ℝ)/n)^2 < (((d:ℝ)+1) * (2/(n:ℝ)))^2 := by
    calc
      (d:ℝ) * ((2:ℝ)/n)^2 < ((d:ℝ)+1)^2 * ((2:ℝ)/n)^2 := by
        exact mul_lt_mul_of_pos_right hlt (sq_pos_of_pos hq)
      _ = (((d:ℝ)+1) * (2/(n:ℝ)))^2 := by ring
  have htarget : ((2:ℝ) * ((d:ℝ)+1) / n) = ((d:ℝ)+1) * (2/(n:ℝ)) := by ring
  rw [htarget]
  have htpos : (0:ℝ) < ((d:ℝ)+1) * (2/(n:ℝ)) := by positivity
  nlinarith

/-- There are arbitrarily fine regular grids; this rational, over-large cell
bound is useful for avoiding square roots in the combinatorial argument. -/
lemma exists_grid_fine (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ (2:ℝ) * ((d:ℝ) + 1) / n < δ := by
  obtain ⟨n : ℕ, hn : (2:ℝ) * ((d:ℝ)+1) / δ < n⟩ := exists_nat_gt ((2:ℝ) * ((d:ℝ)+1) / δ)
  have hp : 0 < (2:ℝ) * ((d:ℝ)+1) / δ := by positivity
  have hn0 : 0 < n := by exact_mod_cast (lt_trans hp hn)
  refine ⟨n, hn0, ?_⟩
  have hn' : (0:ℝ) < n := by exact_mod_cast hn0
  apply (div_lt_iff₀ hn').2
  have hcross : (2:ℝ) * ((d:ℝ)+1) < (n:ℝ) * δ :=
    (div_lt_iff₀ hδ).mp hn
  nlinarith

end BrouwerSupport

namespace BrouwerSupport
namespace GridVertex

/-- The corner of the cell with lower indices `a`. Coordinates in the finite
set `s` have been advanced once. -/
def corner {d n : ℕ} (a : Fin d → Fin n) (s : Finset (Fin d)) :
    Fin d → Fin (n+1) := fun i =>
  ⟨(a i : ℕ) + if i ∈ s then 1 else 0, by
    split_ifs <;> omega⟩

@[simp] lemma corner_val {d n} (a : Fin d → Fin n) (s : Finset (Fin d)) (i : Fin d) :
    (corner a s i : ℕ) = (a i : ℕ) + if i ∈ s then 1 else 0 := rfl

lemma corner_diff {d n} (a : Fin d → Fin n) (s t : Finset (Fin d))
    (i : Fin d) :
    ((corner a s i : ℤ) - (corner a t i : ℤ)) ∈ Set.Icc (-1 : ℤ) 1 := by
  dsimp [corner]
  split_ifs <;> simp <;> omega

lemma dist_corners_lt {d n : ℕ} (hn : 0 < n)
    (a : Fin d → Fin n) (s t : Finset (Fin d)) :
    dist (gridPoint n (corner a s)) (gridPoint n (corner a t))
      < (2:ℝ) * ((d:ℝ)+1) / n :=
  dist_gridPoint_lt hn _ _ (corner_diff a s t)

@[simp] lemma corner_without {d n} (a : Fin d → Fin n)
    (s : Finset (Fin d)) (i : Fin d) (h : i ∉ s) :
    (corner a s i : ℕ) = (a i : ℕ) := by simp [corner_val, h]
@[simp] lemma corner_with {d n} (a : Fin d → Fin n)
    (s : Finset (Fin d)) (i : Fin d) (h : i ∈ s) :
    (corner a s i : ℕ) = (a i : ℕ)+1 := by simp [corner_val, h]

end GridVertex

end BrouwerSupport

end
-- END INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/GridGeometry.lean

-- BEGIN INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/Projection.lean
section

open Set Topology InnerProductSpace Real

/-! A small, self-contained form of the Hilbert projection theorem for a closed
convex subset of a real Hilbert space.  `exists_norm_eq_iInf_of_complete_convex`
in mathlib is formulated as an existence result; for fixed point reductions it
is quite convenient to have the resulting *map*, together with its elementary
Lipschitz estimate. -/

namespace BrouwerSupport

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Closest point on a nonempty complete convex set.  The proofs used here do
not rely on canonicity of the choice: uniqueness and the Lipschitz estimate
follow from the variational characterization. -/
noncomputable def convexProj (K : Set F) (hne : K.Nonempty)
    (hcomp : IsComplete K) (hconv : Convex ℝ K) (u : F) : F :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hcomp hconv u)

variable (K : Set F) (hne : K.Nonempty) (hcomp : IsComplete K)
  (hconv : Convex ℝ K)

lemma convexProj_mem (u : F) : convexProj K hne hcomp hconv u ∈ K :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hne hcomp hconv u)).1

lemma convexProj_min (u : F) :
    ‖u - convexProj K hne hcomp hconv u‖ = ⨅ w : K, ‖u - (w : F)‖ :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hne hcomp hconv u)).2

/-- Variational characterization of the point chosen by `convexProj`. -/
lemma convexProj_inner (u : F) :
    ∀ w ∈ K,
      @inner ℝ F _ (u - convexProj K hne hcomp hconv u)
        (w - convexProj K hne hcomp hconv u) ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hconv
      (convexProj_mem K hne hcomp hconv u)).1
    (convexProj_min K hne hcomp hconv u)

/-- The metric projection fixes every point of the set.  This also gives a
short uniqueness proof without needing a packaged strict-convexity lemma. -/
lemma convexProj_eq_self {u : F} (hu : u ∈ K) :
    convexProj K hne hcomp hconv u = u := by
  -- At a point of `K` the infimum distance is squeezed between `0` and
  -- `‖u-u‖`; since the chosen minimizer has distance zero it must be `u`.
  have hle : (⨅ w : K, ‖u - (w : F)‖) ≤ ‖u - (⟨u, hu⟩ : K)‖ :=
    ciInf_le ⟨(0:ℝ), by
      intro b hb
      rcases hb with ⟨w, rfl⟩
      exact norm_nonneg _⟩ _
  have hi : (⨅ w : K, ‖u - (w : F)‖) ≤ 0 := by
    simpa using hle
  have hnorm : ‖u - convexProj K hne hcomp hconv u‖ = 0 := by
    have hpnon : 0 ≤ ‖u - convexProj K hne hcomp hconv u‖ := norm_nonneg _
    have hp_le : ‖u - convexProj K hne hcomp hconv u‖ ≤ 0 := by
      calc
        ‖u - convexProj K hne hcomp hconv u‖ =
            (⨅ w : K, ‖u - (w : F)‖) := convexProj_min K hne hcomp hconv u
        _ ≤ 0 := hi
    exact le_antisymm hp_le hpnon
  have hz : u - convexProj K hne hcomp hconv u = 0 :=
    (norm_eq_zero.mp hnorm)
  exact (sub_eq_zero.mp hz).symm

/-- Algebraic heart of the Lipschitz assertion.  This form (with arbitrary
minimizers) is useful because it avoids any reasoning about choices. -/
lemma dist_minimizers_le {u v p q : F}
    (hp : ∀ w ∈ K, @inner ℝ F _ (u - p) (w - p) ≤ 0)
    (hq : ∀ w ∈ K, @inner ℝ F _ (v - q) (w - q) ≤ 0)
    (hpK : p ∈ K) (hqK : q ∈ K) :
    ‖p - q‖ ≤ ‖u - v‖ := by
  -- Put `z = p-q`.  The two variational inequalities give
  -- `‖z‖^2 ≤ ⟪u-v,z⟫`; Cauchy--Schwarz then finishes, including `z=0`.
  have hpa : @inner ℝ F _ (u - p) (q - p) ≤ 0 := hp q hqK
  have hqa : @inner ℝ F _ (v - q) (p - q) ≤ 0 := hq p hpK
  -- Rewrite `q-p` as `-(p-q)` in the first inequality.
  have hpz : 0 ≤ @inner ℝ F _ (u - p) (p - q) := by
    have hneg : q - p = -(p - q) := by abel
    rw [hneg, inner_neg_right] at hpa
    linarith
  -- Subtract the two inequalities and expand.  Keeping this as a scalar
  -- inequality makes the final division by `‖p-q‖` transparent.
  have hsq : ‖p - q‖ * ‖p - q‖ ≤
      @inner ℝ F _ (u - v) (p - q) := by
    have hdiff : 0 ≤
        @inner ℝ F _ (u - p) (p - q) -
          @inner ℝ F _ (v - q) (p - q) := sub_nonneg.mpr (le_trans hqa hpz)
    have hid :
        @inner ℝ F _ (u - p) (p - q) -
            @inner ℝ F _ (v - q) (p - q) =
          @inner ℝ F _ (u - v) (p - q) -
            @inner ℝ F _ (p - q) (p - q) := by
      rw [inner_sub_left, inner_sub_left, inner_sub_left]
      rw [inner_sub_left]
      ring
    rw [hid, real_inner_self_eq_norm_mul_norm] at hdiff
    linarith
  have hcs : @inner ℝ F _ (u - v) (p - q) ≤
      ‖u - v‖ * ‖p - q‖ := real_inner_le_norm _ _
  by_cases hz : ‖p - q‖ = 0
  · -- in this case the desired inequality is just non-negativity of a norm
    simpa [hz] using (norm_nonneg (u - v))
  · have hzpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hmul : ‖p - q‖ * ‖p - q‖ ≤ ‖u - v‖ * ‖p - q‖ :=
      le_trans hsq hcs
    exact le_of_mul_le_mul_right hmul hzpos

/-- The chosen projection is 1-Lipschitz, hence in particular continuous. -/
lemma convexProj_lipschitz :
    LipschitzWith 1 (convexProj K hne hcomp hconv) := by
  refine (lipschitzWith_iff_dist_le_mul).2 ?_
  intro x y
  simp [dist_eq_norm] -- try
  change ‖convexProj K hne hcomp hconv x -
            convexProj K hne hcomp hconv y‖ ≤ ‖x - y‖
  exact dist_minimizers_le K
    (convexProj_inner K hne hcomp hconv x)
    (convexProj_inner K hne hcomp hconv y)
    (convexProj_mem K hne hcomp hconv x)
    (convexProj_mem K hne hcomp hconv y)

lemma continuous_convexProj :
    Continuous (convexProj K hne hcomp hconv) :=
  (convexProj_lipschitz K hne hcomp hconv).continuous

end BrouwerSupport

end
-- END INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/Projection.lean

-- BEGIN INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/Parity.lean
section

open Finset
namespace BrouwerSupport
namespace Parity
open BrouwerSupport.Grid

-- assignments of the lower coordinates in a face of the rectangular grid
abbrev Asg {d : ℕ} (T : Finset (Fin d)) (n : ℕ) := (x : (↥T)) → Fin n

def zfin {n : ℕ} (hn : 0 < n) : Fin n := ⟨0, hn⟩

def extBase {d n : ℕ} (hn : 0 < n) (T : Finset (Fin d)) (a : Asg T n) : Fin d → Fin n :=
  fun i => if h : i ∈ T then a ⟨i,h⟩ else zfin hn

/-- the vertex map of an elementary face; all coordinates outside `T` are fixed at the bottom.-/
def vert {d n : ℕ} (hn : 0 < n) (T : Finset (Fin d)) (a : Asg T n)
    (s : Finset (Fin d)) : Fin d → Fin (n+1) :=
  GridVertex.corner (extBase hn T a) (s ∩ T)

/-- turn a boolean label into an F2 vertex function on a face -/
def lab {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (T : Finset (Fin d)) (a : Asg T n) (i : Fin d) : Finset (Fin d) → F2 :=
  fun s => if L (vert hn T a s) i = true then 1 else 0

def tot {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (is : List (Fin d)) : F2 :=
  let T := is.toFinset
  ∑ a : Asg T n, Grid.paths (is.map (fun i => lab hn L T a i)) ∅ T

/-- assignments split into the coordinate `j` and all other ones -/
def splitEquiv {d n : ℕ} (T : Finset (Fin d)) (j : Fin d) (hj : j ∈ T) :
    Asg T n ≃ (Fin n × Asg (T.erase j) n) where
  toFun a :=
    (a ⟨j,hj⟩,
     fun k => a ⟨(k : Fin d), Finset.mem_of_mem_erase k.property⟩)
  invFun p :=
    fun k => if h : (k : Fin d) = j then
      p.1
    else
      p.2 ⟨(k : Fin d), Finset.mem_erase.mpr ⟨h, k.property⟩⟩
  left_inv := by
    intro a
    funext k
    dsimp
    split_ifs with h
    · subst j
      rfl
    · rfl
  right_inv := by
    intro p
    cases p with
    | mk q r =>
      apply Prod.ext
      · dsimp
        simp
      · funext k
        dsimp
        split_ifs with h
        · have hk := (Finset.mem_erase.mp k.property).1
          exact (hk h).elim
        · rfl

/-- a small telescoping identity for F2 on an interval -/
lemma sum_succ_cast {n : ℕ} (g : Fin (n+1) → F2) :
    (∑ k : Fin n, (g k.succ + g k.castSucc)) = g (Fin.last n) + g 0 := by
  classical
  rw [Finset.sum_add_distrib]
  have h : g 0 + (∑ k : Fin n, g k.succ) =
      (∑ k : Fin n, g k.castSucc) + g (Fin.last n) := by
    calc
      g 0 + (∑ k : Fin n, g k.succ) = ∑ q : Fin (n+1), g q :=
        (Fin.sum_univ_succ g).symm
      _ = (∑ k : Fin n, g k.castSucc) + g (Fin.last n) :=
        Fin.sum_univ_castSucc g
  calc
    (∑ k : Fin n, g k.succ) + (∑ k : Fin n, g k.castSucc)
        = (g 0 + (∑ k : Fin n, g k.succ)) +
            (g 0 + (∑ k : Fin n, g k.castSucc)) := by
              -- insert the two cancelling copies
              rw [show g 0 + (∑ k : Fin n, g k.succ) +
                    (g 0 + (∑ k : Fin n, g k.castSucc)) =
                    ((∑ k : Fin n, g k.succ) + (∑ k : Fin n, g k.castSucc)) +
                      (g 0 + g 0) by ac_rfl]
              simp
    _ = ((∑ k : Fin n, g k.castSucc) + g (Fin.last n)) +
            (g 0 + (∑ k : Fin n, g k.castSucc)) := by rw [h]
    _ = g (Fin.last n) + g 0 := by
          rw [show ((∑ k : Fin n, g k.castSucc) + g (Fin.last n)) +
                    (g 0 + (∑ k : Fin n, g k.castSucc)) =
                    (g (Fin.last n) + g 0) +
                      ((∑ k : Fin n, g k.castSucc) + (∑ k : Fin n, g k.castSucc)) by ac_rfl]
          simp

/-- Restrict all vertex functions to an affine subface. This harmless
naturality of `paths` lets us forget fixed coordinates. -/
lemma paths_anchor
    {A : Type*} [DecidableEq A]
    (l : List (Finset A → F2)) (V anchor : Finset A) :
    let l' := l.map (fun f => fun r : Finset A => f (anchor ∪ (r ∩ V)))
    ∀ (s u : Finset A), s ⊆ V → u ⊆ V →
      Grid.paths l' s u = Grid.paths l (anchor ∪ s) u := by
  classical
  dsimp
  induction l with
  | nil =>
      intro s u hs hu
      simp [Grid.paths]
  | cons b l ih =>
      intro s u hs hu
      simp only [List.map_cons, Grid.paths_cons]
      apply Finset.sum_congr rfl
      intro a ha
      have haV : a ∈ V := hu ha
      have hs' : insert a s ⊆ V := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact haV
        · exact hs hx
      have hu' : u.erase a ⊆ V := Finset.Subset.trans (Finset.erase_subset _ _) hu
      have he1 : anchor ∪ (insert a s ∩ V) = insert a (anchor ∪ s) := by
        ext x
        by_cases hx : x = a
        · subst x; simp [haV]
        · by_cases hv : x ∈ V
          · simp [Finset.mem_union, hv, hx]
          · have hxs : x ∉ s := fun h => hv (hs h)
            simp [Finset.mem_union, hv, hx, hxs]
      have he0 : anchor ∪ (s ∩ V) = anchor ∪ s := by
        ext x
        by_cases hv : x ∈ V
        · simp [Finset.mem_union, hv]
        · have hxs : x ∉ s := fun h => hv (hs h)
          simp [Finset.mem_union, hv, hxs]
      rw [he1, he0]
      rw [ih (insert a s) (u.erase a) hs' hu']
      have huins : anchor ∪ insert a s = insert a (anchor ∪ s) := by
        ext x; simp [Finset.mem_union, or_assoc, or_left_comm, or_comm]
      rw [huins]

/-- vertex map of a face with the coordinate `j` pinned at the arbitrary level `q` -/
def faceVert {d n : ℕ} (hn : 0 < n)
    (T : Finset (Fin d)) (j : Fin d)
    (r : Asg (T.erase j) n) (q : Fin (n+1))
    (s : Finset (Fin d)) : Fin d → Fin (n+1) :=
  fun k => if h : k = j then q
      else GridVertex.corner (extBase hn (T.erase j) r) (s ∩ (T.erase j)) k

def faceLab {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (T : Finset (Fin d)) (j : Fin d)
    (r : Asg (T.erase j) n) (q : Fin (n+1)) (i : Fin d) :
    Finset (Fin d) → F2 :=
  fun s => if L (faceVert hn T j r q s) i = true then 1 else 0

def faceVal {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (T : Finset (Fin d)) (j i : Fin d)
    (tail : List (Fin d))
    (r : Asg (T.erase j) n) (q : Fin (n+1)) : F2 :=
  faceLab hn L T j r q i ∅ *
    Grid.paths (tail.map (fun k => faceLab hn L T j r q k)) ∅ (T.erase j)

-- equalities between a cell and its two descriptions of a face
lemma face_lower_vertex {d n : ℕ} (hn : 0 < n)
    (T : Finset (Fin d)) (j : Fin d) (hj : j ∈ T)
    (k : Fin n) (r : Asg (T.erase j) n)
    (s : Finset (Fin d)) :
    faceVert hn T j r k.castSucc s =
      vert hn T ((splitEquiv T j hj).symm (k,r)) (s ∩ (T.erase j)) := by
  classical
  funext x
  by_cases hx : x = j
  · subst x
    have hv (p : j ∈ T) : ((splitEquiv T j hj).symm (k,r)) ⟨j,p⟩ = k := by
      have H := congrArg Prod.fst ((splitEquiv T j hj).apply_symm_apply (k,r))
      exact H
    simp only [faceVert, if_pos rfl, vert, GridVertex.corner, extBase]
    simp [hj]
    apply Fin.ext
    change (k:ℕ) = (((splitEquiv T j hj).symm (k,r)) ⟨j, _⟩ : Fin n).val
    exact congrArg Fin.val (hv _).symm
  · have he : x ∈ T.erase j ↔ x ∈ T := by simp [hx]
    by_cases hT : x ∈ T
    · have hE : x ∈ T.erase j := he.mpr hT
      -- other active coordinate
      -- reduce everything to r at that coordinate
      simp [faceVert, vert, GridVertex.corner, extBase, hx, hT, hE,
        splitEquiv]
    · have hE : x ∉ T.erase j := by simpa [hx] using hT
      -- outside, bottom
      simp [faceVert, vert, GridVertex.corner, extBase, hx, hT, hE, zfin,
        splitEquiv]

lemma face_upper_vertex {d n : ℕ} (hn : 0 < n)
    (T : Finset (Fin d)) (j : Fin d) (hj : j ∈ T)
    (k : Fin n) (r : Asg (T.erase j) n)
    (s : Finset (Fin d)) :
    faceVert hn T j r k.succ s =
      vert hn T ((splitEquiv T j hj).symm (k,r))
        (insert j (s ∩ (T.erase j))) := by
  classical
  funext x
  by_cases hx : x = j
  · subst x
    have hv (p : j ∈ T) : ((splitEquiv T j hj).symm (k,r)) ⟨j,p⟩ = k := by
      have H := congrArg Prod.fst ((splitEquiv T j hj).apply_symm_apply (k,r))
      exact H
    simp only [faceVert, if_pos rfl, vert, GridVertex.corner, extBase]
    simp [hj]
    apply Fin.ext
    change (k.val+1) = (((splitEquiv T j hj).symm (k,r)) ⟨j, _⟩ : Fin n).val + 1
    rw [hv]
  · have he : x ∈ T.erase j ↔ x ∈ T := by simp [hx]
    by_cases hT : x ∈ T
    · have hE : x ∈ T.erase j := he.mpr hT
      simp [faceVert, vert, GridVertex.corner, extBase, hx, hT, hE,
        splitEquiv]
    · have hE : x ∉ T.erase j := by simpa [hx] using hT
      simp [faceVert, vert, GridVertex.corner, extBase, hx, hT, hE, zfin,
        splitEquiv]

-- converting the face terms of the cellular boundary
lemma face_lower_val {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (T : Finset (Fin d)) (j i : Fin d) (hj : j ∈ T)
    (tail : List (Fin d))
    (k : Fin n) (r : Asg (T.erase j) n) :
    faceVal hn L T j i tail r k.castSucc =
      lab hn L T ((splitEquiv T j hj).symm (k,r)) i ∅ *
        Grid.paths (tail.map (fun m => lab hn L T ((splitEquiv T j hj).symm (k,r)) m))
          ∅ (T.erase j) := by
  classical
  -- every face label is a restriction with empty anchor
  let a : Asg T n := (splitEquiv T j hj).symm (k,r)
  have ef (m : Fin d) (s : Finset (Fin d)) :
      faceLab hn L T j r k.castSucc m s =
        lab hn L T a m (∅ ∪ (s ∩ (T.erase j))) := by
    dsimp [faceLab, lab, a]
    rw [face_lower_vertex hn T j hj k r s]
    simp
  have ep :
      Grid.paths (tail.map (fun m => faceLab hn L T j r k.castSucc m)) ∅ (T.erase j)
      = Grid.paths (tail.map (fun m => lab hn L T a m)) (∅ ∪ ∅) (T.erase j) := by
    -- use the anchor lemma
    have h := paths_anchor (tail.map (fun m => lab hn L T a m)) (T.erase j) (∅ : Finset (Fin d))
      (∅ : Finset (Fin d)) (T.erase j) (by simp) (by intro x; exact id)
    -- convert the mapped list
    have lists :
        tail.map (fun m => faceLab hn L T j r k.castSucc m) =
          (tail.map (fun m => lab hn L T a m)).map
            (fun f => fun s : Finset (Fin d) => f (∅ ∪ (s ∩ (T.erase j)))) := by
      have funs (m : Fin d) :
          faceLab hn L T j r k.castSucc m =
            (fun s : Finset (Fin d) => lab hn L T a m (∅ ∪ (s ∩ (T.erase j)))) :=
            funext (ef m)
      rw [List.map_map]
      apply List.map_congr_left
      intro m hm
      exact funs m
    rw [lists]
    exact h
  unfold faceVal
  rw [ep]
  -- the leading vertex too
  rw [ef i ∅]
  simp [a]

lemma face_upper_val {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (T : Finset (Fin d)) (j i : Fin d) (hj : j ∈ T)
    (tail : List (Fin d))
    (k : Fin n) (r : Asg (T.erase j) n) :
    faceVal hn L T j i tail r k.succ =
      lab hn L T ((splitEquiv T j hj).symm (k,r)) i (insert j ∅) *
        Grid.paths (tail.map (fun m => lab hn L T ((splitEquiv T j hj).symm (k,r)) m))
          (insert j ∅) (T.erase j) := by
  classical
  let a : Asg T n := (splitEquiv T j hj).symm (k,r)
  have ef (m : Fin d) (s : Finset (Fin d)) :
      faceLab hn L T j r k.succ m s =
        lab hn L T a m ({j} ∪ (s ∩ (T.erase j))) := by
    dsimp [faceLab, lab, a]
    rw [face_upper_vertex hn T j hj k r s]
  have ep :
      Grid.paths (tail.map (fun m => faceLab hn L T j r k.succ m)) ∅ (T.erase j)
      = Grid.paths (tail.map (fun m => lab hn L T a m)) ({j} ∪ ∅) (T.erase j) := by
    have h := paths_anchor (tail.map (fun m => lab hn L T a m)) (T.erase j) ({j} : Finset (Fin d))
      (∅ : Finset (Fin d)) (T.erase j) (by simp) (by intro x; exact id)
    have lists :
        tail.map (fun m => faceLab hn L T j r k.succ m) =
          (tail.map (fun m => lab hn L T a m)).map
            (fun f => fun s : Finset (Fin d) => f ({j} ∪ (s ∩ (T.erase j)))) := by
      have funs (m : Fin d) :
          faceLab hn L T j r k.succ m =
            (fun s : Finset (Fin d) => lab hn L T a m ({j} ∪ (s ∩ (T.erase j)))) :=
            funext (ef m)
      rw [List.map_map]
      apply List.map_congr_left
      intro m hm
      exact funs m
    rw [lists]
    exact h
  unfold faceVal
  rw [ep, ef i ∅]
  simp [a]

end Parity
end BrouwerSupport

namespace BrouwerSupport.Parity
open Finset
open BrouwerSupport.Grid

lemma face_zero_vertex {d n : ℕ} (hn : 0 < n)
    (T : Finset (Fin d)) (j : Fin d)
    (r : Asg (T.erase j) n) (s : Finset (Fin d)) :
    faceVert hn T j r (0 : Fin (n+1)) s = vert hn (T.erase j) r s := by
  classical
  funext x
  by_cases hx : x = j
  · subst x
    simp [faceVert, vert, GridVertex.corner, extBase, zfin]
  · simp [faceVert, vert, GridVertex.corner, extBase, hx]

lemma face_coord_zero {d n : ℕ} (hn : 0 < n)
    (T : Finset (Fin d)) (j : Fin d) (r : Asg (T.erase j) n)
    (s : Finset (Fin d)) :
    ((faceVert hn T j r (0 : Fin (n+1)) s j : Fin (n+1)) : ℕ) = 0 := by
  simp [faceVert]
lemma face_coord_last {d n : ℕ} (hn : 0 < n)
    (T : Finset (Fin d)) (j : Fin d) (r : Asg (T.erase j) n)
    (s : Finset (Fin d)) :
    ((faceVert hn T j r (Fin.last n) s j : Fin (n+1)) : ℕ) = n := by
  simp [faceVert]

lemma faceLab_low_j {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (hlo : ∀ v i, (v i : ℕ) = 0 → L v i = true)
    (T : Finset (Fin d)) (j : Fin d) (r : Asg (T.erase j) n)
    (s : Finset (Fin d)) :
    faceLab hn L T j r 0 j s = 1 := by
  unfold faceLab
  have H : L (faceVert hn T j r 0 s) j = true :=
    hlo _ j (face_coord_zero hn T j r s)
  simp [H]
lemma faceLab_high_j {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (hhi : ∀ v i, (v i : ℕ) = n → L v i = false)
    (T : Finset (Fin d)) (j : Fin d) (r : Asg (T.erase j) n)
    (s : Finset (Fin d)) :
    faceLab hn L T j r (Fin.last n) j s = 0 := by
  unfold faceLab
  rw [if_neg]
  intro h
  have hh := hhi _ j (face_coord_last hn T j r s)
  rw [hh] at h
  cases h

lemma face_zero_other_low {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (hlo : ∀ v i, (v i : ℕ) = 0 → L v i = true)
    (T : Finset (Fin d)) (j i : Fin d) (tail : List (Fin d))
    (hm : j ∈ tail)
    (r : Asg (T.erase j) n) :
    faceVal hn L T j i tail r (0 : Fin (n+1)) = 0 := by
  classical
  have hb : faceLab hn L T j r 0 j ∈
      tail.map (fun k => faceLab hn L T j r 0 k) :=
    List.mem_map.mpr ⟨j, hm, rfl⟩
  have zz := Grid.paths_eq_zero_of_mem_flat
      (tail.map (fun k => faceLab hn L T j r 0 k))
      (faceLab hn L T j r 0 j) hb (T.erase j) (by
        intro s a ha
        rw [faceLab_low_j hn L hlo T j r,
            faceLab_low_j hn L hlo T j r]) (∅ : Finset (Fin d))
  -- leading factor irrelevant
  simp [faceVal, zz]

lemma face_zero_other_high {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (hhi : ∀ v i, (v i : ℕ) = n → L v i = false)
    (T : Finset (Fin d)) (j i : Fin d) (tail : List (Fin d))
    (hm : j ∈ tail)
    (r : Asg (T.erase j) n) :
    faceVal hn L T j i tail r (Fin.last n) = 0 := by
  classical
  have hb : faceLab hn L T j r (Fin.last n) j ∈
      tail.map (fun k => faceLab hn L T j r (Fin.last n) k) :=
    List.mem_map.mpr ⟨j, hm, rfl⟩
  have zz := Grid.paths_eq_zero_of_mem_flat
      (tail.map (fun k => faceLab hn L T j r (Fin.last n) k))
      (faceLab hn L T j r (Fin.last n) j) hb (T.erase j) (by
        intro s a ha
        rw [faceLab_high_j hn L hhi T j r,
            faceLab_high_j hn L hhi T j r]) (∅ : Finset (Fin d))
  simp [faceVal, zz]

lemma face_head_high {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (hhi : ∀ v i, (v i : ℕ) = n → L v i = false)
    (T : Finset (Fin d)) (j : Fin d) (tail : List (Fin d))
    (r : Asg (T.erase j) n) :
    faceVal hn L T j j tail r (Fin.last n) = 0 := by
  unfold faceVal
  rw [faceLab_high_j hn L hhi T j r]
  simp

lemma face_head_low {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (hlo : ∀ v i, (v i : ℕ) = 0 → L v i = true)
    (T : Finset (Fin d)) (j : Fin d) (tail : List (Fin d))
    (r : Asg (T.erase j) n) :
    faceVal hn L T j j tail r (0 : Fin (n+1)) =
      Grid.paths (tail.map (fun k => lab hn L (T.erase j) r k)) ∅ (T.erase j) := by
  classical
  have ef (k : Fin d) :
      faceLab hn L T j r (0 : Fin (n+1)) k = lab hn L (T.erase j) r k := by
    funext s
    unfold faceLab lab
    rw [face_zero_vertex]
  unfold faceVal
  rw [faceLab_low_j hn L hlo T j r]
  simp only [one_mul]
  congr 2
  funext k
  exact ef k

end BrouwerSupport.Parity
namespace BrouwerSupport.Parity
open Finset
open BrouwerSupport.Grid

lemma tot_cons {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (hlo : ∀ v i, (v i : ℕ) = 0 → L v i = true)
    (hhi : ∀ v i, (v i : ℕ) = n → L v i = false)
    (i : Fin d) (tail : List (Fin d))
    (hnd : (i :: tail).Nodup) :
    tot hn L (i :: tail) = tot hn L tail := by
  classical
  let T : Finset (Fin d) := (i :: tail).toFinset
  have hiT : i ∈ T := by simp [T]
  have hnot : i ∉ tail := (List.nodup_cons.mp hnd).1
  have htailnd : tail.Nodup := (List.nodup_cons.mp hnd).2
  have Terase : T.erase i = tail.toFinset := by
    simp [T, List.toFinset_cons, List.mem_toFinset, hnot]
  have cardT : T.card = (tail.map
        (fun m => lab hn L T (Classical.choice (show Nonempty (Asg T n) from
          ⟨fun _ => zfin hn⟩)) m)).length + 1 := by
    -- the right list has length of tail; the functions do not matter
    rw [List.length_map]
    have hc := List.toFinset_card_of_nodup hnd
    -- card of list
    simp [T] at hc ⊢
    omega
  -- boundary identity at a single cell, with the functions depending on it
  have one (a : Asg T n) :
      Grid.paths ((i::tail).map (fun m => lab hn L T a m)) ∅ T =
        ∑ j ∈ T,
          (lab hn L T a i (insert j ∅) *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                (insert j ∅) (T.erase j) +
           lab hn L T a i ∅ *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                ∅ (T.erase j)) := by
    have ht : T.card = (tail.map (fun m => lab hn L T a m)).length + 1 := by
      rw [List.length_map]
      have hc := List.toFinset_card_of_nodup hnd
      change T.card = _
      -- hc : (i::tail).toFinset.card = ...
      simpa [T] using hc
    have eq := Grid.paths_eq_boundary
      (lab hn L T a i) (tail.map (fun m => lab hn L T a m))
        (∅ : Finset (Fin d)) T ht
    -- expand the boundary
    simpa [Grid.boundary] using eq
  -- sum over the cells in one direction telescopes
  have strip (j : Fin d) (hj : j ∈ T) :
      (∑ a : Asg T n,
          (lab hn L T a i (insert j ∅) *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                (insert j ∅) (T.erase j) +
           lab hn L T a i ∅ *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                ∅ (T.erase j))) =
        ∑ r : Asg (T.erase j) n,
           (faceVal hn L T j i tail r (Fin.last n) +
            faceVal hn L T j i tail r (0 : Fin (n+1))) := by
    classical
    -- split an assignment and use the two face identifications
    calc
      (∑ a : Asg T n,
          (lab hn L T a i (insert j ∅) *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                (insert j ∅) (T.erase j) +
           lab hn L T a i ∅ *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                ∅ (T.erase j))) =
          ∑ p : (Fin n × Asg (T.erase j) n),
            (faceVal hn L T j i tail p.2 p.1.succ +
             faceVal hn L T j i tail p.2 p.1.castSucc) := by
                -- reindex the finite sum via `splitEquiv`
                apply Fintype.sum_equiv (splitEquiv T j hj)
                intro a
                -- the lower and the upper faces
                rw [face_upper_val hn L T j i hj tail, face_lower_val hn L T j i hj tail]
                have ee : (splitEquiv T j hj).symm ((splitEquiv T j hj) a) = a :=
                  (splitEquiv T j hj).symm_apply_apply a
                simpa using (congrArg (fun z : Asg T n =>
                  lab hn L T z i (insert j ∅) *
                    Grid.paths (tail.map (fun m => lab hn L T z m))
                      (insert j ∅) (T.erase j) +
                  lab hn L T z i ∅ *
                    Grid.paths (tail.map (fun m => lab hn L T z m))
                      ∅ (T.erase j)) ee).symm
      _ = ∑ k : Fin n, ∑ r : Asg (T.erase j) n,
            (faceVal hn L T j i tail r k.succ +
             faceVal hn L T j i tail r k.castSucc) := by
                rw [Fintype.sum_prod_type]
      _ = ∑ r : Asg (T.erase j) n, ∑ k : Fin n,
            (faceVal hn L T j i tail r k.succ +
             faceVal hn L T j i tail r k.castSucc) := by
                -- commute the two finite sums
                exact Finset.sum_comm
      _ = ∑ r : Asg (T.erase j) n,
           (faceVal hn L T j i tail r (Fin.last n) +
            faceVal hn L T j i tail r (0 : Fin (n+1))) := by
                apply Finset.sum_congr rfl
                intro r hr
                exact sum_succ_cast (fun q => faceVal hn L T j i tail r q)
  -- now sum the boundary of all the cells
  change (∑ a : Asg T n,
        Grid.paths ((i::tail).map (fun m => lab hn L T a m)) ∅ T) = _
  rw [show (∑ a : Asg T n,
        Grid.paths ((i::tail).map (fun m => lab hn L T a m)) ∅ T) =
      ∑ a : Asg T n, ∑ j ∈ T,
          (lab hn L T a i (insert j ∅) *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                (insert j ∅) (T.erase j) +
           lab hn L T a i ∅ *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                ∅ (T.erase j)) by
        apply Finset.sum_congr rfl
        intro a ha
        exact one a]
  -- put directions before cells, then use strips
  rw [show (∑ a : Asg T n, ∑ j ∈ T,
          (lab hn L T a i (insert j ∅) *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                (insert j ∅) (T.erase j) +
           lab hn L T a i ∅ *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                ∅ (T.erase j))) =
      ∑ j ∈ T, ∑ a : Asg T n,
          (lab hn L T a i (insert j ∅) *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                (insert j ∅) (T.erase j) +
           lab hn L T a i ∅ *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                ∅ (T.erase j)) by
          -- univ and T
          exact Finset.sum_comm]
  rw [show (∑ j ∈ T, ∑ a : Asg T n,
          (lab hn L T a i (insert j ∅) *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                (insert j ∅) (T.erase j) +
           lab hn L T a i ∅ *
              Grid.paths (tail.map (fun m => lab hn L T a m))
                ∅ (T.erase j))) =
        ∑ j ∈ T, ∑ r : Asg (T.erase j) n,
          (faceVal hn L T j i tail r (Fin.last n) +
           faceVal hn L T j i tail r (0 : Fin (n+1))) by
            apply Finset.sum_congr rfl
            intro j hj
            exact strip j hj]
  -- only the face belonging to the head coordinate remains
  rw [Finset.sum_eq_single i]
  · -- that strip is the total on the smaller bottom face
    simp_rw [face_head_high hn L hhi T i tail]
    simp_rw [face_head_low hn L hlo T i tail]
    -- put T.erase i = tail.toFinset
    simp only [zero_add]
    change (∑ x : Asg (T.erase i) n, _ ) = tot hn L tail
    rw [Terase]
    rfl
  · intro j hjT hji
    have hmset : j ∈ tail.toFinset := by
      have : j = i ∨ j ∈ tail.toFinset := by simpa [T] using hjT
      rcases this with e | e
      · exact (hji e).elim
      · exact e
    have hm : j ∈ tail := (List.mem_toFinset.mp hmset)
    simp_rw [face_zero_other_high hn L hhi T j i tail hm]
    simp_rw [face_zero_other_low hn L hlo T j i tail hm]
    simp
  · intro hh
    exact (hh hiT).elim
end BrouwerSupport.Parity
namespace BrouwerSupport.Parity
open Finset
open BrouwerSupport.Grid
lemma tot_one {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (hlo : ∀ v i, (v i : ℕ) = 0 → L v i = true)
    (hhi : ∀ v i, (v i : ℕ) = n → L v i = false) :
    ∀ is : List (Fin d), is.Nodup → tot hn L is = 1 := by
  intro is h
  induction is with
  | nil =>
      -- there is just the empty assignment and the empty vertex
      classical
      simp [tot, Asg, Grid.paths]
  | cons i t ih =>
      rw [tot_cons hn L hlo hhi i t h]
      exact ih (List.nodup_cons.mp h).2

lemma vert_univ {d n : ℕ} (hn : 0 < n)
    (a : Asg (Finset.univ : Finset (Fin d)) n) (s : Finset (Fin d)) :
    vert hn Finset.univ a s =
      GridVertex.corner (fun i => a ⟨i, Finset.mem_univ i⟩) s := by
  classical
  unfold vert extBase
  congr 1
  · funext i
    simp
  · simp

/-- finite labelled cubical lemma -/
theorem labeled_cell {d n : ℕ} (hn : 0 < n)
    (L : (Fin d → Fin (n+1)) → Fin d → Bool)
    (hlo : ∀ v i, (v i : ℕ) = 0 → L v i = true)
    (hhi : ∀ v i, (v i : ℕ) = n → L v i = false) :
    ∃ a : Fin d → Fin n, ∀ i : Fin d,
       (∃ s : Finset (Fin d), L (GridVertex.corner a s) i = true) ∧
       (∃ t : Finset (Fin d), L (GridVertex.corner a t) i = false) := by
  classical
  let is : List (Fin d) := (Finset.univ : Finset (Fin d)).toList
  have nd : is.Nodup := Finset.nodup_toList _
  have isT : is.toFinset = (Finset.univ : Finset (Fin d)) := by
    exact Finset.toList_toFinset _
  have total := tot_one hn L hlo hhi is nd
  unfold tot at total
  -- pick a cell with non-zero characteristic product
  have existsa : ∃ a : Asg (Finset.univ : Finset (Fin d)) n,
      Grid.paths (is.map (fun k => lab hn L Finset.univ a k)) ∅ Finset.univ ≠ 0 := by
    rw [isT] at total
    by_contra hh
    push_neg at hh
    have z : (∑ a : Asg (Finset.univ : Finset (Fin d)) n,
        Grid.paths (is.map (fun k => lab hn L Finset.univ a k)) ∅ Finset.univ) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      exact hh a
    rw [z] at total
    have no : (0 : Grid.F2) ≠ 1 := by decide
    exact no total
  obtain ⟨a, ha⟩ := existsa
  let af : Fin d → Fin n := fun i => a ⟨i, Finset.mem_univ i⟩
  refine ⟨af, ?_⟩
  intro i
  have him : i ∈ is := by simp [is]
  let bi : Finset (Fin d) → Grid.F2 := lab hn L Finset.univ a i
  have hbmem : bi ∈ (is.map (fun k => lab hn L Finset.univ a k)) :=
    List.mem_map.mpr ⟨i, him, rfl⟩
  -- some edge changes this label, or its differential would kill the product
  have notflat : ¬ (∀ (s : Finset (Fin d)) (j : Fin d), j ∈ (Finset.univ : Finset (Fin d)) →
          bi (insert j s) = bi s) := by
    intro flat
    have zz := Grid.paths_eq_zero_of_mem_flat
      (is.map (fun k => lab hn L Finset.univ a k)) bi hbmem
      (Finset.univ : Finset (Fin d)) flat (∅ : Finset (Fin d))
    exact ha zz
  push_neg at notflat
  obtain ⟨s,j,hj,hdiff⟩ := notflat
  have ev (u : Finset (Fin d)) :
      bi u = if L (GridVertex.corner af u) i = true then 1 else 0 := by
    unfold bi lab
    rw [vert_univ hn a u]
  have booldiff :
      L (GridVertex.corner af (insert j s)) i ≠
        L (GridVertex.corner af s) i := by
    intro e
    apply hdiff
    simp [ev, e]
  -- two different booleans are the two truth values
  by_cases e : L (GridVertex.corner af s) i = true
  · have e' : L (GridVertex.corner af (insert j s)) i = false := by
      cases h : L (GridVertex.corner af (insert j s)) i with
      | false => rfl
      | true => exact (booldiff (by rw [h, e])).elim
    exact ⟨⟨s, e⟩, ⟨insert j s, e'⟩⟩
  · have es : L (GridVertex.corner af s) i = false := by
      cases h : L (GridVertex.corner af s) i with
      | false => rfl
      | true => exact (e h).elim
    have et : L (GridVertex.corner af (insert j s)) i = true := by
      cases h : L (GridVertex.corner af (insert j s)) i with
      | true => rfl
      | false => exact (booldiff (by rw [h, es])).elim
    exact ⟨⟨insert j s, et⟩, ⟨s, es⟩⟩
end BrouwerSupport.Parity

end
-- END INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/Parity.lean

-- BEGIN INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/Cube.lean
section

open Set Topology

namespace BrouwerSupport

/-- Symmetric coordinate cube in Euclidean space (coordinates come from
`PiLp`, so it is convenient not to put an order on `EuclideanSpace`). -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, |x i| ≤ (1:ℝ)}

lemma cube_nonempty (d : ℕ) : (cube d).Nonempty := by
  refine ⟨0, ?_⟩
  intro i
  simp

lemma unitBall_subset_cube (d : ℕ) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (1:ℝ) ⊆ cube d := by
  intro x hx i
  have hx' : ‖x‖ ≤ (1:ℝ) := by
    simpa [Metric.mem_closedBall] using hx
  have hi := PiLp.norm_apply_le x i
  rw [Real.norm_eq_abs] at hi
  exact le_trans hi hx'

lemma isClosed_cube (d : ℕ) : IsClosed (cube d) := by
  have hh : (cube d) = ⋂ i : Fin d,
        {x : EuclideanSpace ℝ (Fin d) | |x i| ≤ (1:ℝ)} := by
    ext x
    simp [cube]
  rw [hh]
  apply isClosed_iInter
  intro i
  apply isClosed_le
  · exact (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).abs
  · fun_prop

lemma cube_subset_bigBall (d : ℕ) :
    cube d ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ((d:ℝ) + 1) := by
  intro x hx
  have hs : (∑ i : Fin d, (x i) ^ 2) ≤ (d : ℝ) := by
    calc
      (∑ i : Fin d, (x i)^2) ≤ ∑ _i : Fin d, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hai : 0 ≤ |x i| := abs_nonneg _
        have hsqi := (sq_le_sq₀ hai (by norm_num : (0:ℝ) ≤ 1)).2 (hx i)
        simpa [sq_abs] using hsqi
      _ = (d:ℝ) := by simp
  have hsq : ‖x‖ ^ 2 ≤ (d:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact hs
  have hn : ‖x‖ ≤ (d:ℝ) + 1 := by
    have hdn : 0 ≤ (d:ℝ) := Nat.cast_nonneg _
    have hnorm : 0 ≤ ‖x‖ := norm_nonneg _
    nlinarith
  simpa [Metric.mem_closedBall] using hn

lemma isCompact_cube (d : ℕ) : IsCompact (cube d) := by
  -- Closed and bounded in the proper finite-dimensional Euclidean space.
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_cube d) ?_
  exact (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin d))).2
    ⟨(d:ℝ)+1, cube_subset_bigBall d⟩


/-- In dimension one the cubical step is just the ordinary intermediate value
theorem. Keeping this degenerate case out of the combinatorial lemma is useful
(the grid lemma will only have to handle dimension at least two). -/
lemma cube_fixed_one
    (g : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
    (hg : ContinuousOn g (cube 1)) (hm : MapsTo g (cube 1) (cube 1)) :
    ∃ x ∈ cube 1, g x = x := by
  let ofR : ℝ → EuclideanSpace ℝ (Fin 1) :=
    fun t => (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => t)
  have ofR_apply (t : ℝ) (i : Fin 1) : ofR t i = t := by
    simp [ofR]
  have ofR_mem {t:ℝ} (ht : t ∈ Icc (-1:ℝ) 1) : ofR t ∈ cube 1 := by
    intro i
    rw [ofR_apply]
    exact (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
  have cofr : Continuous ofR := by dsimp [ofR]; fun_prop
  let F : ℝ → ℝ := fun t => g (ofR t) (0:Fin 1) - t
  have Fcont : ContinuousOn F (Icc (-1:ℝ) 1) := by
    have hcomp := hg.comp cofr.continuousOn (fun t (ht:t∈Icc (-1:ℝ) 1) => ofR_mem ht)
    have hcoord' : ContinuousOn (fun t : ℝ => (g (ofR t)) (0:Fin 1)) (Icc (-1:ℝ) 1) := by
      have hc : Continuous (fun z : EuclideanSpace ℝ (Fin 1) => z (0:Fin 1)) :=
        PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0
      simpa [Function.comp_def] using hc.comp_continuousOn hcomp
    exact hcoord'.sub continuousOn_id
  have Fneg : F (1:ℝ) ≤ 0 := by
    have hx := hm (ofR_mem (by simp : (1:ℝ) ∈ Icc (-1) 1))
    have hi := hx (0:Fin 1)
    change g (ofR 1) 0 - 1 ≤ 0
    linarith [le_trans (le_abs_self _) hi]
  have Fpos : 0 ≤ F (-1:ℝ) := by
    have hx := hm (ofR_mem (by simp : (-1:ℝ) ∈ Icc (-1) 1))
    have hi := hx (0:Fin 1)
    change 0 ≤ g (ofR (-1)) 0 - (-1)
    have hlow := (neg_le_of_abs_le hi)
    linarith
  have hzmem : (0:ℝ) ∈ Icc (F 1) (F (-1)) := ⟨Fneg, Fpos⟩
  have hz := intermediate_value_Icc' (show (-1:ℝ) ≤ 1 by norm_num) Fcont
  have hz' := hz (show (0:ℝ) ∈ Icc (F 1) (F (-1)) by exact hzmem)
  rcases hz' with ⟨t, ht, ht0⟩
  have htF : F t = 0 := ht0
  have htcoord : g (ofR t) (0:Fin 1) = t := by linarith [htF]
  refine ⟨ofR t, ofR_mem ht, ?_⟩
  -- all coordinates Fin1
  apply (EuclideanSpace.equiv (Fin 1) ℝ).injective
  funext i
  have ie : i = (0:Fin 1) := Subsingleton.elim _ _
  subst i
  -- `equiv` simply gives coordinate functions
  -- maybe instead ext
  simpa [ofR_apply] using htcoord


/-- Finite cubical labelling step. No continuity is used here: one labels a fine
rectangular grid by the signs of the coordinates of `F`. The cubical Sperner
lemma produces a cell containing, for each coordinate, both signs. In this
metric formulation `x` is one corner of that cell. This is the only discrete
(topology-free) obstruction left in the reduction. -/
lemma cubical_sign_selection {d : ℕ} (hd : 2 ≤ d)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hlo : ∀ x ∈ cube d, ∀ i : Fin d, x i = (-1:ℝ) → 0 ≤ F x i)
    (hhi : ∀ x ∈ cube d, ∀ i : Fin d, x i = (1:ℝ) → F x i ≤ 0) :
    ∀ δ : ℝ, 0 < δ → ∃ x ∈ cube d, ∀ i : Fin d,
      ∃ y ∈ cube d, ∃ z ∈ cube d,
        dist y x < δ ∧ dist z x < δ ∧ 0 ≤ F y i ∧ F z i ≤ 0 := by
  classical
  intro δ hδ
  obtain ⟨n, hn, hnsmall⟩ := exists_grid_fine d hδ
  -- This is the precise finite part which remains. Everything below just
  -- translates a small cell of the regular grid to the metric formulation.
  have cell : ∃ a : Fin d → Fin n, ∀ i : Fin d,
       (∃ s : Finset (Fin d),
          0 ≤ F (gridPoint n (GridVertex.corner a s)) i) ∧
       (∃ t : Finset (Fin d),
          F (gridPoint n (GridVertex.corner a t)) i ≤ 0) := by
    let L : (Fin d → Fin (n+1)) → Fin d → Bool := fun v i =>
      if (v i : ℕ) = 0 then true else
      if (v i : ℕ) = n then false else
        decide (0 ≤ F (gridPoint n v) i)
    have Llow (v : Fin d → Fin (n+1)) (i : Fin d)
        (h : (v i : ℕ) = 0) : L v i = true := by
      dsimp [L]
      rw [if_pos h]
    have Ltop (v : Fin d → Fin (n+1)) (i : Fin d)
        (h : (v i : ℕ) = n) : L v i = false := by
      have nz : n ≠ 0 := Nat.ne_of_gt hn
      have h0 : ¬ (v i : ℕ) = 0 := by omega
      dsimp [L]
      rw [if_neg h0, if_pos h]
    -- This statement is now wholly finite (there is no topology, or even
    -- order, in it).  It is the cubical Sperner/counting lemma.  In
    -- characteristic two it follows by summing `db₁⋯dbᵣ` over the small
    -- cubes; `Grid.paths_eq_boundary` and `Grid.paths_cocycle` record the
    -- Stokes calculation without orientations.
    have parity : ∀ (L : (Fin d → Fin (n+1)) → Fin d → Bool),
        (∀ v i, (v i : ℕ) = 0 → L v i = true) →
        (∀ v i, (v i : ℕ) = n → L v i = false) →
        ∃ a : Fin d → Fin n, ∀ i : Fin d,
          (∃ s : Finset (Fin d), L (GridVertex.corner a s) i = true) ∧
          (∃ t : Finset (Fin d), L (GridVertex.corner a t) i = false) := by
      intro L h0 h1
      exact Parity.labeled_cell hn L h0 h1
    obtain ⟨a, ha⟩ := parity L Llow Ltop
    refine ⟨a, ?_⟩
    intro i
    obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := ha i
    constructor
    · refine ⟨s, ?_⟩
      by_cases h0 : (GridVertex.corner a s i : ℕ) = 0
      · exact hlo _ (gridPoint_mem_cube' hn _) i
            (gridPoint_zero_face hn _ i h0)
      · by_cases h1 : (GridVertex.corner a s i : ℕ) = n
        · have : L (GridVertex.corner a s) i = false :=
            Ltop _ _ h1
          cases (by simpa [this] using hs : (False))
        · have h0' := h0
          have h1' := h1
          change ¬ ((a i : ℕ) + if i ∈ s then 1 else 0) = 0 at h0'
          change ¬ ((a i : ℕ) + if i ∈ s then 1 else 0) = n at h1'
          have H : decide (0 ≤ F (gridPoint n (GridVertex.corner a s)) i) = true := by
            dsimp [L] at hs
            rw [if_neg h0', if_neg h1'] at hs
            exact hs
          exact of_decide_eq_true H

    · refine ⟨t, ?_⟩
      by_cases h1 : (GridVertex.corner a t i : ℕ) = n
      · exact hhi _ (gridPoint_mem_cube' hn _) i
            (gridPoint_top_face hn _ i h1)
      · by_cases h0 : (GridVertex.corner a t i : ℕ) = 0
        · have H : L (GridVertex.corner a t) i = true := Llow _ _ h0
          cases (by simpa [H] using ht : (False))
        · have h0' := h0
          have h1' := h1
          change ¬ ((a i : ℕ) + if i ∈ t then 1 else 0) = 0 at h0'
          change ¬ ((a i : ℕ) + if i ∈ t then 1 else 0) = n at h1'
          have H : decide (0 ≤ F (gridPoint n (GridVertex.corner a t)) i) = false := by
            dsimp [L] at ht
            rw [if_neg h0', if_neg h1'] at ht
            exact ht
          have H' : ¬ 0 ≤ F (gridPoint n (GridVertex.corner a t)) i :=
            decide_eq_false_iff_not.mp H
          exact le_of_lt (lt_of_not_ge H')

  obtain ⟨a, ha⟩ := cell
  let X := gridPoint n (GridVertex.corner a (∅ : Finset (Fin d)))
  have mem_corner (s : Finset (Fin d)) :
      gridPoint n (GridVertex.corner a s) ∈ cube d := by
    exact gridPoint_mem_cube' hn _
  have hx : X ∈ cube d := mem_corner ∅
  refine ⟨X, hx, ?_⟩
  intro i
  obtain ⟨⟨s,hs⟩,⟨t,ht⟩⟩ := ha i
  refine ⟨gridPoint n (GridVertex.corner a s), mem_corner s,
          gridPoint n (GridVertex.corner a t), mem_corner t, ?_, ?_, hs, ht⟩
  · exact lt_trans (GridVertex.dist_corners_lt hn a s ∅) hnsmall
  · exact lt_trans (GridVertex.dist_corners_lt hn a t ∅) hnsmall

/-- Sign version of the remaining cubical step (Poincare--Miranda).  Unlike
all projection and compactness lemmas, this is a purely finite-dimensional
cube statement: in a combinatorial proof it is exactly the consequence of
the labelled-grid/Sperner lemma. Restricting to `2 ≤ d` keeps the intermediate
value and empty cases separate. -/
lemma poincare_miranda_cube_approx {d : ℕ} (hd : 2 ≤ d)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hF : ContinuousOn F (cube d))
    (hlo : ∀ x ∈ cube d, ∀ i : Fin d, x i = (-1:ℝ) → 0 ≤ F x i)
    (hhi : ∀ x ∈ cube d, ∀ i : Fin d, x i = (1:ℝ) → F x i ≤ 0) :
    ∀ ε : ℝ, 0 < ε → ∃ x ∈ cube d, ‖F x‖ < ε := by
  intro ε hε
  let e : ℝ := ε / ((d:ℝ) + 1)
  have he : 0 < e := div_pos hε (by exact_mod_cast (Nat.zero_lt_succ d))
  have hu := IsCompact.uniformContinuousOn_of_continuous (isCompact_cube d) hF
  obtain ⟨δ,hδ,hun⟩ :=
    (Metric.uniformContinuousOn_iff.mp hu) e he
  obtain ⟨x,hx,hxs⟩ := cubical_sign_selection hd F hlo hhi δ hδ
  have hcoord : ∀ i : Fin d, |F x i| ≤ e := by
    intro i
    obtain ⟨y,hy,z,hz,hyx,hzx,hy0,hz0⟩ := hxs i
    have hdy : dist (F y) (F x) < e := hun y hy x hx hyx
    have hdz : dist (F z) (F x) < e := hun z hz x hx hzx
    have hay : |F y i - F x i| ≤ dist (F y) (F x) := by
      have hh := PiLp.norm_apply_le (F y - F x) i
      rw [Real.norm_eq_abs] at hh
      simpa [dist_eq_norm] using hh
    have haz : |F z i - F x i| ≤ dist (F z) (F x) := by
      have hh := PiLp.norm_apply_le (F z - F x) i
      rw [Real.norm_eq_abs] at hh
      simpa [dist_eq_norm] using hh
    have hyb : |F y i - F x i| < e := lt_of_le_of_lt hay hdy
    have hzb : |F z i - F x i| < e := lt_of_le_of_lt haz hdz
    have lowabs := (abs_lt.mp hyb)
    have upabs := (abs_lt.mp hzb)
    apply (abs_le).2
    constructor <;> linarith
  refine ⟨x,hx,?_⟩
  have hsum : (∑ i : Fin d, (F x i)^2) ≤ (d:ℝ) * e^2 := by
    calc
      (∑ i : Fin d, (F x i)^2) ≤ ∑ _i : Fin d, e^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := (sq_le_sq₀ (abs_nonneg (F x i)) (le_of_lt he)).2 (hcoord i)
        simpa [sq_abs] using hh
      _ = (d:ℝ) * e^2 := by simp
  have hnormsq : ‖F x‖^2 ≤ (d:ℝ) * e^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact hsum
  have hd0 : (0:ℝ) ≤ d := by exact_mod_cast (Nat.zero_le d)
  have hdplus : 0 < (d:ℝ)+1 := by exact_mod_cast (Nat.zero_lt_succ d)
  have hn0 : 0 ≤ ‖F x‖ := norm_nonneg _
  dsimp [e] at hnormsq ⊢
  have key : (d:ℝ) < ((d:ℝ)+1)^2 := by nlinarith
  have heps : 0 < ε := hε
  calc
    ‖F x‖ < ε := by
      -- clear the positive denominator in the estimate
      have : (d:ℝ) * (ε / ((d:ℝ)+1))^2 < ε^2 := by
        field_simp
        nlinarith
      nlinarith


/-- Cubical, approximate core of the fixed point theorem.  Isolating this form
lets all limit, projection and scaling issues be handled independently of the
(eventually Sperner) finite-dimensional combinatorics. -/
lemma cube_approx_fixed {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hg : ContinuousOn g (cube d)) (hm : MapsTo g (cube d) (cube d)) :
    ∀ ε : ℝ, 0 < ε → ∃ x ∈ cube d, ‖g x - x‖ < ε := by
  classical
  by_cases h0 : d = 0
  · subst d
    intro ε hε
    let x : EuclideanSpace ℝ (Fin 0) := 0
    have hx : x ∈ cube 0 := by
      intro i
      exact Fin.elim0 i
    have hzx : g x = x := Subsingleton.elim _ _
    exact ⟨x, hx, by simp [hzx, hε]⟩
  by_cases h1 : d = 1
  · subst d
    obtain ⟨x,hx,hfix⟩ := cube_fixed_one g hg hm
    intro ε hε
    exact ⟨x,hx, by simp [hfix, hε]⟩
  · have hd : 2 ≤ d := by omega
    let F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
      fun x => g x - x
    have hF : ContinuousOn F (cube d) := by
      exact hg.sub continuousOn_id
    have hlo : ∀ x ∈ cube d, ∀ i : Fin d, x i = (-1:ℝ) → 0 ≤ F x i := by
      intro x hx i hi
      have hgx := hm hx
      have hab : |g x i| ≤ (1:ℝ) := hgx i
      have low : (-1:ℝ) ≤ g x i := neg_le_of_abs_le hab
      change 0 ≤ g x i - x i
      linarith
    have hhi : ∀ x ∈ cube d, ∀ i : Fin d, x i = (1:ℝ) → F x i ≤ 0 := by
      intro x hx i hi
      have hgx := hm hx
      have hab : |g x i| ≤ (1:ℝ) := hgx i
      have up : g x i ≤ (1:ℝ) := le_trans (le_abs_self _) hab
      change g x i - x i ≤ 0
      linarith
    intro ε hε
    obtain ⟨x,hx,hxe⟩ := poincare_miranda_cube_approx hd F hF hlo hhi ε hε
    exact ⟨x,hx,hxe⟩

lemma cube_fixed {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hg : ContinuousOn g (cube d)) (hm : MapsTo g (cube d) (cube d)) :
    ∃ x ∈ cube d, g x = x :=
  fixed_of_approx (isCompact_cube d) (cube_nonempty d) g hg
    (cube_approx_fixed g hg hm)

end BrouwerSupport

end
-- END INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/Cube.lean

-- BEGIN INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/Ball.lean
section

open Set Topology
open scoped Real

namespace BrouwerSupport

local notation "B₁[" d "]" =>
  (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (1:ℝ))
local notation "B_[" d "," R "]" =>
  (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R)

/-- The genuinely Brouwer (combinatorial/topological) part isolated in an
approximate form. Everything else in the reduction only uses compactness and
convex Hilbert projection. Future proofs may furnish this lemma by Sperner or
by a no-retraction theorem. -/
lemma unitBall_approx_fixed {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hg : ContinuousOn g B₁[d]) (hm : MapsTo g B₁[d] B₁[d]) :
    ∀ ε : ℝ, 0 < ε → ∃ x ∈ B₁[d], ‖g x - x‖ < ε := by
  classical
  let C : Set (EuclideanSpace ℝ (Fin d)) := B₁[d]
  have hne : C.Nonempty := ⟨0, by simp [C]⟩
  have hco : IsComplete C :=
    (Metric.isClosed_closedBall : IsClosed C).isComplete
  have hcv : Convex ℝ C := convex_closedBall _ _
  let P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    convexProj C hne hco hcv
  have hPmem (x : EuclideanSpace ℝ (Fin d)) : P x ∈ C :=
    convexProj_mem C hne hco hcv x
  have hPc : Continuous P := continuous_convexProj C hne hco hcv
  have hPs {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ C) : P x = x :=
    convexProj_eq_self C hne hco hcv hx
  let k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun x => g (P x)
  have kc : Continuous k := by
    have h := hg.comp_continuous hPc (fun x => hPmem x)
    simpa [k, C, Function.comp_def] using h
  have km : MapsTo k (cube d) (cube d) := by
    intro x hx
    apply unitBall_subset_cube d
    change g (P x) ∈ B₁[d]
    exact hm (hPmem x)
  obtain ⟨x, hxq, hxfix⟩ :=
    cube_fixed k kc.continuousOn km
  have hxC : x ∈ C := by
    have hxv : k x ∈ C := by
      change g (P x) ∈ B₁[d]
      exact hm (hPmem x)
    simpa [hxfix] using hxv
  have hfixg : g x = x := by
    simpa [k, hPs hxC] using hxfix
  intro ε hε
  refine ⟨x, hxC, ?_⟩
  simp [hfixg, hε]

/-- Exact closed-unit-ball version; the passage from approximate to exact is
an independent compactness argument. -/
lemma unitBall_fixed {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hg : ContinuousOn g B₁[d]) (hm : MapsTo g B₁[d] B₁[d]) :
    ∃ x ∈ B₁[d], g x = x := by
  have hc : IsCompact B₁[d] := ProperSpace.isCompact_closedBall _ _
  have hn : (B₁[d]).Nonempty := ⟨0, by simp⟩
  exact fixed_of_approx hc hn g hg (unitBall_approx_fixed g hg hm)

/-- Scaling transports the closed-ball result to every positive radius.  It is
useful to state this separately: reductions for a compact set naturally
produce a possibly large enclosing ball. -/
lemma closedBall_fixed_of_pos {d : ℕ} {R : ℝ} (hR : 0 < R)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hg : ContinuousOn g B_[d,R]) (hm : MapsTo g B_[d,R] B_[d,R]) :
    ∃ x ∈ B_[d,R], g x = x := by
  let S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => R • x
  let T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => (R⁻¹) • x
  have hs : Continuous S := by
    dsimp [S]
    fun_prop
  have ht : Continuous T := by
    dsimp [T]
    fun_prop
  have hto : MapsTo S B₁[d] B_[d,R] := by
    intro x hx
    have hxnorm : ‖x‖ ≤ (1:ℝ) := by
      simpa [Metric.mem_closedBall] using hx
    have hynorm : ‖S x‖ ≤ R := by
      dsimp [S]
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt hR)]
      nlinarith
    simpa [Metric.mem_closedBall] using hynorm
  let h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun x => T (g (S x))
  have hmaps : MapsTo h B₁[d] B₁[d] := by
    intro x hx
    have hgg : g (S x) ∈ B_[d,R] := hm (hto hx)
    have hgg' : ‖g (S x)‖ ≤ R := by
      simpa [Metric.mem_closedBall] using hgg
    have hh' : ‖h x‖ ≤ (1:ℝ) := by
      dsimp [h, T]
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hR))]
      calc
        R⁻¹ * ‖g (S x)‖ ≤ R⁻¹ * R :=
          mul_le_mul_of_nonneg_left hgg' (le_of_lt (inv_pos.mpr hR))
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hR)
    simpa [Metric.mem_closedBall] using hh'
  have hcont : ContinuousOn h B₁[d] := by
    have ccomp : ContinuousOn (g ∘ S) B₁[d] := hg.comp hs.continuousOn hto
    have cc := ccomp.const_smul (R⁻¹)
    -- the preceding composite followed by scalar multiplication is precisely `h`
    simpa [h, T, Function.comp_def] using cc
  obtain ⟨x, hx, hxfix⟩ := unitBall_fixed h hcont hmaps
  refine ⟨S x, hto hx, ?_⟩
  -- undo the rescaling equation
  have hx' := congrArg (fun z : EuclideanSpace ℝ (Fin d) => R • z) hxfix
  dsimp [h, T] at hx'
  have hmul : R * R⁻¹ = (1:ℝ) := mul_inv_cancel₀ (ne_of_gt hR)
  simpa [S, smul_smul, hmul] using hx'

end BrouwerSupport

end
-- END INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/Ball.lean

-- BEGIN INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/Reduce.lean
section

open Set Topology

namespace BrouwerSupport

/-- Reduction from a compact nonempty convex set to a closed ball.  It is a
useful precise substitute for the often-quoted but surprisingly awkward
"homeomorphic to a ball" reduction: nearest-point projection is continuous,
fixes the set, and lets a fixed point in a large ambient ball land back in the
set automatically. -/
theorem fixed_compactConvex_of_ball {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hKc : IsCompact K) (hKv : Convex ℝ K) (hKn : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f K) (hfm : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  let E := EuclideanSpace ℝ (Fin d)
  have hclosed : IsClosed K := hKc.isClosed
  have hcomplete : IsComplete K := hclosed.isComplete
  let P : E → E := convexProj K hKn hcomplete hKv
  have hPmem : ∀ x, P x ∈ K := by
    intro x
    exact convexProj_mem K hKn hcomplete hKv x
  have hPcont : Continuous P := continuous_convexProj K hKn hcomplete hKv
  have hPself {x : E} (hx : x ∈ K) : P x = x :=
    convexProj_eq_self K hKn hcomplete hKv hx

  -- Enclose the compact set in a ball with positive radius.
  obtain ⟨r, hr⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : E)).1 hKc.isBounded
  let R : ℝ := max r 1
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hsub : K ⊆ Metric.closedBall (0 : E) R := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : E) r := hr hx
    have hn : ‖x‖ ≤ r := by
      simpa [Metric.mem_closedBall] using hx'
    have hn' : ‖x‖ ≤ R := le_trans hn (le_max_left _ _)
    simpa [Metric.mem_closedBall] using hn'
  -- First project onto `K`, then apply `f`.  This is a continuous map on the
  -- *ambient* space although `f` was only assumed continuous on `K`.
  let g : E → E := fun x => f (P x)
  have gc : Continuous g := by
    have h := hf.comp_continuous hPcont hPmem
    simpa [g, Function.comp_def] using h
  have gm : MapsTo g (Metric.closedBall (0 : E) R)
                      (Metric.closedBall (0 : E) R) := by
    intro x hx
    apply hsub
    exact hfm (hPmem x)
  obtain ⟨x,hxb,hfix⟩ :=
    closedBall_fixed_of_pos (d:=d) hR g gc.continuousOn gm
  have hxK : x ∈ K := by
    -- the value of `g` lies in `K`; at a fixed point so does `x`
    have hxv : g x ∈ K := hfm (hPmem x)
    simpa [hfix] using hxv
  refine ⟨x, hxK, ?_⟩
  simpa [g, hPself hxK] using hfix

end BrouwerSupport

end
-- END INLINED FILE: Mathlib/Support/brouwer_fixed_point_01f7e049e5/Reduce.lean

-- BEGIN INLINED MAIN PRELUDE

open Set
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem brouwer_fixed_point {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (_hK_compact : IsCompact K) (_hK_convex : Convex ℝ K)
    (_hK_nonempty : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (_hf_cont : ContinuousOn f K) (_hf_maps : MapsTo f K K) :
    ∃ x ∈ K, f x = x :=
/-ResultProofBegin-/by
  exact BrouwerSupport.fixed_compactConvex_of_ball _hK_compact _hK_convex
    _hK_nonempty f _hf_cont _hf_maps
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
