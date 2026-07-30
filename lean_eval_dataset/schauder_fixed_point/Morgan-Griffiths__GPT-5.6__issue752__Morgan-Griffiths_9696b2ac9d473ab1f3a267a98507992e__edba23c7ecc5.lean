import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/schauder_fixed_point_390f5406f7/CubeParity.lean
open scoped BigOperators
open Finset Function
namespace CubeParity
variable {D : Type*} [DecidableEq D]

lemma pair_sum_zero (S : Finset D) (A : D → D → ZMod 2)
    (hs : ∀ d ∈ S, ∀ e ∈ S, d ≠ e → A d e = A e d) :
    (∑ d ∈ S, ∑ e ∈ S.erase d, A d e) = 0 := by
  classical
  -- strong induction on finset
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have hsym : ∀ d ∈ t, ∀ e ∈ t, d ≠ e → A d e = A e d := by
      intro d hd e he hne
      exact hs d (by simp [hd]) e (by simp [he]) hne
    have hi := ih hsym
    -- expand sums
    -- outer a term and t terms; split inner erase
    rw [Finset.sum_insert ha]
    have herasea : (insert a t).erase a = t := by simp [ha]
    rw [herasea]
    -- split remaining outer t terms
    -- each (insert a t).erase d = insert a (t.erase d)
    have hform (d : D) (hd : d ∈ t) : (insert a t).erase d = insert a (t.erase d) := by
      ext z
      by_cases hzd : z = d
      · subst z; have hda : d ≠ a := by intro h; subst d; exact ha hd
        simp [hd, hda]
      · by_cases hza : z = a
        · subst z; simp [ha, hd, hzd]
        · simp [hzd, hza]
    have hnot (d : D) (hd : d ∈ t) : a ∉ t.erase d := by simp [ha]
    -- rewrite sums over t
    calc
      (∑ e ∈ t, A a e) + ∑ d ∈ t, ∑ e ∈ (insert a t).erase d, A d e
          = (∑ e ∈ t, A a e) + ∑ d ∈ t, (A d a + ∑ e ∈ t.erase d, A d e) := by
              congr 1
              apply Finset.sum_congr rfl
              intro d hd
              rw [hform d hd, Finset.sum_insert (hnot d hd)]
      _ = (∑ e ∈ t, A a e) + (∑ d ∈ t, A d a) +
            (∑ d ∈ t, ∑ e ∈ t.erase d, A d e) := by
              rw [Finset.sum_add_distrib]
              ac_rfl
      _ = 0 := by
              rw [hi]
              simp
              have hcross : (∑ d ∈ t, A d a) = (∑ d ∈ t, A a d) := by
                apply Finset.sum_congr rfl
                intro d hd
                exact hs d (by simp [hd]) a (by simp) (by intro h; subst d; exact ha hd)
              -- fix symmetry orientation
              rw [hcross]
              exact CharTwo.add_self_eq_zero _
end CubeParity

namespace CubeParity
variable {D : Type*} [DecidableEq D]
abbrev Vertex (D : Type*) := D → ℕ

def inc (a : Vertex D) (d : D) (b : Fin 2) : Vertex D :=
  Function.update a d (a d + (b:ℕ))

@[simp] lemma inc_zero (a : Vertex D) (d : D) : inc a d (0 : Fin 2) = a := by
  funext i; by_cases h:i=d <;> simp [inc, h]
lemma inc_comm (a : Vertex D) {d e : D} (h : d ≠ e) (b c : Fin 2) :
    inc (inc a d b) e c = inc (inc a e c) d b := by
  funext i
  by_cases hi : i = d
  · subst i; simp [inc, h]
  · by_cases hj : i = e
    · subst i; simp [inc, h, hi]
    · simp [inc, hi, hj]

-- cubical coboundary on all lower corners
def bdry (C : Finset D → Vertex D → ZMod 2) (S : Finset D) (a : Vertex D) : ZMod 2 :=
  ∑ d ∈ S, ∑ b : Fin 2, C (S.erase d) (inc a d b)

lemma bdry_bdry (C : Finset D → Vertex D → ZMod 2) (S : Finset D) (a : Vertex D) :
    bdry (fun T x => bdry C T x) S a = 0 := by
  classical
  let A : D → D → ZMod 2 := fun d e =>
    ∑ b : Fin 2, ∑ c : Fin 2,
      C ((S.erase d).erase e) (inc (inc a d b) e c)
  have hsym : ∀ d ∈ S, ∀ e ∈ S, d ≠ e → A d e = A e d := by
    intro d hd e he hne
    dsimp [A]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    have her : (S.erase d).erase e = (S.erase e).erase d := by
      ext z; simp [and_left_comm, and_comm, and_assoc]
    rw [her]
    rw [inc_comm a hne]
  have hp := pair_sum_zero S A hsym
  rw [← hp]
  unfold bdry
  -- commute middle b/e sums
  apply Finset.sum_congr rfl
  intro d hd
  -- for a fixed d
  dsimp [A]
  rw [Finset.sum_comm]
end CubeParity

namespace CubeParity
variable {D : Type*} [DecidableEq D]

def Q : List (Vertex D → ZMod 2) → Finset D → Vertex D → ZMod 2
| [], _, _ => 1
| f :: fs, S, a => bdry (fun T x => f x * Q fs T x) S a

lemma Q_cons (f : Vertex D → ZMod 2) (fs : List (Vertex D → ZMod 2)) (S : Finset D) (a : Vertex D) :
   Q (f::fs) S a = bdry (fun T x => f x * Q fs T x) S a := rfl

lemma bdry_const_one (S : Finset D) (a : Vertex D) :
    bdry (fun _ _ => (1 : ZMod 2)) S a = 0 := by
  classical
  unfold bdry
  apply Finset.sum_eq_zero
  intro d hd
  exact (by decide : (∑ _ : Fin 2, (1 : ZMod 2)) = 0)


lemma Q_closed (fs : List (Vertex D → ZMod 2)) (S : Finset D) (a : Vertex D) :
    bdry (Q fs) S a = 0 := by
  cases fs with
  | nil => exact bdry_const_one S a
  | cons f fs =>
    change bdry (fun T x => bdry (fun T x => f x * Q fs T x) T x) S a = 0
    exact bdry_bdry _ _ _

-- if one label is constant on all vertices of the cube, Q vanishes
-- vertex condition expressed as invariance on all face lower corners appearing
lemma Q_zero_of_head_const (f : Vertex D → ZMod 2) (fs : List (Vertex D → ZMod 2))
    (S : Finset D) (a : Vertex D) (c : ZMod 2)
    (h : ∀ d ∈ S, ∀ b : Fin 2, f (inc a d b) = c) :
    Q (f::fs) S a = 0 := by
  classical
  rw [Q_cons]
  unfold bdry
  have hre : (∑ d ∈ S, ∑ b : Fin 2, f (inc a d b) * Q fs (S.erase d) (inc a d b)) =
      ∑ d ∈ S, ∑ b : Fin 2, c * Q fs (S.erase d) (inc a d b) := by
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro b hb
    rw [h d hd b]
  rw [hre]
  simp_rw [← Finset.mul_sum]
  have hc := Q_closed fs S a
  unfold bdry at hc
  rw [hc]
  simp
end CubeParity
namespace CubeParity
variable {D : Type*} [DecidableEq D]

def IsConstOnCube (f : Vertex D → ZMod 2) (S : Finset D) (a : Vertex D)
    (c : ZMod 2) : Prop :=
  ∀ x : Vertex D, (∀ i, a i ≤ x i ∧ x i ≤ a i + (if i ∈ S then 1 else 0)) → f x = c

lemma isConst_face {f : Vertex D → ZMod 2} {S : Finset D} {a : Vertex D} {c : ZMod 2}
    (h : IsConstOnCube f S a c) {d : D} (hd : d ∈ S) (b : Fin 2) :
    IsConstOnCube f (S.erase d) (inc a d b) c := by
  intro x hx
  apply h x
  intro i
  by_cases hi : i = d
  · subst i
    have hx' := hx d
    simp [inc] at hx'
    constructor
    · omega
    · have hb : (b:ℕ) ≤ 1 := by omega
      have hx2 := hx'.2
      have : x d ≤ a d + 1 := by omega
      simpa [hd] using this
  · have hx' := hx i
    have hn : i ∈ S.erase d ↔ i ∈ S := by simp [hi]
    simpa [inc, hi, hn] using hx'

lemma inc_in_cube (S : Finset D) (a : Vertex D) {d : D} (hd : d ∈ S) (b : Fin 2) :
    (∀ i, a i ≤ inc a d b i ∧ inc a d b i ≤ a i + (if i ∈ S then 1 else 0)) := by
 intro i
 by_cases hi : i = d
 · subst i
   simp [inc, hd]
   omega
 · simp [inc, hi]

-- if any label in the list is constant on the cube, the value vanishes (for matching degree)
lemma Q_zero_of_const (ls : List (Vertex D → ZMod 2)) (S : Finset D) (a : Vertex D)
    (hcard : S.card = ls.length) :
    (∃ f ∈ ls, ∃ c, IsConstOnCube f S a c) → Q ls S a = 0 := by
  classical
  induction ls generalizing S a with
  | nil => simp
  | cons f fs ih =>
    intro hex
    rcases hex with ⟨g, hg, c, hc⟩
    by_cases heq : g = f
    · subst g
      apply Q_zero_of_head_const f fs S a c
      intro d hd b
      exact hc _ (inc_in_cube S a hd b)
    · have htail : g ∈ fs := (List.mem_cons.mp hg).resolve_left heq
      rw [Q_cons]
      unfold bdry
      apply Finset.sum_eq_zero
      intro d hd
      apply Finset.sum_eq_zero
      intro b hb
      have hcface := isConst_face hc hd b
      have hcard' : (S.erase d).card = fs.length := by
        rw [Finset.card_erase_of_mem hd] at *
        simp at hcard ⊢
        omega
      change f (inc a d b) * Q fs (S.erase d) (inc a d b) = 0
      rw [ih (S.erase d) (inc a d b) hcard' ⟨g, htail, c, hcface⟩]
      simp
end CubeParity
namespace CubeParity
-- elementary telescoping in characteristic two; this is the cancellation of
-- the two copies of every interior face of a row of small cubes.
lemma sum_range_add_next (q : ℕ) (φ : ℕ → ZMod 2) :
    (∑ k ∈ Finset.range q, (φ k + φ (k+1))) = φ 0 + φ q := by
  induction q with
  | zero =>
    simp [CharTwo.add_self_eq_zero]
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    -- cancel the middle endpoint
    have hh : φ q + φ q = 0 := CharTwo.add_self_eq_zero _
    -- commutative additive group
    calc
      φ 0 + φ q + (φ q + φ (q + 1)) = φ 0 + (φ q + φ q) + φ (q+1) := by ac_rfl
      _ = _ := by rw [hh]; simp
end CubeParity
namespace CubeParity
variable {D : Type*} [DecidableEq D]
lemma exists_two_vertices_of_Q_ne_zero (ls : List (Vertex D → ZMod 2)) (S : Finset D)
    (a : Vertex D) (hcard : S.card = ls.length) (hQ : Q ls S a ≠ 0)
    {f : Vertex D → ZMod 2} (hf : f ∈ ls) :
    (∃ u : Vertex D, (∀ i, a i ≤ u i ∧ u i ≤ a i + (if i ∈ S then 1 else 0)) ∧ f u = 0) ∧
    (∃ v : Vertex D, (∀ i, a i ≤ v i ∧ v i ≤ a i + (if i ∈ S then 1 else 0)) ∧ f v = 1) := by
  classical
  have hnoconst (c : ZMod 2) : ¬ IsConstOnCube f S a c := by
    intro hc
    exact hQ (Q_zero_of_const ls S a hcard ⟨f, hf, c, hc⟩)
  have hex (c : ZMod 2) : ∃ u : Vertex D,
      (∀ i, a i ≤ u i ∧ u i ≤ a i + (if i ∈ S then 1 else 0)) ∧ f u ≠ c := by
    simpa [IsConstOnCube] using (hnoconst c)
  rcases hex 1 with ⟨u, hu, hu'⟩
  rcases hex 0 with ⟨v, hv, hv'⟩
  -- there are exactly two elements in the coefficient ring
  have alltwo (x : ZMod 2) : x = 0 ∨ x = 1 := by decide +revert
  have hu0 : f u = (0 : ZMod 2) := (alltwo _).resolve_right hu'
  have hv1 : f v = (1 : ZMod 2) := (alltwo _).resolve_left hv' 
  exact ⟨⟨u, hu, hu0⟩, ⟨v, hv, hv1⟩⟩
end CubeParity

-- END INLINED FILE: Mathlib/Support/schauder_fixed_point_390f5406f7/CubeParity.lean

-- BEGIN INLINED FILE: Mathlib/Support/schauder_fixed_point_390f5406f7/GridParity.lean
open scoped BigOperators
open Finset Function
namespace GridParity
open CubeParity
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- lower corner obtained by letting only coordinates in `S` vary. -/
def corner (m : ℕ) (S : Finset D) (base : Vertex D)
    (g : ({i // i ∈ S}) → Fin m) : Vertex D :=
  fun i => if hi : i ∈ S then (g ⟨i,hi⟩ : ℕ) else base i

@[simp] lemma corner_mem (m : ℕ) (S : Finset D) (base : Vertex D)
    (g : ({i // i ∈ S}) → Fin m) {i : D} (hi : i ∈ S) :
    corner m S base g i = (g ⟨i,hi⟩ : ℕ) := by
  simp [corner, hi]
@[simp] lemma corner_notmem (m : ℕ) (S : Finset D) (base : Vertex D)
    (g : ({i // i ∈ S}) → Fin m) {i : D} (hi : i ∉ S) :
    corner m S base g i = base i := by simp [corner, hi]

/-- split an assignment along a singled out member. -/
def splitAssign (m : ℕ) (S : Finset D) (d : D) (hd : d ∈ S) :
    (({i // i ∈ S}) → Fin m) ≃ (Fin m × (({i // i ∈ S.erase d}) → Fin m)) where
  toFun g :=
    (g ⟨d, hd⟩, fun i => g ⟨i.1, (Finset.mem_of_mem_erase i.2)⟩)
  invFun p := fun i =>
    if h : i.1 = d then p.1 else
      p.2 ⟨i.1, (Finset.mem_erase).2 ⟨h, i.2⟩⟩
  left_inv g := by
    funext i
    by_cases h : i.1 = d
    · change (dite (i.1 = d) (fun _ => _) (fun _ => _)) = _
      simp [h]
      congr 1
      apply Subtype.ext
      exact h.symm
    · change (dite (i.1 = d) (fun _ => _) (fun _ => _)) = _
      simp [h]
  right_inv p := by
    rcases p with ⟨t,h⟩
    apply Prod.ext
    · simp
    · funext i
      have hi : i.val ≠ d := (Finset.mem_erase.mp i.property).1
      simp [hi]

lemma splitAssign_inv_val (m : ℕ) (S : Finset D) (base : Vertex D) (d : D) (hd : d ∈ S)
    (p : Fin m × (({i // i ∈ S.erase d}) → Fin m)) (i : D) :
    corner m S base ((splitAssign m S d hd).symm p) i =
      if h : i = d then (p.1 : ℕ) else
        if hi : i ∈ S.erase d then (p.2 ⟨i,hi⟩ : ℕ) else base i := by
  classical
  by_cases h : i = d
  · subst i
    simp [corner, splitAssign, hd]
  · by_cases hiS : i ∈ S
    · have hier : i ∈ S.erase d := (Finset.mem_erase).2 ⟨h, hiS⟩
      simp [corner, splitAssign, hiS, h, hier]
    · have hier : i ∉ S.erase d := by simpa using fun hh : i ∈ S.erase d => hiS (Finset.mem_of_mem_erase hh)
      simp [corner, splitAssign, hiS, h, hier]

/-- moving the distinguished coordinate in a corner. -/
lemma inc_corner_split (m : ℕ) (S : Finset D) (base : Vertex D) (d : D) (hd : d ∈ S)
    (p : Fin m × (({i // i ∈ S.erase d}) → Fin m)) (b : Fin 2) :
    CubeParity.inc (corner m S base ((splitAssign m S d hd).symm p)) d b =
      corner m (S.erase d) (Function.update base d ((p.1:ℕ) + (b:ℕ))) p.2 := by
  classical
  funext i
  by_cases h : i = d
  · subst i
    simp [CubeParity.inc, corner, splitAssign, hd, Function.update]
  · have hc := splitAssign_inv_val m S base d hd p i
    simp [h] at hc
    by_cases hi : i ∈ S.erase d
    · have hiS : i ∈ S := Finset.mem_of_mem_erase hi
      -- neither update nor increment modifies this coordinate
      simpa [CubeParity.inc, Function.update, h, corner, hiS, hi] using hc
    · have hiS : i ∉ S := by
        intro hz; exact hi ((Finset.mem_erase).2 ⟨h, hz⟩)
      simpa [CubeParity.inc, Function.update, h, corner, hiS, hi] using hc

/-- telescope the rows of small cubes in one coordinate. -/
lemma face_telescope (m : ℕ) (S : Finset D) (base : Vertex D)
    (d : D) (hd : d ∈ S) (A : Vertex D → ZMod 2) :
    (∑ g : (({i // i ∈ S}) → Fin m),
       ∑ b : Fin 2, A (CubeParity.inc (corner m S base g) d b))
      =
    ∑ h : (({i // i ∈ S.erase d}) → Fin m),
      (A (corner m (S.erase d) (Function.update base d 0) h) +
       A (corner m (S.erase d) (Function.update base d m) h)) := by
  classical
  -- split off the value at d
  rw [Fintype.sum_equiv (splitAssign m S d hd)
    (fun g : (({i // i ∈ S}) → Fin m) => ∑ b : Fin 2, A (CubeParity.inc (corner m S base g) d b))
    (fun p : (Fin m × (({i // i ∈ S.erase d}) → Fin m)) =>
      ∑ b : Fin 2, A (CubeParity.inc (corner m S base ((splitAssign m S d hd).symm p)) d b))
    (by intro x; rw [(splitAssign m S d hd).symm_apply_apply x]) ]
  rw [Fintype.sum_prod_type]
  -- commute the value and the remaining assignment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  -- now one-dimensional telescoping
  -- express as natural range using Fin
  -- convert inner Fin2 sum into two endpoints
  -- use the elementary characteristic-two telescoping lemma
  have ht := CubeParity.sum_range_add_next m
    (fun k : ℕ => A (corner m (S.erase d) (Function.update base d k) h))
  -- make each summand match
  calc
    (∑ i : Fin m,
        (∑ b : Fin 2, A (CubeParity.inc
          (corner m S base ((splitAssign m S d hd).symm (i,h))) d b)))
        = ∑ i : Fin m,
            (A (corner m (S.erase d) (Function.update base d (i:ℕ)) h) +
             A (corner m (S.erase d) (Function.update base d ((i:ℕ)+1)) h)) := by
                apply Finset.sum_congr rfl
                intro i hi
                -- the two points of a row are its consecutive endpoints
                rw [Fin.sum_univ_two]
                simp [inc_corner_split m S base d hd (i,h)]
                -- maybe simp handles plus zero
    _ = ∑ k ∈ Finset.range m,
            (A (corner m (S.erase d) (Function.update base d k) h) +
             A (corner m (S.erase d) (Function.update base d (k+1)) h)) := by
               rw [← Fin.sum_univ_eq_sum_range
                 (fun k : ℕ =>
                   (A (corner m (S.erase d) (Function.update base d k) h) +
                    A (corner m (S.erase d) (Function.update base d (k+1)) h))) m]
    _ = _ := ht
end GridParity

namespace GridParity
open CubeParity
open Finset Function
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The total (mod two) index of the small cubes in a box.  The list orders the
active coordinate directions.  The functions labelling a direction are zero on
its bottom face and one on its top face, with no hypotheses in the interior. -/
theorem total_Q (m : ℕ) (f : D → Vertex D → ZMod 2)
    (hz : ∀ d x, x d = 0 → f d x = 0)
    (ho : ∀ d x, x d = m → f d x = 1)
    (ds : List D) (hds : ds.Nodup) (base : Vertex D) :
    (∑ g : (({i // i ∈ ds.toFinset}) → Fin m),
      Q (ds.map f) ds.toFinset (corner m ds.toFinset base g)) = 1 := by
  classical
  induction ds generalizing base with
  | nil =>
      -- one zero-dimensional cube
      simp [CubeParity.Q]
  | cons i xs ih =>
    have hix : i ∉ xs := (List.nodup_cons.mp hds).1
    have hnod : xs.Nodup := (List.nodup_cons.mp hds).2
    have hift : i ∉ xs.toFinset := by simpa using hix
    let S : Finset D := (i :: xs).toFinset
    let T : Finset D := xs.toFinset
    have hiS : i ∈ S := by simp [S]
    have heri : S.erase i = T := by
      simp [S, T, hift]
    -- expand the first boundary and commute the direction with the small corners
    change (∑ g : (({d // d ∈ S}) → Fin m),
      ∑ d ∈ S, ∑ b : Fin 2,
        f i (CubeParity.inc (corner m S base g) d b) *
          Q (xs.map f) (S.erase d) (CubeParity.inc (corner m S base g) d b)) = 1
    -- move the sum indexed by d outwards
    rw [Finset.sum_comm]
    -- it is enough to compute each direction
    have hother : ∀ d ∈ S, d ≠ i →
        (∑ g : (({z // z ∈ S}) → Fin m),
           ∑ b : Fin 2,
             f i (CubeParity.inc (corner m S base g) d b) *
               Q (xs.map f) (S.erase d) (CubeParity.inc (corner m S base g) d b)) = 0 := by
      intro d hd hne
      have hdT : d ∈ T := by
        have : d = i ∨ d ∈ xs.toFinset := by simpa [S, T] using hd
        exact this.resolve_left hne
      have hdlist : d ∈ xs := by simpa [T] using hdT
      have hmem : f d ∈ xs.map f := List.mem_map.mpr ⟨d, hdlist, rfl⟩
      have hcard : (S.erase d).card = (xs.map f).length := by
        rw [Finset.card_erase_of_mem hd]
        have hcS : S.card = xs.toFinset.card + 1 := by
          simp [S, hift]
        simpa [hcS] using (List.toFinset_card_of_nodup hnod)
      -- telescope this row in the direction d
      rw [face_telescope m S base d hd
        (fun x => f i x * Q (xs.map f) (S.erase d) x)]
      apply Finset.sum_eq_zero
      intro h hh
      have hde : d ∉ S.erase d := by simp
      have hx0 : corner m (S.erase d) (Function.update base d 0) h d = 0 := by
        simp [corner, hde, Function.update]
      have hxm : corner m (S.erase d) (Function.update base d m) h d = m := by
        simp [corner, hde, Function.update]
      have hc0 : CubeParity.IsConstOnCube (f d) (S.erase d)
          (corner m (S.erase d) (Function.update base d 0) h) 0 := by
        intro y hy
        apply hz d y
        have hy' := hy d
        simp [hde, hx0] at hy'
        omega
      have hcm : CubeParity.IsConstOnCube (f d) (S.erase d)
          (corner m (S.erase d) (Function.update base d m) h) 1 := by
        intro y hy
        apply ho d y
        have hy' := hy d
        -- on this face the coordinate cannot vary
        simp [hde, hxm] at hy'
        omega
      have hq0 : Q (xs.map f) (S.erase d)
            (corner m (S.erase d) (Function.update base d 0) h) = 0 :=
        CubeParity.Q_zero_of_const (xs.map f) (S.erase d) _ hcard
          ⟨f d, hmem, 0, hc0⟩
      have hqm : Q (xs.map f) (S.erase d)
            (corner m (S.erase d) (Function.update base d m) h) = 0 :=
        CubeParity.Q_zero_of_const (xs.map f) (S.erase d) _ hcard
          ⟨f d, hmem, 1, hcm⟩
      simp [hq0, hqm]
    have hmain :
        (∑ g : (({z // z ∈ S}) → Fin m),
           ∑ b : Fin 2,
             f i (CubeParity.inc (corner m S base g) i b) *
               Q (xs.map f) (S.erase i) (CubeParity.inc (corner m S base g) i b)) = 1 := by
      rw [face_telescope m S base i hiS
        (fun x => f i x * Q (xs.map f) (S.erase i) x)]
      -- bottom endpoint has coefficient zero, top endpoint one
      have hnot : i ∉ S.erase i := by simp
      -- identify the remaining sum with the induction hypothesis
      have hrec := ih hnod (Function.update base i m)
      -- ih maybe arguments?
      -- simplify each summand first
      calc
        (∑ h : (({z // z ∈ S.erase i}) → Fin m),
          (f i (corner m (S.erase i) (Function.update base i 0) h) *
              Q (xs.map f) (S.erase i)
                (corner m (S.erase i) (Function.update base i 0) h) +
           f i (corner m (S.erase i) (Function.update base i m) h) *
              Q (xs.map f) (S.erase i)
                (corner m (S.erase i) (Function.update base i m) h)))
            = ∑ h : (({z // z ∈ S.erase i}) → Fin m),
                Q (xs.map f) (S.erase i)
                  (corner m (S.erase i) (Function.update base i m) h) := by
                    apply Finset.sum_congr rfl
                    intro h hh
                    have hx0 : corner m (S.erase i) (Function.update base i 0) h i = 0 := by
                      simp [corner, Function.update]
                    have hxm : corner m (S.erase i) (Function.update base i m) h i = m := by
                      simp [corner, Function.update]
                    rw [hz i _ hx0, ho i _ hxm]
                    simp
        _ = 1 := by
          rw [heri]
          exact hrec
    -- all the other directions have already vanished
    exact (Finset.sum_eq_single i (by
      intro d hd hdi
      exact hother d hd hdi) (by
        intro hi
        exact (hi hiS).elim)).trans hmain
end GridParity

namespace GridParity
open CubeParity Finset Function
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Clamp an unrestricted (natural) vertex to the finite box. -/
def clip (m : ℕ) (x : Vertex D) : D → Fin (m+1) := fun i =>
  ⟨min (x i) m, by omega⟩

@[simp] lemma clip_val (m : ℕ) (x : Vertex D) (i : D) :
    ((clip m x i : Fin (m+1)) : ℕ) = min (x i) m := rfl

lemma clip_of_le (m : ℕ) (x : Vertex D) {i : D} (h : x i ≤ m) :
    ((clip m x i : Fin (m+1)) : ℕ) = x i := by simp [clip, h]

/-- Finite labelled box parity lemma. -/
theorem box_exists (m : ℕ) (hm : 0 < m)
    (L : (D → Fin (m+1)) → D → ZMod 2)
    (L0 : ∀ v i, (v i : ℕ) = 0 → L v i = 0)
    (Lm : ∀ v i, (v i : ℕ) = m → L v i = 1) :
    ∃ a : D → Fin m, ∀ i : D,
      ∃ u v : D → Fin (m+1),
        (∀ j, (a j : ℕ) ≤ (u j : ℕ) ∧ (u j : ℕ) ≤ (a j : ℕ)+1) ∧
        (∀ j, (a j : ℕ) ≤ (v j : ℕ) ∧ (v j : ℕ) ≤ (a j : ℕ)+1) ∧
        L u i = 0 ∧ L v i = 1 := by
  classical
  let f : D → Vertex D → ZMod 2 := fun i x => L (clip m x) i
  have hz : ∀ d x, x d = 0 → f d x = 0 := by
    intro d x hx
    dsimp [f]
    apply L0
    simp [clip, hx]
  have ho : ∀ d x, x d = m → f d x = 1 := by
    intro d x hx
    dsimp [f]
    apply Lm
    simp [clip, hx]
  let ds : List D := (Finset.univ : Finset D).toList
  have hnod : ds.Nodup := by
    dsimp [ds]
    exact Finset.nodup_toList _
  let base : Vertex D := fun _ => 0
  have htot := total_Q (D:=D) m f hz ho ds hnod base
  have hdset : ds.toFinset = (Finset.univ : Finset D) := by
    simp [ds]
  have htot' :
      (∑ g : (({i // i ∈ ds.toFinset}) → Fin m),
        Q (ds.map f) ds.toFinset (corner m ds.toFinset base g)) ≠ 0 := by
    rw [htot]
    exact one_ne_zero
  obtain ⟨g, hgmem, hg⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero htot'
  -- turn the indexing subtype of the full set back into just `D`
  let aa : D → Fin m := fun i => g ⟨i, by simp [hdset]⟩
  have hcorner (i : D) : corner m ds.toFinset base g i = (aa i : ℕ) := by
    dsimp [aa]
    simp [corner, hdset]
  have hcard : ds.toFinset.card = (ds.map f).length := by
    have hn := List.toFinset_card_of_nodup hnod
    simpa using hn
  refine ⟨aa, ?_⟩
  intro i
  have hfi : f i ∈ ds.map f := by
    apply List.mem_map.mpr
    exact ⟨i, (Finset.mem_toList).2 (by simp), rfl⟩
  obtain ⟨⟨u, hu, huval⟩, ⟨v, hv, hvval⟩⟩ :=
    CubeParity.exists_two_vertices_of_Q_ne_zero (ds.map f) ds.toFinset
      (corner m ds.toFinset base g) hcard hg hfi
  have hS (j : D) : j ∈ ds.toFinset := by simp [hdset]
  have hu_bounds (j : D) : (aa j : ℕ) ≤ u j ∧ u j ≤ (aa j : ℕ)+1 := by
    simpa [hcorner j, hS j] using hu j
  have hv_bounds (j : D) : (aa j : ℕ) ≤ v j ∧ v j ≤ (aa j : ℕ)+1 := by
    simpa [hcorner j, hS j] using hv j
  have hu_m (j : D) : u j ≤ m := by
    have hjlt : (aa j : ℕ) < m := (aa j).isLt
    have hj := (hu_bounds j).2
    omega
  have hv_m (j : D) : v j ≤ m := by
    have hjlt : (aa j : ℕ) < m := (aa j).isLt
    have hj := (hv_bounds j).2
    omega
  let u' : D → Fin (m+1) := clip m u
  let v' : D → Fin (m+1) := clip m v
  refine ⟨u', v', ?_, ?_, ?_, ?_⟩
  · intro j
    simpa [u', clip, hu_m j] using hu_bounds j
  · intro j
    simpa [v', clip, hv_m j] using hv_bounds j
  · exact huval
  · exact hvval
end GridParity

-- END INLINED FILE: Mathlib/Support/schauder_fixed_point_390f5406f7/GridParity.lean

-- BEGIN INLINED FILE: Mathlib/Support/schauder_fixed_point_390f5406f7/Reduction.lean

noncomputable section
open Set Metric Topology Filter
open scoped BigOperators

namespace SchauderReduction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- Tent (partition of unity) weight of a centre of an `r`-net. -/
def wt (r : ℝ) (p x : E) : ℝ := max 0 (r - dist x p)

def W (r : ℝ) (p : ι → E) (x : E) : ℝ := ∑ i, wt r (p i) x

def coords (r : ℝ) (p : ι → E) (x : E) : ι → ℝ :=
  fun i => wt r (p i) x / W r p x

def comb (p : ι → E) (a : ι → ℝ) : E := ∑ i, a i • p i

lemma wt_nonneg (r : ℝ) (p x : E) : 0 ≤ wt r p x :=
  le_max_left _ _

lemma wt_pos_iff {r : ℝ} {p x : E} : 0 < wt r p x ↔ dist x p < r := by
  dsimp [wt]
  rw [lt_max_iff]
  simp

lemma continuous_wt (r : ℝ) (p : E) : Continuous (fun x : E => wt r p x) := by
  unfold wt
  fun_prop

lemma continuous_W (r : ℝ) (p : ι → E) : Continuous (W r p) := by
  unfold W
  simpa using (continuous_finset_sum (s := (Finset.univ : Finset ι))
    (f := fun i x => wt r (p i) x) (fun i hi => continuous_wt r (p i)))

lemma W_pos_of_exists {r : ℝ} {p : ι → E} {x : E}
    (h : ∃ i, dist x (p i) < r) : 0 < W r p x := by
  rcases h with ⟨i, hi⟩
  have hwi : 0 < wt r (p i) x := (wt_pos_iff).2 hi
  unfold W
  exact lt_of_lt_of_le hwi (Finset.single_le_sum (fun j _ => wt_nonneg r (p j) x)
    (Finset.mem_univ i))

lemma continuousOn_coords_of {r : ℝ} {p : ι → E} {s : Set E}
    (hW : ∀ x ∈ s, 0 < W r p x) : ContinuousOn (coords r p) s := by
  have hc : Continuous (W r p) := continuous_W r p
  -- coordinates pointwise
  intro x hx
  have hn : W r p x ≠ 0 := ne_of_gt (hW x hx)
  -- pi continuous
  exact continuousWithinAt_pi.2 (fun i =>
    ((continuous_wt r (p i)).continuousWithinAt).div hc.continuousWithinAt
      (by simpa using hn))

lemma coords_mem_stdSimplex {r : ℝ} {p : ι → E} {x : E}
    (hW : 0 < W r p x) : coords r p x ∈ stdSimplex ℝ ι := by
  constructor
  · intro i
    exact div_nonneg (wt_nonneg _ _ _) (le_of_lt hW)
  · unfold coords W
    -- factor denominator
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hW)

lemma continuous_comb (p : ι → E) : Continuous (comb p) := by
  unfold comb
  fun_prop

lemma comb_mem_convex {p : ι → E} {K : Set E}
    (hp : ∀ i, p i ∈ K) (hK : Convex ℝ K)
    {a : ι → ℝ} (ha : a ∈ stdSimplex ℝ ι) [Nonempty ι] : comb p a ∈ K := by
  -- convex sum lemma
  unfold comb
  classical
  have hs : ∑ i ∈ (Finset.univ : Finset ι), a i = (1:ℝ) := by
    simpa using ha.2
  -- Convex.sum_mem ?
  exact hK.sum_mem (t := (Finset.univ : Finset ι)) (w := a) (z := p)
    (fun i hi => ha.1 i) (by simpa using hs) (fun i hi => hp i)

/-- The partition-of-unity convex combination is at distance at most `r`. -/
lemma dist_comb_coords_le {r : ℝ} {p : ι → E} {x : E}
    (hW : 0 < W r p x) :
    dist x (comb p (coords r p x)) ≤ r := by
  classical
  have hsimp : coords r p x ∈ stdSimplex ℝ ι := coords_mem_stdSimplex hW
  have hsum : ∑ i, coords r p x i = (1 : ℝ) := hsimp.2
  have heq : (∑ i, coords r p x i • (x - p i)) =
      x - comb p (coords r p x) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hsum, one_smul]
    rfl
  rw [dist_eq_norm, ← heq]
  calc
    ‖∑ i, coords r p x i • (x - p i)‖
        ≤ ∑ i : ι, ‖coords r p x i • (x - p i)‖ :=
      (norm_sum_le (Finset.univ : Finset ι) _)
    _ ≤ ∑ i : ι, (coords r p x i) * r := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hai : 0 ≤ coords r p x i := hsimp.1 i
      by_cases hz : wt r (p i) x = 0
      · have hz' : coords r p x i = 0 := by simp [coords, hz]
        simp [hz']
      · have hwpos : 0 < wt r (p i) x :=
          lt_of_le_of_ne (wt_nonneg r (p i) x) (Ne.symm hz)
        have hd : dist x (p i) < r := wt_pos_iff.mp hwpos
        calc
          ‖coords r p x i • (x - p i)‖
              = (coords r p x i) * ‖x - p i‖ := by
                  rw [norm_smul]
                  simp [Real.norm_eq_abs, abs_of_nonneg hai]
          _ ≤ (coords r p x i) * r := by
                exact mul_le_mul_of_nonneg_left ((dist_eq_norm x (p i)) ▸ (le_of_lt hd)) hai
    _ = r := by
      rw [← Finset.sum_mul, hsum]
      simp


end SchauderReduction

namespace SchauderReduction

/-- Approximate, finite cubical sign lemma. This is the small combinatorial/mesh form of
Poincare--Miranda still needed: on a cube with opposite signed faces there are points with all
coordinates of the field as small as prescribed. Compactness is *not* part of this statement.
Typically one proves it by the labelled cubical (Kuhn/Sperner) subdivision. -/
theorem cubical_sign_approx_fin
    (n : ℕ) [Nontrivial (Fin n)]
    (H : (Fin n → ℝ) → (Fin n → ℝ))
    (hH : ContinuousOn H (Set.Icc (0 : Fin n → ℝ) 1))
    (hlo : ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, ∀ i, x i = 0 → 0 ≤ H x i)
    (hhi : ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, ∀ i, x i = 1 → H x i ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Set.Icc (0 : Fin n → ℝ) 1, ∀ i, |H x i| ≤ ε := by
  classical
  -- The outstanding ingredient is now a purely finite cubical parity fact.  Its
  -- vertices use `Fin (m+1)`; no topology occurs here.
  have gridlemma : ∀ (m : ℕ), 0 < m →
      ∀ L : (Fin n → Fin (m+1)) → Fin n → ZMod 2,
       (∀ v i, (v i : ℕ) = 0 → L v i = 0) →
       (∀ v i, (v i : ℕ) = m → L v i = 1) →
       ∃ a : Fin n → Fin m, ∀ i : Fin n,
         ∃ u v : Fin n → Fin (m+1),
           (∀ j, (a j : ℕ) ≤ (u j : ℕ) ∧ (u j : ℕ) ≤ (a j : ℕ) + 1) ∧
           (∀ j, (a j : ℕ) ≤ (v j : ℕ) ∧ (v j : ℕ) ≤ (a j : ℕ) + 1) ∧
           L u i = 0 ∧ L v i = 1 := by
    intro m hm L L0 Lm
    exact GridParity.box_exists (D := Fin n) m hm L L0 Lm
  have hu := (isCompact_Icc : IsCompact (Set.Icc (0 : Fin n → ℝ) 1)).uniformContinuousOn_of_continuous hH
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp hu) ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  let m : ℕ := k + 1
  have hm0 : 0 < m := by simp [m]
  have hmesh : (1:ℝ) / m < δ := by simpa [m, Nat.cast_add, Nat.cast_one] using hk
  let emb : (Fin n → Fin (m+1)) → (Fin n → ℝ) :=
    fun v i => (v i : ℝ) / m
  have embmem (v : Fin n → Fin (m+1)) : emb v ∈ Set.Icc (0 : Fin n → ℝ) 1 := by
    constructor
    · intro i; dsimp [emb]; positivity
    · intro i
      dsimp [emb]
      have hi : (v i : ℕ) ≤ m := (Nat.lt_succ_iff.mp (v i).isLt)
      have hmR : (0:ℝ) < m := by exact_mod_cast hm0
      apply (div_le_one hmR).2
      exact_mod_cast hi
  -- The weak signs on faces allow zeroes to be labelled on either face.
  -- In the interior a zero receives the lower label.
  let L : (Fin n → Fin (m+1)) → Fin n → ZMod 2 := fun v i =>
    if (v i : ℕ) = 0 then 0 else
    if (v i : ℕ) = m then 1 else
    if H (emb v) i < 0 then 1 else 0
  have Llo : ∀ v i, (v i : ℕ) = 0 → L v i = 0 := by
    intro v i h; have hv0 : v i = 0 := Fin.ext h
    simp [L, hv0]
  have Lhi : ∀ v i, (v i : ℕ) = m → L v i = 1 := by
    intro v i h
    have hnz : (v i : ℕ) ≠ 0 := by omega
    have hnzf : v i ≠ 0 := by intro h0; have : (v i : ℕ) = 0 := congrArg Fin.val h0; exact hnz this
    simp [L, h, hnzf]
  obtain ⟨a, ha⟩ := gridlemma m hm0 L Llo Lhi
  -- Pick the lower vertex of the distinguished small cube. All its other
  -- vertices are less than one mesh away, hence all values of `H` there are
  -- coordinatewise `ε`-close.
  let a0 : Fin n → Fin (m+1) := fun i =>
    ⟨a i, Nat.lt.step (a i).isLt⟩
  refine ⟨emb a0, embmem a0, ?_⟩
  intro i
  obtain ⟨u, v, hu', hv', hlu, hlv⟩ := ha i
  have close (w : Fin n → Fin (m+1))
      (hw : ∀ j, (a j : ℕ) ≤ (w j : ℕ) ∧ (w j : ℕ) ≤ (a j : ℕ) + 1) :
      dist (H (emb a0)) (H (emb w)) < ε := by
    apply hmod (emb a0) (embmem a0) (emb w) (embmem w)
    apply (dist_pi_lt_iff hδ).2
    intro j
    rw [Real.dist_eq]
    dsimp [emb, a0]
    have hmR : (0:ℝ) < m := by exact_mod_cast hm0
    have hlow := (hw j).1
    have hupp := (hw j).2
    have hd1 : |((a j : ℝ) / m) - ((w j : ℝ) / m)| ≤ (1:ℝ)/m := by
      rw [← sub_div]
      rw [abs_div]
      rw [abs_of_pos hmR]
      apply (div_le_div_iff_of_pos_right hmR).2
      rw [abs_le]
      have hz : (-(1:ℤ) ≤ (a j : ℤ) - (w j : ℤ) ∧ (a j : ℤ) - (w j : ℤ) ≤ 1) := by omega
      constructor
      · exact_mod_cast hz.1
      · exact_mod_cast hz.2
    exact lt_of_le_of_lt hd1 hmesh
  have cu := close u hu'
  have cv := close v hv'
  have cui : |H (emb a0) i - H (emb u) i| < ε := by
    exact (dist_pi_lt_iff hε).1 cu i |>.trans_le (by rfl) -- fix
  have cvi : |H (emb a0) i - H (emb v) i| < ε := by
    exact (dist_pi_lt_iff hε).1 cv i |>.trans_le (by rfl)
  have hupos : 0 ≤ H (emb u) i := by
    -- lower label means nonnegative, using the lower face sign if necessary
    dsimp [L] at hlu
    split at hlu <;> rename_i z
    · have hz : emb u i = 0 := by dsimp [emb]; simp [z]
      exact hlo _ (embmem u) i hz
    · split at hlu <;> rename_i top
      · cases hlu -- 1 ≠ 0
      · split at hlu <;> rename_i neg
        · cases hlu
        · exact le_of_not_gt neg
  have hvneg : H (emb v) i ≤ 0 := by
    dsimp [L] at hlv
    split at hlv <;> rename_i z
    · cases hlv
    · split at hlv <;> rename_i top
      · have hz : emb v i = 1 := by
          dsimp [emb]
          have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm0)
          simp [top, Nat.cast_ofNat]
        exact hhi _ (embmem v) i hz
      · split at hlv <;> rename_i neg
        · exact le_of_lt neg
        · cases hlv
  have cui' : -ε < H (emb a0) i - H (emb u) i ∧
        H (emb a0) i - H (emb u) i < ε := (abs_lt.mp cui)
  have cvi' : -ε < H (emb a0) i - H (emb v) i ∧
        H (emb a0) i - H (emb v) i < ε := (abs_lt.mp cvi)
  rw [abs_le]
  constructor <;> linarith


/-- Coordinate names are immaterial in the cubical sign lemma. Thus the unsolved
mesh lemma may harmlessly be taken with the canonical, linearly ordered vertices `Fin n`;
no topology is lost in this normalization. -/
theorem cubical_sign_approx
    (ι : Type*) [Fintype ι] [Nontrivial ι]
    (H : (ι → ℝ) → (ι → ℝ))
    (hH : ContinuousOn H (Set.Icc (0 : ι → ℝ) 1))
    (hlo : ∀ x ∈ Set.Icc (0 : ι → ℝ) 1, ∀ i, x i = 0 → 0 ≤ H x i)
    (hhi : ∀ x ∈ Set.Icc (0 : ι → ℝ) 1, ∀ i, x i = 1 → H x i ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Set.Icc (0 : ι → ℝ) 1, ∀ i, |H x i| ≤ ε := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  letI : Nontrivial (Fin (Fintype.card ι)) := e.injective.nontrivial
  let u : (Fin (Fintype.card ι) → ℝ) → (ι → ℝ) := fun y i => y (e i)
  let v : (ι → ℝ) → (Fin (Fintype.card ι) → ℝ) := fun x j => x (e.symm j)
  have hu : Continuous u := by
    unfold u
    fun_prop
  have hv : Continuous v := by
    unfold v
    fun_prop
  have hu_map : Set.MapsTo u (Set.Icc (0 : Fin (Fintype.card ι) → ℝ) 1)
      (Set.Icc (0 : ι → ℝ) 1) := by
    intro y hy
    exact ⟨fun i => hy.1 (e i), fun i => hy.2 (e i)⟩
  let G : (Fin (Fintype.card ι) → ℝ) → (Fin (Fintype.card ι) → ℝ) :=
    fun y => v (H (u y))
  have hpre : ContinuousOn (fun y : Fin (Fintype.card ι) → ℝ => H (u y))
      (Set.Icc (0 : Fin (Fintype.card ι) → ℝ) 1) := by
    simpa [Function.comp_def] using hH.comp hu.continuousOn hu_map
  have hG : ContinuousOn G (Set.Icc (0 : Fin (Fintype.card ι) → ℝ) 1) := by
    simpa [G, Function.comp_def] using hv.comp_continuousOn hpre
  obtain ⟨y, hy, hy'⟩ := cubical_sign_approx_fin (Fintype.card ι) G hG
    (by
      intro z hz j hj
      have hcoord : u z (e.symm j) = 0 := by simpa [u] using hj
      simpa [G, v] using hlo (u z) (hu_map hz) (e.symm j) hcoord)
    (by
      intro z hz j hj
      have hcoord : u z (e.symm j) = 1 := by simpa [u] using hj
      simpa [G, v] using hhi (u z) (hu_map hz) (e.symm j) hcoord)
    hε
  refine ⟨u y, hu_map hy, ?_⟩
  intro i
  simpa [G, v, u] using hy' (e i)


/-- Compactness turns the genuinely finite/mesh sign lemma into an exact zero. -/
theorem poincare_miranda_nontrivial
    (ι : Type*) [Fintype ι] [Nontrivial ι]
    (H : (ι → ℝ) → (ι → ℝ))
    (hH : ContinuousOn H (Set.Icc (0 : ι → ℝ) 1))
    (hlo : ∀ x ∈ Set.Icc (0 : ι → ℝ) 1, ∀ i, x i = 0 → 0 ≤ H x i)
    (hhi : ∀ x ∈ Set.Icc (0 : ι → ℝ) 1, ∀ i, x i = 1 → H x i ≤ 0) :
    ∃ x ∈ Set.Icc (0 : ι → ℝ) 1, H x = 0 := by
  classical
  let L : (ι → ℝ) → ℝ := fun x => ∑ i, |H x i|
  have hc (i : ι) : ContinuousOn (fun x => H x i)
      (Set.Icc (0 : ι → ℝ) 1) :=
    (continuous_apply (A := fun _ : ι => ℝ) i).comp_continuousOn hH
  have hL : ContinuousOn L (Set.Icc (0 : ι → ℝ) 1) := by
    exact continuousOn_finset_sum (Finset.univ : Finset ι)
      (fun i hi => (hc i).abs)
  have hn : (Set.Icc (0 : ι → ℝ) 1).Nonempty :=
    ⟨0, ⟨le_rfl, (by exact fun i => zero_le_one)⟩⟩
  obtain ⟨x, hx, hxmin⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ι → ℝ) 1)).exists_isMinOn hn hL
  have hLnon (y : ι → ℝ) : 0 ≤ L y :=
    Finset.sum_nonneg (fun i hi => abs_nonneg _)
  have hzero : L x = 0 := by
    by_contra hne
    have hpos : 0 < L x := lt_of_le_of_ne (hLnon x) (Ne.symm hne)
    have hcpos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
    have heps : 0 < L x / ((Fintype.card ι : ℝ) * 2) := by positivity
    obtain ⟨y, hy, hya⟩ := cubical_sign_approx ι H hH hlo hhi heps
    have hbound : L y ≤ (Fintype.card ι : ℝ) * (L x / ((Fintype.card ι : ℝ) * 2)) := by
      change (∑ i, |H y i|) ≤ _
      calc
        (∑ i, |H y i|) ≤ ∑ _i : ι, (L x / ((Fintype.card ι : ℝ) * 2)) := by
          exact Finset.sum_le_sum (fun i hi => hya i)
        _ = (Fintype.card ι : ℝ) * (L x / ((Fintype.card ι : ℝ) * 2)) := by
          simp
    have hhalf : (Fintype.card ι : ℝ) * (L x / ((Fintype.card ι : ℝ) * 2)) = L x / 2 := by
      field_simp
    have hxy : L x ≤ L y := hxmin hy
    rw [hhalf] at hbound
    have : L x ≤ L x / 2 := hxy.trans hbound
    linarith
  have hcoord : ∀ i : ι, |H x i| = 0 := by
    have hzsum : (∑ i, |H x i|) = (0:ℝ) := hzero
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (s := (Finset.univ : Finset ι))
      (f := fun i => |H x i|) (fun i hi => abs_nonneg _)).mp hzsum |>
       (fun hall i => hall i (Finset.mem_univ i))
  refine ⟨x, hx, ?_⟩
  funext i
  have hz : H x i = 0 := (abs_eq_zero.mp (hcoord i))
  simpa using hz

/-- Finite-dimensional Poincare--Miranda (the cubical sign lemma). The only missing
case in this lemma is isolated above; dimensions zero and one use no Brouwer machinery. -/
theorem poincare_miranda
    (ι : Type*) [Fintype ι]
    (H : (ι → ℝ) → (ι → ℝ))
    (hH : ContinuousOn H (Set.Icc (0 : ι → ℝ) 1))
    (hlo : ∀ x ∈ Set.Icc (0 : ι → ℝ) 1, ∀ i, x i = 0 → 0 ≤ H x i)
    (hhi : ∀ x ∈ Set.Icc (0 : ι → ℝ) 1, ∀ i, x i = 1 → H x i ≤ 0) :
    ∃ x ∈ Set.Icc (0 : ι → ℝ) 1, H x = 0 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI : IsEmpty ι := hempty
      refine ⟨(0 : ι → ℝ), ?_, ?_⟩
      · exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩
      · exact Subsingleton.elim _ _
  | inr hne =>
    letI : Nonempty ι := hne
    rcases subsingleton_or_nontrivial ι with hs | hn
    · letI : Subsingleton ι := hs
      let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
      let emb : ℝ → (ι → ℝ) := fun a _ => a
      let g : ℝ → ℝ := fun a => H (emb a) i0
      have hemb : Continuous emb := by
        apply continuous_pi
        intro i
        exact continuous_id
      have hembmap : Set.MapsTo emb (Set.Icc (0:ℝ) 1)
            (Set.Icc (0 : ι → ℝ) 1) := by
        intro a ha
        exact ⟨fun i => ha.1, fun i => ha.2⟩
      have hcomp : ContinuousOn (fun a : ℝ => H (emb a)) (Set.Icc (0:ℝ) 1) := by
        simpa [Function.comp_def] using hH.comp hemb.continuousOn hembmap
      have hg : ContinuousOn g (Set.Icc (0:ℝ) 1) := by
        simpa [g, Function.comp_def] using
          (continuous_apply (A := fun _ : ι => ℝ) i0).comp_continuousOn hcomp
      have he0 : emb 0 ∈ Set.Icc (0 : ι → ℝ) 1 :=
        hembmap ⟨le_rfl, zero_le_one⟩
      have he1 : emb 1 ∈ Set.Icc (0 : ι → ℝ) 1 :=
        hembmap ⟨zero_le_one, le_rfl⟩
      have hg0 : 0 ≤ g 0 := by
        exact hlo (emb 0) he0 i0 rfl
      have hg1 : g 1 ≤ 0 := by
        exact hhi (emb 1) he1 i0 rfl
      have hzmem : (0:ℝ) ∈ Set.Icc (g 1) (g 0) := ⟨hg1, hg0⟩
      obtain ⟨a, ha, hga⟩ := (intermediate_value_Icc' (α := ℝ)
          (δ := ℝ) (zero_le_one) hg) hzmem
      have hza : g a = 0 := by simpa using hga
      refine ⟨emb a, hembmap ha, ?_⟩
      funext i
      have hi : i = i0 := Subsingleton.elim _ _
      simpa [g, emb, hi] using hza
    · letI : Nontrivial ι := hn
      exact poincare_miranda_nontrivial ι H hH hlo hhi

/-- Cubical Brouwer is a short formal consequence of the signed cubical zero
lemma.  Keeping this step explicit is useful in the Schauder reduction, since it
makes the finite-dimensional obligation completely transparent. -/
theorem cube_fixedPoint
    (ι : Type*) [Fintype ι]
    (F : (ι → ℝ) → (ι → ℝ))
    (hF : ContinuousOn F (Set.Icc (0 : ι → ℝ) 1))
    (hFM : MapsTo F (Set.Icc (0 : ι → ℝ) 1) (Set.Icc (0 : ι → ℝ) 1)) :
    ∃ a ∈ Set.Icc (0 : ι → ℝ) 1, F a = a := by
  have hsub : ContinuousOn (fun x => F x - x)
      (Set.Icc (0 : ι → ℝ) 1) := hF.sub continuous_id.continuousOn
  obtain ⟨x, hx, hz⟩ :=
    poincare_miranda ι (fun x => F x - x) hsub
      (by
        intro y hy i hi
        have hy' := (hFM hy).1
        have hi' : 0 ≤ F y i := hy' i
        simpa [Pi.sub_apply, hi] using hi')
      (by
        intro y hy i hi
        have hy' := (hFM hy).2
        have hi' : F y i ≤ 1 := hy' i
        have : F y i - y i ≤ 0 := by linarith
        simpa [Pi.sub_apply] using this)
  refine ⟨x, hx, ?_⟩
  exact sub_eq_zero.mp hz

/-- Retraction used to pass from a cube to its standard simplex. -/
noncomputable def cubeRetract (ι : Type*) [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) : ι → ℝ := by
  classical
  let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
  let S : ℝ := ∑ i, x i
  exact fun i => (x i + (if i = i0 then max (1 - S) 0 else 0)) / max 1 S

lemma continuous_cubeRetract (ι : Type*) [Fintype ι] [Nonempty ι] :
    Continuous (cubeRetract ι) := by
  classical
  let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
  have hS : Continuous (fun x : ι → ℝ => ∑ j, x j) := by
    exact continuous_finset_sum (Finset.univ : Finset ι)
      (fun j hj => continuous_apply j)
  change Continuous (fun x : ι → ℝ =>
    fun i => (x i + (if i = i0 then max (1 - (∑ j, x j)) 0 else 0)) /
      max 1 (∑ j, x j))
  apply continuous_pi
  intro i
  apply Continuous.div₀
  · apply Continuous.add (continuous_apply i)
    by_cases hi : i = i0
    · simp [hi]
      fun_prop
    · simp [hi]
      fun_prop
  · exact continuous_const.max hS
  · intro x
    exact ne_of_gt (lt_of_lt_of_le (zero_lt_one) (le_max_left _ _))

lemma cubeRetract_mem (ι : Type*) [Fintype ι] [Nonempty ι]
    {x : ι → ℝ} (hx : x ∈ Set.Icc (0 : ι → ℝ) 1) :
    cubeRetract ι x ∈ stdSimplex ℝ ι := by
  classical
  let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
  let S : ℝ := ∑ i, x i
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i hi => (hx.1 i))
  have hd : 0 < max (1:ℝ) S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  -- expand the definition once; computations with the distinguished coordinate are finite sums
  change (fun i => (x i + (if i = i0 then max (1 - S) 0 else 0)) / max 1 S)
      ∈ stdSimplex ℝ ι
  constructor
  · intro i
    exact div_nonneg (add_nonneg (hx.1 i) (by split_ifs <;> positivity)) (le_of_lt hd)
  · -- sum of the extra mass is exactly its value at `i0`
    have hmass : (∑ i : ι, (if i = i0 then max (1-S) 0 else 0)) = max (1-S) 0 := by
      classical
      simp
    rw [← Finset.sum_div]
    have hnum : (∑ i : ι, (x i + (if i = i0 then max (1-S) 0 else 0)))
          = S + max (1-S) 0 := by
      rw [Finset.sum_add_distrib, hmass]
    rw [hnum]
    have heq : S + max (1-S) 0 = max 1 S := by
      rcases le_total S 1 with h | h
      · rw [max_eq_left (by linarith : 0 ≤ 1-S), max_eq_left h]
        ring
      · rw [max_eq_right (by linarith : 1-S ≤ 0), max_eq_right h]
        simp_all
    rw [heq]
    exact div_self (ne_of_gt hd)

lemma cubeRetract_id (ι : Type*) [Fintype ι] [Nonempty ι]
    {x : ι → ℝ} (hx : x ∈ stdSimplex ℝ ι) : cubeRetract ι x = x := by
  classical
  let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
  let S : ℝ := ∑ i, x i
  have hs : S = 1 := hx.2
  funext i
  change (x i + (if i = i0 then max (1-S) 0 else 0)) / max 1 S = x i
  rw [hs]
  simp

lemma stdSimplex_subset_cube (ι : Type*) [Fintype ι] [Nonempty ι] :
    stdSimplex ℝ ι ⊆ Set.Icc (0 : ι → ℝ) 1 := by
  intro x hx
  exact stdSimplex_subset_Icc ℝ hx

/-- Brouwer on a finite simplex, reduced to the cubical sign lemma. -/
theorem simplex_fixedPoint
    (ι : Type*) [Fintype ι] [Nonempty ι]
    (F : (ι → ℝ) → (ι → ℝ))
    (hF : ContinuousOn F (stdSimplex ℝ ι))
    (hFM : MapsTo F (stdSimplex ℝ ι) (stdSimplex ℝ ι)) :
    ∃ a ∈ stdSimplex ℝ ι, F a = a := by
  -- extend over the cube by the explicit retraction
  let R : (ι → ℝ) → (ι → ℝ) := cubeRetract ι
  let G : (ι → ℝ) → (ι → ℝ) := fun x => F (R x)
  have hRcont : Continuous R := continuous_cubeRetract ι
  have hRmap : MapsTo R (Set.Icc (0 : ι → ℝ) 1) (stdSimplex ℝ ι) :=
    fun x hx => cubeRetract_mem ι hx
  have hGcont : ContinuousOn G (Set.Icc (0 : ι → ℝ) 1) := by
    simpa [G, R, Function.comp_def] using hF.comp hRcont.continuousOn hRmap
  have hGmap : MapsTo G (Set.Icc (0 : ι → ℝ) 1)
        (Set.Icc (0 : ι → ℝ) 1) := by
    intro x hx
    exact stdSimplex_subset_cube ι (hFM (hRmap hx))
  obtain ⟨x, hx, heq⟩ := cube_fixedPoint ι G hGcont hGmap
  have hxs : x ∈ stdSimplex ℝ ι := by
    rw [← heq]
    exact hFM (hRmap hx)
  refine ⟨x, hxs, ?_⟩
  have hr : R x = x := cubeRetract_id ι hxs
  simpa [G, hr] using heq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Approximate fixed point obtained from a finite net, conditional only on Brouwer for the
standard (finite) simplex. -/
theorem approx_fixed_of_compact
    {K : Set E} (hKc : IsCompact K) (hKv : Convex ℝ K) (hKn : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K) (hfK : MapsTo f K K)
    {r : ℝ} (hr : 0 < r) : ∃ x ∈ K, dist (f x) x ≤ r := by
  classical
  rcases Metric.finite_approx_of_totallyBounded hKc.totallyBounded r hr with
    ⟨t, htK, htfin, hcov⟩
  letI : Fintype {y // y ∈ t} := htfin.fintype
  let p : {y // y ∈ t} → E := fun i => (i : E)
  have hex (x : E) (hx : x ∈ K) : ∃ i : {y // y ∈ t}, dist x (p i) < r := by
    have hm := hcov hx
    simp only [Set.mem_iUnion] at hm
    rcases hm with ⟨y, hy⟩
    rcases hy with ⟨hyt, hball⟩
    refine ⟨⟨y, hyt⟩, ?_⟩
    exact (Metric.mem_ball.1 hball)
  have htne : t.Nonempty := by
    rcases hKn with ⟨x, hx⟩
    rcases hex x hx with ⟨⟨y, hy⟩, h⟩
    exact ⟨y, hy⟩
  letI : Nonempty {y // y ∈ t} := htne.to_subtype
  have hp (i : {y // y ∈ t}) : p i ∈ K := htK i.property
  have hW (x : E) (hx : x ∈ K) : 0 < W r p x :=
    W_pos_of_exists (hex x hx)
  have hcomb : MapsTo (comb p) (stdSimplex ℝ {y // y ∈ t}) K := by
    intro a ha
    exact comb_mem_convex hp hKv ha
  have hfcomp : ContinuousOn (fun a : ({y // y ∈ t} → ℝ) => f (comb p a))
        (stdSimplex ℝ {y // y ∈ t}) := by
    simpa [Function.comp_def] using hf.comp (continuous_comb p).continuousOn hcomb
  have hfcomb : MapsTo (fun a : ({y // y ∈ t} → ℝ) => f (comb p a))
        (stdSimplex ℝ {y // y ∈ t}) K :=
    hfK.comp hcomb
  have hTcont : ContinuousOn
        (fun a : ({y // y ∈ t} → ℝ) => coords r p (f (comb p a)))
        (stdSimplex ℝ {y // y ∈ t}) := by
    simpa [Function.comp_def] using
      (continuousOn_coords_of (r := r) (p := p) hW).comp hfcomp hfcomb
  have hTmap : MapsTo
        (fun a : ({y // y ∈ t} → ℝ) => coords r p (f (comb p a)))
        (stdSimplex ℝ {y // y ∈ t}) (stdSimplex ℝ {y // y ∈ t}) := by
    intro a ha
    have hx : comb p a ∈ K := hcomb ha
    have hfx : f (comb p a) ∈ K := hfK hx
    exact coords_mem_stdSimplex (hW _ hfx)
  obtain ⟨a, ha, ha'⟩ :=
    simplex_fixedPoint {y // y ∈ t}
      (fun a : ({y // y ∈ t} → ℝ) => coords r p (f (comb p a))) hTcont hTmap
  refine ⟨comb p a, hcomb ha, ?_⟩
  have hfx : f (comb p a) ∈ K := hfK (hcomb ha)
  have hle := dist_comb_coords_le (p := p) (x := f (comb p a)) (hW _ hfx)
  rw [ha'] at hle
  exact hle

end SchauderReduction

namespace SchauderReduction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compactness promotes arbitrarily good approximate fixed points to an exact one, by minimizing
the continuous displacement. This avoids any choices of subsequences. -/
theorem exact_of_approx
    {K : Set E} (hK : IsCompact K) (hn : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K)
    (ha : ∀ {r : ℝ}, 0 < r → ∃ x ∈ K, dist (f x) x ≤ r) :
    ∃ x ∈ K, f x = x := by
  have hg : ContinuousOn (fun x : E => dist (f x) x) K := by
    simpa [dist_eq_norm] using (hf.sub continuous_id.continuousOn).norm
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hn hg
  refine ⟨x, hx, ?_⟩
  have hz : dist (f x) x = 0 := by
    by_contra hne
    have hpos : 0 < dist (f x) x :=
      lt_of_le_of_ne dist_nonneg (Ne.symm hne)
    obtain ⟨y, hy, hle⟩ := ha (show 0 < dist (f x) x / 2 by linarith)
    have hxy : dist (f x) x ≤ dist (f y) y := hmin hy
    have h' : dist (f x) x ≤ dist (f x) x / 2 := hxy.trans hle
    linarith
  exact (dist_eq_zero.mp hz)

/-- Analytic Schauder reduction: save Brouwer for the one finite-dimensional statement above. -/
theorem fixed_of_compact
    {K : Set E} (hKc : IsCompact K) (hKv : Convex ℝ K) (hKn : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K) (hfK : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  apply exact_of_approx hKc hKn f hf
  intro r hr
  exact approx_fixed_of_compact hKc hKv hKn f hf hfK hr

end SchauderReduction

end

-- END INLINED FILE: Mathlib/Support/schauder_fixed_point_390f5406f7/Reduction.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem schauder_fixed_point {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set E}
    (_hK_compact : IsCompact K) (_hK_convex : Convex ℝ K)
    (_hK_nonempty : K.Nonempty)
    (f : E → E)
    (_hf_cont : ContinuousOn f K) (_hf_maps : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x :=
/-ResultProofBegin-/by
  exact SchauderReduction.fixed_of_compact _hK_compact _hK_convex _hK_nonempty f _hf_cont _hf_maps
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
