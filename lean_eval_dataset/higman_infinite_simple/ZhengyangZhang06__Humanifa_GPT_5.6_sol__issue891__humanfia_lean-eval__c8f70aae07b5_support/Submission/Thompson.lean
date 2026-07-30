import Mathlib

set_option maxRecDepth 10000

namespace Submission.Thompson

open scoped commutatorElement

theorem double_commutator_eq_of_commute_conjugate {G : Type*} [Group G]
    (a b g : G) (hcomm : Commute a (g * b⁻¹ * g⁻¹)) :
    ⁅a, ⁅b, g⁆⁆ = ⁅a, b⁆ := by
  let q := g * b⁻¹ * g⁻¹
  have hinner : ⁅b, g⁆ = b * q := by
    simp [q, commutatorElement_def, mul_assoc]
  rw [hinner]
  simp only [commutatorElement_def, mul_inv_rev]
  change a * (b * q) * a⁻¹ * (q⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹
  calc
    _ = a * b * (q * a⁻¹) * (q⁻¹ * b⁻¹) := by simp only [mul_assoc]
    _ = a * b * (a⁻¹ * q) * (q⁻¹ * b⁻¹) := by rw [hcomm.inv_left.symm.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by simp [mul_assoc]

theorem map_mem_commutator {G H : Type*} [Group G] [Group H]
    (f : G →* H) {g : G} (hg : g ∈ commutator G) :
    f g ∈ commutator H := by
  have hmap : f g ∈ (commutator G).map f := Subgroup.mem_map_of_mem f hg
  rw [commutator_def, Subgroup.map_commutator] at hmap
  exact Subgroup.commutator_mono le_top le_top hmap

theorem exists_equiv_apply_eq {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (hcard : Fintype.card A = Fintype.card B)
    (a : A) (b : B) : ∃ e : A ≃ B, e a = b := by
  let e₀ := Fintype.equivOfCardEq hcard
  refine ⟨e₀.trans (Equiv.swap (e₀ a) b), ?_⟩
  simp

theorem exists_equiv_map_pair {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (hcard : Fintype.card A = Fintype.card B)
    {a₁ a₂ : A} {b₁ b₂ : B} (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) :
    ∃ e : A ≃ B, e a₁ = b₁ ∧ e a₂ = b₂ := by
  let e₀ := Fintype.equivOfCardEq hcard
  let p₁ := Equiv.swap (e₀ a₁) b₁
  let b₂' := p₁ (e₀ a₂)
  have hp₁a : p₁ (e₀ a₁) = b₁ := by simp [p₁]
  have hb₂' : b₂' ≠ b₁ := by
    intro h
    apply ha
    apply e₀.injective
    apply p₁.injective
    rw [hp₁a]
    exact h.symm
  let p₂ := Equiv.swap b₂' b₂
  have hp₂a : p₂ b₁ = b₁ := by
    exact Equiv.swap_apply_of_ne_of_ne hb₂'.symm hb
  refine ⟨e₀.trans (p₁.trans p₂), ?_, ?_⟩
  · exact hp₁a ▸ hp₂a
  · simp [Equiv.trans_apply, b₂', p₂]

/-- Cantor space, represented by infinite binary streams. -/
abbrev Cantor := ℕ → Bool

namespace Cantor

def head (x : Cantor) : Bool := x 0

def tail (x : Cantor) : Cantor := fun n => x (n + 1)

def cons (b : Bool) (x : Cantor) : Cantor
  | 0 => b
  | n + 1 => x n

@[simp] theorem head_cons (b : Bool) (x : Cantor) : head (cons b x) = b := rfl

@[simp] theorem tail_cons (b : Bool) (x : Cantor) : tail (cons b x) = x := by
  funext n
  rfl

@[simp] theorem cons_head_tail (x : Cantor) : cons (head x) (tail x) = x := by
  funext n
  cases n <;> rfl

/-- Attach a finite word to a binary stream. -/
def prepend : List Bool → Cantor → Cantor
  | [], x => x
  | b :: word, x => cons b (prepend word x)

@[simp] theorem prepend_nil (x : Cantor) : prepend [] x = x := rfl

@[simp] theorem prepend_cons (b : Bool) (word : List Bool) (x : Cantor) :
    prepend (b :: word) x = cons b (prepend word x) := rfl

@[simp] theorem prepend_append (left right : List Bool) (x : Cantor) :
    prepend (left ++ right) x = prepend left (prepend right x) := by
  induction left with
  | nil => rfl
  | cons b left ih => simp [ih]

theorem prepend_injective (word : List Bool) : Function.Injective (prepend word) := by
  induction word with
  | nil => exact Function.injective_id
  | cons b word ih =>
      intro x y h
      apply ih
      exact congrArg tail h

/-- Apply a permutation inside one of the two top-level cylinders and fix the
other cylinder pointwise. -/
def branchFun (b : Bool) (g : Equiv.Perm Cantor) (x : Cantor) : Cantor :=
  if head x = b then cons b (g (tail x)) else x

def branchPerm (b : Bool) (g : Equiv.Perm Cantor) : Equiv.Perm Cantor where
  toFun := branchFun b g
  invFun := branchFun b g.symm
  left_inv x := by
    cases b <;> cases h : head x <;>
      simp [branchFun, h] <;>
      simpa [h] using cons_head_tail x
  right_inv x := by
    cases b <;> cases h : head x <;>
      simp [branchFun, h] <;>
      simpa [h] using cons_head_tail x

/-- Localize a permutation to the cylinder determined by `word`. -/
def localPerm : List Bool → Equiv.Perm Cantor → Equiv.Perm Cantor
  | [], g => g
  | b :: word, g => branchPerm b (localPerm word g)

@[simp] theorem localPerm_nil (g : Equiv.Perm Cantor) : localPerm [] g = g := rfl

@[simp] theorem localPerm_cons (b : Bool) (word : List Bool) (g : Equiv.Perm Cantor) :
    localPerm (b :: word) g = branchPerm b (localPerm word g) := rfl

@[simp] theorem localPerm_prepend (word : List Bool) (g : Equiv.Perm Cantor) (x : Cantor) :
    localPerm word g (prepend word x) = prepend word (g x) := by
  induction word with
  | nil => rfl
  | cons b word ih =>
      simp [localPerm, prepend, branchPerm, branchFun, ih]

theorem localPerm_injective (word : List Bool) : Function.Injective (localPerm word) := by
  intro g h heq
  apply Equiv.ext
  intro x
  apply prepend_injective word
  rw [← localPerm_prepend word g x, ← localPerm_prepend word h x, heq]

@[simp] theorem localPerm_one (word : List Bool) :
    localPerm word (1 : Equiv.Perm Cantor) = 1 := by
  induction word with
  | nil => rfl
  | cons b word ih =>
      apply Equiv.ext
      intro x
      cases b <;> cases h : head x <;>
        simp [localPerm, branchPerm, branchFun, h, ih] <;>
        simpa [h] using cons_head_tail x

@[simp] theorem localPerm_mul (word : List Bool) (g h : Equiv.Perm Cantor) :
    localPerm word (g * h) = localPerm word g * localPerm word h := by
  induction word with
  | nil => rfl
  | cons b word ih =>
      apply Equiv.ext
      intro x
      cases b <;> cases hx : head x <;>
        simp [localPerm, branchPerm, branchFun, hx, ih, Equiv.Perm.mul_apply]

/-- Localization as an injective group homomorphism on the full permutation
group of Cantor space. -/
def localHom (word : List Bool) :
    Equiv.Perm Cantor →* Equiv.Perm Cantor where
  toFun := localPerm word
  map_one' := localPerm_one word
  map_mul' := localPerm_mul word

@[simp] theorem localPerm_inv (word : List Bool) (g : Equiv.Perm Cantor) :
    localPerm word g⁻¹ = (localPerm word g)⁻¹ :=
  map_inv (localHom word) g

theorem localHom_injective (word : List Bool) : Function.Injective (localHom word) :=
  localPerm_injective word

/-- The clopen cylinder consisting of streams with a specified word. -/
def cylinder (word : List Bool) : Set Cantor := Set.range (prepend word)

@[simp] theorem cylinder_nil : cylinder [] = Set.univ := by
  ext x
  simp [cylinder]

theorem mem_cylinder_cons (b : Bool) (word : List Bool) (x : Cantor) :
    x ∈ cylinder (b :: word) ↔ head x = b ∧ tail x ∈ cylinder word := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨head_cons b _, ⟨y, tail_cons b _⟩⟩
  · rintro ⟨hhead, y, htail⟩
    refine ⟨y, ?_⟩
    calc
      prepend (b :: word) y = cons b (prepend word y) := rfl
      _ = cons (head x) (tail x) := by rw [hhead, htail]
      _ = x := cons_head_tail x

theorem localPerm_mem_cylinder {word : List Bool} {g : Equiv.Perm Cantor} {x : Cantor}
    (hx : x ∈ cylinder word) : localPerm word g x ∈ cylinder word := by
  rcases hx with ⟨y, rfl⟩
  exact ⟨g y, (localPerm_prepend word g y).symm⟩

theorem localPerm_fixed_of_not_mem {word : List Bool} {g : Equiv.Perm Cantor} {x : Cantor}
    (hx : x ∉ cylinder word) : localPerm word g x = x := by
  induction word generalizing x with
  | nil => exact (hx (by simp [cylinder])).elim
  | cons b word ih =>
      by_cases hhead : head x = b
      · have htail : tail x ∉ cylinder word := by
          intro h
          exact hx ((mem_cylinder_cons b word x).2 ⟨hhead, h⟩)
        rw [show x = cons b (tail x) by simpa [hhead] using (cons_head_tail x).symm]
        simp [localPerm, branchPerm, branchFun, ih htail]
      · simp [localPerm, branchPerm, branchFun, hhead]

theorem localPerm_commute_of_disjoint {left right : List Bool}
    (hdisjoint : Disjoint (cylinder left) (cylinder right))
    (g h : Equiv.Perm Cantor) : Commute (localPerm left g) (localPerm right h) := by
  change localPerm left g * localPerm right h =
    localPerm right h * localPerm left g
  apply Equiv.ext
  intro x
  by_cases hxLeft : x ∈ cylinder left
  · have hxRight : x ∉ cylinder right :=
      Set.disjoint_left.1 hdisjoint hxLeft
    have hgLeft : localPerm left g x ∈ cylinder left := localPerm_mem_cylinder hxLeft
    have hgRight : localPerm left g x ∉ cylinder right :=
      Set.disjoint_left.1 hdisjoint hgLeft
    simp [Equiv.Perm.mul_apply, localPerm_fixed_of_not_mem hxRight,
      localPerm_fixed_of_not_mem hgRight]
  · by_cases hxRight : x ∈ cylinder right
    · have hhRight : localPerm right h x ∈ cylinder right := localPerm_mem_cylinder hxRight
      have hhLeft : localPerm right h x ∉ cylinder left := fun hmem =>
        Set.disjoint_left.1 hdisjoint hmem hhRight
      simp [Equiv.Perm.mul_apply, localPerm_fixed_of_not_mem hxLeft,
        localPerm_fixed_of_not_mem hhLeft]
    · simp [Equiv.Perm.mul_apply, localPerm_fixed_of_not_mem hxLeft,
        localPerm_fixed_of_not_mem hxRight]

theorem prefix_or_prefix_of_prepend_eq {left right : List Bool} {x y : Cantor}
    (h : prepend left x = prepend right y) : left <+: right ∨ right <+: left := by
  induction left generalizing right x y with
  | nil => exact Or.inl List.nil_prefix
  | cons b left ih =>
      cases right with
      | nil => exact Or.inr List.nil_prefix
      | cons c right =>
          have hbc : b = c := by
            simpa using congrArg head h
          subst c
          have htail : prepend left x = prepend right y := by
            simpa using congrArg tail h
          rcases ih htail with hprefix | hprefix
          · exact Or.inl ((List.cons_prefix_cons).2 ⟨rfl, hprefix⟩)
          · exact Or.inr ((List.cons_prefix_cons).2 ⟨rfl, hprefix⟩)

theorem cylinder_disjoint_of_incomparable {left right : List Bool}
    (hleft : ¬ left <+: right) (hright : ¬ right <+: left) :
    Disjoint (cylinder left) (cylinder right) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  rcases prefix_or_prefix_of_prepend_eq (hx.trans hy.symm) with h | h
  · exact hleft h
  · exact hright h

/-- Appending one common suffix makes any two distinct finite words
incomparable. -/
theorem exists_append_incomparable {left right : List Bool} (hne : left ≠ right) :
    ∃ suffix : List Bool,
      ¬ left ++ suffix <+: right ++ suffix ∧
        ¬ right ++ suffix <+: left ++ suffix := by
  by_cases hlr : left <+: right
  · rcases hlr with ⟨middle, hmiddle⟩
    cases middle with
    | nil =>
        exact (hne (by simpa using hmiddle)).elim
    | cons b middle =>
        refine ⟨[!b], ?_, ?_⟩
        · rw [← hmiddle]
          simp only [List.append_assoc, List.prefix_append_right_inj]
          simp
        · rw [← hmiddle]
          simp only [List.append_assoc, List.prefix_append_right_inj]
          simp
  · by_cases hrl : right <+: left
    · rcases hrl with ⟨middle, hmiddle⟩
      cases middle with
      | nil =>
          exact (hne (by simpa using hmiddle.symm)).elim
      | cons b middle =>
          refine ⟨[!b], ?_, ?_⟩
          · rw [← hmiddle]
            simp only [List.append_assoc, List.prefix_append_right_inj]
            simp
          · rw [← hmiddle]
            simp only [List.append_assoc, List.prefix_append_right_inj]
            simp
    · exact ⟨[], by simpa, by simpa⟩

theorem inv_prepend_of_map_prepend {left right : List Bool}
    (g : Equiv.Perm Cantor)
    (hmap : ∀ x : Cantor, g (prepend left x) = prepend right x) (x : Cantor) :
    g⁻¹ (prepend right x) = prepend left x := by
  apply g.injective
  simp [hmap]

/-- Rigidly carrying one cylinder to another conjugates the corresponding
localized permutations. -/
theorem conjugate_localPerm_of_map_prepend {left right : List Bool}
    (g h : Equiv.Perm Cantor)
    (hmap : ∀ x : Cantor, g (prepend left x) = prepend right x) :
    g * localPerm left h * g⁻¹ = localPerm right h := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ cylinder right
  · rcases hx with ⟨y, rfl⟩
    simp only [Equiv.Perm.mul_apply]
    rw [inv_prepend_of_map_prepend g hmap]
    simp [hmap]
  · have hinv : g⁻¹ x ∉ cylinder left := by
      rintro ⟨y, hy⟩
      apply hx
      refine ⟨y, ?_⟩
      calc
        prepend right y = g (prepend left y) := (hmap y).symm
        _ = g (g⁻¹ x) := congrArg g hy
        _ = x := g.apply_symm_apply x
    simp only [Equiv.Perm.mul_apply]
    rw [localPerm_fixed_of_not_mem hinv]
    rw [localPerm_fixed_of_not_mem hx]
    exact g.apply_symm_apply x

end Cantor

/-- A finite full binary tree. Its leaves form a finite complete word code. -/
inductive Tree where
  | leaf : Tree
  | fork : Tree → Tree → Tree
  deriving DecidableEq

/-- The finite type of leaves of a binary tree. -/
@[reducible] def Tree.Leaf : Tree → Type
  | .leaf => Unit
  | .fork left right => Tree.Leaf left ⊕ Tree.Leaf right

namespace Tree

@[reducible] def leafFintype : (t : Tree) → Fintype t.Leaf
  | .leaf => inferInstance
  | .fork left right => by
      letI : Fintype left.Leaf := leafFintype left
      letI : Fintype right.Leaf := leafFintype right
      exact inferInstance

@[reducible] instance (t : Tree) : Fintype t.Leaf := leafFintype t

@[reducible] def leafDecidableEq : (t : Tree) → DecidableEq t.Leaf
  | .leaf => inferInstance
  | .fork left right => by
      letI : DecidableEq left.Leaf := leafDecidableEq left
      letI : DecidableEq right.Leaf := leafDecidableEq right
      exact inferInstance

@[reducible] instance (t : Tree) : DecidableEq t.Leaf := leafDecidableEq t

theorem leafNonempty : (t : Tree) → Nonempty t.Leaf
  | .leaf => ⟨()⟩
  | .fork left _ => (leafNonempty left).map Sum.inl

instance (t : Tree) : Nonempty t.Leaf := leafNonempty t

/-- The finite word labelling a leaf of a binary tree. -/
def path : (t : Tree) → t.Leaf → List Bool
  | .leaf, _ => []
  | .fork left _, Sum.inl i => false :: path left i
  | .fork _ right, Sum.inr i => true :: path right i

/-- A full tree having a prescribed word as a distinguished leaf. -/
def prefixTree : List Bool → Tree
  | [] => .leaf
  | false :: word => .fork (prefixTree word) .leaf
  | true :: word => .fork .leaf (prefixTree word)

def prefixLeaf : (word : List Bool) → (prefixTree word).Leaf
  | [] => ()
  | false :: word => Sum.inl (prefixLeaf word)
  | true :: word => Sum.inr (prefixLeaf word)

@[simp] theorem path_prefixLeaf (word : List Bool) :
    path (prefixTree word) (prefixLeaf word) = word := by
  induction word with
  | nil => rfl
  | cons b word ih => cases b <;> simp [prefixTree, prefixLeaf, path, ih]

@[simp] theorem card_prefixTree_leaf (word : List Bool) :
    Fintype.card (prefixTree word).Leaf = word.length + 1 := by
  induction word with
  | nil => simp [prefixTree, Tree.Leaf]
  | cons b word ih =>
      cases b with
      | false =>
          change Fintype.card ((prefixTree word).Leaf ⊕ Unit) = word.length + 1 + 1
          rw [Fintype.card_sum, ih]
          simp
      | true =>
          change Fintype.card (Unit ⊕ (prefixTree word).Leaf) = word.length + 1 + 1
          rw [Fintype.card_sum, ih]
          simp [Nat.add_comm, Nat.add_left_comm]

/-- Replace each leaf of `t` by a specified binary tree. -/
def expand : (t : Tree) → (t.Leaf → Tree) → Tree
  | .leaf, pieces => pieces ()
  | .fork left right, pieces =>
      .fork (expand left (fun i => pieces (Sum.inl i)))
        (expand right (fun i => pieces (Sum.inr i)))

@[simp] theorem expand_all_leaf : ∀ t : Tree, expand t (fun _ => .leaf) = t
  | .leaf => rfl
  | .fork left right => by simp [expand, expand_all_leaf left, expand_all_leaf right]

/-- Package a leaf of an expanded tree as an outer leaf together with a leaf
of the tree inserted there. -/
def packExpandedLeaf : (t : Tree) → (pieces : t.Leaf → Tree) →
    (expand t pieces).Leaf → Σ i : t.Leaf, (pieces i).Leaf
  | .leaf, _, i => ⟨(), i⟩
  | .fork left _, pieces, Sum.inl i =>
      let packed := packExpandedLeaf left (fun j => pieces (Sum.inl j)) i
      ⟨Sum.inl packed.1, packed.2⟩
  | .fork _ right, pieces, Sum.inr i =>
      let packed := packExpandedLeaf right (fun j => pieces (Sum.inr j)) i
      ⟨Sum.inr packed.1, packed.2⟩

/-- Unpackage an outer leaf and an inserted-tree leaf into a leaf of the
expanded tree. -/
def unpackExpandedLeaf : (t : Tree) → (pieces : t.Leaf → Tree) →
    (Σ i : t.Leaf, (pieces i).Leaf) → (expand t pieces).Leaf
  | .leaf, _, ⟨(), i⟩ => i
  | .fork left _, pieces, ⟨Sum.inl i, j⟩ =>
      Sum.inl (unpackExpandedLeaf left (fun k => pieces (Sum.inl k)) ⟨i, j⟩)
  | .fork _ right, pieces, ⟨Sum.inr i, j⟩ =>
      Sum.inr (unpackExpandedLeaf right (fun k => pieces (Sum.inr k)) ⟨i, j⟩)

@[simp] theorem unpack_pack_expanded_leaf :
    ∀ (t : Tree) (pieces : t.Leaf → Tree) (i : (expand t pieces).Leaf),
      unpackExpandedLeaf t pieces (packExpandedLeaf t pieces i) = i := by
  intro t
  induction t with
  | leaf => intro pieces i; exact rfl
  | fork left right ihLeft ihRight =>
      intro pieces i
      cases i with
      | inl i => simp [packExpandedLeaf, unpackExpandedLeaf, ihLeft]
      | inr i => simp [packExpandedLeaf, unpackExpandedLeaf, ihRight]

@[simp] theorem pack_unpack_expanded_leaf :
    ∀ (t : Tree) (pieces : t.Leaf → Tree) (i : Σ j : t.Leaf, (pieces j).Leaf),
      packExpandedLeaf t pieces (unpackExpandedLeaf t pieces i) = i := by
  intro t
  induction t with
  | leaf => rintro pieces ⟨i, j⟩; cases i; rfl
  | fork left right ihLeft ihRight =>
      rintro pieces ⟨i, j⟩
      cases i with
      | inl i =>
          have h := ihLeft (fun k => pieces (Sum.inl k)) ⟨i, j⟩
          have h' := congrArg
            (fun p : Σ k : left.Leaf, (pieces (Sum.inl k)).Leaf =>
              (⟨Sum.inl p.1, p.2⟩ :
                Σ k : (Tree.fork left right).Leaf, (pieces k).Leaf)) h
          simpa only [packExpandedLeaf, unpackExpandedLeaf] using h'
      | inr i =>
          have h := ihRight (fun k => pieces (Sum.inr k)) ⟨i, j⟩
          have h' := congrArg
            (fun p : Σ k : right.Leaf, (pieces (Sum.inr k)).Leaf =>
              (⟨Sum.inr p.1, p.2⟩ :
                Σ k : (Tree.fork left right).Leaf, (pieces k).Leaf)) h
          simpa only [packExpandedLeaf, unpackExpandedLeaf] using h'

/-- Leaves of an expanded tree are canonically pairs of an outer leaf and an
inner leaf. -/
def expandedLeafEquiv (t : Tree) (pieces : t.Leaf → Tree) :
    (expand t pieces).Leaf ≃ Σ i : t.Leaf, (pieces i).Leaf where
  toFun := packExpandedLeaf t pieces
  invFun := unpackExpandedLeaf t pieces
  left_inv := unpack_pack_expanded_leaf t pieces
  right_inv := pack_unpack_expanded_leaf t pieces

/-- Split a stream at the unique leaf of `t` whose word it has. The residual
stream is the part following that word. -/
def encode : (t : Tree) → Cantor → t.Leaf × Cantor
  | .leaf, x => ((), x)
  | .fork left right, x =>
      if Cantor.head x then
        let encoded := encode right (Cantor.tail x)
        (Sum.inr encoded.1, encoded.2)
      else
        let encoded := encode left (Cantor.tail x)
        (Sum.inl encoded.1, encoded.2)

/-- Reattach a leaf word to a residual stream. -/
def decode : (t : Tree) → t.Leaf × Cantor → Cantor
  | .leaf, pair => pair.2
  | .fork left _, (Sum.inl i, x) => Cantor.cons false (decode left (i, x))
  | .fork _ right, (Sum.inr i, x) => Cantor.cons true (decode right (i, x))

theorem decode_eq_prepend : ∀ (t : Tree) (i : t.Leaf) (x : Cantor),
    decode t (i, x) = Cantor.prepend (path t i) x := by
  intro t
  induction t with
  | leaf => rintro i x; cases i; rfl
  | fork left right ihLeft ihRight =>
      rintro (i | i) x
      · simp [decode, path, ihLeft]
      · simp [decode, path, ihRight]

@[simp] theorem decode_encode : ∀ (t : Tree) (x : Cantor), decode t (encode t x) = x := by
  intro t
  induction t with
  | leaf => intro x; exact rfl
  | fork left right ihLeft ihRight =>
      intro x
      cases h : Cantor.head x with
      | false =>
          rw [show x = Cantor.cons false (Cantor.tail x) by
            simpa [h] using (Cantor.cons_head_tail x).symm]
          simp [encode, decode, ihLeft]
      | true =>
          rw [show x = Cantor.cons true (Cantor.tail x) by
            simpa [h] using (Cantor.cons_head_tail x).symm]
          simp [encode, decode, ihRight]

@[simp] theorem encode_decode : ∀ (t : Tree) (p : t.Leaf × Cantor), encode t (decode t p) = p := by
  intro t
  induction t with
  | leaf => rintro ⟨i, x⟩; cases i; rfl
  | fork left right ihLeft ihRight =>
      rintro ⟨i, x⟩
      cases i with
      | inl i => simp [encode, decode, ihLeft]
      | inr i => simp [encode, decode, ihRight]

/-- The canonical coding equivalence associated to the leaves of a tree. -/
def codeEquiv (t : Tree) : Cantor ≃ t.Leaf × Cantor where
  toFun := encode t
  invFun := decode t
  left_inv := decode_encode t
  right_inv := encode_decode t

/-- Coding first by the outer tree and then by the tree inserted at the
selected leaf. -/
def nestedEncode (t : Tree) (pieces : t.Leaf → Tree) (x : Cantor) :
    (Σ i : t.Leaf, (pieces i).Leaf) × Cantor :=
  let outer := encode t x
  let inner := encode (pieces outer.1) outer.2
  (⟨outer.1, inner.1⟩, inner.2)

/-- Inverse of `nestedEncode`. -/
def nestedDecode (t : Tree) (pieces : t.Leaf → Tree)
    (p : (Σ i : t.Leaf, (pieces i).Leaf) × Cantor) : Cantor :=
  decode t (p.1.1, decode (pieces p.1.1) (p.1.2, p.2))

@[simp] theorem nested_decode_encode (t : Tree) (pieces : t.Leaf → Tree) (x : Cantor) :
    nestedDecode t pieces (nestedEncode t pieces x) = x := by
  simp [nestedDecode, nestedEncode]

@[simp] theorem nested_encode_decode (t : Tree) (pieces : t.Leaf → Tree)
    (p : (Σ i : t.Leaf, (pieces i).Leaf) × Cantor) :
    nestedEncode t pieces (nestedDecode t pieces p) = p := by
  rcases p with ⟨⟨i, j⟩, x⟩
  simp only [nestedDecode, nestedEncode]
  rw [encode_decode]
  rw [encode_decode]

def nestedCodeEquiv (t : Tree) (pieces : t.Leaf → Tree) :
    Cantor ≃ (Σ i : t.Leaf, (pieces i).Leaf) × Cantor where
  toFun := nestedEncode t pieces
  invFun := nestedDecode t pieces
  left_inv := nested_decode_encode t pieces
  right_inv := nested_encode_decode t pieces

theorem pack_encode_expand :
    ∀ (t : Tree) (pieces : t.Leaf → Tree) (x : Cantor),
      ((expandedLeafEquiv t pieces).prodCongr (Equiv.refl Cantor))
          (encode (expand t pieces) x) =
        nestedEncode t pieces x := by
  intro t
  induction t with
  | leaf => intro pieces x; rfl
  | fork left right ihLeft ihRight =>
      intro pieces x
      cases h : Cantor.head x with
      | false =>
          rw [show x = Cantor.cons false (Cantor.tail x) by
            simpa [h] using (Cantor.cons_head_tail x).symm]
          let liftLeft :
              ((Σ i : left.Leaf, (pieces (Sum.inl i)).Leaf) × Cantor) →
                ((Σ i : (Tree.fork left right).Leaf, (pieces i).Leaf) × Cantor) :=
            fun p => (⟨Sum.inl p.1.1, p.1.2⟩, p.2)
          have hi := congrArg liftLeft
            (ihLeft (fun i => pieces (Sum.inl i)) (Cantor.tail x))
          change liftLeft
              (((expandedLeafEquiv left (fun i => pieces (Sum.inl i))).prodCongr
                (Equiv.refl Cantor))
                (encode (expand left (fun i => pieces (Sum.inl i))) (Cantor.tail x))) =
            liftLeft (nestedEncode left (fun i => pieces (Sum.inl i)) (Cantor.tail x))
          exact hi
      | true =>
          rw [show x = Cantor.cons true (Cantor.tail x) by
            simpa [h] using (Cantor.cons_head_tail x).symm]
          let liftRight :
              ((Σ i : right.Leaf, (pieces (Sum.inr i)).Leaf) × Cantor) →
                ((Σ i : (Tree.fork left right).Leaf, (pieces i).Leaf) × Cantor) :=
            fun p => (⟨Sum.inr p.1.1, p.1.2⟩, p.2)
          have hi := congrArg liftRight
            (ihRight (fun i => pieces (Sum.inr i)) (Cantor.tail x))
          change liftRight
              (((expandedLeafEquiv right (fun i => pieces (Sum.inr i))).prodCongr
                (Equiv.refl Cantor))
                (encode (expand right (fun i => pieces (Sum.inr i))) (Cantor.tail x))) =
            liftRight (nestedEncode right (fun i => pieces (Sum.inr i)) (Cantor.tail x))
          exact hi

theorem decode_unpack_expand :
    ∀ (t : Tree) (pieces : t.Leaf → Tree)
      (p : (Σ i : t.Leaf, (pieces i).Leaf) × Cantor),
      decode (expand t pieces)
          ((expandedLeafEquiv t pieces).symm p.1, p.2) =
        nestedDecode t pieces p := by
  intro t
  induction t with
  | leaf => rintro pieces ⟨⟨i, j⟩, x⟩; cases i; rfl
  | fork left right ihLeft ihRight =>
      rintro pieces ⟨⟨i, j⟩, x⟩
      cases i with
      | inl i =>
          change Cantor.cons false
              (decode (expand left (fun k => pieces (Sum.inl k)))
                ((expandedLeafEquiv left (fun k => pieces (Sum.inl k))).symm ⟨i, j⟩, x)) =
            Cantor.cons false
              (nestedDecode left (fun k => pieces (Sum.inl k)) (⟨i, j⟩, x))
          exact congrArg (Cantor.cons false)
            (ihLeft (fun k => pieces (Sum.inl k)) (⟨i, j⟩, x))
      | inr i =>
          change Cantor.cons true
              (decode (expand right (fun k => pieces (Sum.inr k)))
                ((expandedLeafEquiv right (fun k => pieces (Sum.inr k))).symm ⟨i, j⟩, x)) =
            Cantor.cons true
              (nestedDecode right (fun k => pieces (Sum.inr k)) (⟨i, j⟩, x))
          exact congrArg (Cantor.cons true)
            (ihRight (fun k => pieces (Sum.inr k)) (⟨i, j⟩, x))

theorem expanded_code_equiv (t : Tree) (pieces : t.Leaf → Tree) :
    (codeEquiv (expand t pieces)).trans
        ((expandedLeafEquiv t pieces).prodCongr (Equiv.refl Cantor)) =
      nestedCodeEquiv t pieces := by
  apply Equiv.ext
  intro x
  exact pack_encode_expand t pieces x

/-- Extend a leaf bijection through matching expansions at corresponding
leaves. -/
def expandEquiv {source target : Tree} (e : source.Leaf ≃ target.Leaf)
    (pieces : source.Leaf → Tree) :
    (expand source pieces).Leaf ≃
      (expand target (fun j => pieces (e.symm j))).Leaf :=
  (expandedLeafEquiv source pieces).trans
    ((Equiv.sigmaCongrLeft' e).trans
      (expandedLeafEquiv target (fun j => pieces (e.symm j))).symm)

/-- The least common refinement of two binary trees. -/
def join : Tree → Tree → Tree
  | .leaf, other => other
  | tree@(.fork _ _), .leaf => tree
  | .fork left right, .fork left' right' =>
      .fork (join left left') (join right right')

/-- The trees which must be inserted at the leaves of the first argument to
obtain `join`. -/
def joinPiecesLeft : (first second : Tree) → first.Leaf → Tree
  | .leaf, second, _ => second
  | .fork _ _, .leaf, _ => .leaf
  | .fork left _, .fork left' _, Sum.inl i => joinPiecesLeft left left' i
  | .fork _ right, .fork _ right', Sum.inr i => joinPiecesLeft right right' i

/-- The trees which must be inserted at the leaves of the second argument to
obtain `join`. -/
def joinPiecesRight : (first second : Tree) → second.Leaf → Tree
  | first, .leaf, _ => first
  | .leaf, .fork _ _, _ => .leaf
  | .fork left _, .fork left' _, Sum.inl i => joinPiecesRight left left' i
  | .fork _ right, .fork _ right', Sum.inr i => joinPiecesRight right right' i

@[simp] theorem expand_joinPiecesLeft : ∀ (first second : Tree),
    expand first (joinPiecesLeft first second) = join first second := by
  intro first
  induction first with
  | leaf => intro second; rfl
  | fork left right ihLeft ihRight =>
      intro second
      cases second with
      | leaf =>
          simp [expand, join, joinPiecesLeft]
      | fork left' right' =>
          simp [expand, join, joinPiecesLeft, ihLeft, ihRight]

@[simp] theorem expand_joinPiecesRight : ∀ (first second : Tree),
    expand second (joinPiecesRight first second) = join first second := by
  intro first
  induction first with
  | leaf =>
      intro second
      induction second with
      | leaf => rfl
      | fork left right ihLeft ihRight =>
          simp [expand, join, joinPiecesRight]
  | fork left right ihLeft ihRight =>
      intro second
      cases second with
      | leaf => rfl
      | fork left' right' =>
          simp [expand, join, joinPiecesRight, ihLeft, ihRight]

/-- A word-replacement table sends each leaf word of `source` to the
corresponding leaf word of `target` and leaves the remaining stream intact. -/
def table (source target : Tree) (e : source.Leaf ≃ target.Leaf) : Equiv.Perm Cantor :=
  (codeEquiv source).trans ((e.prodCongr (Equiv.refl Cantor)).trans (codeEquiv target).symm)

def leafEquivOfEq {source target : Tree} (h : source = target) :
    source.Leaf ≃ target.Leaf :=
  Equiv.cast (congrArg Tree.Leaf h)

theorem table_change_target {source target target' : Tree}
    (e : source.Leaf ≃ target.Leaf) (h : target = target') :
    table source target' (e.trans (leafEquivOfEq h)) = table source target e := by
  cases h
  rfl

theorem table_change_source {source source' target : Tree}
    (e : source.Leaf ≃ target.Leaf) (h : source = source') :
    table source' target ((leafEquivOfEq h).symm.trans e) = table source target e := by
  cases h
  rfl

@[simp] theorem table_apply (source target : Tree) (e : source.Leaf ≃ target.Leaf)
    (x : Cantor) :
    table source target e x = decode target (e (encode source x).1, (encode source x).2) :=
  rfl

/-- Simultaneously refining corresponding source and target leaves does not
change the represented word-replacement permutation. -/
theorem table_expand (source target : Tree) (e : source.Leaf ≃ target.Leaf)
    (pieces : source.Leaf → Tree) :
    table (expand source pieces)
        (expand target (fun j => pieces (e.symm j))) (expandEquiv e pieces) =
      table source target e := by
  apply Equiv.ext
  intro x
  let outer := encode source x
  let inner := encode (pieces outer.1) outer.2
  let targetInner : Σ j : target.Leaf, (pieces (e.symm j)).Leaf :=
    (Equiv.sigmaCongrLeft'
      (β := fun i : source.Leaf => (pieces i).Leaf) e) ⟨outer.1, inner.1⟩
  change decode (expand target (fun j => pieces (e.symm j)))
      (expandEquiv e pieces (encode (expand source pieces) x).1,
        (encode (expand source pieces) x).2) =
    decode target (e outer.1, outer.2)
  have hencode := pack_encode_expand source pieces x
  change
    ((expandedLeafEquiv source pieces) (encode (expand source pieces) x).1,
      (encode (expand source pieces) x).2) =
      (⟨outer.1, inner.1⟩, inner.2) at hencode
  have hdecode := decode_unpack_expand target (fun j => pieces (e.symm j))
    (⟨targetInner, inner.2⟩)
  simp only [nestedDecode] at hdecode
  have hsigma :
      (e.symm.sigmaCongrLeft
          (β := fun i : source.Leaf => (pieces i).Leaf) targetInner :
        Σ i : source.Leaf, (pieces i).Leaf) = ⟨outer.1, inner.1⟩ := by
    exact (e.symm.sigmaCongrLeft
      (β := fun i : source.Leaf => (pieces i).Leaf)).apply_symm_apply
        ⟨outer.1, inner.1⟩
  have hdecoded := congrArg
    (fun q : Σ i : source.Leaf, (pieces i).Leaf =>
      decode target (e q.1, decode (pieces q.1) (q.2, inner.2))) hsigma
  have hdecoded' :
      decode target
          (targetInner.1,
            decode (pieces (e.symm targetInner.1)) (targetInner.2, inner.2)) =
        decode target (e outer.1, outer.2) := by
    rw [Equiv.sigmaCongrLeft_apply] at hdecoded
    simpa [inner] using hdecoded
  have hdecode' :
      decode (expand target (fun j => pieces (e.symm j)))
          ((expandedLeafEquiv target (fun j => pieces (e.symm j))).symm targetInner,
            inner.2) =
        decode target (e outer.1, outer.2) := by
    exact hdecode.trans hdecoded'
  rw [← hdecode']
  congr 2
  · apply (expandedLeafEquiv target (fun j => pieces (e.symm j))).injective
    rw [(expandedLeafEquiv target (fun j => pieces (e.symm j))).apply_symm_apply]
    simp only [expandEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
    have := congrArg Prod.fst hencode
    simpa [targetInner] using congrArg (Equiv.sigmaCongrLeft' e) this
  · exact congrArg Prod.snd hencode

/-- The target-oriented form of `table_expand`. -/
theorem exists_table_expand_target (source target : Tree)
    (e : source.Leaf ≃ target.Leaf) (pieces : target.Leaf → Tree) :
    ∃ e' : (expand source (fun i => pieces (e i))).Leaf ≃
        (expand target pieces).Leaf,
      table (expand source (fun i => pieces (e i))) (expand target pieces) e' =
        table source target e := by
  have h := table_expand source target e (fun i => pieces (e i))
  have hex :
      ∃ e' : (expand source (fun i => pieces (e i))).Leaf ≃
          (expand target (fun j => pieces (e (e.symm j)))).Leaf,
        table (expand source (fun i => pieces (e i)))
            (expand target (fun j => pieces (e (e.symm j)))) e' =
          table source target e :=
    ⟨expandEquiv e (fun i => pieces (e i)), h⟩
  have hfun : (fun j => pieces (e (e.symm j))) = pieces := by
    funext j
    rw [e.apply_symm_apply]
  rw [hfun] at hex
  exact hex

/-- Tables compose directly when the target tree of the right factor is the
source tree of the left factor. -/
theorem table_mul_table_same_middle (source middle target : Tree)
    (e : source.Leaf ≃ middle.Leaf) (f : middle.Leaf ≃ target.Leaf) :
    table middle target f * table source middle e = table source target (e.trans f) := by
  apply Equiv.ext
  intro x
  simp [Equiv.Perm.mul_apply, table_apply]

theorem branchPerm_false_table (source target : Tree) (e : source.Leaf ≃ target.Leaf) :
    Cantor.branchPerm false (table source target e) =
      table (.fork source .leaf) (.fork target .leaf)
        (e.sumCongr (Equiv.refl Unit)) := by
  apply Equiv.ext
  intro x
  cases h : Cantor.head x with
  | false =>
      rw [show x = Cantor.cons false (Cantor.tail x) by
        simpa [h] using (Cantor.cons_head_tail x).symm]
      simp [Cantor.branchPerm, Cantor.branchFun, table_apply, encode, decode]
  | true =>
      rw [show x = Cantor.cons true (Cantor.tail x) by
        simpa [h] using (Cantor.cons_head_tail x).symm]
      simp [Cantor.branchPerm, Cantor.branchFun, table_apply, encode, decode]

theorem branchPerm_true_table (source target : Tree) (e : source.Leaf ≃ target.Leaf) :
    Cantor.branchPerm true (table source target e) =
      table (.fork .leaf source) (.fork .leaf target)
        ((Equiv.refl Unit).sumCongr e) := by
  apply Equiv.ext
  intro x
  cases h : Cantor.head x with
  | false =>
      rw [show x = Cantor.cons false (Cantor.tail x) by
        simpa [h] using (Cantor.cons_head_tail x).symm]
      simp [Cantor.branchPerm, Cantor.branchFun, table_apply, encode, decode]
  | true =>
      rw [show x = Cantor.cons true (Cantor.tail x) by
        simpa [h] using (Cantor.cons_head_tail x).symm]
      simp [Cantor.branchPerm, Cantor.branchFun, table_apply, encode, decode]

@[simp] theorem table_prepend_path (source target : Tree)
    (e : source.Leaf ≃ target.Leaf) (i : source.Leaf) (x : Cantor) :
    table source target e (Cantor.prepend (path source i) x) =
      Cantor.prepend (path target (e i)) x := by
  rw [← decode_eq_prepend source i x]
  simp only [table_apply, encode_decode]
  exact decode_eq_prepend target (e i) x

@[simp] theorem table_prepend_path_append (source target : Tree)
    (e : source.Leaf ≃ target.Leaf) (i : source.Leaf)
    (suffix : List Bool) (x : Cantor) :
    table source target e
        (Cantor.prepend (path source i ++ suffix) x) =
      Cantor.prepend (path target (e i) ++ suffix) x := by
  simpa only [Cantor.prepend_append] using
    table_prepend_path source target e i (Cantor.prepend suffix x)

theorem exists_path_ne_of_table_ne_one (source target : Tree)
    (e : source.Leaf ≃ target.Leaf) (hne : table source target e ≠ 1) :
    ∃ i : source.Leaf, path source i ≠ path target (e i) := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hne
  apply Equiv.ext
  intro x
  let encoded := encode source x
  change decode target (e encoded.1, encoded.2) = x
  rw [decode_eq_prepend, ← h encoded.1, ← decode_eq_prepend]
  exact decode_encode source x

/-- A nonidentity table moves some cylinder rigidly onto a disjoint cylinder. -/
theorem exists_disjoint_cylinder_of_table_ne_one (source target : Tree)
    (e : source.Leaf ≃ target.Leaf) (hne : table source target e ≠ 1) :
    ∃ left right : List Bool,
      Disjoint (Cantor.cylinder left) (Cantor.cylinder right) ∧
        ∀ x : Cantor,
          table source target e (Cantor.prepend left x) =
            Cantor.prepend right x := by
  obtain ⟨i, hi⟩ := exists_path_ne_of_table_ne_one source target e hne
  obtain ⟨suffix, hleft, hright⟩ := Cantor.exists_append_incomparable hi
  refine ⟨path source i ++ suffix, path target (e i) ++ suffix,
    Cantor.cylinder_disjoint_of_incomparable hleft hright, ?_⟩
  exact table_prepend_path_append source target e i suffix

@[simp] theorem table_symm (source target : Tree) (e : source.Leaf ≃ target.Leaf) :
    (table source target e).symm = table target source e.symm := by
  apply Equiv.ext
  intro x
  rfl

@[simp] theorem table_refl (t : Tree) : table t t (Equiv.refl t.Leaf) = 1 := by
  apply Equiv.ext
  intro x
  exact decode_encode t x

/-- The raw set of finite binary word-replacement permutations. -/
def tableSet : Set (Equiv.Perm Cantor) :=
  {g | ∃ (source target : Tree) (e : source.Leaf ≃ target.Leaf),
    g = table source target e}

theorem one_mem_tableSet : (1 : Equiv.Perm Cantor) ∈ tableSet := by
  exact ⟨.leaf, .leaf, Equiv.refl Unit, (table_refl .leaf).symm⟩

theorem inv_mem_tableSet {g : Equiv.Perm Cantor} (hg : g ∈ tableSet) : g⁻¹ ∈ tableSet := by
  rcases hg with ⟨source, target, e, rfl⟩
  refine ⟨target, source, e.symm, ?_⟩
  change (table source target e).symm = table target source e.symm
  exact table_symm source target e

theorem mul_mem_tableSet {g h : Equiv.Perm Cantor}
    (hg : g ∈ tableSet) (hh : h ∈ tableSet) : g * h ∈ tableSet := by
  rcases hg with ⟨sourceG, targetG, eG, rfl⟩
  rcases hh with ⟨sourceH, targetH, eH, rfl⟩
  let piecesH := joinPiecesLeft targetH sourceG
  let piecesG := joinPiecesRight targetH sourceG
  obtain ⟨eH', heH'⟩ := exists_table_expand_target sourceH targetH eH piecesH
  let eG' := expandEquiv eG piecesG
  have heG' := table_expand sourceG targetG eG piecesG
  have hmiddleH : expand targetH piecesH = join targetH sourceG :=
    expand_joinPiecesLeft targetH sourceG
  have hmiddleG : expand sourceG piecesG = join targetH sourceG :=
    expand_joinPiecesRight targetH sourceG
  let eH'' := eH'.trans (leafEquivOfEq hmiddleH)
  have heH'' :
      table (expand sourceH (fun i => piecesH (eH i)))
          (join targetH sourceG) eH'' = table sourceH targetH eH :=
    (table_change_target eH' hmiddleH).trans heH'
  let eG'' := (leafEquivOfEq hmiddleG).symm.trans eG'
  have heG'' :
      table (join targetH sourceG)
          (expand targetG (fun j => piecesG (eG.symm j))) eG'' =
        table sourceG targetG eG :=
    (table_change_source eG' hmiddleG).trans heG'
  refine ⟨expand sourceH (fun i => piecesH (eH i)),
    expand targetG (fun j => piecesG (eG.symm j)), eH''.trans eG'', ?_⟩
  rw [← heG'', ← heH'', table_mul_table_same_middle]

/-- Prefix-replacement tables themselves form a subgroup. -/
def tableSubgroup : Subgroup (Equiv.Perm Cantor) where
  carrier := tableSet
  one_mem' := one_mem_tableSet
  mul_mem' := mul_mem_tableSet
  inv_mem' := inv_mem_tableSet

/-- Thompson's group `V`, initially presented as the subgroup of Cantor-space
permutations generated by all finite word-replacement tables. -/
def V : Subgroup (Equiv.Perm Cantor) := Subgroup.closure tableSet

theorem V_eq_tableSubgroup : V = tableSubgroup := by
  apply le_antisymm
  · exact (Subgroup.closure_le tableSubgroup).2 fun _ h => h
  · exact fun _ h => Subgroup.subset_closure h

theorem mem_V_iff_table {g : Equiv.Perm Cantor} :
    g ∈ V ↔ ∃ (source target : Tree) (e : source.Leaf ≃ target.Leaf),
      g = table source target e := by
  rw [V_eq_tableSubgroup]
  rfl

theorem localPerm_mem_tableSet (word : List Bool) {g : Equiv.Perm Cantor}
    (hg : g ∈ tableSet) : Cantor.localPerm word g ∈ tableSet := by
  induction word with
  | nil => exact hg
  | cons b word ih =>
      rcases ih with ⟨source, target, e, heq⟩
      change Cantor.branchPerm b (Cantor.localPerm word g) ∈ tableSet
      rw [heq]
      cases b
      · exact ⟨.fork source .leaf, .fork target .leaf,
          e.sumCongr (Equiv.refl Unit), branchPerm_false_table source target e⟩
      · exact ⟨.fork .leaf source, .fork .leaf target,
          (Equiv.refl Unit).sumCongr e, branchPerm_true_table source target e⟩

theorem localPerm_mem_V (word : List Bool) {g : Equiv.Perm Cantor}
    (hg : g ∈ V) : Cantor.localPerm word g ∈ V := by
  rw [V_eq_tableSubgroup] at hg ⊢
  exact localPerm_mem_tableSet word hg

/-- Localization restricts to an injective endomorphism of `V`. -/
def localVHom (word : List Bool) : V →* V where
  toFun g := ⟨Cantor.localPerm word g, localPerm_mem_V word g.2⟩
  map_one' := Subtype.ext (Cantor.localPerm_one word)
  map_mul' g h := Subtype.ext (Cantor.localPerm_mul word g h)

theorem localVHom_injective (word : List Bool) : Function.Injective (localVHom word) := by
  intro g h heq
  apply Subtype.ext
  exact Cantor.localPerm_injective word (congrArg Subtype.val heq)

theorem table_mem_V (source target : Tree) (e : source.Leaf ≃ target.Leaf) :
    table source target e ∈ V :=
  Subgroup.subset_closure ⟨source, target, e, rfl⟩

/-- A word-replacement table regarded as an element of `V`.  Keeping this
constructor named lets composition be stated as an equality in the subtype,
so subgroup-membership proofs do not depend on proof irrelevance rewrites. -/
def tableElement (source target : Tree) (e : source.Leaf ≃ target.Leaf) : V :=
  ⟨table source target e, table_mem_V source target e⟩

@[simp] theorem tableElement_mul (source middle target : Tree)
    (e : source.Leaf ≃ middle.Leaf) (f : middle.Leaf ≃ target.Leaf) :
    tableElement middle target f * tableElement source middle e =
      tableElement source target (e.trans f) := by
  apply Subtype.ext
  exact table_mul_table_same_middle source middle target e f

@[simp] theorem tableElement_inv (source target : Tree)
    (e : source.Leaf ≃ target.Leaf) :
    (tableElement source target e)⁻¹ = tableElement target source e.symm := by
  apply Subtype.ext
  exact table_symm source target e

/-- Permuting the leaves of a fixed tree gives a homomorphism into `V`. -/
def leafPermHom (t : Tree) : Equiv.Perm t.Leaf →* V where
  toFun e := ⟨table t t e, table_mem_V t t e⟩
  map_one' := Subtype.ext (table_refl t)
  map_mul' e f := Subtype.ext <| by
    change table t t (e * f) = table t t e * table t t f
    rw [table_mul_table_same_middle]
    rfl

/-- A fixed six-leaf tree, used to replace every leaf by an even number of
copies while retaining at least five leaves. -/
def sixTree : Tree :=
  .fork .leaf (.fork .leaf (.fork .leaf (.fork .leaf (.fork .leaf .leaf))))

@[simp] theorem card_sixTree_leaf : Fintype.card sixTree.Leaf = 6 := by
  change Fintype.card (Unit ⊕ Unit ⊕ Unit ⊕ Unit ⊕ Unit ⊕ Unit) = 6
  norm_num [Fintype.card_sum]

theorem five_le_card_expand_six (t : Tree) :
    5 ≤ Nat.card (expand t (fun _ => sixTree)).Leaf := by
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (expandedLeafEquiv t (fun _ => sixTree))]
  simp only [Fintype.card_sigma, card_sixTree_leaf, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hpos : 0 < Fintype.card t.Leaf := Fintype.card_pos
  nlinarith

theorem sign_expandEquiv_six (t : Tree) (e : Equiv.Perm t.Leaf) :
    Equiv.Perm.sign (expandEquiv e (fun _ => sixTree)) = 1 := by
  let expanded := expandEquiv e (fun _ => sixTree)
  let productPerm : Equiv.Perm (t.Leaf × sixTree.Leaf) :=
    e.prodCongr (Equiv.refl sixTree.Leaf)
  let conjugating : (expand t (fun _ => sixTree)).Leaf ≃
      t.Leaf × sixTree.Leaf :=
    (expandedLeafEquiv t (fun _ => sixTree)).trans
      (Equiv.sigmaEquivProd t.Leaf sixTree.Leaf)
  have hsigma (q : Σ _ : t.Leaf, sixTree.Leaf) :
      (Equiv.sigmaCongrLeft' (β := fun _ : t.Leaf => sixTree.Leaf) e) q =
        e.sigmaCongrLeft (β := fun _ : t.Leaf => sixTree.Leaf) q := by
    change (e.symm.sigmaCongrLeft
        (β := fun _ : t.Leaf => sixTree.Leaf)).symm q =
      e.sigmaCongrLeft (β := fun _ : t.Leaf => sixTree.Leaf) q
    apply (e.symm.sigmaCongrLeft
      (β := fun _ : t.Leaf => sixTree.Leaf)).injective
    rw [(e.symm.sigmaCongrLeft
      (β := fun _ : t.Leaf => sixTree.Leaf)).apply_symm_apply]
    simp only [Equiv.sigmaCongrLeft_apply, e.symm_apply_apply]
  have hconj : ∀ x, conjugating (expanded x) = productPerm (conjugating x) := by
    rintro x
    simp [conjugating, expanded, productPerm, expandEquiv, hsigma]
  rw [Equiv.Perm.sign_eq_sign_of_equiv expanded productPerm conjugating hconj]
  have hproduct : productPerm = Equiv.prodCongrLeft (fun _ : sixTree.Leaf => e) := by
    apply Equiv.ext
    intro x
    rfl
  rw [hproduct, Equiv.Perm.sign_prodCongrLeft]
  simp only [Finset.prod_const]
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with hsign | hsign
  · simp [hsign]
  · norm_num [hsign]

theorem expandEquiv_six_mem_commutator (t : Tree) (e : Equiv.Perm t.Leaf) :
    expandEquiv e (fun _ => sixTree) ∈
      commutator (Equiv.Perm (expand t (fun _ => sixTree)).Leaf) := by
  rw [alternatingGroup.commutator_perm_eq (five_le_card_expand_six t)]
  exact (Equiv.Perm.mem_alternatingGroup).2 (sign_expandEquiv_six t e)

/-- Every permutation of the leaves of one fixed tree already lies in the
commutator subgroup of `V`. -/
theorem table_same_tree_mem_commutator (t : Tree) (e : Equiv.Perm t.Leaf) :
    (⟨table t t e, table_mem_V t t e⟩ : V) ∈ commutator V := by
  have hmapped := map_mem_commutator
    (leafPermHom (expand t (fun _ => sixTree)))
    (expandEquiv_six_mem_commutator t e)
  have heq :
      (⟨table (expand t (fun _ => sixTree)) (expand t (fun _ => sixTree))
          (expandEquiv e (fun _ => sixTree)),
        table_mem_V _ _ _⟩ : V) =
        (⟨table t t e, table_mem_V t t e⟩ : V) := by
    apply Subtype.ext
    exact table_expand t t e (fun _ => sixTree)
  rw [← heq]
  exact hmapped

def rotationSource : Tree := .fork (.fork .leaf .leaf) .leaf

def rotationTarget : Tree := .fork .leaf (.fork .leaf .leaf)

def rotationEquiv : rotationSource.Leaf ≃ rotationTarget.Leaf :=
  Equiv.sumAssoc Unit Unit Unit

def sourceEndSwap : Equiv.Perm rotationSource.Leaf :=
  { toFun := fun i =>
      match i with
      | Sum.inl (Sum.inl _) => Sum.inr ()
      | Sum.inl (Sum.inr _) => Sum.inl (Sum.inr ())
      | Sum.inr _ => Sum.inl (Sum.inl ())
    invFun := fun i =>
      match i with
      | Sum.inl (Sum.inl _) => Sum.inr ()
      | Sum.inl (Sum.inr _) => Sum.inl (Sum.inr ())
      | Sum.inr _ => Sum.inl (Sum.inl ())
    left_inv := by rintro ((i | i) | i) <;> cases i <;> rfl
    right_inv := by rintro ((i | i) | i) <;> cases i <;> rfl }

def targetEndSwap : Equiv.Perm rotationTarget.Leaf :=
  { toFun := fun i =>
      match i with
      | Sum.inl _ => Sum.inl ()
      | Sum.inr (Sum.inl _) => Sum.inr (Sum.inr ())
      | Sum.inr (Sum.inr _) => Sum.inr (Sum.inl ())
    invFun := fun i =>
      match i with
      | Sum.inl _ => Sum.inl ()
      | Sum.inr (Sum.inl _) => Sum.inr (Sum.inr ())
      | Sum.inr (Sum.inr _) => Sum.inr (Sum.inl ())
    left_inv := by rintro (i | (i | i)) <;> cases i <;> rfl
    right_inv := by rintro (i | (i | i)) <;> cases i <;> rfl }

@[simp] theorem sourceEndSwap_left_left :
    sourceEndSwap (Sum.inl (Sum.inl ())) = Sum.inr () := rfl

@[simp] theorem sourceEndSwap_left_right :
    sourceEndSwap (Sum.inl (Sum.inr ())) = Sum.inl (Sum.inr ()) := rfl

@[simp] theorem sourceEndSwap_right :
    sourceEndSwap (Sum.inr ()) = Sum.inl (Sum.inl ()) := rfl

@[simp] theorem targetEndSwap_left :
    targetEndSwap (Sum.inl ()) = Sum.inl () := rfl

@[simp] theorem targetEndSwap_right_left :
    targetEndSwap (Sum.inr (Sum.inl ())) = Sum.inr (Sum.inr ()) := rfl

@[simp] theorem targetEndSwap_right_right :
    targetEndSwap (Sum.inr (Sum.inr ())) = Sum.inr (Sum.inl ()) := rfl

@[simp] theorem rotationEquiv_left_left :
    rotationEquiv (Sum.inl (Sum.inl ())) = Sum.inl () := rfl

@[simp] theorem rotationEquiv_left_right :
    rotationEquiv (Sum.inl (Sum.inr ())) = Sum.inr (Sum.inl ()) := rfl

@[simp] theorem rotationEquiv_right :
    rotationEquiv (Sum.inr ()) = Sum.inr (Sum.inr ()) := rfl

@[simp] theorem rotationEquiv_symm_left :
    rotationEquiv.symm (Sum.inl ()) = Sum.inl (Sum.inl ()) := rfl

@[simp] theorem rotationEquiv_symm_right_left :
    rotationEquiv.symm (Sum.inr (Sum.inl ())) = Sum.inl (Sum.inr ()) := rfl

@[simp] theorem rotationEquiv_symm_right_right :
    rotationEquiv.symm (Sum.inr (Sum.inr ())) = Sum.inr () := rfl

/-- The elementary associativity rotation is a product of three leaf
permutations (on the source tree, the top fork, and the target tree). -/
theorem rotation_factorization :
    table rotationTarget rotationTarget targetEndSwap *
        table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit) *
      table rotationSource rotationSource sourceEndSwap =
        table rotationSource rotationTarget rotationEquiv := by
  apply Equiv.ext
  intro x
  generalize hp : encode rotationSource x = p
  rcases p with ⟨i, z⟩
  have hx : x = decode rotationSource (i, z) := by
    rw [← hp, decode_encode]
  rw [hx, decode_eq_prepend]
  rcases i with ((i | i) | i) <;> cases i
  · have hC := table_prepend_path rotationSource rotationSource sourceEndSwap
        (Sum.inl (Sum.inl ())) z
    rw [sourceEndSwap_left_left] at hC
    have hpCB : path rotationSource (Sum.inr ()) =
        path (.fork .leaf .leaf) (Sum.inr ()) := rfl
    rw [hpCB] at hC
    have hB := table_prepend_path (.fork .leaf .leaf) (.fork .leaf .leaf)
      (Equiv.sumComm Unit Unit) (Sum.inr ()) z
    have hswap : (Equiv.sumComm Unit Unit) (Sum.inr ()) = Sum.inl () := rfl
    rw [hswap] at hB
    have hpBA : path (.fork .leaf .leaf) (Sum.inl ()) =
        path rotationTarget (Sum.inl ()) := rfl
    rw [hpBA] at hB
    have hA := table_prepend_path rotationTarget rotationTarget targetEndSwap
      (Sum.inl ()) z
    rw [targetEndSwap_left] at hA
    have hR := table_prepend_path rotationSource rotationTarget rotationEquiv
      (Sum.inl (Sum.inl ())) z
    rw [rotationEquiv_left_left] at hR
    simpa only [Equiv.Perm.mul_apply] using
      (calc
        table rotationTarget rotationTarget targetEndSwap
              (table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit)
                (table rotationSource rotationSource sourceEndSwap
                  (Cantor.prepend (path rotationSource (Sum.inl (Sum.inl ()))) z))) =
            table rotationTarget rotationTarget targetEndSwap
              (table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit)
                (Cantor.prepend (path (.fork .leaf .leaf) (Sum.inr ())) z)) :=
          congrArg (fun y => table rotationTarget rotationTarget targetEndSwap
            (table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit) y)) hC
        _ = table rotationTarget rotationTarget targetEndSwap
              (Cantor.prepend (path rotationTarget (Sum.inl ())) z) := congrArg _ hB
        _ = Cantor.prepend (path rotationTarget (Sum.inl ())) z := hA
        _ = table rotationSource rotationTarget rotationEquiv
              (Cantor.prepend (path rotationSource (Sum.inl (Sum.inl ()))) z) := hR.symm)
  · have hC := table_prepend_path rotationSource rotationSource sourceEndSwap
        (Sum.inl (Sum.inr ())) z
    rw [sourceEndSwap_left_right] at hC
    have hpCB : path rotationSource (Sum.inl (Sum.inr ())) =
        path (.fork .leaf .leaf) (Sum.inl ()) ++ [true] := rfl
    rw [hpCB] at hC
    have hB := table_prepend_path_append (.fork .leaf .leaf) (.fork .leaf .leaf)
      (Equiv.sumComm Unit Unit) (Sum.inl ()) [true] z
    have hswap : (Equiv.sumComm Unit Unit) (Sum.inl ()) = Sum.inr () := rfl
    rw [hswap] at hB
    have hpBA : path (.fork .leaf .leaf) (Sum.inr ()) ++ [true] =
        path rotationTarget (Sum.inr (Sum.inr ())) := rfl
    rw [hpBA] at hB
    have hA := table_prepend_path rotationTarget rotationTarget targetEndSwap
      (Sum.inr (Sum.inr ())) z
    rw [targetEndSwap_right_right] at hA
    have hR := table_prepend_path rotationSource rotationTarget rotationEquiv
      (Sum.inl (Sum.inr ())) z
    rw [rotationEquiv_left_right] at hR
    simpa only [Equiv.Perm.mul_apply] using
      (calc
        table rotationTarget rotationTarget targetEndSwap
              (table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit)
                (table rotationSource rotationSource sourceEndSwap
                  (Cantor.prepend (path rotationSource (Sum.inl (Sum.inr ()))) z))) =
            table rotationTarget rotationTarget targetEndSwap
              (table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit)
                (Cantor.prepend (path (.fork .leaf .leaf) (Sum.inl ()) ++ [true]) z)) :=
          congrArg (fun y => table rotationTarget rotationTarget targetEndSwap
            (table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit) y)) hC
        _ = table rotationTarget rotationTarget targetEndSwap
              (Cantor.prepend (path rotationTarget (Sum.inr (Sum.inr ()))) z) := congrArg _ hB
        _ = Cantor.prepend (path rotationTarget (Sum.inr (Sum.inl ()))) z := hA
        _ = table rotationSource rotationTarget rotationEquiv
              (Cantor.prepend (path rotationSource (Sum.inl (Sum.inr ()))) z) := hR.symm)
  · have hC := table_prepend_path rotationSource rotationSource sourceEndSwap
      (Sum.inr ()) z
    rw [sourceEndSwap_right] at hC
    have hpCB : path rotationSource (Sum.inl (Sum.inl ())) =
        path (.fork .leaf .leaf) (Sum.inl ()) ++ [false] := rfl
    rw [hpCB] at hC
    have hB := table_prepend_path_append (.fork .leaf .leaf) (.fork .leaf .leaf)
      (Equiv.sumComm Unit Unit) (Sum.inl ()) [false] z
    have hswap : (Equiv.sumComm Unit Unit) (Sum.inl ()) = Sum.inr () := rfl
    rw [hswap] at hB
    have hpBA : path (.fork .leaf .leaf) (Sum.inr ()) ++ [false] =
        path rotationTarget (Sum.inr (Sum.inl ())) := rfl
    rw [hpBA] at hB
    have hA := table_prepend_path rotationTarget rotationTarget targetEndSwap
      (Sum.inr (Sum.inl ())) z
    rw [targetEndSwap_right_left] at hA
    have hR := table_prepend_path rotationSource rotationTarget rotationEquiv
      (Sum.inr ()) z
    rw [rotationEquiv_right] at hR
    simpa only [Equiv.Perm.mul_apply] using
      (calc
        table rotationTarget rotationTarget targetEndSwap
              (table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit)
                (table rotationSource rotationSource sourceEndSwap
                  (Cantor.prepend (path rotationSource (Sum.inr ())) z))) =
            table rotationTarget rotationTarget targetEndSwap
              (table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit)
                (Cantor.prepend (path (.fork .leaf .leaf) (Sum.inl ()) ++ [false]) z)) :=
          congrArg (fun y => table rotationTarget rotationTarget targetEndSwap
            (table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit) y)) hC
        _ = table rotationTarget rotationTarget targetEndSwap
              (Cantor.prepend (path rotationTarget (Sum.inr (Sum.inl ()))) z) := congrArg _ hB
        _ = Cantor.prepend (path rotationTarget (Sum.inr (Sum.inr ()))) z := hA
        _ = table rotationSource rotationTarget rotationEquiv
              (Cantor.prepend (path rotationSource (Sum.inr ())) z) := hR.symm)

theorem rotation_mem_commutator :
    (⟨table rotationSource rotationTarget rotationEquiv,
      table_mem_V rotationSource rotationTarget rotationEquiv⟩ : V) ∈ commutator V := by
  let targetElement : V :=
    ⟨table rotationTarget rotationTarget targetEndSwap, table_mem_V _ _ _⟩
  let topElement : V :=
    ⟨table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit),
      table_mem_V _ _ _⟩
  let sourceElement : V :=
    ⟨table rotationSource rotationSource sourceEndSwap, table_mem_V _ _ _⟩
  let rotationElement : V :=
    ⟨table rotationSource rotationTarget rotationEquiv, table_mem_V _ _ _⟩
  have hprod : targetElement * topElement * sourceElement ∈ commutator V :=
    (commutator V).mul_mem
    ((commutator V).mul_mem
      (table_same_tree_mem_commutator rotationTarget targetEndSwap)
      (table_same_tree_mem_commutator (.fork .leaf .leaf)
        (Equiv.sumComm Unit Unit)))
    (table_same_tree_mem_commutator rotationSource sourceEndSwap)
  have heq : targetElement * topElement * sourceElement = rotationElement := by
    apply Subtype.ext
    exact rotation_factorization
  change rotationElement ∈ commutator V
  rw [← heq]
  exact hprod

def rotationPieces (a b c : Tree) : rotationSource.Leaf → Tree
  | Sum.inl (Sum.inl _) => a
  | Sum.inl (Sum.inr _) => b
  | Sum.inr _ => c

theorem expand_rotationSource (a b c : Tree) :
    expand rotationSource (rotationPieces a b c) =
      Tree.fork (Tree.fork a b) c := by
  rfl

theorem expand_rotationTarget (a b c : Tree) :
    expand rotationTarget (fun j => rotationPieces a b c (rotationEquiv.symm j)) =
      Tree.fork a (Tree.fork b c) := by
  change Tree.fork
    (rotationPieces a b c (rotationEquiv.symm (Sum.inl ())))
    (Tree.fork
      (rotationPieces a b c (rotationEquiv.symm (Sum.inr (Sum.inl ()))))
      (rotationPieces a b c (rotationEquiv.symm (Sum.inr (Sum.inr ()))))) =
      Tree.fork a (Tree.fork b c)
  rw [rotationEquiv_symm_left, rotationEquiv_symm_right_left,
    rotationEquiv_symm_right_right]
  rfl

/-- The leaf equivalence associated to an associativity rotation of three
arbitrary subtrees. -/
def assocEquiv (a b c : Tree) :
    (Tree.fork (Tree.fork a b) c).Leaf ≃
      (Tree.fork a (Tree.fork b c)).Leaf := by
  let raw := expandEquiv rotationEquiv (rotationPieces a b c)
  exact (leafEquivOfEq (expand_rotationSource a b c)).symm.trans
    (raw.trans (leafEquivOfEq (expand_rotationTarget a b c)))

theorem table_assocEquiv (a b c : Tree) :
    table (.fork (.fork a b) c) (.fork a (.fork b c)) (assocEquiv a b c) =
      table rotationSource rotationTarget rotationEquiv := by
  let raw := expandEquiv rotationEquiv (rotationPieces a b c)
  have hraw := table_expand rotationSource rotationTarget rotationEquiv
    (rotationPieces a b c)
  have htarget := table_change_target raw (expand_rotationTarget a b c)
  have hsource := table_change_source
    (raw.trans (leafEquivOfEq (expand_rotationTarget a b c)))
    (expand_rotationSource a b c)
  exact hsource.trans (htarget.trans hraw)

theorem table_assoc_mem_commutator (a b c : Tree) :
    (⟨table (.fork (.fork a b) c) (.fork a (.fork b c)) (assocEquiv a b c),
      table_mem_V _ _ _⟩ : V) ∈ commutator V := by
  simpa only [table_assocEquiv] using rotation_mem_commutator

/-- A table on a fork is the product of the two tables localized to its left
and right cylinders. -/
theorem table_fork (sourceLeft sourceRight targetLeft targetRight : Tree)
    (eLeft : sourceLeft.Leaf ≃ targetLeft.Leaf)
    (eRight : sourceRight.Leaf ≃ targetRight.Leaf) :
    table (.fork sourceLeft sourceRight) (.fork targetLeft targetRight)
        (eLeft.sumCongr eRight) =
      Cantor.branchPerm false (table sourceLeft targetLeft eLeft) *
        Cantor.branchPerm true (table sourceRight targetRight eRight) := by
  apply Equiv.ext
  intro x
  cases h : Cantor.head x with
  | false =>
      rw [show x = Cantor.cons false (Cantor.tail x) by
        simpa [h] using (Cantor.cons_head_tail x).symm]
      simp [Equiv.Perm.mul_apply, Cantor.branchPerm, Cantor.branchFun, table_apply,
        encode, decode]
  | true =>
      rw [show x = Cantor.cons true (Cantor.tail x) by
        simpa [h] using (Cantor.cons_head_tail x).symm]
      simp [Equiv.Perm.mul_apply, Cantor.branchPerm, Cantor.branchFun, table_apply,
        encode, decode]

theorem table_fork_mem_commutator
    (sourceLeft sourceRight targetLeft targetRight : Tree)
    (eLeft : sourceLeft.Leaf ≃ targetLeft.Leaf)
    (eRight : sourceRight.Leaf ≃ targetRight.Leaf)
    (hLeft : (⟨table sourceLeft targetLeft eLeft, table_mem_V _ _ _⟩ : V) ∈
      commutator V)
    (hRight : (⟨table sourceRight targetRight eRight, table_mem_V _ _ _⟩ : V) ∈
      commutator V) :
    (⟨table (.fork sourceLeft sourceRight) (.fork targetLeft targetRight)
        (eLeft.sumCongr eRight), table_mem_V _ _ _⟩ : V) ∈ commutator V := by
  let leftElement : V :=
    ⟨table sourceLeft targetLeft eLeft, table_mem_V _ _ _⟩
  let rightElement : V :=
    ⟨table sourceRight targetRight eRight, table_mem_V _ _ _⟩
  let forkElement : V :=
    ⟨table (.fork sourceLeft sourceRight) (.fork targetLeft targetRight)
      (eLeft.sumCongr eRight), table_mem_V _ _ _⟩
  have hLocalLeft := map_mem_commutator (localVHom [false]) hLeft
  have hLocalRight := map_mem_commutator (localVHom [true]) hRight
  have heq : forkElement = localVHom [false] leftElement * localVHom [true] rightElement := by
    apply Subtype.ext
    simpa [forkElement, leftElement, rightElement, localVHom, Cantor.localPerm] using
      table_fork sourceLeft sourceRight targetLeft targetRight eLeft eRight
  change forkElement ∈ commutator V
  rw [heq]
  exact (commutator V).mul_mem hLocalLeft hLocalRight

/-- The right-associated binary tree with `n + 1` leaves. -/
def rightVine : ℕ → Tree
  | 0 => .leaf
  | n + 1 => .fork .leaf (rightVine n)

@[simp] theorem card_rightVine_leaf (n : ℕ) :
    Fintype.card (rightVine n).Leaf = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Fintype.card (Unit ⊕ (rightVine n).Leaf) = n + 1 + 1
      rw [Fintype.card_sum, ih]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- Two right vines can be merged, using associativity rotations, into one
right vine by a table in the commutator subgroup. -/
theorem exists_vine_merge : ∀ m n : ℕ,
    ∃ (k : ℕ) (e : (Tree.fork (rightVine m) (rightVine n)).Leaf ≃
      (rightVine k).Leaf),
      (⟨table (.fork (rightVine m) (rightVine n)) (rightVine k) e,
        table_mem_V _ _ _⟩ : V) ∈ commutator V := by
  intro m
  induction m with
  | zero =>
      intro n
      refine ⟨n + 1, Equiv.refl (rightVine (n + 1)).Leaf, ?_⟩
      simpa [rightVine] using
        table_same_tree_mem_commutator (rightVine (n + 1))
          (Equiv.refl (rightVine (n + 1)).Leaf)
  | succ m ih =>
      intro n
      obtain ⟨k, e, he⟩ := ih n
      let rotation := assocEquiv .leaf (rightVine m) (rightVine n)
      let forkEquiv := (Equiv.refl Unit).sumCongr e
      have hrotation := table_assoc_mem_commutator .leaf (rightVine m) (rightVine n)
      have hfork := table_fork_mem_commutator .leaf
        (.fork (rightVine m) (rightVine n)) .leaf (rightVine k)
        (Equiv.refl Unit) e
        (table_same_tree_mem_commutator .leaf (Equiv.refl Unit)) he
      refine ⟨k + 1, rotation.trans forkEquiv, ?_⟩
      have hproduct := (commutator V).mul_mem hfork hrotation
      change tableElement (.fork (.fork .leaf (rightVine m)) (rightVine n))
        (rightVine (k + 1)) (rotation.trans forkEquiv) ∈ commutator V
      change tableElement (.fork .leaf (.fork (rightVine m) (rightVine n)))
          (rightVine (k + 1)) forkEquiv *
        tableElement (.fork (.fork .leaf (rightVine m)) (rightVine n))
          (.fork .leaf (.fork (rightVine m) (rightVine n))) rotation ∈
          commutator V at hproduct
      rw [tableElement_mul] at hproduct
      exact hproduct

/-- Every tree can be changed to a right vine by a table in the commutator
subgroup. -/
theorem exists_vine_normalization : ∀ t : Tree,
    ∃ (n : ℕ) (e : t.Leaf ≃ (rightVine n).Leaf),
      (⟨table t (rightVine n) e, table_mem_V _ _ _⟩ : V) ∈ commutator V := by
  intro t
  induction t with
  | leaf =>
      refine ⟨0, Equiv.refl Unit, ?_⟩
      exact table_same_tree_mem_commutator .leaf (Equiv.refl Unit)
  | fork left right ihLeft ihRight =>
      obtain ⟨m, eLeft, hLeft⟩ := ihLeft
      obtain ⟨n, eRight, hRight⟩ := ihRight
      obtain ⟨k, eMerge, hMerge⟩ := exists_vine_merge m n
      let forkEquiv := eLeft.sumCongr eRight
      have hfork := table_fork_mem_commutator left right (rightVine m) (rightVine n)
        eLeft eRight hLeft hRight
      refine ⟨k, forkEquiv.trans eMerge, ?_⟩
      have hproduct := (commutator V).mul_mem hMerge hfork
      change tableElement (.fork left right) (rightVine k)
        (forkEquiv.trans eMerge) ∈ commutator V
      change tableElement (.fork (rightVine m) (rightVine n)) (rightVine k)
          eMerge *
        tableElement (.fork left right) (.fork (rightVine m) (rightVine n))
          forkEquiv ∈ commutator V at hproduct
      rw [tableElement_mul] at hproduct
      exact hproduct

/-- Every word-replacement table lies in the commutator subgroup. -/
theorem table_mem_commutator (source target : Tree)
    (e : source.Leaf ≃ target.Leaf) :
    (⟨table source target e, table_mem_V _ _ _⟩ : V) ∈ commutator V := by
  change tableElement source target e ∈ commutator V
  obtain ⟨m, eSource, hSource⟩ := exists_vine_normalization source
  obtain ⟨n, eTarget, hTarget⟩ := exists_vine_normalization target
  have hSourceCard : Fintype.card source.Leaf = m + 1 :=
    (Fintype.card_congr eSource).trans (card_rightVine_leaf m)
  have hTargetCard : Fintype.card target.Leaf = n + 1 :=
    (Fintype.card_congr eTarget).trans (card_rightVine_leaf n)
  have hEqualCard : Fintype.card source.Leaf = Fintype.card target.Leaf :=
    Fintype.card_congr e
  have hmn : m = n := by omega
  subst n
  let shape := eSource.trans eTarget.symm
  have hTargetInv :
      tableElement (rightVine m) target eTarget.symm ∈ commutator V := by
    have hinv := (commutator V).inv_mem hTarget
    change (tableElement target (rightVine m) eTarget)⁻¹ ∈
      commutator V at hinv
    rw [tableElement_inv] at hinv
    exact hinv
  have hShape :
      tableElement source target shape ∈ commutator V := by
    have hproduct := (commutator V).mul_mem hTargetInv hSource
    change tableElement (rightVine m) target eTarget.symm *
      tableElement source (rightVine m) eSource ∈ commutator V at hproduct
    rw [tableElement_mul] at hproduct
    exact hproduct
  let adjust : Equiv.Perm target.Leaf := shape.symm.trans e
  have hAdjust := table_same_tree_mem_commutator target adjust
  have hproduct := (commutator V).mul_mem hAdjust hShape
  change tableElement target target adjust * tableElement source target shape ∈
    commutator V at hproduct
  rw [tableElement_mul] at hproduct
  simpa only [adjust, ← Equiv.trans_assoc, Equiv.self_trans_symm,
    Equiv.refl_trans] using hproduct

instance : Group.IsPerfect V where
  commutator_eq_top := by
    apply top_unique
    intro g _
    obtain ⟨source, target, e, heq⟩ := (mem_V_iff_table).1 g.2
    have hg : g = (⟨table source target e, table_mem_V _ _ _⟩ : V) :=
      Subtype.ext heq
    rw [hg]
    exact table_mem_commutator source target e

/-- A nontrivial element of a normal subgroup forces that subgroup to contain
a localized copy of all of `V`. -/
theorem normal_contains_local_copy (N : Subgroup V) (hNormal : N.Normal)
    (g : V) (hg : g ∈ N) (hne : g ≠ 1) :
    ∃ left : List Bool, left ≠ [] ∧ ∀ a : V, localVHom left a ∈ N := by
  obtain ⟨source, target, e, heq⟩ := (mem_V_iff_table).1 g.2
  have htable : table source target e ≠ 1 := by
    intro h
    apply hne
    apply Subtype.ext
    rw [heq, h]
    rfl
  obtain ⟨left, right, hdisjoint, hmapTable⟩ :=
    exists_disjoint_cylinder_of_table_ne_one source target e htable
  have hmap : ∀ x : Cantor,
      (g : Equiv.Perm Cantor) (Cantor.prepend left x) = Cantor.prepend right x := by
    intro x
    rw [heq]
    exact hmapTable x
  have hleft : left ≠ [] := by
    intro hnil
    subst left
    let base : Cantor := fun _ => false
    have hAll : Cantor.prepend right base ∈ Cantor.cylinder [] := by
      simp [Cantor.cylinder]
    have hRight : Cantor.prepend right base ∈ Cantor.cylinder right :=
      ⟨base, rfl⟩
    exact Set.disjoint_left.1 hdisjoint hAll hRight
  have hcommutators : ∀ a b : V,
      ⁅localVHom left a, localVHom left b⁆ ∈ N := by
    intro a b
    let A := localVHom left a
    let B := localVHom left b
    let R := localVHom right b⁻¹
    have hconj : g * B⁻¹ * g⁻¹ = R := by
      apply Subtype.ext
      simpa [B, R, localVHom, Cantor.localHom] using
        Cantor.conjugate_localPerm_of_map_prepend
          (g : Equiv.Perm Cantor) ((b : V) : Equiv.Perm Cantor)⁻¹ hmap
    have hcommLocal : Commute A R := by
      apply Subtype.ext
      exact (Cantor.localPerm_commute_of_disjoint hdisjoint
        ((a : V) : Equiv.Perm Cantor) (((b : V) : Equiv.Perm Cantor)⁻¹)).eq
    have hcommConj : Commute A (g * B⁻¹ * g⁻¹) := by
      rw [hconj]
      exact hcommLocal
    have hInner : ⁅B, g⁆ ∈ N := by
      rw [commutatorElement_def]
      exact N.mul_mem (hNormal.conj_mem g hg B) (N.inv_mem hg)
    have hOuter : ⁅A, ⁅B, g⁆⁆ ∈ N := by
      rw [commutatorElement_def]
      exact N.mul_mem (hNormal.conj_mem _ hInner A) (N.inv_mem hInner)
    rw [double_commutator_eq_of_commute_conjugate A B g hcommConj] at hOuter
    exact hOuter
  refine ⟨left, hleft, ?_⟩
  intro a
  have hmapComm : (commutator V).map (localVHom left) ≤ N := by
    rw [commutator_def, Subgroup.map_commutator]
    apply Subgroup.commutator_le.mpr
    rintro _ ⟨a, _, rfl⟩ _ ⟨b, _, rfl⟩
    exact hcommutators a b
  apply hmapComm
  exact Subgroup.mem_map_of_mem (localVHom left) (by simp)

theorem normal_contains_false_copy (N : Subgroup V) (hNormal : N.Normal)
    (g : V) (hg : g ∈ N) (hne : g ≠ 1) :
    ∀ a : V, localVHom [false] a ∈ N := by
  obtain ⟨left, hleft, hLocal⟩ := normal_contains_local_copy N hNormal g hg hne
  have hlength : 0 < left.length := by
    cases left with
    | nil => exact (hleft rfl).elim
    | cons _ _ => simp
  have hcard : Fintype.card (prefixTree left).Leaf =
      Fintype.card (Tree.fork Tree.leaf (rightVine (left.length - 1))).Leaf := by
    rw [card_prefixTree_leaf]
    change left.length + 1 =
      Fintype.card (Unit ⊕ (rightVine (left.length - 1)).Leaf)
    rw [Fintype.card_sum, card_rightVine_leaf]
    simp only [Fintype.card_unit]
    omega
  obtain ⟨e, he⟩ := exists_equiv_apply_eq hcard (prefixLeaf left) (Sum.inl ())
  let conjugator : V :=
    ⟨table (prefixTree left) (.fork .leaf (rightVine (left.length - 1))) e,
      table_mem_V _ _ _⟩
  have hmap : ∀ x : Cantor,
      (conjugator : Equiv.Perm Cantor) (Cantor.prepend left x) =
        Cantor.prepend [false] x := by
    intro x
    simpa [conjugator, he, Tree.path] using
      table_prepend_path (prefixTree left)
        (.fork .leaf (rightVine (left.length - 1))) e (prefixLeaf left) x
  intro a
  have hmem := hNormal.conj_mem (localVHom left a) (hLocal a) conjugator
  have heq : conjugator * localVHom left a * conjugator⁻¹ =
      localVHom [false] a := by
    apply Subtype.ext
    simpa [conjugator, localVHom, Cantor.localHom] using
      Cantor.conjugate_localPerm_of_map_prepend
        (conjugator : Equiv.Perm Cantor) ((a : V) : Equiv.Perm Cantor) hmap
  rwa [heq] at hmem

def siblingSwap : Equiv.Perm rotationSource.Leaf where
  toFun
    | Sum.inl (Sum.inl _) => Sum.inl (Sum.inr ())
    | Sum.inl (Sum.inr _) => Sum.inl (Sum.inl ())
    | Sum.inr _ => Sum.inr ()
  invFun
    | Sum.inl (Sum.inl _) => Sum.inl (Sum.inr ())
    | Sum.inl (Sum.inr _) => Sum.inl (Sum.inl ())
    | Sum.inr _ => Sum.inr ()
  left_inv := by rintro ((i | i) | i) <;> cases i <;> rfl
  right_inv := by rintro ((i | i) | i) <;> cases i <;> rfl

theorem siblingSwap_eq_sumCongr :
    siblingSwap = (Equiv.sumComm Unit Unit).sumCongr (Equiv.refl Unit) := by
  apply Equiv.ext
  rintro ((i | i) | i) <;> cases i <;> rfl

def pairPieces (n : ℕ) : rotationSource.Leaf → Tree
  | Sum.inl _ => .leaf
  | Sum.inr _ => rightVine n

def pairTree (n : ℕ) : Tree := .fork (.fork .leaf .leaf) (rightVine n)

def pairFirst (n : ℕ) : (pairTree n).Leaf :=
  Sum.inl (Sum.inl ())

def pairSecond (n : ℕ) : (pairTree n).Leaf :=
  Sum.inl (Sum.inr ())

def pairSwap (n : ℕ) : Equiv.Perm (pairTree n).Leaf :=
  Equiv.swap (pairFirst n) (pairSecond n)

theorem pairFirst_ne_pairSecond (n : ℕ) : pairFirst n ≠ pairSecond n := by
  rintro h
  have : (Sum.inl () : Unit ⊕ Unit) = Sum.inr () := Sum.inl.inj h
  contradiction

theorem pairSwap_eq_swap (n : ℕ) :
    pairSwap n = Equiv.swap (pairFirst n) (pairSecond n) := by
  rfl

@[simp] theorem card_pairTree_leaf (n : ℕ) :
    Fintype.card (pairTree n).Leaf = n + 3 := by
  change Fintype.card ((Unit ⊕ Unit) ⊕ (rightVine n).Leaf) = n + 3
  rw [Fintype.card_sum, Fintype.card_sum, card_rightVine_leaf]
  simp only [Fintype.card_unit]
  omega

theorem table_pairSwap_eq_siblingSwap (n : ℕ) :
    table (pairTree n) (pairTree n) (pairSwap n) =
      table rotationSource rotationSource siblingSwap := by
  let raw : Equiv.Perm (pairTree n).Leaf :=
    expandEquiv siblingSwap (pairPieces n)
  have hequiv : raw = pairSwap n := by
    apply Equiv.ext
    rintro (i | j)
    · rcases i with (i | i) <;> cases i <;> rfl
    · rfl
  rw [← hequiv]
  exact table_expand rotationSource rotationSource siblingSwap (pairPieces n)

theorem normal_contains_siblingSwap (N : Subgroup V) (hNormal : N.Normal)
    (g : V) (hg : g ∈ N) (hne : g ≠ 1) :
    (⟨table rotationSource rotationSource siblingSwap, table_mem_V _ _ _⟩ : V) ∈ N := by
  have hFalse := normal_contains_false_copy N hNormal g hg hne
    (leafPermHom (.fork .leaf .leaf) (Equiv.sumComm Unit Unit))
  let localized := localVHom [false]
    (leafPermHom (.fork .leaf .leaf) (Equiv.sumComm Unit Unit))
  let sibling := tableElement rotationSource rotationSource siblingSwap
  have heq : localized = sibling := by
    apply Subtype.ext
    change Cantor.branchPerm false
        (table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit)) =
      table rotationSource rotationSource siblingSwap
    rw [siblingSwap_eq_sumCongr]
    exact branchPerm_false_table (.fork .leaf .leaf) (.fork .leaf .leaf)
      (Equiv.sumComm Unit Unit)
  change localized ∈ N at hFalse
  change sibling ∈ N
  rwa [← heq]

/-- In a tree with at least three leaves, every leaf transposition is a
conjugate of the sibling transposition contained in the normal subgroup. -/
theorem normal_contains_leaf_swap_of_three_le (N : Subgroup V) (hNormal : N.Normal)
    (g : V) (hg : g ∈ N) (hne : g ≠ 1) (t : Tree)
    {i j : t.Leaf} (hij : i ≠ j) (hcard : 3 ≤ Fintype.card t.Leaf) :
    (⟨table t t (Equiv.swap i j), table_mem_V _ _ _⟩ : V) ∈ N := by
  let n := Fintype.card t.Leaf - 3
  have hPairCard : Fintype.card (pairTree n).Leaf = Fintype.card t.Leaf := by
    simp [n]
    omega
  obtain ⟨e, hFirst, hSecond⟩ := exists_equiv_map_pair hPairCard
    (pairFirst_ne_pairSecond n) hij
  let conjugator : V := ⟨table (pairTree n) t e, table_mem_V _ _ _⟩
  have hPair :
      (⟨table (pairTree n) (pairTree n) (pairSwap n), table_mem_V _ _ _⟩ : V) ∈ N := by
    simpa only [table_pairSwap_eq_siblingSwap] using
      normal_contains_siblingSwap N hNormal g hg hne
  have hConjugate := hNormal.conj_mem _ hPair conjugator
  have htable :
      table (pairTree n) t e * table (pairTree n) (pairTree n) (pairSwap n) *
          (table (pairTree n) t e)⁻¹ =
        table t t (Equiv.swap i j) := by
    have hinv : (table (pairTree n) t e)⁻¹ = table t (pairTree n) e.symm :=
      table_symm (pairTree n) t e
    calc
      _ = table (pairTree n) t ((pairSwap n).trans e) *
          table t (pairTree n) e.symm := by
            rw [hinv, table_mul_table_same_middle]
      _ = table t t (e.symm.trans ((pairSwap n).trans e)) := by
            rw [table_mul_table_same_middle]
      _ = table t t (Equiv.swap i j) := by
            congr 1
            rw [pairSwap_eq_swap, ← Equiv.trans_assoc,
              Equiv.symm_trans_swap_trans, hFirst, hSecond]
  have heq : conjugator *
      (⟨table (pairTree n) (pairTree n) (pairSwap n), table_mem_V _ _ _⟩ : V) *
        conjugator⁻¹ =
      (⟨table t t (Equiv.swap i j), table_mem_V _ _ _⟩ : V) :=
    Subtype.ext htable
  rwa [heq] at hConjugate

def topTree : Tree := .fork .leaf .leaf

def squareTree : Tree := .fork topTree topTree

def rowSwap : Equiv.Perm squareTree.Leaf :=
  Equiv.sumComm topTree.Leaf topTree.Leaf

def square₀₀ : squareTree.Leaf := Sum.inl (Sum.inl ())
def square₀₁ : squareTree.Leaf := Sum.inl (Sum.inr ())
def square₁₀ : squareTree.Leaf := Sum.inr (Sum.inl ())
def square₁₁ : squareTree.Leaf := Sum.inr (Sum.inr ())

theorem rowSwap_factorization :
    rowSwap = Equiv.swap square₀₀ square₁₀ *
      Equiv.swap square₀₁ square₁₁ := by
  apply Equiv.ext
  intro x
  rcases x with ((x | x) | (x | x)) <;> cases x <;>
    rfl

theorem table_rowSwap_eq_topSwap :
    table squareTree squareTree rowSwap =
      table topTree topTree (Equiv.sumComm Unit Unit) := by
  change table (.fork (.fork .leaf .leaf) (.fork .leaf .leaf))
      (.fork (.fork .leaf .leaf) (.fork .leaf .leaf))
        (Equiv.sumComm (Unit ⊕ Unit) (Unit ⊕ Unit)) =
    table (.fork .leaf .leaf) (.fork .leaf .leaf) (Equiv.sumComm Unit Unit)
  let pieces : (Tree.fork .leaf .leaf).Leaf → Tree :=
    fun _ => .fork .leaf .leaf
  have hequiv :
      expandEquiv (source := .fork .leaf .leaf) (target := .fork .leaf .leaf)
        (Equiv.sumComm Unit Unit) pieces =
      Equiv.sumComm (Unit ⊕ Unit) (Unit ⊕ Unit) := by
    apply Equiv.ext
    rintro ((i | i) | (i | i)) <;> cases i <;>
      rfl
  rw [← hequiv]
  exact table_expand (.fork .leaf .leaf) (.fork .leaf .leaf)
    (Equiv.sumComm Unit Unit) pieces

theorem normal_contains_topSwap (N : Subgroup V) (hNormal : N.Normal)
    (g : V) (hg : g ∈ N) (hne : g ≠ 1) :
    (⟨table topTree topTree (Equiv.sumComm Unit Unit), table_mem_V _ _ _⟩ : V) ∈ N := by
  have hcard : 3 ≤ Fintype.card squareTree.Leaf := by
    decide
  have h₀ := normal_contains_leaf_swap_of_three_le N hNormal g hg hne squareTree
    (i := square₀₀) (j := square₁₀) (by decide) hcard
  have h₁ := normal_contains_leaf_swap_of_three_le N hNormal g hg hne squareTree
    (i := square₀₁) (j := square₁₁) (by decide) hcard
  have hmul := N.mul_mem h₀ h₁
  have hrow : (⟨table squareTree squareTree rowSwap, table_mem_V _ _ _⟩ : V) ∈ N := by
    have heq :
        (⟨table squareTree squareTree (Equiv.swap square₀₀ square₁₀),
          table_mem_V _ _ _⟩ : V) *
          (⟨table squareTree squareTree (Equiv.swap square₀₁ square₁₁),
            table_mem_V _ _ _⟩ : V) =
          (⟨table squareTree squareTree rowSwap, table_mem_V _ _ _⟩ : V) := by
      change leafPermHom squareTree (Equiv.swap square₀₀ square₁₀) *
          leafPermHom squareTree (Equiv.swap square₀₁ square₁₁) =
        leafPermHom squareTree rowSwap
      rw [← map_mul, ← rowSwap_factorization]
    rwa [heq] at hmul
  simpa only [table_rowSwap_eq_topSwap] using hrow

theorem topSwap_eq_swap :
    (Equiv.sumComm Unit Unit) = Equiv.swap (Sum.inl ()) (Sum.inr ()) := by
  apply Equiv.ext
  intro x
  rcases x with (x | x) <;> cases x <;> rfl

theorem normal_contains_leaf_swap (N : Subgroup V) (hNormal : N.Normal)
    (g : V) (hg : g ∈ N) (hne : g ≠ 1) (t : Tree)
    {i j : t.Leaf} (hij : i ≠ j) :
    (⟨table t t (Equiv.swap i j), table_mem_V _ _ _⟩ : V) ∈ N := by
  by_cases hcard : 3 ≤ Fintype.card t.Leaf
  · exact normal_contains_leaf_swap_of_three_le N hNormal g hg hne t hij hcard
  · have htwo : 2 ≤ Fintype.card t.Leaf := by
      have hlt : 1 < Fintype.card t.Leaf :=
        Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨i, j, hij⟩⟩
      omega
    have hcardEq : Fintype.card topTree.Leaf = Fintype.card t.Leaf := by
      change Fintype.card (Unit ⊕ Unit) = Fintype.card t.Leaf
      rw [Fintype.card_sum]
      simp only [Fintype.card_unit]
      omega
    obtain ⟨e, hFirst, hSecond⟩ := exists_equiv_map_pair hcardEq
      (a₁ := Sum.inl ()) (a₂ := Sum.inr ()) (by rintro h; cases h) hij
    let conjugator : V := ⟨table topTree t e, table_mem_V _ _ _⟩
    have hTop := normal_contains_topSwap N hNormal g hg hne
    have hConjugate := hNormal.conj_mem _ hTop conjugator
    have htable :
        table topTree t e * table topTree topTree (Equiv.sumComm Unit Unit) *
            (table topTree t e)⁻¹ = table t t (Equiv.swap i j) := by
      have hinv : (table topTree t e)⁻¹ = table t topTree e.symm :=
        table_symm topTree t e
      calc
        _ = table topTree t ((Equiv.sumComm Unit Unit).trans e) *
            table t topTree e.symm := by
              rw [hinv, table_mul_table_same_middle]
              rfl
        _ = table t t (e.symm.trans ((Equiv.sumComm Unit Unit).trans e)) := by
              rw [table_mul_table_same_middle]
        _ = table t t (Equiv.swap i j) := by
              congr 1
              rw [topSwap_eq_swap]
              calc
                e.symm.trans ((Equiv.swap (Sum.inl ()) (Sum.inr ())).trans e) =
                    (e.symm.trans (Equiv.swap (Sum.inl ()) (Sum.inr ()))).trans e :=
                  (Equiv.trans_assoc _ _ _).symm
                _ = Equiv.swap (e (Sum.inl ())) (e (Sum.inr ())) :=
                  Equiv.symm_trans_swap_trans _ _ e
                _ = Equiv.swap i j := by rw [hFirst, hSecond]
    have heq : conjugator *
        (⟨table topTree topTree (Equiv.sumComm Unit Unit), table_mem_V _ _ _⟩ : V) *
          conjugator⁻¹ =
        (⟨table t t (Equiv.swap i j), table_mem_V _ _ _⟩ : V) :=
      Subtype.ext htable
    rwa [heq] at hConjugate

theorem normal_contains_same_tree_table (N : Subgroup V) (hNormal : N.Normal)
    (g : V) (hg : g ∈ N) (hne : g ≠ 1) (t : Tree)
    (e : Equiv.Perm t.Leaf) :
    (⟨table t t e, table_mem_V _ _ _⟩ : V) ∈ N := by
  induction e using Equiv.Perm.swap_induction_on with
  | one =>
      change leafPermHom t 1 ∈ N
      rw [map_one]
      exact N.one_mem
  | swap_mul e i j hij ih =>
      have hswap := normal_contains_leaf_swap N hNormal g hg hne t hij
      have hmul := N.mul_mem hswap ih
      change leafPermHom t (Equiv.swap i j) * leafPermHom t e ∈ N at hmul
      rw [← map_mul] at hmul
      exact hmul

/-- The subgroup generated by tables which merely permute the leaves of one
fixed tree. -/
def leafTableSet : Set V :=
  {g | ∃ (t : Tree) (e : Equiv.Perm t.Leaf),
    g = ⟨table t t e, table_mem_V _ _ _⟩}

def leafGenerated : Subgroup V := Subgroup.closure leafTableSet

theorem same_tree_mem_leafGenerated (t : Tree) (e : Equiv.Perm t.Leaf) :
    (⟨table t t e, table_mem_V _ _ _⟩ : V) ∈ leafGenerated :=
  Subgroup.subset_closure ⟨t, e, rfl⟩

theorem exists_local_same_tree (word : List Bool) (t : Tree)
    (e : Equiv.Perm t.Leaf) :
    ∃ (u : Tree) (f : Equiv.Perm u.Leaf),
      Cantor.localPerm word (table t t e) = table u u f := by
  induction word with
  | nil => exact ⟨t, e, rfl⟩
  | cons b word ih =>
      obtain ⟨u, f, hf⟩ := ih
      rw [Cantor.localPerm_cons, hf]
      cases b
      · exact ⟨.fork u .leaf, f.sumCongr (Equiv.refl Unit),
          branchPerm_false_table u u f⟩
      · exact ⟨.fork .leaf u, (Equiv.refl Unit).sumCongr f,
          branchPerm_true_table u u f⟩

theorem local_mem_leafGenerated (word : List Bool) {a : V}
    (ha : a ∈ leafGenerated) : localVHom word a ∈ leafGenerated := by
  have hle : leafGenerated ≤ leafGenerated.comap (localVHom word) := by
    apply (Subgroup.closure_le _).2
    rintro x ⟨t, e, rfl⟩
    obtain ⟨u, f, hf⟩ := exists_local_same_tree word t e
    have hgen := same_tree_mem_leafGenerated u f
    have heq : localVHom word (tableElement t t e) = tableElement u u f :=
      Subtype.ext hf
    change localVHom word (tableElement t t e) ∈ leafGenerated
    rw [heq]
    change tableElement u u f ∈ leafGenerated at hgen
    exact hgen
  exact hle ha

theorem rotation_mem_leafGenerated :
    (⟨table rotationSource rotationTarget rotationEquiv,
      table_mem_V _ _ _⟩ : V) ∈ leafGenerated := by
  have hprod := leafGenerated.mul_mem
    (leafGenerated.mul_mem
      (same_tree_mem_leafGenerated rotationTarget targetEndSwap)
      (same_tree_mem_leafGenerated topTree (Equiv.sumComm Unit Unit)))
    (same_tree_mem_leafGenerated rotationSource sourceEndSwap)
  let product : V :=
    tableElement rotationTarget rotationTarget targetEndSwap *
      tableElement topTree topTree (Equiv.sumComm Unit Unit) *
        tableElement rotationSource rotationSource sourceEndSwap
  let rotation : V := tableElement rotationSource rotationTarget rotationEquiv
  have heq : product = rotation := by
    apply Subtype.ext
    exact rotation_factorization
  change product ∈ leafGenerated at hprod
  change rotation ∈ leafGenerated
  rwa [← heq]

theorem assoc_mem_leafGenerated (a b c : Tree) :
    (⟨table (.fork (.fork a b) c) (.fork a (.fork b c)) (assocEquiv a b c),
      table_mem_V _ _ _⟩ : V) ∈ leafGenerated := by
  simpa only [table_assocEquiv] using rotation_mem_leafGenerated

theorem fork_mem_leafGenerated
    (sourceLeft sourceRight targetLeft targetRight : Tree)
    (eLeft : sourceLeft.Leaf ≃ targetLeft.Leaf)
    (eRight : sourceRight.Leaf ≃ targetRight.Leaf)
    (hLeft : (⟨table sourceLeft targetLeft eLeft, table_mem_V _ _ _⟩ : V) ∈
      leafGenerated)
    (hRight : (⟨table sourceRight targetRight eRight, table_mem_V _ _ _⟩ : V) ∈
      leafGenerated) :
    (⟨table (.fork sourceLeft sourceRight) (.fork targetLeft targetRight)
        (eLeft.sumCongr eRight), table_mem_V _ _ _⟩ : V) ∈ leafGenerated := by
  let leftElement := tableElement sourceLeft targetLeft eLeft
  let rightElement := tableElement sourceRight targetRight eRight
  let forkElement := tableElement (.fork sourceLeft sourceRight)
    (.fork targetLeft targetRight) (eLeft.sumCongr eRight)
  have hLocalLeft := local_mem_leafGenerated [false] hLeft
  have hLocalRight := local_mem_leafGenerated [true] hRight
  have heq : forkElement =
      localVHom [false] leftElement * localVHom [true] rightElement := by
    apply Subtype.ext
    simpa [forkElement, leftElement, rightElement, tableElement, localVHom,
      Cantor.localPerm] using
      table_fork sourceLeft sourceRight targetLeft targetRight eLeft eRight
  change forkElement ∈ leafGenerated
  rw [heq]
  exact leafGenerated.mul_mem hLocalLeft hLocalRight

theorem exists_vine_merge_leafGenerated : ∀ m n : ℕ,
    ∃ (k : ℕ) (e : (Tree.fork (rightVine m) (rightVine n)).Leaf ≃
      (rightVine k).Leaf),
      (⟨table (.fork (rightVine m) (rightVine n)) (rightVine k) e,
        table_mem_V _ _ _⟩ : V) ∈ leafGenerated := by
  intro m
  induction m with
  | zero =>
      intro n
      refine ⟨n + 1, Equiv.refl (rightVine (n + 1)).Leaf, ?_⟩
      simpa [rightVine] using
        same_tree_mem_leafGenerated (rightVine (n + 1))
          (Equiv.refl (rightVine (n + 1)).Leaf)
  | succ m ih =>
      intro n
      obtain ⟨k, e, he⟩ := ih n
      let rotation := assocEquiv .leaf (rightVine m) (rightVine n)
      let forkEquiv := (Equiv.refl Unit).sumCongr e
      have hrotation := assoc_mem_leafGenerated .leaf (rightVine m) (rightVine n)
      have hfork := fork_mem_leafGenerated .leaf
        (.fork (rightVine m) (rightVine n)) .leaf (rightVine k)
        (Equiv.refl Unit) e
        (same_tree_mem_leafGenerated .leaf (Equiv.refl Unit)) he
      refine ⟨k + 1, rotation.trans forkEquiv, ?_⟩
      have hproduct := leafGenerated.mul_mem hfork hrotation
      change tableElement (.fork (.fork .leaf (rightVine m)) (rightVine n))
        (rightVine (k + 1)) (rotation.trans forkEquiv) ∈ leafGenerated
      change tableElement (.fork .leaf (.fork (rightVine m) (rightVine n)))
          (rightVine (k + 1)) forkEquiv *
        tableElement (.fork (.fork .leaf (rightVine m)) (rightVine n))
          (.fork .leaf (.fork (rightVine m) (rightVine n))) rotation ∈
          leafGenerated at hproduct
      rw [tableElement_mul] at hproduct
      exact hproduct

theorem exists_vine_normalization_leafGenerated : ∀ t : Tree,
    ∃ (n : ℕ) (e : t.Leaf ≃ (rightVine n).Leaf),
      (⟨table t (rightVine n) e, table_mem_V _ _ _⟩ : V) ∈ leafGenerated := by
  intro t
  induction t with
  | leaf =>
      refine ⟨0, Equiv.refl Unit, ?_⟩
      exact same_tree_mem_leafGenerated .leaf (Equiv.refl Unit)
  | fork left right ihLeft ihRight =>
      obtain ⟨m, eLeft, hLeft⟩ := ihLeft
      obtain ⟨n, eRight, hRight⟩ := ihRight
      obtain ⟨k, eMerge, hMerge⟩ := exists_vine_merge_leafGenerated m n
      let forkEquiv := eLeft.sumCongr eRight
      have hfork := fork_mem_leafGenerated left right (rightVine m) (rightVine n)
        eLeft eRight hLeft hRight
      refine ⟨k, forkEquiv.trans eMerge, ?_⟩
      have hproduct := leafGenerated.mul_mem hMerge hfork
      change tableElement (.fork left right) (rightVine k)
        (forkEquiv.trans eMerge) ∈ leafGenerated
      change tableElement (.fork (rightVine m) (rightVine n)) (rightVine k)
          eMerge *
        tableElement (.fork left right) (.fork (rightVine m) (rightVine n))
          forkEquiv ∈ leafGenerated at hproduct
      rw [tableElement_mul] at hproduct
      exact hproduct

theorem table_mem_leafGenerated (source target : Tree)
    (e : source.Leaf ≃ target.Leaf) :
    (⟨table source target e, table_mem_V _ _ _⟩ : V) ∈ leafGenerated := by
  change tableElement source target e ∈ leafGenerated
  obtain ⟨m, eSource, hSource⟩ := exists_vine_normalization_leafGenerated source
  obtain ⟨n, eTarget, hTarget⟩ := exists_vine_normalization_leafGenerated target
  have hSourceCard : Fintype.card source.Leaf = m + 1 :=
    (Fintype.card_congr eSource).trans (card_rightVine_leaf m)
  have hTargetCard : Fintype.card target.Leaf = n + 1 :=
    (Fintype.card_congr eTarget).trans (card_rightVine_leaf n)
  have hEqualCard : Fintype.card source.Leaf = Fintype.card target.Leaf :=
    Fintype.card_congr e
  have hmn : m = n := by omega
  subst n
  let shape := eSource.trans eTarget.symm
  have hTargetInv :
      tableElement (rightVine m) target eTarget.symm ∈ leafGenerated := by
    have hinv := leafGenerated.inv_mem hTarget
    change (tableElement target (rightVine m) eTarget)⁻¹ ∈ leafGenerated at hinv
    rw [tableElement_inv] at hinv
    exact hinv
  have hShape :
      tableElement source target shape ∈ leafGenerated := by
    have hproduct := leafGenerated.mul_mem hTargetInv hSource
    change tableElement (rightVine m) target eTarget.symm *
      tableElement source (rightVine m) eSource ∈ leafGenerated at hproduct
    rw [tableElement_mul] at hproduct
    exact hproduct
  let adjust : Equiv.Perm target.Leaf := shape.symm.trans e
  have hAdjust := same_tree_mem_leafGenerated target adjust
  have hproduct := leafGenerated.mul_mem hAdjust hShape
  change tableElement target target adjust * tableElement source target shape ∈
    leafGenerated at hproduct
  rw [tableElement_mul] at hproduct
  simpa only [adjust, ← Equiv.trans_assoc, Equiv.self_trans_symm,
    Equiv.refl_trans] using hproduct

theorem leafGenerated_eq_top : leafGenerated = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨source, target, e, heq⟩ := (mem_V_iff_table).1 g.2
  have hg : g = (⟨table source target e, table_mem_V _ _ _⟩ : V) :=
    Subtype.ext heq
  rw [hg]
  exact table_mem_leafGenerated source target e

/-- A tree whose two deepest sibling cylinders occur below `n` consecutive
left branches. -/
def deepFork : ℕ → Tree
  | 0 => .fork .leaf .leaf
  | n + 1 => .fork (deepFork n) .leaf

/-- Swap the two deepest sibling leaves of `deepFork n`, fixing every other
leaf. -/
def deepSwap : (n : ℕ) → (deepFork n).Leaf ≃ (deepFork n).Leaf
  | 0 => Equiv.sumComm Unit Unit
  | n + 1 => (deepSwap n).sumCongr (Equiv.refl Unit)

/-- The word replacement which flips the bit following `n` initial zeroes. -/
def deepPerm (n : ℕ) : Equiv.Perm Cantor := table (deepFork n) (deepFork n) (deepSwap n)

theorem deepPerm_mem_V (n : ℕ) : deepPerm n ∈ V :=
  table_mem_V _ _ _

def zero : Cantor := fun _ => false

/-- The stream with a unique `true` bit at position `n`. -/
def pulse (n : ℕ) : Cantor := fun k => decide (k = n)

@[simp] theorem pulse_apply_self (n : ℕ) : pulse n n = true := by
  simp [pulse]

theorem pulse_injective : Function.Injective pulse := by
  intro m n h
  by_contra hmn
  have hmn' : m ≠ n := by simpa using hmn
  have := congrFun h m
  simp [pulse, hmn'] at this

theorem pulse_succ (n : ℕ) : pulse (n + 1) = Cantor.cons false (pulse n) := by
  funext k
  cases k with
  | zero => simp [pulse, Cantor.cons]
  | succ k => simp [pulse, Cantor.cons]

@[simp] theorem deepPerm_zero (n : ℕ) : deepPerm n zero = pulse n := by
  induction n with
  | zero =>
      funext k
      cases k with
      | zero => rfl
      | succ k => simp [deepPerm, deepFork, deepSwap, table, codeEquiv, encode, decode,
          zero, pulse, Cantor.head, Cantor.tail, Cantor.cons]
  | succ n ih =>
      calc
        deepPerm (n + 1) zero = Cantor.cons false (deepPerm n zero) := by
          rfl
        _ = Cantor.cons false (pulse n) := congrArg (Cantor.cons false) ih
        _ = pulse (n + 1) := (pulse_succ n).symm

/-- An explicit infinite family of elements of `V`. -/
def deepElement (n : ℕ) : V := ⟨deepPerm n, deepPerm_mem_V n⟩

theorem deepElement_injective : Function.Injective deepElement := by
  intro m n h
  apply pulse_injective
  rw [← deepPerm_zero m, ← deepPerm_zero n]
  exact congrArg (fun g : V => (g : Equiv.Perm Cantor) zero) h

instance : Infinite V := Infinite.of_injective deepElement deepElement_injective

instance : IsSimpleGroup V := by
  apply IsSimpleGroup.mk
  intro N hNormal
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨n, hn⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    let g : V := n
    have hg : g ∈ N := n.2
    have hgne : g ≠ 1 := by
      intro h
      apply hn
      apply Subtype.ext
      exact h
    have hle : leafGenerated ≤ N := by
      apply (Subgroup.closure_le _).2
      rintro _ ⟨t, e, rfl⟩
      exact normal_contains_same_tree_table N hNormal g hg hgne t e
    rw [leafGenerated_eq_top] at hle
    exact top_unique hle

end Tree

end Submission.Thompson
