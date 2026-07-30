import Mathlib

namespace Submission.Helpers

/-- A rooted tree carrying at each selected node the number of leaves in
the corresponding subtree of an expansion tree. -/
inductive SizedTree where
  | node (rootSize : ℕ) (children : List SizedTree)
deriving Repr

namespace SizedTree

def size : SizedTree → ℕ
  | node n _ => n

def nodeCount : SizedTree → ℕ
  | node _ children => 1 + (children.map nodeCount).sum
termination_by tree => sizeOf tree

/-- The numerical conditions satisfied by a tree obtained by retaining
only nodes whose small divisor is below a fixed threshold. -/
def Separated (q : ℕ) : SizedTree → Prop
  | node n children =>
      q < n ∧
      (children.map size).sum ≤ n ∧
      (∀ child ∈ children, q < n - child.size) ∧
      ∀ child ∈ children, Separated q child
termination_by tree => sizeOf tree

private theorem sum_mul_nodeCount_add_one (q : ℕ) (children : List SizedTree) :
    (children.map fun child => q * (child.nodeCount + 1)).sum =
      q * ((children.map nodeCount).sum + children.length) := by
  induction children with
  | nil => simp
  | cons child children ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      ring

private theorem sum_two_mul_size (children : List SizedTree) :
    (children.map fun child => 2 * child.size).sum =
      2 * (children.map size).sum := by
  induction children <;> simp_all [Nat.mul_add]

@[elab_as_elim]
private theorem sizedTreeInduction
    {motive : SizedTree → Prop}
    (node : ∀ n children,
      (∀ child ∈ children, motive child) →
        motive (.node n children)) :
    ∀ tree, motive tree
  | .node n children =>
      node n children fun child _hchild =>
        sizedTreeInduction node child
termination_by tree => sizeOf tree
decreasing_by
  simp_wf
  have hlt := List.sizeOf_lt_of_mem _hchild
  omega

/-- A separated selected tree has at most twice as many nodes as its
root has `q`-blocks of leaves. The extra `+ 1` is the slack needed to
compose the estimate over a forest. -/
theorem mul_nodeCount_add_one_le_two_mul_size
    {q : ℕ} (_hq : q ≠ 0) :
    ∀ tree : SizedTree, tree.Separated q →
      q * (tree.nodeCount + 1) ≤ 2 * tree.size := by
  intro tree
  refine sizedTreeInduction (motive := fun tree =>
    tree.Separated q → q * (tree.nodeCount + 1) ≤ 2 * tree.size) ?_ tree
  intro n children ih hsep
  simp only [Separated] at hsep
  rcases hsep with ⟨hqn, hsizes, hedge, hchildren⟩
  have hchild :
      ∀ child ∈ children,
        q * (child.nodeCount + 1) ≤ 2 * child.size :=
    fun child hmem => ih child hmem (hchildren child hmem)
  have hsum :
      q * ((children.map nodeCount).sum + children.length) ≤
        2 * (children.map size).sum := by
    rw [← sum_mul_nodeCount_add_one, ← sum_two_mul_size]
    exact List.sum_le_sum hchild
  have hsum_n :
      q * ((children.map nodeCount).sum + children.length) ≤ 2 * n :=
    hsum.trans (Nat.mul_le_mul_left 2 hsizes)
  rcases children with _ | ⟨child, children⟩
  · simp only [nodeCount, List.map_nil, List.sum_nil, size]
    omega
  · rcases children with _ | ⟨child₂, children⟩
    · have hedge' : q < n - child.size := hedge child (by simp)
      have hchild' := hchild child (by simp)
      have hsize : child.size ≤ n := by
        simpa using hsizes
      simp only [nodeCount, size, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero]
      calc
          q * (1 + child.nodeCount + 1) =
            q * (child.nodeCount + 1) + q := by ring
        _ ≤ 2 * child.size + q :=
          Nat.add_le_add_right hchild' q
        _ ≤ 2 * n := by omega
    · have hlength :
          2 ≤ (child :: child₂ :: children).length := by simp
      have hmono :
          q * ((List.map nodeCount (child :: child₂ :: children)).sum + 2) ≤
            q * ((List.map nodeCount (child :: child₂ :: children)).sum +
              (child :: child₂ :: children).length) :=
        Nat.mul_le_mul_left q (Nat.add_le_add_left hlength _)
      simp only [nodeCount, size]
      calc
        q * (1 +
            (List.map nodeCount (child :: child₂ :: children)).sum + 1) =
          q * ((List.map nodeCount
            (child :: child₂ :: children)).sum + 2) := by ring
        _ ≤ q * ((List.map nodeCount
            (child :: child₂ :: children)).sum +
              (child :: child₂ :: children).length) := hmono
        _ ≤ 2 * n := hsum_n

/-- Forest form of the preceding estimate. -/
theorem mul_sum_nodeCount_le_two_mul_sum_size
    {q : ℕ} (hq : q ≠ 0) (forest : List SizedTree)
    (hforest : ∀ tree ∈ forest, tree.Separated q) :
    q * (forest.map nodeCount).sum ≤ 2 * (forest.map size).sum := by
  have hsum :
      (forest.map fun tree => q * (tree.nodeCount + 1)).sum ≤
        (forest.map fun tree => 2 * tree.size).sum := by
    apply List.sum_le_sum
    intro tree htree
    exact mul_nodeCount_add_one_le_two_mul_size hq tree (hforest tree htree)
  rw [sum_mul_nodeCount_add_one, sum_two_mul_size] at hsum
  exact (Nat.mul_le_mul_left q
    (Nat.le_add_right (forest.map nodeCount).sum forest.length)).trans hsum

end SizedTree

namespace BinaryTree

variable (P : ℕ → Prop) [DecidablePred P]

/-- Number of internal nodes whose subtree leaf count satisfies `P`. -/
def selectedNodeCount : BinaryTree Unit → ℕ
  | .nil => 0
  | tree@(.node _ left right) =>
      (if P tree.numLeaves then 1 else 0) +
        selectedNodeCount left + selectedNodeCount right

/-- Compress a binary tree to the forest consisting only of selected
nodes. The children of a retained node are its first retained descendants. -/
def selectedForest : BinaryTree Unit → List SizedTree
  | .nil => []
  | tree@(.node _ left right) =>
      let children := selectedForest left ++ selectedForest right
      if P tree.numLeaves then
        [SizedTree.node tree.numLeaves children]
      else
        children

theorem selectedForest_sum_size_le :
    ∀ tree : BinaryTree Unit,
      ((selectedForest P tree).map SizedTree.size).sum ≤ tree.numLeaves := by
  intro tree
  induction tree with
  | nil => simp [selectedForest]
  | node value left right ihleft ihrigh =>
      by_cases hroot : P (left.numLeaves + right.numLeaves)
      · simp [selectedForest, BinaryTree.numLeaves, hroot, SizedTree.size]
      · simp only [selectedForest, BinaryTree.numLeaves, hroot, ↓reduceIte, List.map_append,
          List.sum_append, BinaryTree.numLeaves]
        omega

theorem selectedForest_root_size_le :
    ∀ (tree : BinaryTree Unit) (selected : SizedTree),
      selected ∈ selectedForest P tree →
        selected.size ≤ tree.numLeaves := by
  intro tree
  induction tree with
  | nil =>
      simp [selectedForest]
  | node value left right ihleft ihrigh =>
      intro selected hselected
      by_cases hroot : P (left.numLeaves + right.numLeaves)
      · simp only [selectedForest, BinaryTree.numLeaves, hroot, ↓reduceIte,
          List.mem_singleton] at hselected
        subst selected
        simp [SizedTree.size]
      ·
        simp only [selectedForest, BinaryTree.numLeaves, hroot, ↓reduceIte,
          List.mem_append] at hselected
        rcases hselected with hleft | hright
        · exact (ihleft selected hleft).trans
            (Nat.le_add_right left.numLeaves right.numLeaves)
        · exact (ihrigh selected hright).trans
            (Nat.le_add_left right.numLeaves left.numLeaves)

theorem selectedForest_root_selected :
    ∀ (tree : BinaryTree Unit) (selected : SizedTree),
      selected ∈ selectedForest P tree → P selected.size := by
  intro tree
  induction tree with
  | nil =>
      simp [selectedForest]
  | node value left right ihleft ihrigh =>
      intro selected hselected
      by_cases hroot : P (left.numLeaves + right.numLeaves)
      · simp only [selectedForest, BinaryTree.numLeaves, hroot, ↓reduceIte,
          List.mem_singleton] at hselected
        subst selected
        simpa [SizedTree.size] using hroot
      ·
        simp only [selectedForest, BinaryTree.numLeaves, hroot, ↓reduceIte,
          List.mem_append] at hselected
        rcases hselected with hleft | hright
        · exact ihleft selected hleft
        · exact ihrigh selected hright

theorem selectedForest_sum_nodeCount :
    ∀ tree : BinaryTree Unit,
      ((selectedForest P tree).map SizedTree.nodeCount).sum =
        selectedNodeCount P tree := by
  intro tree
  induction tree with
  | nil => simp [selectedForest, selectedNodeCount]
  | node value left right ihleft ihrigh =>
      by_cases hroot : P (left.numLeaves + right.numLeaves)
      · simp only [selectedForest, selectedNodeCount, BinaryTree.numLeaves, hroot, ↓reduceIte,
          List.map_singleton, List.sum_singleton, SizedTree.nodeCount,
          List.map_append, List.sum_append, ihleft, ihrigh]
        omega
      · simp [selectedForest, selectedNodeCount, BinaryTree.numLeaves, hroot, ihleft, ihrigh]

/-- The compressed selected forest is separated whenever selected subtree
sizes are large and any two distinct selected sizes are `q`-separated. -/
theorem selectedForest_separated
    {q : ℕ}
    (hlarge : ∀ n, P n → q < n)
    (hsep : ∀ m n, P m → P n → m < n → q < n - m) :
    ∀ (tree : BinaryTree Unit) (selected : SizedTree),
      selected ∈ selectedForest P tree → selected.Separated q := by
  intro tree
  induction tree with
  | nil =>
      simp [selectedForest]
  | node value left right ihleft ihrigh =>
      intro selected hselected
      let children :=
        selectedForest P left ++ selectedForest P right
      have hchildren :
          ∀ child ∈ children, child.Separated q := by
        intro child hchild
        rcases List.mem_append.mp hchild with hchild | hchild
        · exact ihleft child hchild
        · exact ihrigh child hchild
      by_cases hroot : P (left.numLeaves + right.numLeaves)
      · have hselected_eq :
            selected =
              SizedTree.node (left.numLeaves + right.numLeaves) children := by
          simpa [children, selectedForest, hroot] using hselected
        subst selected
        simp only [SizedTree.Separated]
        refine ⟨hlarge (left.numLeaves + right.numLeaves) hroot, ?_, ?_, hchildren⟩
        · dsimp [children]
          simp only [List.map_append, List.sum_append]
          have hleft := selectedForest_sum_size_le P left
          have hright := selectedForest_sum_size_le P right
          omega
        · intro child hchild
          have hchild_selected : P child.size := by
            rcases List.mem_append.mp hchild with hchild | hchild
            · exact selectedForest_root_selected P left child hchild
            · exact selectedForest_root_selected P right child hchild
          have hchild_lt :
              child.size < left.numLeaves + right.numLeaves := by
            rcases List.mem_append.mp hchild with hchild | hchild
            · have hle := selectedForest_root_size_le P left child hchild
              exact hle.trans_lt (Nat.lt_add_of_pos_right right.numLeaves_pos)
            · have hle := selectedForest_root_size_le P right child hchild
              exact hle.trans_lt (Nat.lt_add_of_pos_left left.numLeaves_pos)
          exact hsep child.size (left.numLeaves + right.numLeaves)
            hchild_selected hroot hchild_lt
      · have hmember : selected ∈ children := by
          simpa [children, selectedForest, hroot] using hselected
        exact hchildren selected hmember

/-- A threshold selection satisfying the two elementary separation
conditions occupies at most `2 / q` nodes per leaf. -/
theorem mul_selectedNodeCount_le_two_mul_numLeaves
    {q : ℕ} (hq : q ≠ 0)
    (hlarge : ∀ n, P n → q < n)
    (hsep : ∀ m n, P m → P n → m < n → q < n - m)
    (tree : BinaryTree Unit) :
    q * selectedNodeCount P tree ≤ 2 * tree.numLeaves := by
  rw [← selectedForest_sum_nodeCount P tree]
  refine (SizedTree.mul_sum_nodeCount_le_two_mul_sum_size hq
    (selectedForest P tree) ?_).trans ?_
  · exact selectedForest_separated P hlarge hsep tree
  · gcongr
    exact selectedForest_sum_size_le P tree

end BinaryTree

end Submission.Helpers
