import Submission.FormalLinearization
import Submission.TreeMajorant

open Finset FormalMultilinearSeries

namespace Submission

private def binaryComb : ℕ → BinaryTree Unit
  | 0 => .nil
  | n + 1 => .node () .nil (binaryComb n)

@[simp]
private theorem binaryComb_numNodes (n : ℕ) :
    (binaryComb n).numNodes = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [binaryComb, ih]

private theorem treesOfNumNodesEq_nonempty (n : ℕ) :
    (BinaryTree.treesOfNumNodesEq n).Nonempty := by
  refine ⟨binaryComb n, ?_⟩
  exact BinaryTree.mem_treesOfNumNodesEq.mpr (binaryComb_numNodes n)

/-- Worst binary-tree small-divisor product in a fixed degree. -/
noncomputable def treeSmallDivisorMajorant (lam : ℂ) (n : ℕ) : ℝ :=
  if _hn : n = 0 then 1
  else
    (BinaryTree.treesOfNumNodesEq (n - 1)).sup'
      (treesOfNumNodesEq_nonempty (n - 1))
      (binarySmallDivisorWeight lam)

private theorem binarySmallDivisorWeight_one_le (lam : ℂ) :
    ∀ tree : BinaryTree Unit, 1 ≤ binarySmallDivisorWeight lam tree := by
  intro tree
  induction tree with
  | nil => simp [binarySmallDivisorWeight]
  | node value left right ihleft ihrigh =>
      simp only [binarySmallDivisorWeight]
      have hfactor :
          1 ≤ max 1
            (smallDivisor lam
              (BinaryTree.node value left right).numLeaves)⁻¹ :=
        le_max_left _ _
      have hchildren :
          1 * 1 ≤
            binarySmallDivisorWeight lam left *
              binarySmallDivisorWeight lam right :=
        mul_le_mul ihleft ihrigh zero_le_one (zero_le_one.trans ihleft)
      calc
        1 = 1 * (1 * 1) := by ring
        _ ≤ max 1
                (smallDivisor lam
                  (BinaryTree.node value left right).numLeaves)⁻¹ *
              (binarySmallDivisorWeight lam left *
                binarySmallDivisorWeight lam right) :=
          mul_le_mul hfactor hchildren (by positivity)
            (zero_le_one.trans hfactor)
        _ = _ := by ring

theorem treeSmallDivisorMajorant_one_le (lam : ℂ) (n : ℕ) :
    1 ≤ treeSmallDivisorMajorant lam n := by
  by_cases hn : n = 0
  · simp [treeSmallDivisorMajorant, hn]
  · rw [treeSmallDivisorMajorant, dif_neg hn]
    obtain ⟨tree, htree⟩ := treesOfNumNodesEq_nonempty (n - 1)
    exact (binarySmallDivisorWeight_one_le lam tree).trans
      (Finset.le_sup' _ htree)

private theorem exists_treeSmallDivisorMajorant
    (lam : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ∃ tree : BinaryTree Unit,
      tree.numLeaves = n ∧
        treeSmallDivisorMajorant lam n =
          binarySmallDivisorWeight lam tree := by
  rw [treeSmallDivisorMajorant, dif_neg hn]
  obtain ⟨tree, hmem, heq⟩ :=
    Finset.exists_mem_eq_sup'
      (treesOfNumNodesEq_nonempty (n - 1))
      (binarySmallDivisorWeight lam)
  refine ⟨tree, ?_, heq⟩
  rw [BinaryTree.numLeaves_eq_numNodes_succ,
    BinaryTree.mem_treesOfNumNodesEq.mp hmem]
  omega

theorem treeSmallDivisorMajorant_le_pow
    {lam : ℂ} {c : ℝ} {T : ℕ}
    (hc : 0 < c) (hT : T ≠ 0) (hlam : ‖lam‖ = 1)
    (hnonzero : ∀ r : ℕ, r ≠ 0 → lam ^ r ≠ 1)
    (hbound : ∀ r : ℕ, r ≠ 0 →
      c / (r : ℝ) ^ T ≤ ‖lam ^ r - 1‖)
    (n : ℕ) :
    treeSmallDivisorMajorant lam n ≤
      (max 1 (2 / c) * (((2 : ℝ) ^ T) ^ 4)) ^ n := by
  by_cases hn : n = 0
  · subst n
    simp [treeSmallDivisorMajorant]
  · rw [treeSmallDivisorMajorant, dif_neg hn]
    apply Finset.sup'_le
    intro tree htree
    have hle :=
      binarySmallDivisorWeight_le_pow hc hT hlam hnonzero hbound tree
    rw [BinaryTree.numLeaves_eq_numNodes_succ,
      BinaryTree.mem_treesOfNumNodesEq.mp htree] at hle
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] using hle

/-- Right-associated combination of a nonempty list of binary trees. -/
private def combineTrees : List (BinaryTree Unit) → BinaryTree Unit
  | [] => .nil
  | [tree] => tree
  | tree₁ :: tree₂ :: trees =>
      .node () tree₁ (combineTrees (tree₂ :: trees))
termination_by trees => trees.length

private theorem combineTrees_numLeaves
    (trees : List (BinaryTree Unit)) (htrees : trees ≠ []) :
    (combineTrees trees).numLeaves =
      (trees.map BinaryTree.numLeaves).sum := by
  induction trees with
  | nil => contradiction
  | cons tree trees ih =>
      cases trees with
      | nil => simp [combineTrees]
      | cons tree₂ trees =>
          simp only [combineTrees, BinaryTree.numLeaves, List.map_cons,
            List.sum_cons]
          rw [ih (by simp)]
          simp

private theorem binarySmallDivisorWeight_nonneg (lam : ℂ) :
    ∀ tree : BinaryTree Unit, 0 ≤ binarySmallDivisorWeight lam tree :=
  fun tree => (zero_le_one.trans
    (binarySmallDivisorWeight_one_le lam tree))

private theorem prod_weight_le_combineTrees
    (lam : ℂ) (trees : List (BinaryTree Unit)) (htrees : trees ≠ []) :
    (trees.map (binarySmallDivisorWeight lam)).prod ≤
      binarySmallDivisorWeight lam (combineTrees trees) := by
  induction trees with
  | nil => contradiction
  | cons tree trees ih =>
      cases trees with
      | nil => simp [combineTrees]
      | cons tree₂ trees =>
          simp only [combineTrees, binarySmallDivisorWeight,
            List.map_cons, List.prod_cons]
          have hi := ih (by simp)
          have hfactor :
              1 ≤ max 1
                (smallDivisor lam
                  (BinaryTree.node () tree
                    (combineTrees (tree₂ :: trees))).numLeaves)⁻¹ :=
            le_max_left _ _
          calc
            binarySmallDivisorWeight lam tree *
                (binarySmallDivisorWeight lam tree₂ *
                  (List.map (binarySmallDivisorWeight lam) trees).prod)
                ≤ binarySmallDivisorWeight lam tree *
                    binarySmallDivisorWeight lam
                      (combineTrees (tree₂ :: trees)) := by
                  exact mul_le_mul_of_nonneg_left hi
                    (binarySmallDivisorWeight_nonneg lam tree)
            _ ≤ max 1
                    (smallDivisor lam
                      (BinaryTree.node () tree
                        (combineTrees (tree₂ :: trees))).numLeaves)⁻¹ *
                  binarySmallDivisorWeight lam tree *
                  binarySmallDivisorWeight lam
                    (combineTrees (tree₂ :: trees)) := by
              calc
                binarySmallDivisorWeight lam tree *
                    binarySmallDivisorWeight lam
                      (combineTrees (tree₂ :: trees))
                    = 1 *
                        (binarySmallDivisorWeight lam tree *
                          binarySmallDivisorWeight lam
                            (combineTrees (tree₂ :: trees))) := by ring
                _ ≤ max 1
                      (smallDivisor lam
                        (BinaryTree.node () tree
                          (combineTrees (tree₂ :: trees))).numLeaves)⁻¹ *
                        (binarySmallDivisorWeight lam tree *
                          binarySmallDivisorWeight lam
                            (combineTrees (tree₂ :: trees))) := by
                    exact mul_le_mul_of_nonneg_right hfactor
                      (mul_nonneg
                        (binarySmallDivisorWeight_nonneg lam tree)
                        (binarySmallDivisorWeight_nonneg lam
                          (combineTrees (tree₂ :: trees))))
                _ = _ := by ring

private theorem divisor_prod_weight_le_combineTrees
    (lam : ℂ) (trees : List (BinaryTree Unit))
    (htwo : 2 ≤ trees.length) :
    (smallDivisor lam
        (trees.map BinaryTree.numLeaves).sum)⁻¹ *
        (trees.map (binarySmallDivisorWeight lam)).prod ≤
      binarySmallDivisorWeight lam (combineTrees trees) := by
  obtain ⟨tree₁, tree₂, rest, rfl⟩ :
      ∃ tree₁ tree₂ rest, trees = tree₁ :: tree₂ :: rest := by
    rcases trees with _ | ⟨tree₁, trees⟩
    · simp at htwo
    · rcases trees with _ | ⟨tree₂, trees⟩
      · simp at htwo
      · exact ⟨tree₁, tree₂, trees, rfl⟩
  simp only [combineTrees, binarySmallDivisorWeight, BinaryTree.numLeaves,
    List.map_cons, List.sum_cons, List.prod_cons]
  rw [combineTrees_numLeaves (tree₂ :: rest) (by simp)]
  have htail :=
    prod_weight_le_combineTrees lam (tree₂ :: rest) (by simp)
  have hfactor :
      (smallDivisor lam
        (tree₁.numLeaves +
          (List.map BinaryTree.numLeaves (tree₂ :: rest)).sum))⁻¹ ≤
        max 1
          (smallDivisor lam
            (tree₁.numLeaves +
              (combineTrees (tree₂ :: rest)).numLeaves))⁻¹ := by
    rw [combineTrees_numLeaves (tree₂ :: rest) (by simp)]
    exact le_max_right _ _
  have hhead_nonneg :
      0 ≤ binarySmallDivisorWeight lam tree₁ :=
    binarySmallDivisorWeight_nonneg lam tree₁
  have htailprod_nonneg :
      0 ≤ (List.map (binarySmallDivisorWeight lam)
        (tree₂ :: rest)).prod := by
    apply List.prod_nonneg
    intro weight hweight
    rw [List.mem_map] at hweight
    obtain ⟨tree, _, rfl⟩ := hweight
    exact binarySmallDivisorWeight_nonneg lam tree
  have hrootfactor_nonneg :
      0 ≤ max 1
        (smallDivisor lam
          (tree₁.numLeaves +
            (combineTrees (tree₂ :: rest)).numLeaves))⁻¹ :=
    zero_le_one.trans (le_max_left _ _)
  calc
    (smallDivisor lam
          (tree₁.numLeaves +
            (List.map BinaryTree.numLeaves (tree₂ :: rest)).sum))⁻¹ *
        (binarySmallDivisorWeight lam tree₁ *
          (binarySmallDivisorWeight lam tree₂ *
            (List.map (binarySmallDivisorWeight lam) rest).prod))
        ≤ max 1
              (smallDivisor lam
                (tree₁.numLeaves +
                  (combineTrees (tree₂ :: rest)).numLeaves))⁻¹ *
            (binarySmallDivisorWeight lam tree₁ *
              (binarySmallDivisorWeight lam tree₂ *
                (List.map (binarySmallDivisorWeight lam) rest).prod)) := by
          exact mul_le_mul_of_nonneg_right hfactor
            (mul_nonneg hhead_nonneg htailprod_nonneg)
    _ ≤ max 1
            (smallDivisor lam
              (tree₁.numLeaves +
                (combineTrees (tree₂ :: rest)).numLeaves))⁻¹ *
          (binarySmallDivisorWeight lam tree₁ *
            binarySmallDivisorWeight lam
              (combineTrees (tree₂ :: rest))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left htail hhead_nonneg)
          hrootfactor_nonneg
    _ = max 1
            (smallDivisor lam
              (tree₁.numLeaves +
                (List.map BinaryTree.numLeaves (tree₂ :: rest)).sum))⁻¹ *
          binarySmallDivisorWeight lam tree₁ *
          binarySmallDivisorWeight lam
            (combineTrees (tree₂ :: rest)) := by
        rw [combineTrees_numLeaves (tree₂ :: rest) (by simp)]
        ring

private theorem treeSmallDivisorMajorant_comp
    (lam : ℂ) {n : ℕ} (c : Composition n) (hc : 1 < c.length) :
    (smallDivisor lam n)⁻¹ *
        ∏ i, treeSmallDivisorMajorant lam (c.blocksFun i) ≤
      treeSmallDivisorMajorant lam n := by
  have hnpos : 0 < n :=
    (by omega : 0 < c.length).trans_le c.length_le
  have hn : n ≠ 0 := hnpos.ne'
  have hblock (i : Fin c.length) : c.blocksFun i ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (c.one_le_blocksFun i)
  choose trees hleaves hweights using
    fun i => exists_treeSmallDivisorMajorant lam (hblock i)
  let forest : List (BinaryTree Unit) := List.ofFn trees
  have hlength : forest.length = c.length := by
    simp [forest]
  have htwo : 2 ≤ forest.length := by omega
  have hsum :
      (forest.map BinaryTree.numLeaves).sum = n := by
    dsimp [forest]
    rw [List.map_ofFn, List.sum_ofFn]
    calc
      ∑ i, (BinaryTree.numLeaves ∘ trees) i =
          ∑ i, c.blocksFun i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hleaves i
      _ = n := c.sum_blocksFun
  have hforest_nonempty : forest ≠ [] := by
    intro hforest
    rw [hforest] at htwo
    simp at htwo
  have hcombined_mem :
      combineTrees forest ∈ BinaryTree.treesOfNumNodesEq (n - 1) := by
    rw [BinaryTree.mem_treesOfNumNodesEq]
    have hleaves : (combineTrees forest).numLeaves = n := by
      rw [combineTrees_numLeaves forest hforest_nonempty, hsum]
    rw [BinaryTree.numLeaves_eq_numNodes_succ] at hleaves
    omega
  calc
    (smallDivisor lam n)⁻¹ *
          ∏ i, treeSmallDivisorMajorant lam (c.blocksFun i) =
        (smallDivisor lam n)⁻¹ *
          (forest.map (binarySmallDivisorWeight lam)).prod := by
      congr 1
      dsimp [forest]
      rw [List.map_ofFn, List.prod_ofFn]
      apply Finset.prod_congr rfl
      intro i _
      exact hweights i
    _ = (smallDivisor lam
          (forest.map BinaryTree.numLeaves).sum)⁻¹ *
        (forest.map (binarySmallDivisorWeight lam)).prod := by
      rw [hsum]
    _ ≤ binarySmallDivisorWeight lam (combineTrees forest) :=
      divisor_prod_weight_le_combineTrees lam forest htwo
    _ ≤ treeSmallDivisorMajorant lam n := by
      rw [treeSmallDivisorMajorant, dif_neg hn]
      exact Finset.le_sup' _ hcombined_mem

/-- A real scalar series whose nonlinear coefficients are the negative
norms of the coefficients of `p`. -/
noncomputable def normMajorantSource
    (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => -‖p n‖)

/-- The convergent formal inverse used as the coefficient-counting
majorant. Its coefficients are nonnegative because of the sign chosen
in `normMajorantSource`. -/
noncomputable def normMajorant
    (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  (normMajorantSource p).rightInv
    (ContinuousLinearEquiv.refl ℝ ℝ) 0

private theorem norm_normMajorantSource
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    ‖normMajorantSource p n‖ = ‖p n‖ := by
  rw [normMajorantSource, FormalMultilinearSeries.ofScalars_norm]
  simp

theorem normMajorant_radius_pos
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (hp : 0 < p.radius) :
    0 < (normMajorant p).radius := by
  apply FormalMultilinearSeries.radius_rightInv_pos_of_radius_pos
  exact hp.trans_le
    (FormalMultilinearSeries.radius_le_of_le
      (p := normMajorantSource p) (q := p)
      (fun n => (norm_normMajorantSource p n).le))

private theorem normMajorant_applyComposition_one
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    {n : ℕ} (c : Composition n) :
    (normMajorant p).applyComposition c (fun _ => 1) =
      fun i => (normMajorant p).coeff (c.blocksFun i) := by
  funext i
  rfl

theorem normMajorant_coeff_of_two_le
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (normMajorant p).coeff (n + 2) =
      ∑ c ∈ ({c : Composition (n + 2) | 1 < c.length}.toFinset),
        ‖p c.length‖ *
          ∏ i, (normMajorant p).coeff (c.blocksFun i) := by
  have h := FormalMultilinearSeries.rightInv_coeff
    (normMajorantSource p) (ContinuousLinearEquiv.refl ℝ ℝ) 0
    (n + 2) (by omega)
  have happ := congrArg (fun q => q (fun _ => (1 : ℝ))) h
  change (normMajorant p).coeff (n + 2) = _ at happ
  have hfold :
      (normMajorantSource p).rightInv
          (ContinuousLinearEquiv.refl ℝ ℝ) 0 =
        normMajorant p := rfl
  rw [hfold] at happ
  simp only [ContinuousMultilinearMap.neg_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.refl_symm,
    ContinuousLinearEquiv.refl_apply,
    ContinuousMultilinearMap.sum_apply,
    FormalMultilinearSeries.compAlongComposition_apply,
    normMajorant_applyComposition_one,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    normMajorantSource, FormalMultilinearSeries.coeff_ofScalars,
    smul_eq_mul] at happ
  rw [happ]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  ring_nf

private theorem nonlinear_block_lt
    {n : ℕ} (c : Composition (n + 2)) (hc : 1 < c.length) :
    ∀ i, c.blocksFun i < n + 2 := by
  simp [← Composition.ne_single_iff (by omega : 0 < n + 2),
    Composition.eq_single_iff_length, ne_of_gt hc]

theorem normMajorant_coeff_nonneg
    (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    ∀ n, 0 ≤ (normMajorant p).coeff n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 =>
          simp [normMajorant, FormalMultilinearSeries.coeff,
            FormalMultilinearSeries.rightInv_coeff_zero]
      | 1 =>
          simp [normMajorant, FormalMultilinearSeries.coeff,
            FormalMultilinearSeries.rightInv_coeff_one]
      | n + 2 =>
          rw [normMajorant_coeff_of_two_le]
          apply Finset.sum_nonneg
          intro c hc
          apply mul_nonneg (norm_nonneg _)
          apply Finset.prod_nonneg
          intro i _
          have hclen : 1 < c.length := by simpa using hc
          exact ih (c.blocksFun i) (nonlinear_block_lt c hclen i)

@[simp]
theorem normMajorant_coeff_zero
    (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    (normMajorant p).coeff 0 = 0 := by
  simp [normMajorant, FormalMultilinearSeries.coeff,
    FormalMultilinearSeries.rightInv_coeff_zero]

@[simp]
theorem normMajorant_coeff_one
    (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    (normMajorant p).coeff 1 = 1 := by
  simp [normMajorant, FormalMultilinearSeries.coeff,
    FormalMultilinearSeries.rightInv_coeff_one]

private theorem norm_resonance_inv
    {lam : ℂ} (hlam : ‖lam‖ = 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖(lam ^ n - lam)⁻¹‖ = (smallDivisor lam n)⁻¹ := by
  rw [norm_inv, smallDivisor]
  congr 1
  calc
    ‖lam ^ n - lam‖ =
        ‖lam * (lam ^ (n - 1) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one, ← pow_succ']
      congr
      omega
    _ = ‖lam ^ (n - 1) - 1‖ := by
      rw [norm_mul, hlam, one_mul]

/-- The recursively constructed complex coefficients are bounded by
the convergent real inverse majorant, up to the exact worst
small-divisor tree product in their degree. -/
theorem norm_linearizationCoeff_le_treeMajorant
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (lam : ℂ) (hlam : ‖lam‖ = 1) :
    ∀ n,
      ‖linearizationCoeff p.coeff lam n‖ ≤
        treeSmallDivisorMajorant lam n *
          (normMajorant p).coeff n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 =>
          simp
      | 1 =>
          simpa using treeSmallDivisorMajorant_one_le lam 1
      | n + 2 =>
          let S :=
            ({c : Composition (n + 2) | 1 < c.length}.toFinset)
          have hterm (c : Composition (n + 2)) (hcS : c ∈ S) :
              (smallDivisor lam (n + 2))⁻¹ *
                  ‖p.coeff c.length *
                    ∏ i, linearizationCoeff p.coeff lam
                      (c.blocksFun i)‖ ≤
                treeSmallDivisorMajorant lam (n + 2) *
                  (‖p c.length‖ *
                    ∏ i, (normMajorant p).coeff
                      (c.blocksFun i)) := by
            have hc : 1 < c.length := by
              simpa [S] using hcS
            have hprod :
                ∏ i, ‖linearizationCoeff p.coeff lam
                    (c.blocksFun i)‖ ≤
                  ∏ i, (treeSmallDivisorMajorant lam
                      (c.blocksFun i) *
                    (normMajorant p).coeff
                      (c.blocksFun i)) := by
              apply Finset.prod_le_prod
              · intro i _
                exact norm_nonneg _
              intro i _
              exact ih (c.blocksFun i) (nonlinear_block_lt c hc i)
            have htree :=
              treeSmallDivisorMajorant_comp lam c hc
            have hdiv_nonneg :
                0 ≤ (smallDivisor lam (n + 2))⁻¹ := by
              apply inv_nonneg.mpr
              simp [smallDivisor]
            have hright_nonneg :
                0 ≤ ‖p c.length‖ *
                    ∏ i, (normMajorant p).coeff
                      (c.blocksFun i) := by
              apply mul_nonneg (norm_nonneg _)
              apply Finset.prod_nonneg
              intro i _
              exact normMajorant_coeff_nonneg p _
            rw [norm_mul, norm_prod]
            have hpcoeffnorm :
                ‖p.coeff c.length‖ = ‖p c.length‖ :=
              (FormalMultilinearSeries.norm_apply_eq_norm_coef
                (p := p) (n := c.length)).symm
            rw [hpcoeffnorm]
            calc
              (smallDivisor lam (n + 2))⁻¹ *
                    (‖p c.length‖ *
                      ∏ i, ‖linearizationCoeff p.coeff lam
                        (c.blocksFun i)‖)
                  ≤ (smallDivisor lam (n + 2))⁻¹ *
                    (‖p c.length‖ *
                      ∏ i, (treeSmallDivisorMajorant lam
                          (c.blocksFun i) *
                        (normMajorant p).coeff
                          (c.blocksFun i))) := by
                    exact mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
                      hdiv_nonneg
              _ = (smallDivisor lam (n + 2))⁻¹ *
                    (‖p c.length‖ *
                      ((∏ i, treeSmallDivisorMajorant lam
                          (c.blocksFun i)) *
                        ∏ i, (normMajorant p).coeff
                          (c.blocksFun i))) := by
                    rw [Finset.prod_mul_distrib]
              _ = ((smallDivisor lam (n + 2))⁻¹ *
                    ∏ i, treeSmallDivisorMajorant lam
                      (c.blocksFun i)) *
                  (‖p c.length‖ *
                    ∏ i, (normMajorant p).coeff
                      (c.blocksFun i)) := by ring
              _ ≤ treeSmallDivisorMajorant lam (n + 2) *
                  (‖p c.length‖ *
                    ∏ i, (normMajorant p).coeff
                      (c.blocksFun i)) := by
                    exact mul_le_mul_of_nonneg_right htree hright_nonneg
          rw [linearizationCoeff_of_two_le, norm_mul,
            norm_resonance_inv hlam (by omega)]
          have hdiv_nonneg :
              0 ≤ (smallDivisor lam (n + 2))⁻¹ := by
            apply inv_nonneg.mpr
            simp [smallDivisor]
          calc
            (smallDivisor lam (n + 2))⁻¹ *
                  ‖∑ c ∈ S,
                    p.coeff c.length *
                      ∏ i, linearizationCoeff p.coeff lam
                        (c.blocksFun i)‖
                ≤ (smallDivisor lam (n + 2))⁻¹ *
                  ∑ c ∈ S,
                    ‖p.coeff c.length *
                      ∏ i, linearizationCoeff p.coeff lam
                        (c.blocksFun i)‖ := by
                      exact mul_le_mul_of_nonneg_left
                        (norm_sum_le S _) hdiv_nonneg
            _ = ∑ c ∈ S,
                  (smallDivisor lam (n + 2))⁻¹ *
                    ‖p.coeff c.length *
                      ∏ i, linearizationCoeff p.coeff lam
                        (c.blocksFun i)‖ := by
                    rw [Finset.mul_sum]
            _ ≤ ∑ c ∈ S,
                  treeSmallDivisorMajorant lam (n + 2) *
                    (‖p c.length‖ *
                      ∏ i, (normMajorant p).coeff
                        (c.blocksFun i)) :=
              Finset.sum_le_sum hterm
            _ = treeSmallDivisorMajorant lam (n + 2) *
                  ∑ c ∈ S,
                    ‖p c.length‖ *
                      ∏ i, (normMajorant p).coeff
                        (c.blocksFun i) := by
                    rw [Finset.mul_sum]
            _ = treeSmallDivisorMajorant lam (n + 2) *
                (normMajorant p).coeff (n + 2) := by
                  rw [normMajorant_coeff_of_two_le]

/-- Real scalar multiplication as a continuous linear map. -/
noncomputable def realScalingCLM (D : ℝ) : ℝ →L[ℝ] ℝ :=
  D • ContinuousLinearMap.id ℝ ℝ

@[simp]
theorem realScalingCLM_apply (D x : ℝ) :
    realScalingCLM D x = D * x := by
  simp [realScalingCLM]

noncomputable def scaledNormMajorant
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (D : ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  (normMajorant p).compContinuousLinearMap (realScalingCLM D)

private theorem norm_scaledNormMajorant
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    ‖scaledNormMajorant p D n‖ =
      D ^ n * (normMajorant p).coeff n := by
  rw [FormalMultilinearSeries.norm_apply_eq_norm_coef]
  change ‖(scaledNormMajorant p D) n (fun _ => 1)‖ = _
  rw [scaledNormMajorant]
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
  have hfun :
      realScalingCLM D ∘ (fun _ : Fin n => (1 : ℝ)) =
        fun _ => D := by
    funext i
    simp
  rw [hfun, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    norm_smul, norm_pow, Real.norm_eq_abs,
    abs_of_nonneg hD, Real.norm_eq_abs,
    abs_of_nonneg (normMajorant_coeff_nonneg p n)]

private theorem scaledNormMajorant_radius_pos
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : 0 < p.radius) (D : ℝ) :
    0 < (scaledNormMajorant p D).radius := by
  have hq := normMajorant_radius_pos p hp
  have hdiv :
      (normMajorant p).radius / ‖realScalingCLM D‖ₑ ≤
        (scaledNormMajorant p D).radius :=
    FormalMultilinearSeries.div_le_radius_compContinuousLinearMap
      (normMajorant p) (realScalingCLM D)
  exact (ENNReal.div_pos hq.ne' enorm_ne_top).trans_le hdiv

/-- The formal Siegel linearization has a positive convergence radius. -/
theorem linearizationFMS_radius_pos
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : 0 < p.radius)
    (lam : ℂ) (hlam : ‖lam‖ = 1)
    {c : ℝ} {T : ℕ}
    (hc : 0 < c) (hT : T ≠ 0)
    (hnonzero : ∀ r : ℕ, r ≠ 0 → lam ^ r ≠ 1)
    (hbound : ∀ r : ℕ, r ≠ 0 →
      c / (r : ℝ) ^ T ≤ ‖lam ^ r - 1‖) :
    0 < (linearizationFMS p.coeff lam).radius := by
  let D : ℝ := max 1 (2 / c) * (((2 : ℝ) ^ T) ^ 4)
  have hD : 1 ≤ D := by
    dsimp [D]
    exact one_le_mul_of_one_le_of_one_le
      (le_max_left _ _)
      (one_le_pow₀ (one_le_pow₀ (by norm_num)))
  have hnorm (n : ℕ) :
      ‖linearizationFMS p.coeff lam n‖ ≤
        ‖scaledNormMajorant p D n‖ := by
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef,
      linearizationFMS_coeff,
      norm_scaledNormMajorant p (zero_le_one.trans hD)]
    calc
      ‖linearizationCoeff p.coeff lam n‖ ≤
          treeSmallDivisorMajorant lam n *
            (normMajorant p).coeff n :=
        norm_linearizationCoeff_le_treeMajorant p lam hlam n
      _ ≤ D ^ n * (normMajorant p).coeff n := by
        exact mul_le_mul_of_nonneg_right
          (treeSmallDivisorMajorant_le_pow
            hc hT hlam hnonzero hbound n)
          (normMajorant_coeff_nonneg p n)
  have hscaled : 0 < (scaledNormMajorant p D).radius :=
    scaledNormMajorant_radius_pos p hp D
  exact hscaled.trans_le
    (FormalMultilinearSeries.radius_le_of_le
      (p := linearizationFMS p.coeff lam)
      (q := scaledNormMajorant p D) hnorm)

end Submission
