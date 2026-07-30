import Submission.Thompson
import Submission.PermLift

namespace Submission.Thompson.Tree

namespace Presentation

/-- The basic associativity element, usually denoted `x₀`. -/
def xZero : V :=
  ⟨table rotationSource rotationTarget rotationEquiv, table_mem_V _ _ _⟩

/-- The basic transposition of the two top-level cylinders. -/
def topTransposition : V :=
  ⟨table topTree topTree (Equiv.sumComm Unit Unit), table_mem_V _ _ _⟩

/-- The standard right-spine copies of the associativity element. -/
def x (n : ℕ) : V := localVHom (List.replicate n true) xZero

/-- The standard right-spine copies of the top transposition. -/
def tau (n : ℕ) : V := localVHom (List.replicate n true) topTransposition

@[simp] theorem x_zero : x 0 = xZero := rfl

@[simp] theorem tau_zero : tau 0 = topTransposition := rfl

theorem xZero_map_right_prefix (suffix : List Bool) (z : Cantor) :
    (xZero : Equiv.Perm Cantor) (Cantor.prepend (true :: suffix) z) =
      Cantor.prepend (true :: true :: suffix) z := by
  change table rotationSource rotationTarget rotationEquiv
      (Cantor.prepend (true :: suffix) z) = _
  have h := table_prepend_path_append rotationSource rotationTarget rotationEquiv
    (Sum.inr ()) suffix z
  simpa only [show path rotationSource (Sum.inr ()) = [true] by rfl,
    show path rotationTarget (rotationEquiv (Sum.inr ())) = [true, true] by rfl,
    List.cons_append, List.nil_append] using h

theorem conjugate_local_right_by_xZero (suffix : List Bool) (g : V) :
    xZero * localVHom (true :: suffix) g * xZero⁻¹ =
      localVHom (true :: true :: suffix) g := by
  apply Subtype.ext
  simpa [xZero, localVHom, Cantor.localHom] using
    Cantor.conjugate_localPerm_of_map_prepend
      (xZero : Equiv.Perm Cantor) ((g : V) : Equiv.Perm Cantor)
      (xZero_map_right_prefix suffix)

theorem conjugate_x_succ (n : ℕ) :
    xZero * x (n + 1) * xZero⁻¹ = x (n + 2) := by
  simpa [x, List.replicate_succ] using
    conjugate_local_right_by_xZero (List.replicate n true) xZero

theorem conjugate_tau_succ (n : ℕ) :
    xZero * tau (n + 1) * xZero⁻¹ = tau (n + 2) := by
  simpa [tau, List.replicate_succ] using
    conjugate_local_right_by_xZero (List.replicate n true) topTransposition

/-- A finite candidate generating set for the eventual presentation. -/
def finiteGenerators : Set V := {xZero, x 1, tau 0, tau 1}

def finitelyGeneratedSubgroup : Subgroup V := Subgroup.closure finiteGenerators

theorem xZero_mem_finitelyGenerated : xZero ∈ finitelyGeneratedSubgroup := by
  exact Subgroup.subset_closure (by simp [finiteGenerators])

theorem x_one_mem_finitelyGenerated : x 1 ∈ finitelyGeneratedSubgroup := by
  exact Subgroup.subset_closure (by simp [finiteGenerators])

theorem tau_zero_mem_finitelyGenerated : tau 0 ∈ finitelyGeneratedSubgroup := by
  exact Subgroup.subset_closure (by simp [finiteGenerators])

theorem tau_one_mem_finitelyGenerated : tau 1 ∈ finitelyGeneratedSubgroup := by
  exact Subgroup.subset_closure (by simp [finiteGenerators])

theorem x_mem_finitelyGenerated (n : ℕ) : x n ∈ finitelyGeneratedSubgroup := by
  cases n with
  | zero => simpa using xZero_mem_finitelyGenerated
  | succ n =>
      induction n with
      | zero => exact x_one_mem_finitelyGenerated
      | succ n ih =>
          rw [← conjugate_x_succ n]
          exact finitelyGeneratedSubgroup.mul_mem
            (finitelyGeneratedSubgroup.mul_mem xZero_mem_finitelyGenerated ih)
            (finitelyGeneratedSubgroup.inv_mem xZero_mem_finitelyGenerated)

theorem tau_mem_finitelyGenerated (n : ℕ) : tau n ∈ finitelyGeneratedSubgroup := by
  cases n with
  | zero => exact tau_zero_mem_finitelyGenerated
  | succ n =>
      induction n with
      | zero => exact tau_one_mem_finitelyGenerated
      | succ n ih =>
          rw [← conjugate_tau_succ n]
          exact finitelyGeneratedSubgroup.mul_mem
            (finitelyGeneratedSubgroup.mul_mem xZero_mem_finitelyGenerated ih)
            (finitelyGeneratedSubgroup.inv_mem xZero_mem_finitelyGenerated)

/-!
## A finite self-similar presentation

The four generators below are `x₀`, its right-hand copy, the top swap, and its
right-hand copy.  Rather than enumerate a conventional presentation of `V`, we
take all true relations up to a fixed length and one image of those relations
under the right-localization substitution.  This is still a finite set.  The
second iterate of the substitution is conjugate to its first iterate modulo
short relations, so the substitution descends to the resulting presented
group.  This gives the two localization homomorphisms used in the tree
coherence argument below.
-/

abbrev Generator := Fin 4

abbrev Word := FreeGroup Generator

def generatorValue : Generator → V :=
  ![xZero, x 1, tau 0, tau 1]

def evaluation : Word →* V := FreeGroup.lift generatorValue

@[simp] theorem evaluation_of (i : Generator) :
    evaluation (FreeGroup.of i) = generatorValue i := by
  simp [evaluation]

def a : Word := FreeGroup.of 0

def b : Word := FreeGroup.of 1

def s : Word := FreeGroup.of 2

def t : Word := FreeGroup.of 3

def rightGenerator : Generator → Word :=
  ![b, a * b * a⁻¹, t, a * t * a⁻¹]

/-- The substitution representing localization in the right top-level
cylinder. -/
def rightWord : Word →* Word := FreeGroup.lift rightGenerator

/-- The corresponding substitution for the left top-level cylinder. -/
def leftWord : Word →* Word :=
  (MulAut.conj s).toMonoidHom.comp rightWord

@[simp] theorem evaluation_a : evaluation a = xZero := by
  simp [evaluation, a, generatorValue]

@[simp] theorem evaluation_b : evaluation b = x 1 := by
  simp [evaluation, b, generatorValue]

@[simp] theorem evaluation_s : evaluation s = tau 0 := by
  simp [evaluation, s, generatorValue]

@[simp] theorem evaluation_t : evaluation t = tau 1 := by
  simp [evaluation, t, generatorValue]

theorem evaluation_rightWord (w : Word) :
    evaluation (rightWord w) = localVHom [true] (evaluation w) := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      fin_cases i
      · rfl
      · simpa [rightWord, rightGenerator, evaluation, generatorValue, a, b, x,
          localVHom, Cantor.localPerm] using
          conjugate_x_succ 0
      · rfl
      · simpa [rightWord, rightGenerator, evaluation, generatorValue, a, t, tau,
          localVHom, Cantor.localPerm] using
          conjugate_tau_succ 0
  | inv_of i hi => simpa using congrArg Inv.inv hi
  | mul u v hu hv => simp [hu, hv]

/-- A deliberately generous bound for all of the local coherence diagrams
used below. -/
def relationBound : ℕ := 1000

def boundedKernel : Set Word :=
  {w | evaluation w = 1 ∧ FreeGroup.norm w ≤ relationBound}

theorem boundedKernel_finite : boundedKernel.Finite := by
  let words : Set (List (Generator × Bool)) :=
    {l | l.length ≤ relationBound}
  have hwords : words.Finite := List.finite_length_le (Generator × Bool) relationBound
  have hpre : (FreeGroup.toWord ⁻¹' words).Finite :=
    hwords.preimage FreeGroup.toWord_injective.injOn
  apply hpre.subset
  intro w hw
  exact hw.2

/-- A finite relator set stable enough to define one step of localization. -/
def relations : Set Word := boundedKernel ∪ rightWord '' boundedKernel

theorem relations_finite : relations.Finite :=
  boundedKernel_finite.union (boundedKernel_finite.image rightWord)

theorem relation_evaluates_one {w : Word} (hw : w ∈ relations) : evaluation w = 1 := by
  rcases hw with hw | ⟨u, hu, rfl⟩
  · exact hw.1
  · rw [evaluation_rightWord, hu.1]
    simp

abbrev P := PresentedGroup relations

def quotientMap : Word →* P := PresentedGroup.mk relations

/-- Evaluation of the finite presentation in the concrete tree-table group. -/
def toV : P →* V :=
  PresentedGroup.toGroup (f := generatorValue) (by
    intro w hw
    simpa [evaluation] using relation_evaluates_one hw)

@[simp] theorem toV_quotientMap (w : Word) :
    toV (quotientMap w) = evaluation w := by
  rfl

@[simp] theorem coe_localVHom_singleton (b : Bool) (g : V) :
    ((localVHom [b] g : V) : Equiv.Perm Cantor) =
      Cantor.branchPerm b (g : Equiv.Perm Cantor) := by
  rfl

theorem quotientMap_eq_of_bounded {u v : Word}
    (heval : evaluation u = evaluation v)
    (hbound : FreeGroup.norm (u * v⁻¹) ≤ relationBound) :
    quotientMap u = quotientMap v := by
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact Or.inl ⟨by simpa using congrArg (fun z => z * (evaluation v)⁻¹) heval,
    hbound⟩

theorem quotientMap_one_of_bounded {w : Word}
    (heval : evaluation w = 1)
    (hbound : FreeGroup.norm w ≤ relationBound) :
    quotientMap w = 1 := by
  exact PresentedGroup.one_of_mem (Or.inl ⟨heval, hbound⟩)

theorem evaluation_rightWord_rightWord (w : Word) :
    evaluation (rightWord (rightWord w)) =
      evaluation (a * rightWord w * a⁻¹) := by
  rw [map_mul, map_mul, map_inv, evaluation_a, evaluation_rightWord,
    evaluation_rightWord]
  simpa [localVHom, Cantor.localHom, Cantor.localPerm] using
    (conjugate_local_right_by_xZero [] (evaluation w)).symm

theorem quotientMap_rightWord_rightWord (w : Word) :
    quotientMap (rightWord (rightWord w)) =
      quotientMap (a * rightWord w * a⁻¹) := by
  let lhs : Word →* P := quotientMap.comp (rightWord.comp rightWord)
  let rhs : Word →* P :=
    (MulAut.conj (quotientMap a)).toMonoidHom.comp (quotientMap.comp rightWord)
  have heq : lhs = rhs := by
    apply FreeGroup.ext_hom
    intro i
    apply quotientMap_eq_of_bounded
    · exact evaluation_rightWord_rightWord (FreeGroup.of i)
    · fin_cases i <;>
        decide
  exact DFunLike.congr_fun heq w

theorem rightWord_normalClosure :
    Subgroup.normalClosure relations ≤
      (Subgroup.normalClosure relations).comap rightWord := by
  apply Subgroup.normalClosure_le_normal
  intro w hw
  change rightWord w ∈ Subgroup.normalClosure relations
  rw [← PresentedGroup.mk_eq_one_iff]
  rcases hw with hw | ⟨u, hu, rfl⟩
  · exact PresentedGroup.one_of_mem (Or.inr ⟨w, hw, rfl⟩)
  · change quotientMap (rightWord (rightWord u)) = 1
    rw [quotientMap_rightWord_rightWord]
    have hright : quotientMap (rightWord u) = 1 :=
      PresentedGroup.one_of_mem (Or.inr ⟨u, hu, rfl⟩)
    simp [hright]

/-- Localization in the right top-level cylinder, now descended to the finite
presented group. -/
def rightP : P →* P :=
  QuotientGroup.map (Subgroup.normalClosure relations)
    (Subgroup.normalClosure relations) rightWord rightWord_normalClosure

@[simp] theorem rightP_quotientMap (w : Word) :
    rightP (quotientMap w) = quotientMap (rightWord w) :=
  rfl

/-- Localization in the left top-level cylinder.  It is obtained from right
localization by the top swap. -/
def leftP : P →* P :=
  (MulAut.conj (quotientMap s)).toMonoidHom.comp rightP

@[simp] theorem leftP_apply (z : P) :
    leftP z = quotientMap s * rightP z * (quotientMap s)⁻¹ :=
  rfl

theorem topTransposition_map_right (z : Cantor) :
    (topTransposition : Equiv.Perm Cantor) (Cantor.prepend [true] z) =
      Cantor.prepend [false] z := by
  change table topTree topTree (Equiv.sumComm Unit Unit)
      (Cantor.prepend [true] z) = _
  have h := table_prepend_path_append topTree topTree (Equiv.sumComm Unit Unit)
    (Sum.inr ()) [] z
  change table topTree topTree (Equiv.sumComm Unit Unit)
      (Cantor.prepend (path topTree (Sum.inr ()) ++ []) z) =
    Cantor.prepend
      (path topTree ((Equiv.sumComm Unit Unit) (Sum.inr ())) ++ []) z at h
  simpa only [show path topTree (Sum.inr ()) = [true] by rfl,
    show path topTree ((Equiv.sumComm Unit Unit) (Sum.inr ())) = [false] by rfl,
    List.append_nil] using h

theorem conjugate_local_right_by_topTransposition (g : V) :
    topTransposition * localVHom [true] g * topTransposition⁻¹ =
      localVHom [false] g := by
  apply Subtype.ext
  simpa [topTransposition, localVHom, Cantor.localHom] using
    Cantor.conjugate_localPerm_of_map_prepend
      (topTransposition : Equiv.Perm Cantor) ((g : V) : Equiv.Perm Cantor)
      topTransposition_map_right

theorem evaluation_leftWord (w : Word) :
    evaluation (s * rightWord w * s⁻¹) = localVHom [false] (evaluation w) := by
  rw [map_mul, map_mul, map_inv, evaluation_s, evaluation_rightWord]
  exact conjugate_local_right_by_topTransposition (evaluation w)

theorem evaluation_leftWord' (w : Word) :
    evaluation (leftWord w) = localVHom [false] (evaluation w) :=
  evaluation_leftWord w

theorem localVHom_false_commute_true (g h : V) :
    Commute (localVHom [false] g) (localVHom [true] h) := by
  change localVHom [false] g * localVHom [true] h =
    localVHom [true] h * localVHom [false] g
  apply Subtype.ext
  exact (Cantor.localPerm_commute_of_disjoint
    (Cantor.cylinder_disjoint_of_incomparable (by simp) (by simp))
    (g : Equiv.Perm Cantor) (h : Equiv.Perm Cantor)).eq

theorem leftP_rightP_of_commute (i j : Generator) :
    Commute (leftP (PresentedGroup.of i)) (rightP (PresentedGroup.of j)) := by
  change leftP (PresentedGroup.of i) * rightP (PresentedGroup.of j) =
    rightP (PresentedGroup.of j) * leftP (PresentedGroup.of i)
  change quotientMap
      ((s * rightWord (FreeGroup.of i) * s⁻¹) * rightWord (FreeGroup.of j)) =
    quotientMap
      (rightWord (FreeGroup.of j) * (s * rightWord (FreeGroup.of i) * s⁻¹))
  apply quotientMap_eq_of_bounded
  · calc
      evaluation
            ((s * rightWord (FreeGroup.of i) * s⁻¹) *
              rightWord (FreeGroup.of j)) =
          evaluation (s * rightWord (FreeGroup.of i) * s⁻¹) *
            evaluation (rightWord (FreeGroup.of j)) := map_mul _ _ _
      _ = localVHom [false] (generatorValue i) *
            localVHom [true] (generatorValue j) := by
          rw [evaluation_leftWord, evaluation_rightWord, evaluation_of,
            evaluation_of]
      _ = localVHom [true] (generatorValue j) *
            localVHom [false] (generatorValue i) :=
          (localVHom_false_commute_true (generatorValue i) (generatorValue j)).eq
      _ = evaluation
            (rightWord (FreeGroup.of j) *
              (s * rightWord (FreeGroup.of i) * s⁻¹)) := by
          rw [map_mul, evaluation_rightWord, evaluation_leftWord, evaluation_of,
            evaluation_of]
  · fin_cases i <;> fin_cases j <;> decide

theorem leftP_rightP_commute (x y : P) : Commute (leftP x) (rightP y) := by
  have hgenRight (j : Generator) (x : P) :
      Commute (leftP x) (rightP (PresentedGroup.of j)) := by
    have hx : x ∈
        (Subgroup.centralizer {rightP (PresentedGroup.of j)}).comap leftP := by
      apply PresentedGroup.generated_by relations
      intro i
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (leftP_rightP_of_commute i j).eq
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hx
    exact hx
  have hy : y ∈ (Subgroup.centralizer {leftP x}).comap rightP := by
    apply PresentedGroup.generated_by relations
    intro j
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (hgenRight j x).eq.symm
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hy
  exact hy.symm

theorem toV_rightP (z : P) :
    toV (rightP z) = localVHom [true] (toV z) := by
  induction z using PresentedGroup.induction_on with
  | H w =>
      change toV (rightP (quotientMap w)) = localVHom [true] (toV (quotientMap w))
      rw [rightP_quotientMap, toV_quotientMap, toV_quotientMap]
      exact evaluation_rightWord w

theorem toV_leftP (z : P) :
    toV (leftP z) = localVHom [false] (toV z) := by
  rw [leftP_apply, map_mul, map_mul, map_inv, toV_quotientMap, evaluation_s,
    toV_rightP]
  exact conjugate_local_right_by_topTransposition (toV z)

@[simp] theorem leftP_quotientMap (w : Word) :
    leftP (quotientMap w) = quotientMap (leftWord w) :=
  rfl

/-- Put two presented elements in the two disjoint top-level cylinders. -/
def tensorP : P × P →* P where
  toFun z := leftP z.1 * rightP z.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    calc
      leftP x.1 * leftP y.1 * (rightP x.2 * rightP y.2) =
          leftP x.1 * (leftP y.1 * rightP x.2) * rightP y.2 := by
            simp [mul_assoc]
      _ = leftP x.1 * (rightP x.2 * leftP y.1) * rightP y.2 := by
            rw [(leftP_rightP_commute y.1 x.2).eq]
      _ = (leftP x.1 * rightP x.2) * (leftP y.1 * rightP y.2) := by
            simp [mul_assoc]

@[simp] theorem tensorP_apply (x y : P) :
    tensorP (x, y) = leftP x * rightP y :=
  rfl

theorem toV_tensorP (x y : P) :
    toV (tensorP (x, y)) =
      localVHom [false] (toV x) * localVHom [true] (toV y) := by
  rw [tensorP_apply, map_mul, toV_leftP, toV_rightP]

def assocP : P := quotientMap a

def swapP : P := quotientMap s

theorem evaluation_swap_square : evaluation (s * s) = 1 := by
  rw [map_mul, evaluation_s]
  rw [tau_zero]
  apply Subtype.ext
  change table topTree topTree (Equiv.sumComm Unit Unit) *
      table topTree topTree (Equiv.sumComm Unit Unit) = 1
  rw [table_mul_table_same_middle]
  convert table_refl topTree using 2
  apply Equiv.ext
  intro i
  cases i <;> rfl

theorem swapP_square : swapP * swapP = 1 := by
  change quotientMap (s * s) = 1
  apply quotientMap_one_of_bounded evaluation_swap_square
  decide

@[simp] theorem swapP_inv : swapP⁻¹ = swapP := by
  exact (eq_inv_of_mul_eq_one_right swapP_square).symm

/-- The stable swap of the first two leaves of every right vine having at
least three leaves. -/
def headWord : Word := a * leftWord s * a⁻¹

def headSwapP : P := quotientMap headWord

def headEquiv : Equiv.Perm rotationTarget.Leaf :=
  rotationEquiv.symm.trans (siblingSwap.trans rotationEquiv)

theorem evaluation_headWord :
    evaluation headWord =
      (⟨table rotationTarget rotationTarget headEquiv,
        table_mem_V _ _ _⟩ : V) := by
  rw [headWord, map_mul, map_mul, map_inv, evaluation_a,
    evaluation_leftWord', evaluation_s]
  apply Subtype.ext
  have hlocal :
      Cantor.branchPerm false
          (table topTree topTree (Equiv.sumComm Unit Unit)) =
        table rotationSource rotationSource siblingSwap := by
    rw [branchPerm_false_table, siblingSwap_eq_sumCongr]
    rfl
  have hinv :
      (table rotationSource rotationTarget rotationEquiv)⁻¹ =
        table rotationTarget rotationSource rotationEquiv.symm :=
    table_symm rotationSource rotationTarget rotationEquiv
  change table rotationSource rotationTarget rotationEquiv *
      Cantor.branchPerm false (table topTree topTree (Equiv.sumComm Unit Unit)) *
        (table rotationSource rotationTarget rotationEquiv)⁻¹ =
    table rotationTarget rotationTarget headEquiv
  rw [hlocal, hinv, mul_assoc,
    table_mul_table_same_middle, table_mul_table_same_middle]
  rfl

def rightBaseEquiv : Equiv.Perm rotationTarget.Leaf :=
  (Equiv.refl Unit).sumCongr (Equiv.sumComm Unit Unit)

theorem evaluation_right_s :
    evaluation (rightWord s) =
      (⟨table rotationTarget rotationTarget rightBaseEquiv,
        table_mem_V _ _ _⟩ : V) := by
  rw [evaluation_rightWord, evaluation_s]
  apply Subtype.ext
  simpa [topTransposition, localVHom, Cantor.localPerm, rotationTarget,
    rightBaseEquiv, topTree] using
    branchPerm_true_table topTree topTree (Equiv.sumComm Unit Unit)

theorem evaluation_head_right_s_braid :
    evaluation (headWord * rightWord s * headWord) =
      evaluation (rightWord s * headWord * rightWord s) := by
  simp only [map_mul, evaluation_headWord, evaluation_right_s]
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [table_mul_table_same_middle, table_mul_table_same_middle,
    table_mul_table_same_middle, table_mul_table_same_middle]
  congr 1
  decide

def headExpandPieces : rotationTarget.Leaf → Tree
  | Sum.inl _ => .leaf
  | Sum.inr (Sum.inl _) => .leaf
  | Sum.inr (Sum.inr _) => topTree

theorem headExpand_source :
    expand rotationTarget headExpandPieces = rightVine 3 := by
  rfl

theorem headExpand_target :
    expand rotationTarget (fun j => headExpandPieces (headEquiv.symm j)) =
      rightVine 3 := by
  decide

def expandedHeadEquiv : Equiv.Perm (rightVine 3).Leaf :=
  ((leafEquivOfEq headExpand_source).symm.trans
      (expandEquiv headEquiv headExpandPieces)).trans
    (leafEquivOfEq headExpand_target)

theorem table_expandedHeadEquiv :
    table (rightVine 3) (rightVine 3) expandedHeadEquiv =
      table rotationTarget rotationTarget headEquiv := by
  calc
    table (rightVine 3) (rightVine 3) expandedHeadEquiv =
        table (rightVine 3)
          (expand rotationTarget
            (fun j => headExpandPieces (headEquiv.symm j)))
          ((leafEquivOfEq headExpand_source).symm.trans
            (expandEquiv headEquiv headExpandPieces)) := by
              exact table_change_target _ headExpand_target
    _ = table (expand rotationTarget headExpandPieces)
          (expand rotationTarget
            (fun j => headExpandPieces (headEquiv.symm j)))
          (expandEquiv headEquiv headExpandPieces) := by
              exact table_change_source _ headExpand_source
    _ = table rotationTarget rotationTarget headEquiv :=
      table_expand rotationTarget rotationTarget headEquiv headExpandPieces

def rightHeadEquiv : Equiv.Perm (rightVine 3).Leaf :=
  (Equiv.refl Unit).sumCongr headEquiv

theorem evaluation_right_headWord :
    evaluation (rightWord headWord) =
      (⟨table (rightVine 3) (rightVine 3) rightHeadEquiv,
        table_mem_V _ _ _⟩ : V) := by
  rw [evaluation_rightWord, evaluation_headWord]
  apply Subtype.ext
  change Cantor.branchPerm true (table rotationTarget rotationTarget headEquiv) =
    table (rightVine 3) (rightVine 3) rightHeadEquiv
  have h := branchPerm_true_table rotationTarget rotationTarget headEquiv
  change Cantor.branchPerm true (table rotationTarget rotationTarget headEquiv) =
    table (rightVine 3) (rightVine 3) rightHeadEquiv at h
  exact h

theorem evaluation_head_right_head_braid :
    evaluation (headWord * rightWord headWord * headWord) =
      evaluation (rightWord headWord * headWord * rightWord headWord) := by
  simp only [map_mul, evaluation_headWord, evaluation_right_headWord]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, ← table_expandedHeadEquiv]
  rw [table_mul_table_same_middle, table_mul_table_same_middle,
    table_mul_table_same_middle, table_mul_table_same_middle]
  congr 1
  decide

set_option maxRecDepth 100000 in
theorem evaluation_assoc_pentagon :
    evaluation (rightWord a * a * leftWord a) = evaluation (a * a) := by
  simp only [map_mul, evaluation_rightWord, evaluation_leftWord', evaluation_a]
  apply Subtype.ext
  ext z
  cases h₀ : Cantor.head z <;>
    cases h₁ : Cantor.head (Cantor.tail z) <;>
    cases h₂ : Cantor.head (Cantor.tail (Cantor.tail z)) <;>
    simp [Equiv.Perm.mul_apply, localVHom, Cantor.localPerm,
      Cantor.branchPerm, Cantor.branchFun, xZero, table_apply, rotationSource,
      rotationTarget, rotationEquiv, Tree.encode, Tree.decode, h₀, h₁, h₂]

set_option maxRecDepth 100000 in
theorem evaluation_swap_hexagon_left :
    evaluation (a * leftWord s * a⁻¹ * rightWord s * a) = evaluation s := by
  simp only [map_mul, map_inv, evaluation_a, evaluation_s, evaluation_leftWord',
    evaluation_rightWord]
  apply Subtype.ext
  ext z
  cases h₀ : Cantor.head z <;>
    cases h₁ : Cantor.head (Cantor.tail z) <;>
    simp [Equiv.Perm.mul_apply, localVHom, Cantor.localPerm,
      Cantor.branchPerm, Cantor.branchFun, xZero, topTransposition, table_apply,
      topTree, rotationSource, rotationTarget, rotationEquiv, Tree.encode,
      Tree.decode, h₀, h₁] <;>
    rw [← Cantor.cons_head_tail (Cantor.tail z), h₁] <;> rfl

set_option maxRecDepth 100000 in
theorem evaluation_swap_hexagon_right :
    evaluation (a⁻¹ * rightWord s * a * leftWord s * a⁻¹) = evaluation s := by
  simp only [map_mul, map_inv, evaluation_a, evaluation_s, evaluation_leftWord',
    evaluation_rightWord]
  apply Subtype.ext
  ext z
  cases h₀ : Cantor.head z <;>
    cases h₁ : Cantor.head (Cantor.tail z) <;>
    simp [Equiv.Perm.mul_apply, localVHom, Cantor.localPerm,
      Cantor.branchPerm, Cantor.branchFun, xZero, topTransposition, table_apply,
      topTree, rotationSource, rotationTarget, rotationEquiv, Tree.encode,
      Tree.decode, h₀, h₁] <;>
    rw [← Cantor.cons_head_tail (Cantor.tail z), h₁] <;> rfl

theorem headSwapP_eq :
    headSwapP = assocP * leftP swapP * assocP⁻¹ := by
  rfl

theorem headSwapP_square : headSwapP * headSwapP = 1 := by
  have hleft : leftP swapP * leftP swapP = 1 := by
    rw [← map_mul, swapP_square, map_one]
  rw [headSwapP_eq]
  calc
    (assocP * leftP swapP * assocP⁻¹) *
          (assocP * leftP swapP * assocP⁻¹) =
        assocP * (leftP swapP * leftP swapP) * assocP⁻¹ := by group
    _ = 1 := by rw [hleft]; simp

@[simp] theorem headSwapP_inv : headSwapP⁻¹ = headSwapP := by
  exact (eq_inv_of_mul_eq_one_right headSwapP_square).symm

theorem headSwapP_braid_right_swapP :
    headSwapP * rightP swapP * headSwapP =
      rightP swapP * headSwapP * rightP swapP := by
  rw [headSwapP, swapP, rightP_quotientMap, ← map_mul, ← map_mul,
    ← map_mul, ← map_mul]
  apply quotientMap_eq_of_bounded evaluation_head_right_s_braid
  decide

theorem headSwapP_braid_right_headSwapP :
    headSwapP * rightP headSwapP * headSwapP =
      rightP headSwapP * headSwapP * rightP headSwapP := by
  rw [headSwapP, rightP_quotientMap, ← map_mul, ← map_mul,
    ← map_mul, ← map_mul]
  apply quotientMap_eq_of_bounded evaluation_head_right_head_braid
  decide

theorem assocP_pentagon :
    rightP assocP * assocP * leftP assocP = assocP * assocP := by
  rw [assocP, rightP_quotientMap, leftP_quotientMap, ← map_mul, ← map_mul,
    ← map_mul]
  apply quotientMap_eq_of_bounded evaluation_assoc_pentagon
  decide

theorem swapP_hexagon_left :
    assocP * leftP swapP * assocP⁻¹ * rightP swapP * assocP = swapP := by
  have hq :
      quotientMap (a * leftWord s * a⁻¹ * rightWord s * a) =
        quotientMap s := by
    apply quotientMap_eq_of_bounded evaluation_swap_hexagon_left
    decide
  simpa only [assocP, swapP, leftP_quotientMap, rightP_quotientMap,
    map_mul, map_inv] using hq

theorem swapP_hexagon_right :
    assocP⁻¹ * rightP swapP * assocP * leftP swapP * assocP⁻¹ = swapP := by
  have hq :
      quotientMap (a⁻¹ * rightWord s * a * leftWord s * a⁻¹) =
        quotientMap s := by
    apply quotientMap_eq_of_bounded evaluation_swap_hexagon_right
    decide
  simpa only [assocP, swapP, leftP_quotientMap, rightP_quotientMap,
    map_mul, map_inv] using hq

theorem xZero_map_false_false (z : Cantor) :
    (xZero : Equiv.Perm Cantor) (Cantor.prepend [false, false] z) =
      Cantor.prepend [false] z := by
  change table rotationSource rotationTarget rotationEquiv
      (Cantor.prepend [false, false] z) = Cantor.prepend [false] z
  have h := table_prepend_path_append rotationSource rotationTarget rotationEquiv
    (Sum.inl (Sum.inl ())) [] z
  change table rotationSource rotationTarget rotationEquiv
      (Cantor.prepend (path rotationSource (Sum.inl (Sum.inl ())) ++ []) z) =
    Cantor.prepend
      (path rotationTarget (rotationEquiv (Sum.inl (Sum.inl ()))) ++ []) z at h
  simpa only [show path rotationSource (Sum.inl (Sum.inl ())) = [false, false] by rfl,
    show path rotationTarget (rotationEquiv (Sum.inl (Sum.inl ()))) = [false] by rfl,
    List.append_nil] using h

theorem xZero_map_false_true (z : Cantor) :
    (xZero : Equiv.Perm Cantor) (Cantor.prepend [false, true] z) =
      Cantor.prepend [true, false] z := by
  change table rotationSource rotationTarget rotationEquiv
      (Cantor.prepend [false, true] z) = Cantor.prepend [true, false] z
  have h := table_prepend_path_append rotationSource rotationTarget rotationEquiv
    (Sum.inl (Sum.inr ())) [] z
  change table rotationSource rotationTarget rotationEquiv
      (Cantor.prepend (path rotationSource (Sum.inl (Sum.inr ())) ++ []) z) =
    Cantor.prepend
      (path rotationTarget (rotationEquiv (Sum.inl (Sum.inr ()))) ++ []) z at h
  simpa only [show path rotationSource (Sum.inl (Sum.inr ())) = [false, true] by rfl,
    show path rotationTarget (rotationEquiv (Sum.inl (Sum.inr ()))) = [true, false] by rfl,
    List.append_nil] using h

theorem conjugate_local_false_false_by_xZero (g : V) :
    xZero * localVHom [false, false] g * xZero⁻¹ = localVHom [false] g := by
  apply Subtype.ext
  simpa [xZero, localVHom, Cantor.localHom] using
    Cantor.conjugate_localPerm_of_map_prepend
      (xZero : Equiv.Perm Cantor) ((g : V) : Equiv.Perm Cantor)
      xZero_map_false_false

theorem conjugate_local_false_true_by_xZero (g : V) :
    xZero * localVHom [false, true] g * xZero⁻¹ =
      localVHom [true, false] g := by
  apply Subtype.ext
  simpa [xZero, localVHom, Cantor.localHom] using
    Cantor.conjugate_localPerm_of_map_prepend
      (xZero : Equiv.Perm Cantor) ((g : V) : Equiv.Perm Cantor)
      xZero_map_false_true

theorem evaluation_assoc_left (w : Word) :
    evaluation (a * leftWord (leftWord w) * a⁻¹) = evaluation (leftWord w) := by
  rw [map_mul, map_mul, map_inv, evaluation_a, evaluation_leftWord',
    evaluation_leftWord']
  simpa [localVHom, Cantor.localHom, Cantor.localPerm] using
    conjugate_local_false_false_by_xZero (evaluation w)

theorem evaluation_assoc_middle (w : Word) :
    evaluation (a * leftWord (rightWord w) * a⁻¹) =
      evaluation (rightWord (leftWord w)) := by
  rw [map_mul, map_mul, map_inv, evaluation_a, evaluation_leftWord',
    evaluation_rightWord, evaluation_rightWord, evaluation_leftWord']
  simpa [localVHom, Cantor.localHom, Cantor.localPerm] using
    conjugate_local_false_true_by_xZero (evaluation w)

theorem assocP_leftP_leftP (z : P) :
    assocP * leftP (leftP z) * assocP⁻¹ = leftP z := by
  let lhs : P →* P :=
    (MulAut.conj assocP).toMonoidHom.comp (leftP.comp leftP)
  have heq : lhs = leftP := by
    apply PresentedGroup.ext
    intro i
    change quotientMap (a * leftWord (leftWord (FreeGroup.of i)) * a⁻¹) =
      quotientMap (leftWord (FreeGroup.of i))
    apply quotientMap_eq_of_bounded
    · exact evaluation_assoc_left (FreeGroup.of i)
    · fin_cases i <;> decide
  exact DFunLike.congr_fun heq z

theorem assocP_leftP_rightP (z : P) :
    assocP * leftP (rightP z) * assocP⁻¹ = rightP (leftP z) := by
  let lhs : P →* P :=
    (MulAut.conj assocP).toMonoidHom.comp (leftP.comp rightP)
  let rhs : P →* P := rightP.comp leftP
  have heq : lhs = rhs := by
    apply PresentedGroup.ext
    intro i
    change quotientMap (a * leftWord (rightWord (FreeGroup.of i)) * a⁻¹) =
      quotientMap (rightWord (leftWord (FreeGroup.of i)))
    apply quotientMap_eq_of_bounded
    · exact evaluation_assoc_middle (FreeGroup.of i)
    · fin_cases i <;> decide
  exact DFunLike.congr_fun heq z

theorem assocP_rightP (z : P) :
    assocP * rightP z * assocP⁻¹ = rightP (rightP z) := by
  induction z using PresentedGroup.induction_on with
  | H w =>
      change quotientMap (a * rightWord w * a⁻¹) =
        quotientMap (rightWord (rightWord w))
      exact (quotientMap_rightWord_rightWord w).symm

theorem assocP_leftP_headSwapP :
    assocP * leftP headSwapP * assocP⁻¹ =
      (rightP assocP)⁻¹ * headSwapP * rightP assocP := by
  have hp : assocP * leftP assocP =
      (rightP assocP)⁻¹ * assocP * assocP := by
    calc
      assocP * leftP assocP =
          (rightP assocP)⁻¹ *
            (rightP assocP * assocP * leftP assocP) := by group
      _ = (rightP assocP)⁻¹ * (assocP * assocP) := by
        rw [assocP_pentagon]
      _ = (rightP assocP)⁻¹ * assocP * assocP := by group
  rw [headSwapP_eq, map_mul, map_mul, map_inv]
  calc
    assocP *
          (leftP assocP * leftP (leftP swapP) * (leftP assocP)⁻¹) *
        assocP⁻¹ =
      (assocP * leftP assocP) * leftP (leftP swapP) *
        (assocP * leftP assocP)⁻¹ := by group
    _ = ((rightP assocP)⁻¹ * assocP * assocP) *
        leftP (leftP swapP) *
          ((rightP assocP)⁻¹ * assocP * assocP)⁻¹ := by rw [hp]
    _ = (rightP assocP)⁻¹ * assocP *
          (assocP * leftP (leftP swapP) * assocP⁻¹) *
        assocP⁻¹ * rightP assocP := by group
    _ = (rightP assocP)⁻¹ *
          (assocP * leftP swapP * assocP⁻¹) * rightP assocP := by
            rw [assocP_leftP_leftP]
            group

theorem headSwapP_commute_right_right (z : P) :
    Commute headSwapP (rightP (rightP z)) := by
  have h := (leftP_rightP_commute swapP z).map
    (MulAut.conj assocP).toMonoidHom
  change Commute (assocP * leftP swapP * assocP⁻¹)
    (assocP * rightP z * assocP⁻¹) at h
  rw [assocP_rightP] at h
  simpa only [headSwapP_eq] using h

/-! ### Canonical tree flattening -/

/-- `vineIndex t + 1` is the number of leaves of `t`. -/
def vineIndex : Tree → ℕ
  | .leaf => 0
  | .fork left right => vineIndex left + vineIndex right + 1

@[simp] theorem card_leaf_eq_vineIndex_add_one (tree : Tree) :
    Fintype.card tree.Leaf = vineIndex tree + 1 := by
  induction tree with
  | leaf => rfl
  | fork left right ihLeft ihRight =>
      simp [Tree.Leaf, vineIndex, ihLeft, ihRight]
      omega

theorem table_equiv_injective (source target : Tree) :
    Function.Injective (table source target) := by
  intro e f hef
  apply Equiv.ext
  intro i
  let z : Cantor := fun _ => false
  have hvalue := Equiv.congr_fun hef (Tree.decode source (i, z))
  have hfirst := congrArg (fun x => (Tree.encode target x).1) hvalue
  simpa [table_apply] using hfirst

set_option maxRecDepth 10000 in
theorem table_sumAssoc (aTree bTree cTree : Tree) :
    table (.fork (.fork aTree bTree) cTree)
        (.fork aTree (.fork bTree cTree))
        (Equiv.sumAssoc aTree.Leaf bTree.Leaf cTree.Leaf) =
      table rotationSource rotationTarget rotationEquiv := by
  apply Equiv.ext
  intro z
  cases h₀ : Cantor.head z <;>
    cases h₁ : Cantor.head (Cantor.tail z) <;>
    simp [table_apply, rotationSource, rotationTarget, rotationEquiv,
      Tree.encode, Tree.decode, h₀, h₁]

theorem assocEquiv_eq_sumAssoc (aTree bTree cTree : Tree) :
    assocEquiv aTree bTree cTree =
      Equiv.sumAssoc aTree.Leaf bTree.Leaf cTree.Leaf := by
  apply table_equiv_injective
  rw [table_assocEquiv, table_sumAssoc]

/-- The order-preserving reassociation of a pair of right vines into one
right vine. -/
theorem mergeTarget_succ (m n : ℕ) :
    Tree.fork .leaf (rightVine (m + n + 1)) =
      rightVine (m + 1 + n + 1) := by
  rw [show m + 1 + n = m + n + 1 by omega]
  rfl

def mergeEquiv : ∀ m n : ℕ,
    (Tree.fork (rightVine m) (rightVine n)).Leaf ≃
      (rightVine (m + n + 1)).Leaf
  | 0, n => leafEquivOfEq (by simp [rightVine])
  | m + 1, n =>
      ((assocEquiv .leaf (rightVine m) (rightVine n)).trans
          ((Equiv.refl Unit).sumCongr (mergeEquiv m n))).trans
        (leafEquivOfEq (mergeTarget_succ m n))

def vineCast {m n : ℕ} (h : m = n) :
    (rightVine m).Leaf ≃ (rightVine n).Leaf :=
  leafEquivOfEq (congrArg rightVine h)

theorem mergeEquiv_natural {m m' n n' : ℕ} (hLeft : m = m')
    (hRight : n = n') :
    (mergeEquiv m' n').trans
        (vineCast (by omega : m' + n' + 1 = m + n + 1)) =
      ((vineCast hLeft.symm).sumCongr (vineCast hRight.symm)).trans
        (mergeEquiv m n) := by
  cases hLeft
  cases hRight
  apply Equiv.ext
  intro i
  simp [vineCast, leafEquivOfEq]

theorem mergeEquiv_zero (n : ℕ) :
    mergeEquiv 0 n = vineCast (by omega : n + 1 = 0 + n + 1) := by
  apply Equiv.ext
  intro i
  change cast _ i = cast _ i
  congr

/-- The word in the finite presentation implementing `mergeEquiv`. -/
def mergeP : ℕ → ℕ → P
  | 0, _ => 1
  | m + 1, n => rightP (mergeP m n) * assocP

theorem toV_mergeP (m n : ℕ) :
    toV (mergeP m n) =
      (⟨table (.fork (rightVine m) (rightVine n))
          (rightVine (m + n + 1)) (mergeEquiv m n), table_mem_V _ _ _⟩ : V) := by
  induction m with
  | zero =>
      apply Subtype.ext
      change 1 = table (.fork (rightVine 0) (rightVine n))
        (rightVine (0 + n + 1)) (mergeEquiv 0 n)
      let htree : Tree.fork (rightVine 0) (rightVine n) =
          rightVine (0 + n + 1) := by simp [rightVine]
      calc
        1 = table (.fork (rightVine 0) (rightVine n))
            (.fork (rightVine 0) (rightVine n)) (Equiv.refl _) :=
          (table_refl _).symm
        _ = table (.fork (rightVine 0) (rightVine n))
            (rightVine (0 + n + 1)) (mergeEquiv 0 n) := by
          simpa [mergeEquiv, htree] using
            (table_change_target (Equiv.refl
              (Tree.fork (rightVine 0) (rightVine n)).Leaf) htree).symm
  | succ m ih =>
      rw [mergeP, map_mul, toV_rightP, ih, assocP, toV_quotientMap,
        evaluation_a]
      apply Subtype.ext
      change Cantor.branchPerm true
          (table (.fork (rightVine m) (rightVine n))
            (rightVine (m + n + 1)) (mergeEquiv m n)) *
        table rotationSource rotationTarget rotationEquiv =
          table (.fork (rightVine (m + 1)) (rightVine n))
            (rightVine (m + 1 + n + 1)) (mergeEquiv (m + 1) n)
      rw [branchPerm_true_table]
      rw [← table_assocEquiv .leaf (rightVine m) (rightVine n)]
      rw [table_mul_table_same_middle]
      let base := (assocEquiv .leaf (rightVine m) (rightVine n)).trans
        ((Equiv.refl Unit).sumCongr (mergeEquiv m n))
      have hmerge : mergeEquiv (m + 1) n =
          base.trans (leafEquivOfEq (mergeTarget_succ m n)) := by
        rfl
      rw [hmerge]
      exact (table_change_target base (mergeTarget_succ m n)).symm

/-- The canonical order-preserving leaf equivalence from a tree to the right
vine with the same number of leaves. -/
def flattenEquiv : (tree : Tree) →
    tree.Leaf ≃ (rightVine (vineIndex tree)).Leaf
  | .leaf => Equiv.refl Unit
  | .fork left right =>
      ((flattenEquiv left).sumCongr (flattenEquiv right)).trans
        (mergeEquiv (vineIndex left) (vineIndex right))

/-- The corresponding element of the finite presented group. -/
def flattenP : Tree → P
  | .leaf => 1
  | .fork left right =>
      mergeP (vineIndex left) (vineIndex right) *
        tensorP (flattenP left, flattenP right)

theorem toV_flattenP (tree : Tree) :
    toV (flattenP tree) =
      (⟨table tree (rightVine (vineIndex tree)) (flattenEquiv tree),
        table_mem_V _ _ _⟩ : V) := by
  induction tree with
  | leaf =>
      apply Subtype.ext
      change 1 = table .leaf .leaf (Equiv.refl Unit)
      exact (table_refl .leaf).symm
  | fork left right ihLeft ihRight =>
      rw [flattenP, map_mul, toV_mergeP, toV_tensorP, ihLeft, ihRight]
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [coe_localVHom_singleton, coe_localVHom_singleton]
      rw [← table_fork]
      rw [table_mul_table_same_middle]
      rfl

/-! ### Permutations of canonical vines -/

/-- The left-to-right numbering of the leaves of a right vine. -/
def finVineEquiv : (n : ℕ) → Fin (n + 1) ≃ (rightVine n).Leaf
  | 0 =>
      { toFun := fun _ => ()
        invFun := fun _ => 0
        left_inv := fun i => (Fin.eq_zero i).symm
        right_inv := fun _ => rfl }
  | n + 1 =>
      { toFun := Fin.cases (Sum.inl ()) (fun i => Sum.inr (finVineEquiv n i))
        invFun := Sum.elim (fun _ => 0) (fun i => (finVineEquiv n).symm i |>.succ)
        left_inv := by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · rfl
          · simp
        right_inv := by
          intro i
          rcases i with (i | i)
          · cases i
            rfl
          · simp }

theorem finVineEquiv_vineCast {m n : ℕ} (h : m = n)
    (i : Fin (m + 1)) :
    vineCast h (finVineEquiv m i) =
      finVineEquiv n (Fin.cast (congrArg (fun k => k + 1) h) i) := by
  subst n
  rfl

theorem mergeZero_index (n : ℕ) (i : Fin (n + 2)) :
    (finVineEquiv (0 + n + 1)).symm
        (mergeEquiv 0 n (finVineEquiv (n + 1) i)) =
      Fin.cast (by omega) i := by
  rw [mergeEquiv_zero]
  apply (finVineEquiv (0 + n + 1)).symm_apply_eq.mpr
  exact finVineEquiv_vineCast (by omega : n + 1 = 0 + n + 1) i

theorem mergeTarget_index (m n : ℕ) (i : Fin (m + n + 3)) :
    (finVineEquiv (m + 1 + n + 1)).symm
        (leafEquivOfEq (mergeTarget_succ m n)
          (finVineEquiv (m + n + 2) i)) =
      Fin.cast (by omega) i := by
  let hIndex : m + n + 2 = m + 1 + n + 1 := by omega
  have hCast :
      leafEquivOfEq (mergeTarget_succ m n) = vineCast hIndex := by
    apply Equiv.ext
    intro x
    change cast _ x = cast _ x
    congr
  rw [hCast]
  apply (finVineEquiv (m + 1 + n + 1)).symm_apply_eq.mpr
  exact finVineEquiv_vineCast hIndex i

def vinePerm (n : ℕ) (e : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (rightVine n).Leaf :=
  (finVineEquiv n).permCongr e

theorem vinePerm_swap (n : ℕ) (i j : Fin (n + 1)) :
    vinePerm n (Equiv.swap i j) =
      Equiv.swap (finVineEquiv n i) (finVineEquiv n j) := by
  exact Equiv.symm_trans_swap_trans i j (finVineEquiv n)

@[simp] theorem vinePerm_one (n : ℕ) :
    vinePerm n 1 = 1 := by
  exact (finVineEquiv n).permCongr_refl

theorem vinePerm_mul (n : ℕ) (e f : Equiv.Perm (Fin (n + 1))) :
    vinePerm n (e * f) = vinePerm n e * vinePerm n f := by
  exact (finVineEquiv n).permCongrHom.map_mul e f

theorem sum_vinePerm_swap (n : ℕ) (i j : Fin (n + 1)) :
    (Equiv.refl Unit).sumCongr (vinePerm n (Equiv.swap i j)) =
      vinePerm (n + 1) (Equiv.swap i.succ j.succ) := by
  rw [vinePerm_swap, vinePerm_swap]
  have hi : finVineEquiv (n + 1) i.succ = Sum.inr (finVineEquiv n i) := rfl
  have hj : finVineEquiv (n + 1) j.succ = Sum.inr (finVineEquiv n j) := rfl
  rw [hi, hj]
  apply Equiv.ext
  rintro (x | x)
  · cases x
    change (Sum.inl () : Unit ⊕ (rightVine n).Leaf) =
      Equiv.swap (Sum.inr (finVineEquiv n i))
        (Sum.inr (finVineEquiv n j)) (Sum.inl ())
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)]
  · obtain ⟨k, rfl⟩ := (finVineEquiv n).surjective x
    by_cases hki : k = i
    · subst k
      change Sum.inr (Equiv.swap (finVineEquiv n i) (finVineEquiv n j)
          (finVineEquiv n i)) =
        Equiv.swap (Sum.inr (finVineEquiv n i))
          (Sum.inr (finVineEquiv n j)) (Sum.inr (finVineEquiv n i))
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    · by_cases hkj : k = j
      · subst k
        change Sum.inr (Equiv.swap (finVineEquiv n i) (finVineEquiv n j)
            (finVineEquiv n j)) =
          Equiv.swap (Sum.inr (finVineEquiv n i))
            (Sum.inr (finVineEquiv n j)) (Sum.inr (finVineEquiv n j))
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
      · have hki' : finVineEquiv n k ≠ finVineEquiv n i :=
          fun h => hki ((finVineEquiv n).injective h)
        have hkj' : finVineEquiv n k ≠ finVineEquiv n j :=
          fun h => hkj ((finVineEquiv n).injective h)
        change Sum.inr (Equiv.swap (finVineEquiv n i) (finVineEquiv n j)
            (finVineEquiv n k)) =
          Equiv.swap (Sum.inr (finVineEquiv n i))
            (Sum.inr (finVineEquiv n j)) (Sum.inr (finVineEquiv n k))
        rw [Equiv.swap_apply_of_ne_of_ne hki' hkj',
          Equiv.swap_apply_of_ne_of_ne (by simpa using hki') (by simpa using hkj')]

@[simp] theorem vinePerm_head_left (n : ℕ) :
    vinePerm (n + 2) (Equiv.swap 0 1) (Sum.inl ()) =
      Sum.inr (Sum.inl ()) := by
  rw [vinePerm_swap]
  have hzero : finVineEquiv (n + 2) 0 = Sum.inl () := rfl
  have hone : finVineEquiv (n + 2) 1 = Sum.inr (Sum.inl ()) := rfl
  rw [← hzero, Equiv.swap_apply_left, hone]

@[simp] theorem vinePerm_head_middle (n : ℕ) :
    vinePerm (n + 2) (Equiv.swap 0 1) (Sum.inr (Sum.inl ())) =
      Sum.inl () := by
  rw [vinePerm_swap]
  change Equiv.swap (Sum.inl ()) (Sum.inr (Sum.inl ()))
      (Sum.inr (Sum.inl ())) = Sum.inl ()
  exact Equiv.swap_apply_right _ _

@[simp] theorem vinePerm_head_right (n : ℕ) (x : (rightVine n).Leaf) :
    vinePerm (n + 2) (Equiv.swap 0 1) (Sum.inr (Sum.inr x)) =
      Sum.inr (Sum.inr x) := by
  rw [vinePerm_swap]
  obtain ⟨k, rfl⟩ := (finVineEquiv n).surjective x
  change Equiv.swap (Sum.inl ()) (Sum.inr (Sum.inl ()))
      (Sum.inr (Sum.inr (finVineEquiv n k))) =
    Sum.inr (Sum.inr (finVineEquiv n k))
  exact Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)

set_option maxRecDepth 10000 in
theorem table_vine_head (n : ℕ) :
    table (rightVine (n + 2)) (rightVine (n + 2))
        (vinePerm (n + 2) (Equiv.swap 0 1)) =
      table rotationTarget rotationTarget headEquiv := by
  apply Equiv.ext
  intro z
  cases h₀ : Cantor.head z
  · cases h₁ : Cantor.head (Cantor.tail z)
    · simp [table_apply, rightVine, headEquiv, rotationTarget, rotationSource,
        rotationEquiv, siblingSwap, Tree.encode, Tree.decode, h₀]
      change Tree.decode (rightVine (n + 2))
          (vinePerm (n + 2) (Equiv.swap 0 1) (Sum.inl ()), z.tail) = _
      rw [vinePerm_head_left]
      rfl
    · simp [table_apply, rightVine, headEquiv, rotationTarget, rotationSource,
        rotationEquiv, siblingSwap, Tree.encode, Tree.decode, h₀]
      change Tree.decode (rightVine (n + 2))
          (vinePerm (n + 2) (Equiv.swap 0 1) (Sum.inl ()), z.tail) = _
      rw [vinePerm_head_left]
      rfl
  · cases h₁ : Cantor.head (Cantor.tail z)
    · simp [table_apply, rightVine, headEquiv, rotationTarget, rotationSource,
        rotationEquiv, siblingSwap, Tree.encode, Tree.decode, h₀, h₁]
      change Tree.decode (rightVine (n + 2))
          (vinePerm (n + 2) (Equiv.swap 0 1) (Sum.inr (Sum.inl ())),
            z.tail.tail) = _
      rw [vinePerm_head_middle]
      rfl
    · simp [table_apply, rightVine, headEquiv, rotationTarget, rotationSource,
        rotationEquiv, siblingSwap, Tree.encode, Tree.decode, h₀, h₁]
      change Tree.decode (rightVine (n + 2))
          (vinePerm (n + 2) (Equiv.swap 0 1)
            (Sum.inr (Sum.inr ((rightVine n).encode z.tail.tail).1)),
              ((rightVine n).encode z.tail.tail).2) = _
      rw [vinePerm_head_right]
      change Cantor.cons true (Cantor.cons true
          (Tree.decode (rightVine n) (Tree.encode (rightVine n) z.tail.tail))) =
        Cantor.cons true (Cantor.cons true z.tail.tail)
      rw [Tree.decode_encode]

def finPermP (n : ℕ) : Equiv.Perm (Fin (n + 1)) →* P :=
  Submission.PermLift.Tower.permHom rightP swapP headSwapP
    swapP_square headSwapP_square headSwapP_commute_right_right
    headSwapP_braid_right_swapP headSwapP_braid_right_headSwapP n

@[simp] theorem finPermP_swap (n : ℕ) (i j : Fin (n + 1)) :
    finPermP n (Equiv.swap i j) =
      Submission.PermLift.Tower.trans rightP swapP headSwapP n i j := by
  exact Submission.PermLift.Tower.permHom_swap rightP swapP headSwapP
    swapP_square headSwapP_square headSwapP_commute_right_right
    headSwapP_braid_right_swapP headSwapP_braid_right_headSwapP n i j

theorem toV_swapP_vine :
    toV swapP =
      leafPermHom (rightVine 1) (vinePerm 1 (Equiv.swap 0 1)) := by
  rw [swapP, toV_quotientMap, evaluation_s]
  apply Subtype.ext
  change table topTree topTree (Equiv.sumComm Unit Unit) =
    table (rightVine 1) (rightVine 1) (vinePerm 1 (Equiv.swap 0 1))
  have he : vinePerm 1 (Equiv.swap 0 1) = Equiv.sumComm Unit Unit := by
    rw [vinePerm_swap]
    apply Equiv.ext
    rintro (x | x) <;> cases x <;> rfl
  rw [he]
  rfl

theorem toV_headSwapP_vine (n : ℕ) :
    toV headSwapP =
      leafPermHom (rightVine (n + 2)) (vinePerm (n + 2) (Equiv.swap 0 1)) := by
  rw [headSwapP, toV_quotientMap, evaluation_headWord]
  exact Subtype.ext (table_vine_head n).symm

theorem toV_tower_cross : ∀ (n : ℕ) (j : Fin (n + 1)),
    toV (Submission.PermLift.Tower.cross rightP swapP headSwapP n j) =
      leafPermHom (rightVine (n + 1))
        (vinePerm (n + 1) (Equiv.swap 0 j.succ)) := by
  intro n
  induction n with
  | zero =>
      intro j
      fin_cases j
      simpa using toV_swapP_vine
  | succ n ih =>
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa using toV_headSwapP_vine n
      · rw [Submission.PermLift.Tower.cross_succ_succ, map_mul, map_mul,
          map_inv, toV_rightP, ih, toV_headSwapP_vine]
        apply Subtype.ext
        change Cantor.branchPerm true
              (table (rightVine (n + 1)) (rightVine (n + 1))
                (vinePerm (n + 1) (Equiv.swap 0 k.succ))) *
            table (rightVine (n + 2)) (rightVine (n + 2))
              (vinePerm (n + 2) (Equiv.swap 0 1)) *
            (Cantor.branchPerm true
              (table (rightVine (n + 1)) (rightVine (n + 1))
                (vinePerm (n + 1) (Equiv.swap 0 k.succ))))⁻¹ =
          table (rightVine (n + 2)) (rightVine (n + 2))
            (vinePerm (n + 2) (Equiv.swap 0 k.succ.succ))
        rw [branchPerm_true_table, sum_vinePerm_swap]
        change table (rightVine (n + 2)) (rightVine (n + 2))
              (vinePerm (n + 2) (Equiv.swap 1 k.succ.succ)) *
            table (rightVine (n + 2)) (rightVine (n + 2))
              (vinePerm (n + 2) (Equiv.swap 0 1)) *
            (table (rightVine (n + 2)) (rightVine (n + 2))
              (vinePerm (n + 2) (Equiv.swap 1 k.succ.succ)))⁻¹ =
          table (rightVine (n + 2)) (rightVine (n + 2))
            (vinePerm (n + 2) (Equiv.swap 0 k.succ.succ))
        have hinv :
            (table (rightVine (n + 2)) (rightVine (n + 2))
              (vinePerm (n + 2) (Equiv.swap 1 k.succ.succ)))⁻¹ =
            table (rightVine (n + 2)) (rightVine (n + 2))
              (vinePerm (n + 2) (Equiv.swap 1 k.succ.succ)).symm :=
          table_symm _ _ _
        rw [hinv,
          table_mul_table_same_middle, table_mul_table_same_middle]
        congr 1
        rw [vinePerm_swap, vinePerm_swap, vinePerm_swap,
          ← Equiv.trans_assoc,
          Equiv.symm_trans_swap_trans]
        congr 1

theorem toV_tower_trans : ∀ (n : ℕ) (i j : Fin (n + 1)),
    toV (Submission.PermLift.Tower.trans rightP swapP headSwapP n i j) =
      leafPermHom (rightVine n) (vinePerm n (Equiv.swap i j)) := by
  intro n
  induction n with
  | zero =>
      intro i j
      fin_cases i
      fin_cases j
      change 1 = leafPermHom (rightVine 0)
        (vinePerm 0 (Equiv.swap (0 : Fin 1) 0))
      rw [show Equiv.swap (0 : Fin 1) 0 = 1 by
        apply Equiv.ext
        intro x
        fin_cases x
        rfl, vinePerm_one, map_one]
  | succ n ih =>
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · change 1 = leafPermHom (rightVine (n + 1))
            (vinePerm (n + 1) (Equiv.swap 0 0))
          rw [show Equiv.swap (0 : Fin (n + 2)) 0 = 1 by
            apply Equiv.ext
            intro x
            simp,
            vinePerm_one, map_one]
        · simpa using toV_tower_cross n j
      · refine Fin.cases ?_ (fun j => ?_) j
        · simpa [Equiv.swap_comm] using toV_tower_cross n i
        · rw [Submission.PermLift.Tower.trans_succ_succ_succ, toV_rightP,
            ih]
          apply Subtype.ext
          change Cantor.branchPerm true
              (table (rightVine n) (rightVine n)
                (vinePerm n (Equiv.swap i j))) =
            table (rightVine (n + 1)) (rightVine (n + 1))
              (vinePerm (n + 1) (Equiv.swap i.succ j.succ))
          rw [branchPerm_true_table, sum_vinePerm_swap]
          change table (rightVine (n + 1)) (rightVine (n + 1))
              (vinePerm (n + 1) (Equiv.swap i.succ j.succ)) =
            table (rightVine (n + 1)) (rightVine (n + 1))
              (vinePerm (n + 1) (Equiv.swap i.succ j.succ))
          rfl

theorem toV_finPermP (n : ℕ) (e : Equiv.Perm (Fin (n + 1))) :
    toV (finPermP n e) = leafPermHom (rightVine n) (vinePerm n e) := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp [finPermP, vinePerm_one]
  | swap_mul e i j _ ih =>
      rw [map_mul, map_mul, finPermP_swap, toV_tower_trans, ih, vinePerm_mul,
        map_mul]

def vinePermP (n : ℕ) : Equiv.Perm (rightVine n).Leaf →* P :=
  (finPermP n).comp (finVineEquiv n).symm.permCongrHom.toMonoidHom

theorem vinePermP_eq_of_heq {m n : ℕ}
    {e : Equiv.Perm (rightVine m).Leaf}
    {f : Equiv.Perm (rightVine n).Leaf} (h : m = n) (hef : HEq e f) :
    vinePermP m e = vinePermP n f := by
  subst n
  cases hef
  rfl

theorem vinePermP_cast {m n : ℕ} (h : m = n)
    (e : Equiv.Perm (rightVine n).Leaf) :
    vinePermP m
        ((leafEquivOfEq (congrArg rightVine h.symm)).permCongr e) =
      vinePermP n e := by
  cases h
  rfl

theorem toV_vinePermP (n : ℕ) (e : Equiv.Perm (rightVine n).Leaf) :
    toV (vinePermP n e) = leafPermHom (rightVine n) e := by
  rw [vinePermP, MonoidHom.comp_apply, toV_finPermP]
  congr 1
  exact (finVineEquiv n).permCongr.apply_symm_apply e

theorem vineIndex_eq_of_equiv {source target : Tree}
    (e : source.Leaf ≃ target.Leaf) : vineIndex source = vineIndex target := by
  have hcard := Fintype.card_congr e
  simp only [card_leaf_eq_vineIndex_add_one] at hcard
  omega

def flattenTargetEquiv {source target : Tree}
    (h : vineIndex source = vineIndex target) :
    target.Leaf ≃ (rightVine (vineIndex source)).Leaf :=
  (flattenEquiv target).trans
    (leafEquivOfEq (congrArg rightVine h.symm))

@[simp] theorem flattenTargetEquiv_rfl (tree : Tree) :
    flattenTargetEquiv (source := tree) (target := tree) rfl =
      flattenEquiv tree := by
  rfl

/-- The element represented by a tree-pair diagram, when the equality of its
two leaf counts is supplied explicitly. -/
def tableCodeEq {source target : Tree}
    (h : vineIndex source = vineIndex target)
    (e : source.Leaf ≃ target.Leaf) : P :=
  (flattenP target)⁻¹ *
    vinePermP (vineIndex source)
      ((flattenEquiv source).symm.trans (e.trans (flattenTargetEquiv h))) *
    flattenP source

def tableCode {source target : Tree} (e : source.Leaf ≃ target.Leaf) : P :=
  tableCodeEq (vineIndex_eq_of_equiv e) e

theorem toV_tableCodeEq {source target : Tree}
    (h : vineIndex source = vineIndex target) (e : source.Leaf ≃ target.Leaf) :
    toV (tableCodeEq h e) =
      (⟨table source target e, table_mem_V _ _ _⟩ : V) := by
  rw [tableCodeEq, map_mul, map_mul, map_inv, toV_flattenP,
    toV_vinePermP, toV_flattenP]
  apply Subtype.ext
  simp only [leafPermHom, Subgroup.coe_mul, Subgroup.coe_inv]
  have hinv :
      (table target (rightVine (vineIndex target)) (flattenEquiv target))⁻¹ =
        table (rightVine (vineIndex target)) target (flattenEquiv target).symm :=
    table_symm target (rightVine (vineIndex target)) (flattenEquiv target)
  have hsource : rightVine (vineIndex target) =
      rightVine (vineIndex source) := congrArg rightVine h.symm
  have hchange :
      table (rightVine (vineIndex source)) target (flattenTargetEquiv h).symm =
        table (rightVine (vineIndex target)) target (flattenEquiv target).symm := by
    simpa [flattenTargetEquiv] using
      table_change_source (flattenEquiv target).symm hsource
  rw [hinv, ← hchange]
  change table (rightVine (vineIndex source)) target
        (flattenTargetEquiv h).symm *
      table (rightVine (vineIndex source)) (rightVine (vineIndex source))
        ((flattenEquiv source).symm.trans (e.trans (flattenTargetEquiv h))) *
      table source (rightVine (vineIndex source)) (flattenEquiv source) =
    table source target e
  rw [table_mul_table_same_middle, table_mul_table_same_middle]
  apply congrArg (table source target)
  apply Equiv.ext
  intro i
  simp [Equiv.trans_apply, flattenTargetEquiv]

theorem toV_tableCode {source target : Tree} (e : source.Leaf ≃ target.Leaf) :
    toV (tableCode e) =
      (⟨table source target e, table_mem_V _ _ _⟩ : V) :=
  toV_tableCodeEq (vineIndex_eq_of_equiv e) e

@[simp] theorem tableCodeEq_refl (tree : Tree) :
    tableCodeEq rfl (Equiv.refl tree.Leaf) = 1 := by
  have hp :
      (flattenEquiv tree).symm.trans
          ((Equiv.refl tree.Leaf).trans (flattenTargetEquiv rfl)) = 1 := by
    rw [flattenTargetEquiv_rfl]
    apply Equiv.ext
    intro i
    simp
  rw [tableCodeEq, hp, map_one]
  simp

theorem tableCodeEq_trans {source middle target : Tree}
    (e : source.Leaf ≃ middle.Leaf) (f : middle.Leaf ≃ target.Leaf)
    (h₁ : vineIndex source = vineIndex middle)
    (h₂ : vineIndex middle = vineIndex target) :
    tableCodeEq h₂ f * tableCodeEq h₁ e =
      tableCodeEq (h₁.trans h₂) (e.trans f) := by
  let pMiddle : Equiv.Perm (rightVine (vineIndex middle)).Leaf :=
    (flattenEquiv middle).symm.trans (f.trans (flattenTargetEquiv h₂))
  let pF : Equiv.Perm (rightVine (vineIndex source)).Leaf :=
    (leafEquivOfEq (congrArg rightVine h₁.symm)).permCongr pMiddle
  have hperm :
      vinePermP (vineIndex middle) pMiddle =
        vinePermP (vineIndex source) pF := by
    exact (vinePermP_cast h₁ pMiddle).symm
  simp only [tableCodeEq]
  rw [hperm]
  let pE : Equiv.Perm (rightVine (vineIndex source)).Leaf :=
    (flattenEquiv source).symm.trans (e.trans (flattenTargetEquiv h₁))
  change (flattenP target)⁻¹ * vinePermP (vineIndex source) pF *
        flattenP middle * ((flattenP middle)⁻¹ *
          vinePermP (vineIndex source) pE * flattenP source) =
      (flattenP target)⁻¹ *
        vinePermP (vineIndex source)
          ((flattenEquiv source).symm.trans
            ((e.trans f).trans (flattenTargetEquiv (h₁.trans h₂)))) *
        flattenP source
  calc
    _ = (flattenP target)⁻¹ *
        (vinePermP (vineIndex source) pF * vinePermP (vineIndex source) pE) *
        flattenP source := by group
    _ = (flattenP target)⁻¹ * vinePermP (vineIndex source) (pF * pE) *
        flattenP source := by rw [map_mul]
    _ = _ := by
      have hpProduct : pF * pE =
          (flattenEquiv source).symm.trans
            ((e.trans f).trans (flattenTargetEquiv (h₁.trans h₂))) := by
        apply Equiv.ext
        intro i
        simp [pF, pMiddle, pE, flattenTargetEquiv, Equiv.Perm.mul_apply,
          Equiv.trans_apply, Equiv.permCongr_apply]
        change cast _ (cast _ _) = cast _ _
        rw [cast_cast]
      rw [hpProduct]

def mergeLeftIndex (m n : ℕ) (i : Fin (m + 1)) : Fin (m + n + 2) :=
  (finVineEquiv (m + n + 1)).symm
    (mergeEquiv m n (Sum.inl (finVineEquiv m i)))

def mergeRightIndex (m n : ℕ) (j : Fin (n + 1)) : Fin (m + n + 2) :=
  (finVineEquiv (m + n + 1)).symm
    (mergeEquiv m n (Sum.inr (finVineEquiv n j)))

def finMergeEquiv (m n : ℕ) :
    Fin (m + 1) ⊕ Fin (n + 1) ≃ Fin (m + n + 2) :=
  ((finVineEquiv m).sumCongr (finVineEquiv n)).trans
    ((mergeEquiv m n).trans (finVineEquiv (m + n + 1)).symm)

def mergePermHom (m n : ℕ) :
    Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin (n + 1)) →*
      Equiv.Perm (Fin (m + n + 2)) :=
  (finMergeEquiv m n).permCongrHom.toMonoidHom.comp
    (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1)))

def mergeVinePerm (m n : ℕ)
    (e : Equiv.Perm (rightVine m).Leaf)
    (f : Equiv.Perm (rightVine n).Leaf) :
    Equiv.Perm (rightVine (m + n + 1)).Leaf :=
  (mergeEquiv m n).permCongr (e.sumCongr f)

theorem mergePermHom_converted (m n : ℕ)
    (e : Equiv.Perm (rightVine m).Leaf)
    (f : Equiv.Perm (rightVine n).Leaf) :
    mergePermHom m n
        ((finVineEquiv m).symm.permCongr e,
          (finVineEquiv n).symm.permCongr f) =
      (finVineEquiv (m + n + 1)).symm.permCongr (mergeVinePerm m n e f) := by
  apply Equiv.ext
  intro i
  simp [mergePermHom, mergeVinePerm, finMergeEquiv, Equiv.permCongr_apply,
    Equiv.Perm.sumCongrHom_apply]
  generalize (mergeEquiv m n).symm (finVineEquiv (m + n + 1) i) = x
  rcases x with x | x <;> simp [Equiv.permCongr_apply]

@[simp] theorem mergeLeftIndex_zero (n : ℕ) (i : Fin 1) :
    mergeLeftIndex 0 n i = 0 := by
  fin_cases i
  unfold mergeLeftIndex
  change (finVineEquiv (0 + n + 1)).symm
      (mergeEquiv 0 n (Sum.inl ())) = 0
  rw [mergeEquiv_zero]
  apply (finVineEquiv (0 + n + 1)).symm_apply_eq.mpr
  change vineCast (by omega : n + 1 = 0 + n + 1)
      (finVineEquiv (n + 1) 0) =
    finVineEquiv (0 + n + 1) 0
  rw [finVineEquiv_vineCast]
  congr

@[simp] theorem mergeRightIndex_zero (n : ℕ) (j : Fin (n + 1)) :
    mergeRightIndex 0 n j = Fin.cast (by omega) j.succ := by
  unfold mergeRightIndex
  rw [mergeEquiv_zero]
  apply (finVineEquiv (0 + n + 1)).symm_apply_eq.mpr
  change vineCast (by omega : n + 1 = 0 + n + 1)
      (finVineEquiv (n + 1) j.succ) =
    finVineEquiv (0 + n + 1) (Fin.cast _ j.succ)
  rw [finVineEquiv_vineCast]

theorem mergePermHom_left_swap (m n : ℕ) (i j : Fin (m + 1)) :
    mergePermHom m n (Equiv.swap i j, 1) =
      Equiv.swap (mergeLeftIndex m n i) (mergeLeftIndex m n j) := by
  rw [mergePermHom, MonoidHom.comp_apply, Equiv.Perm.sumCongrHom_apply]
  change (finMergeEquiv m n).permCongr
      ((Equiv.swap i j).sumCongr (Equiv.refl _)) = _
  rw [show (Equiv.swap i j).sumCongr (Equiv.refl _) =
      Equiv.swap (Sum.inl i) (Sum.inl j) by
        apply Equiv.ext
        intro x
        rcases x with (x | x) <;> simp [Equiv.swap_apply_def]]
  change (finMergeEquiv m n).permCongr
      (Equiv.swap (Sum.inl i) (Sum.inl j)) =
    Equiv.swap (finMergeEquiv m n (Sum.inl i))
      (finMergeEquiv m n (Sum.inl j))
  exact Equiv.symm_trans_swap_trans _ _ (finMergeEquiv m n)

theorem mergePermHom_right_swap (m n : ℕ) (i j : Fin (n + 1)) :
    mergePermHom m n (1, Equiv.swap i j) =
      Equiv.swap (mergeRightIndex m n i) (mergeRightIndex m n j) := by
  rw [mergePermHom, MonoidHom.comp_apply, Equiv.Perm.sumCongrHom_apply]
  change (finMergeEquiv m n).permCongr
      ((Equiv.refl _).sumCongr (Equiv.swap i j)) = _
  rw [show (Equiv.refl _).sumCongr (Equiv.swap i j) =
      Equiv.swap (Sum.inr i) (Sum.inr j) by
        apply Equiv.ext
        intro x
        rcases x with (x | x) <;> simp [Equiv.swap_apply_def]]
  change (finMergeEquiv m n).permCongr
      (Equiv.swap (Sum.inr i) (Sum.inr j)) =
    Equiv.swap (finMergeEquiv m n (Sum.inr i))
      (finMergeEquiv m n (Sum.inr j))
  exact Equiv.symm_trans_swap_trans _ _ (finMergeEquiv m n)

@[simp] theorem mergeLeftIndex_succ_zero (m n : ℕ) :
    mergeLeftIndex (m + 1) n 0 = 0 := by
  unfold mergeLeftIndex
  rw [mergeEquiv, assocEquiv_eq_sumAssoc]
  change (finVineEquiv (m + 1 + n + 1)).symm
      (leafEquivOfEq (mergeTarget_succ m n)
        (finVineEquiv (m + n + 2) 0)) = 0
  apply Fin.ext
  exact congrArg Fin.val (mergeTarget_index m n 0)

@[simp] theorem mergeLeftIndex_succ_succ (m n : ℕ) (i : Fin (m + 1)) :
    mergeLeftIndex (m + 1) n i.succ =
      Fin.cast (by omega) (mergeLeftIndex m n i).succ := by
  have hLeaf :
      mergeEquiv m n (Sum.inl (finVineEquiv m i)) =
        finVineEquiv (m + n + 1) (mergeLeftIndex m n i) :=
    ((finVineEquiv (m + n + 1)).apply_symm_apply _).symm
  unfold mergeLeftIndex
  rw [mergeEquiv, assocEquiv_eq_sumAssoc]
  change (finVineEquiv (m + 1 + n + 1)).symm
      (leafEquivOfEq (mergeTarget_succ m n)
        (Sum.inr (mergeEquiv m n (Sum.inl (finVineEquiv m i))))) = _
  rw [hLeaf]
  rw [show Sum.inr (finVineEquiv (m + n + 1) (mergeLeftIndex m n i)) =
      finVineEquiv (m + n + 2) (mergeLeftIndex m n i).succ by rfl]
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  have h := congrArg Fin.val
    (mergeTarget_index m n (mergeLeftIndex m n i).succ)
  simpa using h

@[simp] theorem mergeRightIndex_succ (m n : ℕ) (j : Fin (n + 1)) :
    mergeRightIndex (m + 1) n j =
      Fin.cast (by omega) (mergeRightIndex m n j).succ := by
  have hLeaf :
      mergeEquiv m n (Sum.inr (finVineEquiv n j)) =
        finVineEquiv (m + n + 1) (mergeRightIndex m n j) :=
    ((finVineEquiv (m + n + 1)).apply_symm_apply _).symm
  unfold mergeRightIndex
  rw [mergeEquiv, assocEquiv_eq_sumAssoc]
  change (finVineEquiv (m + 1 + n + 1)).symm
      (leafEquivOfEq (mergeTarget_succ m n)
        (Sum.inr (mergeEquiv m n (Sum.inr (finVineEquiv n j))))) = _
  rw [hLeaf]
  rw [show Sum.inr (finVineEquiv (m + n + 1) (mergeRightIndex m n j)) =
      finVineEquiv (m + n + 2) (mergeRightIndex m n j).succ by rfl]
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  have h := congrArg Fin.val
    (mergeTarget_index m n (mergeRightIndex m n j).succ)
  simpa using h

theorem towerTrans_succ_succ_of_eq {n k : ℕ} (h : k = n + 1)
    (i j : Fin (n + 1)) :
    Submission.PermLift.Tower.trans rightP swapP headSwapP k
        (Fin.cast (congrArg (fun q => q + 1) h.symm) i.succ)
        (Fin.cast (congrArg (fun q => q + 1) h.symm) j.succ) =
      rightP (Submission.PermLift.Tower.trans rightP swapP headSwapP n i j) := by
  subst k
  rfl

theorem towerTrans_zero_succ_of_eq {n k : ℕ} (h : k = n + 1)
    (j : Fin (n + 1)) :
    Submission.PermLift.Tower.trans rightP swapP headSwapP k 0
        (Fin.cast (congrArg (fun q => q + 1) h.symm) j.succ) =
      Submission.PermLift.Tower.cross rightP swapP headSwapP n j := by
  subst k
  rfl

theorem towerTrans_succ_zero_of_eq {n k : ℕ} (h : k = n + 1)
    (i : Fin (n + 1)) :
    Submission.PermLift.Tower.trans rightP swapP headSwapP k
        (Fin.cast (congrArg (fun q => q + 1) h.symm) i.succ) 0 =
      Submission.PermLift.Tower.cross rightP swapP headSwapP n i := by
  subst k
  rfl

theorem towerCross_zero_of_eq {n k : ℕ} (h : k = n + 1) :
    Submission.PermLift.Tower.cross rightP swapP headSwapP k 0 = headSwapP := by
  subst k
  rfl

theorem towerCross_succ_of_eq {n k : ℕ} (h : k = n + 1)
    (j : Fin (n + 1)) :
    Submission.PermLift.Tower.cross rightP swapP headSwapP k
        (Fin.cast (congrArg (fun q => q + 1) h.symm) j.succ) =
      rightP (Submission.PermLift.Tower.cross rightP swapP headSwapP n j) *
        headSwapP *
          (rightP (Submission.PermLift.Tower.cross rightP swapP headSwapP n j))⁻¹ := by
  subst k
  rfl

theorem mergeP_right_trans : ∀ (m n : ℕ) (i j : Fin (n + 1)),
    mergeP m n *
        rightP (Submission.PermLift.Tower.trans rightP swapP headSwapP n i j) *
        (mergeP m n)⁻¹ =
      Submission.PermLift.Tower.trans rightP swapP headSwapP (m + n + 1)
        (mergeRightIndex m n i) (mergeRightIndex m n j) := by
  intro m
  induction m with
  | zero =>
      intro n i j
      simp only [mergeP, one_mul, inv_one, mul_one]
      let hk : 0 + n + 1 = n + 1 := by omega
      have hi : mergeRightIndex 0 n i =
          Fin.cast (congrArg (fun q => q + 1) hk.symm) i.succ := by
        apply Fin.ext
        simp
      have hj : mergeRightIndex 0 n j =
          Fin.cast (congrArg (fun q => q + 1) hk.symm) j.succ := by
        apply Fin.ext
        simp
      symm
      rw [hi, hj]
      exact towerTrans_succ_succ_of_eq hk i j
  | succ m ih =>
      intro n i j
      let z := Submission.PermLift.Tower.trans rightP swapP headSwapP n i j
      calc
        mergeP (m + 1) n * rightP z * (mergeP (m + 1) n)⁻¹ =
            rightP (mergeP m n) *
              (assocP * rightP z * assocP⁻¹) *
              (rightP (mergeP m n))⁻¹ := by
                simp only [mergeP]
                group
        _ = rightP (mergeP m n) * rightP (rightP z) *
              (rightP (mergeP m n))⁻¹ := by rw [assocP_rightP]
        _ = rightP
              (mergeP m n * rightP z * (mergeP m n)⁻¹) := by
                simp
        _ = rightP
              (Submission.PermLift.Tower.trans rightP swapP headSwapP
                (m + n + 1) (mergeRightIndex m n i) (mergeRightIndex m n j)) := by
                  rw [ih]
        _ = Submission.PermLift.Tower.trans rightP swapP headSwapP
              (m + 1 + n + 1) (mergeRightIndex (m + 1) n i)
                (mergeRightIndex (m + 1) n j) := by
                  let hk : m + 1 + n + 1 = (m + n + 1) + 1 := by omega
                  have hi : mergeRightIndex (m + 1) n i =
                      Fin.cast (congrArg (fun q => q + 1) hk.symm)
                        (mergeRightIndex m n i).succ := by
                    apply Fin.ext
                    simp
                  have hj : mergeRightIndex (m + 1) n j =
                      Fin.cast (congrArg (fun q => q + 1) hk.symm)
                        (mergeRightIndex m n j).succ := by
                    apply Fin.ext
                    simp
                  symm
                  rw [hi, hj]
                  exact towerTrans_succ_succ_of_eq hk
                    (mergeRightIndex m n i) (mergeRightIndex m n j)

theorem mergeP_left_cross : ∀ (m n : ℕ) (k : Fin (m + 1)),
    mergeP (m + 1) n *
        leftP (Submission.PermLift.Tower.cross rightP swapP headSwapP m k) *
        (mergeP (m + 1) n)⁻¹ =
      Submission.PermLift.Tower.cross rightP swapP headSwapP (m + n + 1)
        (mergeLeftIndex m n k) := by
  intro m
  induction m with
  | zero =>
      intro n k
      fin_cases k
      simp [mergeP, headSwapP_eq]
  | succ m ih =>
      intro n k
      refine Fin.cases ?_ (fun l => ?_) k
      · let d := mergeP m n
        let q := mergeP (m + 1) n
        calc
          mergeP (m + 2) n * leftP headSwapP * (mergeP (m + 2) n)⁻¹ =
              rightP q * (assocP * leftP headSwapP * assocP⁻¹) *
                (rightP q)⁻¹ := by
                  simp only [mergeP, q]
                  group
          _ = rightP q * ((rightP assocP)⁻¹ * headSwapP *
                rightP assocP) * (rightP q)⁻¹ := by
                  rw [assocP_leftP_headSwapP]
          _ = rightP (rightP d) * headSwapP * (rightP (rightP d))⁻¹ := by
                  simp [q, d, mergeP]
                  group
          _ = headSwapP := by
                  rw [(headSwapP_commute_right_right d).symm.eq]
                  simp
          _ = Submission.PermLift.Tower.cross rightP swapP headSwapP
                (m + 1 + n + 1) (mergeLeftIndex (m + 1) n 0) := by
                  let hk : m + 1 + n + 1 = (m + n + 1) + 1 := by omega
                  rw [mergeLeftIndex_succ_zero]
                  exact (towerCross_zero_of_eq hk).symm
      · let c := Submission.PermLift.Tower.cross rightP swapP headSwapP m l
        let d := mergeP m n
        let q := mergeP (m + 1) n
        let c' := Submission.PermLift.Tower.cross rightP swapP headSwapP
          (m + n + 1) (mergeLeftIndex m n l)
        have hi : q * leftP c * q⁻¹ = c' := by
          exact ih n l
        have hinner : q * leftP c * assocP⁻¹ = c' * rightP d := by
          calc
            q * leftP c * assocP⁻¹ =
                (q * leftP c * q⁻¹) * rightP d := by
                  simp [q, d, mergeP]
                  group
            _ = c' * rightP d := by rw [hi]
        have hu : rightP q * rightP (leftP c) * (rightP assocP)⁻¹ =
            rightP c' * rightP (rightP d) := by
          simpa only [map_mul, map_inv] using congrArg rightP hinner
        have hmergeQ : mergeP (m + 2) n = rightP q * assocP := by
          rfl
        calc
          mergeP (m + 2) n *
                leftP (rightP c * headSwapP * (rightP c)⁻¹) *
                (mergeP (m + 2) n)⁻¹ =
              (rightP q * rightP (leftP c) * (rightP assocP)⁻¹) *
                headSwapP *
                (rightP q * rightP (leftP c) * (rightP assocP)⁻¹)⁻¹ := by
                  rw [hmergeQ]
                  simp only [map_mul, map_inv]
                  calc
                    (rightP q * assocP) *
                          (leftP (rightP c) * leftP headSwapP *
                            (leftP (rightP c))⁻¹) *
                          (rightP q * assocP)⁻¹ =
                        rightP q *
                          (assocP * leftP (rightP c) * assocP⁻¹) *
                          (assocP * leftP headSwapP * assocP⁻¹) *
                          (assocP * leftP (rightP c) * assocP⁻¹)⁻¹ *
                          (rightP q)⁻¹ := by group
                    _ = _ := by
                      rw [assocP_leftP_rightP, assocP_leftP_headSwapP]
                      group
          _ = (rightP c' * rightP (rightP d)) * headSwapP *
                (rightP c' * rightP (rightP d))⁻¹ := by rw [hu]
          _ = rightP c' * headSwapP * (rightP c')⁻¹ := by
                  calc
                    (rightP c' * rightP (rightP d)) * headSwapP *
                          (rightP c' * rightP (rightP d))⁻¹ =
                        rightP c' *
                          (rightP (rightP d) * headSwapP *
                            (rightP (rightP d))⁻¹) *
                          (rightP c')⁻¹ := by group
                    _ = rightP c' * headSwapP * (rightP c')⁻¹ := by
                      rw [(headSwapP_commute_right_right d).symm.eq]
                      group
          _ = Submission.PermLift.Tower.cross rightP swapP headSwapP
                (m + 1 + n + 1) (mergeLeftIndex (m + 1) n l.succ) := by
                  let hk : m + 1 + n + 1 = (m + n + 1) + 1 := by omega
                  have hidx : mergeLeftIndex (m + 1) n l.succ =
                      Fin.cast (congrArg (fun q => q + 1) hk.symm)
                        (mergeLeftIndex m n l).succ := by
                    apply Fin.ext
                    simp
                  rw [hidx]
                  exact (towerCross_succ_of_eq hk (mergeLeftIndex m n l)).symm

theorem mergeP_left_trans : ∀ (m n : ℕ) (i j : Fin (m + 1)),
    mergeP m n *
        leftP (Submission.PermLift.Tower.trans rightP swapP headSwapP m i j) *
        (mergeP m n)⁻¹ =
      Submission.PermLift.Tower.trans rightP swapP headSwapP (m + n + 1)
        (mergeLeftIndex m n i) (mergeLeftIndex m n j) := by
  intro m
  induction m with
  | zero =>
      intro n i j
      fin_cases i
      fin_cases j
      simp [mergeP]
  | succ m ih =>
      intro n i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp
        · have htarget :
              Submission.PermLift.Tower.trans rightP swapP headSwapP
                  (m + 1 + n + 1) (mergeLeftIndex (m + 1) n 0)
                    (mergeLeftIndex (m + 1) n j.succ) =
                Submission.PermLift.Tower.cross rightP swapP headSwapP
                  (m + n + 1) (mergeLeftIndex m n j) := by
                let hk : m + 1 + n + 1 = (m + n + 1) + 1 := by omega
                have hidx : mergeLeftIndex (m + 1) n j.succ =
                    Fin.cast (congrArg (fun q => q + 1) hk.symm)
                      (mergeLeftIndex m n j).succ := by
                  apply Fin.ext
                  simp
                rw [mergeLeftIndex_succ_zero, hidx]
                exact towerTrans_zero_succ_of_eq hk (mergeLeftIndex m n j)
          exact (mergeP_left_cross m n j).trans htarget.symm
      · refine Fin.cases ?_ (fun j => ?_) j
        · have htarget :
              Submission.PermLift.Tower.trans rightP swapP headSwapP
                  (m + 1 + n + 1) (mergeLeftIndex (m + 1) n i.succ)
                    (mergeLeftIndex (m + 1) n 0) =
                Submission.PermLift.Tower.cross rightP swapP headSwapP
                  (m + n + 1) (mergeLeftIndex m n i) := by
                let hk : m + 1 + n + 1 = (m + n + 1) + 1 := by omega
                have hidx : mergeLeftIndex (m + 1) n i.succ =
                    Fin.cast (congrArg (fun q => q + 1) hk.symm)
                      (mergeLeftIndex m n i).succ := by
                  apply Fin.ext
                  simp
                rw [mergeLeftIndex_succ_zero, hidx]
                exact towerTrans_succ_zero_of_eq hk (mergeLeftIndex m n i)
          exact (mergeP_left_cross m n i).trans htarget.symm
        · let z := Submission.PermLift.Tower.trans rightP swapP headSwapP m i j
          let q := mergeP m n
          calc
            mergeP (m + 1) n * leftP (rightP z) * (mergeP (m + 1) n)⁻¹ =
                rightP q *
                  (assocP * leftP (rightP z) * assocP⁻¹) *
                  (rightP q)⁻¹ := by
                    simp only [mergeP, q]
                    group
            _ = rightP q * rightP (leftP z) * (rightP q)⁻¹ := by
                    rw [assocP_leftP_rightP]
            _ = rightP (q * leftP z * q⁻¹) := by simp
            _ = rightP
                  (Submission.PermLift.Tower.trans rightP swapP headSwapP
                    (m + n + 1) (mergeLeftIndex m n i)
                      (mergeLeftIndex m n j)) := by rw [ih]
            _ = Submission.PermLift.Tower.trans rightP swapP headSwapP
                  (m + 1 + n + 1) (mergeLeftIndex (m + 1) n i.succ)
                    (mergeLeftIndex (m + 1) n j.succ) := by
                      let hk : m + 1 + n + 1 = (m + n + 1) + 1 := by omega
                      have hi : mergeLeftIndex (m + 1) n i.succ =
                          Fin.cast (congrArg (fun q => q + 1) hk.symm)
                            (mergeLeftIndex m n i).succ := by
                        apply Fin.ext
                        simp
                      have hj : mergeLeftIndex (m + 1) n j.succ =
                          Fin.cast (congrArg (fun q => q + 1) hk.symm)
                            (mergeLeftIndex m n j).succ := by
                        apply Fin.ext
                        simp
                      symm
                      rw [hi, hj]
                      exact towerTrans_succ_succ_of_eq hk
                        (mergeLeftIndex m n i) (mergeLeftIndex m n j)

theorem mergeP_left_finPerm (m n : ℕ)
    (e : Equiv.Perm (Fin (m + 1))) :
    mergeP m n * leftP (finPermP m e) * (mergeP m n)⁻¹ =
      finPermP (m + n + 1) (mergePermHom m n (e, 1)) := by
  induction e using Equiv.Perm.swap_induction_on with
  | one =>
      have hm : mergePermHom m n (1, 1) = 1 := (mergePermHom m n).map_one
      simp only [map_one, hm, mul_one, mul_inv_cancel]
  | swap_mul e i j _ ih =>
      calc
        mergeP m n * leftP (finPermP m (Equiv.swap i j * e)) *
              (mergeP m n)⁻¹ =
            (mergeP m n * leftP (finPermP m (Equiv.swap i j)) *
                (mergeP m n)⁻¹) *
              (mergeP m n * leftP (finPermP m e) * (mergeP m n)⁻¹) := by
                rw [map_mul, map_mul]
                group
        _ = Submission.PermLift.Tower.trans rightP swapP headSwapP
              (m + n + 1) (mergeLeftIndex m n i) (mergeLeftIndex m n j) *
            finPermP (m + n + 1) (mergePermHom m n (e, 1)) := by
              rw [finPermP_swap, mergeP_left_trans, ih]
        _ = finPermP (m + n + 1)
              (Equiv.swap (mergeLeftIndex m n i) (mergeLeftIndex m n j) *
                mergePermHom m n (e, 1)) := by
              rw [← finPermP_swap, map_mul]
        _ = finPermP (m + n + 1)
              (mergePermHom m n (Equiv.swap i j * e, 1)) := by
              congr 1
              rw [← mergePermHom_left_swap, ← map_mul]
              rfl

theorem mergeP_right_finPerm (m n : ℕ)
    (e : Equiv.Perm (Fin (n + 1))) :
    mergeP m n * rightP (finPermP n e) * (mergeP m n)⁻¹ =
      finPermP (m + n + 1) (mergePermHom m n (1, e)) := by
  induction e using Equiv.Perm.swap_induction_on with
  | one =>
      have hm : mergePermHom m n (1, 1) = 1 := (mergePermHom m n).map_one
      simp only [map_one, hm, mul_one, mul_inv_cancel]
  | swap_mul e i j _ ih =>
      calc
        mergeP m n * rightP (finPermP n (Equiv.swap i j * e)) *
              (mergeP m n)⁻¹ =
            (mergeP m n * rightP (finPermP n (Equiv.swap i j)) *
                (mergeP m n)⁻¹) *
              (mergeP m n * rightP (finPermP n e) * (mergeP m n)⁻¹) := by
                rw [map_mul, map_mul]
                group
        _ = Submission.PermLift.Tower.trans rightP swapP headSwapP
              (m + n + 1) (mergeRightIndex m n i) (mergeRightIndex m n j) *
            finPermP (m + n + 1) (mergePermHom m n (1, e)) := by
              rw [finPermP_swap, mergeP_right_trans, ih]
        _ = finPermP (m + n + 1)
              (Equiv.swap (mergeRightIndex m n i) (mergeRightIndex m n j) *
                mergePermHom m n (1, e)) := by
              rw [← finPermP_swap, map_mul]
        _ = finPermP (m + n + 1)
              (mergePermHom m n (1, Equiv.swap i j * e)) := by
              congr 1
              rw [← mergePermHom_right_swap, ← map_mul]
              rfl

theorem mergeP_tensor_finPerm (m n : ℕ)
    (e : Equiv.Perm (Fin (m + 1))) (f : Equiv.Perm (Fin (n + 1))) :
    mergeP m n * tensorP (finPermP m e, finPermP n f) * (mergeP m n)⁻¹ =
      finPermP (m + n + 1) (mergePermHom m n (e, f)) := by
  calc
    mergeP m n * tensorP (finPermP m e, finPermP n f) * (mergeP m n)⁻¹ =
        (mergeP m n * leftP (finPermP m e) * (mergeP m n)⁻¹) *
          (mergeP m n * rightP (finPermP n f) * (mergeP m n)⁻¹) := by
            rw [tensorP_apply]
            group
    _ = finPermP (m + n + 1) (mergePermHom m n (e, 1)) *
          finPermP (m + n + 1) (mergePermHom m n (1, f)) := by
            rw [mergeP_left_finPerm, mergeP_right_finPerm]
    _ = finPermP (m + n + 1) (mergePermHom m n (e, f)) := by
            rw [← map_mul, ← map_mul]
            rfl

theorem mergeP_tensor_vinePerm (m n : ℕ)
    (e : Equiv.Perm (rightVine m).Leaf)
    (f : Equiv.Perm (rightVine n).Leaf) :
    mergeP m n * tensorP (vinePermP m e, vinePermP n f) * (mergeP m n)⁻¹ =
      vinePermP (m + n + 1) (mergeVinePerm m n e f) := by
  rw [vinePermP, vinePermP, vinePermP]
  change mergeP m n *
      tensorP
        (finPermP m ((finVineEquiv m).symm.permCongr e),
          finPermP n ((finVineEquiv n).symm.permCongr f)) *
        (mergeP m n)⁻¹ = _
  rw [mergeP_tensor_finPerm, mergePermHom_converted]
  rfl

theorem tableCodeEq_sumCongr {sourceLeft sourceRight targetLeft targetRight : Tree}
    (e : sourceLeft.Leaf ≃ targetLeft.Leaf)
    (f : sourceRight.Leaf ≃ targetRight.Leaf)
    (hLeft : vineIndex sourceLeft = vineIndex targetLeft)
    (hRight : vineIndex sourceRight = vineIndex targetRight) :
    tableCodeEq (source := .fork sourceLeft sourceRight)
        (target := .fork targetLeft targetRight)
        (by simp [vineIndex, hLeft, hRight]) (e.sumCongr f) =
      tensorP (tableCodeEq hLeft e, tableCodeEq hRight f) := by
  let hFork : vineIndex (.fork sourceLeft sourceRight) =
      vineIndex (.fork targetLeft targetRight) := by
    simp [vineIndex, hLeft, hRight]
  change tableCodeEq hFork (e.sumCongr f) =
    tensorP (tableCodeEq hLeft e, tableCodeEq hRight f)
  let pLeft : Equiv.Perm (rightVine (vineIndex sourceLeft)).Leaf :=
    (flattenEquiv sourceLeft).symm.trans (e.trans (flattenTargetEquiv hLeft))
  let pRight : Equiv.Perm (rightVine (vineIndex sourceRight)).Leaf :=
    (flattenEquiv sourceRight).symm.trans (f.trans (flattenTargetEquiv hRight))
  have hp :
      (flattenEquiv (.fork sourceLeft sourceRight)).symm.trans
          ((e.sumCongr f).trans (flattenTargetEquiv hFork)) =
        mergeVinePerm (vineIndex sourceLeft) (vineIndex sourceRight) pLeft pRight := by
    let coreLeft :
        (rightVine (vineIndex sourceLeft)).Leaf ≃
          (rightVine (vineIndex targetLeft)).Leaf :=
      (flattenEquiv sourceLeft).symm.trans (e.trans (flattenEquiv targetLeft))
    let coreRight :
        (rightVine (vineIndex sourceRight)).Leaf ≃
          (rightVine (vineIndex targetRight)).Leaf :=
      (flattenEquiv sourceRight).symm.trans (f.trans (flattenEquiv targetRight))
    apply Equiv.ext
    intro i
    let x := (mergeEquiv (vineIndex sourceLeft) (vineIndex sourceRight)).symm i
    let y := (coreLeft.sumCongr coreRight) x
    have hCore :
        ((flattenEquiv targetLeft).sumCongr (flattenEquiv targetRight))
            ((e.sumCongr f)
              (((flattenEquiv sourceLeft).sumCongr
                (flattenEquiv sourceRight)).symm x)) = y := by
      rcases x with x | x <;> rfl
    have hTotalCast :
        leafEquivOfEq (congrArg rightVine hFork.symm) =
          vineCast (by omega :
            vineIndex targetLeft + vineIndex targetRight + 1 =
              vineIndex sourceLeft + vineIndex sourceRight + 1) := by
      apply Equiv.ext
      intro z
      change cast _ z = cast _ z
      congr
    have hPieces :
        (pLeft.sumCongr pRight) x =
          ((vineCast hLeft.symm).sumCongr (vineCast hRight.symm)) y := by
      rcases x with x | x <;> rfl
    have hNatural := Equiv.congr_fun (mergeEquiv_natural hLeft hRight) y
    simp only [flattenEquiv, flattenTargetEquiv, mergeVinePerm, pLeft, pRight,
      Equiv.trans_apply, Equiv.symm_trans_apply]
    change leafEquivOfEq (congrArg rightVine hFork.symm)
        (mergeEquiv (vineIndex targetLeft) (vineIndex targetRight)
          (((flattenEquiv targetLeft).sumCongr (flattenEquiv targetRight))
            ((e.sumCongr f)
              (((flattenEquiv sourceLeft).sumCongr
                (flattenEquiv sourceRight)).symm x)))) =
      mergeEquiv (vineIndex sourceLeft) (vineIndex sourceRight)
        ((pLeft.sumCongr pRight) x)
    rw [hCore, hTotalCast, hPieces]
    exact hNatural
  have hVine :
      vinePermP (vineIndex (.fork sourceLeft sourceRight))
          ((flattenEquiv (.fork sourceLeft sourceRight)).symm.trans
            ((e.sumCongr f).trans (flattenTargetEquiv hFork))) =
        vinePermP (vineIndex sourceLeft + vineIndex sourceRight + 1)
          (mergeVinePerm (vineIndex sourceLeft) (vineIndex sourceRight)
            pLeft pRight) := by
    change vinePermP (vineIndex sourceLeft + vineIndex sourceRight + 1) _ = _
    rw [hp]
  simp only [tableCodeEq, flattenP]
  rw [hVine]
  rw [show mergeP (vineIndex targetLeft) (vineIndex targetRight) =
      mergeP (vineIndex sourceLeft) (vineIndex sourceRight) by
        rw [hLeft, hRight]]
  rw [← mergeP_tensor_vinePerm]
  have hTensor :
      tensorP
          ((flattenP targetLeft)⁻¹ * vinePermP (vineIndex sourceLeft) pLeft *
              flattenP sourceLeft,
            (flattenP targetRight)⁻¹ * vinePermP (vineIndex sourceRight) pRight *
              flattenP sourceRight) =
        (tensorP (flattenP targetLeft, flattenP targetRight))⁻¹ *
          tensorP
            (vinePermP (vineIndex sourceLeft) pLeft,
              vinePermP (vineIndex sourceRight) pRight) *
          tensorP (flattenP sourceLeft, flattenP sourceRight) := by
    calc
      _ = tensorP
          ((flattenP targetLeft, flattenP targetRight)⁻¹ *
            (vinePermP (vineIndex sourceLeft) pLeft,
              vinePermP (vineIndex sourceRight) pRight) *
            (flattenP sourceLeft, flattenP sourceRight)) := by rfl
      _ = _ := by rw [map_mul, map_mul, map_inv]
  rw [hTensor]
  group

theorem assocP_tensor (x y z : P) :
    assocP * tensorP (tensorP (x, y), z) * assocP⁻¹ =
      tensorP (x, tensorP (y, z)) := by
  simp only [tensorP_apply, map_mul]
  calc
    assocP *
          (leftP (leftP x) * leftP (rightP y) * rightP z) * assocP⁻¹ =
        (assocP * leftP (leftP x) * assocP⁻¹) *
          (assocP * leftP (rightP y) * assocP⁻¹) *
          (assocP * rightP z * assocP⁻¹) := by group
    _ = leftP x * rightP (leftP y) * rightP (rightP z) := by
      rw [assocP_leftP_leftP, assocP_leftP_rightP, assocP_rightP]
    _ = leftP x * (rightP (leftP y) * rightP (rightP z)) :=
      mul_assoc _ _ _

theorem mergeP_assoc : ∀ m n k : ℕ,
    mergeP (m + n + 1) k * leftP (mergeP m n) =
      mergeP m (n + k + 1) * rightP (mergeP n k) * assocP := by
  intro m
  induction m with
  | zero =>
      intro n k
      simp [mergeP]
  | succ m ih =>
      intro n k
      have hmiddle (z : P) :
          assocP * leftP (rightP z) = rightP (leftP z) * assocP := by
        calc
          assocP * leftP (rightP z) =
              (assocP * leftP (rightP z) * assocP⁻¹) * assocP := by group
          _ = rightP (leftP z) * assocP := by rw [assocP_leftP_rightP]
      have hright (z : P) :
          rightP (rightP z) * assocP = assocP * rightP z := by
        calc
          rightP (rightP z) * assocP =
              (assocP * rightP z * assocP⁻¹) * assocP := by
                rw [assocP_rightP]
          _ = assocP * rightP z := by group
      calc
        mergeP (m + 1 + n + 1) k * leftP (mergeP (m + 1) n) =
            rightP (mergeP (m + n + 1) k) * assocP *
              leftP (rightP (mergeP m n)) * leftP assocP := by
                rw [show m + 1 + n + 1 = (m + n + 1) + 1 by omega]
                simp only [mergeP, map_mul]
                group
        _ = rightP (mergeP (m + n + 1) k) *
              rightP (leftP (mergeP m n)) * assocP * leftP assocP := by
                calc
                  rightP (mergeP (m + n + 1) k) * assocP *
                        leftP (rightP (mergeP m n)) * leftP assocP =
                      rightP (mergeP (m + n + 1) k) *
                        (assocP * leftP (rightP (mergeP m n))) *
                          leftP assocP := by group
                  _ = rightP (mergeP (m + n + 1) k) *
                        (rightP (leftP (mergeP m n)) * assocP) *
                          leftP assocP := by rw [hmiddle]
                  _ = _ := by group
        _ = rightP (mergeP (m + n + 1) k * leftP (mergeP m n)) *
              assocP * leftP assocP := by
                rw [map_mul]
        _ = rightP
              (mergeP m (n + k + 1) * rightP (mergeP n k) * assocP) *
              assocP * leftP assocP := by rw [ih]
        _ = rightP (mergeP m (n + k + 1)) *
              rightP (rightP (mergeP n k)) *
              (rightP assocP * assocP * leftP assocP) := by
                simp only [map_mul]
                group
        _ = rightP (mergeP m (n + k + 1)) *
              rightP (rightP (mergeP n k)) * (assocP * assocP) := by
                rw [assocP_pentagon]
        _ = rightP (mergeP m (n + k + 1)) * assocP *
              rightP (mergeP n k) * assocP := by
                calc
                  rightP (mergeP m (n + k + 1)) *
                        rightP (rightP (mergeP n k)) * (assocP * assocP) =
                      rightP (mergeP m (n + k + 1)) *
                        (rightP (rightP (mergeP n k)) * assocP) * assocP := by
                          group
                  _ = rightP (mergeP m (n + k + 1)) *
                        (assocP * rightP (mergeP n k)) * assocP := by rw [hright]
                  _ = _ := by group
        _ = mergeP (m + 1) (n + k + 1) * rightP (mergeP n k) * assocP := by
                rfl

theorem flattenP_assoc (aTree bTree cTree : Tree) :
    flattenP (.fork aTree (.fork bTree cTree)) * assocP =
      flattenP (.fork (.fork aTree bTree) cTree) := by
  let x := flattenP aTree
  let y := flattenP bTree
  let z := flattenP cTree
  let mergeBC := mergeP (vineIndex bTree) (vineIndex cTree)
  have hcommute :
      Commute (leftP x) (rightP mergeBC) :=
    leftP_rightP_commute x mergeBC
  have hassocTensor :
      tensorP (x, tensorP (y, z)) * assocP =
        assocP * tensorP (tensorP (x, y), z) := by
    calc
      tensorP (x, tensorP (y, z)) * assocP =
          (assocP * tensorP (tensorP (x, y), z) * assocP⁻¹) * assocP := by
            rw [assocP_tensor]
      _ = assocP * tensorP (tensorP (x, y), z) := by group
  have hmerge := mergeP_assoc (vineIndex aTree) (vineIndex bTree)
    (vineIndex cTree)
  calc
    flattenP (.fork aTree (.fork bTree cTree)) * assocP =
        mergeP (vineIndex aTree) (vineIndex bTree + vineIndex cTree + 1) *
          leftP x * rightP mergeBC * rightP (leftP y) *
          rightP (rightP z) * assocP := by
            simp only [flattenP, vineIndex, tensorP_apply, map_mul, x, y, z,
              mergeBC]
            group
    _ = mergeP (vineIndex aTree) (vineIndex bTree + vineIndex cTree + 1) *
          rightP mergeBC * leftP x * rightP (leftP y) *
          rightP (rightP z) * assocP := by
            calc
              mergeP (vineIndex aTree) (vineIndex bTree + vineIndex cTree + 1) *
                    leftP x * rightP mergeBC * rightP (leftP y) *
                    rightP (rightP z) * assocP =
                  mergeP (vineIndex aTree) (vineIndex bTree + vineIndex cTree + 1) *
                    (leftP x * rightP mergeBC) * rightP (leftP y) *
                    rightP (rightP z) * assocP := by group
              _ = mergeP (vineIndex aTree) (vineIndex bTree + vineIndex cTree + 1) *
                    (rightP mergeBC * leftP x) * rightP (leftP y) *
                    rightP (rightP z) * assocP := by rw [hcommute.eq]
              _ = _ := by group
    _ = mergeP (vineIndex aTree) (vineIndex bTree + vineIndex cTree + 1) *
          rightP mergeBC * tensorP (x, tensorP (y, z)) * assocP := by
            simp only [tensorP_apply, map_mul]
            group
    _ = (mergeP (vineIndex aTree) (vineIndex bTree + vineIndex cTree + 1) *
          rightP mergeBC * assocP) * tensorP (tensorP (x, y), z) := by
            calc
              mergeP (vineIndex aTree) (vineIndex bTree + vineIndex cTree + 1) *
                    rightP mergeBC * tensorP (x, tensorP (y, z)) * assocP =
                  (mergeP (vineIndex aTree) (vineIndex bTree + vineIndex cTree + 1) *
                    rightP mergeBC) *
                      (tensorP (x, tensorP (y, z)) * assocP) := by group
              _ = (mergeP (vineIndex aTree)
                    (vineIndex bTree + vineIndex cTree + 1) * rightP mergeBC) *
                      (assocP * tensorP (tensorP (x, y), z)) := by rw [hassocTensor]
              _ = _ := by group
    _ = (mergeP (vineIndex aTree + vineIndex bTree + 1) (vineIndex cTree) *
          leftP (mergeP (vineIndex aTree) (vineIndex bTree))) *
            tensorP (tensorP (x, y), z) := by rw [hmerge]
    _ = flattenP (.fork (.fork aTree bTree) cTree) := by
          simp only [flattenP, vineIndex, tensorP_apply, map_mul, x, y, z]
          group

theorem assoc_flattenEquiv (aTree bTree cTree : Tree)
    (hIndex : vineIndex (.fork (.fork aTree bTree) cTree) =
      vineIndex (.fork aTree (.fork bTree cTree))) :
    (assocEquiv aTree bTree cTree).trans
        (flattenTargetEquiv hIndex) =
      flattenEquiv (.fork (.fork aTree bTree) cTree) := by
  have h := congrArg toV (flattenP_assoc aTree bTree cTree)
  simp only [map_mul, toV_flattenP, assocP, toV_quotientMap, evaluation_a] at h
  have hcoe := congrArg Subtype.val h
  simp only [Subgroup.coe_mul] at hcoe
  have hchange :
      table (.fork aTree (.fork bTree cTree))
          (rightVine (vineIndex (.fork (.fork aTree bTree) cTree)))
          (flattenTargetEquiv hIndex) =
        table (.fork aTree (.fork bTree cTree))
          (rightVine (vineIndex (.fork aTree (.fork bTree cTree))))
          (flattenEquiv (.fork aTree (.fork bTree cTree))) := by
    simpa [flattenTargetEquiv] using
      table_change_target (flattenEquiv (.fork aTree (.fork bTree cTree)))
        (congrArg rightVine hIndex.symm)
  change table (.fork aTree (.fork bTree cTree))
        (rightVine (vineIndex (.fork aTree (.fork bTree cTree))))
          (flattenEquiv (.fork aTree (.fork bTree cTree))) *
      table rotationSource rotationTarget rotationEquiv =
    table (.fork (.fork aTree bTree) cTree)
      (rightVine (vineIndex (.fork (.fork aTree bTree) cTree)))
        (flattenEquiv (.fork (.fork aTree bTree) cTree)) at hcoe
  rw [← hchange, ← table_assocEquiv aTree bTree cTree,
    table_mul_table_same_middle] at hcoe
  exact table_equiv_injective _ _ hcoe

theorem tableCodeEq_assoc (aTree bTree cTree : Tree)
    (h : vineIndex (.fork (.fork aTree bTree) cTree) =
      vineIndex (.fork aTree (.fork bTree cTree))) :
    tableCodeEq h (assocEquiv aTree bTree cTree) = assocP := by
  simp only [tableCodeEq]
  have hvineOne :
      vinePermP (vineIndex ((aTree.fork bTree).fork cTree))
          (Equiv.refl _) = 1 := by
    change vinePermP _ 1 = 1
    exact map_one _
  rw [assoc_flattenEquiv aTree bTree cTree h,
    Equiv.symm_trans_self, hvineOne]
  rw [mul_one]
  rw [← flattenP_assoc aTree bTree cTree]
  group

@[simp] theorem tableCode_refl (tree : Tree) :
    tableCode (Equiv.refl tree.Leaf) = 1 := by
  simp [tableCode, tableCodeEq_refl]

theorem tableCode_trans {source middle target : Tree}
    (e : source.Leaf ≃ middle.Leaf) (f : middle.Leaf ≃ target.Leaf) :
    tableCode (e.trans f) = tableCode f * tableCode e := by
  simpa [tableCode] using
    (tableCodeEq_trans e f (vineIndex_eq_of_equiv e) (vineIndex_eq_of_equiv f)).symm

theorem tableCode_sumCongr {sourceLeft sourceRight targetLeft targetRight : Tree}
    (e : sourceLeft.Leaf ≃ targetLeft.Leaf)
    (f : sourceRight.Leaf ≃ targetRight.Leaf) :
    tableCode (source := .fork sourceLeft sourceRight)
        (target := .fork targetLeft targetRight) (e.sumCongr f) =
      tensorP (tableCode e, tableCode f) := by
  simpa [tableCode] using tableCodeEq_sumCongr e f
    (vineIndex_eq_of_equiv e) (vineIndex_eq_of_equiv f)

theorem tableCode_assoc (aTree bTree cTree : Tree) :
    tableCode (assocEquiv aTree bTree cTree) = assocP := by
  simpa [tableCode] using tableCodeEq_assoc aTree bTree cTree
    (vineIndex_eq_of_equiv (assocEquiv aTree bTree cTree))

theorem tableCode_symm {source target : Tree} (e : source.Leaf ≃ target.Leaf) :
    tableCode e.symm = (tableCode e)⁻¹ := by
  have h := tableCode_trans e e.symm
  rw [Equiv.self_trans_symm, tableCode_refl] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem sumComm_fork_left (aTree bTree cTree : Tree) :
    Equiv.sumComm (aTree.Leaf ⊕ bTree.Leaf) cTree.Leaf =
      (assocEquiv aTree bTree cTree).trans
        (((Equiv.refl aTree.Leaf).sumCongr (Equiv.sumComm bTree.Leaf cTree.Leaf)).trans
          ((assocEquiv aTree cTree bTree).symm.trans
            (((Equiv.sumComm aTree.Leaf cTree.Leaf).sumCongr
                (Equiv.refl bTree.Leaf)).trans
              (assocEquiv cTree aTree bTree)))) := by
  simp only [assocEquiv_eq_sumAssoc]
  apply Equiv.ext
  intro i
  rcases i with ((i | i) | i) <;> rfl

theorem sumComm_fork_right (aTree bTree cTree : Tree) :
    Equiv.sumComm aTree.Leaf (bTree.Leaf ⊕ cTree.Leaf) =
      (assocEquiv aTree bTree cTree).symm.trans
        (((Equiv.sumComm aTree.Leaf bTree.Leaf).sumCongr
            (Equiv.refl cTree.Leaf)).trans
          ((assocEquiv bTree aTree cTree).trans
            (((Equiv.refl bTree.Leaf).sumCongr
                (Equiv.sumComm aTree.Leaf cTree.Leaf)).trans
              (assocEquiv bTree cTree aTree).symm))) := by
  simp only [assocEquiv_eq_sumAssoc]
  apply Equiv.ext
  intro i
  rcases i with (i | (i | i)) <;> rfl

theorem tableCode_sumComm : ∀ aTree bTree : Tree,
    tableCode (source := .fork aTree bTree) (target := .fork bTree aTree)
      (Equiv.sumComm aTree.Leaf bTree.Leaf) = swapP := by
  intro aTree
  induction aTree with
  | leaf =>
      intro bTree
      induction bTree with
      | leaf =>
          let q : Equiv.Perm (rightVine 1).Leaf :=
            (flattenEquiv topTree).symm.trans
              ((Equiv.sumComm Unit Unit).trans
                (flattenTargetEquiv (source := topTree) (target := topTree)
                  (vineIndex_eq_of_equiv (Equiv.sumComm Unit Unit))))
          change (flattenP topTree)⁻¹ * vinePermP 1 q * flattenP topTree = swapP
          have hFlatten : flattenP topTree = 1 := by
            simp [topTree, flattenP, vineIndex, mergeP, tensorP_apply]
          rw [hFlatten, inv_one, one_mul, mul_one]
          have hq : q = vinePerm 1 (Equiv.swap 0 1) := by
            decide
          rw [hq]
          change finPermP 1
              ((finVineEquiv 1).symm.permCongr
                (vinePerm 1 (Equiv.swap 0 1))) = swapP
          rw [show (finVineEquiv 1).symm.permCongr
              (vinePerm 1 (Equiv.swap 0 1)) = Equiv.swap 0 1 by
                exact (finVineEquiv 1).permCongr.symm_apply_apply _]
          rw [finPermP_swap]
          rfl
      | fork bTree cTree ihB ihC =>
          rw [sumComm_fork_right]
          let e₁ := (assocEquiv .leaf bTree cTree).symm
          let e₂ := (Equiv.sumComm Unit bTree.Leaf).sumCongr
            (Equiv.refl cTree.Leaf)
          let e₃ := assocEquiv bTree .leaf cTree
          let e₄ := (Equiv.refl bTree.Leaf).sumCongr
            (Equiv.sumComm Unit cTree.Leaf)
          let e₅ := (assocEquiv bTree cTree .leaf).symm
          rw [tableCode_trans
              (source := .fork .leaf (.fork bTree cTree))
              (middle := .fork (.fork .leaf bTree) cTree)
              (target := .fork (.fork bTree cTree) .leaf)
              e₁ (e₂.trans (e₃.trans (e₄.trans e₅))),
            tableCode_trans
              (source := .fork (.fork .leaf bTree) cTree)
              (middle := .fork (.fork bTree .leaf) cTree)
              (target := .fork (.fork bTree cTree) .leaf)
              e₂ (e₃.trans (e₄.trans e₅)),
            tableCode_trans
              (source := .fork (.fork bTree .leaf) cTree)
              (middle := .fork bTree (.fork .leaf cTree))
              (target := .fork (.fork bTree cTree) .leaf)
              e₃ (e₄.trans e₅),
            tableCode_trans
              (source := .fork bTree (.fork .leaf cTree))
              (middle := .fork bTree (.fork cTree .leaf))
              (target := .fork (.fork bTree cTree) .leaf) e₄ e₅]
          dsimp only [e₁, e₂, e₃, e₄, e₅]
          rw [tableCode_symm
              (source := .fork (.fork bTree cTree) .leaf)
              (target := .fork bTree (.fork cTree .leaf))
              (assocEquiv bTree cTree .leaf),
            tableCode_assoc bTree cTree .leaf,
            tableCode_sumCongr
              (sourceLeft := bTree) (sourceRight := .fork .leaf cTree)
              (targetLeft := bTree) (targetRight := .fork cTree .leaf)
              (Equiv.refl bTree.Leaf) (Equiv.sumComm Unit cTree.Leaf),
            tableCode_refl bTree, ihC, tableCode_assoc bTree .leaf cTree,
            tableCode_sumCongr
              (sourceLeft := .fork .leaf bTree) (sourceRight := cTree)
              (targetLeft := .fork bTree .leaf) (targetRight := cTree)
              (Equiv.sumComm Unit bTree.Leaf) (Equiv.refl cTree.Leaf),
            ihB, tableCode_refl cTree,
            tableCode_symm
              (source := .fork (.fork .leaf bTree) cTree)
              (target := .fork .leaf (.fork bTree cTree))
              (assocEquiv .leaf bTree cTree),
            tableCode_assoc .leaf bTree cTree]
          simp only [tensorP_apply, map_one, one_mul, mul_one]
          exact swapP_hexagon_right
  | fork aTree bTree ihA ihB =>
      intro cTree
      rw [sumComm_fork_left]
      let e₁ := assocEquiv aTree bTree cTree
      let e₂ := (Equiv.refl aTree.Leaf).sumCongr
        (Equiv.sumComm bTree.Leaf cTree.Leaf)
      let e₃ := (assocEquiv aTree cTree bTree).symm
      let e₄ := (Equiv.sumComm aTree.Leaf cTree.Leaf).sumCongr
        (Equiv.refl bTree.Leaf)
      let e₅ := assocEquiv cTree aTree bTree
      rw [tableCode_trans
          (source := .fork (.fork aTree bTree) cTree)
          (middle := .fork aTree (.fork bTree cTree))
          (target := .fork cTree (.fork aTree bTree))
          e₁ (e₂.trans (e₃.trans (e₄.trans e₅))),
        tableCode_trans
          (source := .fork aTree (.fork bTree cTree))
          (middle := .fork aTree (.fork cTree bTree))
          (target := .fork cTree (.fork aTree bTree))
          e₂ (e₃.trans (e₄.trans e₅)),
        tableCode_trans
          (source := .fork aTree (.fork cTree bTree))
          (middle := .fork (.fork aTree cTree) bTree)
          (target := .fork cTree (.fork aTree bTree))
          e₃ (e₄.trans e₅),
        tableCode_trans
          (source := .fork (.fork aTree cTree) bTree)
          (middle := .fork (.fork cTree aTree) bTree)
          (target := .fork cTree (.fork aTree bTree)) e₄ e₅]
      dsimp only [e₁, e₂, e₃, e₄, e₅]
      rw [tableCode_assoc cTree aTree bTree,
        tableCode_sumCongr
          (sourceLeft := .fork aTree cTree) (sourceRight := bTree)
          (targetLeft := .fork cTree aTree) (targetRight := bTree)
          (Equiv.sumComm aTree.Leaf cTree.Leaf) (Equiv.refl bTree.Leaf),
        ihA cTree, tableCode_refl bTree,
        tableCode_symm
          (source := .fork (.fork aTree cTree) bTree)
          (target := .fork aTree (.fork cTree bTree))
          (assocEquiv aTree cTree bTree),
        tableCode_assoc aTree cTree bTree,
        tableCode_sumCongr
          (sourceLeft := aTree) (sourceRight := .fork bTree cTree)
          (targetLeft := aTree) (targetRight := .fork cTree bTree)
          (Equiv.refl aTree.Leaf) (Equiv.sumComm bTree.Leaf cTree.Leaf),
        tableCode_refl aTree, ihB cTree, tableCode_assoc aTree bTree cTree]
      simp only [tensorP_apply, map_one, one_mul, mul_one]
      exact swapP_hexagon_left

def pathSet (tree : Tree) : Set (List Bool) := Set.range (Tree.path tree)

@[simp] theorem nil_mem_pathSet_iff (tree : Tree) :
    [] ∈ pathSet tree ↔ tree = .leaf := by
  cases tree <;> simp [pathSet, Tree.path]

@[simp] theorem cons_false_mem_pathSet_fork (left right : Tree) (word : List Bool) :
    false :: word ∈ pathSet (.fork left right) ↔ word ∈ pathSet left := by
  simp [pathSet, Tree.path]

@[simp] theorem cons_true_mem_pathSet_fork (left right : Tree) (word : List Bool) :
    true :: word ∈ pathSet (.fork left right) ↔ word ∈ pathSet right := by
  simp [pathSet, Tree.path]

theorem pathSet_injective : Function.Injective pathSet := by
  intro source
  induction source with
  | leaf =>
      intro target h
      exact (nil_mem_pathSet_iff target).1 (h ▸ (nil_mem_pathSet_iff .leaf).2 rfl) |>.symm
  | fork sourceLeft sourceRight ihLeft ihRight =>
      intro target h
      cases target with
      | leaf =>
          have hnil : [] ∈ pathSet (.fork sourceLeft sourceRight) :=
            h.symm ▸ (nil_mem_pathSet_iff .leaf).2 rfl
          simp at hnil
      | fork targetLeft targetRight =>
          congr
          · apply ihLeft
            ext word
            have hw := Set.ext_iff.1 h (false :: word)
            simpa using hw
          · apply ihRight
            ext word
            have hw := Set.ext_iff.1 h (true :: word)
            simpa using hw

theorem path_injective (tree : Tree) : Function.Injective (Tree.path tree) := by
  induction tree with
  | leaf =>
      intro i j _
      cases i
      cases j
      rfl
  | fork left right ihLeft ihRight =>
      intro i j h
      rcases i with (i | i) <;> rcases j with (j | j)
      · exact congrArg Sum.inl (ihLeft (List.cons.inj h).2)
      · simp [Tree.path] at h
      · simp [Tree.path] at h
      · exact congrArg Sum.inr (ihRight (List.cons.inj h).2)

theorem paths_eq_of_table_eq_one {source target : Tree}
    (e : source.Leaf ≃ target.Leaf) (htable : table source target e = 1)
    (i : source.Leaf) : Tree.path source i = Tree.path target (e i) := by
  by_contra hne
  obtain ⟨suffix, hleft, hright⟩ := Cantor.exists_append_incomparable hne
  let z : Cantor := fun _ => false
  have hmap := table_prepend_path_append source target e i suffix z
  rw [htable] at hmap
  have hp := Cantor.prefix_or_prefix_of_prepend_eq hmap.symm
  exact hp.elim hright hleft

theorem tree_eq_of_table_eq_one {source target : Tree}
    (e : source.Leaf ≃ target.Leaf) (htable : table source target e = 1) :
    source = target := by
  apply pathSet_injective
  ext word
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, (paths_eq_of_table_eq_one e htable i).symm⟩
  · rintro ⟨j, rfl⟩
    refine ⟨e.symm j, ?_⟩
    simpa using paths_eq_of_table_eq_one e htable (e.symm j)

theorem equiv_eq_refl_of_table_eq_one {tree : Tree}
    (e : Equiv.Perm tree.Leaf) (htable : table tree tree e = 1) :
    e = Equiv.refl _ := by
  apply Equiv.ext
  intro i
  apply path_injective tree
  simpa using (paths_eq_of_table_eq_one e htable i).symm

theorem expandEquiv_refl_eq (tree : Tree) (pieces : tree.Leaf → Tree) :
    expandEquiv (Equiv.refl tree.Leaf) pieces = Equiv.refl _ := by
  apply table_equiv_injective (expand tree pieces) (expand tree pieces)
  calc
    table (expand tree pieces) (expand tree pieces)
        (expandEquiv (Equiv.refl tree.Leaf) pieces) =
      table tree tree (Equiv.refl tree.Leaf) :=
        table_expand tree tree (Equiv.refl tree.Leaf) pieces
    _ = table (expand tree pieces) (expand tree pieces) (Equiv.refl _) := by
      rw [table_refl, table_refl]

theorem expandEquiv_trans_eq {source middle target : Tree}
    (e : source.Leaf ≃ middle.Leaf) (f : middle.Leaf ≃ target.Leaf)
    (pieces : source.Leaf → Tree) :
    expandEquiv (e.trans f) pieces =
      (expandEquiv e pieces).trans
        (expandEquiv f (fun j => pieces (e.symm j))) := by
  apply table_equiv_injective (expand source pieces)
    (expand target (fun k => pieces (e.symm (f.symm k))))
  let middlePieces : middle.Leaf → Tree := fun j => pieces (e.symm j)
  let targetPieces : target.Leaf → Tree :=
    fun k => pieces (e.symm (f.symm k))
  have hComposite :
      table (expand source pieces) (expand target targetPieces)
          (expandEquiv (e.trans f) pieces) = table source target (e.trans f) := by
    simpa [targetPieces] using table_expand source target (e.trans f) pieces
  have hFirst :
      table (expand source pieces) (expand middle middlePieces)
          (expandEquiv e pieces) = table source middle e :=
    table_expand source middle e pieces
  have hSecond :
      table (expand middle middlePieces) (expand target targetPieces)
          (expandEquiv f middlePieces) = table middle target f := by
    simpa [middlePieces, targetPieces] using table_expand middle target f middlePieces
  rw [hComposite]
  calc
    table source target (e.trans f) =
        table middle target f * table source middle e :=
      (table_mul_table_same_middle source middle target e f).symm
    _ = table (expand middle middlePieces) (expand target targetPieces)
          (expandEquiv f middlePieces) *
        table (expand source pieces) (expand middle middlePieces)
          (expandEquiv e pieces) := by rw [hFirst, hSecond]
    _ = table (expand source pieces) (expand target targetPieces)
          ((expandEquiv e pieces).trans (expandEquiv f middlePieces)) :=
      table_mul_table_same_middle _ _ _ _ _

set_option maxRecDepth 10000 in
theorem table_fork_sumComm (left right : Tree) :
    table (.fork left right) (.fork right left)
        (Equiv.sumComm left.Leaf right.Leaf) =
      table topTree topTree (Equiv.sumComm Unit Unit) := by
  apply Equiv.ext
  intro z
  cases h : Cantor.head z <;>
    simp [table_apply, topTree, Tree.encode, Tree.decode, h]

theorem equiv_heq_of_table_eq {source target source' target' : Tree}
    {e : source.Leaf ≃ target.Leaf} {f : source'.Leaf ≃ target'.Leaf}
    (hSource : source = source') (hTarget : target = target')
    (hTable : table source target e = table source' target' f) : HEq e f := by
  subst source'
  subst target'
  exact heq_of_eq (table_equiv_injective source target hTable)

set_option maxHeartbeats 1000000 in
theorem expandEquiv_assoc_heq (aTree bTree cTree : Tree)
    (pieces : (Tree.fork (Tree.fork aTree bTree) cTree).Leaf → Tree) :
    HEq (expandEquiv (assocEquiv aTree bTree cTree) pieces)
      (assocEquiv
        (expand aTree (fun i => pieces (Sum.inl (Sum.inl i))))
        (expand bTree (fun i => pieces (Sum.inl (Sum.inr i))))
        (expand cTree (fun i => pieces (Sum.inr i)))) := by
  let piecesA : aTree.Leaf → Tree := fun i => pieces (Sum.inl (Sum.inl i))
  let piecesB : bTree.Leaf → Tree := fun i => pieces (Sum.inl (Sum.inr i))
  let piecesC : cTree.Leaf → Tree := fun i => pieces (Sum.inr i)
  have hSource :
      expand (.fork (.fork aTree bTree) cTree) pieces =
        .fork (.fork (expand aTree piecesA) (expand bTree piecesB))
          (expand cTree piecesC) := by rfl
  have hTarget :
      expand (.fork aTree (.fork bTree cTree))
          (fun j => pieces ((assocEquiv aTree bTree cTree).symm j)) =
        .fork (expand aTree piecesA)
          (.fork (expand bTree piecesB) (expand cTree piecesC)) := by
    rw [assocEquiv_eq_sumAssoc]
    rfl
  apply equiv_heq_of_table_eq hSource hTarget
  calc
    table (expand (.fork (.fork aTree bTree) cTree) pieces)
        (expand (.fork aTree (.fork bTree cTree))
          (fun j => pieces ((assocEquiv aTree bTree cTree).symm j)))
        (expandEquiv (assocEquiv aTree bTree cTree) pieces) =
        table (.fork (.fork aTree bTree) cTree)
          (.fork aTree (.fork bTree cTree))
          (assocEquiv aTree bTree cTree) :=
      table_expand _ _ _ _
    _ = table rotationSource rotationTarget rotationEquiv :=
      table_assocEquiv _ _ _
    _ = table
        (.fork (.fork (expand aTree piecesA) (expand bTree piecesB))
          (expand cTree piecesC))
        (.fork (expand aTree piecesA)
          (.fork (expand bTree piecesB) (expand cTree piecesC)))
        (assocEquiv (expand aTree piecesA) (expand bTree piecesB)
          (expand cTree piecesC)) := (table_assocEquiv _ _ _).symm

set_option maxHeartbeats 1000000 in
theorem expandEquiv_sumComm_heq (left right : Tree)
    (pieces : (Tree.fork left right).Leaf → Tree) :
    HEq (expandEquiv (source := .fork left right) (target := .fork right left)
      (Equiv.sumComm left.Leaf right.Leaf) pieces)
      (Equiv.sumComm
        (expand left (fun i => pieces (Sum.inl i))).Leaf
        (expand right (fun i => pieces (Sum.inr i))).Leaf) := by
  let piecesLeft : left.Leaf → Tree := fun i => pieces (Sum.inl i)
  let piecesRight : right.Leaf → Tree := fun i => pieces (Sum.inr i)
  have hSource : expand (.fork left right) pieces =
      .fork (expand left piecesLeft) (expand right piecesRight) := by rfl
  have hTarget :
      expand (.fork right left)
          (fun j => pieces ((Equiv.sumComm left.Leaf right.Leaf).symm j)) =
        .fork (expand right piecesRight) (expand left piecesLeft) := by rfl
  refine equiv_heq_of_table_eq
    (source := expand (.fork left right) pieces)
    (target := expand (.fork right left)
      (fun j => pieces ((Equiv.sumComm left.Leaf right.Leaf).symm j)))
    (source' := .fork (expand left piecesLeft) (expand right piecesRight))
    (target' := .fork (expand right piecesRight) (expand left piecesLeft))
    (e := expandEquiv (source := .fork left right) (target := .fork right left)
      (Equiv.sumComm left.Leaf right.Leaf) pieces)
    (f := Equiv.sumComm (expand left piecesLeft).Leaf
      (expand right piecesRight).Leaf) hSource hTarget ?_
  calc
    table (expand (.fork left right) pieces)
        (expand (.fork right left)
          (fun j => pieces ((Equiv.sumComm left.Leaf right.Leaf).symm j)))
        (expandEquiv (source := .fork left right) (target := .fork right left)
          (Equiv.sumComm left.Leaf right.Leaf) pieces) =
        table (.fork left right) (.fork right left)
          (Equiv.sumComm left.Leaf right.Leaf) :=
      table_expand _ _ _ _
    _ = table topTree topTree (Equiv.sumComm Unit Unit) :=
      table_fork_sumComm left right
    _ = table (.fork (expand left piecesLeft) (expand right piecesRight))
        (.fork (expand right piecesRight) (expand left piecesLeft))
        (Equiv.sumComm (expand left piecesLeft).Leaf
          (expand right piecesRight).Leaf) :=
      (table_fork_sumComm (expand left piecesLeft) (expand right piecesRight)).symm

set_option maxHeartbeats 1000000 in
theorem expandEquiv_sumCongr_heq
    {sourceLeft sourceRight targetLeft targetRight : Tree}
    (e : sourceLeft.Leaf ≃ targetLeft.Leaf)
    (f : sourceRight.Leaf ≃ targetRight.Leaf)
    (pieces : (Tree.fork sourceLeft sourceRight).Leaf → Tree) :
    HEq (expandEquiv (source := .fork sourceLeft sourceRight)
        (target := .fork targetLeft targetRight) (e.sumCongr f) pieces)
      ((expandEquiv e (fun i => pieces (Sum.inl i))).sumCongr
        (expandEquiv f (fun i => pieces (Sum.inr i)))) := by
  let piecesLeft : sourceLeft.Leaf → Tree := fun i => pieces (Sum.inl i)
  let piecesRight : sourceRight.Leaf → Tree := fun i => pieces (Sum.inr i)
  let targetPiecesLeft : targetLeft.Leaf → Tree :=
    fun j => piecesLeft (e.symm j)
  let targetPiecesRight : targetRight.Leaf → Tree :=
    fun j => piecesRight (f.symm j)
  have hSource : expand (.fork sourceLeft sourceRight) pieces =
      .fork (expand sourceLeft piecesLeft) (expand sourceRight piecesRight) := by rfl
  have hTarget :
      expand (.fork targetLeft targetRight)
          (fun j => pieces ((e.sumCongr f).symm j)) =
        .fork (expand targetLeft targetPiecesLeft)
          (expand targetRight targetPiecesRight) := by rfl
  refine equiv_heq_of_table_eq
    (source := expand (.fork sourceLeft sourceRight) pieces)
    (target := expand (.fork targetLeft targetRight)
      (fun j => pieces ((e.sumCongr f).symm j)))
    (source' := .fork (expand sourceLeft piecesLeft)
      (expand sourceRight piecesRight))
    (target' := .fork (expand targetLeft targetPiecesLeft)
      (expand targetRight targetPiecesRight))
    (e := expandEquiv (source := .fork sourceLeft sourceRight)
      (target := .fork targetLeft targetRight) (e.sumCongr f) pieces)
    (f := (expandEquiv e piecesLeft).sumCongr
      (expandEquiv f piecesRight)) hSource hTarget ?_
  calc
    table (expand (.fork sourceLeft sourceRight) pieces)
        (expand (.fork targetLeft targetRight)
          (fun j => pieces ((e.sumCongr f).symm j)))
        (expandEquiv (source := .fork sourceLeft sourceRight)
          (target := .fork targetLeft targetRight) (e.sumCongr f) pieces) =
        table (.fork sourceLeft sourceRight) (.fork targetLeft targetRight)
          (e.sumCongr f) := table_expand _ _ _ _
    _ = Cantor.branchPerm false (table sourceLeft targetLeft e) *
          Cantor.branchPerm true (table sourceRight targetRight f) :=
      table_fork _ _ _ _ _ _
    _ = table
        (.fork (expand sourceLeft piecesLeft) (expand sourceRight piecesRight))
        (.fork (expand targetLeft targetPiecesLeft)
          (expand targetRight targetPiecesRight))
        ((expandEquiv e piecesLeft).sumCongr
          (expandEquiv f piecesRight)) := by
      rw [table_fork, table_expand, table_expand]

set_option maxHeartbeats 1000000 in
theorem expandEquiv_symm_heq {source target : Tree}
    (e : source.Leaf ≃ target.Leaf) (pieces : target.Leaf → Tree) :
    HEq (expandEquiv e.symm pieces)
      (expandEquiv e (fun i => pieces (e i))).symm := by
  let sourcePieces : source.Leaf → Tree := fun i => pieces (e i)
  let targetPieces : target.Leaf → Tree := fun j => sourcePieces (e.symm j)
  have hSource : expand target pieces = expand target targetPieces := by
    congr 1
    funext j
    simp [targetPieces, sourcePieces]
  have hTarget :
      expand source (fun i => pieces (e.symm.symm i)) =
        expand source sourcePieces := by
    congr 1
  apply equiv_heq_of_table_eq hSource hTarget
  have hExpanded := table_expand source target e sourcePieces
  calc
    table (expand target pieces)
        (expand source (fun i => pieces (e.symm.symm i)))
        (expandEquiv e.symm pieces) = table target source e.symm :=
      table_expand target source e.symm pieces
    _ = (table source target e)⁻¹ := (table_symm source target e).symm
    _ = (table (expand source sourcePieces) (expand target targetPieces)
          (expandEquiv e sourcePieces))⁻¹ :=
      congrArg Inv.inv hExpanded.symm
    _ = table (expand target targetPieces) (expand source sourcePieces)
        (expandEquiv e sourcePieces).symm :=
      table_symm _ _ _

inductive Realizes : {source target : Tree} →
    (source.Leaf ≃ target.Leaf) → P → Prop
  | refl (tree : Tree) : Realizes (Equiv.refl tree.Leaf) 1
  | assoc (aTree bTree cTree : Tree) :
      Realizes (assocEquiv aTree bTree cTree) assocP
  | swap (aTree bTree : Tree) :
      Realizes (source := .fork aTree bTree) (target := .fork bTree aTree)
        (Equiv.sumComm aTree.Leaf bTree.Leaf) swapP
  | trans {source middle target : Tree}
      {e : source.Leaf ≃ middle.Leaf} {f : middle.Leaf ≃ target.Leaf}
      {p q : P} : Realizes e p → Realizes f q → Realizes (e.trans f) (q * p)
  | sumCongr {sourceLeft sourceRight targetLeft targetRight : Tree}
      {e : sourceLeft.Leaf ≃ targetLeft.Leaf}
      {f : sourceRight.Leaf ≃ targetRight.Leaf} {p q : P} :
      Realizes e p → Realizes f q →
        Realizes (source := .fork sourceLeft sourceRight)
          (target := .fork targetLeft targetRight) (e.sumCongr f) (tensorP (p, q))
  | symm {source target : Tree} {e : source.Leaf ≃ target.Leaf} {p : P} :
      Realizes e p → Realizes e.symm p⁻¹

theorem Realizes.of_heq {source target source' target' : Tree}
    {e : source.Leaf ≃ target.Leaf} {e' : source'.Leaf ≃ target'.Leaf}
    {p : P} (hSource : source = source') (hTarget : target = target')
    (hEquiv : HEq e e') (h : Realizes e p) : Realizes e' p := by
  subst source'
  subst target'
  cases hEquiv
  exact h

theorem Realizes.changeTarget {source target target' : Tree}
    {e : source.Leaf ≃ target.Leaf} {p : P} (h : Realizes e p)
    (hTarget : target = target') :
    Realizes (e.trans (leafEquivOfEq hTarget)) p := by
  cases hTarget
  simpa [leafEquivOfEq] using h

theorem Realizes.changeSource {source source' target : Tree}
    {e : source.Leaf ≃ target.Leaf} {p : P} (h : Realizes e p)
    (hSource : source = source') :
    Realizes ((leafEquivOfEq hSource).symm.trans e) p := by
  cases hSource
  simpa [leafEquivOfEq] using h

theorem Realizes.eq_tableCode {source target : Tree}
    {e : source.Leaf ≃ target.Leaf} {p : P} (h : Realizes e p) :
    p = tableCode e := by
  induction h with
  | refl tree => simp
  | assoc aTree bTree cTree => exact (tableCode_assoc _ _ _).symm
  | swap aTree bTree => exact (tableCode_sumComm _ _).symm
  | trans h₁ h₂ ih₁ ih₂ =>
      rw [tableCode_trans, ← ih₁, ← ih₂]
  | sumCongr h₁ h₂ ih₁ ih₂ =>
      rw [tableCode_sumCongr, ← ih₁, ← ih₂]
  | symm h ih =>
      rw [tableCode_symm, ← ih]

theorem Realizes.expand {source target : Tree}
    {e : source.Leaf ≃ target.Leaf} {p : P} (h : Realizes e p)
    (pieces : source.Leaf → Tree) :
    Realizes (expandEquiv e pieces) p := by
  induction h with
  | refl tree =>
      rw [expandEquiv_refl_eq]
      exact Realizes.refl (Tree.expand tree pieces)
  | assoc aTree bTree cTree =>
      let piecesA : aTree.Leaf → Tree := fun i => pieces (Sum.inl (Sum.inl i))
      let piecesB : bTree.Leaf → Tree := fun i => pieces (Sum.inl (Sum.inr i))
      let piecesC : cTree.Leaf → Tree := fun i => pieces (Sum.inr i)
      have hSource :
          Tree.expand (.fork (.fork aTree bTree) cTree) pieces =
            .fork (.fork (Tree.expand aTree piecesA) (Tree.expand bTree piecesB))
              (Tree.expand cTree piecesC) := by rfl
      have hTarget :
          Tree.expand (.fork aTree (.fork bTree cTree))
              (fun j => pieces ((assocEquiv aTree bTree cTree).symm j)) =
            .fork (Tree.expand aTree piecesA)
              (.fork (Tree.expand bTree piecesB) (Tree.expand cTree piecesC)) := by
        rw [assocEquiv_eq_sumAssoc]
        rfl
      have hEq := expandEquiv_assoc_heq aTree bTree cTree pieces
      exact Realizes.of_heq hSource.symm hTarget.symm hEq.symm
        (Realizes.assoc (Tree.expand aTree piecesA) (Tree.expand bTree piecesB)
          (Tree.expand cTree piecesC))
  | swap aTree bTree =>
      let piecesA : aTree.Leaf → Tree := fun i => pieces (Sum.inl i)
      let piecesB : bTree.Leaf → Tree := fun i => pieces (Sum.inr i)
      have hSource : Tree.expand (.fork aTree bTree) pieces =
          .fork (Tree.expand aTree piecesA) (Tree.expand bTree piecesB) := by rfl
      have hTarget :
          Tree.expand (.fork bTree aTree)
              (fun j => pieces ((Equiv.sumComm aTree.Leaf bTree.Leaf).symm j)) =
            .fork (Tree.expand bTree piecesB) (Tree.expand aTree piecesA) := by rfl
      have hEq := expandEquiv_sumComm_heq aTree bTree pieces
      exact Realizes.of_heq hSource.symm hTarget.symm hEq.symm
        (Realizes.swap (Tree.expand aTree piecesA) (Tree.expand bTree piecesB))
  | @trans source middle target e f p q h₁ h₂ ih₁ ih₂ =>
      let middlePieces : middle.Leaf → Tree := fun j => pieces (e.symm j)
      have hFirst := ih₁ pieces
      have hSecond := ih₂ middlePieces
      rw [expandEquiv_trans_eq]
      exact Realizes.trans hFirst hSecond
  | @sumCongr sourceLeft sourceRight targetLeft targetRight e f p q
      h₁ h₂ ih₁ ih₂ =>
      let leftPieces : sourceLeft.Leaf → Tree := fun i => pieces (Sum.inl i)
      let rightPieces : sourceRight.Leaf → Tree := fun i => pieces (Sum.inr i)
      have hLeft := ih₁ leftPieces
      have hRight := ih₂ rightPieces
      let targetLeftPieces : targetLeft.Leaf → Tree :=
        fun j => leftPieces (e.symm j)
      let targetRightPieces : targetRight.Leaf → Tree :=
        fun j => rightPieces (f.symm j)
      have hSource : Tree.expand (.fork sourceLeft sourceRight) pieces =
          .fork (Tree.expand sourceLeft leftPieces)
            (Tree.expand sourceRight rightPieces) := by rfl
      have hTarget :
          Tree.expand (.fork targetLeft targetRight)
              (fun j => pieces ((e.sumCongr f).symm j)) =
            .fork (Tree.expand targetLeft targetLeftPieces)
              (Tree.expand targetRight targetRightPieces) := by rfl
      have hEq := expandEquiv_sumCongr_heq e f pieces
      exact Realizes.of_heq hSource.symm hTarget.symm hEq.symm
        (Realizes.sumCongr hLeft hRight)
  | @symm source target e p h ih =>
      let sourcePieces : source.Leaf → Tree := fun i => pieces (e i)
      let targetPieces : target.Leaf → Tree :=
        fun j => sourcePieces (e.symm j)
      have hExpanded := ih sourcePieces
      have hSource : Tree.expand target pieces =
          Tree.expand target targetPieces := by
        congr 1
        funext j
        simp [targetPieces, sourcePieces]
      have hTarget :
          Tree.expand source (fun i => pieces (e.symm.symm i)) =
            Tree.expand source sourcePieces := by
        congr 1
      have hEq := expandEquiv_symm_heq e pieces
      exact Realizes.of_heq hSource.symm hTarget.symm hEq.symm
        (Realizes.symm hExpanded)

theorem Realizes.expandTarget {source target : Tree}
    {e : source.Leaf ≃ target.Leaf} {p : P} (h : Realizes e p)
    (pieces : target.Leaf → Tree) :
    Realizes (expandEquiv e (fun i => pieces (e i))) p := by
  simpa using h.expand (fun i => pieces (e i))

theorem rightP_assocP : rightP assocP = quotientMap b := by
  rfl

theorem rightP_swapP : rightP swapP = quotientMap t := by
  rfl

theorem generator_realization (i : Generator) :
    ∃ (source target : Tree) (e : source.Leaf ≃ target.Leaf),
      Realizes e (quotientMap (FreeGroup.of i)) := by
  fin_cases i
  · refine ⟨.fork (.fork .leaf .leaf) .leaf,
      .fork .leaf (.fork .leaf .leaf), assocEquiv .leaf .leaf .leaf, ?_⟩
    change Realizes (assocEquiv .leaf .leaf .leaf) assocP
    exact Realizes.assoc .leaf .leaf .leaf
  · refine ⟨.fork .leaf (.fork (.fork .leaf .leaf) .leaf),
      .fork .leaf (.fork .leaf (.fork .leaf .leaf)),
      (Equiv.refl Unit).sumCongr (assocEquiv .leaf .leaf .leaf), ?_⟩
    have h := Realizes.sumCongr (Realizes.refl .leaf)
      (Realizes.assoc .leaf .leaf .leaf)
    simpa [tensorP_apply, rightP_assocP, b] using h
  · refine ⟨.fork .leaf .leaf, .fork .leaf .leaf,
      Equiv.sumComm Unit Unit, ?_⟩
    change @Realizes (.fork .leaf .leaf) (.fork .leaf .leaf)
      (Equiv.sumComm Unit Unit) swapP
    exact Realizes.swap .leaf .leaf
  · refine ⟨.fork .leaf (.fork .leaf .leaf),
      .fork .leaf (.fork .leaf .leaf),
      (Equiv.refl Unit).sumCongr (Equiv.sumComm Unit Unit), ?_⟩
    have h := Realizes.sumCongr (Realizes.refl .leaf) (Realizes.swap .leaf .leaf)
    simpa [tensorP_apply, rightP_swapP, t] using h

theorem word_realization (w : Word) :
    ∃ (source target : Tree) (e : source.Leaf ≃ target.Leaf),
      Realizes e (quotientMap w) := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      exact ⟨.leaf, .leaf, Equiv.refl Unit, by simpa using Realizes.refl .leaf⟩
  | of i =>
      exact generator_realization i
  | inv_of i _ =>
      obtain ⟨source, target, e, h⟩ := generator_realization i
      exact ⟨target, source, e.symm, by
        simpa only [map_inv] using Realizes.symm h⟩
  | mul u v hu hv =>
      obtain ⟨sourceU, targetU, eU, hU⟩ := hu
      obtain ⟨sourceV, targetV, eV, hV⟩ := hv
      let piecesV := joinPiecesLeft targetV sourceU
      let piecesU := joinPiecesRight targetV sourceU
      have hV' := hV.expandTarget piecesV
      have hU' := hU.expand piecesU
      have hmiddleV : Tree.expand targetV piecesV = Tree.join targetV sourceU := by
        exact expand_joinPiecesLeft targetV sourceU
      have hmiddleV' :
          Tree.expand targetV (fun j => piecesV (eV (eV.symm j))) =
            Tree.join targetV sourceU := by
        calc
          Tree.expand targetV (fun j => piecesV (eV (eV.symm j))) =
              Tree.expand targetV piecesV := by
            congr 1
            funext j
            simp
          _ = Tree.join targetV sourceU := hmiddleV
      have hmiddleU : Tree.expand sourceU piecesU = Tree.join targetV sourceU := by
        exact expand_joinPiecesRight targetV sourceU
      have hV'' := hV'.changeTarget hmiddleV'
      have hU'' := hU'.changeSource hmiddleU
      exact ⟨_, _, _, by
        simpa only [map_mul] using Realizes.trans hV'' hU''⟩

theorem toV_injective : Function.Injective toV := by
  apply (injective_iff_map_eq_one toV).2
  intro p hp
  induction p using PresentedGroup.induction_on with
  | H w =>
      obtain ⟨source, target, e, hRealizes⟩ := word_realization w
      have htableV :
          (⟨table source target e, table_mem_V _ _ _⟩ : V) = 1 := by
        exact (toV_tableCode e).symm.trans
          ((congrArg toV hRealizes.eq_tableCode).symm.trans hp)
      have htable : table source target e = 1 := by
        simpa using congrArg Subtype.val htableV
      have htrees := tree_eq_of_table_eq_one e htable
      subst target
      have he := equiv_eq_refl_of_table_eq_one e htable
      subst e
      exact hRealizes.eq_tableCode.trans (tableCode_refl source)

theorem toV_surjective : Function.Surjective toV := by
  intro g
  obtain ⟨source, target, e, hg⟩ := mem_V_iff_table.mp g.2
  refine ⟨tableCode e, ?_⟩
  rw [toV_tableCode]
  exact Subtype.ext hg.symm

noncomputable def presentationEquiv : P ≃* V :=
  MulEquiv.ofBijective toV ⟨toV_injective, toV_surjective⟩

end Presentation

end Submission.Thompson.Tree
