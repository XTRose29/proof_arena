import ChallengeDeps
import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/Cycles.lean
section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open unitInterval
noncomputable section
namespace HurewiczSupport
abbrev K (X:Type) [TopologicalSpace X] := (TopCat.toSSet.obj (TopCat.of X)).chainComplex (AddCommGrpCat.of ℤ)
noncomputable abbrev sc1 (S : SSet) : ShortComplex AddCommGrpCat :=
  (S.chainComplex (AddCommGrpCat.of ℤ)).sc' 2 1 0
noncomputable abbrev scX (X:Type) [TopologicalSpace X] : ShortComplex AddCommGrpCat := sc1 (TopCat.toSSet.obj (TopCat.of X))
noncomputable abbrev H1Quot (X:Type) [TopologicalSpace X] : Type :=
 (AddMonoidHom.ker (scX X).g.hom) ⧸ (AddMonoidHom.range (scX X).abToCycles)
noncomputable def integralHomologyOneIso (X:Type) [TopologicalSpace X] :
 ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1 |>.obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)) ≅ AddCommGrpCat.of (H1Quot X) := by
 let k := K X
 exact (k.homologyIsoSc' 2 1 0 (by simpa using ChainComplex.prev ℕ 1)
     (by simpa using ChainComplex.next_nat_succ 0)) ≪≫ (scX X).abHomologyIso
noncomputable def integralHomologyOneEquiv (X:Type) [TopologicalSpace X] :
 (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1 |>.obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)):Type) ≃+
 H1Quot X := (integralHomologyOneIso X).addCommGroupIsoToAddEquiv

/-- generator corresponding to a singular simplex in the coproduct chain group -/
abbrev chainGen {X : Type} [TopologicalSpace X] {m:ℕ}
 (a : TopCat.toSSet.obj (TopCat.of X) _⦋m⦌) : (K X).X m :=
  (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R:=AddCommGrpCat.of ℤ) a (1:ℤ)

lemma boundary_chainGen {Y : Type} [TopologicalSpace Y] {m:ℕ}
 (a : TopCat.toSSet.obj (TopCat.of Y) _⦋(m+1)⦌) :
  (K Y).d (m+1) m (chainGen a) = ∑ i : Fin (m+2), (-1 : ℤ)^i.val • chainGen ((TopCat.toSSet.obj (TopCat.of Y)).δ i a) := by
  have h := (SSet.ιChainComplex_d (C:=AddCommGrpCat) (X:=TopCat.toSSet.obj (TopCat.of Y)) (R:=AddCommGrpCat.of ℤ) a)
  have h' := congrArg (fun (f : AddCommGrpCat.of ℤ ⟶ (K Y).X m) => f (1:ℤ)) h
  rw [ConcreteCategory.comp_apply] at h'
  have eval_sum {ι : Type} [DecidableEq ι]
      (s : Finset ι) (u : ι → (AddCommGrpCat.of ℤ ⟶ (K Y).X m)) :
      (∑ i ∈ s, u i) (1:ℤ) = ∑ i ∈ s, u i (1:ℤ) := by
        classical
        induction s using Finset.induction_on with
        | empty => rfl
        | @insert i t hi ht => simp [hi, ht]
  classical
  rw [eval_sum] at h'
  simp only [AddCommGrpCat.hom_zsmul, AddMonoidHom.zsmul_apply] at h'
  exact h'

/-- Singular edge from an ordinary path, through the interval description. -/
noncomputable def pathSimplex {X:Type} [TopologicalSpace X] {x y:X} (p:Path x y) :
 TopCat.toSSet.obj (TopCat.of X) _⦋1⦌ :=
  TopCat.toSSetObj₁Equiv.symm (TopCat.pathEquiv (X := TopCat.of X) |>.symm p).hom
@[simp] lemma pathSimplex_source {X:Type} [TopologicalSpace X] {x y:X} (p:Path x y) :
  (TopCat.toSSet.obj (TopCat.of X)).δ 1 (pathSimplex p) = TopCat.toSSetObj₀Equiv.symm x := by
  rw [pathSimplex, TopCat.δ_one_toSSetObj₁Equiv.symm]
  congr 1
  exact p.source
@[simp] lemma pathSimplex_target {X:Type} [TopologicalSpace X] {x y:X} (p:Path x y) :
  (TopCat.toSSet.obj (TopCat.of X)).δ 0 (pathSimplex p) = TopCat.toSSetObj₀Equiv.symm y := by
  rw [pathSimplex, TopCat.δ_zero_toSSetObj₁Equiv.symm]
  congr 1
  exact p.target

/-- The one-chain of a loop is a cycle. -/
noncomputable def loopCycle {X:Type} [TopologicalSpace X] (x:X) (p:Path x x) :
 AddMonoidHom.ker (scX X).g.hom := by
  refine ⟨chainGen (pathSimplex p), ?_⟩
  change (K X).d 1 0 (chainGen (pathSimplex p)) = 0
  rw [boundary_chainGen (m:=0)]
  classical
  simp [Fin.sum_univ_two, pathSimplex_source, pathSimplex_target]

/-- Class of a based path. -/
noncomputable def loopClass {X:Type} [TopologicalSpace X] (x:X) (p:Path x x) : H1Quot X :=
  QuotientAddGroup.mk' _ (loopCycle x p)
end HurewiczSupport

end

end
-- END INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/Cycles.lean

-- BEGIN INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/LoopMap.lean
section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open unitInterval
noncomputable section
namespace HurewiczSupport
variable {X : Type} [TopologicalSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)

abbrev Simp (T : SSet) (n:ℕ) := T _⦋n⦌
-- small coordinate calculations for faces of an ordinary topological triangle
private lemma __LoopMap_face000 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 0 = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __LoopMap_face001 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 1 = z 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __LoopMap_face002 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 2 = z 1 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __LoopMap_face100 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (1:Fin 3)) z : Fin 3 → ℝ) 0 = z 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __LoopMap_face101 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (1:Fin 3)) z : Fin 3 → ℝ) 1 = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __LoopMap_face102 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (1:Fin 3)) z : Fin 3 → ℝ) 2 = z 1 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __LoopMap_face200 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 0 = z 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __LoopMap_face201 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 1 = z 1 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __LoopMap_face202 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 2 = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]

private def __LoopMap_zcoord (i : Fin 3) : stdSimplex ℝ (Fin 3) → ℝ :=
  fun z => z i
private lemma __LoopMap_zcoord_cont (i : Fin 3) : Continuous (__LoopMap_zcoord i) :=
  (continuous_apply i).comp continuous_subtype_val
private lemma __LoopMap_sum12_mem (z : stdSimplex ℝ (Fin 3)) : z 1 + z 2 ∈ Set.Icc (0:ℝ) 1 := by
  have hs := stdSimplex.sum_eq_one z
  simp only [Fin.sum_univ_three] at hs
  constructor
  · linarith [stdSimplex.zero_le z (1:Fin 3), stdSimplex.zero_le z (2:Fin 3)]
  · linarith [stdSimplex.zero_le z (0:Fin 3)]
private lemma __LoopMap_one_mem (z : stdSimplex ℝ (Fin 3)) (i : Fin 3) : z i ∈ Set.Icc (0:ℝ) 1 :=
  ⟨stdSimplex.zero_le z i, stdSimplex.le_one z i⟩

private def __LoopMap_c1 (z : stdSimplex ℝ (Fin 3)) : I := ⟨z 1 + z 2, __LoopMap_sum12_mem z⟩
private def __LoopMap_c2 (z : stdSimplex ℝ (Fin 3)) : I := ⟨z 2, __LoopMap_one_mem z _⟩
private def __LoopMap_c3 (z : stdSimplex ℝ (Fin 3)) : I := ⟨z 1, __LoopMap_one_mem z _⟩
private lemma __LoopMap_c1_cont : Continuous (__LoopMap_c1 : stdSimplex ℝ (Fin 3) → I) :=
  Continuous.subtype_mk ((__LoopMap_zcoord_cont (1:Fin 3)).add (__LoopMap_zcoord_cont (2:Fin 3))) _
private lemma __LoopMap_c2_cont : Continuous (__LoopMap_c2 : stdSimplex ℝ (Fin 3) → I) :=
  Continuous.subtype_mk (__LoopMap_zcoord_cont (2:Fin 3)) _
private lemma __LoopMap_c3_cont : Continuous (__LoopMap_c3 : stdSimplex ℝ (Fin 3) → I) :=
  Continuous.subtype_mk (__LoopMap_zcoord_cont (1:Fin 3)) _

/-- First of the two triangles in the square of a path homotopy.  Vertices are
(0,0),(1,0),(1,1). -/
private def __LoopMap_tri₁ {x : X} {p q : Path x x} (F : p.Homotopy q) : Simp S 2 :=
  (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
    ⟨ (fun z => F (__LoopMap_c1 z, __LoopMap_c2 z)),
      F.continuous.comp (__LoopMap_c1_cont.prodMk __LoopMap_c2_cont) ⟩
/-- Second triangle. Vertices are (0,0),(1,1),(0,1). -/
private def __LoopMap_tri₂ {x : X} {p q : Path x x} (F : p.Homotopy q) : Simp S 2 :=
  (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
    ⟨ (fun z => F (__LoopMap_c3 z, __LoopMap_c1 z)),
      F.continuous.comp (__LoopMap_c3_cont.prodMk __LoopMap_c1_cont) ⟩

-- convenient evaluation rules
@[simp] private lemma __LoopMap_tri₁_eval {x : X} {p q : Path x x} (F : p.Homotopy q)
    (z : stdSimplex ℝ (Fin 3)) :
    (TopCat.toSSetObjEquiv (TopCat.of X) _ (__LoopMap_tri₁ F)) z = F (__LoopMap_c1 z, __LoopMap_c2 z) := by
  simp [__LoopMap_tri₁]
@[simp] private lemma __LoopMap_tri₂_eval {x:X} {p q:Path x x} (F:p.Homotopy q)
    (z : stdSimplex ℝ (Fin 3)) :
    (TopCat.toSSetObjEquiv (TopCat.of X) _ (__LoopMap_tri₂ F)) z = F (__LoopMap_c3 z, __LoopMap_c1 z) := by
  simp [__LoopMap_tri₂]

-- ext/evaluation principle for edges
private lemma __LoopMap_edge_ext {a b : Simp S 1}
    (h : ∀ z : stdSimplex ℝ (Fin 2),
      (TopCat.toSSetObjEquiv (TopCat.of X) _ a) z =
      (TopCat.toSSetObjEquiv (TopCat.of X) _ b) z) : a = b := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
  ext z
  exact h z

private lemma __LoopMap_home_val (z : stdSimplex ℝ (Fin 2)) :
    (TopCat.stdSimplexHomeomorphI.{0} z).down.val = z 1 := rfl
private def __LoopMap_iz (z : stdSimplex ℝ (Fin 2)) : I :=
  (TopCat.stdSimplexHomeomorphI.{0} z).down
private lemma __LoopMap_iz_val (z : stdSimplex ℝ (Fin 2)) : (__LoopMap_iz z : ℝ) = z 1 := rfl
private lemma __LoopMap_zsum (z : stdSimplex ℝ (Fin 2)) : z 0 + z 1 = 1 := stdSimplex.add_eq_one z

-- faces of the square triangles
private lemma __LoopMap_tri₁_face0 {x:X} {p q:Path x x} (F:p.Homotopy q) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 0 (__LoopMap_tri₁ F) = pathSimplex q := by
  apply __LoopMap_edge_ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, __LoopMap_tri₁_eval]
  have h1 := __LoopMap_face001 z
  have h2 := __LoopMap_face002 z
  change F (⟨_, _⟩, ⟨_, _⟩) = q (__LoopMap_iz z)
  calc
    _ = F (1, __LoopMap_iz z) := by
      congr 2
      · apply Subtype.ext
        change _ + _ = (1:ℝ)
        rw [h1, h2, __LoopMap_zsum]
      · apply Subtype.ext
        change _ = z 1
        exact h2
    _ = _ := F.map_one_left _

private lemma __LoopMap_tri₁_face2_const {x:X} {p q:Path x x} (F:p.Homotopy q) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 2 (__LoopMap_tri₁ F) = pathSimplex (Path.refl x) := by
  apply __LoopMap_edge_ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, __LoopMap_tri₁_eval]
  have h1 := __LoopMap_face201 z
  have h2 := __LoopMap_face202 z
  change F (⟨_, _⟩, ⟨_, _⟩) = (Path.refl x) (__LoopMap_iz z)
  calc
    _ = F ( (⟨_, _⟩ : I), 0) := by
      -- the first coordinate is kept; the second is zero
      congr 2
      apply Subtype.ext
      exact h2
    _ = _ := Path.Homotopy.source F _

private lemma __LoopMap_tri₂_face0_const {x:X} {p q:Path x x} (F:p.Homotopy q) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 0 (__LoopMap_tri₂ F) = pathSimplex (Path.refl x) := by
  apply __LoopMap_edge_ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, __LoopMap_tri₂_eval]
  have h1 := __LoopMap_face001 z
  have h2 := __LoopMap_face002 z
  change F (⟨_, _⟩, ⟨_, _⟩) = (Path.refl x) (__LoopMap_iz z)
  calc
    _ = F ((⟨_, _⟩ : I), 1) := by
      congr 2
      apply Subtype.ext
      change _ + _ = (1:ℝ)
      rw [h1, h2, __LoopMap_zsum]
    _ = _ := Path.Homotopy.target F _

private lemma __LoopMap_tri₂_face1 {x:X} {p q:Path x x} (F:p.Homotopy q) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 1 (__LoopMap_tri₂ F) = pathSimplex p := by
  apply __LoopMap_edge_ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, __LoopMap_tri₂_eval]
  have h1 := __LoopMap_face101 z
  have h2 := __LoopMap_face102 z
  change F (⟨_, _⟩, ⟨_, _⟩) = p (__LoopMap_iz z)
  calc
    _ = F (0, __LoopMap_iz z) := by
      congr 2
      · apply Subtype.ext
        exact h1
      · apply Subtype.ext
        change _ + _ = z 1
        rw [h1, h2]
        simp
    _ = _ := F.map_zero_left _

private lemma __LoopMap_diag_eq {x:X} {p q:Path x x} (F:p.Homotopy q) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 2 (__LoopMap_tri₂ F) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 1 (__LoopMap_tri₁ F) := by
  apply __LoopMap_edge_ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, __LoopMap_tri₂_eval,
      TopCat.toSSetObjEquiv_δ_apply, __LoopMap_tri₁_eval]
  have a1 := __LoopMap_face201 z
  have a2 := __LoopMap_face202 z
  have b1 := __LoopMap_face101 z
  have b2 := __LoopMap_face102 z
  -- both arguments are (z1,z1)
  apply congrArg (fun w : I × I => F w)
    -- automatically changes to equality of the two pairs
    ?_
  congr 1 <;> apply Subtype.ext
  · change (stdSimplex.map (Fin.succAbove (2:Fin 3)) z) 1 = (stdSimplex.map (Fin.succAbove (1:Fin 3)) z) 1 + (stdSimplex.map (Fin.succAbove (1:Fin 3)) z) 2
    rw [a1, b1,b2]
    simp
  · change (stdSimplex.map (Fin.succAbove (2:Fin 3)) z) 1 + (stdSimplex.map (Fin.succAbove (2:Fin 3)) z) 2 = (stdSimplex.map (Fin.succAbove (1:Fin 3)) z) 2
    rw [a1,a2,b2]
    simp

/-- A constant singular edge is itself a boundary (unnormalized chains). -/
private def __LoopMap_constTri (x : X) : Simp S 2 :=
 (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
   ⟨fun _ => x, continuous_const⟩
private lemma __LoopMap_constTri_faces (x:X) (i:Fin 3) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (__LoopMap_constTri x) = pathSimplex (Path.refl x) := by
  apply __LoopMap_edge_ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  simp [__LoopMap_constTri, pathSimplex, TopCat.toSSetObj₁Equiv, TopCat.pathEquiv, __LoopMap_iz, ConcreteCategory.comp_apply]
  change x = (Path.refl x) (TopCat.stdSimplexHomeomorphI z).down
  rfl



private lemma __LoopMap_homotopy_boundary {x:X} {p q:Path x x} (F:p.Homotopy q) :
    ((K X).d 2 1)
        (- chainGen (__LoopMap_tri₁ F) - chainGen (__LoopMap_tri₂ F) +
          (2:ℤ) • chainGen (__LoopMap_constTri x)) =
      chainGen (pathSimplex p) - chainGen (pathSimplex q) := by
  rw [map_add, map_sub, map_neg, map_zsmul]
  rw [boundary_chainGen (m:=1), boundary_chainGen (m:=1), boundary_chainGen (m:=1)]
  simp [Fin.sum_univ_succ, Fin.sum_univ_two, __LoopMap_tri₁_face0, __LoopMap_tri₁_face2_const,
    __LoopMap_tri₂_face0_const, __LoopMap_tri₂_face1, __LoopMap_diag_eq, __LoopMap_constTri_faces]
  module

 theorem loopClass_homotopy {x : X} {p q : Path x x} (F : p.Homotopy q) :
    loopClass x p = loopClass x q := by
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  change (loopCycle x p - loopCycle x q) ∈
    AddMonoidHom.range (sc1 (TopCat.toSSet.obj (TopCat.of X))).abToCycles
  refine ⟨(- chainGen (__LoopMap_tri₁ F) - chainGen (__LoopMap_tri₂ F) +
        (2:ℤ) • chainGen (__LoopMap_constTri x)), ?_⟩
  apply Subtype.ext
  change ((K X).d 2 1)
        (- chainGen (__LoopMap_tri₁ F) - chainGen (__LoopMap_tri₂ F) +
          (2:ℤ) • chainGen (__LoopMap_constTri x)) =
      chainGen (pathSimplex p) - chainGen (pathSimplex q)
  exact __LoopMap_homotopy_boundary F

/-- Degenerate (constant) loop has zero class even in the unnormalised singular
complex: its three-face constant triangle has boundary that edge. -/
theorem loopClass_refl {x : X} : loopClass x (Path.refl x) = 0 := by
  change (QuotientAddGroup.mk' _ (loopCycle x (Path.refl x))) =
    (0 : H1Quot X)
  apply (QuotientAddGroup.eq_zero_iff _).2
  change loopCycle x (Path.refl x) ∈
    AddMonoidHom.range (sc1 (TopCat.toSSet.obj (TopCat.of X))).abToCycles
  refine ⟨chainGen (__LoopMap_constTri x), ?_⟩
  apply Subtype.ext
  change (K X).d 2 1 (chainGen (__LoopMap_constTri x)) = chainGen (pathSimplex (Path.refl x))
  rw [boundary_chainGen (m:=1)]
  simp [Fin.sum_univ_succ, __LoopMap_constTri_faces]


end HurewiczSupport

end

end
-- END INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/LoopMap.lean

-- BEGIN INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/Concat.lean
section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open unitInterval
noncomputable section
namespace HurewiczSupport
variable {X : Type} [TopologicalSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)
-- A few barycentric coordinate calculations.  These deliberately live here
-- rather than making any use of normalised chains: throughout this construction
-- we work with the un-normalised singular chain complex from `Cycles`.
private lemma __Concat_tface001 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 1 = z 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __Concat_tface002 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 2 = z 1 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __Concat_tface101 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (1:Fin 3)) z : Fin 3 → ℝ) 1 = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __Concat_tface102 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (1:Fin 3)) z : Fin 3 → ℝ) 2 = z 1 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __Concat_tface201 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 1 = z 1 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __Concat_tface202 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 2 = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]

private def __Concat_tc (i : Fin 3) : stdSimplex ℝ (Fin 3) → ℝ := fun z => z i
private lemma __Concat_tc_cont (i : Fin 3) : Continuous (__Concat_tc i) :=
  (continuous_apply i).comp continuous_subtype_val

-- The parameter assigned to a point in the triangle whose vertices have
-- parameters 0, 1/2 and 1 on the concatenated path.
private lemma __Concat_concat_mem (z : stdSimplex ℝ (Fin 3)) :
    z 1 / 2 + z 2 ∈ Set.Icc (0:ℝ) 1 := by
  have hs := stdSimplex.sum_eq_one z
  simp only [Fin.sum_univ_three] at hs
  constructor
  · linarith [stdSimplex.zero_le z (1:Fin 3), stdSimplex.zero_le z (2:Fin 3)]
  · linarith [stdSimplex.zero_le z (0:Fin 3), stdSimplex.zero_le z (1:Fin 3),
      stdSimplex.zero_le z (2:Fin 3)]
private def __Concat_concat_t (z : stdSimplex ℝ (Fin 3)) : I :=
  ⟨z 1 / 2 + z 2, __Concat_concat_mem z⟩
private lemma __Concat_concat_t_cont : Continuous (__Concat_concat_t : stdSimplex ℝ (Fin 3) → I) :=
  Continuous.subtype_mk ((__Concat_tc_cont (1:Fin 3)).div_const (2:ℝ) |>.add (__Concat_tc_cont (2:Fin 3))) _

/-- A single triangle filling the boundary consisting of `p`, `q`, and their
literal half-speed concatenation.  Face 0 is `q`, face 1 the concatenation,
and face 2 is `p`.  The linear choice of the real parameter is important: on
face 1 it is just the usual parameter, while on the other two it runs through
one half of the interval. -/
private def __Concat_transTri {x : X} (p q : Path x x) : Simp S 2 :=
  (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
    ⟨(fun z => (p.trans q) (__Concat_concat_t z)),
      (p.trans q).continuous.comp __Concat_concat_t_cont⟩
@[simp] private lemma __Concat_transTri_eval {x : X} (p q : Path x x)
    (z : stdSimplex ℝ (Fin 3)) :
    (TopCat.toSSetObjEquiv (TopCat.of X) _ (__Concat_transTri p q)) z =
      (p.trans q) (__Concat_concat_t z) := by
  simp [__Concat_transTri]

private lemma __Concat_trans_edge_ext {a b : Simp S 1}
    (h : ∀ z : stdSimplex ℝ (Fin 2),
      (TopCat.toSSetObjEquiv (TopCat.of X) _ a) z =
        (TopCat.toSSetObjEquiv (TopCat.of X) _ b) z) : a = b := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
  ext z
  exact h z
private def __Concat_tiz (z : stdSimplex ℝ (Fin 2)) : I :=
  (TopCat.stdSimplexHomeomorphI.{0} z).down
private lemma __Concat_tiz_val (z : stdSimplex ℝ (Fin 2)) : (__Concat_tiz z : ℝ) = z 1 := rfl
private lemma __Concat_tsum (z : stdSimplex ℝ (Fin 2)) : z 0 + z 1 = 1 :=
  stdSimplex.add_eq_one z

-- face 0 uses the second half of the concatenation
private lemma __Concat_transTri_face0 {x : X} (p q : Path x x) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 0 (__Concat_transTri p q) = pathSimplex q := by
  apply __Concat_trans_edge_ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, __Concat_transTri_eval]
  -- only the real coordinates of this face will be used below
  have h1 := __Concat_tface001 z
  have h2 := __Concat_tface002 z
  have hz := __Concat_tsum z
  change (p.trans q) (⟨_, _⟩ : I) = q (__Concat_tiz z)
  -- regard the point as an extension parameter on the real line.  This lets
  -- us use the two half-interval formulas without splitting an equality case.
  have ht : (1 / 2 : ℝ) ≤
      (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 1 / 2 +
        (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 2 := by
    rw [h1, h2]
    have hznon := stdSimplex.zero_le z (1:Fin 2)
    linarith
  calc
    (p.trans q) (⟨_, _⟩ : I) =
        (p.trans q).extend
          ((stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 1 / 2 +
            (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 2) := by
              symm
              exact Path.extend_extends'
                (p.trans q)
                (⟨_, _⟩ : Set.Icc (0:ℝ) 1)
    _ = q.extend
          (2 * ((stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 1 / 2 +
            (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 2) - 1) := by
              exact Path.extend_trans_of_half_le p q ht
    _ = q.extend (z 1) := by
          congr 1
          rw [h1, h2]
          linarith
    _ = q (__Concat_tiz z) := by
          -- the interval point used for one-simplices has this value
          simpa [__Concat_tiz_val] using (Path.extend_extends' q (__Concat_tiz z))

-- face 1 goes all the way down the diagonal, hence is the literal trans path
private lemma __Concat_transTri_face1 {x : X} (p q : Path x x) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 1 (__Concat_transTri p q) = pathSimplex (p.trans q) := by
  apply __Concat_trans_edge_ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, __Concat_transTri_eval]
  have h1 := __Concat_tface101 z
  have h2 := __Concat_tface102 z
  change (p.trans q) (⟨_, _⟩ : I) = (p.trans q) (__Concat_tiz z)
  congr 1
  apply Subtype.ext
  change _ / 2 + _ = (z 1:ℝ)
  rw [h1, h2]
  ring

-- face 2 uses the first half
private lemma __Concat_transTri_face2 {x : X} (p q : Path x x) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 2 (__Concat_transTri p q) = pathSimplex p := by
  apply __Concat_trans_edge_ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, __Concat_transTri_eval]
  have h1 := __Concat_tface201 z
  have h2 := __Concat_tface202 z
  change (p.trans q) (⟨_, _⟩ : I) = p (__Concat_tiz z)
  have ht :
      (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 1 / 2 +
          (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 2 ≤
        (1 / 2 : ℝ) := by
      rw [h1, h2]
      have hzle := stdSimplex.le_one z (1:Fin 2)
      linarith
  calc
    (p.trans q) (⟨_, _⟩ : I) =
        (p.trans q).extend
          ((stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 1 / 2 +
            (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 2) := by
              symm
              exact Path.extend_extends'
                (p.trans q)
                (⟨_, _⟩ : Set.Icc (0:ℝ) 1)
    _ = p.extend
          (2 * ((stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 1 / 2 +
            (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 2)) := by
              exact Path.extend_trans_of_le_half p q ht
    _ = p.extend (z 1) := by
          congr 1
          rw [h1, h2]
          ring
    _ = p (__Concat_tiz z) := by
          simpa [__Concat_tiz_val] using (Path.extend_extends' p (__Concat_tiz z))

private lemma __Concat_transTri_boundary {x : X} (p q : Path x x) :
    (K X).d 2 1 (chainGen (__Concat_transTri p q)) =
      chainGen (pathSimplex q) - chainGen (pathSimplex (p.trans q)) +
        chainGen (pathSimplex p) := by
  rw [boundary_chainGen (m:=1)]
  simp [Fin.sum_univ_succ, __Concat_transTri_face0, __Concat_transTri_face1, __Concat_transTri_face2,
    sub_eq_add_neg, add_assoc]

/-- The singular-cycle class of a literal concatenation is the sum of the two
classes.  This is proved for `Path.trans` itself (not just for reparametrised
or homotopic paths), so it is the useful multiplicativity statement before
passing to fundamental-group quotients. -/
theorem loopClass_trans {x : X} (p q : Path x x) :
    loopClass x (p.trans q) = loopClass x p + loopClass x q := by
  -- make the quotient representatives explicit; membership will be witnessed
  -- by the (negative) triangle above.  The equality on the right is first
  -- expressed as one representative since the quotient projection is
  -- additive.
  change
    (QuotientAddGroup.mk'
        (AddMonoidHom.range (sc1 (TopCat.toSSet.obj (TopCat.of X))).abToCycles)
        (loopCycle x (p.trans q))) =
      (QuotientAddGroup.mk'
        (AddMonoidHom.range (sc1 (TopCat.toSSet.obj (TopCat.of X))).abToCycles)
        (loopCycle x p)) +
      (QuotientAddGroup.mk'
        (AddMonoidHom.range (sc1 (TopCat.toSSet.obj (TopCat.of X))).abToCycles)
        (loopCycle x q))
  rw [← map_add]
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  change (loopCycle x (p.trans q) - (loopCycle x p + loopCycle x q)) ∈
    AddMonoidHom.range (sc1 (TopCat.toSSet.obj (TopCat.of X))).abToCycles
  refine ⟨- chainGen (__Concat_transTri p q), ?_⟩
  apply Subtype.ext
  change (K X).d 2 1 (- chainGen (__Concat_transTri p q)) =
    chainGen (pathSimplex (p.trans q)) -
      (chainGen (pathSimplex p) + chainGen (pathSimplex q))
  rw [map_neg, __Concat_transTri_boundary]
  abel

end HurewiczSupport

end

end
-- END INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/Concat.lean

-- BEGIN INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/Pi1Map.lean
section

/-!
This file constructs the easy half of the degree one Hurewicz map.  An
important minor point here is the convention on multiplication in
`FundamentalGroup`: it is an `End`, so that `a*b` is `b ≫ a`.  Hence the order
of the two loops below is reversed.  Passing to an abelian target is exactly
what permits this to still be a homomorphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open unitInterval
noncomputable section
namespace HurewiczSupport

variable {X : Type} [TopologicalSpace X]

/-- `loopClass` is constant on homotopy classes (with the endpoints fixed),
so it can first be regarded as a function on arrows in the fundamental
groupoid.  We only need the endomorphism case here.  Defining this separately
is useful: the quotient in `FundamentalGroupoid` is literally this `Quotient`,
not a second auxiliary quotient. -/
noncomputable def quotientLoopClass (x : X) :
    Path.Homotopic.Quotient x x → H1Quot X :=
  Quotient.lift (fun p : Path x x => loopClass x p)
    (by
      rintro a b ⟨F⟩
      exact loopClass_homotopy F)

@[simp]
theorem quotientLoopClass_mk {x : X} (p : Path x x) :
    quotientLoopClass x (Path.Homotopic.Quotient.mk p) = loopClass x p :=
  rfl

@[simp]
theorem quotientLoopClass_refl {x : X} :
    quotientLoopClass x (Path.Homotopic.Quotient.refl x) = 0 := by
  change loopClass x (Path.refl x) = 0
  exact loopClass_refl

/-- Composition of arrows in the path groupoid is literal `Path.trans` on
representatives.  At this stage there is no reparametrisation to do: it is
precisely the triangle of `loopClass_trans`. -/
@[simp]
theorem quotientLoopClass_trans {x : X}
    (a b : Path.Homotopic.Quotient x x) :
    quotientLoopClass x (Path.Homotopic.Quotient.trans a b) =
      quotientLoopClass x a + quotientLoopClass x b := by
  induction a using Path.Homotopic.Quotient.ind with
  | mk a =>
    induction b using Path.Homotopic.Quotient.ind with
    | mk b =>
      change loopClass x (a.trans b) = loopClass x a + loopClass x b
      exact loopClass_trans a b

/-- The based-loop map, now an honest homomorphism on `π₁`.  We use the
multiplicative synonym of the kernel/range homology group.  Multiplication in
`End` is the *reverse* of category composition; thus in `map_mul'` the arrow
represented by `b` is followed by the arrow represented by `a`.  The target is
commutative, so `loopClass_trans` gives the required equality after commuting
these two summands. -/
noncomputable def pi1H1Hom (x : X) :
    FundamentalGroup X x →* Multiplicative (H1Quot X) where
  toFun g :=
    Multiplicative.ofAdd (quotientLoopClass x (FundamentalGroup.toPath g))
  map_one' := by
    change quotientLoopClass x (Path.Homotopic.Quotient.refl x) = 0
    exact quotientLoopClass_refl
  map_mul' a b := by
    change quotientLoopClass x
        (Path.Homotopic.Quotient.trans (FundamentalGroup.toPath b)
          (FundamentalGroup.toPath a)) =
      quotientLoopClass x (FundamentalGroup.toPath a) +
        quotientLoopClass x (FundamentalGroup.toPath b)
    rw [quotientLoopClass_trans]
    ac_rfl

@[simp]
theorem pi1H1Hom_mk (x : X) (p : Path x x) :
    pi1H1Hom x
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      Multiplicative.ofAdd (loopClass x p) :=
  rfl

/-- The target is commutative, so the preceding map factors canonically
through the algebraic abelianization. -/
noncomputable def abPi1H1Hom (x : X) :
    Abelianization (FundamentalGroup X x) →* Multiplicative (H1Quot X) :=
  Abelianization.lift (pi1H1Hom x)

/-- Additive form of `abPi1H1Hom`.  Both synonyms on the target cancel
definitionally (`Additive (Multiplicative A)` has the same operations as `A`),
which makes this the hom whose bijectivity is needed for the eventual
edge-path theorem. -/
noncomputable def additiveAbPi1H1Hom (x : X) :
    Additive (Abelianization (FundamentalGroup X x)) →+ H1Quot X := by
  let f : Additive (Abelianization (FundamentalGroup X x)) →+
      Additive (Multiplicative (H1Quot X)) :=
    MonoidHom.toAdditive (abPi1H1Hom x)
  exact f

@[simp]
theorem abPi1H1Hom_of (x : X) (g : FundamentalGroup X x) :
    abPi1H1Hom x (Abelianization.of g) = pi1H1Hom x g := by
  simp [abPi1H1Hom]

@[simp]
theorem additiveAbPi1H1Hom_of (x : X) (p : Path x x) :
    additiveAbPi1H1Hom x
        (Additive.ofMul
          (Abelianization.of
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)))) =
      loopClass x p := by
  change
    abPi1H1Hom x
        (Abelianization.of
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) =
      Multiplicative.ofAdd (loopClass x p)
  rw [abPi1H1Hom_of, pi1H1Hom_mk]

end HurewiczSupport

end

end
-- END INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/Pi1Map.lean

-- BEGIN INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/EdgeConcat.lean
section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open unitInterval
noncomputable section
namespace HurewiczSupport
variable {X : Type} [TopologicalSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)
-- A few barycentric coordinate calculations.  These deliberately live here
-- rather than making any use of normalised chains: throughout this construction
-- we work with the un-normalised singular chain complex from `Cycles`.
private lemma __EdgeConcat_tface001 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 1 = z 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __EdgeConcat_tface002 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 2 = z 1 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __EdgeConcat_tface101 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (1:Fin 3)) z : Fin 3 → ℝ) 1 = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __EdgeConcat_tface102 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (1:Fin 3)) z : Fin 3 → ℝ) 2 = z 1 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __EdgeConcat_tface201 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 1 = z 1 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]
private lemma __EdgeConcat_tface202 (z : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 2 = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ _ (z:Fin 2 → ℝ) _ = _
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.succAbove]

private def __EdgeConcat_tc (i : Fin 3) : stdSimplex ℝ (Fin 3) → ℝ := fun z => z i
private lemma __EdgeConcat_tc_cont (i : Fin 3) : Continuous (__EdgeConcat_tc i) :=
  (continuous_apply i).comp continuous_subtype_val

-- The parameter assigned to a point in the triangle whose vertices have
-- parameters 0, 1/2 and 1 on the concatenated path.
private lemma __EdgeConcat_concat_mem (z : stdSimplex ℝ (Fin 3)) :
    z 1 / 2 + z 2 ∈ Set.Icc (0:ℝ) 1 := by
  have hs := stdSimplex.sum_eq_one z
  simp only [Fin.sum_univ_three] at hs
  constructor
  · linarith [stdSimplex.zero_le z (1:Fin 3), stdSimplex.zero_le z (2:Fin 3)]
  · linarith [stdSimplex.zero_le z (0:Fin 3), stdSimplex.zero_le z (1:Fin 3),
      stdSimplex.zero_le z (2:Fin 3)]
private def __EdgeConcat_concat_t (z : stdSimplex ℝ (Fin 3)) : I :=
  ⟨z 1 / 2 + z 2, __EdgeConcat_concat_mem z⟩
private lemma __EdgeConcat_concat_t_cont : Continuous (__EdgeConcat_concat_t : stdSimplex ℝ (Fin 3) → I) :=
  Continuous.subtype_mk ((__EdgeConcat_tc_cont (1:Fin 3)).div_const (2:ℝ) |>.add (__EdgeConcat_tc_cont (2:Fin 3))) _

/-- A single triangle filling the boundary consisting of `p`, `q`, and their
literal half-speed concatenation.  Face 0 is `q`, face 1 the concatenation,
and face 2 is `p`.  The linear choice of the real parameter is important: on
face 1 it is just the usual parameter, while on the other two it runs through
one half of the interval. -/
private def __EdgeConcat_transTri {u v w : X} (p : Path u v) (q : Path v w) : Simp S 2 :=
  (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
    ⟨(fun z => (p.trans q) (__EdgeConcat_concat_t z)),
      (p.trans q).continuous.comp __EdgeConcat_concat_t_cont⟩
@[simp] private lemma __EdgeConcat_transTri_eval {u v w : X} (p : Path u v) (q : Path v w)
    (z : stdSimplex ℝ (Fin 3)) :
    (TopCat.toSSetObjEquiv (TopCat.of X) _ (__EdgeConcat_transTri p q)) z =
      (p.trans q) (__EdgeConcat_concat_t z) := by
  simp [__EdgeConcat_transTri]

private lemma __EdgeConcat_trans_edge_ext {a b : Simp S 1}
    (h : ∀ z : stdSimplex ℝ (Fin 2),
      (TopCat.toSSetObjEquiv (TopCat.of X) _ a) z =
        (TopCat.toSSetObjEquiv (TopCat.of X) _ b) z) : a = b := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
  ext z
  exact h z
private def __EdgeConcat_tiz (z : stdSimplex ℝ (Fin 2)) : I :=
  (TopCat.stdSimplexHomeomorphI.{0} z).down
private lemma __EdgeConcat_tiz_val (z : stdSimplex ℝ (Fin 2)) : (__EdgeConcat_tiz z : ℝ) = z 1 := rfl
private lemma __EdgeConcat_tsum (z : stdSimplex ℝ (Fin 2)) : z 0 + z 1 = 1 :=
  stdSimplex.add_eq_one z

-- face 0 uses the second half of the concatenation
private lemma __EdgeConcat_transTri_face0 {u v w : X} (p : Path u v) (q : Path v w) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 0 (__EdgeConcat_transTri p q) = pathSimplex q := by
  apply __EdgeConcat_trans_edge_ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, __EdgeConcat_transTri_eval]
  -- only the real coordinates of this face will be used below
  have h1 := __EdgeConcat_tface001 z
  have h2 := __EdgeConcat_tface002 z
  have hz := __EdgeConcat_tsum z
  change (p.trans q) (⟨_, _⟩ : I) = q (__EdgeConcat_tiz z)
  -- regard the point as an extension parameter on the real line.  This lets
  -- us use the two half-interval formulas without splitting an equality case.
  have ht : (1 / 2 : ℝ) ≤
      (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 1 / 2 +
        (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 2 := by
    rw [h1, h2]
    have hznon := stdSimplex.zero_le z (1:Fin 2)
    linarith
  calc
    (p.trans q) (⟨_, _⟩ : I) =
        (p.trans q).extend
          ((stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 1 / 2 +
            (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 2) := by
              symm
              exact Path.extend_extends'
                (p.trans q)
                (⟨_, _⟩ : Set.Icc (0:ℝ) 1)
    _ = q.extend
          (2 * ((stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 1 / 2 +
            (stdSimplex.map (Fin.succAbove (0:Fin 3)) z : Fin 3 → ℝ) 2) - 1) := by
              exact Path.extend_trans_of_half_le p q ht
    _ = q.extend (z 1) := by
          congr 1
          rw [h1, h2]
          linarith
    _ = q (__EdgeConcat_tiz z) := by
          -- the interval point used for one-simplices has this value
          simpa [__EdgeConcat_tiz_val] using (Path.extend_extends' q (__EdgeConcat_tiz z))

-- face 1 goes all the way down the diagonal, hence is the literal trans path
private lemma __EdgeConcat_transTri_face1 {u v w : X} (p : Path u v) (q : Path v w) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 1 (__EdgeConcat_transTri p q) = pathSimplex (p.trans q) := by
  apply __EdgeConcat_trans_edge_ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, __EdgeConcat_transTri_eval]
  have h1 := __EdgeConcat_tface101 z
  have h2 := __EdgeConcat_tface102 z
  change (p.trans q) (⟨_, _⟩ : I) = (p.trans q) (__EdgeConcat_tiz z)
  congr 1
  apply Subtype.ext
  change _ / 2 + _ = (z 1:ℝ)
  rw [h1, h2]
  ring

-- face 2 uses the first half
private lemma __EdgeConcat_transTri_face2 {u v w : X} (p : Path u v) (q : Path v w) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 2 (__EdgeConcat_transTri p q) = pathSimplex p := by
  apply __EdgeConcat_trans_edge_ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, __EdgeConcat_transTri_eval]
  have h1 := __EdgeConcat_tface201 z
  have h2 := __EdgeConcat_tface202 z
  change (p.trans q) (⟨_, _⟩ : I) = p (__EdgeConcat_tiz z)
  have ht :
      (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 1 / 2 +
          (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 2 ≤
        (1 / 2 : ℝ) := by
      rw [h1, h2]
      have hzle := stdSimplex.le_one z (1:Fin 2)
      linarith
  calc
    (p.trans q) (⟨_, _⟩ : I) =
        (p.trans q).extend
          ((stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 1 / 2 +
            (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 2) := by
              symm
              exact Path.extend_extends'
                (p.trans q)
                (⟨_, _⟩ : Set.Icc (0:ℝ) 1)
    _ = p.extend
          (2 * ((stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 1 / 2 +
            (stdSimplex.map (Fin.succAbove (2:Fin 3)) z : Fin 3 → ℝ) 2)) := by
              exact Path.extend_trans_of_le_half p q ht
    _ = p.extend (z 1) := by
          congr 1
          rw [h1, h2]
          ring
    _ = p (__EdgeConcat_tiz z) := by
          simpa [__EdgeConcat_tiz_val] using (Path.extend_extends' p (__EdgeConcat_tiz z))

private lemma __EdgeConcat_transTri_boundary {u v w : X} (p : Path u v) (q : Path v w) :
    (K X).d 2 1 (chainGen (__EdgeConcat_transTri p q)) =
      chainGen (pathSimplex q) - chainGen (pathSimplex (p.trans q)) +
        chainGen (pathSimplex p) := by
  rw [boundary_chainGen (m:=1)]
  simp [Fin.sum_univ_succ, __EdgeConcat_transTri_face0, __EdgeConcat_transTri_face1, __EdgeConcat_transTri_face2,
    sub_eq_add_neg, add_assoc]


/-- For composable paths the concatenation differs from the two edge chains by a
2-boundary.  Endpoints need not be the basepoint. -/
theorem edge_trans_boundary {u v w : X} (p : Path u v) (q : Path v w) :
    (K X).d 2 1 (chainGen (__EdgeConcat_transTri p q)) =
      chainGen (pathSimplex q) - chainGen (pathSimplex (p.trans q)) +
        chainGen (pathSimplex p) :=
  __EdgeConcat_transTri_boundary p q

/-- Rearranged as a witness-producing formula. -/
theorem edge_trans_boundary_neg {u v w : X} (p : Path u v) (q : Path v w) :
    (K X).d 2 1 (- chainGen (__EdgeConcat_transTri p q)) =
      chainGen (pathSimplex (p.trans q)) -
        chainGen (pathSimplex p) - chainGen (pathSimplex q) := by
  rw [map_neg, __EdgeConcat_transTri_boundary]
  abel

theorem edge_trans_exists {u v w : X} (p : Path u v) (q : Path v w) :
    ∃ c : (K X).X 2, (K X).d 2 1 c =
      chainGen (pathSimplex (p.trans q)) -
        chainGen (pathSimplex p) - chainGen (pathSimplex q) :=
  ⟨- chainGen (__EdgeConcat_transTri p q), edge_trans_boundary_neg p q⟩

end HurewiczSupport

end

end
-- END INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/EdgeConcat.lean

-- BEGIN INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/Edges.lean
section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open unitInterval
set_option maxHeartbeats 800000
noncomputable section
namespace HurewiczSupport
variable {X : Type} [TopologicalSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)

/-- endpoints and path underlying a singular edge -/
noncomputable def edgeSource (a : S _⦋1⦌) : X :=
  TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 a)
noncomputable def edgeTarget (a : S _⦋1⦌) : X :=
  TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 a)
noncomputable def edgePath (a : S _⦋1⦌) : Path (edgeSource a) (edgeTarget a) :=
  TopCat.pathEquiv
    ({ hom := TopCat.toSSetObj₁Equiv a
       hom₀ := TopCat.toSSetObj₁Equiv_apply_zero a
       hom₁ := TopCat.toSSetObj₁Equiv_apply_one a } : (TopCat.of X).Path _ _)

@[simp] theorem pathSimplex_edgePath (a : S _⦋1⦌) :
    pathSimplex (edgePath a) = a := by
  change TopCat.toSSetObj₁Equiv.symm
    ((TopCat.pathEquiv).symm (edgePath a)).hom = a
  rw [edgePath, Equiv.symm_apply_apply]
  exact Equiv.symm_apply_apply _ a

-- The big quotient of all one-chains. It is convenient because paths with
-- different endpoints can be compared before imposing the cycle condition.
noncomputable abbrev bigQ (X : Type) [TopologicalSpace X] : Type :=
  ((K X).X 1 : Type) ⧸ AddMonoidHom.range ((K X).d 2 1).hom
noncomputable def bigMk (X : Type) [TopologicalSpace X] :
    ((K X).X 1 : Type) →+ bigQ X :=
  QuotientAddGroup.mk' _

@[simp] theorem bigMk_chain (c : (K X).X 2) :
    bigMk X ((K X).d 2 1 c) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).2
  exact ⟨c, rfl⟩

/-- Each cycle class maps to the quotient of all chains by boundaries. -/
noncomputable def h1ToBig (X : Type) [TopologicalSpace X] : H1Quot X →+ bigQ X := by
  let f : AddMonoidHom.ker (scX X).g.hom →+ bigQ X :=
    (bigMk X).comp (AddSubgroup.subtype _)
  exact QuotientAddGroup.lift _ f (by
    rintro z hz
    rcases hz with ⟨c, rfl⟩
    -- an element in the range of abToCycles is literally a boundary
    apply (QuotientAddGroup.eq_zero_iff _).2
    exact ⟨c, rfl⟩)

@[simp] theorem h1ToBig_mk (z : AddMonoidHom.ker (scX X).g.hom) :
    h1ToBig X (QuotientAddGroup.mk' _ z) = bigMk X z.1 := by
  rfl

theorem h1ToBig_injective : Function.Injective (h1ToBig X) := by
  intro u v h
  induction u using QuotientAddGroup.induction_on with
  | _ u =>
    induction v using QuotientAddGroup.induction_on with
    | _ v =>
      apply (QuotientAddGroup.eq_iff_sub_mem).2
      change bigMk X u.1 = bigMk X v.1 at h
      letI : (AddMonoidHom.range ((K X).d 2 1).hom).Normal := AddSubgroup.normal_of_isAddCommutative _
      have hb : (u.1 - v.1) ∈ AddMonoidHom.range ((K X).d 2 1).hom := by
        have hm : (-(u.1) + v.1) ∈ AddMonoidHom.range ((K X).d 2 1).hom :=
          QuotientAddGroup.eq.mp h
        obtain ⟨c, hc⟩ := hm
        refine ⟨-c, ?_⟩
        rw [map_neg, hc]
        simp [sub_eq_add_neg, add_comm]
        abel

      obtain ⟨c, hc⟩ := hb
      refine ⟨c, ?_⟩
      apply Subtype.ext
      exact hc
end HurewiczSupport

namespace HurewiczSupport
variable {X : Type} [TopologicalSpace X]
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial unitInterval
@[simp] theorem big_trans {u v w : X} (p : Path u v) (q : Path v w) :
    bigMk X (chainGen (pathSimplex (p.trans q))) =
      bigMk X (chainGen (pathSimplex p)) + bigMk X (chainGen (pathSimplex q)) := by
  rw [← map_add]
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  obtain ⟨c, hc⟩ := edge_trans_exists p q
  refine ⟨c, ?_⟩
  -- equality of one-chains
  rw [hc]
  abel
end HurewiczSupport

namespace HurewiczSupport
variable {X : Type} [TopologicalSpace X]
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial unitInterval
@[simp] theorem big_loopClass {x : X} (p : Path x x) :
    h1ToBig X (loopClass x p) = bigMk X (chainGen (pathSimplex p)) := rfl
@[simp] theorem big_refl (x : X) :
    bigMk X (chainGen (pathSimplex (Path.refl x))) = 0 := by
  rw [← big_loopClass]
  rw [loopClass_refl, map_zero]

@[simp] theorem big_symm {u v : X} (p : Path u v) :
    bigMk X (chainGen (pathSimplex p.symm)) =
       - bigMk X (chainGen (pathSimplex p)) := by
  have hq : (Path.Homotopic.Quotient.mk (p.trans p.symm)) =
      Path.Homotopic.Quotient.mk (Path.refl u) := by
    rw [Path.Homotopic.Quotient.mk_trans]
    rw [Path.Homotopic.Quotient.mk_symm]
    exact Path.Homotopic.Quotient.trans_symm _
  have hl : loopClass u (p.trans p.symm) = loopClass u (Path.refl u) := by
    exact congrArg (quotientLoopClass u) hq
  have hb := congrArg (h1ToBig X) hl
  rw [big_loopClass, big_loopClass, big_trans, big_refl] at hb
  -- A + B = 0
  exact eq_neg_of_add_eq_zero_right hb
end HurewiczSupport
namespace HurewiczSupport
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial unitInterval
variable {X : Type} [TopologicalSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)

/-- evaluation hom on the coproduct defining singular chains -/
noncomputable def evalChain (n : ℕ) {A : Type} [AddCommGroup A]
    (f : S _⦋n⦌ → A) : ((K X).X n : Type) →+ A :=
  (Limits.Sigma.desc (fun a : S _⦋n⦌ =>
    AddCommGrpCat.ofHom
      { toFun := fun k : ℤ => k • f a
        map_zero' := by simp
        map_add' := by intros; simp [add_smul] }) :
      ((K X).X n ⟶ AddCommGrpCat.of A)).hom

@[simp] theorem evalChain_gen (n : ℕ) {A : Type} [AddCommGroup A]
    (f : S _⦋n⦌ → A) (a : S _⦋n⦌) :
    evalChain (X:=X) n f (chainGen a) = f a := by
  change (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex a ≫
    (Limits.Sigma.desc (fun b : S _⦋n⦌ =>
      AddCommGrpCat.ofHom
        { toFun := fun k : ℤ => k • f b
          map_zero' := by simp
          map_add' := by intros; simp [add_smul] }) :
       (K X).X n ⟶ AddCommGrpCat.of A)) (1:ℤ)) = _
  change ((Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of X) _⦋n⦌) => AddCommGrpCat.of ℤ) a ≫
    Limits.Sigma.desc (fun b : (TopCat.toSSet.obj (TopCat.of X) _⦋n⦌) =>
      AddCommGrpCat.ofHom
        { toFun := fun k : ℤ => k • f b
          map_zero' := by simp
          map_add' := by intros; simp [add_smul] })) (1:ℤ)) = _
  rw [Limits.Sigma.ι_desc]
  simp

/-- Two chain evaluations coincide if the assigned generator values coincide. -/
theorem eval_ext {n : ℕ} {A : Type} [AddCommGroup A]
    {F G : ((K X).X n : Type) →+ A}
    (h : ∀ a : S _⦋n⦌, F (chainGen a) = G (chainGen a)) : F = G := by
  -- use the categorical coproduct ext principle
  apply AddCommGrpCat.ofHom_injective
  apply SSet.chainComplex_hom_ext (X:= (TopCat.toSSet.obj (TopCat.of X)))
       (R:=AddCommGrpCat.of ℤ)
  intro a
  apply ConcreteCategory.hom_ext _ _
  intro k
  change F ((ConcreteCategory.hom ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R:=AddCommGrpCat.of ℤ) a)) k) =
    G ((ConcreteCategory.hom ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R:=AddCommGrpCat.of ℤ) a)) k)
  have hone := h a
  change F ((ConcreteCategory.hom ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R:=AddCommGrpCat.of ℤ) a)) (1:ℤ)) =
    G ((ConcreteCategory.hom ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R:=AddCommGrpCat.of ℤ) a)) (1:ℤ)) at hone
  have hh := congrArg (fun t => k • t) hone
  simpa [← map_zsmul] using hh

end HurewiczSupport
namespace HurewiczSupport
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial unitInterval
variable {X : Type} [TopologicalSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)
noncomputable def connector [PathConnectedSpace X] (x y : X) : Path x y := by
  classical
  exact if h : y = x then h.symm ▸ Path.refl x else (PathConnectedSpace.joined x y).somePath

@[simp] theorem connector_self [PathConnectedSpace X] (x : X) :
    connector x x = Path.refl x := by simp [connector]
-- definition usable only with path connected; make earlier def require instance
variable [PathConnectedSpace X]
noncomputable def basedEdge (x : X) (a : S _⦋1⦌) : Path x x :=
  ((connector x (edgeSource a)).trans (edgePath a)).trans
    (connector x (edgeTarget a)).symm

@[simp] theorem big_basedEdge (x : X) (a : S _⦋1⦌) :
    bigMk X (chainGen (pathSimplex (basedEdge x a))) =
      bigMk X (chainGen a) +
      bigMk X (chainGen (pathSimplex (connector x (edgeSource a)))) -
      bigMk X (chainGen (pathSimplex (connector x (edgeTarget a)))) := by
  simp [basedEdge, big_trans, big_symm, pathSimplex_edgePath]
  abel

lemma eval_boundary (z : (K X).X 1)
    {A : Type} [AddCommGroup A] (f : X → A) :
    evalChain (X:=X) 0 (fun v : S _⦋0⦌ => f (TopCat.toSSetObj₀Equiv v))
       ((K X).d 1 0 z) =
    evalChain (X:=X) 1 (fun a : S _⦋1⦌ => f (edgeTarget a) - f (edgeSource a)) z := by
  -- equality of the two homomorphisms
  let l : ((K X).X 1 : Type) →+ A :=
    (evalChain (X:=X) 0 (fun v : S _⦋0⦌ => f (TopCat.toSSetObj₀Equiv v))).comp
      ((K X).d 1 0).hom
  have he : l = evalChain (X:=X) 1
      (fun a : S _⦋1⦌ => f (edgeTarget a) - f (edgeSource a)) := by
    apply eval_ext
    intro a
    change evalChain (X:=X) 0 (fun v : S _⦋0⦌ => f (TopCat.toSSetObj₀Equiv v))
       ((K X).d 1 0 (chainGen a)) = _
    rw [boundary_chainGen (m:=0)]
    simp [Fin.sum_univ_two, evalChain_gen, edgeSource, edgeTarget, sub_eq_add_neg]
  exact DFunLike.congr_fun he z

/-- Cancellation of the connectors: a cycle is represented, in the quotient of
all chains by boundaries, by the sum of its based edges. -/
theorem cycle_based_edges (x : X) (z : AddMonoidHom.ker (scX X).g.hom) :
    bigMk X z.1 =
      evalChain (X:=X) 1 (fun a : S _⦋1⦌ =>
        bigMk X (chainGen (pathSimplex (basedEdge x a)))) z.1 := by
  let src : S _⦋1⦌ → bigQ X := fun a =>
    bigMk X (chainGen (pathSimplex (connector x (edgeSource a))))
  let tgt : S _⦋1⦌ → bigQ X := fun a =>
    bigMk X (chainGen (pathSimplex (connector x (edgeTarget a))))
  have he : evalChain (X:=X) 1 (fun a : S _⦋1⦌ =>
        bigMk X (chainGen (pathSimplex (basedEdge x a)))) =
      (bigMk X) + evalChain (X:=X) 1 src - evalChain (X:=X) 1 tgt := by
    apply eval_ext
    intro a
    simp [evalChain_gen, src, tgt, big_basedEdge]
  rw [he]
  -- the remaining two sums cancel by the boundary equation
  have hz0 : (K X).d 1 0 z.1 = 0 := z.2
  have can := eval_boundary (X:=X) z.1
       (fun y => bigMk X (chainGen (pathSimplex (connector x y))))
  rw [hz0] at can
  simp at can
  -- can says targets - sources sum is zero; split evaluation linearly
  have split : evalChain (X:=X) 1
      (fun a : S _⦋1⦌ =>
        bigMk X (chainGen (pathSimplex (connector x (edgeTarget a)))) -
        bigMk X (chainGen (pathSimplex (connector x (edgeSource a))))) =
        evalChain (X:=X) 1 tgt - evalChain (X:=X) 1 src := by
    apply eval_ext
    intro a
    simp [evalChain_gen, src, tgt]
  have cz : (evalChain (X:=X) 1 tgt - evalChain (X:=X) 1 src) z.1 = 0 := by
    rw [← split]
    exact can.symm
  change bigMk X z.1 =
    (bigMk X + evalChain (X:=X) 1 src - evalChain (X:=X) 1 tgt) z.1
  -- pointwise arithmetic
  dsimp
  -- morphism operations evaluate pointwise
  change bigMk X z.1 = bigMk X z.1 + _ - _
  have : evalChain (X:=X) 1 tgt z.1 - evalChain (X:=X) 1 src z.1 = 0 := by
    exact cz
  calc
    _ = bigMk X z.1 + 0 := by simp
    _ = bigMk X z.1 +
        (evalChain (X:=X) 1 src z.1 - evalChain (X:=X) 1 tgt z.1) := by rw [sub_eq_zero.mpr (eq_of_sub_eq_zero this).symm]
    _ = _ := by abel
end HurewiczSupport
namespace HurewiczSupport
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial unitInterval
variable {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)
noncomputable def edgePre (x : X) (a : S _⦋1⦌) :
    Additive (Abelianization (FundamentalGroup X x)) :=
  Additive.ofMul (Abelianization.of
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (basedEdge x a))))

theorem map_eval (x : X) (c : (K X).X 1) :
    additiveAbPi1H1Hom x (evalChain (X:=X) 1 (edgePre x) c) =
      evalChain (X:=X) 1 (fun a : S _⦋1⦌ => loopClass x (basedEdge x a)) c := by
  have e : (additiveAbPi1H1Hom x).comp (evalChain (X:=X) 1 (edgePre x)) =
      evalChain (X:=X) 1 (fun a : S _⦋1⦌ => loopClass x (basedEdge x a)) := by
    apply eval_ext
    intro a
    simp [evalChain_gen, edgePre, additiveAbPi1H1Hom_of]
  exact DFunLike.congr_fun e c

theorem cycle_equal_loops (x : X) (z : AddMonoidHom.ker (scX X).g.hom) :
    QuotientAddGroup.mk' _ z =
      evalChain (X:=X) 1 (fun a : S _⦋1⦌ => loopClass x (basedEdge x a)) z.1 := by
  apply h1ToBig_injective (X:=X)
  rw [h1ToBig_mk]
  rw [cycle_based_edges x z]
  -- commute the map with evaluation
  have e : (h1ToBig X).comp
      (evalChain (X:=X) 1 (fun a : S _⦋1⦌ => loopClass x (basedEdge x a))) =
      evalChain (X:=X) 1 (fun a : S _⦋1⦌ =>
         bigMk X (chainGen (pathSimplex (basedEdge x a)))) := by
    apply eval_ext
    intro a
    simp [evalChain_gen, big_loopClass]
  exact DFunLike.congr_fun e z.1 |>.symm

theorem additiveAb_surjective (x : X) :
    Function.Surjective (additiveAbPi1H1Hom (X:=X) x) := by
  intro y
  induction y using QuotientAddGroup.induction_on with
  | _ z =>
    refine ⟨evalChain (X:=X) 1 (edgePre x) z.1, ?_⟩
    rw [map_eval]
    exact (cycle_equal_loops x z).symm
end HurewiczSupport

end

end
-- END INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/Edges.lean

-- BEGIN INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/Triangles.lean
section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open unitInterval
noncomputable section
namespace HurewiczSupport
variable {X : Type} [TopologicalSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)
-- the point of the 1-simplex associated to a parameter
noncomputable def seg (t : I) : stdSimplex ℝ (Fin 2) :=
  TopCat.stdSimplexHomeomorphI.{0}.symm (ULift.up t)
@[simp] lemma seg_val1 (t : I) : (seg t : Fin 2 → ℝ) 1 = t := by rfl
lemma seg_val0 (t : I) : (seg t : Fin 2 → ℝ) 0 = 1-(t:ℝ) := by
  have h := stdSimplex.add_eq_one (seg t)
  simp only [seg_val1] at h
  linarith
lemma continuous_seg : Continuous (seg : I → stdSimplex ℝ (Fin 2)) :=
  TopCat.stdSimplexHomeomorphI.{0}.symm.continuous.comp continuous_uliftUp

-- canonical parametrised sides in the topological triangle
-- face i opposite i, indices chosen as in singular boundary
noncomputable def cside (i : Fin 3) : I → stdSimplex ℝ (Fin 3) :=
  fun t => stdSimplex.map i.succAbove (seg t)
lemma cside_cont (i : Fin 3) : Continuous (cside i) := by
  -- map is continuous linear
  exact (stdSimplex.continuous_map i.succAbove).comp continuous_seg

-- evaluate an edge of a singular triangle
lemma edge_of_triangle (T : S _⦋2⦌) (i : Fin 3) (t : I) :
    edgePath ((TopCat.toSSet.obj (TopCat.of X)).δ i T) t =
      (TopCat.toSSetObjEquiv (TopCat.of X) _ T) (cside i t) := by
  rfl
end HurewiczSupport

namespace HurewiczSupport
open CategoryTheory AlgebraicTopology Simplicial unitInterval
noncomputable section
-- path along side i in the simplex
noncomputable def cpath (i : Fin 3) :
    Path (stdSimplex.vertex (S:=ℝ) (i.succAbove (0:Fin 2)))
         (stdSimplex.vertex (S:=ℝ) (i.succAbove (1:Fin 2))) where
  toFun := cside i
  continuous_toFun := cside_cont i
  source' := by
    change stdSimplex.map i.succAbove (seg 0) = _
    rw [show seg 0 = stdSimplex.vertex (S:=ℝ) 0 from (TopCat.stdSimplexHomeomorphI.{0}.injective (by rfl))]
    rw [stdSimplex.map_vertex]
  target' := by
    change stdSimplex.map i.succAbove (seg 1) = _
    rw [show seg 1 = stdSimplex.vertex (S:=ℝ) 1 from (TopCat.stdSimplexHomeomorphI.{0}.injective (by rfl))]
    rw [stdSimplex.map_vertex]
-- instantiate endpoints and casts with explicit numerals easier verify
lemma v20 : (2:Fin 3).succAbove (0:Fin 2) = 0 := rfl
lemma v21 : (2:Fin 3).succAbove (1:Fin 2) = 1 := rfl
lemma v00 : (0:Fin 3).succAbove (0:Fin 2) = 1 := rfl
lemma v01 : (0:Fin 3).succAbove (1:Fin 2) = 2 := rfl
lemma v10 : (1:Fin 3).succAbove (0:Fin 2) = 0 := rfl
lemma v11 : (1:Fin 3).succAbove (1:Fin 2) = 2 := rfl
-- broken boundary and direct diagonal, in the simplex
noncomputable def cp2 : Path (stdSimplex.vertex (S:=ℝ) (0:Fin 3)) (stdSimplex.vertex (S:=ℝ) (1:Fin 3)) := cpath 2
noncomputable def cp0 : Path (stdSimplex.vertex (S:=ℝ) (1:Fin 3)) (stdSimplex.vertex (S:=ℝ) (2:Fin 3)) := cpath 0
noncomputable def cp1 : Path (stdSimplex.vertex (S:=ℝ) (0:Fin 3)) (stdSimplex.vertex (S:=ℝ) (2:Fin 3)) := cpath 1

noncomputable def broken : Path (stdSimplex.vertex (S:=ℝ) (0:Fin 3)) (stdSimplex.vertex (S:=ℝ) (2:Fin 3)) :=
  cp2.trans cp0
noncomputable def direct : Path (stdSimplex.vertex (S:=ℝ) (0:Fin 3)) (stdSimplex.vertex (S:=ℝ) (2:Fin 3)) :=
  cp1


-- convex interpolate two points
noncomputable def smix (t : I) (a b : stdSimplex ℝ (Fin 3)) : stdSimplex ℝ (Fin 3) := by
  refine ⟨fun j => (1-(t:ℝ))*a j + (t:ℝ)*b j, ?_, ?_⟩
  · intro j
    have ha := stdSimplex.zero_le a j
    have hb := stdSimplex.zero_le b j
    have ht := t.2
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) ha) (mul_nonneg t.2.1 hb)
  · simp only [Fin.sum_univ_three]
    have ha := stdSimplex.sum_eq_one a
    have hb := stdSimplex.sum_eq_one b
    simp only [Fin.sum_univ_three] at ha hb
    linear_combination (1-(t:ℝ))*ha + (t:ℝ)*hb
lemma smix_zero (a b : stdSimplex ℝ (Fin 3)) : smix 0 a b = a := by
  ext i
  change (1-(0:ℝ))*a i + (0:ℝ)*b i = a i
  ring
lemma smix_one (a b : stdSimplex ℝ (Fin 3)) : smix 1 a b = b := by
  ext i
  change (1-(1:ℝ))*a i + (1:ℝ)*b i = b i
  ring
lemma smix_same (t : I) (a : stdSimplex ℝ (Fin 3)) : smix t a a = a := by
  ext i
  change (1-(t:ℝ))*a i + (t:ℝ)*a i = a i
  ring
lemma smix_cont : Continuous (fun w : I × (stdSimplex ℝ (Fin 3) × stdSimplex ℝ (Fin 3)) => smix w.1 w.2.1 w.2.2) := by
  apply Continuous.subtype_mk _ _
  apply continuous_pi
  intro i
  change Continuous (fun w : I × (stdSimplex ℝ (Fin 3) × stdSimplex ℝ (Fin 3)) =>
    (1-(w.1:ℝ))*w.2.1 i + (w.1:ℝ)*w.2.2 i)
  have ht : Continuous (fun w : I × (stdSimplex ℝ (Fin 3) × stdSimplex ℝ (Fin 3)) => (w.1:ℝ)) :=
    continuous_subtype_val.comp (continuous_fst (X:=I) (Y:= (stdSimplex ℝ (Fin 3) × stdSimplex ℝ (Fin 3))))
  have ha : Continuous (fun w : I × (stdSimplex ℝ (Fin 3) × stdSimplex ℝ (Fin 3)) => w.2.1 i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hb : Continuous (fun w : I × (stdSimplex ℝ (Fin 3) × stdSimplex ℝ (Fin 3)) => w.2.2 i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  exact ((continuous_const.sub ht).mul ha).add (ht.mul hb)

-- homotopy inside the simplex
noncomputable def simplexHom : (broken).Homotopy direct where
  toFun w := smix w.1 (broken w.2) (direct w.2)
  continuous_toFun := by
    have harg : Continuous (fun w : I × I => (w.1, (broken w.2, direct w.2))) := by fun_prop
    exact smix_cont.comp harg
  map_zero_left s := by exact smix_zero _ _
  map_one_left s := by exact smix_one _ _
  prop' t s hs := by
    rcases hs with hs|hs
    · subst s
      -- endpoints coincide
      change smix t (broken 0) (direct 0) = broken 0
      have e : direct 0 = broken 0 := by
        exact (direct.source).trans broken.source.symm
      rw [e]
      exact smix_same _ _
    · rw [Set.mem_singleton_iff] at hs
      subst s
      change smix t (broken 1) (direct 1) = broken 1
      have e : direct 1 = broken 1 := by exact (direct.target).trans broken.target.symm
      rw [e]
      exact smix_same _ _
end
end HurewiczSupport

namespace HurewiczSupport
open CategoryTheory AlgebraicTopology Simplicial unitInterval
variable {X:Type} [TopologicalSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)
lemma ev_v0 (T:S _⦋2⦌) :
 (TopCat.toSSetObjEquiv (TopCat.of X) _ T) ((stdSimplex.vertex (0:Fin 3) : stdSimplex ℝ (Fin 3))) =
 edgeSource ((TopCat.toSSet.obj (TopCat.of X)).δ 2 T) := by
  calc
    _ = (TopCat.toSSetObjEquiv (TopCat.of X) _ T) (cside 2 0) := by
      rw [show cside 2 0 = _ from (cpath (2:Fin 3)).source]
      rfl
    _ = _ := (edge_of_triangle T 2 0).symm.trans (edgePath _).source
lemma ev_v1a (T:S _⦋2⦌) :
 (TopCat.toSSetObjEquiv (TopCat.of X) _ T) ((stdSimplex.vertex (1:Fin 3) : stdSimplex ℝ (Fin 3))) =
 edgeTarget ((TopCat.toSSet.obj (TopCat.of X)).δ 2 T) := by
  calc
    _ = (TopCat.toSSetObjEquiv (TopCat.of X) _ T) (cside 2 1) := by
      rw [show cside 2 1 = _ from (cpath (2:Fin 3)).target]
      rfl
    _ = _ := (edge_of_triangle T 2 1).symm.trans (edgePath _).target
lemma ev_v1b (T:S _⦋2⦌) :
 (TopCat.toSSetObjEquiv (TopCat.of X) _ T) ((stdSimplex.vertex (1:Fin 3) : stdSimplex ℝ (Fin 3))) =
 edgeSource ((TopCat.toSSet.obj (TopCat.of X)).δ 0 T) := by
  calc
    _ = (TopCat.toSSetObjEquiv (TopCat.of X) _ T) (cside 0 0) := by
      rw [show cside 0 0 = _ from (cpath (0:Fin 3)).source]
      rfl
    _ = _ := (edge_of_triangle T 0 0).symm.trans (edgePath _).source
lemma ev_v2 (T:S _⦋2⦌) :
 (TopCat.toSSetObjEquiv (TopCat.of X) _ T) ((stdSimplex.vertex (2:Fin 3) : stdSimplex ℝ (Fin 3))) =
 edgeTarget ((TopCat.toSSet.obj (TopCat.of X)).δ 0 T) := by
  calc
    _ = (TopCat.toSSetObjEquiv (TopCat.of X) _ T) (cside 0 1) := by
      rw [show cside 0 1 = _ from (cpath (0:Fin 3)).target]
      rfl
    _ = _ := (edge_of_triangle T 0 1).symm.trans (edgePath _).target
end HurewiczSupport
namespace HurewiczSupport
open CategoryTheory AlgebraicTopology Simplicial unitInterval
variable {X:Type} [TopologicalSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)
noncomputable def ft (T:S _⦋2⦌) : C(stdSimplex ℝ (Fin 3), X) :=
 TopCat.toSSetObjEquiv (TopCat.of X) _ T
lemma ev_v0d (T:S _⦋2⦌) : ft T (stdSimplex.vertex (0:Fin 3)) =
 edgeSource ((TopCat.toSSet.obj (TopCat.of X)).δ 1 T) := by
  calc
   _ = ft T (cside 1 0) := by rw [show cside 1 0 = _ from (cpath (1:Fin 3)).source];rfl
   _ = _ := (edge_of_triangle T 1 0).symm.trans (edgePath _).source
lemma ev_v2d (T:S _⦋2⦌) : ft T (stdSimplex.vertex (2:Fin 3)) =
 edgeTarget ((TopCat.toSSet.obj (TopCat.of X)).δ 1 T) := by
  calc
   _ = ft T (cside 1 1) := by rw [show cside 1 1 = _ from (cpath (1:Fin 3)).target];rfl
   _ = _ := (edge_of_triangle T 1 1).symm.trans (edgePath _).target
noncomputable def ep (T:S _⦋2⦌) (i:Fin 3) := edgePath ((TopCat.toSSet.obj (TopCat.of X)).δ i T)
-- cast the three sides to exact vertex images
noncomputable def pp2 (T:S _⦋2⦌) : Path (ft T (stdSimplex.vertex (0:Fin 3))) (ft T (stdSimplex.vertex (1:Fin 3))) :=
 (ep T 2).cast (ev_v0 T) (ev_v1a T)
noncomputable def pp0 (T:S _⦋2⦌) : Path (ft T (stdSimplex.vertex (1:Fin 3))) (ft T (stdSimplex.vertex (2:Fin 3))) :=
 (ep T 0).cast (ev_v1b T) (ev_v2 T)
noncomputable def pp1 (T:S _⦋2⦌) : Path (ft T (stdSimplex.vertex (0:Fin 3))) (ft T (stdSimplex.vertex (2:Fin 3))) :=
 (ep T 1).cast (ev_v0d T) (ev_v2d T)
lemma pp_eq (T:S _⦋2⦌) (i:Fin 3) :
 (cpath i).map (ft T).continuous =
  (ep T i).cast
    (by fin_cases i; exact ev_v1b T; exact ev_v0d T; exact ev_v0 T)
    (by fin_cases i; exact ev_v2 T; exact ev_v2d T; exact ev_v1a T) := by
  ext t
  -- cast does not change the function
  exact (edge_of_triangle T i t).symm
noncomputable def triangle_hom (T:S _⦋2⦌) :
 ((pp2 T).trans (pp0 T)).Homotopy (pp1 T) := by
  have F := (simplexHom.map (ft T))
  have e2 : cp2.map (ft T).continuous = pp2 T := pp_eq T 2
  have e0 : cp0.map (ft T).continuous = pp0 T := pp_eq T 0
  have e1 : cp1.map (ft T).continuous = pp1 T := pp_eq T 1
  have eb : broken.map (ft T).continuous =
      (cp2.map (ft T).continuous).trans (cp0.map (ft T).continuous) := by
    exact Path.map_trans _ _ _
  exact F.cast (eb.trans (congrArg₂ Path.trans e2 e0)) e1

end HurewiczSupport
namespace HurewiczSupport
open CategoryTheory AlgebraicTopology Simplicial unitInterval
-- arrow cancellation calculus
lemma arrow_calc {Y:Type} [TopologicalSpace Y] {x u v w:Y}
 (cu : Path.Homotopic.Quotient x u) (cv : Path.Homotopic.Quotient x v)
 (cw : Path.Homotopic.Quotient x w)
 (p : Path.Homotopic.Quotient u v) (q: Path.Homotopic.Quotient v w)
 (r: Path.Homotopic.Quotient u w) (h : p.trans q = r) :
 (((cu.trans p).trans cv.symm).trans ((cv.trans q).trans cw.symm)) =
   (cu.trans r).trans cw.symm := by
  rw [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc cv.symm]
  rw [← Path.Homotopic.Quotient.trans_assoc cv.symm cv q]
  rw [Path.Homotopic.Quotient.symm_trans]
  rw [Path.Homotopic.Quotient.refl_trans]
  rw [Path.Homotopic.Quotient.trans_assoc cu p (q.trans cw.symm)]
  rw [← Path.Homotopic.Quotient.trans_assoc p q cw.symm]
  rw [h]
  rw [← Path.Homotopic.Quotient.trans_assoc]
end HurewiczSupport
namespace HurewiczSupport
open CategoryTheory AlgebraicTopology Simplicial unitInterval
variable {X:Type} [TopologicalSpace X] [PathConnectedSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)
noncomputable def face (T:S _⦋2⦌) (i:Fin 3) : S _⦋1⦌ := (TopCat.toSSet.obj (TopCat.of X)).δ i T
noncomputable def cu (x:X) (T:S _⦋2⦌) : Path x (ft T (stdSimplex.vertex (0:Fin 3))) :=
 (connector x (edgeSource (face T 2))).cast rfl (ev_v0 T)
noncomputable def cv (x:X) (T:S _⦋2⦌) : Path x (ft T (stdSimplex.vertex (1:Fin 3))) :=
 (connector x (edgeTarget (face T 2))).cast rfl (ev_v1a T)
noncomputable def cw (x:X) (T:S _⦋2⦌) : Path x (ft T (stdSimplex.vertex (2:Fin 3))) :=
 (connector x (edgeTarget (face T 0))).cast rfl (ev_v2 T)
-- the literal based paths agree after the harmless endpoint casts
lemma based2 (x:X) (T:S _⦋2⦌) : basedEdge x (face T 2) =
   ((cu x T).trans (pp2 T)).trans (cv x T).symm := by
  ext t
  rfl
lemma based0 (x:X) (T:S _⦋2⦌) : basedEdge x (face T 0) =
   ((cv x T).trans (pp0 T)).trans (cw x T).symm := by
  have hc : (connector x (edgeSource (face T 0))).cast rfl (ev_v1b T) = cv x T := by
    ext t
    exact congrArg (fun y : X => (connector x y) t) ((ev_v1a T).symm.trans (ev_v1b T)).symm
  rw [← hc]
  ext t
  rfl
lemma based1 (x:X) (T:S _⦋2⦌) : basedEdge x (face T 1) =
   ((cu x T).trans (pp1 T)).trans (cw x T).symm := by
  have hc : (connector x (edgeSource (face T 1))).cast rfl (ev_v0d T) = cu x T := by
    ext t
    exact congrArg (fun y : X => (connector x y) t) ((ev_v0 T).symm.trans (ev_v0d T)).symm
  have hd : (connector x (edgeTarget (face T 1))).cast rfl (ev_v2d T) = cw x T := by
    ext t
    exact congrArg (fun y : X => (connector x y) t) ((ev_v2 T).symm.trans (ev_v2d T)).symm
  rw [← hc, ← hd]
  ext t
  rfl

end HurewiczSupport
namespace HurewiczSupport
open CategoryTheory AlgebraicTopology Simplicial unitInterval
variable {X:Type} [TopologicalSpace X] [PathConnectedSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)
open Path.Homotopic
lemma loops_triangle (x:X) (T:S _⦋2⦌) :
 (Path.Homotopic.Quotient.mk (basedEdge x (face T 2))).trans
  (Path.Homotopic.Quotient.mk (basedEdge x (face T 0))) =
 Path.Homotopic.Quotient.mk (basedEdge x (face T 1)) := by
  have hp : (Path.Homotopic.Quotient.mk (pp2 T)).trans
      (Path.Homotopic.Quotient.mk (pp0 T)) =
       Path.Homotopic.Quotient.mk (pp1 T) := by
    rw [← Path.Homotopic.Quotient.mk_trans]
    exact Path.Homotopic.Quotient.eq.mpr ⟨triangle_hom T⟩
  -- expand the based loops
  rw [based2 x T, based0 x T, based1 x T]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  exact arrow_calc _ _ _ _ _ _ hp
lemma pre_triangle (x:X) (T:S _⦋2⦌) :
 edgePre x (face T 2) + edgePre x (face T 0) = edgePre x (face T 1) := by
  -- turn the preceding arrow equality into equality in the fundamental group
  have hl := loops_triangle x T
  -- `End` multiplication is reverse composition
  let g (i:Fin 3) : FundamentalGroup X x :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (basedEdge x (face T i)))
  have hg : g 0 * g 2 = g 1 := by
    exact hl
  change Abelianization.of (g 2) * Abelianization.of (g 0) = Abelianization.of (g 1)
  rw [mul_comm]
  rw [← map_mul, hg]
end HurewiczSupport
namespace HurewiczSupport
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial unitInterval
variable {X:Type} [TopologicalSpace X] [PathConnectedSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)
theorem pre_boundary_zero (x:X) (c:(K X).X 2) :
 evalChain (X:=X) 1 (edgePre x) ((K X).d 2 1 c) = 0 := by
  let l : ((K X).X 2 : Type) →+ Additive (Abelianization (FundamentalGroup X x)) :=
    (evalChain (X:=X) 1 (edgePre x)).comp ((K X).d 2 1).hom
  have hz : l = 0 := by
    apply eval_ext
    intro T
    change evalChain (X:=X) 1 (edgePre x) ((K X).d 2 1 (chainGen T)) = _
    rw [boundary_chainGen (m:=1)]
    simp [Fin.sum_univ_succ, evalChain_gen]
    have h := pre_triangle x T
    change edgePre x (face T 2) + edgePre x (face T 0) = edgePre x (face T 1) at h
    change _ = (0 : Additive (Abelianization (FundamentalGroup X x)))
    -- alternating boundary
    dsimp [face] at h ⊢
    abel_nf at h ⊢
    simpa [sub_eq_add_neg, add_assoc] using (sub_eq_zero.mpr h)
  exact DFunLike.congr_fun hz c
end HurewiczSupport

end

end
-- END INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/Triangles.lean

-- BEGIN INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/Inverse.lean
section

/-!
The morphism in the other direction.  Evaluating a chain on the based edges
(only in the abelianisation) is particularly convenient here: the little
triangle computation in `Triangles` says exactly that this evaluation is
zero on the image of `C₂`.  It therefore descends to homology.  On a based
loop the two joining paths are constant, so the descended map recovers the
original element of the abelianised fundamental group.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial unitInterval
open HurewiczSupport
noncomputable section
namespace HurewiczSupport
variable {X : Type} [TopologicalSpace X]
local notation "S" => TopCat.toSSet.obj (TopCat.of X)

-- The elementary endpoint facts are useful because the endpoints of
-- `edgePath` are written using the face maps of an edge.
@[simp] lemma edgeSource_pathSimplex {u v : X} (p : Path u v) :
    edgeSource (pathSimplex p) = u := by
  simp [edgeSource]

@[simp] lemma edgeTarget_pathSimplex {u v : X} (p : Path u v) :
    edgeTarget (pathSimplex p) = v := by
  simp [edgeTarget]

-- The casts here are the direction accepted by `Path.cast` (`new = old`).
lemma edgePath_pathSimplex_cast {u v : X} (p : Path u v) :
    (edgePath (pathSimplex p)).cast
        ((edgeSource_pathSimplex p).symm)
        ((edgeTarget_pathSimplex p).symm) = p := by
  ext t
  rfl

variable [PathConnectedSpace X]

/-- For an edge coming from a loop at the basepoint its *based* edge is the
same loop, in the path groupoid.  It is generally not the same literal path:
`Path.trans` puts pauses into it. -/
lemma mk_basedEdge_pathSimplex {x : X} (p : Path x x) :
    Path.Homotopic.Quotient.mk (basedEdge x (pathSimplex p)) =
      Path.Homotopic.Quotient.mk p := by
  -- First put all three pieces over the same endpoints.  Casts do not change
  -- the underlying functions, which makes the comparison with `basedEdge`
  -- literal below.
  let q0 : Path x x :=
    (connector x (edgeSource (pathSimplex p))).cast rfl
      ((edgeSource_pathSimplex p).symm)
  let q1 : Path x x :=
    (connector x (edgeTarget (pathSimplex p))).cast rfl
      ((edgeTarget_pathSimplex p).symm)
  let mid : Path x x :=
    (edgePath (pathSimplex p)).cast
      ((edgeSource_pathSimplex p).symm)
      ((edgeTarget_pathSimplex p).symm)
  have hq0 : q0 = Path.refl x := by
    ext t
    change (connector x (edgeSource (pathSimplex p))) t = _
    rw [edgeSource_pathSimplex p]
    simp
  have hq1 : q1 = Path.refl x := by
    ext t
    change (connector x (edgeTarget (pathSimplex p))) t = _
    rw [edgeTarget_pathSimplex p]
    simp
  have hm : mid = p := edgePath_pathSimplex_cast p
  have hb : basedEdge x (pathSimplex p) =
        (q0.trans mid).trans q1.symm := by
    ext t
    rfl
  rw [hb]
  rw [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm]
  rw [hq0, hq1, hm]
  have hr : (Path.Homotopic.Quotient.refl x).symm =
      Path.Homotopic.Quotient.refl x := by
    rfl
  change
    ((Path.Homotopic.Quotient.refl x).trans
        (Path.Homotopic.Quotient.mk p)).trans
          (Path.Homotopic.Quotient.refl x).symm = _
  rw [hr, Path.Homotopic.Quotient.trans_refl,
      Path.Homotopic.Quotient.refl_trans]

/-- Evaluation by based edges, now as a map *out* of `H₁`.  This differs
from the use of `edgePre` for surjectivity: here we use exactly the fact that
triangle boundaries evaluate to zero. -/
noncomputable def h1Pre (x : X) :
    H1Quot X →+ Additive (Abelianization (FundamentalGroup X x)) := by
  let f : AddMonoidHom.ker (scX X).g.hom →+
        Additive (Abelianization (FundamentalGroup X x)) :=
    (evalChain (X:=X) 1 (edgePre x)).comp (AddSubgroup.subtype _)
  exact QuotientAddGroup.lift _ f (by
    rintro z hz
    rcases hz with ⟨c, rfl⟩
    -- As a one-chain this is simply the boundary of `c`.
    change
      evalChain (X:=X) 1 (edgePre x) ((K X).d 2 1 c) = 0
    exact pre_boundary_zero x c)

@[simp] lemma h1Pre_mk (x : X) (z : AddMonoidHom.ker (scX X).g.hom) :
    h1Pre x (QuotientAddGroup.mk' _ z) =
      evalChain (X:=X) 1 (edgePre x) z.1 := by
  rfl

@[simp] lemma h1Pre_loop {x : X} (p : Path x x) :
    h1Pre x (loopClass x p) =
      Additive.ofMul
        (Abelianization.of
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) := by
  rw [loopClass]
  rw [h1Pre_mk]
  simp [loopCycle, evalChain_gen, edgePre]
  rw [mk_basedEdge_pathSimplex p]

/-- On the image of the loop map the preceding evaluation is a left
inverse.  To check it on every element of the abelianisation one only has to
do the two quotient inductions: first that every element of a quotient group
comes from an element, then that an arrow of the fundamental groupoid has a
path representative. -/
theorem h1Pre_left (x : X)
    (a : Additive (Abelianization (FundamentalGroup X x))) :
    h1Pre x (additiveAbPi1H1Hom x a) = a := by
  cases a with
  | ofMul a =>
    induction a using QuotientGroup.induction_on with
    | _ g =>
      change
        h1Pre x
          (additiveAbPi1H1Hom x
            (Additive.ofMul (Abelianization.of g))) =
          Additive.ofMul (Abelianization.of g)
      induction g using Path.Homotopic.Quotient.ind with
      | mk p =>
        rw [additiveAbPi1H1Hom_of]
        exact h1Pre_loop p

/-- Consequently the map from the abelianised fundamental group to `H1Quot`
is injective. -/
theorem additiveAb_injective (x : X) :
    Function.Injective (additiveAbPi1H1Hom (X:=X) x) := by
  intro a b h
  calc
    a = h1Pre x (additiveAbPi1H1Hom x a) := (h1Pre_left x a).symm
    _ = h1Pre x (additiveAbPi1H1Hom x b) := congrArg (fun t => h1Pre x t) h
    _ = b := h1Pre_left x b

end HurewiczSupport

end

end
-- END INLINED FILE: Mathlib/Support/hurewicz_h1_abelianization_1f69f77ba4/Inverse.lean

-- BEGIN INLINED MAIN PRELUDE


open LeanEval.Topology.Hurewicz
open CategoryTheory AlgebraicTopology
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem hurewicz_h1_abelianization (X : Type) [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Nonempty (Additive (Abelianization (FundamentalGroup X x)) ≃+
      (IntegralHomology 1 X : Type)) :=
/-ResultProofBegin-/ by
  -- Convert singular homology to cycles modulo boundaries; this part is the
  -- standard short-complex presentation and is completely independent of
  -- paths.  In that presentation there is a concrete based-loop
  -- homomorphism.  Its well-definedness on `π₁` (including the reversal in
  -- `End` multiplication) and its factorisation through `Abelianization`
  -- are in `Pi1Map`.
  suffices hsurinj : Function.Bijective
       (HurewiczSupport.additiveAbPi1H1Hom (X:=X) x) by
    let e : Additive (Abelianization (FundamentalGroup X x)) ≃+
        HurewiczSupport.H1Quot X :=
      AddEquiv.ofBijective
        (HurewiczSupport.additiveAbPi1H1Hom (X:=X) x) hsurinj
    exact ⟨e.trans (HurewiczSupport.integralHomologyOneEquiv X).symm⟩
  -- The edge-cycle half is now proved: coproduct evaluation of chains,
  -- cancellation of connector paths using the degree-zero boundary, gives
  -- an explicit preimage of every cycle; see `additiveAb_surjective`.
  -- It remains the triangle/van Kampen (injectivity) half.
  refine ⟨?_, HurewiczSupport.additiveAb_surjective (X:=X) x⟩
  -- Injectivity is exactly the remaining triangle presentation.  Surjectivity
  -- above used only one-chains and the zero boundary equation, hence is
  -- independent of this step.
  exact HurewiczSupport.additiveAb_injective (X:=X) x
  /-ResultProofEnd-/
/-ResultEnd-/

end Submission
