import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Matrix.BilinearForm

open LeanEval.Geometry.Darboux
open Set Function Matrix Module

namespace Submission.LinearNormal

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The bilinear form underlying a continuous alternating two-form. -/
def toBilin (ω : V [⋀^Fin 2]→L[ℝ] ℝ) : LinearMap.BilinForm ℝ V where
  toFun v := ((ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)).symm
    (ω.curryLeft v)).toLinearMap
  map_add' := by
    intro x y
    ext z
    simp
  map_smul' := by
    intro c x
    ext z
    simp

@[simp]
theorem toBilin_apply (ω : V [⋀^Fin 2]→L[ℝ] ℝ) (v w : V) :
    toBilin ω v w = ω ![v, w] := by
  have htail : (fun _ : Fin 1 => w) = ![w] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  change ω (Matrix.vecCons v fun _ : Fin 1 => w) = ω (Matrix.vecCons v ![w])
  rw [htail]

theorem toBilin_isAlt (ω : V [⋀^Fin 2]→L[ℝ] ℝ) : (toBilin ω).IsAlt := by
  intro v
  rw [toBilin_apply]
  exact ω.map_eq_zero_of_eq ![v, v] (by simp) Fin.zero_ne_one

theorem toBilin_nondegenerate [FiniteDimensional ℝ V]
    (ω : V [⋀^Fin 2]→L[ℝ] ℝ)
    (hω : ∀ v : V, v ≠ 0 → ∃ w : V, ω ![v, w] ≠ 0) :
    (toBilin ω).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro v hv
  by_contra hv0
  obtain ⟨w, hw⟩ := hω v hv0
  apply hw
  rw [← toBilin_apply]
  exact hv w

structure SymplecticFrame (B : LinearMap.BilinForm ℝ V) (n : ℕ) where
  p : Fin n → V
  q : Fin n → V
  pair_pq : ∀ i j, B (p i) (q j) = if i = j then 1 else 0
  pair_pp : ∀ i j, B (p i) (p j) = 0
  pair_qq : ∀ i j, B (q i) (q j) = 0
  spans : ⊤ ≤ Submodule.span ℝ (Set.range (Sum.elim p q))

variable {B : LinearMap.BilinForm ℝ V}

private theorem plane_restrict_nondegenerate [FiniteDimensional ℝ V]
    (hAlt : B.IsAlt) {v q : V} (hvq : B v q = 1) :
    (B.restrict (Submodule.span ℝ ({v, q} : Set V))).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro u hu
  apply Subtype.ext
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp u.property
  have hq := hu
    (⟨q, Submodule.subset_span (by simp)⟩ : Submodule.span ℝ ({v, q} : Set V))
  have hv := hu
    (⟨v, Submodule.subset_span (by simp)⟩ : Submodule.span ℝ ({v, q} : Set V))
  have ha : a = 0 := by
    simpa [LinearMap.BilinForm.restrict_apply, ← hab, hvq, hAlt.self_eq_zero] using hq
  have hb : b = 0 := by
    have hqv : B q v = -1 := by
      rw [← hAlt.neg_eq v q, hvq]
    simpa [LinearMap.BilinForm.restrict_apply, ← hab, hAlt.self_eq_zero, hqv] using hv
  rw [← hab, ha, hb]
  simp

theorem exists_symplecticFrame :
    ∀ n : ℕ, ∀ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V),
      B.IsAlt → B.Nondegenerate → Module.finrank ℝ V = 2 * n →
        Nonempty (SymplecticFrame B n) := by
  intro n
  induction n with
  | zero =>
      intro V _ _ _ B _ _ hfin
      refine ⟨{
        p := Fin.elim0
        q := Fin.elim0
        pair_pq := fun i => Fin.elim0 i
        pair_pp := fun i => Fin.elim0 i
        pair_qq := fun i => Fin.elim0 i
        spans := ?_ }⟩
      intro v _
      have hv : v = 0 := finrank_zero_iff_forall_zero.mp (by simpa using hfin) v
      simp [hv]
  | succ n ih =>
      intro V _ _ _ B hAlt hB hfin
      letI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hfin]; omega)
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have hnot : ¬∀ w : V, B v w = 0 := fun h => hv (hB.1 v h)
      push Not at hnot
      obtain ⟨w, hw⟩ := hnot
      let q : V := (B v w)⁻¹ • w
      have hvq : B v q = 1 := by simp [q, hw]
      let P : Submodule ℝ V := Submodule.span ℝ ({v, q} : Set V)
      let W : Submodule ℝ V := B.orthogonal P
      have hP : (B.restrict P).Nondegenerate := by
        simpa [P] using plane_restrict_nondegenerate hAlt hvq
      have hcomp : IsCompl P W := by
        simpa [W] using B.isCompl_orthogonal_of_restrict_nondegenerate hAlt.isRefl hP
      have hWAlt : (B.restrict W).IsAlt := fun z => hAlt z
      have hWNondeg : (B.restrict W).Nondegenerate := by
        apply B.nondegenerate_restrict_of_disjoint_orthogonal hAlt.isRefl
        have horth : B.orthogonal W = P := by
          simpa [W] using B.orthogonal_orthogonal hB hAlt.isRefl P
        rw [horth]
        exact hcomp.symm.disjoint
      have hpLin : LinearIndependent ℝ ![v, q] := by
        rw [LinearIndependent.pair_iff' hv]
        intro a ha
        have := congrArg (fun z => B v z) ha
        simp [hvq, hAlt.self_eq_zero] at this
      have hPfin : Module.finrank ℝ P = 2 := by
        have hrange : Set.range ![v, q] = ({v, q} : Set V) := by
          ext z
          simp [or_comm]
        rw [show P = Submodule.span ℝ ({v, q} : Set V) from rfl, ← hrange]
        simpa using (finrank_span_eq_card hpLin)
      have hWfin : Module.finrank ℝ W = 2 * n := by
        rw [B.finrank_orthogonal hB P, hfin, hPfin]
        omega
      obtain ⟨frame⟩ := ih (B.restrict W) hWAlt hWNondeg hWfin
      let p : Fin (n + 1) → V := Fin.cases v fun i => (frame.p i : V)
      let q' : Fin (n + 1) → V := Fin.cases q fun i => (frame.q i : V)
      refine ⟨{
        p := p
        q := q'
        pair_pq := ?_
        pair_pp := ?_
        pair_qq := ?_
        spans := ?_ }⟩
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
        · simpa [p, q'] using hvq
        · have h := (frame.q j).property v (Submodule.subset_span (by simp))
          have hne : (0 : Fin (n + 1)) ≠ j.succ := by
            intro heq
            have := congrArg Fin.val heq
            simp at this
          rw [if_neg hne]
          simpa [p, q', W] using h
        · have h := (frame.p i).property q (Submodule.subset_span (by simp))
          convert hAlt.eq_iff.mpr h using 1 <;> simp [p, q']
        · simpa [p, q'] using frame.pair_pq i j
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
        · simp [p, hAlt.self_eq_zero]
        · have h := (frame.p j).property v (Submodule.subset_span (by simp))
          simpa [p, W] using h
        · have h := (frame.p i).property v (Submodule.subset_span (by simp))
          simpa [p] using (hAlt.eq_iff.mpr h)
        · simpa [p] using frame.pair_pp i j
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
        · simp [q', hAlt.self_eq_zero]
        · have h := (frame.q j).property q (Submodule.subset_span (by simp))
          simpa [q', W] using h
        · have h := (frame.q i).property q (Submodule.subset_span (by simp))
          simpa [q'] using (hAlt.eq_iff.mpr h)
        · simpa [q'] using frame.pair_qq i j
      · let S := Submodule.span ℝ (Set.range (Sum.elim p q'))
        have hvS : v ∈ S := by
          apply Submodule.subset_span
          exact ⟨Sum.inl 0, by simp [p]⟩
        have hqS : q ∈ S := by
          apply Submodule.subset_span
          exact ⟨Sum.inr 0, by simp [q']⟩
        have hPS : P ≤ S := by
          apply Submodule.span_le.mpr
          simp only [Set.pair_subset_iff]
          exact ⟨hvS, hqS⟩
        have hWS : W ≤ S := by
          intro y hy
          let yW : W := ⟨y, hy⟩
          have hyspan : yW ∈ Submodule.span ℝ (Set.range (Sum.elim frame.p frame.q)) :=
            frame.spans Submodule.mem_top
          refine Submodule.span_induction (R := ℝ)
            (s := Set.range (Sum.elim frame.p frame.q)) (x := yW)
            (p := fun (z : W) _ => (z : V) ∈ S) ?_ S.zero_mem
            (fun _ _ _ _ hx hy => S.add_mem hx hy) (fun a _ _ hx => S.smul_mem a hx) hyspan
          intro z hz
          rcases hz with ⟨i, rfl⟩
          cases i with
          | inl i =>
              apply Submodule.subset_span
              exact ⟨Sum.inl i.succ, by simp [p]⟩
          | inr i =>
              apply Submodule.subset_span
              exact ⟨Sum.inr i.succ, by simp [q']⟩
        rw [← hcomp.sup_eq_top]
        exact sup_le hPS hWS

private def indexEquiv (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
  finSumFinEquiv.trans (finCongr (by omega))

@[simp]
private theorem indexEquiv_inl {n : ℕ} (i : Fin n) :
    indexEquiv n (Sum.inl i) = idxP i := by
  ext
  simp [indexEquiv, idxP]

@[simp]
private theorem indexEquiv_inr {n : ℕ} (i : Fin n) :
    indexEquiv n (Sum.inr i) = idxQ i := by
  ext
  simp [indexEquiv, idxQ, add_comm]

noncomputable def SymplecticFrame.toBasis [FiniteDimensional ℝ V]
    {n : ℕ} (frame : SymplecticFrame B n) (hfin : Module.finrank ℝ V = 2 * n) :
    Basis (Fin n ⊕ Fin n) ℝ V :=
  basisOfTopLeSpanOfCardEqFinrank (Sum.elim frame.p frame.q) frame.spans (by
    rw [hfin]
    simp
    omega)

@[simp]
theorem SymplecticFrame.toBasis_apply_inl [FiniteDimensional ℝ V]
    {n : ℕ} (frame : SymplecticFrame B n) (hfin : Module.finrank ℝ V = 2 * n)
    (i : Fin n) : frame.toBasis hfin (Sum.inl i) = frame.p i := by
  simp [SymplecticFrame.toBasis]

@[simp]
theorem SymplecticFrame.toBasis_apply_inr [FiniteDimensional ℝ V]
    {n : ℕ} (frame : SymplecticFrame B n) (hfin : Module.finrank ℝ V = 2 * n)
    (i : Fin n) : frame.toBasis hfin (Sum.inr i) = frame.q i := by
  simp [SymplecticFrame.toBasis]

noncomputable def SymplecticFrame.toContinuousLinearEquiv [FiniteDimensional ℝ V]
    {n : ℕ} (frame : SymplecticFrame B n) (hfin : Module.finrank ℝ V = 2 * n) :
    E n ≃L[ℝ] V :=
  let standard := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis
  let target := (frame.toBasis hfin).reindex (indexEquiv n)
  (standard.equiv target (Equiv.refl _)).toContinuousLinearEquiv

@[simp]
theorem SymplecticFrame.toContinuousLinearEquiv_single_idxP [FiniteDimensional ℝ V]
    {n : ℕ} (frame : SymplecticFrame B n) (hfin : Module.finrank ℝ V = 2 * n)
    (i : Fin n) :
    frame.toContinuousLinearEquiv hfin (EuclideanSpace.single (idxP i) 1) = frame.p i := by
  rw [← EuclideanSpace.basisFun_apply]
  change ((EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis.equiv
    ((frame.toBasis hfin).reindex (indexEquiv n)) (Equiv.refl _))
      ((EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis (idxP i)) = frame.p i
  rw [Basis.equiv_apply]
  rw [← indexEquiv_inl i]
  rw [Basis.reindex_apply, Equiv.refl_apply, Equiv.symm_apply_apply]
  exact frame.toBasis_apply_inl hfin i

@[simp]
theorem SymplecticFrame.toContinuousLinearEquiv_single_idxQ [FiniteDimensional ℝ V]
    {n : ℕ} (frame : SymplecticFrame B n) (hfin : Module.finrank ℝ V = 2 * n)
    (i : Fin n) :
    frame.toContinuousLinearEquiv hfin (EuclideanSpace.single (idxQ i) 1) = frame.q i := by
  rw [← EuclideanSpace.basisFun_apply]
  change ((EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis.equiv
    ((frame.toBasis hfin).reindex (indexEquiv n)) (Equiv.refl _))
      ((EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis (idxQ i)) = frame.q i
  rw [Basis.equiv_apply]
  rw [← indexEquiv_inr i]
  rw [Basis.reindex_apply, Equiv.refl_apply, Equiv.symm_apply_apply]
  exact frame.toBasis_apply_inr hfin i

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
private theorem comp_pair {W : Type*} (f : V → W) (x y : V) :
    f ∘ ![x, y] = ![f x, f y] := by
  funext i
  fin_cases i <;> rfl

theorem exists_linear_normal {n : ℕ} (ω : E n [⋀^Fin 2]→L[ℝ] ℝ)
    (hω : ∀ v : E n, v ≠ 0 → ∃ w : E n, ω ![v, w] ≠ 0) :
    ∃ e : E n ≃L[ℝ] E n,
      IsDarbouxNormal (ω.compContinuousLinearMap e.toContinuousLinearMap) := by
  let B := toBilin ω
  have hfin : Module.finrank ℝ (E n) = 2 * n := by simp [E]
  obtain ⟨frame⟩ := exists_symplecticFrame n B (toBilin_isAlt ω)
    (toBilin_nondegenerate ω hω) hfin
  let e := frame.toContinuousLinearEquiv hfin
  refine ⟨e, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [comp_pair]
    simpa [e, B, Function.comp_def] using frame.pair_pq i j
  · intro i j
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [comp_pair]
    simpa [e, B, Function.comp_def] using frame.pair_pp i j
  · intro i j
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [comp_pair]
    simpa [e, B, Function.comp_def] using frame.pair_qq i j

end

end Submission.LinearNormal
