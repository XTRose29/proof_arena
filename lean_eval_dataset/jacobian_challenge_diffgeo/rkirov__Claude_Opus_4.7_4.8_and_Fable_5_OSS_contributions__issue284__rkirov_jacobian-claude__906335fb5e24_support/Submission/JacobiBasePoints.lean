/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Forster Lemma 21.3 — base points for the Jacobi map

On a compact Riemann surface of genus `g` there are `g` distinct points `a 0, …, a (g-1)` such
that the only holomorphic 1-form vanishing at all of them is `0`.  Consequently the `g × g`
**evaluation matrix** `A i j = (coefficient of ω_i in the chart at a j)` of the period basis
forms is invertible — the Jacobian matrix of the local Jacobi map `F` of Forster 21.4(a).

The proof is Forster's: for `a : X` the evaluation functional `formEvalSelf a`
(`α ↦ localRep α a a`, the chart-centre coefficient) has kernel `H_a` of codimension `0` or `1`
in the `g`-dimensional `Ω(X) = HolomorphicOneForms X`; since a nonzero form has a nonzero
coefficient somewhere (`exists_localRep_self_ne_zero`), one can pick points dropping the
dimension of `H_{a_1} ∩ ⋯ ∩ H_{a_k}` by exactly one each step.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), Lemma 21.3 (p. 168).
-/
import Submission.SmoothPathCore
import Submission.Dolbeault.FormCoeff

open scoped Manifold ContDiff
open Module

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The chart-centre evaluation functional -/

/-- **Evaluation of a holomorphic 1-form at a point**, as a `ℂ`-linear functional: the chart-centre
coefficient `localRep α a a` (the value of `α` at `a` on the unit coordinate tangent vector of the
chart at `a`).  Its vanishing is the chart-invariant meaning of "`α(a) = 0`" (the tangent fibre is
1-dimensional). -/
noncomputable def formEvalSelf (a : X) : HolomorphicOneForms X →ₗ[ℂ] ℂ where
  toFun α := Jacobians.Montel.localRep α a a
  map_add' α β := Jacobians.Montel.localRep_add α β a a
  map_smul' c α := Jacobians.Montel.localRep_smul c α a a

@[simp] theorem formEvalSelf_apply (a : X) (α : HolomorphicOneForms X) :
    formEvalSelf a α = Jacobians.Montel.localRep α a a := rfl

/-! ### The codimension-one drop -/

/-- **One-step kernel drop.**  If some `α ∈ V` has `formEvalSelf a α ≠ 0`, then cutting `V` by the
kernel of the evaluation at `a` drops the dimension by exactly one (rank–nullity for the restricted
functional, whose range is all of `ℂ`). -/
theorem finrank_inf_ker_formEvalSelf (V : Submodule ℂ (HolomorphicOneForms X))
    {α : HolomorphicOneForms X} (hωV : α ∈ V) {a : X} (hωa : formEvalSelf a α ≠ 0) :
    finrank ℂ ↥(V ⊓ LinearMap.ker (formEvalSelf (X := X) a))
      = finrank ℂ ↥V - 1 := by
  classical
  set ψ : ↥V →ₗ[ℂ] ℂ := (formEvalSelf (X := X) a).comp V.subtype with hψ
  -- ψ is surjective: it hits the nonzero value `formEvalSelf a α`.
  have hsurj : Function.Surjective ψ := by
    intro c
    refine ⟨(c / formEvalSelf a α) • ⟨α, hωV⟩, ?_⟩
    show (formEvalSelf a) (V.subtype ((c / formEvalSelf a α) • ⟨α, hωV⟩)) = c
    rw [map_smul, map_smul, smul_eq_mul]
    show c / formEvalSelf a α * formEvalSelf a α = c
    field_simp
  -- rank–nullity: finrank (range ψ) + finrank (ker ψ) = finrank V, with range = ⊤ (dim 1).
  have hrn := ψ.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hrn
  -- identify ker ψ with V ⊓ ker (formEvalSelf a) inside V.
  have hker : LinearMap.ker ψ
      = (V ⊓ LinearMap.ker (formEvalSelf (X := X) a)).comap V.subtype := by
    rw [hψ, LinearMap.ker_comp, Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  have hequiv := (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : V ⊓ LinearMap.ker (formEvalSelf (X := X) a) ≤ V)).finrank_eq
  rw [hker, hequiv] at hrn
  omega

/-! ### Forster 21.3: the base-point induction -/

/-- **The induction core**: for every `k ≤ g` there is a `k`-element set of points whose common
evaluation kernel has dimension exactly `g − k`. -/
theorem exists_finset_formEvalSelf_ker (k : ℕ) (hk : k ≤ genus X) :
    ∃ s : Finset X, s.card = k ∧
      finrank ℂ ↥(⨅ a ∈ s, LinearMap.ker (formEvalSelf (X := X) a)) = genus X - k := by
  classical
  induction k with
  | zero =>
    refine ⟨∅, Finset.card_empty, ?_⟩
    rw [show (⨅ a ∈ (∅ : Finset X), LinearMap.ker (formEvalSelf (X := X) a)) = ⊤ by simp,
      finrank_top]
    exact (finrank_HolomorphicOneForms_eq_genus X).trans (by omega)
  | succ n ih =>
    obtain ⟨s, hcard, hdim⟩ := ih (by omega)
    set V : Submodule ℂ (HolomorphicOneForms X) :=
      ⨅ a ∈ s, LinearMap.ker (formEvalSelf (X := X) a) with hV
    -- V is nonzero (its dimension is g − n ≥ 1), so pick 0 ≠ α ∈ V.
    have hVne : V ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hdim
      omega
    obtain ⟨α, hωV, hωne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
    -- α has a nonzero coefficient at some point a'.
    obtain ⟨a', ha'⟩ := Jacobians.Dolbeault.exists_localRep_self_ne_zero α hωne
    have ha'eval : formEvalSelf a' α ≠ 0 := ha'
    -- a' is new: α vanishes at every point of s.
    have ha'new : a' ∉ s := by
      intro hmem
      exact ha'eval (by
        have : V ≤ LinearMap.ker (formEvalSelf (X := X) a') := biInf_le _ hmem
        exact this hωV)
    refine ⟨insert a' s, by rw [Finset.card_insert_of_notMem ha'new, hcard], ?_⟩
    rw [Finset.iInf_insert, inf_comm, ← hV,
      finrank_inf_ker_formEvalSelf V hωV ha'eval, hdim]
    omega

/-- **Forster Lemma 21.3.**  There are `g` distinct points `a j` on `X` such that the only
holomorphic 1-form whose coefficient vanishes at all of them is the zero form. -/
theorem exists_jacobiBasePoints :
    ∃ a : Fin (genus X) → X, Function.Injective a ∧
      ∀ α : HolomorphicOneForms X,
        (∀ j, Jacobians.Montel.localRep α (a j) (a j) = 0) → α = 0 := by
  classical
  obtain ⟨s, hcard, hdim⟩ := exists_finset_formEvalSelf_ker (X := X) (genus X) le_rfl
  rw [Nat.sub_self] at hdim
  -- index the set by Fin g
  have hequiv : Fin (genus X) ≃ ↥s := (s.equivFin.trans (finCongr hcard)).symm
  refine ⟨fun j => (hequiv j : X), ?_, ?_⟩
  · exact fun j₁ j₂ h => hequiv.injective (Subtype.ext h)
  · intro α hα
    have hmem : α ∈ ⨅ a ∈ s, LinearMap.ker (formEvalSelf (X := X) a) := by
      rw [Submodule.mem_iInf]
      intro b
      rw [Submodule.mem_iInf]
      intro hb
      have h := hα (hequiv.symm ⟨b, hb⟩)
      simp only [Equiv.apply_symm_apply] at h
      rw [LinearMap.mem_ker, formEvalSelf_apply]
      exact h
    have hbot : (⨅ a ∈ s, LinearMap.ker (formEvalSelf (X := X) a)) = ⊥ :=
      Submodule.finrank_eq_zero.mp hdim
    rw [hbot] at hmem
    exact hmem

/-! ### The evaluation matrix of the period basis and its invertibility -/

/-- The `g × g` **evaluation matrix** of the period basis forms at a point family:
`A i j` = chart-centre coefficient of `periodBasisForm X i` at `a j`.  This is the Jacobian
matrix of Forster 21.4(a)'s local Jacobi map at the base point. -/
noncomputable def jacobiEvalMatrix (a : Fin (genus X) → X) :
    Matrix (Fin (genus X)) (Fin (genus X)) ℂ :=
  Matrix.of fun i j => Jacobians.Montel.localRep (periodBasisForm X i) (a j) (a j)

@[simp] theorem jacobiEvalMatrix_apply (a : Fin (genus X) → X) (i j : Fin (genus X)) :
    jacobiEvalMatrix a i j = Jacobians.Montel.localRep (periodBasisForm X i) (a j) (a j) := rfl

/-- **Rank `g` of the evaluation matrix** (Forster 21.4(a)): at a family of base points with the
21.3 property, the evaluation matrix of the period basis is invertible (`det ≠ 0`).  A nonzero
left null vector `v` would make `α = ∑ v i • ω_i = ambientIso X v` a nonzero form vanishing at
every `a j`. -/
theorem jacobiEvalMatrix_det_ne_zero {a : Fin (genus X) → X}
    (ha : ∀ α : HolomorphicOneForms X,
      (∀ j, Jacobians.Montel.localRep α (a j) (a j) = 0) → α = 0) :
    (jacobiEvalMatrix a).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  -- the form with coefficient vector v
  set α : HolomorphicOneForms X := ambientIso X v with hω
  have hωeval : ∀ j, Jacobians.Montel.localRep α (a j) (a j) = 0 := by
    intro j
    have hsum : α = ∑ i, v i • periodBasisForm X i := by
      have hv' : (∑ i, v i • Pi.basisFun ℂ (Fin (genus X)) i) = v := by
        ext k
        simp [Pi.basisFun_apply, Pi.single_apply, Finset.sum_ite_eq]
      calc α = ambientIso X v := hω
        _ = ambientIso X (∑ i, v i • Pi.basisFun ℂ (Fin (genus X)) i) := by rw [hv']
        _ = ∑ i, v i • periodBasisForm X i := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
    have := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    calc Jacobians.Montel.localRep α (a j) (a j)
        = formEvalSelf (a j) α := rfl
      _ = ∑ i, v i * formEvalSelf (a j) (periodBasisForm X i) := by
          rw [hsum, map_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
      _ = 0 := this
  have : α = 0 := ha α hωeval
  exact hvne ((ambientIso X).map_eq_zero_iff.mp (hω ▸ this))

/-- **Forster 21.3 + 21.4(a) rank statement, packaged**: a family of `g` distinct base points at
which the period-basis evaluation matrix is invertible. -/
theorem exists_jacobiBasePoints_det_ne_zero :
    ∃ a : Fin (genus X) → X, Function.Injective a ∧
      (jacobiEvalMatrix (X := X) a).det ≠ 0 := by
  obtain ⟨a, hinj, ha⟩ := exists_jacobiBasePoints (X := X)
  exact ⟨a, hinj, jacobiEvalMatrix_det_ne_zero ha⟩

end Jacobians
