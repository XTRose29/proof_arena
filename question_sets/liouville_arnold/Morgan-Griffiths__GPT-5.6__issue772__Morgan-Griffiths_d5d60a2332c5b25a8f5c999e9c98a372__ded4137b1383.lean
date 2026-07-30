import ChallengeDeps
import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Hamiltonian.lean
section

open scoped BigOperators
open Function
open Fintype

namespace LeanEval.Geometry.LiouvilleArnold.Support


noncomputable def hamVec {n : ℕ}
    (p q : Fin n → Fin (2*n))
    (l : (EuclideanSpace ℝ (Fin (2*n))) →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin (2*n)) :=
  ∑ i : Fin n,
    ((- l (EuclideanSpace.single (q i) (1 : ℝ))) •
          EuclideanSpace.single (p i) (1 : ℝ) +
      (l (EuclideanSpace.single (p i) (1 : ℝ))) •
          EuclideanSpace.single (q i) (1 : ℝ))


theorem apply_hamVec {n : ℕ}
    (p q : Fin n → Fin (2*n))
    (l m : (EuclideanSpace ℝ (Fin (2*n))) →L[ℝ] ℝ) :
    m (hamVec p q l) =
      ∑ i : Fin n,
        (l (EuclideanSpace.single (p i) (1 : ℝ)) *
            m (EuclideanSpace.single (q i) (1 : ℝ)) -
         l (EuclideanSpace.single (q i) (1 : ℝ)) *
            m (EuclideanSpace.single (p i) (1 : ℝ))) := by
  classical
  unfold hamVec
  simp_rw [map_sum, map_add, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp
  ring


theorem apply_hamVec_eq_zero_of_sum_eq_zero {n : ℕ}
    (p q : Fin n → Fin (2*n))
    (l m : (EuclideanSpace ℝ (Fin (2*n))) →L[ℝ] ℝ)
    (h : (∑ i : Fin n,
        (l (EuclideanSpace.single (p i) (1 : ℝ)) *
            m (EuclideanSpace.single (q i) (1 : ℝ)) -
         l (EuclideanSpace.single (q i) (1 : ℝ)) *
            m (EuclideanSpace.single (p i) (1 : ℝ)))) = 0) :
    m (hamVec p q l) = 0 := by
  rw [apply_hamVec]
  exact h


noncomputable def hamVecLM {n : ℕ}
    (p q : Fin n → Fin (2*n)) :
    (((EuclideanSpace ℝ (Fin (2*n))) →L[ℝ] ℝ) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (2*n))) where
  toFun l := hamVec p q l
  map_add' l m := by
    classical
    unfold hamVec
    simp only [map_add, add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp [neg_add, add_smul]
    abel
  map_smul' c l := by
    classical
    unfold hamVec
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [smul_add, mul_smul]

end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Hamiltonian.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/OrbitChartCore.lean
section
open Set Function Filter
open scoped Topology BigOperators
namespace LeanEval.Geometry.LiouvilleArnold.Support
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def coordCLM {m : ℕ} (w : Fin m → W) : (Fin m → ℝ) →L[ℝ] W :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (w i)

@[simp] theorem coordCLM_apply {m : ℕ} (w : Fin m → W) (u : Fin m → ℝ) :
    coordCLM w u = ∑ i, u i • w i := by
  simp [coordCLM]

 theorem continuous_coordCLM {m : ℕ} {X : Type*} [TopologicalSpace X] {w : Fin m → X → W}
    (h : ∀ i, Continuous (w i)) :
    Continuous (fun x => coordCLM (fun i => w i x)) := by
  unfold coordCLM
  apply continuous_finset_sum _
  intro i hi
  let T : W →L[ℝ] ((Fin m → ℝ) →L[ℝ] W) :=
    (ContinuousLinearMap.smulRightL ℝ (Fin m → ℝ) W) (ContinuousLinearMap.proj i)
  exact (T.continuous.comp (h i))

 theorem hasStrictFDerivAt_pi_of_partials :
  ∀ m : ℕ, ∀ (g : (Fin m → ℝ) → W) (w : Fin m → (Fin m → ℝ) → W),
    (∀ i, Continuous (w i)) →
    (∀ i x, HasDerivAt (fun t : ℝ => g (Function.update x i t)) (w i x)
       (x i)) →
    ∀ x, HasStrictFDerivAt g (coordCLM (fun i => w i x)) x := by
  intro m
  induction m with
  | zero =>
      intro g w hw hl x
      have hx : ∀ y : (Fin 0 → ℝ), y = x := by
        intro y; funext i; exact Fin.elim0 i
      have hg : g = fun _ => g x := by
        funext y; rw [hx y]
      rw [hg]
      have hz : coordCLM (fun i => w i x) = (0 : (Fin 0 → ℝ) →L[ℝ] W) := by
        ext u
        simp [coordCLM_apply]
      rw [hz]
      exact hasStrictFDerivAt_const (𝕜 := ℝ) (g x) x
  | succ m ih =>
      intro g w hw hl x
      let e : (ℝ × (Fin m → ℝ)) ≃L[ℝ] (Fin m.succ → ℝ) :=
        Fin.consEquivL ℝ (fun _ : Fin m.succ => ℝ)
      let a : ℝ := x 0
      let b : Fin m → ℝ := fun i => x i.succ
      have ex : e (a,b) = x := by
        funext i
        refine Fin.cases ?_ ?_ i <;> simp [e, a, b]
      let f : ℝ → (Fin m → ℝ) → W := fun s t => g (Fin.cons s t)
      let wt (i : Fin m) : (Fin m → ℝ) → W := fun t => w i.succ (Fin.cons a t)
      have hwt : ∀ i, Continuous (wt i) := by
        intro i
        exact (hw i.succ).comp
          (continuous_const.finCons continuous_id)
      have tail_update (aa:ℝ) (t : Fin m → ℝ) (i:Fin m) (s:ℝ) :
          Fin.cons aa (Function.update t i s) =
             Function.update (Fin.cons aa t : Fin m.succ → ℝ) i.succ s := by
        funext j
        refine Fin.cases ?_ ?_ j
        · simp [Function.update_apply]
          intro H; exact (Fin.succ_ne_zero i H.symm).elim
        · intro k
          by_cases hk : k = i
          · subst k; simp [Function.update_apply]
          · have hne : k.succ ≠ i.succ := by simpa using hk
            simp [Function.update_apply, hk, hne]
      have hlt : ∀ i (t : Fin m → ℝ),
          HasDerivAt
            (fun s : ℝ => (fun b => f a b) (Function.update t i s))
            (wt i t) (t i) := by
        intro i t
        have H := hl i.succ (Fin.cons a t)
        have heq : (fun s : ℝ => (fun b => f a b) (Function.update t i s)) =
            (fun s : ℝ => g (Function.update (Fin.cons a t) i.succ s)) := by
          funext s; exact congrArg g (tail_update a t i s)
        rw [heq]
        simpa [wt] using H
      have hbder : HasStrictFDerivAt (fun t => f a t)
              (coordCLM (fun i => wt i b)) b := ih _ _ hwt hlt b
      let f1 : ℝ → (Fin m → ℝ) → (ℝ →L[ℝ] W) := fun s t =>
        (1 : ℝ →L[ℝ] ℝ).smulRight (w 0 (Fin.cons s t))
      let f2 : ℝ → (Fin m → ℝ) → ((Fin m → ℝ) →L[ℝ] W) := fun s t =>
        coordCLM (fun i => w i.succ (Fin.cons s t))
      have df1all : ∀ p : ℝ × (Fin m → ℝ),
          HasFDerivAt (fun r => f r p.2) (f1 p.1 p.2) p.1 := by
        intro p
        have H := hl 0 (Fin.cons p.1 p.2)
        have heq :
            (fun t : ℝ => g (Function.update (Fin.cons p.1 p.2) (0 : Fin m.succ) t)) =
            (fun t : ℝ => f t p.2) := by
          funext t
          apply congrArg g
          funext j
          refine Fin.cases ?_ ?_ j
          · simp
          · intro k; simp [Function.update_apply, Fin.succ_ne_zero k]
        rw [heq] at H
        exact H
      have df2all : ∀ p : ℝ × (Fin m → ℝ),
          HasFDerivAt (fun t => f p.1 t) (f2 p.1 p.2) p.2 := by
        intro p
        let w' (i : Fin m) : (Fin m → ℝ) → W := fun t =>
          w i.succ (Fin.cons p.1 t)
        have hw' : ∀ i, Continuous (w' i) := by
          intro i; exact (hw i.succ).comp (continuous_const.finCons continuous_id)
        have hl' : ∀ i (t : Fin m → ℝ),
            HasDerivAt
              (fun s : ℝ => (fun q => f p.1 q) (Function.update t i s))
              (w' i t) (t i) := by
          intro i t
          have H := hl i.succ (Fin.cons p.1 t)
          have heq :
            (fun s : ℝ => (fun q => f p.1 q) (Function.update t i s)) =
            (fun s : ℝ => g (Function.update (Fin.cons p.1 t) i.succ s)) := by
              funext s; exact congrArg g (tail_update p.1 t i s)
          rw [heq]
          simpa [w'] using H
        exact (ih _ _ hw' hl' p.2).hasFDerivAt
      have cecons : Continuous (fun p : ℝ × (Fin m → ℝ) =>
          (Fin.cons p.1 p.2 : Fin m.succ → ℝ)) := by
          exact e.continuous
      have cf1 : ContinuousAt (Function.uncurry f1) (a,b) := by
        let T : W →L[ℝ] (ℝ →L[ℝ] W) :=
          (ContinuousLinearMap.smulRightL ℝ ℝ W) (1 : ℝ →L[ℝ] ℝ)
        exact (T.continuous.comp ((hw 0).comp cecons)).continuousAt
      have cf2 : ContinuousAt (Function.uncurry f2) (a,b) := by
        have hh : ∀ i : Fin m,
            Continuous (fun p : ℝ × (Fin m → ℝ) => w i.succ (Fin.cons p.1 p.2)) :=
          fun i => (hw i.succ).comp cecons
        exact (continuous_coordCLM hh).continuousAt
      have hpstrict : HasStrictFDerivAt (Function.uncurry f)
          (((f1 a b).coprod (f2 a b))) (a,b) :=
        hasStrictFDerivAt_uncurry_coprod (u := (a,b)) (f:=f) (f₁:=f1) (f₂:=f2)
          (Filter.Eventually.of_forall df1all)
          (Filter.Eventually.of_forall df2all) cf1 cf2
      have heder : HasStrictFDerivAt e.symm (e.symm : (Fin m.succ → ℝ) →L[ℝ] (ℝ × (Fin m → ℝ))) x := e.symm.hasStrictFDerivAt
      have comp := hpstrict.comp x heder
      have fun_eq : (Function.uncurry f) ∘ e.symm = g := by
        funext y
        change g (e (e.symm y)) = g y
        rw [e.apply_symm_apply]
      have fun_eq' : (fun x => Function.uncurry f (e.symm x)) = g := fun_eq
      rw [fun_eq'] at comp
      have hmap :
          ((f1 a b).coprod (f2 a b)).comp (e.symm :
              (Fin m.succ → ℝ) →L[ℝ] (ℝ × (Fin m → ℝ))) =
            coordCLM (fun i => w i x) := by
        ext u
        simp [ContinuousLinearMap.comp_apply, f1, f2, coordCLM_apply, e]
        have hx : (Fin.cons a b : Fin m.succ → ℝ) = x := by
          funext j
          refine Fin.cases ?_ ?_ j
          · simp [a]
          · intro k
            simp [b]
        rw [← hx]
        rw [Fin.sum_univ_succ]
        rfl
      rw [hmap] at comp
      exact comp
end
end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/OrbitChartCore.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/OrbitReduce.lean
section
open Set Function Filter Metric
open scoped Topology
namespace LeanEval.Geometry.LiouvilleArnold.Support


theorem action_stabilizer_discrete_of_isolated
    {A X : Type*} [NormedAddCommGroup A]
    [TopologicalSpace X]
    (Ψ : A → X → X) (z : X)
    (h0 : ∀ x, Ψ 0 x = x)
    (ha : ∀ a b x, Ψ (a+b) x = Ψ a (Ψ b x))
    (hi : ∃ D ∈ nhds (0:A), ∀ a ∈ D, Ψ a z = z → a = 0) :
    IsDiscrete {a : A | Ψ a z = z} := by
  classical
  rcases hi with ⟨D,hD,hiso⟩
  apply isDiscrete_iff_nhdsWithin.2
  intro a haS
  have hneg : Ψ (-a) z = z := by
    have hh := ha (-a) a z
    rw [haS] at hh
    have hh' : z = Ψ (-a) z := by simpa [h0] using hh
    exact hh'.symm
  let N : Set A := (fun q : A => (-a)+q) ⁻¹' D
  have hN : N ∈ nhds a := by
    have ht : Tendsto (fun q : A => (-a)+q) (nhds a) (nhds ((-a)+a)) :=
      (continuous_const_add (-a)).continuousAt
    have hzero : (-a)+a = (0:A) := neg_add_cancel a
    have : D ∈ nhds ((-a)+a) := by simpa [hzero] using hD
    exact ht this
  have hinter : N ∩ {q : A | Ψ q z = z} ⊆ ({a} : Set A) := by
    intro b hb
    have hfix : Ψ ((-a)+b) z = z := by
      rw [ha]
      have hb' : Ψ b z = z := hb.2
      rw [hb', hneg]
    have hm : (-a)+b ∈ D := hb.1
    have hz0 := hiso ((-a)+b) hm hfix
    have eq : b = a := by
      have : b = a + 0 := by
        calc b = a + ((-a)+b) := by simp [add_assoc]
             _ = a + 0 := by rw [hz0]
      simpa using this
    simpa [eq]
  apply le_antisymm
  · exact (Filter.le_pure_iff).2 ((mem_nhdsWithin_iff_exists_mem_nhds_inter).2
        ⟨N, hN, hinter⟩)
  · -- a point belongs both to its neighbourhood and to the carrier
    rw [nhdsWithin]
    refine le_inf (show pure a ≤ nhds a from (@pure_le_nhds A _ a)) ?_
    exact le_principal_iff.mpr (by simpa using haS)

end LeanEval.Geometry.LiouvilleArnold.Support

namespace LeanEval.Geometry.LiouvilleArnold.Support
open Set Function Filter
open scoped Topology

theorem compact_lifts_of_local_orbit_charts
    {A X : Type*} [NormedAddCommGroup A]
    [TopologicalSpace X] [PreconnectedSpace X] [Nonempty X]
    (Ψ : A → X → X)
    (h0 : ∀ x, Ψ 0 x = x)
    (ha : ∀ a b x, Ψ (a+b) x = Ψ a (Ψ b x))
    (hloc : ∀ z : X, ∃ D : Set A, IsCompact D ∧
       ∃ W ∈ nhds z, W ⊆ (fun u : A => Ψ u z) '' D) :
    ∀ x y : X, ∃ C : Set A, IsCompact C ∧
       ∃ W ∈ nhds y, W ⊆ (fun u : A => Ψ u x) '' C := by
  classical
  intro x
  let O : Set X := Set.range (fun u : A => Ψ u x)
  have hOopen : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases hz with ⟨t,rfl⟩
    obtain ⟨D,hDc,W,hW,hsub⟩ := hloc (Ψ t x)
    have hWO : W ⊆ O := by
      intro q hq
      rcases hsub hq with ⟨a,haD,rfl⟩
      refine ⟨a+t, ?_⟩
      exact ha a t x
    exact mem_of_superset hW hWO
  have hOcopen : IsOpen Oᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨D,hDc,W,hW,hsub⟩ := hloc z
    have hWO : W ⊆ Oᶜ := by
      intro q hq
      apply (Set.mem_compl_iff _ _).2
      intro hqin
      rcases hsub hq with ⟨a,haD,heq⟩
      rcases hqin with ⟨b,hb⟩
      change Ψ b x = q at hb
      change Ψ a z = q at heq
      have hback : Ψ (-a) (Ψ a z) = z := by
        rw [← ha]
        simp [h0]
      have : z ∈ O := by
        refine ⟨(-a)+b, ?_⟩
        calc
          Ψ ((-a)+b) x = Ψ (-a) (Ψ b x) := ha _ _ _
          _ = Ψ (-a) q := by rw [hb]
          _ = z := by rw [← heq, hback]
      exact hz this
    exact mem_of_superset hW hWO
  have hOu : O = (Set.univ : Set X) :=
    (show IsClopen O from ⟨(by simpa using (isClosed_compl_iff.mpr hOcopen)), hOopen⟩).eq_univ
      ⟨Ψ 0 x, ⟨0, rfl⟩⟩
  intro y
  have hy : y ∈ O := by rw [hOu]; trivial
  rcases hy with ⟨t,ht⟩
  change Ψ t x = y at ht
  obtain ⟨D,hD,W,hW,hsub⟩ := hloc y
  let C : Set A := (fun a : A => t+a) '' D
  have hC : IsCompact C :=
    hD.image (continuous_const_add t)
  refine ⟨C,hC,W,hW,?_⟩
  intro q hq
  rcases hsub hq with ⟨a,haD,rfl⟩
  refine ⟨t+a, ⟨a,haD,rfl⟩, ?_⟩
  calc
    Ψ (t+a) x = Ψ (a+t) x := by rw [add_comm]
    _ = Ψ a (Ψ t x) := ha _ _ _
    _ = Ψ a y := by rw [ht]
end LeanEval.Geometry.LiouvilleArnold.Support
namespace LeanEval.Geometry.LiouvilleArnold.Support
open Set Function Filter Metric

theorem compact_chart_of_ball
 {A X : Type*} [NormedAddCommGroup A] [ProperSpace A]
 [TopologicalSpace X] {Ψ : A → X → X}
 (h : ∀ z : X, ∃ r : ℝ, 0 < r ∧
    ∃ W ∈ nhds z, W ⊆ (fun u : A => Ψ u z) '' (Metric.ball 0 r)) :
 ∀ z : X, ∃ D : Set A, IsCompact D ∧
    ∃ W ∈ nhds z, W ⊆ (fun u : A => Ψ u z) '' D := by
 intro z
 obtain ⟨r,hr,W,hW,hh⟩ := h z
 refine ⟨Metric.closedBall 0 r, ProperSpace.isCompact_closedBall _ _, W, hW, ?_⟩
 exact fun q hq =>
   (Set.image_mono Metric.ball_subset_closedBall) (hh hq)
end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/OrbitReduce.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Submersion.lean
section



open scoped BigOperators
open Function
open Set
open Module

namespace LeanEval.Geometry.LiouvilleArnold.Support

variable {ι : Type*}


def rowsMap (V : Type*) [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V]
    (u : ι → (V →L[ℝ] ℝ)) : V →ₗ[ℝ] (ι → ℝ) where
  toFun v i := u i v
  map_add' v w := by
    funext i
    exact map_add (u i) v w
  map_smul' c v := by
    funext i
    exact map_smul (u i) c v

@[simp] lemma rowsMap_apply
    {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (u : ι → (V →L[ℝ] ℝ)) (v : V) (i : ι) :
    rowsMap (ι := ι) V u v i = u i v := rfl


theorem rowsMap_surjective
    {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [Fintype ι]
    (u : ι → (V →L[ℝ] ℝ)) (hu : LinearIndependent ℝ u) :
    Function.Surjective (rowsMap (ι := ι) V u) := by
  classical
  let A : V →ₗ[ℝ] (ι → ℝ) := rowsMap (ι := ι) V u
  let forget : (V →L[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ) :=
    ContinuousLinearMap.coeLM ℝ
  have hforg : Function.Injective forget := by
    intro a b h
    apply ContinuousLinearMap.ext
    intro x
    exact LinearMap.congr_fun h x
  have hu' : LinearIndependent ℝ (fun i => (u i).toLinearMap) := by
    have h := hu.map' forget (LinearMap.ker_eq_bot.mpr hforg)
    exact h
  let b : Module.Basis ι ℝ (ι → ℝ) := Pi.basisFun ℝ ι
  have hrow (i : ι) : A.dualMap (b.dualBasis i) = (u i).toLinearMap := by
    apply LinearMap.ext
    intro v
    simp [A, b, LinearMap.dualMap_apply, rowsMap, Module.Basis.dualBasis_apply,
      Pi.basisFun_repr]
  have hli : LinearIndependent ℝ ((A.dualMap : Module.Dual ℝ (ι → ℝ) →ₗ[ℝ]
        Module.Dual ℝ V) ∘ (b.dualBasis : ι → Module.Dual ℝ (ι → ℝ))) := by
    have hfun :
        ((A.dualMap : Module.Dual ℝ (ι → ℝ) →ₗ[ℝ] Module.Dual ℝ V) ∘
            (b.dualBasis : ι → Module.Dual ℝ (ι → ℝ))) =
          (fun i => (u i).toLinearMap) := by
      funext i
      exact hrow i
    rw [hfun]
    exact hu'
  have hspan : Submodule.span ℝ (Set.range (b.dualBasis : ι →
        Module.Dual ℝ (ι → ℝ))) = ⊤ := Module.Basis.span_eq _
  have hinj : Function.Injective
      (A.dualMap : Module.Dual ℝ (ι → ℝ) → Module.Dual ℝ V) :=
    LinearMap.injective_of_linearIndependent hspan hli
  have hsurj : Function.Surjective (A : V → (ι → ℝ)) :=
    (LinearMap.dualMap_injective_iff).1 hinj
  exact hsurj

end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Submersion.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/FlowPrep.lean
section
open scoped BigOperators ContDiff
open Function Set
namespace LeanEval.Geometry.LiouvilleArnold.Support
noncomputable def hamVecCLM {n : ℕ}
    (p q : Fin n → Fin (2 * n)) :
    (((EuclideanSpace ℝ (Fin (2 * n))) →L[ℝ] ℝ) →L[ℝ]
        EuclideanSpace ℝ (Fin (2 * n))) :=
  LinearMap.toContinuousLinearMap (hamVecLM p q)
@[simp] theorem hamVecCLM_apply {n : ℕ}
    (p q : Fin n → Fin (2 * n))
    (l : (EuclideanSpace ℝ (Fin (2 * n))) →L[ℝ] ℝ) :
  hamVecCLM p q l = hamVec p q l := by
  rfl

theorem contDiffOn_hamVec {n : ℕ}
    (p q : Fin n → Fin (2 * n))
    {f : (EuclideanSpace ℝ (Fin (2 * n))) → ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (2 * n)))}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞
      (fun x => hamVec p q (fderiv ℝ f x)) s := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) s :=
    hf.fderiv_of_isOpen hs (by simp)
  have hc : ContDiff ℝ ∞ (hamVecCLM p q) :=
    (hamVecCLM p q).contDiff
  have hcomp := hc.comp_contDiffOn hd
  simpa [Function.comp_def] using hcomp

theorem contDiffAt_hamVec {n : ℕ}
    (p q : Fin n → Fin (2 * n))
    {f : (EuclideanSpace ℝ (Fin (2 * n))) → ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (2 * n)))}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) {x} (hx : x ∈ s) :
    ContDiffAt ℝ 1 (fun y => hamVec p q (fderiv ℝ f y)) x := by
  have h := contDiffOn_hamVec p q hs hf
  exact (h.contDiffAt (hs.mem_nhds hx)).of_le (by simp)
end LeanEval.Geometry.LiouvilleArnold.Support
open scoped ContDiff
open Function Set
namespace LeanEval.Geometry.LiouvilleArnold.Support
theorem hamVec_exists_lipschitz {n : ℕ}
    (p q : Fin n → Fin (2 * n))
    {f : (EuclideanSpace ℝ (Fin (2 * n))) → ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (2 * n)))}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) {x} (hx : x ∈ s) :
    ∃ K : NNReal, ∃ t ∈ nhds x, t ⊆ s ∧
      LipschitzOnWith K (fun y => hamVec p q (fderiv ℝ f y)) t := by
  have hc := contDiffAt_hamVec p q hs hf hx
  obtain ⟨K, t, ht, hL⟩ := hc.exists_lipschitzOnWith
  refine ⟨K, t ∩ s, Filter.inter_mem ht (hs.mem_nhds hx), ?_, hL.mono ?_⟩
  · exact Set.inter_subset_right
  · exact Set.inter_subset_left
end LeanEval.Geometry.LiouvilleArnold.Support
open scoped ContDiff
open Function Set
namespace LeanEval.Geometry.LiouvilleArnold.Support

theorem firstIntegral_const_on_Ioo
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {v : V → V} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (hzero : ∀ x ∈ U, fderiv ℝ f x (v x) = 0)
    {α : ℝ → V} {a b : ℝ}
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (v (α t)) t)
    (hstay : MapsTo α (Ioo a b) U) :
    ∀ {s t}, s ∈ Ioo a b → t ∈ Ioo a b → f (α s) = f (α t) := by
  have hcomp : ∀ t ∈ Ioo a b,
      HasDerivAt (fun z => f (α z)) (fderiv ℝ f (α t) (v (α t))) t := by
    intro t ht
    have hf' : HasFDerivAt f (fderiv ℝ f (α t)) (α t) :=
      hf.hasFDerivAt (hU.mem_nhds (hstay ht))
    simpa [Function.comp_def] using
      (hf'.comp_hasDerivAt t (hα t ht))
  have hdif : DifferentiableOn ℝ (fun z => f (α z)) (Ioo a b) := by
    intro t ht
    exact (hcomp t ht).differentiableAt.differentiableWithinAt
  have hdz : (Ioo a b).EqOn (deriv (fun z => f (α z))) (0 : ℝ → ℝ) := by
    intro t ht
    have hh := (hcomp t ht).deriv
    simpa [hzero (α t) (hstay ht)] using hh
  intro s t hs ht
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdif hdz hs ht
end LeanEval.Geometry.LiouvilleArnold.Support

open Set Function Filter
namespace LeanEval.Geometry.LiouvilleArnold.Support


theorem eventuallyEq_integralCurve_of_lipschitz
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {v : V → V} {s : Set V} {K : NNReal}
    (hl : LipschitzOnWith K v s)
    {α β : ℝ → V} {t₀ : ℝ}
    (hα : ∀ᶠ t in nhds t₀, HasDerivAt α (v (α t)) t ∧ α t ∈ s)
    (hβ : ∀ᶠ t in nhds t₀, HasDerivAt β (v (β t)) t ∧ β t ∈ s)
    (h0 : α t₀ = β t₀) : α =ᶠ[nhds t₀] β := by
  apply ODE_solution_unique_of_eventually
    (v := fun _ : ℝ => v) (s := fun _ : ℝ => s) (K := K)
    (hf := hα) (hg := hβ)
  · exact Filter.Eventually.of_forall (fun _ => hl)
  · exact h0


end LeanEval.Geometry.LiouvilleArnold.Support


end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/FlowPrep.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/HamiltonianStd.lean
section

open scoped BigOperators
open Function
open Fintype

namespace LeanEval.Geometry.LiouvilleArnold.Support


def pstd {n : ℕ} (i : Fin n) : Fin (2*n) :=
  ⟨i.val, by have := i.isLt; omega⟩

def qstd {n : ℕ} (i : Fin n) : Fin (2*n) :=
  ⟨i.val + n, by have := i.isLt; omega⟩

lemma pstd_inj {n : ℕ} {i j : Fin n} :
    (pstd i : Fin (2*n)) = pstd j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    simpa [pstd] using congrArg Fin.val h
  · exact fun h => congrArg pstd h
lemma qstd_inj {n : ℕ} {i j : Fin n} :
    (qstd i : Fin (2*n)) = qstd j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have t := congrArg Fin.val h
    dsimp [qstd] at t
    omega
  · exact fun h => congrArg qstd h

lemma pstd_ne_qstd {n : ℕ} (i j : Fin n) :
    (pstd i : Fin (2*n)) ≠ qstd j := by
  intro h
  have t := congrArg Fin.val h
  dsimp [pstd, qstd] at t
  have hi := i.isLt
  have hj := j.isLt
  omega

lemma qstd_ne_pstd {n : ℕ} (i j : Fin n) :
    (qstd i : Fin (2*n)) ≠ pstd j := by
  exact Ne.symm (pstd_ne_qstd j i)


theorem hamVec_pcoord {n : ℕ}
    (l : (EuclideanSpace ℝ (Fin (2*n))) →L[ℝ] ℝ)
    (k : Fin n) :
    (hamVec (@pstd n) (@qstd n) l).ofLp (pstd k) =
      - l (EuclideanSpace.single (qstd k) (1 : ℝ)) := by
  classical
  change
    (EuclideanSpace.proj (𝕜 := ℝ) (pstd k))
        (hamVec (@pstd n) (@qstd n) l) = _
  unfold hamVec
  rw [map_sum]
  have hterm (i : Fin n) :
      (EuclideanSpace.proj (𝕜 := ℝ) (pstd k))
        ((- l (EuclideanSpace.single (qstd i) (1 : ℝ))) •
              EuclideanSpace.single (pstd i) (1 : ℝ) +
          (l (EuclideanSpace.single (pstd i) (1 : ℝ))) •
              EuclideanSpace.single (qstd i) (1 : ℝ)) =
        if i = k then
          - l (EuclideanSpace.single (qstd k) (1 : ℝ))
        else 0 := by
      by_cases h : i = k
      · subst i
        simp [EuclideanSpace.single_apply,
          pstd_ne_qstd k k]
      · have hpk : (pstd k : Fin (2*n)) ≠ pstd i := by
            intro eq
            exact h ((pstd_inj).1 eq.symm)
        have hpq : (pstd k : Fin (2*n)) ≠ qstd i :=
          pstd_ne_qstd k i
        simp [EuclideanSpace.single_apply, h, hpk, hpq]
  simp_rw [hterm]
  simp


theorem hamVec_qcoord {n : ℕ}
    (l : (EuclideanSpace ℝ (Fin (2*n))) →L[ℝ] ℝ)
    (k : Fin n) :
    (hamVec (@pstd n) (@qstd n) l).ofLp (qstd k) =
        l (EuclideanSpace.single (pstd k) (1 : ℝ)) := by
  classical
  change
    (EuclideanSpace.proj (𝕜 := ℝ) (qstd k))
        (hamVec (@pstd n) (@qstd n) l) = _
  unfold hamVec
  rw [map_sum]
  have hterm (i : Fin n) :
      (EuclideanSpace.proj (𝕜 := ℝ) (qstd k))
        ((- l (EuclideanSpace.single (qstd i) (1 : ℝ))) •
              EuclideanSpace.single (pstd i) (1 : ℝ) +
          (l (EuclideanSpace.single (pstd i) (1 : ℝ))) •
              EuclideanSpace.single (qstd i) (1 : ℝ)) =
        if i = k then
            l (EuclideanSpace.single (pstd k) (1 : ℝ))
        else 0 := by
      by_cases h : i = k
      · subst i
        simp [EuclideanSpace.single_apply, qstd_ne_pstd k k]
      · have hqk : (qstd k : Fin (2*n)) ≠ qstd i := by
            intro eq
            exact h ((qstd_inj).1 eq.symm)
        have hqp : (qstd k : Fin (2*n)) ≠ pstd i :=
          qstd_ne_pstd k i
        simp [EuclideanSpace.single_apply, h, hqk, hqp]
  simp_rw [hterm]
  simp


theorem hamVecLM_std_injective {n : ℕ} :
    Function.Injective
      (hamVecLM (@pstd n) (@qstd n)) := by
  classical
  intro l m h
  let b : Module.Basis (Fin (2*n)) ℝ (EuclideanSpace ℝ (Fin (2*n))) :=
    PiLp.basisFun 2 ℝ _
  apply ContinuousLinearMap.ext
  intro v
  have heq : l.toLinearMap = m.toLinearMap := by
    apply b.ext
    intro a
    by_cases ha : a.val < n
    · let k : Fin n := ⟨a.val, ha⟩
      have ak : (pstd k : Fin (2*n)) = a := by
        apply Fin.ext
        rfl
      have z := congrArg (fun v : EuclideanSpace ℝ (Fin (2*n)) =>
            v.ofLp (qstd k)) h
      change (hamVec (@pstd n) (@qstd n) l).ofLp (qstd k) =
             (hamVec (@pstd n) (@qstd n) m).ofLp (qstd k) at z
      have z' : l (EuclideanSpace.single (pstd k) (1 : ℝ)) =
             m (EuclideanSpace.single (pstd k) (1 : ℝ)) := by
        simpa [hamVec_qcoord] using z
      simpa [b, PiLp.basisFun_apply, ak] using z'
    · have hge : n ≤ a.val := Nat.le_of_not_lt ha
      have hlt : a.val - n < n := by
        have htop := a.isLt
        omega
      let k : Fin n := ⟨a.val - n, hlt⟩
      have ak : (qstd k : Fin (2*n)) = a := by
        apply Fin.ext
        dsimp [qstd, k]
        omega
      have z := congrArg (fun v : EuclideanSpace ℝ (Fin (2*n)) =>
            v.ofLp (pstd k)) h
      change (hamVec (@pstd n) (@qstd n) l).ofLp (pstd k) =
             (hamVec (@pstd n) (@qstd n) m).ofLp (pstd k) at z
      have z' : l (EuclideanSpace.single (qstd k) (1 : ℝ)) =
             m (EuclideanSpace.single (qstd k) (1 : ℝ)) := by
        have zz : - l (EuclideanSpace.single (qstd k) (1 : ℝ)) =
             - m (EuclideanSpace.single (qstd k) (1 : ℝ)) := by
          simpa [hamVec_pcoord] using z
        linarith
      simpa [b, PiLp.basisFun_apply, ak] using z'
  have hv := LinearMap.congr_fun heq v
  exact hv


theorem independent_hamVec {n : ℕ} {κ : Type*}
    (u : κ → (EuclideanSpace ℝ (Fin (2*n)) →L[ℝ] ℝ))
    (hu : LinearIndependent ℝ u) :
    LinearIndependent ℝ
      (fun i => hamVec (@pstd n) (@qstd n) (u i)) := by
  classical
  let J := hamVecLM (@pstd n) (@qstd n)
  have hz : J.ker = ⊥ := LinearMap.ker_eq_bot.mpr hamVecLM_std_injective
  have h := hu.map' J hz
  exact h

end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/HamiltonianStd.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/OrbitChart.lean
section
open Set Function Filter Metric
open scoped Topology
namespace LeanEval.Geometry.LiouvilleArnold.Support
noncomputable section


theorem local_level_chart_of_frame
    {A V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace A] [CompleteSpace V]
    (q : (A × A) ≃L[ℝ] V) (z : V) (f : V → A) (g : A → V)
    (hg0 : g 0 = z)
    (hf : HasStrictFDerivAt f
      ((ContinuousLinearMap.snd ℝ A A).comp
        (q.symm : V →L[ℝ] (A × A))) z)
    (hg : HasStrictFDerivAt g
      ((q : (A × A) →L[ℝ] V).comp
        (ContinuousLinearMap.inl ℝ A A)) 0)
    (hlevel : ∀ u, f (g u) = f z) :
    ∃ r : ℝ, 0 < r ∧ Set.InjOn g (Metric.ball 0 r) ∧
      ∃ N ∈ nhds z, ∀ x ∈ N, f x = f z →
        x ∈ g '' (Metric.ball 0 r) := by
  classical
  let B : V →L[ℝ] A :=
    (ContinuousLinearMap.fst ℝ A A).comp (q.symm : V →L[ℝ] (A × A))
  let Y : A →L[ℝ] V :=
    (q : (A × A) →L[ℝ] V).comp (ContinuousLinearMap.inl ℝ A A)
  have hBY : B.comp Y = (ContinuousLinearMap.id ℝ A) := by
    ext u
    change (q.symm (q (u, (0:A)))).1 = u
    simp
  let k : A → A := fun u => B (g u - z)
  have hsubg : HasStrictFDerivAt (fun u : A => g u - z) Y 0 := by
    exact hg.sub_const z
  have hk' : HasStrictFDerivAt k (ContinuousLinearMap.id ℝ A) 0 := by
    have h := (B.hasStrictFDerivAt.comp 0 hsubg)
    rw [hBY] at h
    exact h
  have hk0 : k 0 = 0 := by simp [k, hg0]
  let H : V → (A × A) := fun x => (B (x-z), f x - f z)
  have htrans : HasStrictFDerivAt (fun x : V => x - z)
        (ContinuousLinearMap.id ℝ V) z := by
    simpa only [id_eq] using (hasStrictFDerivAt_id z).sub_const z
  have hfirst : HasStrictFDerivAt (fun x : V => B (x-z)) B z := by
    simpa using (B.hasStrictFDerivAt.comp z htrans)
  have hsecond : HasStrictFDerivAt (fun x : V => f x - f z)
      ((ContinuousLinearMap.snd ℝ A A).comp
        (q.symm : V →L[ℝ] (A × A))) z := by
    exact hf.sub_const (f z)
  have hprod : HasStrictFDerivAt H
      (B.prod ((ContinuousLinearMap.snd ℝ A A).comp
        (q.symm : V →L[ℝ] (A × A)))) z :=
    hfirst.prodMk hsecond
  have hmap : (B.prod ((ContinuousLinearMap.snd ℝ A A).comp
        (q.symm : V →L[ℝ] (A × A)))) =
        (q.symm : V →L[ℝ] (A × A)) := by
    ext v <;> rfl
  have hH' : HasStrictFDerivAt H (q.symm : V →L[ℝ] (A × A)) z := by
    rw [← hmap]
    exact hprod
  have hH0 : H z = (0,0) := by simp [H]
  let idq : A ≃L[ℝ] A := ContinuousLinearEquiv.refl ℝ A
  have hk'' : HasStrictFDerivAt k (idq : A →L[ℝ] A) 0 := hk'
  let ek := hk''.toOpenPartialHomeomorph k
  let eH := hH'.toOpenPartialHomeomorph H
  have h0k : (0:A) ∈ ek.source := hk''.mem_toOpenPartialHomeomorph_source
  have hzk : z ∈ eH.source := hH'.mem_toOpenPartialHomeomorph_source
  have Sk : ek.source ∈ nhds (0:A) :=
    ek.open_source.mem_nhds h0k
  have SH : eH.source ∈ nhds z :=
    eH.open_source.mem_nhds hzk
  have guH : {u : A | g u ∈ eH.source} ∈ nhds (0:A) := by
    have : Tendsto g (nhds (0:A)) (nhds z) :=
      (hg.continuousAt : ContinuousAt g 0) |>.tendsto |>.trans (by
        rw [hg0])
    exact this SH
  have Sint : ek.source ∩ {u : A | g u ∈ eH.source} ∈ nhds (0:A) :=
    inter_mem Sk guH
  obtain ⟨r,hr,hball⟩ := (Metric.mem_nhds_iff).1 Sint
  let l : A → A := hk''.localInverse k _ _
  have hright : ∀ᶠ p in nhds (0:A), k (l p) = p := by
    have h := hk''.eventually_right_inverse
    simpa [l, hk0] using h
  have ht_l : Tendsto l (nhds (0:A)) (nhds (0:A)) := by
    simpa [l, hk0] using hk''.localInverse_tendsto
  have hlball : ∀ᶠ p in nhds (0:A), l p ∈ Metric.ball (0:A) r :=
    ht_l (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  let P : Set A := {p | k (l p) = p} ∩ {p | l p ∈ Metric.ball (0:A) r}
  have hP : P ∈ nhds (0:A) := by
    exact inter_mem hright hlball
  let pmap : V → A := fun x => B (x-z)
  have hpmap : Tendsto pmap (nhds z) (nhds (0:A)) := by
    have hc : ContinuousAt pmap z :=
      (hfirst.continuousAt)
    simpa [pmap] using hc.tendsto
  have hpN : {x : V | pmap x ∈ P} ∈ nhds z := hpmap hP
  let N : Set V := eH.source ∩ {x : V | pmap x ∈ P}
  have hN : N ∈ nhds z := inter_mem SH hpN
  refine ⟨r, hr, ?_, N, hN, ?_⟩
  · intro a ha b hb hab
    apply ek.injOn (hball ha).1 (hball hb).1
    change k a = k b
    dsimp [k]
    rw [hab]
  · intro x hx hfx
    have hxS : x ∈ eH.source := hx.1
    have hpP : pmap x ∈ P := hx.2
    let p : A := pmap x
    let u : A := l p
    have hu_ball : u ∈ Metric.ball (0:A) r := hpP.2
    have huS : u ∈ ek.source ∩ {u : A | g u ∈ eH.source} :=
      hball hu_ball
    have hku : k u = p := hpP.1
    have hguS : g u ∈ eH.source := huS.2
    have hHeq : H (g u) = H x := by
      apply Prod.ext
      · change k u = pmap x
        exact hku
      · change f (g u) - f z = f x - f z
        rw [hlevel, hfx]
    have hxeq : g u = x :=
      eH.injOn hguS hxS hHeq
    exact ⟨u, hu_ball, hxeq⟩
end
end LeanEval.Geometry.LiouvilleArnold.Support

namespace LeanEval.Geometry.LiouvilleArnold.Support
noncomputable section
open scoped BigOperators

theorem exists_frame_equiv {m : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (R : V →ₗ[ℝ] (Fin m → ℝ)) (hR : Function.Surjective R)
    (w : Fin m → V) (hw : LinearIndependent ℝ w)
    (hker : Submodule.span ℝ (Set.range w) = LinearMap.ker R) :
    ∃ q : ((Fin m → ℝ) × (Fin m → ℝ)) ≃L[ℝ] V,
       (∀ u, q (u,0) = ∑ i, u i • w i) ∧
       (∀ p, R (q p) = p.2) := by
  classical
  let Y : (Fin m → ℝ) →ₗ[ℝ] V := Fintype.linearCombination ℝ w
  have hYi : Function.Injective Y := by
    exact hw.fintypeLinearCombination_injective
  have hYr : LinearMap.range Y = Submodule.span ℝ (Set.range w) :=
    Fintype.range_linearCombination _ _
  obtain ⟨J,hJ⟩ := R.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hR)
  have hRJ : ∀ b, R (J b) = b := fun b => LinearMap.congr_fun hJ b
  have hY0 : ∀ a, R (Y a) = 0 := by
    intro a
    have hy : Y a ∈ Submodule.span ℝ (Set.range w) := by
      rw [← hYr]
      exact ⟨a, rfl⟩
    rw [hker] at hy
    exact (LinearMap.mem_ker).1 hy
  let Q : ((Fin m → ℝ) × (Fin m → ℝ)) →ₗ[ℝ] V :=
    (Y.comp (LinearMap.fst ℝ _ _)) +
      (J.comp (LinearMap.snd ℝ _ _))
  have hQ_apply (p : (Fin m → ℝ) × (Fin m → ℝ)) :
      Q p = Y p.1 + J p.2 := rfl
  have hRQ (p : (Fin m → ℝ) × (Fin m → ℝ)) : R (Q p) = p.2 := by
    simp [hQ_apply, hY0, hRJ]
  have hQi : Function.Injective Q := by
    intro a b hab
    have h2 : a.2 = b.2 := by
      simpa [hRQ] using congrArg R hab
    have h1Y : Y a.1 = Y b.1 := by
      simpa [hQ_apply, h2] using hab
    have h1 : a.1 = b.1 := hYi h1Y
    exact Prod.ext h1 h2
  have hQs : Function.Surjective Q := by
    intro x
    let b : (Fin m → ℝ) := R x
    have hxker : x - J b ∈ LinearMap.ker R := by
      apply (LinearMap.mem_ker).2
      simp [b, hRJ]
    rw [← hker, ← hYr] at hxker
    rcases hxker with ⟨a,ha⟩
    refine ⟨(a,b), ?_⟩
    change Y a + J b = x
    rw [ha]; exact sub_add_cancel _ _
  let qe : ((Fin m → ℝ) × (Fin m → ℝ)) ≃ₗ[ℝ] V :=
    LinearEquiv.ofBijective Q ⟨hQi, hQs⟩
  let q : ((Fin m → ℝ) × (Fin m → ℝ)) ≃L[ℝ] V := qe.toContinuousLinearEquiv
  refine ⟨q, ?_, ?_⟩
  · intro u
    change Q (u,0) = _
    simp [hQ_apply, Y, Fintype.linearCombination_apply]
  · intro p
    change R (Q p) = p.2
    exact hRQ p
end
end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/OrbitChart.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Complete.lean
section
open Set Function Filter Metric
open scoped Topology
namespace LeanEval.Geometry.LiouvilleArnold.Support


def ODESolOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : V → V) (α : ℝ → V) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, HasDerivAt α (v (α t)) t

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]


theorem ode_eqOn_Ioo_of_mem
    {v : V → V} {M : Set V}
    (hloc : ∀ x ∈ M, ∃ K : NNReal, ∃ W ∈ nhds x, LipschitzOnWith K v W)
    {α β : ℝ → V} {a b t₀ : ℝ}
    (hα : ODESolOn v α (Ioo a b)) (hαM : MapsTo α (Ioo a b) M)
    (hβ : ODESolOn v β (Ioo a b)) (hβM : MapsTo β (Ioo a b) M)
    (ht₀ : t₀ ∈ Ioo a b) (heq : α t₀ = β t₀) :
    EqOn α β (Ioo a b) := by
  let S : Set ℝ := {t | α t = β t} ∩ Ioo a b
  have hsub : Ioo a b ⊆ S := by
    apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := S) _
      ⟨t₀, ⟨ht₀, ⟨heq, ht₀⟩⟩⟩
    · -- closed relative to the interval: use the subtype, where both
      dsimp [S]
      rw [inter_comm, ← Subtype.image_preimage_val, inter_comm,
        ← Subtype.image_preimage_val,
        image_subset_image_iff Subtype.val_injective, preimage_setOf_eq]
      intro t ht
      rw [mem_preimage, ← closure_subtype] at ht
      revert ht t
      apply IsClosed.closure_subset (isClosed_eq _ _)
      · rw [continuous_iff_continuousAt]
        rintro ⟨z, hz⟩
        apply ContinuousAt.comp _ continuousAt_subtype_val
        change ContinuousAt α z
        exact (hα z hz).continuousAt
      · rw [continuous_iff_continuousAt]
        rintro ⟨z, hz⟩
        apply ContinuousAt.comp _ continuousAt_subtype_val
        change ContinuousAt β z
        exact (hβ z hz).continuousAt
    · rw [isOpen_iff_mem_nhds]
      intro t ht
      change α t = β t ∧ t ∈ Ioo a b at ht
      have hI : Ioo a b ∈ nhds t := Ioo_mem_nhds ht.2.1 ht.2.2
      obtain ⟨K, W, hW, hL⟩ := hloc (α t) (hαM ht.2)
      have hca : ContinuousAt α t := (hα t ht.2).continuousAt
      have hcb : ContinuousAt β t := (hβ t ht.2).continuousAt
      have haW : ∀ᶠ u in nhds t, α u ∈ W := hca.preimage_mem_nhds hW
      have hbW : ∀ᶠ u in nhds t, β u ∈ W :=
        hcb.preimage_mem_nhds (by simpa [ht.1] using hW)
      have hda : ∀ᶠ u in nhds t, HasDerivAt α (v (α u)) u := by
        filter_upwards [hI] with u hu
        exact hα u hu
      have hdb : ∀ᶠ u in nhds t, HasDerivAt β (v (β u)) u := by
        filter_upwards [hI] with u hu
        exact hβ u hu
      have hnear : α =ᶠ[nhds t] β :=
        eventuallyEq_integralCurve_of_lipschitz hL (hda.and haW) (hdb.and hbW) ht.1
      exact (hnear.and hI).mono (by
        intro u hu
        exact ⟨hu.1, hu.2⟩)
  intro t ht
  exact (hsub ht).1

end LeanEval.Geometry.LiouvilleArnold.Support

namespace LeanEval.Geometry.LiouvilleArnold.Support
open Set Function Filter Metric
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma ode_piecewise_eqOn_right
    {v : V → V} {M : Set V}
    (hloc : ∀ x ∈ M, ∃ K : NNReal, ∃ W ∈ nhds x, LipschitzOnWith K v W)
    {α β : ℝ → V} {a b a' b' t₀ : ℝ}
    (hα : ODESolOn v α (Ioo a b)) (hαM : MapsTo α (Ioo a b) M)
    (hβ : ODESolOn v β (Ioo a' b')) (hβM : MapsTo β (Ioo a' b') M)
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h0 : α t₀ = β t₀) :
    EqOn (piecewise (Ioo a b) α β) β (Ioo a' b') := by
  classical
  intro t ht
  have hcommon : EqOn α β (Ioo (max a a') (min b b')) := by
    apply ode_eqOn_Ioo_of_mem hloc
      (α := α) (β := β) (t₀ := t₀)
    · intro u hu
      exact hα u ⟨lt_of_le_of_lt (le_max_left _ _) hu.1, lt_min_iff.mp hu.2 |>.1⟩
    · intro u hu
      exact hαM ⟨lt_of_le_of_lt (le_max_left _ _) hu.1, (lt_min_iff.mp hu.2).1⟩
    · intro u hu
      exact hβ u ⟨lt_of_le_of_lt (le_max_right _ _) hu.1, (lt_min_iff.mp hu.2).2⟩
    · intro u hu
      exact hβM ⟨lt_of_le_of_lt (le_max_right _ _) hu.1, (lt_min_iff.mp hu.2).2⟩
    · exact ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩
    · exact h0
  by_cases hm : t ∈ Ioo a b
  · rw [piecewise, if_pos hm]
    exact hcommon ⟨max_lt hm.1 ht.1, lt_min hm.2 ht.2⟩
  · rw [piecewise, if_neg hm]

lemma ode_piecewise_sol
    {v : V → V} {M : Set V}
    (hloc : ∀ x ∈ M, ∃ K : NNReal, ∃ W ∈ nhds x, LipschitzOnWith K v W)
    {α β : ℝ → V} {a b a' b' t₀ : ℝ}
    (hα : ODESolOn v α (Ioo a b)) (hαM : MapsTo α (Ioo a b) M)
    (hβ : ODESolOn v β (Ioo a' b')) (hβM : MapsTo β (Ioo a' b') M)
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h0 : α t₀ = β t₀) :
    ODESolOn v (piecewise (Ioo a b) α β) (Ioo a b ∪ Ioo a' b') ∧
      MapsTo (piecewise (Ioo a b) α β) (Ioo a b ∪ Ioo a' b') M := by
  classical
  have heqr := ode_piecewise_eqOn_right hloc hα hαM hβ hβM ht₀ h0
  constructor
  · intro t ht
    by_cases hm : t ∈ Ioo a b
    · have hv0 := hα t hm
      have heval : piecewise (Ioo a b) α β t = α t := by
        simp [piecewise, hm]
      have hev : (piecewise (Ioo a b) α β) =ᶠ[nhds t] α := by
        filter_upwards [Ioo_mem_nhds hm.1 hm.2] with z hz
        simp [piecewise, hz]
      simpa [heval] using (hv0.congr_of_eventuallyEq hev)
    · have hbmem : t ∈ Ioo a' b' := ht.resolve_left hm
      have hv0 := hβ t hbmem
      have hval : piecewise (Ioo a b) α β t = β t := heqr hbmem
      have hev : (piecewise (Ioo a b) α β) =ᶠ[nhds t] β := by
        filter_upwards [Ioo_mem_nhds hbmem.1 hbmem.2] with z hz
        exact heqr hz
      simpa [hval] using (hv0.congr_of_eventuallyEq hev)
  · intro t ht
    by_cases hm : t ∈ Ioo a b
    · simpa [piecewise, hm] using hαM hm
    · have hbmem : t ∈ Ioo a' b' := ht.resolve_left hm
      have hv := hβM hbmem
      simpa [heqr hbmem] using hv

end LeanEval.Geometry.LiouvilleArnold.Support

namespace LeanEval.Geometry.LiouvilleArnold.Support
open Set Function Filter Metric
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]


theorem exists_global_ode_of_uniform
    {v : V → V} {M : Set V}
    (hloc : ∀ x ∈ M, ∃ K : NNReal, ∃ W ∈ nhds x, LipschitzOnWith K v W)
    {ε : ℝ} (hε : 0 < ε)
    (hlocal : ∀ x ∈ M, ∃ γ : ℝ → V, γ 0 = x ∧
      ODESolOn v γ (Ioo (-ε) ε) ∧ MapsTo γ (Ioo (-ε) ε) M) :
    ∀ x ∈ M, ∃ γ : ℝ → V, γ 0 = x ∧
      (∀ t : ℝ, HasDerivAt γ (v (γ t)) t) ∧ (∀ t : ℝ, γ t ∈ M) := by
  intro x hx
  let S : Set ℝ := { a | ∃ γ : ℝ → V, γ 0 = x ∧
      ODESolOn v γ (Ioo (-a) a) ∧ MapsTo γ (Ioo (-a) a) M }
  have hSnon : S.Nonempty := by
    obtain ⟨g,h0,hg,hm⟩ := hlocal x hx
    exact ⟨ε, g, h0, hg, hm⟩
  have from_unbdd : (¬ BddAbove S) →
      ∃ γ : ℝ → V, γ 0 = x ∧
        (∀ t : ℝ, HasDerivAt γ (v (γ t)) t) ∧ (∀ t : ℝ, γ t ∈ M) := by
    intro hnb
    rw [not_bddAbove_iff] at hnb
    have hchoose : ∀ A : ℝ, ∃ γ : ℝ → V, γ 0 = x ∧
        ODESolOn v γ (Ioo (-A) A) ∧ MapsTo γ (Ioo (-A) A) M := by
      intro A
      obtain ⟨r, hrS, hr⟩ := hnb A
      obtain ⟨g,hg0,hg,hm⟩ := hrS
      refine ⟨g,hg0,?_,?_⟩
      · intro t ht
        exact hg t ⟨lt_of_le_of_lt (neg_le_neg hr.le) ht.1,
                    lt_of_lt_of_le ht.2 hr.le⟩
      · intro t ht
        exact hm ⟨lt_of_le_of_lt (neg_le_neg hr.le) ht.1,
                  lt_of_lt_of_le ht.2 hr.le⟩
    choose g g0 gs gm using hchoose
    let ext : ℝ → V := fun t => g (|t| + 1) t
    refine ⟨ext, ?_, ?_, ?_⟩
    · dsimp [ext]
      exact g0 (|0| + 1)
    · intro t
      have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
        rw [mem_Ioo, ← abs_lt]
        exact lt_add_one _
      have heq : (fun u => g (|u| + 1) u) =ᶠ[nhds t] g (|t| + 1) := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
        by_cases hle : |u| + 1 ≤ |t| + 1
        · exact (ode_eqOn_Ioo_of_mem hloc
                (α := g (|u| + 1)) (β := g (|t| + 1)) (t₀ := 0)
                (a := -(|u| + 1)) (b := |u| + 1)
                (gs (|u| + 1)) (gm (|u| + 1))
                (by
                  intro z hz
                  exact gs (|t| + 1) z
                    ⟨lt_of_le_of_lt (neg_le_neg hle) hz.1,
                      lt_of_lt_of_le hz.2 hle⟩)
                (by
                  intro z hz
                  exact gm (|t| + 1)
                    ⟨lt_of_le_of_lt (neg_le_neg hle) hz.1,
                      lt_of_lt_of_le hz.2 hle⟩)
                (by constructor <;> have h : 0 < |u| + 1 := by positivity
                    all_goals linarith)
                (by rw [g0 (|u|+1), g0 (|t|+1)]))
              (by exact ⟨(abs_lt.mp (lt_add_one _)).1,
                           (abs_lt.mp (lt_add_one _)).2⟩)
        · have hle' : |t| + 1 ≤ |u| + 1 := le_of_not_ge hle
          exact (ode_eqOn_Ioo_of_mem hloc
                (α := g (|t| + 1)) (β := g (|u| + 1)) (t₀ := 0)
                (a := -(|t| + 1)) (b := |t| + 1)
                (gs (|t| + 1)) (gm (|t| + 1))
                (by
                  intro z hz
                  exact gs (|u| + 1) z
                    ⟨lt_of_le_of_lt (neg_le_neg hle') hz.1,
                      lt_of_lt_of_le hz.2 hle'⟩)
                (by
                  intro z hz
                  exact gm (|u| + 1)
                    ⟨lt_of_le_of_lt (neg_le_neg hle') hz.1,
                      lt_of_lt_of_le hz.2 hle'⟩)
                (by constructor <;> have h : 0 < |t| + 1 := by positivity
                    all_goals linarith)
                (by rw [g0 (|t|+1), g0 (|u|+1)]))
              hu |>.symm
      exact (gs (|t| + 1) t ht).congr_of_eventuallyEq heq
    · intro t
      exact gm (|t| + 1)
        (by
          rw [mem_Ioo, ← abs_lt]
          exact lt_add_one _)
  apply from_unbdd
  intro hbdd
  let A : ℝ := sSup S
  obtain ⟨a, haS, hlt⟩ := Real.add_neg_lt_sSup hSnon (ε := -(ε/2)) (by
    have := half_pos hε
    linarith)
  change A - ε/2 < a at hlt
  obtain ⟨γ, hγ0, hγ, hγM⟩ := haS
  have hεA : ε ≤ A := le_csSup hbdd (by
    obtain ⟨g,h0,hg,hm⟩ := hlocal x hx
    exact (⟨g,h0,hg,hm⟩ : ε ∈ S))
  have hcenter1 : -(A - ε/2) ∈ Ioo (-a) a := by
    constructor <;> linarith
  have hcenter2 : (A - ε/2) ∈ Ioo (-a) a := by
    constructor <;> linarith
  obtain ⟨g1,hg10,hg1,hg1M⟩ := hlocal (γ (-(A-ε/2))) (hγM hcenter1)
  obtain ⟨g2,hg20,hg2,hg2M⟩ := hlocal (γ (A-ε/2)) (hγM hcenter2)
  let l : ℝ := A - ε/2
  let γ1 : ℝ → V := fun t => g1 (t + l)
  let γ2 : ℝ → V := fun t => g2 (t - l)
  have hγ1 : ODESolOn v γ1 (Ioo (-(A + ε/2)) (-(A-ε*3/2))) := by
    intro t ht
    dsimp [γ1, l]
    apply HasDerivAt.comp_add_const t (A-ε/2)
    apply hg1 (t + (A-ε/2))
    constructor <;> linarith [ht.1, ht.2]
  have hγ1' : ODESolOn v γ1 (Ioo (- (A-ε/2) - ε) (- (A-ε/2) + ε)) := by
    intro t ht
    dsimp [γ1, l]
    apply HasDerivAt.comp_add_const t (A-ε/2)
    exact hg1 (t+(A-ε/2)) (by constructor <;> linarith [ht.1, ht.2])
  have hγ1M' : MapsTo γ1 (Ioo (- (A-ε/2) - ε) (- (A-ε/2) + ε)) M := by
    intro t ht
    exact hg1M (by dsimp [γ1, l]; constructor <;> linarith [ht.1, ht.2])
  have hγ2' : ODESolOn v γ2 (Ioo ((A-ε/2)-ε) ((A-ε/2)+ε)) := by
    intro t ht
    dsimp [γ2, l]
    apply HasDerivAt.comp_sub_const t (A-ε/2)
    exact hg2 (t-(A-ε/2)) (by constructor <;> linarith [ht.1, ht.2])
  have hγ2M' : MapsTo γ2 (Ioo ((A-ε/2)-ε) ((A-ε/2)+ε)) M := by
    intro t ht
    exact hg2M (by dsimp [γ2, l]; constructor <;> linarith [ht.1, ht.2])
  have eq1 : γ1 (-(A-ε/2)) = γ (-(A-ε/2)) := by
    dsimp [γ1, l]
    convert hg10 using 1 <;> ring
  have eq2 : γ (A-ε/2) = γ2 (A-ε/2) := by
    dsimp [γ2, l]
    simpa using hg20.symm
  let mid : ℝ → V := piecewise (Ioo (-a) a) γ γ1
  have hmidall := ode_piecewise_sol hloc hγ hγM hγ1' hγ1M'
    (t₀ := -(A-ε/2))
    (by
      constructor
      · exact hcenter1
      · constructor <;> linarith)
    eq1.symm
  let fin : ℝ → V := piecewise (Ioo (-(A-ε/2)-ε) a) mid γ2
  have hsubsetmid : Ioo (-(A-ε/2)-ε) a ⊆
        Ioo (-a) a ∪ Ioo (-(A-ε/2)-ε) (-(A-ε/2)+ε) := by
    intro t ht
    by_cases hleft : -a < t
    · exact Or.inl ⟨hleft, ht.2⟩
    · exact Or.inr ⟨ht.1, by linarith [show A-ε/2 < a from hlt]⟩
  have hmid : ODESolOn v mid (Ioo (-(A-ε/2)-ε) a) := by
    intro t ht
    exact hmidall.1 t (hsubsetmid ht)
  have hmidM : MapsTo mid (Ioo (-(A-ε/2)-ε) a) M := by
    intro t ht
    exact hmidall.2 (hsubsetmid ht)
  have hrightmem : (A-ε/2) ∈ Ioo (-(A-ε/2)-ε) a := by
    constructor
    · linarith [hεA, hε]
    · exact hlt
  have hrightmem' : (A-ε/2) ∈ Ioo ((A-ε/2)-ε) ((A-ε/2)+ε) := by
    constructor <;> linarith
  have heqmid : mid (A-ε/2) = γ2 (A-ε/2) := by
    change (piecewise (Ioo (-a) a) γ γ1) (A-ε/2) = _
    rw [piecewise, if_pos hcenter2]
    exact eq2
  have hfinall := ode_piecewise_sol hloc hmid hmidM hγ2' hγ2M'
    (t₀ := A-ε/2) ⟨hrightmem, hrightmem'⟩ heqmid
  have hfin0 : fin 0 = x := by
    change (piecewise (Ioo (-(A-ε/2)-ε) a) mid γ2) 0 = x
    have hzeroMid : (0:ℝ) ∈ Ioo (-(A-ε/2)-ε) a := by
      constructor
      · linarith [hεA, hε]
      · linarith [hlt, hεA, hε]
    rw [piecewise, if_pos hzeroMid]
    change (piecewise (Ioo (-a) a) γ γ1) 0 = x
    have hzeroC : (0:ℝ) ∈ Ioo (-a) a := by
      constructor <;> linarith [hlt, hεA, hε]
    rw [piecewise, if_pos hzeroC, hγ0]
  have htarget : Ioo (-(A+ε/2)) (A+ε/2) ⊆
      Ioo (-(A-ε/2)-ε) a ∪ Ioo ((A-ε/2)-ε) ((A-ε/2)+ε) := by
    intro t ht
    by_cases hb : t < a
    · left
      constructor <;> linarith [ht.1]
    · right
      constructor
      · linarith [hb, hlt, hε]
      · linarith [ht.2]
  have hnew : (A + ε/2) ∈ S := by
    refine ⟨fin, hfin0, ?_, ?_⟩
    · intro t ht
      exact hfinall.1 t (htarget ht)
    · intro t ht
      exact hfinall.2 (htarget ht)
  exact (not_lt_of_ge (le_csSup hbdd hnew)) (by linarith [hε])

end LeanEval.Geometry.LiouvilleArnold.Support

namespace LeanEval.Geometry.LiouvilleArnold.Support
open Set Function Filter

theorem compact_uniform_time
    {X : Type*} [TopologicalSpace X]
    {M : Set X} (hc : IsCompact M) (hne : M.Nonempty)
    {P : X → ℝ → Prop}
    (hmono : ∀ x : X, ∀ {u w : ℝ}, 0 < w → w ≤ u → P x u → P x w)
    (hnear : ∀ x ∈ M, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∃ e : ℝ, 0 < e ∧ ∀ y ∈ M, y ∈ W → P y e) :
    ∃ e : ℝ, 0 < e ∧ ∀ x ∈ M, P x e := by
  classical
  choose W hWo hxW e he hp using hnear
  let O : {x // x ∈ M} → Set X := fun x => W x x.property
  have hOo : ∀ j, IsOpen (O j) := by
    intro j; exact hWo _ _
  have hcov : M ⊆ ⋃ j, O j := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, hxW x hx⟩
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover O hOo hcov
  have htne : t.Nonempty := by
    by_contra hn
    have te : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨x,hx⟩ := hne
    have bad := ht hx
    simp [te] at bad
  let d : ℝ := t.inf' htne (fun j : {x // x ∈ M} => e j.1 j.2)
  have claim : ∀ (u : Finset {x // x ∈ M}) (hn : u.Nonempty),
      (∀ j ∈ u, (0:ℝ) < e j.1 j.2) →
        0 < u.inf' hn (fun j : {x // x ∈ M} => e j.1 j.2) := by
    intro u
    induction u using Finset.induction_on with
    | empty => intro hn; simp at hn
    | @insert z u hz ih =>
      intro hn H
      by_cases hu : u.Nonempty
      · rw [Finset.inf'_insert hu]
        exact lt_min (H z (by simp))
          (ih hu (by intro k hk; exact H k (by simp [hk])))
      · have hue : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu
        subst u
        simp [H z (by simp)]
  have hd : 0 < d := by
    dsimp [d]
    apply claim t htne
    intro j hj
    exact he _ _
  refine ⟨d, hd, ?_⟩
  intro x hx
  have hxunion := ht hx
  simp only [mem_iUnion] at hxunion
  obtain ⟨j,hjt,hxj⟩ := hxunion
  have hle : d ≤ e j.1 j.2 := by
    exact Finset.inf'_le _ hjt
  exact hmono x hd hle (hp j.1 j.2 x hx hxj)
end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Complete.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Kernel.lean
section

open Function Set Module

namespace LeanEval.Geometry.LiouvilleArnold.Support


theorem span_eq_ker_rows
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →ₗ[ℝ] (Fin n → ℝ))
    (hV : Module.finrank ℝ V = 2*n)
    (hA : Function.Surjective A)
    (w : Fin n → V)
    (hw : ∀ i, A (w i) = 0)
    (hli : LinearIndependent ℝ w) :
    Submodule.span ℝ (Set.range w) = LinearMap.ker A := by
  classical
  have hrange : LinearMap.range A = ⊤ := LinearMap.range_eq_top.mpr hA
  have hdim : Module.finrank ℝ (LinearMap.ker A) = n := by
    have h := LinearMap.finrank_range_add_finrank_ker A
    rw [hrange, finrank_top, Module.finrank_fin_fun, hV] at h
    omega
  have hsub : Submodule.span ℝ (Set.range w) ≤ LinearMap.ker A := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨i, rfl⟩
    exact (LinearMap.mem_ker).2 (hw i)
  have hspan : Module.finrank ℝ (Submodule.span ℝ (Set.range w)) = n := by
    simpa using (finrank_span_eq_card hli)
  apply Submodule.eq_of_le_of_finrank_eq hsub
  exact hspan.trans hdim.symm


theorem hamVec_span_ker
    {n : ℕ}
    (u : Fin n → (EuclideanSpace ℝ (Fin (2*n)) →L[ℝ] ℝ))
    (hu : LinearIndependent ℝ u)
    (hz : ∀ i j, u j (hamVec (@pstd n) (@qstd n) (u i)) = 0) :
    Submodule.span ℝ
      (Set.range (fun i : Fin n => hamVec (@pstd n) (@qstd n) (u i))) =
      LinearMap.ker (rowsMap (ι := Fin n)
        (EuclideanSpace ℝ (Fin (2*n))) u) := by
  classical
  let A := rowsMap (ι := Fin n) (EuclideanSpace ℝ (Fin (2*n))) u
  apply span_eq_ker_rows A ?_ ?_
      (fun i => hamVec (@pstd n) (@qstd n) (u i)) ?_ ?_
  · simpa using (finrank_euclideanSpace (ι := Fin (2*n)) (𝕜 := ℝ))
  · exact rowsMap_surjective u hu
  · intro i
    funext j
    exact hz i j
  · exact independent_hamVec u hu

end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Kernel.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Lie.lean
section
open scoped BigOperators ContDiff
open Function Set
namespace LeanEval.Geometry.LiouvilleArnold.Support


theorem hamVec_pair_skew {n : ℕ}
    (p q : Fin n → Fin (2*n))
    (l m : (EuclideanSpace ℝ (Fin (2*n))) →L[ℝ] ℝ) :
    m (hamVec p q l) = - l (hamVec p q m) := by
  classical
  rw [apply_hamVec p q l m, apply_hamVec p q m l]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring


theorem fderiv_hamVec_fun {n : ℕ}
    (p q : Fin n → Fin (2*n))
    {f : (EuclideanSpace ℝ (Fin (2*n))) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin (2*n)))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : EuclideanSpace ℝ (Fin (2*n))}
    (hx : x ∈ U) :
    fderiv ℝ (fun y => hamVec p q (fderiv ℝ f y)) x =
      (hamVecCLM p q).comp (fderiv ℝ (fderiv ℝ f) x) := by
  have hf' : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf'.fderiv_right (m := (1 : ℕ∞ω)) (by
      have hh : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
        change (↑(2:ℕ∞) : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top
      convert hh using 1 <;> norm_num)).differentiableAt one_ne_zero
  have hg : HasFDerivAt (fun y => hamVec p q (fderiv ℝ f y))
      ((hamVecCLM p q).comp (fderiv ℝ (fderiv ℝ f) x)) x := by
    have hlin : HasFDerivAt (hamVecCLM p q)
        (hamVecCLM p q) (fderiv ℝ f x) :=
      (hamVecCLM p q).hasFDerivAt
    simpa [Function.comp_def, hamVecCLM_apply] using
      hlin.comp x (hd.hasFDerivAt)
  exact hg.fderiv


theorem lie_hamVec_zero_of_pair
    {n : ℕ}
    {f g : (EuclideanSpace ℝ (Fin (2*n))) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin (2*n)))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hpair : ∀ y ∈ U,
      fderiv ℝ g y
        (hamVec (@pstd n) (@qstd n) (fderiv ℝ f y)) = 0)
    {x : EuclideanSpace ℝ (Fin (2*n))} (hx : x ∈ U) :
    fderiv ℝ (fun y => hamVec (@pstd n) (@qstd n) (fderiv ℝ g y)) x
        (hamVec (@pstd n) (@qstd n) (fderiv ℝ f x)) =
      fderiv ℝ (fun y => hamVec (@pstd n) (@qstd n) (fderiv ℝ f y)) x
        (hamVec (@pstd n) (@qstd n) (fderiv ℝ g x)) := by
  classical
  let L := hamVecCLM (@pstd n) (@qstd n)
  let A := fderiv ℝ f x
  let B := fderiv ℝ g x
  let HA := fderiv ℝ (fderiv ℝ f) x
  let HB := fderiv ℝ (fderiv ℝ g) x
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
  have hgx : ContDiffAt ℝ ∞ g x := hg.contDiffAt (hU.mem_nhds hx)
  have hdA : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hfx.fderiv_right (m := (1 : ℕ∞ω)) (by
      have hh : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
        change (↑(2:ℕ∞) : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top
      convert hh using 1 <;> norm_num)).differentiableAt one_ne_zero
  have hdB : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hgx.fderiv_right (m := (1 : ℕ∞ω)) (by
      have hh : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
        change (↑(2:ℕ∞) : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top
      convert hh using 1 <;> norm_num)).differentiableAt one_ne_zero
  have hsA : ∀ v w : EuclideanSpace ℝ (Fin (2*n)), HA v w = HA w v := by
    have hsym := hfx.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      change (↑(2:ℕ∞) : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
    exact hsym
  have hsB : ∀ v w : EuclideanSpace ℝ (Fin (2*n)), HB v w = HB w v := by
    have hsym := hgx.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      change (↑(2:ℕ∞) : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
    exact hsym
  let b : (EuclideanSpace ℝ (Fin (2*n))) → ℝ := fun y =>
      fderiv ℝ g y
        (hamVec (@pstd n) (@qstd n) (fderiv ℝ f y))
  have hbzero : b =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hpair y hy
  have hu : HasFDerivAt
        (fun y => hamVec (@pstd n) (@qstd n) (fderiv ℝ f y))
        (L.comp HA) x := by
    have hlin : HasFDerivAt L L (fderiv ℝ f x) := L.hasFDerivAt
    simpa [L, HA, Function.comp_def, hamVecCLM_apply] using
      hlin.comp x hdA.hasFDerivAt
  have hc : HasFDerivAt (fderiv ℝ g) HB x := hdB.hasFDerivAt
  have hbder : fderiv ℝ b x =
      (B.comp (L.comp HA)) + HB.flip (L A) := by
    have hcalc := hc.clm_apply hu
    have hh : HasFDerivAt b
        ((B.comp (L.comp HA)) + HB.flip (L A)) x := by
      simpa [b, A, B, HA, HB, L, Function.comp_def, hamVecCLM_apply] using hcalc
    exact hh.fderiv
  have hb0 : fderiv ℝ b x = 0 := by
    have hh := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hbzero
    simpa using hh
  have hid (w : EuclideanSpace ℝ (Fin (2*n))) :
        B (L (HA w)) + (HB w) (L A) = 0 := by
    have he := congrArg (fun T :
        (EuclideanSpace ℝ (Fin (2*n))) →L[ℝ] ℝ => T w)
        (hbder.symm.trans hb0)
    simpa [ContinuousLinearMap.add_apply, L, A, B, HA, HB,
      hamVecCLM_apply] using he
  have hcov : HB (L A) = HA (L B) := by
    apply ContinuousLinearMap.ext
    intro w
    have hz := hid w
    have hsk : B (L (HA w)) = - (HA w) (L B) := by
      simpa [L, hamVecCLM_apply]
        using (hamVec_pair_skew (@pstd n) (@qstd n) (HA w) B)
    rw [hsk] at hz
    rw [hsB w (L A), hsA w (L B)] at hz
    linarith
  rw [fderiv_hamVec_fun (@pstd n) (@qstd n) hU hg hx,
      fderiv_hamVec_fun (@pstd n) (@qstd n) hU hf hx]
  change L (HB (L A)) = L (HA (L B))
  rw [hcov]
end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Lie.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Boxes.lean
section

open Set Function Filter Metric
open scoped Topology NNReal
namespace LeanEval.Geometry.LiouvilleArnold.Support

open ODE

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]




theorem exists_picard_box_in_open
    {v : V → V} {U : Set V} (hU : IsOpen U) {y : V} (hy : y ∈ U)
    (hv : ContDiffAt ℝ 1 v y) :
    ∃ W : Set V, IsOpen W ∧ y ∈ W ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ W,
        ∃ α : ℝ → V, α 0 = z ∧
          (∀ t ∈ Ioo (-ε) ε, HasDerivAt α (v (α t)) t) ∧
          MapsTo α (Ioo (-ε) ε) U := by
  obtain ⟨K, s, hs, hLip⟩ := hv.exists_lipschitzOnWith
  have hsn : s ∩ U ∈ nhds y := inter_mem hs (hU.mem_nhds hy)
  obtain ⟨d, hd, hdsub⟩ := (Metric.mem_nhds_iff.mp hsn)
  have hsmall : closedBall y (d / 2) ⊆ s ∩ U :=
    subset_trans (closedBall_subset_ball (half_lt_self hd)) hdsub
  have hsmall_s : closedBall y (d / 2) ⊆ s :=
    subset_trans hsmall inter_subset_left
  have hsmall_U : closedBall y (d / 2) ⊆ U :=
    subset_trans hsmall inter_subset_right
  have hb (x : V) (hx : x ∈ closedBall y (d / 2)) :
      ‖v x‖ ≤ K * d + ‖v y‖ + 1 := by
    calc
      ‖v x‖ ≤ ‖v x - v y‖ + ‖v y‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x - y‖ + ‖v y‖ := by
        gcongr
        apply hLip.norm_sub_le
        · exact hsmall_s hx
        · exact mem_of_mem_nhds hs
      _ ≤ K * d + ‖v y‖ := by
        gcongr
        rw [← mem_closedBall_iff_norm]
        exact closedBall_subset_closedBall (half_le_self (le_of_lt hd)) hx
      _ ≤ K * d + ‖v y‖ + 1 := le_add_of_nonneg_right (by norm_num)
  let Lr : ℝ := K * d + ‖v y‖ + 1
  have hLr : 0 < Lr := by
    dsimp [Lr]
    have : 0 ≤ (K : ℝ) * d := mul_nonneg K.2 (le_of_lt hd)
    linarith [norm_nonneg (v y)]
  let A : ℝ≥0 := ⟨d / 2, (half_pos hd).le⟩
  let R : ℝ≥0 := A / 2
  let LL : ℝ≥0 := ⟨Lr, (le_of_lt hLr)⟩
  let eps : ℝ := d / Lr / 2 / 2
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have hR : 0 < (R : ℝ) := by
    dsimp [R, A]
    exact half_pos (half_pos hd)
  have hLL : (LL : ℝ) = Lr := rfl
  have hA : (A : ℝ) = d / 2 := rfl
  have hR' : (R : ℝ) = d / 2 / 2 := by rfl
  have hm : (LL : ℝ) *
        max ((0 + eps) - (0:ℝ)) ((0:ℝ) - (0 - eps)) ≤
          (A : ℝ) - (R : ℝ) := by
    have hmx : max ((0 + eps) - (0:ℝ)) ((0:ℝ) - (0 - eps)) = eps := by
      simp
    rw [hmx, hLL, hA, hR']
    have hne : Lr ≠ 0 := ne_of_gt hLr
    have hval : Lr * eps = d / 4 := by
      dsimp [eps]
      field_simp
      <;> norm_num
    rw [hval]
    ring_nf
    linarith
  let tcentre : (Icc (0 - eps) (0 + eps)) :=
    ⟨0, by constructor <;> linarith [heps]⟩
  have hLipA : LipschitzOnWith K v (closedBall y (A : ℝ)) := by
    rw [hA]
    exact hLip.mono hsmall_s
  have hbA : ∀ x ∈ closedBall y (A : ℝ), ‖v x‖ ≤ LL := by
    change ∀ x ∈ closedBall y (A : ℝ), ‖v x‖ ≤ (LL : ℝ)
    rw [hA, hLL]
    exact hb
  have hpl : IsPicardLindelof (fun _ : ℝ => v)
        (tmin := 0 - eps) (tmax := 0 + eps) tcentre y A R LL K := by
    exact IsPicardLindelof.of_time_independent hbA hLipA (by
      simpa [tcentre] using hm)
  refine ⟨Metric.ball y (R : ℝ), Metric.isOpen_ball,
    Metric.mem_ball_self hR, eps, heps, ?_⟩
  intro z hz
  have hzr : z ∈ closedBall y (R : ℝ) := ball_subset_closedBall hz
  classical
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpl hzr
  refine ⟨α.compProj, ?_, ?_, ?_⟩
  · -- initial value of the fixed point
    change α.compProj (tcentre : ℝ) = z
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    have ht' : t ∈ Ioo (0 - eps) (0 + eps) := by
      simpa using ht
    have hh : HasDerivWithinAt α.compProj
          ((fun _ : ℝ => v) t (α.compProj t))
          (Icc (0 - eps) (0 + eps)) t := by
      apply hasDerivWithinAt_picard_Icc tcentre.2 hpl.continuousOn_uncurry
        α.continuous_compProj.continuousOn
        (fun _ ht'' => α.compProj_mem_closedBall hpl.mul_max_le)
        z (Ioo_subset_Icc_self ht') |>.congr_of_mem _ (Ioo_subset_Icc_self ht')
      intro t' ht''
      nth_rw 1 [← hα]
      rw [ODE.FunSpace.compProj_of_mem ht'', ODE.FunSpace.next_apply]
    have hn := hh.hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)
    simpa using hn
  · intro t ht
    have hvball : α.compProj t ∈ closedBall y (A : ℝ) :=
      α.compProj_mem_closedBall hpl.mul_max_le
    rw [hA] at hvball
    exact hsmall_U hvball
end LeanEval.Geometry.LiouvilleArnold.Support


end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Boxes.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/GlobalAction.lean
section

open Set Function Filter Metric
open scoped Topology
namespace LeanEval.Geometry.LiouvilleArnold.Support

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]


theorem ode_eq_of_global_mem
    {v : V → V} {M : Set V}
    (hloc : ∀ x ∈ M, ∃ K : NNReal, ∃ W ∈ nhds x, LipschitzOnWith K v W)
    {α β : ℝ → V} {t₀ : ℝ}
    (hα : ∀ t : ℝ, HasDerivAt α (v (α t)) t)
    (hαM : ∀ t : ℝ, α t ∈ M)
    (hβ : ∀ t : ℝ, HasDerivAt β (v (β t)) t)
    (hβM : ∀ t : ℝ, β t ∈ M)
    (h0 : α t₀ = β t₀) : α = β := by
  funext t
  let R : ℝ := |t| + |t₀| + 1
  have hRp : 0 < R := by
    dsimp [R]
    positivity
  have ht : t ∈ Ioo (-R) R := by
    rw [mem_Ioo, ← abs_lt]
    dsimp [R]
    linarith [abs_nonneg t₀]
  have ht0 : t₀ ∈ Ioo (-R) R := by
    rw [mem_Ioo, ← abs_lt]
    dsimp [R]
    linarith [abs_nonneg t]
  exact ode_eqOn_Ioo_of_mem hloc
    (a := -R) (b := R) (t₀ := t₀)
    (α := α) (β := β)
    (by intro q hq; exact hα q)
    (by intro q hq; exact hαM q)
    (by intro q hq; exact hβ q)
    (by intro q hq; exact hβM q)
    ht0 h0 ht


theorem exists_global_flow_action
    {v : V → V} {M : Set V}
    (hloc : ∀ x ∈ M, ∃ K : NNReal, ∃ W ∈ nhds x, LipschitzOnWith K v W)
    (hcomplete : ∀ x : {z : V // z ∈ M},
      ∃ γ : ℝ → V, γ 0 = (x : V) ∧
        (∀ t : ℝ, HasDerivAt γ (v (γ t)) t) ∧
        (∀ t : ℝ, γ t ∈ M)) :
    ∃ Φ : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M}),
      (∀ x, Φ 0 x = x) ∧
      (∀ (x : {z : V // z ∈ M}) (t : ℝ),
        HasDerivAt (fun s : ℝ => ((Φ s x : {z : V // z ∈ M}) : V))
          (v (Φ t x : V)) t) ∧
      (∀ t u (x : {z : V // z ∈ M}), Φ (t + u) x = Φ t (Φ u x)) ∧
      (∀ t : ℝ, Function.Bijective (Φ t)) := by
  classical
  choose γ hγ0 hγd hγM using hcomplete
  let Φ : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M}) :=
    fun t x => ⟨γ x t, hγM x t⟩
  have hzero : ∀ x, Φ 0 x = x := by
    intro x
    apply Subtype.ext
    exact hγ0 x
  have hder : ∀ (x : {z : V // z ∈ M}) (t : ℝ),
        HasDerivAt (fun s : ℝ => ((Φ s x : {z : V // z ∈ M}) : V))
          (v (Φ t x : V)) t := by
    intro x t
    exact hγd x t
  have hadd : ∀ t u (x : {z : V // z ∈ M}), Φ (t + u) x = Φ t (Φ u x) := by
    intro t u x
    let a : ℝ → V := γ (Φ u x)
    let b : ℝ → V := fun s => γ x (s + u)
    have ha : ∀ s : ℝ, HasDerivAt a (v (a s)) s := by
      intro s
      exact hγd (Φ u x) s
    have ham : ∀ s : ℝ, a s ∈ M := by
      intro s
      exact hγM (Φ u x) s
    have hb : ∀ s : ℝ, HasDerivAt b (v (b s)) s := by
      intro s
      have hud : HasDerivAt (fun r : ℝ => r + u) (1 : ℝ) s := by
        simpa using (hasDerivAt_id s).add_const u
      simpa [b, Function.comp_def] using ((hγd x (s + u)).scomp s hud)
    have hbm : ∀ s : ℝ, b s ∈ M := by
      intro s
      exact hγM x (s + u)
    have hab0 : a 0 = b 0 := by
      change γ (Φ u x) 0 = γ x (0 + u)
      have h0' := hγ0 (Φ u x)
      simpa [Φ] using congrArg Subtype.val (hzero (Φ u x))
    have hab : a = b :=
      ode_eq_of_global_mem hloc (α := a) (β := b) (t₀ := 0)
        ha ham hb hbm hab0
    have hval := congrArg (fun f : ℝ → V => f t) hab
    apply Subtype.ext
    exact hval.symm
  refine ⟨Φ, hzero, hder, hadd, ?_⟩
  intro t
  have hinv₁ : ∀ x : {z : V // z ∈ M}, Φ (-t) (Φ t x) = x := by
    intro x
    rw [← hadd (-t) t x]
    norm_num
    exact hzero x
  have hinv₂ : ∀ x : {z : V // z ∈ M}, Φ t (Φ (-t) x) = x := by
    intro x
    rw [← hadd t (-t) x]
    norm_num
    exact hzero x
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have := congrArg (Φ (-t)) hxy
    simpa [hinv₁ x, hinv₁ y] using this
  · intro y
    exact ⟨Φ (-t) y, hinv₂ y⟩


end LeanEval.Geometry.LiouvilleArnold.Support


end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/GlobalAction.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/FlowCommute.lean
section

open Set Function Filter

namespace LeanEval.Geometry.LiouvilleArnold.Support
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]



theorem commute_of_deriv_zero_orbits
    {M : Set V} {v w : V → V}
    {φ ψ : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M})}
    (hloc : ∀ z ∈ M, ∃ K : NNReal, ∃ W ∈ nhds z, LipschitzOnWith K w W)
    (hψ0 : ∀ z : {z : V // z ∈ M}, ψ 0 z = z)
    (hψD : ∀ (z : {z : V // z ∈ M}) (u : ℝ),
      HasDerivAt (fun r : ℝ => ((ψ r z : {z : V // z ∈ M}) : V))
        (w (ψ u z : V)) u)
    (hψadd : ∀ a b (z : {z : V // z ∈ M}), ψ (a + b) z = ψ a (ψ b z))
    (hd0 : ∀ (T : ℝ) (z : {z : V // z ∈ M}),
      HasDerivAt
        (fun r : ℝ => ((φ T (ψ r z) : {z : V // z ∈ M}) : V))
        (w (φ T z : V)) 0) :
    ∀ (T u : ℝ) (z : {z : V // z ∈ M}),
      φ T (ψ u z) = ψ u (φ T z) := by
  have htrans (T : ℝ) (z : {z : V // z ∈ M}) (u : ℝ) :
      HasDerivAt
        (fun r : ℝ => ((φ T (ψ r z) : {z : V // z ∈ M}) : V))
        (w (φ T (ψ u z) : V)) u := by
    have hz := hd0 T (ψ u z)
    have ht : HasDerivAt (fun r : ℝ => r - u) (1 : ℝ) u := by
      simpa using (hasDerivAt_id u).sub_const u
    have hz' : HasDerivAt
        (fun r : ℝ => ((φ T (ψ r (ψ u z) ) : {z : V // z ∈ M}) : V))
          (w (φ T (ψ u z) : V)) ((fun r : ℝ => r - u) u) := by
      simpa using hz
    have hc := @HasDerivAt.scomp ℝ _ V _ _ u ℝ _ _ _ _ (fun r : ℝ => r - u) 1 _ _ hz' ht
    have heq : (fun r : ℝ =>
          ((φ T (ψ (r - u) (ψ u z)) : {z : V // z ∈ M}) : V)) =
        (fun r : ℝ =>
          ((φ T (ψ r z) : {z : V // z ∈ M}) : V)) := by
      funext r
      have hsum : (r - u) + u = r := by ring
      rw [← hψadd]
      rw [hsum]
    have hc' : HasDerivAt
        (fun r : ℝ => ((φ T (ψ (r-u) (ψ u z)) : {z : V // z ∈ M}) : V))
          (w (φ T (ψ u z) : V)) u := by
      simpa [Function.comp_def] using hc
    rw [heq] at hc'
    exact hc' 
  intro T u z
  let a : ℝ → V := fun r => ((φ T (ψ r z) : {z : V // z ∈ M}) : V)
  let b : ℝ → V := fun r => ((ψ r (φ T z) : {z : V // z ∈ M}) : V)
  have ha : ∀ r : ℝ, HasDerivAt a (w (a r)) r := by
    intro r
    simpa [a] using (htrans T z r)
  have hb : ∀ r : ℝ, HasDerivAt b (w (b r)) r := by
    intro r
    simpa [b] using (hψD (φ T z) r)
  have haM : ∀ r : ℝ, a r ∈ M := by
    intro r
    exact (φ T (ψ r z)).property
  have hbM : ∀ r : ℝ, b r ∈ M := by
    intro r
    exact (ψ r (φ T z)).property
  have hab0 : a 0 = b 0 := by
    simpa [a, b, hψ0]
  have hh : a = b :=
    ode_eq_of_global_mem (v:=w) (M:=M) hloc
      (α := a) (β := b) (t₀ := 0) ha haM hb hbM hab0
  have hv := congrArg (fun f : ℝ → V => f u) hh
  exact Subtype.ext (by simpa [a,b] using hv)

end LeanEval.Geometry.LiouvilleArnold.Support


namespace LeanEval.Geometry.LiouvilleArnold.Support
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem deriv_zero_self_of_flow_add
    {M : Set V} {w : V → V}
    {φ : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M})}
    (hD : ∀ (z : {z : V // z ∈ M}) (t : ℝ),
      HasDerivAt (fun r : ℝ => ((φ r z : {z : V // z ∈ M}) : V))
        (w (φ t z : V)) t)
    (hadd : ∀ a b (z : {z : V // z ∈ M}), φ (a+b) z = φ a (φ b z)) :
    ∀ (T : ℝ) (z : {z : V // z ∈ M}),
      HasDerivAt
        (fun r : ℝ => ((φ T (φ r z) : {z : V // z ∈ M}) : V))
        (w (φ T z : V)) 0 := by
  intro T z
  have ho : HasDerivAt
      (fun q : ℝ => ((φ q z : {z : V // z ∈ M}) : V))
      (w (φ T z : V)) ((fun r : ℝ => T + r) 0) := by
    simpa using (hD z T)
  have hi : HasDerivAt (fun r : ℝ => T + r) (1 : ℝ) 0 := by
    simpa using ((hasDerivAt_id (x := (0:ℝ))).const_add T)
  have hc := @HasDerivAt.scomp ℝ _ V _ _ 0 ℝ _ _ _ _
      (fun r : ℝ => T + r) 1 _ _ ho hi
  have heq :
      (fun q : ℝ => ((φ q z : {z : V // z ∈ M}) : V)) ∘
        (fun r : ℝ => T + r) =
      (fun r : ℝ => ((φ T (φ r z) : {z : V // z ∈ M}) : V)) := by
    funext r
    have h := hadd T r z
    simpa [Function.comp_def] using
      congrArg (fun zz : {z : V // z ∈ M} => (zz : V)) h
  rw [heq] at hc
  simpa using hc
end LeanEval.Geometry.LiouvilleArnold.Support


namespace LeanEval.Geometry.LiouvilleArnold.Support
variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem commute_family_of_mixed_zero
    [DecidableEq J] {M : Set V}
    (X : J → V → V)
    (Φ : J → ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M}))
    (hloc : ∀ j : J, ∀ z ∈ M, ∃ K : NNReal, ∃ W ∈ nhds z,
      LipschitzOnWith K (X j) W)
    (h0 : ∀ j (z : {z : V // z ∈ M}), Φ j 0 z = z)
    (hD : ∀ j (z : {z : V // z ∈ M}) (u : ℝ),
      HasDerivAt (fun r : ℝ => ((Φ j r z : {z : V // z ∈ M}) : V))
        (X j (Φ j u z : V)) u)
    (hadd : ∀ j a b (z : {z : V // z ∈ M}),
      Φ j (a+b) z = Φ j a (Φ j b z))
    (hmixed : ∀ i j : J, i ≠ j → ∀ T : ℝ,
       ∀ z : {z : V // z ∈ M},
       HasDerivAt
         (fun r : ℝ => ((Φ i T (Φ j r z) : {z : V // z ∈ M}) : V))
         (X j (Φ i T z : V)) 0) :
    ∀ i j : J, ∀ T u : ℝ, ∀ z : {z : V // z ∈ M},
      Φ i T (Φ j u z) = Φ j u (Φ i T z) := by
  have hz : ∀ i j : J, ∀ T : ℝ, ∀ z : {z : V // z ∈ M},
       HasDerivAt
         (fun r : ℝ => ((Φ i T (Φ j r z) : {z : V // z ∈ M}) : V))
         (X j (Φ i T z : V)) 0 := by
    intro i j T z
    by_cases h : i = j
    · subst j
      exact deriv_zero_self_of_flow_add (M:=M) (w:=X i)
        (φ:=Φ i) (hD i) (hadd i) T z
    · exact hmixed i j h T z
  intro i j
  exact commute_of_deriv_zero_orbits (v:= X i) (M:=M) (w:=X j)
    (φ:=Φ i) (ψ:=Φ j) (hloc j) (h0 j) (hD j) (hadd j) (hz i j)
end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/FlowCommute.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Joint.lean
section
open Set Function Filter Metric
open scoped Topology
namespace LeanEval.Geometry.LiouvilleArnold.Support
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]


theorem dist_flow_le_exp_abs
    {v : V → V} {M : Set V}
    (K : NNReal) (hL : LipschitzOnWith K v M)
    {Φ : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M})}
    (h0 : ∀ (x : {z : V // z ∈ M}), Φ 0 x = x)
    (hD : ∀ (x : {z : V // z ∈ M}) (t : ℝ),
      HasDerivAt (fun s : ℝ => ((Φ s x : {z : V // z ∈ M}) : V))
        (v (Φ t x : V)) t) :
    ∀ (T : ℝ) (x y : {z : V // z ∈ M}),
      dist (Φ T x : V) (Φ T y : V) ≤
        Real.exp ((K : ℝ) * |T|) * dist (x : V) (y : V) := by
  intro T x y
  by_cases hT : 0 ≤ T
  · have hcurv (z : {z : V // z ∈ M}) :
        Continuous (fun s : ℝ => ((Φ s z : {z : V // z ∈ M}) : V)) := by
        rw [continuous_iff_continuousAt]
        intro s
        exact (hD z s).continuousAt
    have hb := dist_le_of_trajectories_ODE_of_mem
      (v := fun _ : ℝ => v) (s := fun _ : ℝ => M)
      (K := K) (a := (0 : ℝ)) (b := T)
      (f := fun q : ℝ => (Φ q x : V))
      (g := fun q : ℝ => (Φ q y : V))
      (δ := dist (x : V) (y : V))
      (fun q hq => hL)
      (hcurv x).continuousOn
      (by intro q hq; exact (hD x q).hasDerivWithinAt)
      (by intro q hq; exact (Φ q x).property)
      (hcurv y).continuousOn
      (by intro q hq; exact (hD y q).hasDerivWithinAt)
      (by intro q hq; exact (Φ q y).property)
      (by simp [h0])
    have hz := hb T ⟨hT, le_rfl⟩
    rw [abs_of_nonneg hT]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hz
  · have hn : 0 ≤ -T := by linarith
    let w : V → V := fun z => - v z
    let Ψ : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M}) :=
      fun s z => Φ (-s) z
    have hLw : LipschitzOnWith K w M := by
      change LipschitzOnWith K (-v) M
      exact hL.neg
    have hΨ0 : ∀ z : {z : V // z ∈ M}, Ψ 0 z = z := by
      intro z; simpa [Ψ] using h0 z
    have hΨD : ∀ (z : {z : V // z ∈ M}) (s : ℝ),
        HasDerivAt (fun r : ℝ => ((Ψ r z : {z : V // z ∈ M}) : V))
          (w (Ψ s z : V)) s := by
      intro z s
      have hneg : HasDerivAt (fun r : ℝ => -r) (-1 : ℝ) s := hasDerivAt_neg s
      have hc := (hD z (-s)).scomp s hneg
      simpa [Ψ, w, Function.comp_def, neg_one_smul ℝ] using hc
    have hcurv (z : {z : V // z ∈ M}) :
        Continuous (fun s : ℝ => ((Ψ s z : {z : V // z ∈ M}) : V)) := by
        rw [continuous_iff_continuousAt]
        intro s
        exact (hΨD z s).continuousAt
    have hb := dist_le_of_trajectories_ODE_of_mem
      (v := fun _ : ℝ => w) (s := fun _ : ℝ => M)
      (K := K) (a := (0 : ℝ)) (b := -T)
      (f := fun q : ℝ => (Ψ q x : V))
      (g := fun q : ℝ => (Ψ q y : V))
      (δ := dist (x : V) (y : V))
      (fun q hq => hLw)
      (hcurv x).continuousOn
      (by intro q hq; exact (hΨD x q).hasDerivWithinAt)
      (by intro q hq; exact (Ψ q x).property)
      (hcurv y).continuousOn
      (by intro q hq; exact (hΨD y q).hasDerivWithinAt)
      (by intro q hq; exact (Ψ q y).property)
      (by simp [hΨ0])
    have hz := hb (-T) ⟨hn, le_rfl⟩
    have hab : |T| = -T := abs_of_neg (lt_of_not_ge hT)
    rw [hab]
    simpa [Ψ, w, mul_comm, mul_left_comm, mul_assoc] using hz


theorem continuous_joint_flow
    {v : V → V} {M : Set V}
    (K : NNReal) (hL : LipschitzOnWith K v M)
    {Φ : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M})}
    (h0 : ∀ (x : {z : V // z ∈ M}), Φ 0 x = x)
    (hD : ∀ (x : {z : V // z ∈ M}) (t : ℝ),
      HasDerivAt (fun s : ℝ => ((Φ s x : {z : V // z ∈ M}) : V))
        (v (Φ t x : V)) t) :
    Continuous (fun p : ℝ × {z : V // z ∈ M} => Φ p.1 p.2) := by
  have hbound := dist_flow_le_exp_abs (M:=M) (v:=v) K hL h0 hD
  rw [continuous_iff_continuousAt]
  intro p
  rcases p with ⟨t,x⟩
  have horb : Continuous (fun r : ℝ => ((Φ r x : {z : V // z ∈ M}) : V)) := by
    rw [continuous_iff_continuousAt]
    intro r
    exact (hD x r).continuousAt
  let C : ℝ := Real.exp ((K : ℝ) * (|t| + 1))
  have hCp : 0 < C := Real.exp_pos _
  have hev : ∀ᶠ r in nhds t, Real.exp ((K : ℝ) * |r|) ≤ C := by
    have hloc : ∀ᶠ r : ℝ in nhds t, |r| < |t| + 1 := by
      have hc : ContinuousAt (fun r : ℝ => |r|) t :=
        (continuous_abs.continuousAt)
      have hmem : |t| ∈ Iio (|t| + 1) := by simp
      exact hc (isOpen_Iio.mem_nhds hmem)
    filter_upwards [hloc] with r hr
    have hm : (K : ℝ) * |r| ≤ (K : ℝ) * (|t| + 1) :=
      mul_le_mul_of_nonneg_left (le_of_lt hr) (by exact_mod_cast K.2)
    exact Real.exp_le_exp.mpr hm
  have hcontV : ContinuousAt
      (fun p : ℝ × {z : V // z ∈ M} => ((Φ p.1 p.2 : {z : V // z ∈ M}) : V))
      (t,x) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    have hεC : 0 < ε / (2*C) := by positivity
    have hA : ∀ᶠ p : ℝ × {z : V // z ∈ M} in 𝓝 (t,x),
        Real.exp ((K : ℝ) * |p.1|) ≤ C :=
      (@continuousAt_fst ℝ {z : V // z ∈ M} _ _ (t,x)).tendsto.eventually hev
    have htend : Tendsto
        (fun r : ℝ => ((Φ r x : {z : V // z ∈ M}) : V))
        (𝓝 t) (𝓝 ((Φ t x : {z : V // z ∈ M}) : V)) :=
      horb.continuousAt
    have hB' : ∀ᶠ r : ℝ in 𝓝 t,
        dist (Φ r x : V) (Φ t x : V) < ε / 2 :=
      (Metric.tendsto_nhds.1 htend) _ hε2
    have hB : ∀ᶠ p : ℝ × {z : V // z ∈ M} in 𝓝 (t,x),
        dist (Φ p.1 x : V) (Φ t x : V) < ε / 2 :=
      (@continuousAt_fst ℝ {z : V // z ∈ M} _ _ (t,x)).tendsto.eventually hB'
    have hY' : ∀ᶠ y : {z : V // z ∈ M} in 𝓝 x,
        dist (y : V) (x : V) < ε / (2*C) := by
      have ht : Tendsto (fun y : {z : V // z ∈ M} => (y : V))
          (𝓝 x) (𝓝 (x : V)) := continuous_subtype_val.continuousAt
      exact (Metric.tendsto_nhds.1 ht) _ hεC
    have hY : ∀ᶠ p : ℝ × {z : V // z ∈ M} in 𝓝 (t,x),
        dist (p.2 : V) (x : V) < ε / (2*C) :=
      (@continuousAt_snd ℝ {z : V // z ∈ M} _ _ (t,x)).tendsto.eventually hY'
    filter_upwards [hA, hB, hY] with p hpA hpB hpY
    change dist (Φ p.1 p.2 : V) (Φ t x : V) < ε
    calc
      dist (Φ p.1 p.2 : V) (Φ t x : V) ≤
          dist (Φ p.1 p.2 : V) (Φ p.1 x : V) +
            dist (Φ p.1 x : V) (Φ t x : V) := dist_triangle _ _ _
      _ ≤ (Real.exp ((K : ℝ) * |p.1|) * dist (p.2 : V) (x : V)) +
            dist (Φ p.1 x : V) (Φ t x : V) :=
        add_le_add_left (hbound p.1 p.2 x) _
      _ < ε := by
        have hfirst : Real.exp ((K : ℝ) * |p.1|) * dist (p.2 : V) (x : V)
              < ε / 2 := by
          calc
            Real.exp ((K : ℝ) * |p.1|) * dist (p.2 : V) (x : V) ≤
                C * dist (p.2 : V) (x : V) :=
              mul_le_mul_of_nonneg_right hpA dist_nonneg
            _ < C * (ε / (2*C)) :=
              (mul_lt_mul_of_pos_left hpY hCp)
            _ = ε / 2 := by field_simp
        linarith

  exact tendsto_subtype_rng.2 hcontV
end LeanEval.Geometry.LiouvilleArnold.Support

namespace LeanEval.Geometry.LiouvilleArnold.Support
open Set Function Filter Metric
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem continuous_joint_flow_of_compact
    {v : V → V} {M : Set V} (hM : IsCompact M)
    (hloc : ∀ x ∈ M, ∃ K : NNReal, ∃ W ∈ nhds x, LipschitzOnWith K v W)
    {Φ : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M})}
    (h0 : ∀ (x : {z : V // z ∈ M}), Φ 0 x = x)
    (hD : ∀ (x : {z : V // z ∈ M}) (t : ℝ),
      HasDerivAt (fun s : ℝ => ((Φ s x : {z : V // z ∈ M}) : V))
        (v (Φ t x : V)) t) :
    Continuous (fun p : ℝ × {z : V // z ∈ M} => Φ p.1 p.2) := by
  have hloc' : LocallyLipschitzOn M v := by
    intro x hx
    obtain ⟨K,W,hW,hL⟩ := hloc x hx
    exact ⟨K,W, mem_nhdsWithin_of_mem_nhds hW, hL⟩
  obtain ⟨K,hK⟩ := hloc'.exists_lipschitzOnWith_of_compact hM
  exact continuous_joint_flow (M:=M) (v:=v) K hK h0 hD
end LeanEval.Geometry.LiouvilleArnold.Support

namespace LeanEval.Geometry.LiouvilleArnold.Support
open Set Function Filter
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem field_along_curve_variation
    {U : Set V} (hU : IsOpen U)
    {v w : V → V}
    (hv : DifferentiableOn ℝ v U)
    (hw : DifferentiableOn ℝ w U)
    (hbr : ∀ z ∈ U, fderiv ℝ w z (v z) = fderiv ℝ v z (w z))
    {α : ℝ → V}
    (hα : ∀ t : ℝ, HasDerivAt α (v (α t)) t)
    (hmem : ∀ t : ℝ, α t ∈ U) :
    ∀ t : ℝ, HasDerivAt (fun s : ℝ => w (α s))
      (fderiv ℝ v (α t) (w (α t))) t := by
  intro t
  have hw' : HasFDerivAt w (fderiv ℝ w (α t)) (α t) :=
    hw.hasFDerivAt (hU.mem_nhds (hmem t))
  have hc := hw'.comp_hasDerivAt t (hα t)
  simpa [Function.comp_def, hbr (α t) (hmem t)] using hc
end LeanEval.Geometry.LiouvilleArnold.Support


end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Joint.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/InitialVariation.lean
section
open Set Function Filter Metric
open scoped Topology ContDiff
namespace LeanEval.Geometry.LiouvilleArnold.Support
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]


theorem compact_c1_remainder
    {A U : Set V} (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U)
    {f : V → V} (hf : DifferentiableOn ℝ f U)
    (hc : ContinuousOn (fderiv ℝ f) U) :
    ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ A, ∀ y ∈ A, dist y x < ρ →
        ‖f y - f x - fderiv ℝ f x (y-x)‖ ≤ ε * ‖y-x‖ := by
  classical
  intro ε hε
  obtain ⟨d, hd, hdU⟩ := hA.exists_cthickening_subset_open hU hAU
  let B : Set V := Metric.cthickening (d/2) A
  have hd2 : 0 < d/2 := by linarith
  have hBc : IsCompact B := by
    dsimp [B]
    exact hA.cthickening
  have hBU : B ⊆ U := by
    intro z hz
    exact hdU (Metric.cthickening_mono (by linarith : d/2 ≤ d) A hz)
  have hdu : UniformContinuousOn (fderiv ℝ f) B :=
    hBc.uniformContinuousOn_of_continuous (hc.mono hBU)
  obtain ⟨r, hr, hsmall⟩ :=
    (Metric.uniformContinuousOn_iff.1 hdu) ε hε
  let ρ : ℝ := min (d/2) r
  have hρ : 0 < ρ := lt_min hd2 hr
  refine ⟨ρ, hρ, ?_⟩
  intro x hx y hy hxy
  have hxr : dist y x < r := lt_of_lt_of_le hxy (min_le_right _ _)
  have hxd : dist y x < d/2 := lt_of_lt_of_le hxy (min_le_left _ _)
  have hxB : x ∈ B := by
    dsimp [B]
    exact Metric.self_subset_cthickening A hx
  have hyB : y ∈ B := by
    dsimp [B]
    exact Metric.self_subset_cthickening A hy
  let s : Set V := segment ℝ x y
  have hsconv : Convex ℝ s := convex_segment _ _
  have hsB : s ⊆ B := by
    intro p hp
    have hp' := norm_sub_le_of_mem_segment hp
    have hpd : dist p x ≤ dist y x := by
      simpa [dist_eq_norm] using hp'
    dsimp [B]
    exact Metric.mem_cthickening_of_dist_le p x (d/2) A hx
      (hpd.trans (le_of_lt hxd))
  have hderclose : ∀ p ∈ s,
        ‖fderiv ℝ f p - fderiv ℝ f x‖ ≤ ε := by
    intro p hp
    have hpB := hsB hp
    have hpd0 : dist p x ≤ dist y x := by
      have hp' := norm_sub_le_of_mem_segment hp
      simpa [dist_eq_norm] using hp'
    have hpr : dist p x < r := lt_of_le_of_lt hpd0 hxr
    have h := hsmall p hpB x hxB hpr
    exact le_of_lt (by simpa [dist_eq_norm] using h)
  let g : V → V := fun p => f p - fderiv ℝ f x p
  let g' : V → (V →L[ℝ] V) := fun p => fderiv ℝ f p - fderiv ℝ f x
  have hgd : ∀ p ∈ s, HasFDerivWithinAt g (g' p) s p := by
    intro p hp
    have hpU : p ∈ U := hBU (hsB hp)
    have hf' : HasFDerivAt f (fderiv ℝ f p) p :=
      (hf p hpU).differentiableAt (hU.mem_nhds hpU) |>.hasFDerivAt
    have hlin : HasFDerivAt (fun q : V => fderiv ℝ f x q)
        (fderiv ℝ f x) p := (fderiv ℝ f x).hasFDerivAt
    exact (hf'.sub hlin).hasFDerivWithinAt
  have hbound : ∀ p ∈ s, ‖g' p‖ ≤ ε := by
    intro p hp
    exact hderclose p hp
  have hxs : x ∈ s := left_mem_segment ℝ x y
  have hys : y ∈ s := right_mem_segment ℝ x y
  have hm := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (C := ε) hgd hbound hsconv hxs hys
  dsimp [g] at hm
  simpa [map_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hm
end LeanEval.Geometry.LiouvilleArnold.Support


namespace LeanEval.Geometry.LiouvilleArnold.Support
open Set Function Filter Metric
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]


theorem compact_remainder_along_complete_orbits
    {M U : Set V} (hM : IsCompact M) (hU : IsOpen U) (hsub : M ⊆ U)
    {v : V → V} (hv : DifferentiableOn ℝ v U)
    (hc : ContinuousOn (fderiv ℝ v) U)
    (L : NNReal) (hL : LipschitzOnWith L v M)
    {Φ : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M})}
    (h0 : ∀ x : {z : V // z ∈ M}, Φ 0 x = x)
    (hD : ∀ (x : {z : V // z ∈ M}) (t : ℝ),
      HasDerivAt (fun s : ℝ => ((Φ s x : {z : V // z ∈ M}) : V))
        (v (Φ t x : V)) t) :
    ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 0 ≤ R →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (x y : {z : V // z ∈ M}), dist (y:V) (x:V) < δ →
          ∀ t : ℝ, |t| ≤ R →
            ‖v (Φ t y : V) - v (Φ t x : V) -
                fderiv ℝ v (Φ t x : V)
                  ((Φ t y : V) - (Φ t x : V))‖ ≤
              ε * ‖(Φ t y : V) - (Φ t x : V)‖ := by
  intro ε hε R hR
  obtain ⟨ρ,hρ,hrem⟩ := compact_c1_remainder (V:=V)
    hM hU hsub hv hc ε hε
  let A : ℝ := Real.exp ((L:ℝ) * R)
  have hA : 0 < A := Real.exp_pos _
  refine ⟨ρ / A, div_pos hρ hA, ?_⟩
  intro x y hxy t ht
  have hdist := dist_flow_le_exp_abs (M:=M) (v:=v) L hL h0 hD t y x
  have hexpmono : Real.exp ((L:ℝ) * |t|) ≤ A := by
    dsimp [A]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ht (by exact_mod_cast L.2)
  have hlt : dist (Φ t y : V) (Φ t x : V) < ρ := by
    refine lt_of_le_of_lt hdist ?_
    have hm : A * dist (y:V) (x:V) < ρ := by
      have := (mul_lt_mul_of_pos_left hxy hA)
      calc A * dist (y:V) (x:V) < A * (ρ / A) := this
           _ = ρ := by field_simp
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hexpmono (dist_nonneg)) hm
  exact hrem (Φ t x : V) (Φ t x).property
    (Φ t y : V) (Φ t y).property hlt
end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/InitialVariation.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Variational.lean
section

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Variational.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/FiniteFlows.lean
section
open Set Function Filter
open scoped Topology
namespace LeanEval.Geometry.LiouvilleArnold.Support
variable {X ι : Type*} [TopologicalSpace X] [Fintype ι]


def wordFlow (φ : ι → ℝ → X → X) : List ι → (ι → ℝ) → X → X
  | [], _, x => x
  | i :: l, t, x => φ i (t i) (wordFlow φ l t x)

@[simp] theorem wordFlow_nil (φ : ι → ℝ → X → X) (t : ι → ℝ) (x : X) :
    wordFlow φ [] t x = x := rfl
@[simp] theorem wordFlow_cons (φ : ι → ℝ → X → X) (i : ι) (l : List ι)
    (t : ι → ℝ) (x : X) :
    wordFlow φ (i::l) t x = φ i (t i) (wordFlow φ l t x) := rfl



theorem wordFlow_zero {φ : ι → ℝ → X → X}
    (h0 : ∀ i (x : X), φ i 0 x = x) (l : List ι) (x : X) :
    wordFlow φ l (fun _ => 0) x = x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      change φ i 0 (wordFlow φ l (fun _ => 0) x) = x
      rw [h0 i, ih]


theorem continuous_wordFlow {φ : ι → ℝ → X → X}
    (hφ : ∀ i, Continuous (fun p : ℝ × X => φ i p.1 p.2)) :
    ∀ l : List ι,
      Continuous (fun p : (ι → ℝ) × X => wordFlow φ l p.1 p.2) := by
  intro l
  induction l with
  | nil =>
      simpa [wordFlow] using (continuous_snd : Continuous (fun p : (ι → ℝ) × X => p.2))
  | cons i l ih =>
      have htime : Continuous (fun p : (ι → ℝ) × X => p.1 i) :=
        continuous_apply i |>.comp continuous_fst
      have hp : Continuous (fun p : (ι → ℝ) × X =>
          ((p.1 i), wordFlow φ l p.1 p.2)) := htime.prodMk ih
      simpa [wordFlow, Function.comp_def] using (hφ i).comp hp


theorem continuous_univ_wordFlow {φ : ι → ℝ → X → X}
    (hφ : ∀ i, Continuous (fun p : ℝ × X => φ i p.1 p.2)) :
    Continuous (fun p : (ι → ℝ) × X =>
      wordFlow φ (Finset.univ.toList) p.1 p.2) :=
  continuous_wordFlow hφ _

end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/FiniteFlows.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/VariationBound.lean
section
open Set Function Filter Metric
open scoped ContDiff Topology
namespace LeanEval.Geometry.LiouvilleArnold.Support
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]


theorem quotient_variation_pos
    {M U : Set V} {v : V → V}
    (hM : IsCompact M) (hU : IsOpen U) (hsub : M ⊆ U)
    (hv : DifferentiableOn ℝ v U) (hc : ContinuousOn (fderiv ℝ v) U)
    (L : NNReal) (hL : LipschitzOnWith L v M)
    {Φ : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M})}
    (hD : ∀ (z : {z : V // z ∈ M}) (t : ℝ),
      HasDerivAt (fun q : ℝ => ((Φ q z : {z : V // z ∈ M}) : V))
        (v (Φ t z : V)) t)
    {x y : {z : V // z ∈ M}} {r : ℝ} (hr : r ≠ 0)
    {η : ℝ → V}
    (hη : ∀ t : ℝ,
      HasDerivAt η (fderiv ℝ v (Φ t x : V) (η t)) t)
    {T ε B : ℝ} (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hB : ∀ z ∈ M, ‖fderiv ℝ v z‖ ≤ B)
    (hrem : ∀ t ∈ Icc (0:ℝ) T,
        ‖v (Φ t y : V) - v (Φ t x : V) -
            fderiv ℝ v (Φ t x : V) ((Φ t y : V) - (Φ t x : V))‖
          ≤ ε * ‖(Φ t y : V) - (Φ t x : V)‖) :
    ‖r⁻¹ • ((Φ T y : V) - (Φ T x : V)) - η T‖
      ≤ gronwallBound
          ‖r⁻¹ • ((Φ 0 y : V) - (Φ 0 x : V)) - η 0‖ B
          (ε * (Real.exp ((L:ℝ) * T) *
            ‖r⁻¹ • ((Φ 0 y : V) - (Φ 0 x : V))‖)) T := by
  let q : ℝ → V := fun t => r⁻¹ • ((Φ t y : V) - (Φ t x : V))
  let p : ℝ → V := fun t => q t - η t
  let A : ℝ := Real.exp ((L:ℝ) * T)
  let init : ℝ := ‖q 0‖
  let err : ℝ := ε * (A * init)
  have hqd : ∀ t : ℝ,
      HasDerivAt q (r⁻¹ • (v (Φ t y : V) - v (Φ t x : V))) t := by
    intro t
    have hy := hD y t
    have hx := hD x t
    convert ((hy.sub hx).const_smul r⁻¹) using 1 <;> rfl
  have hpd : ∀ t : ℝ,
      HasDerivAt p
        (r⁻¹ • (v (Φ t y : V) - v (Φ t x : V)) -
          fderiv ℝ v (Φ t x : V) (η t)) t := by
    intro t
    convert ((hqd t).sub (hη t)) using 1 <;> rfl
  have hqbound : ∀ t ∈ Icc (0:ℝ) T,
      ‖q t‖ ≤ A * init := by
    intro t ht
    have hcurv (z : {z : V // z ∈ M}) :
        Continuous (fun s : ℝ => ((Φ s z : {z : V // z ∈ M}) : V)) := by
      rw [continuous_iff_continuousAt]
      intro s; exact (hD z s).continuousAt
    have HH := dist_le_of_trajectories_ODE_of_mem
      (v:= fun _ : ℝ => v) (s:= fun _ : ℝ => M)
      (K:=L) (a:=(0:ℝ)) (b:=T)
      (f:= fun s : ℝ => (Φ s y : V))
      (g:= fun s : ℝ => (Φ s x : V))
      (δ:= dist (Φ 0 y : V) (Φ 0 x : V))
      (fun s hs => hL)
      (hcurv y).continuousOn
      (by intro s hs; exact (hD y s).hasDerivWithinAt)
      (by intro s hs; exact (Φ s y).property)
      (hcurv x).continuousOn
      (by intro s hs; exact (hD x s).hasDerivWithinAt)
      (by intro s hs; exact (Φ s x).property)
      (le_rfl)
    have hdist := HH t ht
    have hdist' : ‖(Φ t y : V) - (Φ t x : V)‖ ≤
        Real.exp ((L:ℝ) * T) * ‖(Φ 0 y : V) - (Φ 0 x : V)‖ := by
      have hmono : Real.exp ((L:ℝ) * (t - 0)) ≤ Real.exp ((L:ℝ) * T) := by
        apply Real.exp_le_exp.mpr
        have hn : 0 ≤ (L:ℝ) := by exact_mod_cast L.2
        have ht' : t ≤ T := ht.2
        simpa using (mul_le_mul_of_nonneg_left (by simpa using ht') hn)
      calc
        ‖(Φ t y : V) - (Φ t x : V)‖
            = dist (Φ t y : V) (Φ t x : V) := by rw [dist_eq_norm]
        _ ≤ dist (Φ 0 y : V) (Φ 0 x : V) *
              Real.exp ((L:ℝ) * (t - 0)) := hdist
        _ ≤ Real.exp ((L:ℝ) * T) *
              dist (Φ 0 y : V) (Φ 0 x : V) := by
              have hh := mul_le_mul_of_nonneg_left hmono (dist_nonneg : 0 ≤ dist (Φ 0 y : V) (Φ 0 x : V))
              nlinarith
        _ = Real.exp ((L:ℝ) * T) *
              ‖(Φ 0 y : V) - (Φ 0 x : V)‖ := by rw [dist_eq_norm]
    calc
      ‖q t‖ = ‖(r⁻¹ : ℝ)‖ * ‖(Φ t y : V) - (Φ t x : V)‖ := by simp [q, norm_smul]
      _ ≤ ‖(r⁻¹ : ℝ)‖ *
            (Real.exp ((L:ℝ)*T) * ‖(Φ 0 y : V) - (Φ 0 x : V)‖) :=
            mul_le_mul_of_nonneg_left hdist' (norm_nonneg _)
      _ = A * init := by simp [A, init, q, norm_smul]; ring
  have hpcont : Continuous p := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hpd t).continuousAt
  have hbound : ∀ t ∈ Ico (0:ℝ) T,
      ‖(r⁻¹ • (v (Φ t y : V) - v (Φ t x : V)) -
          fderiv ℝ v (Φ t x : V) (η t))‖
        ≤ B * ‖p t‖ + err := by
    intro t ht
    let R : V := v (Φ t y : V) - v (Φ t x : V) -
            fderiv ℝ v (Φ t x : V)
              ((Φ t y : V) - (Φ t x : V))
    let d := fderiv ℝ v (Φ t x : V)
    have alg :
        r⁻¹ • (v (Φ t y : V) - v (Φ t x : V)) - d (η t)
          = d (p t) + r⁻¹ • R := by
      simp [R, p, q, d, map_sub, map_smul]; module
    rw [alg]
    have hdB : ‖d (p t)‖ ≤ B * ‖p t‖ :=
      (d.le_opNorm (p t)).trans
        (mul_le_mul_of_nonneg_right (hB (Φ t x : V) (Φ t x).property) (norm_nonneg _))
    have htcc : t ∈ Icc (0:ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
    have hRB := hrem t htcc
    have hR' : ‖r⁻¹ • R‖ ≤ ε * ‖q t‖ := by
      calc
        ‖r⁻¹ • R‖ = ‖(r⁻¹ : ℝ)‖ * ‖R‖ := by rw [norm_smul]
        _ ≤ ‖(r⁻¹ : ℝ)‖ *
            (ε * ‖(Φ t y : V) - (Φ t x : V)‖) :=
              mul_le_mul_of_nonneg_left (by simpa [R, d] using hRB) (norm_nonneg _)
        _ = ε * ‖q t‖ := by simp [q, norm_smul]; ring
    calc
      ‖d (p t) + r⁻¹ • R‖ ≤ ‖d (p t)‖ + ‖r⁻¹ • R‖ := norm_add_le _ _
      _ ≤ B * ‖p t‖ + (ε * ‖q t‖) := add_le_add hdB hR'
      _ ≤ B * ‖p t‖ + err := by
        dsimp [err]
        exact add_le_add_right (mul_le_mul_of_nonneg_left (hqbound t htcc) hε) _
  have H := norm_le_gronwallBound_of_norm_deriv_right_le
    (f:=p)
    (f':= fun t =>
      (r⁻¹ • (v (Φ t y : V) - v (Φ t x : V)) -
          fderiv ℝ v (Φ t x : V) (η t)))
    (a:=(0:ℝ)) (b:=T)
    (δ:= ‖p 0‖) (K:=B) (ε:=err)
    hpcont.continuousOn
    (by intro t ht; exact (hpd t).hasDerivWithinAt)
    (le_rfl) hbound T ⟨hT, le_rfl⟩
  simpa [p, q, err, init, A] using H
end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/VariationBound.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Dependence.lean
section
open Set Function Filter Metric
open scoped ContDiff Topology
namespace LeanEval.Geometry.LiouvilleArnold.Support
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

private def __Dependence_gc (B T : ℝ) : ℝ := if B = 0 then 1 else Real.exp (B*T)
private def __Dependence_ge (B T : ℝ) : ℝ := if B = 0 then |T| else |(Real.exp (B*T) - 1) / B|
private lemma __Dependence_gc_pos (B T : ℝ) : 0 < __Dependence_gc B T := by
  unfold __Dependence_gc; split_ifs <;> positivity
private lemma __Dependence_ge_nonneg (B T : ℝ) : 0 ≤ __Dependence_ge B T := by
  unfold __Dependence_ge; split_ifs <;> positivity
private lemma __Dependence_gb_le (B T d e : ℝ) (he:0 ≤ e) :
    gronwallBound d B e T ≤ __Dependence_gc B T * d + __Dependence_ge B T * e := by
  by_cases hb : B = 0
  · subst B
    simp [__Dependence_gc, __Dependence_ge, gronwallBound, mul_comm, mul_left_comm]
    have h := mul_le_mul_of_nonneg_right (le_abs_self T) he
    linarith
  · rw [gronwallBound]; simp [hb, __Dependence_gc, __Dependence_ge]
    have h := mul_le_mul_of_nonneg_right (le_abs_self ((Real.exp (B*T)-1)/B)) he
    ring_nf at h ⊢
    nlinarith


theorem deriv_initial_pos
    {M U : Set V} {v w : V → V}
    (hM : IsCompact M) (hne : M.Nonempty) (hU : IsOpen U) (hsub : M ⊆ U)
    (hv : DifferentiableOn ℝ v U) (hc : ContinuousOn (fderiv ℝ v) U)
    (L : NNReal) (hL : LipschitzOnWith L v M)
    {φ ψ : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M})}
    (hφ0 : ∀ z : {z : V // z ∈ M}, φ 0 z = z)
    (hφD : ∀ (z : {z : V // z ∈ M}) (t : ℝ),
      HasDerivAt (fun q : ℝ => ((φ q z : {z : V // z ∈ M}) : V))
        (v (φ t z : V)) t)
    (hψ0 : ∀ z : {z : V // z ∈ M}, ψ 0 z = z)
    (hψD0 : ∀ z : {z : V // z ∈ M},
      HasDerivAt (fun r : ℝ => ((ψ r z : {z : V // z ∈ M}) : V))
        (w (z:V)) 0)
    (hvar : ∀ (z : {z : V // z ∈ M}) (t : ℝ),
      HasDerivAt (fun q : ℝ => w (φ q z : V))
        (fderiv ℝ v (φ t z : V) (w (φ t z : V))) t) :
    ∀ T : ℝ, 0 ≤ T → ∀ z : {z : V // z ∈ M},
      HasDerivAt (fun r : ℝ => ((φ T (ψ r z) : {z : V // z ∈ M}) : V))
        (w (φ T z : V)) 0 := by
  classical
  have hcM : ContinuousOn (fderiv ℝ v) M := hc.mono hsub
  obtain ⟨B, hB⟩ := hM.exists_bound_of_continuousOn hcM
  intro T hT z
  let q0 : ℝ → V := fun r => r⁻¹ • ((ψ r z : V) - (z:V))
  have hq0 : Tendsto q0 (𝓝[≠] (0:ℝ)) (𝓝 (w (z:V))) := by
    have h := (hψD0 z).tendsto_slope_zero
    simpa [q0, hψ0 z] using h
  have hy : Tendsto (fun r : ℝ => (ψ r z : V)) (𝓝[≠] (0:ℝ)) (𝓝 (z:V)) := by
    have ht : Tendsto (fun r : ℝ => (ψ r z : V)) (𝓝 (0:ℝ)) (𝓝 ((ψ 0 z : {x : V // x ∈ M}) : V)) :=
      (hψD0 z).continuousAt.tendsto
    exact (by simpa [hψ0 z] using
      (ht.mono_left (show (𝓝[≠] (0:ℝ)) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)))
  apply hasDerivAt_iff_tendsto_slope_zero.2
  have target :
      (fun r : ℝ => r⁻¹ •
        (((φ T (ψ (0+r) z) : {x : V // x ∈ M}) : V) -
          ((φ T (ψ 0 z) : {x : V // x ∈ M}) : V))) =
      (fun r : ℝ => r⁻¹ • ((φ T (ψ r z) : V) - (φ T z : V))) := by
    funext r; simp [hψ0]
  rw [target]
  apply (Metric.tendsto_nhds).2
  intro τ hτ
  let C : ℝ := __Dependence_gc B T
  let D : ℝ := __Dependence_ge B T
  let A : ℝ := Real.exp ((L:ℝ)*T)
  let Q : ℝ := ‖w (z:V)‖ + 1
  have hC : 0 < C := __Dependence_gc_pos _ _
  have hD : 0 ≤ D := __Dependence_ge_nonneg _ _
  have hA : 0 < A := Real.exp_pos _
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let s : ℝ := τ / (4 * ((D+1) * (A*Q+1)))
  have hden : 0 < 4 * ((D+1) * (A*Q+1)) := by positivity
  have hs : 0 < s := div_pos hτ hden
  obtain ⟨ρ, hρ, hremρ⟩ :=
    compact_remainder_along_complete_orbits (V:=V)
      (M:=M) (U:=U) (v:=v) hM hU hsub hv hc L hL
      (Φ:=φ) hφ0 hφD s hs T hT
  have he0 : 0 < τ / (2*(C+1)) := by positivity
  have hqev : ∀ᶠ r in 𝓝[≠] (0:ℝ), dist (q0 r) (w (z:V)) < τ/(2*(C+1)) :=
    (Metric.tendsto_nhds.1 hq0) _ he0
  have hqQ0 : 0 < (1:ℝ) := by norm_num
  have hqbd : ∀ᶠ r in 𝓝[≠] (0:ℝ), dist (q0 r) (w (z:V)) < 1 :=
    (Metric.tendsto_nhds.1 hq0) _ hqQ0
  have hyρ : ∀ᶠ r in 𝓝[≠] (0:ℝ), dist (ψ r z : V) (z:V) < ρ :=
    (Metric.tendsto_nhds.1 hy) _ hρ
  have hrne : ∀ᶠ r in 𝓝[≠] (0:ℝ), r ≠ 0 := by
    exact self_mem_nhdsWithin
  filter_upwards [hqev, hqbd, hyρ, hrne] with r er eb ey rn
  change dist (r⁻¹ • ((φ T (ψ r z) : V) - (φ T z : V)))
      (w (φ T z : V)) < τ
  rw [dist_eq_norm]
  have hrem : ∀ t ∈ Icc (0:ℝ) T,
        ‖v (φ t (ψ r z) : V) - v (φ t z : V) -
            fderiv ℝ v (φ t z : V)
              ((φ t (ψ r z) : V) - (φ t z : V))‖
          ≤ s * ‖(φ t (ψ r z) : V) - (φ t z : V)‖ := by
    intro t ht
    exact hremρ z (ψ r z)
      (by simpa [dist_comm] using ey) t (by
        have ht0 : 0 ≤ t := ht.1
        have htt : t ≤ T := ht.2
        simpa [abs_of_nonneg ht0] using htt)
  have H := quotient_variation_pos (V:=V) (M:=M) (U:=U) (v:=v)
      hM hU hsub hv hc L hL hφD (x:=z) (y:=ψ r z) (r:=r) rn
      (η:= fun t : ℝ => w (φ t z : V)) (hvar z) hT (le_of_lt hs) hB hrem
  have H' : ‖r⁻¹ • ((φ T (ψ r z) : V) - (φ T z : V)) -
                w (φ T z : V)‖ ≤
        gronwallBound ‖q0 r - w (z:V)‖ B
          (s * (A * ‖q0 r‖)) T := by
    simpa [q0, A, hφ0] using H
  refine lt_of_le_of_lt H' ?_
  have e_non : 0 ≤ s * (A * ‖q0 r‖) := by positivity
  calc
    gronwallBound ‖q0 r - w (z:V)‖ B (s * (A * ‖q0 r‖)) T
        ≤ C * ‖q0 r - w (z:V)‖ + D * (s * (A * ‖q0 r‖)) := by
            simpa [C, D] using (__Dependence_gb_le B T ‖q0 r - w (z:V)‖
              (s * (A * ‖q0 r‖)) e_non)
    _ < τ := by
      have e' : ‖q0 r - w (z:V)‖ < τ/(2*(C+1)) := by
        simpa [dist_eq_norm] using er
      have qb : ‖q0 r‖ < Q := by
        have hh : ‖q0 r - w (z:V)‖ < 1 := by simpa [dist_eq_norm] using eb
        calc
          ‖q0 r‖ ≤ ‖q0 r - w (z:V)‖ + ‖w (z:V)‖ := by
            simpa [add_comm] using (norm_le_norm_add_norm_sub' (q0 r) (w (z:V)))
          _ < Q := by dsimp [Q]; linarith
      have first : C * ‖q0 r - w (z:V)‖ < τ/2 := by
        have := mul_lt_mul_of_pos_left e' hC
        have hcfrac : C * (τ/(2*(C+1))) < τ/2 := by
          have : C / (C+1) < (1:ℝ) := by
            apply (div_lt_one (by linarith)).2; linarith
          calc C * (τ/(2*(C+1))) = (τ/2) * (C/(C+1)) := by
                 field_simp
               _ < (τ/2) * 1 := by gcongr
               _ = τ/2 := by ring
        exact lt_trans this hcfrac
      have second : D * (s * (A * ‖q0 r‖)) < τ/2 := by
        have dle : D ≤ D+1 := by linarith
        have qle : A * ‖q0 r‖ < A*Q+1 := by
          have := mul_lt_mul_of_pos_left qb hA
          linarith
        have key : D * (A * ‖q0 r‖) < (D+1) * (A*Q+1) := by
          calc D * (A * ‖q0 r‖) ≤ (D+1) * (A * ‖q0 r‖) :=
                  mul_le_mul_of_nonneg_right dle (by positivity)
               _ < (D+1) * (A*Q+1) :=
                  mul_lt_mul_of_pos_left qle (by linarith)
        calc
          D * (s * (A * ‖q0 r‖))
              = s * (D * (A * ‖q0 r‖)) := by ring
          _ < s * ((D+1) * (A*Q+1)) := mul_lt_mul_of_pos_left key hs
          _ = τ/4 := by dsimp [s]; field_simp
          _ < τ/2 := by linarith
      linarith


theorem deriv_initial_all
    {M U : Set V} {v w : V → V}
    (hM : IsCompact M) (hne : M.Nonempty) (hU : IsOpen U) (hsub : M ⊆ U)
    (hv : DifferentiableOn ℝ v U) (hc : ContinuousOn (fderiv ℝ v) U)
    (L : NNReal) (hL : LipschitzOnWith L v M)
    {φ ψ : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M})}
    (hφ0 : ∀ z : {z : V // z ∈ M}, φ 0 z = z)
    (hφD : ∀ (z : {z : V // z ∈ M}) (t : ℝ),
      HasDerivAt (fun q : ℝ => ((φ q z : {z : V // z ∈ M}) : V))
        (v (φ t z : V)) t)
    (hψ0 : ∀ z : {z : V // z ∈ M}, ψ 0 z = z)
    (hψD0 : ∀ z : {z : V // z ∈ M},
      HasDerivAt (fun r : ℝ => ((ψ r z : {z : V // z ∈ M}) : V))
        (w (z:V)) 0)
    (hvar : ∀ (z : {z : V // z ∈ M}) (t : ℝ),
      HasDerivAt (fun q : ℝ => w (φ q z : V))
        (fderiv ℝ v (φ t z : V) (w (φ t z : V))) t) :
    ∀ T : ℝ, ∀ z : {z : V // z ∈ M},
      HasDerivAt (fun r : ℝ => ((φ T (ψ r z) : {z : V // z ∈ M}) : V))
        (w (φ T z : V)) 0 := by
  intro T z
  by_cases ht : 0 ≤ T
  · exact deriv_initial_pos (V:=V) (M:=M) (U:=U) (v:=v) (w:=w)
      hM hne hU hsub hv hc L hL hφ0 hφD hψ0 hψD0 hvar T ht z
  · let vn : V → V := fun y => - v y
    let φn : ℝ → ({z : V // z ∈ M}) → ({z : V // z ∈ M}) := fun t y => φ (-t) y
    have hvn : DifferentiableOn ℝ vn U := by
      intro y hy
      exact (hv y hy).neg
    have hcn : ContinuousOn (fderiv ℝ vn) U := by
      have eqd : fderiv ℝ vn = (fun y => -(fderiv ℝ v y)) := by
        funext y
        change fderiv ℝ (-v) y = - fderiv ℝ v y
        exact fderiv_neg
      rw [eqd]
      exact hc.neg
    have hLn : LipschitzOnWith L vn M := by
      change LipschitzOnWith L (-v) M
      exact hL.neg
    have hn0 : ∀ y : {z : V // z ∈ M}, φn 0 y = y := by
      intro y; simpa [φn] using hφ0 y
    have hnD : ∀ (y : {z : V // z ∈ M}) (t : ℝ),
        HasDerivAt (fun q : ℝ => ((φn q y : {z : V // z ∈ M}) : V))
          (vn (φn t y : V)) t := by
      intro y t
      have hx := (hφD y (-t)).scomp t (hasDerivAt_neg t)
      simpa [φn, vn, Function.comp_def, neg_one_smul ℝ] using hx
    have hnvar : ∀ (y : {z : V // z ∈ M}) (t : ℝ),
        HasDerivAt (fun q : ℝ => w (φn q y : V))
          (fderiv ℝ vn (φn t y : V) (w (φn t y : V))) t := by
      intro y t
      have hx := (hvar y (-t)).scomp t (hasDerivAt_neg t)
      simpa [φn, vn, fderiv_neg, Function.comp_def, neg_one_smul ℝ] using hx
    have hp := deriv_initial_pos (V:=V) (M:=M) (U:=U) (v:=vn) (w:=w)
      hM hne hU hsub hvn hcn L hLn hn0 hnD hψ0 hψD0 hnvar (-T)
      (by linarith) z
    simpa [φn] using hp

end
end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/Dependence.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/LatticeTorus.lean
section
open Set Function Topology
noncomputable section
namespace LeanEval.Geometry.LiouvilleArnold.Support


def stdLattice (ι : Type*) [Fintype ι] : AddSubgroup (ι → ℝ) :=
  (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup

lemma mem_stdLattice {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    v ∈ stdLattice ι ↔ ∀ i, ∃ z : ℤ, (z:ℝ) = v i := by
  change v ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ _
  rw [Module.Basis.mem_span_iff_repr_mem ℤ (Pi.basisFun ℝ ι)]
  apply forall_congr'
  intro i
  rw [Pi.basisFun_repr]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z, hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨z, hz⟩


def standardCircleProj {ι : Type*} (x : ι → ℝ) : ι → AddCircle (1:ℝ) :=
  fun i => QuotientAddGroup.mk (x i)

lemma continuous_standardCircleProj {ι : Type*} :
    Continuous (standardCircleProj (ι:=ι)) := by
  apply continuous_pi
  intro i
  exact QuotientAddGroup.continuous_mk.comp (continuous_apply i)

lemma standardCircleProj_eq {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    standardCircleProj x = standardCircleProj y ↔ x-y ∈ stdLattice ι := by
  rw [mem_stdLattice]
  constructor
  · intro h i
    have hi := congrFun h i
    have hi' : x i - y i ∈ AddSubgroup.zmultiples (1:ℝ) :=
      (QuotientAddGroup.eq_iff_sub_mem.mp hi)
    rcases (AddSubgroup.mem_zmultiples_iff.mp hi') with ⟨z,hz⟩
    refine ⟨z, ?_⟩
    simpa using hz
  · intro h
    funext i
    rcases h i with ⟨z,hz⟩
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨z, ?_⟩
    simpa using hz


def standardQuotientToCircle {ι : Type*} [Fintype ι] :
    ((ι→ℝ) ⧸ stdLattice ι) → (ι → AddCircle (1:ℝ)) :=
 fun q => Quotient.liftOn' q (standardCircleProj (ι:=ι)) (by
   intro a b hab
   apply (standardCircleProj_eq a b).2
   have h := QuotientAddGroup.leftRel_apply.mp hab
   have hn : - ((-a) + b) ∈ stdLattice ι := (stdLattice ι).neg_mem h
   simpa [sub_eq_add_neg, add_comm] using hn)

@[simp] lemma standardQuotientToCircle_mk {ι : Type*} [Fintype ι]
    (x : ι→ℝ) :
    standardQuotientToCircle (QuotientAddGroup.mk x : (ι→ℝ) ⧸ stdLattice ι) =
      standardCircleProj x := rfl

lemma continuous_standardQuotientToCircle {ι : Type*} [Fintype ι] :
    Continuous (standardQuotientToCircle (ι:=ι)) := by
  apply continuous_quot_lift
  exact continuous_standardCircleProj

lemma bijective_standardQuotientToCircle {ι : Type*} [Fintype ι] :
    Function.Bijective (standardQuotientToCircle (ι:=ι)) := by
 constructor
 · intro a b h
   induction a using Quotient.inductionOn' with | _ x => ?_
   induction b using Quotient.inductionOn' with | _ y => ?_
   rw [standardQuotientToCircle_mk, standardQuotientToCircle_mk] at h
   apply Quotient.sound'
   apply QuotientAddGroup.leftRel_apply.mpr
   have hm : x-y ∈ stdLattice ι := (standardCircleProj_eq x y).1 h
   have hn := (stdLattice ι).neg_mem hm
   simpa [sub_eq_add_neg, add_comm] using hn
 · intro y
   classical
   have hi : ∀ i : ι, ∃ x : ℝ, (QuotientAddGroup.mk x : AddCircle (1:ℝ)) = y i := by
     intro i
     exact QuotientAddGroup.mk'_surjective _ (y i)
   choose x hx using hi
   refine ⟨QuotientAddGroup.mk x, ?_⟩
   rw [standardQuotientToCircle_mk]
   funext i
   exact hx i


lemma isCompact_univ_stdQuotient {ι : Type*} [Fintype ι] :
    IsCompact (Set.univ : Set ((ι→ℝ) ⧸ stdLattice ι)) := by
  let S : Submodule ℤ (ι→ℝ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
  have hd : DiscreteTopology S := inferInstance
  have hz : IsZLattice ℝ S := inferInstance
  let f : (ι→ℝ) → ((ι→ℝ) ⧸ stdLattice ι) := fun x => QuotientAddGroup.mk x
  have hf : Continuous f := QuotientAddGroup.continuous_mk
  have hp : ∀ z w : (ι→ℝ), w ∈ S → f (z + w) = f z := by
    intro z w hw
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change z + w - z ∈ stdLattice ι
    change z + w - z ∈ S
    simpa [add_sub_cancel_left] using hw
  have hc : IsCompact (Set.range f) :=
    IsZLattice.isCompact_range_of_periodic S f hf hp
  have hr : Set.range f = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn' with | _ x => ?_
    exact ⟨x, rfl⟩
  rwa [hr] at hc


theorem stdQuotient_homeomorph_torus {ι : Type*} [Fintype ι] :
    Nonempty (((ι→ℝ) ⧸ stdLattice ι) ≃ₜ (ι → AddCircle (1:ℝ))) := by
  classical
  letI : CompactSpace ((ι→ℝ) ⧸ stdLattice ι) := ⟨isCompact_univ_stdQuotient⟩
  have hh : IsHomeomorph (standardQuotientToCircle (ι:=ι)) :=
    (isHomeomorph_iff_continuous_bijective).2
      ⟨continuous_standardQuotientToCircle, bijective_standardQuotientToCircle⟩
  exact ⟨hh.homeomorph _⟩


theorem nonempty_homeomorph_stdQuotient_of_orbit
    {ι : Type*} [Fintype ι]
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (a : (ι → ℝ) → X) (ha : Continuous a)
    (hrel : ∀ u v, a u = a v ↔ u - v ∈ stdLattice ι)
    (hsurj : Function.Surjective a) :
    Nonempty (X ≃ₜ ((ι → ℝ) ⧸ stdLattice ι)) := by
  let A : ((ι → ℝ) ⧸ stdLattice ι) → X :=
    fun q => Quotient.liftOn' q a (by
      intro u v huv
      apply (hrel u v).2
      have h := QuotientAddGroup.leftRel_apply.mp huv
      have hn : - ((-u) + v) ∈ stdLattice ι := (stdLattice ι).neg_mem h
      simpa [sub_eq_add_neg, add_comm] using hn)
  have A_mk (u : ι → ℝ) :
      A (QuotientAddGroup.mk u : ((ι → ℝ) ⧸ stdLattice ι)) = a u := rfl
  have hA : Continuous A := by
    apply continuous_quot_lift
    exact ha
  have hbij : Function.Bijective A := by
    constructor
    · intro p q h
      induction p using Quotient.inductionOn' with | _ u => ?_
      induction q using Quotient.inductionOn' with | _ v => ?_
      rw [A_mk, A_mk] at h
      apply Quotient.sound'
      apply QuotientAddGroup.leftRel_apply.mpr
      have hh : u - v ∈ stdLattice ι := (hrel u v).1 h
      have hn := (stdLattice ι).neg_mem hh
      simpa [sub_eq_add_neg, add_comm] using hn
    · intro x
      obtain ⟨u, rfl⟩ := hsurj x
      exact ⟨QuotientAddGroup.mk u, A_mk u⟩
  letI : CompactSpace ((ι → ℝ) ⧸ stdLattice ι) :=
    ⟨isCompact_univ_stdQuotient⟩
  have hm : IsHomeomorph A :=
    (isHomeomorph_iff_continuous_bijective).2 ⟨hA, hbij⟩
  exact ⟨(hm.homeomorph A).symm⟩

end LeanEval.Geometry.LiouvilleArnold.Support

end

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/LatticeTorus.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/WordAction.lean
section
open Set Function
namespace LeanEval.Geometry.LiouvilleArnold.Support
variable {ι X : Type*} [Fintype ι]

theorem wordFlow_add
    {φ : ι → ℝ → X → X}
    (hadd : ∀ i t u x, φ i (t + u) x = φ i t (φ i u x))
    (hcomm : ∀ i j t u x, φ i t (φ j u x) = φ j u (φ i t x)) :
    ∀ (l : List ι) (a b : ι → ℝ) (x : X),
      wordFlow φ l (a + b) x =
        wordFlow φ l a (wordFlow φ l b x) := by
  intro l
  induction l with
  | nil => intro a b x; rfl
  | cons i l ih =>
    intro a b x
    change φ i ((a+b) i) (wordFlow φ l (a+b) x) =
      φ i (a i) (wordFlow φ l a (φ i (b i) (wordFlow φ l b x)))
    rw [Pi.add_apply, hadd, ih]
    congr 1
    have move : ∀ (k : List ι) (p : ι → ℝ) (y : X),
        wordFlow φ k p (φ i (b i) y) =
          φ i (b i) (wordFlow φ k p y) := by
      intro k
      induction k with
      | nil => intro p y; rfl
      | cons j k hk =>
        intro p y
        change φ j (p j) (wordFlow φ k p (φ i (b i) y)) =
          φ i (b i) (φ j (p j) (wordFlow φ k p y))
        rw [hk]
        exact hcomm j i _ _ _
    exact (move l a (wordFlow φ l b x)).symm


theorem wordFlow_action
    {φ : ι → ℝ → X → X}
    (h0 : ∀ i x, φ i 0 x = x)
    (hadd : ∀ i t u x, φ i (t + u) x = φ i t (φ i u x))
    (hcomm : ∀ i j t u x, φ i t (φ j u x) = φ j u (φ i t x))
    (l : List ι) :
    (∀ x, wordFlow φ l 0 x = x) ∧
    (∀ a b x, wordFlow φ l (a+b) x =
       wordFlow φ l a (wordFlow φ l b x)) := by
  constructor
  · intro x
    induction l with
    | nil => rfl
    | cons i l ih =>
      change φ i 0 (wordFlow φ l 0 x) = x
      rw [h0, ih]
  · exact wordFlow_add hadd hcomm l


theorem orbit_stabilizer_addsubgroup
    {A : Type*} [AddCommGroup A] {X : Type*}
    (Ψ : A → X → X)
    (h0 : ∀ x, Ψ 0 x = x)
    (hadd : ∀ a b x, Ψ (a+b) x = Ψ a (Ψ b x))
    (x : X) :
    ∃ L : AddSubgroup A,
      (∀ a, a ∈ L ↔ Ψ a x = x) ∧
      (∀ a b, Ψ a x = Ψ b x ↔ a - b ∈ L) := by
  let L : AddSubgroup A :=
    { carrier := {a | Ψ a x = x}
      zero_mem' := h0 x
      add_mem' := by
        intro a b ha hb
        change Ψ (a+b) x = x
        rw [hadd, hb, ha]
      neg_mem' := by
        intro a ha
        change Ψ (-a) x = x
        have h := hadd (-a) a x
        rw [ha] at h
        have : Ψ 0 x = Ψ (-a) x := by simpa using h
        simpa [h0] using this.symm }
  refine ⟨L, (by intro a; rfl), ?_⟩
  intro a b
  change Ψ a x = Ψ b x ↔ Ψ (a-b) x = x
  constructor
  · intro hab
    calc
      Ψ (a-b) x = Ψ (-b+a) x := by congr 1 <;> abel
      _ = Ψ (-b) (Ψ a x) := hadd _ _ _
      _ = Ψ (-b) (Ψ b x) := by rw [hab]
      _ = Ψ (-b+b) x := (hadd _ _ _).symm
      _ = x := by simp [h0]
  · intro hab
    calc
      Ψ a x = Ψ ((a-b)+b) x := by
        have : (a-b)+b = a := by abel
        rw [this]
      _ = Ψ b (Ψ (a-b) x) := by
        rw [← hadd]
        congr 1 <;> abel
      _ = Ψ b x := by rw [hab]
end LeanEval.Geometry.LiouvilleArnold.Support


end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/WordAction.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/LatticeClassify.lean
section
open Set Function Topology Submodule
open scoped Topology
noncomputable section
namespace LeanEval.Geometry.LiouvilleArnold.Support


theorem exists_linear_equiv_mem_std_of_zlattice
    {ι : Type*} [Fintype ι]
    (S : Submodule ℤ (ι → ℝ)) [DiscreteTopology S]
    (hs : Submodule.span ℝ (S : Set (ι → ℝ)) = ⊤) :
    ∃ e : (ι → ℝ) ≃L[ℝ] (ι → ℝ), ∀ u : (ι → ℝ),
       e u ∈ S ↔ u ∈ stdLattice ι := by
  classical
  letI : IsZLattice ℝ S := ⟨hs⟩
  let b : Module.Basis ι ℤ S := IsZLattice.basis S
  let br : Module.Basis ι ℝ (ι → ℝ) := b.ofZLatticeBasis ℝ S
  let l : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) := (Pi.basisFun ℝ ι).equiv br (Equiv.refl ι)
  let e : (ι → ℝ) ≃L[ℝ] (ι → ℝ) := l.toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  have himg : Submodule.map (l.toLinearMap.restrictScalars ℤ)
        (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) = S := by
    rw [Submodule.map_span]
    have hrange : (l.toLinearMap.restrictScalars ℤ : (ι → ℝ) →ₗ[ℤ] (ι → ℝ)) ''
          (Set.range (Pi.basisFun ℝ ι)) = Set.range br := by
      ext z
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        refine ⟨i, ?_⟩
        change br i = l ((Pi.basisFun ℝ ι) i)
        simpa [l] using
          ((Pi.basisFun ℝ ι).equiv_apply i br (Equiv.refl ι)).symm
      · rintro ⟨i, rfl⟩
        refine ⟨(Pi.basisFun ℝ ι) i, ⟨i, rfl⟩, ?_⟩
        change l ((Pi.basisFun ℝ ι) i) = br i
        simpa [l] using
          ((Pi.basisFun ℝ ι).equiv_apply i br (Equiv.refl ι))
    rw [hrange]
    exact b.ofZLatticeBasis_span ℝ
  intro u
  change l u ∈ S ↔ _
  change l u ∈ S ↔ u ∈
    Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
  constructor
  · intro hu
    rw [← himg] at hu
    rcases hu with ⟨w, hw, hew⟩
    have : w = u := l.injective (by
      simpa using hew)
    simpa [this] using hw
  · intro hu
    rw [← himg]
    exact ⟨u, hu, rfl⟩

end LeanEval.Geometry.LiouvilleArnold.Support

namespace LeanEval.Geometry.LiouvilleArnold.Support
open Set Function Topology Submodule

theorem discreteTopology_of_isDiscrete_addSubgroup {E : Type*} [AddGroup E] [TopologicalSpace E]
    (L : AddSubgroup E) (hL : IsDiscrete (L : Set E)) :
    DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  rw [isDiscrete_iff_forall_exists_isOpen] at hL
  obtain ⟨U,hU,he⟩ := hL (x:E) x.property
  have hup : IsOpen (Subtype.val ⁻¹' U : Set L) :=
    Topology.IsInducing.subtypeVal.isOpen_iff.mpr ⟨U, hU, rfl⟩
  have he' : (Subtype.val ⁻¹' U : Set L) = {x} := by
    ext y
    constructor
    · intro hy
      change (y:E) ∈ U at hy
      have hmem : (y:E) ∈ U ∩ (L : Set E) := ⟨hy, y.property⟩
      have hsing : (y:E) ∈ ({(x:E)} : Set E) := by simpa [he] using hmem
      have hv : (y:E) = (x:E) := Set.mem_singleton_iff.mp hsing
      exact Set.mem_singleton_iff.mpr (Subtype.ext hv)
    · intro hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      change (x:E) ∈ U
      have : (x:E) ∈ U ∩ (L : Set E) := by
        rw [he]
        exact Set.mem_singleton (x:E)
      exact this.1
  rwa [he'] at hup


theorem exists_linear_equiv_mem_std_of_discrete_span
    {ι : Type*} [Fintype ι]
    (L : AddSubgroup (ι → ℝ)) (hdisc : IsDiscrete (L : Set (ι → ℝ)))
    (hspan : Submodule.span ℝ (L : Set (ι → ℝ)) = ⊤) :
    ∃ e : (ι → ℝ) ≃L[ℝ] (ι → ℝ), ∀ u : (ι → ℝ),
       e u ∈ L ↔ u ∈ stdLattice ι := by
  classical
  let S : Submodule ℤ (ι → ℝ) := AddSubgroup.toIntSubmodule L
  letI : DiscreteTopology L := discreteTopology_of_isDiscrete_addSubgroup L hdisc
  letI : DiscreteTopology S := by
    change DiscreteTopology L
    infer_instance
  have hs : Submodule.span ℝ (S : Set (ι → ℝ)) = ⊤ := by
    simpa [S] using hspan
  obtain ⟨e, he⟩ := exists_linear_equiv_mem_std_of_zlattice S hs
  refine ⟨e, ?_⟩
  intro u
  change e u ∈ AddSubgroup.toIntSubmodule L ↔ _
  exact he u
end LeanEval.Geometry.LiouvilleArnold.Support

namespace LeanEval.Geometry.LiouvilleArnold.Support
open Set Function Topology Submodule

theorem span_eq_top_of_compact_addsubgroup_cover
    {ι : Type*} [Fintype ι]
    (L : AddSubgroup (ι → ℝ))
    {K : Set (ι → ℝ)} (hK : IsCompact K)
    (hcover : ∀ z : (ι → ℝ), ∃ k ∈ K, z - k ∈ L) :
    Submodule.span ℝ (L : Set (ι → ℝ)) = ⊤ := by
  classical
  let S : Submodule ℝ (ι → ℝ) := Submodule.span ℝ (L : Set (ι → ℝ))
  by_contra hn
  have hne : S ≠ ⊤ := by simpa [S] using hn
  obtain ⟨w, hwtop, hw⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  letI : IsClosed (S : Set (ι → ℝ)) :=
    Submodule.closed_of_finiteDimensional S
  have hqne : S.mkQ w ≠ 0 := by
    intro h
    have : w ∈ (S.mkQ).ker := by simpa using h
    rw [Submodule.ker_mkQ] at this
    exact hw this
  have hcont : Continuous (S.mkQ : (ι → ℝ) → ( (ι → ℝ) ⧸ S)) :=
    LinearMap.continuous_of_finiteDimensional _
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hbound : ∀ t : ℝ, ‖t • (S.mkQ w)‖ ≤ C := by
    intro t
    obtain ⟨k,hk,hsub⟩ := hcover (t • w)
    have hsubS : t • w - k ∈ S :=
      Submodule.subset_span hsub
    have hz : S.mkQ (t • w - k) = 0 := by
      have : t • w - k ∈ (S.mkQ).ker := by
        rw [Submodule.ker_mkQ]
        exact hsubS
      exact this
    have heq : t • (S.mkQ w) = S.mkQ k := by
      have h := hz
      rw [map_sub, LinearMap.map_smul] at h
      exact sub_eq_zero.mp h
    rw [heq]
    exact hC k hk
  have hnorm : 0 < ‖S.mkQ w‖ := (norm_pos_iff.mpr hqne)
  let t : ℝ := (|C| + 1) / ‖S.mkQ w‖
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hh := hbound t
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hh
  have he : t * ‖S.mkQ w‖ = |C| + 1 := by
    dsimp [t]
    have hz : ‖S.mkQ w‖ ≠ 0 := ne_of_gt hnorm
    calc
      ((|C| + 1) / ‖S.mkQ w‖) * ‖S.mkQ w‖ = |C| + 1 := by exact div_mul_cancel₀ _ hz
      _ = |C| + 1 := rfl
  rw [he] at hh
  linarith [le_abs_self C]

end LeanEval.Geometry.LiouvilleArnold.Support
namespace LeanEval.Geometry.LiouvilleArnold.Support
open Set Function Topology Filter

theorem exists_compact_cover_of_local_compact_lifts
    {V X : Type*} [TopologicalSpace V] [TopologicalSpace X]
    (hX : IsCompact (Set.univ : Set X)) (a : V → X)
    (hloc : ∀ y : X, ∃ C : Set V, IsCompact C ∧
       ∃ W ∈ nhds y, W ⊆ a '' C) :
    ∃ K : Set V, IsCompact K ∧ ∀ y : X, ∃ k ∈ K, a k = y := by
  classical
  choose C hC W hWy hWi using hloc
  choose O hOW hOo hyO using fun y : X => (mem_nhds_iff.mp (hWy y))
  have hsub : (Set.univ : Set X) ⊆ ⋃ y : X, O y := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨y, hyO y⟩
  obtain ⟨t, ht⟩ := hX.elim_finite_subcover O hOo hsub
  let K : Set V := ⋃ y ∈ t, C y
  refine ⟨K, t.isCompact_biUnion (by intro i hi; exact hC i), ?_⟩
  intro y
  have hyu : y ∈ ⋃ i ∈ t, O i := ht (Set.mem_univ y)
  rcases Set.mem_iUnion.1 hyu with ⟨i, hyu⟩
  rcases Set.mem_iUnion.1 hyu with ⟨hi, hyOi⟩
  have hyW : y ∈ W i := hOW i hyOi
  rcases hWi i hyW with ⟨k, hk, hky⟩
  refine ⟨k, ?_, hky⟩
  exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hk⟩⟩
end LeanEval.Geometry.LiouvilleArnold.Support

end

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/LatticeClassify.lean

-- BEGIN INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/OrbitDevelop.lean
section
open Set Function Filter
open scoped Topology BigOperators
namespace LeanEval.Geometry.LiouvilleArnold.Support
noncomputable section


theorem wordFlow_update_zero
    {ι X : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → ℝ → X → X)
    (h0 : ∀ i (x : X), φ i 0 x = x) :
    ∀ (l : List ι), l.Nodup → ∀ (i : ι) (t : ℝ) (x : X),
      wordFlow φ l (Function.update (0 : ι → ℝ) i t) x =
        if i ∈ l then φ i t x else x := by
  intro l hl
  induction l with
  | nil =>
      intro i t x
      simp [wordFlow]
  | cons a l ih =>
      intro i t x
      have hna : a ∉ l := (List.nodup_cons.1 hl).1
      have hnl : l.Nodup := (List.nodup_cons.1 hl).2
      have ih' := ih hnl
      by_cases hai : a = i
      · subst a
        have hnot : i ∉ l := hna
        have htail := ih' i t x
        simp [hnot] at htail
        simp [wordFlow, htail, hnot]
      · have hia : i ≠ a := Ne.symm hai
        by_cases hil : i ∈ l
        · have htail := ih' i t x
          simp [hil] at htail
          simp [wordFlow, Function.update_apply,
                hai, hia, hil, htail, h0]
        · have htail := ih' i t x
          simp [hil] at htail
          simp [wordFlow, Function.update_apply,
                hai, hia, hil, htail, h0]


theorem univ_wordFlow_update_zero
    {ι X : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → ℝ → X → X)
    (h0 : ∀ i (x : X), φ i 0 x = x)
    (i : ι) (t : ℝ) (x : X) :
    wordFlow φ (Finset.univ.toList) (Function.update (0 : ι → ℝ) i t) x =
      φ i t x := by
  have h := wordFlow_update_zero φ h0 (Finset.univ.toList)
    (Finset.nodup_toList _) i t x
  simpa using h


theorem update_eq_update_zero_add {ι : Type*} [DecidableEq ι]
    (u : ι → ℝ) (i : ι) (t : ℝ) :
    Function.update u i t =
      (Function.update (0 : ι → ℝ) i (t - u i)) + u := by
  funext j
  classical
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update_apply, h]


theorem hasStrictFDerivAt_orbit_of_action
    {m : ℕ} {X V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (emb : X → V)
    (φ : Fin m → ℝ → X → X)
    (Ψ : (Fin m → ℝ) → X → X)
    (Y : Fin m → V → V)
    (h0 : ∀ i (x : X), φ i 0 x = x)
    (hadd : ∀ a b x, Ψ (a+b) x = Ψ a (Ψ b x))
    (hsingle : ∀ i t x,
      Ψ (Function.update (0 : Fin m → ℝ) i t) x = φ i t x)
    (hd : ∀ i (x : X) (t : ℝ),
      HasDerivAt (fun s : ℝ => emb (φ i s x))
        (Y i (emb (φ i t x))) t)
    (z : X)
    (hc : ∀ i, Continuous (fun u : Fin m → ℝ => Y i (emb (Ψ u z)))) :
    ∀ u : (Fin m → ℝ),
      HasStrictFDerivAt (fun u : Fin m → ℝ => emb (Ψ u z))
        (coordCLM (fun i => Y i (emb (Ψ u z)))) u := by
  classical
  apply hasStrictFDerivAt_pi_of_partials (W:=V) m
    (fun u : Fin m → ℝ => emb (Ψ u z))
    (fun i u => Y i (emb (Ψ u z))) hc
  intro i u
  have heq (s : ℝ) :
      Ψ (Function.update u i s) z =
        φ i (s - u i) (Ψ u z) := by
    rw [update_eq_update_zero_add]
    rw [hadd]
    rw [hsingle]
  have hfun :
      (fun s : ℝ => emb (Ψ (Function.update u i s) z)) =
        (fun s : ℝ => emb (φ i (s - u i) (Ψ u z))) := by
    funext s
    rw [heq]
  rw [hfun]
  have hshift : HasDerivAt (fun r : ℝ => r - u i) (1:ℝ) (u i) := by
    simpa using ((hasDerivAt_id' (u i)).sub_const (u i))
  have hz : (u i - u i : ℝ) = 0 := sub_self _
  have hbase := hd i (Ψ u z) (0:ℝ)
  have hbase' : HasDerivAt (fun s : ℝ => emb (φ i s (Ψ u z)))
      (Y i (emb (φ i 0 (Ψ u z)))) (u i - u i) := by
    simpa using hbase
  have hcomp := HasDerivAt.scomp (F:=V) (h := fun r : ℝ => r - u i)
      (x := u i) hbase' hshift
  simpa [Function.comp_def, h0] using hcomp

end
end LeanEval.Geometry.LiouvilleArnold.Support

end
-- END INLINED FILE: Mathlib/Support/liouville_arnold_c43e57bbdc/OrbitDevelop.lean

-- BEGIN INLINED MAIN PRELUDE


open LeanEval.Geometry.LiouvilleArnold
open Set
open scoped ContDiff
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem liouville_arnold {n : ℕ} (F : Fin n → E n → ℝ) (U : Set (E n)) (_hU : IsOpen U)
    (_hLI : IsLiouvilleIntegrable F U)
    (c : Fin n → ℝ)
    (_hMc_sub : levelSet F c ⊆ U)
    (_hMc_compact : IsCompact (levelSet F c))
    (_hMc_connected : IsConnected (levelSet F c)) :
    Nonempty ((levelSet F c) ≃ₜ (Fin n → AddCircle (1 : ℝ))) :=
/-ResultProofBegin-/by
  set_option maxHeartbeats 1000000 in
    classical
    cases n with
    | zero =>
        let x0 : (levelSet F c) :=
          ⟨(0 : E 0), by
            intro i
            exact Fin.elim0 i⟩
        let y0 : (Fin 0 → AddCircle (1 : ℝ)) :=
          fun i => Fin.elim0 i
        refine ⟨{
          toEquiv := {
            toFun := fun _ => y0
            invFun := fun _ => x0
            left_inv := ?_
            right_inv := ?_ }
          continuous_toFun := continuous_const
          continuous_invFun := continuous_const }⟩
        · intro x
          apply Subtype.ext
          apply PiLp.ext
          intro i
          exact Fin.elim0 i
        · intro y
          funext i
          exact Fin.elim0 i
    | succ n =>
        have hsubm : ∀ x ∈ U, Function.Surjective
            (Support.rowsMap
              (ι := Fin n.succ) (E n.succ)
              (fun i => fderiv ℝ (F i) x)) := by
          intro x hx
          exact
            Support.rowsMap_surjective
              (ι := Fin n.succ) (V := E n.succ)
              (fun i => fderiv ℝ (F i) x) (_hLI.2.2 x hx)
        have htangent : ∀ i j : Fin n.succ, ∀ x ∈ U,
            fderiv ℝ (F j) x
              (Support.hamVec
                (fun k : Fin n.succ => idxP k)
                (fun k : Fin n.succ => idxQ k)
                (fderiv ℝ (F i) x)) = 0 := by
          intro i j x hx
          rw [Support.apply_hamVec]
          exact _hLI.2.1 i j x hx
        have hp : (fun k : Fin n.succ => idxP k) =
            (@Support.pstd n.succ) := by
          funext k
          apply Fin.ext
          rfl
        have hq : (fun k : Fin n.succ => idxQ k) =
            (@Support.qstd n.succ) := by
          funext k
          apply Fin.ext
          rfl
        have hfields : ∀ x ∈ U,
            LinearIndependent ℝ
              (fun i : Fin n.succ =>
                Support.hamVec
                  (fun k : Fin n.succ => idxP k)
                  (fun k : Fin n.succ => idxQ k)
                  (fderiv ℝ (F i) x)) := by
          intro x hx
          rw [hp, hq]
          exact
            Support.independent_hamVec
              (fun i : Fin n.succ => fderiv ℝ (F i) x)
              (_hLI.2.2 x hx)
        have hspan : ∀ x ∈ U,
            Submodule.span ℝ
              (Set.range (fun i : Fin n.succ =>
                Support.hamVec
                  (fun k : Fin n.succ => idxP k)
                  (fun k : Fin n.succ => idxQ k)
                  (fderiv ℝ (F i) x))) =
              LinearMap.ker
                (Support.rowsMap
                  (ι := Fin n.succ) (E n.succ)
                  (fun i => fderiv ℝ (F i) x)) := by
          intro x hx
          rw [hp, hq]
          apply Support.hamVec_span_ker
            (fun i : Fin n.succ => fderiv ℝ (F i) x)
            (_hLI.2.2 x hx)
          intro i j
          have hh := htangent i j x hx
          rw [hp, hq] at hh
          exact hh
        have hv_smooth : ∀ i : Fin n.succ,
            ContDiffOn ℝ ∞
              (fun y : E n.succ =>
                Support.hamVec
                  (fun k : Fin n.succ => idxP k)
                  (fun k : Fin n.succ => idxQ k)
                  (fderiv ℝ (F i) y)) U := by
          intro i
          exact
            Support.contDiffOn_hamVec
              (fun k : Fin n.succ => idxP k)
              (fun k : Fin n.succ => idxQ k)
              _hU (_hLI.1 i)
        have hv_lipschitz : ∀ (i : Fin n.succ) (x : E n.succ), x ∈ U →
            ∃ K : NNReal, ∃ s ∈ nhds x, s ⊆ U ∧
              LipschitzOnWith K
                (fun y : E n.succ =>
                  Support.hamVec
                    (fun k : Fin n.succ => idxP k)
                    (fun k : Fin n.succ => idxQ k)
                    (fderiv ℝ (F i) y)) s := by
          intro i x hx
          exact
            Support.hamVec_exists_lipschitz
              (fun k : Fin n.succ => idxP k)
              (fun k : Fin n.succ => idxQ k)
              _hU (_hLI.1 i) hx
        have hcomplete_of_uniform :
            (∀ i : Fin n.succ, ∃ ε : ℝ, 0 < ε ∧
              ∀ x : levelSet F c, ∃ α : ℝ → E n.succ,
                α 0 = (x : E n.succ) ∧
                (∀ t ∈ Ioo (-ε) ε,
                  HasDerivAt α
                    (Support.hamVec
                      (fun k : Fin n.succ => idxP k)
                      (fun k : Fin n.succ => idxQ k)
                      (fderiv ℝ (F i) (α t))) t) ∧
                MapsTo α (Ioo (-ε) ε) (levelSet F c)) →
            (∀ i : Fin n.succ, ∀ x : levelSet F c,
              ∃ α : ℝ → E n.succ, α 0 = (x : E n.succ) ∧
                (∀ t : ℝ, HasDerivAt α
                  (Support.hamVec
                    (fun k : Fin n.succ => idxP k)
                    (fun k : Fin n.succ => idxQ k)
                    (fderiv ℝ (F i) (α t))) t) ∧
                (∀ t : ℝ, α t ∈ levelSet F c)) := by
          intro hu i
          obtain ⟨ε, hε, hεloc⟩ := hu i
          let v : E n.succ → E n.succ := fun y =>
            Support.hamVec
              (fun k : Fin n.succ => idxP k)
              (fun k : Fin n.succ => idxQ k)
              (fderiv ℝ (F i) y)
          have hlip : ∀ y ∈ levelSet F c,
              ∃ K : NNReal, ∃ W ∈ nhds y, LipschitzOnWith K v W := by
            intro y hy
            obtain ⟨K,W,hW,hWU,hL⟩ := hv_lipschitz i y (_hMc_sub hy)
            exact ⟨K,W,hW,hL⟩
          have hloc' : ∀ y ∈ levelSet F c,
              ∃ g : ℝ → E n.succ, g 0 = y ∧
                Support.ODESolOn v g (Ioo (-ε) ε)
                  ∧ MapsTo g (Ioo (-ε) ε) (levelSet F c) := by
            intro y hy
            obtain ⟨g,g0,gd,gm⟩ := hεloc ⟨y,hy⟩
            exact ⟨g,g0,gd,gm⟩
          have hglob :=
            Support.exists_global_ode_of_uniform
              (v := v) (M := levelSet F c) hlip hε hloc'
          intro x
          simpa [v, Support.ODESolOn]
            using hglob (x : E n.succ) x.property
        let Good (i : Fin n.succ) (y : E n.succ) (r : ℝ) : Prop :=
          ∃ α : ℝ → E n.succ, α 0 = y ∧
            (∀ t ∈ Ioo (-r) r,
              HasDerivAt α
                (Support.hamVec
                  (fun k : Fin n.succ => idxP k)
                  (fun k : Fin n.succ => idxQ k)
                  (fderiv ℝ (F i) (α t))) t) ∧
            MapsTo α (Ioo (-r) r) (levelSet F c)
        have hcomplete_of_boxes :
            (∀ i : Fin n.succ, ∀ y ∈ levelSet F c,
              ∃ W : Set (E n.succ), IsOpen W ∧ y ∈ W ∧
                ∃ r : ℝ, 0 < r ∧ ∀ z ∈ levelSet F c, z ∈ W → Good i z r) →
            (∀ i : Fin n.succ, ∀ x : levelSet F c,
              ∃ α : ℝ → E n.succ, α 0 = (x : E n.succ) ∧
                (∀ t : ℝ, HasDerivAt α
                  (Support.hamVec
                    (fun k : Fin n.succ => idxP k)
                    (fun k : Fin n.succ => idxQ k)
                    (fderiv ℝ (F i) (α t))) t) ∧
                (∀ t : ℝ, α t ∈ levelSet F c)) := by
          intro hb
          apply hcomplete_of_uniform
          intro i
          have hmon : ∀ z : E n.succ, ∀ {u w : ℝ}, 0 < w → w ≤ u →
                Good i z u → Good i z w := by
            intro z u w hw hle hz
            rcases hz with ⟨g,g0,gd,gm⟩
            refine ⟨g,g0,?_,?_⟩
            · intro t ht
              exact gd t ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
                           lt_of_lt_of_le ht.2 hle⟩
            · intro t ht
              exact gm ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
                         lt_of_lt_of_le ht.2 hle⟩
          obtain ⟨r, hr, HG⟩ :=
            Support.compact_uniform_time
              (M := levelSet F c) _hMc_compact _hMc_connected.nonempty
              (P := fun z r => Good i z r) hmon (hb i)
          refine ⟨r, hr, ?_⟩
          intro x
          exact HG (x : E n.succ) x.property
        have hinvariant_on_open_interval : ∀ i : Fin n.succ,
            ∀ {g : ℝ → E n.succ} {a b t₀ : ℝ}, t₀ ∈ Ioo a b →
            g t₀ ∈ levelSet F c →
            (∀ t ∈ Ioo a b, HasDerivAt g
              (Support.hamVec
                (fun k : Fin n.succ => idxP k)
                (fun k : Fin n.succ => idxQ k)
                (fderiv ℝ (F i) (g t))) t) →
            MapsTo g (Ioo a b) U → MapsTo g (Ioo a b) (levelSet F c) := by
          intro i g a b t₀ ht₀ hg0 hd hm t ht j
          have hzero : ∀ y ∈ U, fderiv ℝ (F j) y
              (Support.hamVec
                (fun k : Fin n.succ => idxP k)
                (fun k : Fin n.succ => idxQ k)
                (fderiv ℝ (F i) y)) = 0 := by
            intro y hy
            exact htangent i j y hy
          have hconst :=
            Support.firstIntegral_const_on_Ioo
              (V := E n.succ) (f := F j)
              (v := fun y : E n.succ =>
                Support.hamVec
                  (fun k : Fin n.succ => idxP k)
                  (fun k : Fin n.succ => idxQ k)
                  (fderiv ℝ (F i) y))
              (U := U) _hU ((_hLI.1 j).differentiableOn (by simp)) hzero hd hm
              ht ht₀
          calc
            F j (g t) = F j (g t₀) := hconst
            _ = c j := hg0 j
        have hboxes : ∀ i : Fin n.succ, ∀ y ∈ levelSet F c,
              ∃ W : Set (E n.succ), IsOpen W ∧ y ∈ W ∧
                ∃ r : ℝ, 0 < r ∧ ∀ z ∈ levelSet F c,
                  z ∈ W → Good i z r := by
          intro i y hy
          let v : E n.succ → E n.succ := fun z =>
            Support.hamVec
              (fun k : Fin n.succ => idxP k)
              (fun k : Fin n.succ => idxQ k)
              (fderiv ℝ (F i) z)
          have hv : ContDiffAt ℝ 1 v y :=
            Support.contDiffAt_hamVec
              (fun k : Fin n.succ => idxP k)
              (fun k : Fin n.succ => idxQ k)
              _hU (_hLI.1 i) (_hMc_sub hy)
          obtain ⟨W, hWo, hyW, r, hr, H⟩ :=
            Support.exists_picard_box_in_open
              (v := v) (U := U) _hU (_hMc_sub hy) hv
          refine ⟨W, hWo, hyW, r, hr, ?_⟩
          intro z hz hzW
          obtain ⟨g, g0, gd, gm⟩ := H z hzW
          change ∃ α : ℝ → E n.succ, α 0 = z ∧
            (∀ t ∈ Ioo (-r) r,
              HasDerivAt α
                (Support.hamVec
                  (fun k : Fin n.succ => idxP k)
                  (fun k : Fin n.succ => idxQ k)
                  (fderiv ℝ (F i) (α t))) t) ∧
            MapsTo α (Ioo (-r) r) (levelSet F c)
          refine ⟨g, g0, ?_, ?_⟩
          · intro t ht
            simpa [v] using gd t ht
          · have ht0 : (0 : ℝ) ∈ Ioo (-r) r := by
              constructor <;> linarith
            have hg0' : g 0 ∈ levelSet F c := by
              simpa [g0] using hz
            apply hinvariant_on_open_interval i (g := g)
              (a := -r) (b := r) (t₀ := 0) ht0 hg0'
            · intro t ht
              simpa [v] using gd t ht
            · exact gm
        have hcomplete : ∀ i : Fin n.succ, ∀ x : levelSet F c,
              ∃ α : ℝ → E n.succ, α 0 = (x : E n.succ) ∧
                (∀ t : ℝ, HasDerivAt α
                  (Support.hamVec
                    (fun k : Fin n.succ => idxP k)
                    (fun k : Fin n.succ => idxQ k)
                    (fderiv ℝ (F i) (α t))) t) ∧
                (∀ t : ℝ, α t ∈ levelSet F c) :=
          hcomplete_of_boxes hboxes
        have hflow : ∀ i : Fin n.succ,
            ∃ Φ : ℝ → (levelSet F c) → (levelSet F c),
              (∀ x, Φ 0 x = x) ∧
              (∀ (x : levelSet F c) (t : ℝ),
                HasDerivAt (fun s : ℝ => ((Φ s x : levelSet F c) : E n.succ))
                  (Support.hamVec
                    (fun k : Fin n.succ => idxP k)
                    (fun k : Fin n.succ => idxQ k)
                    (fderiv ℝ (F i) (Φ t x : E n.succ))) t) ∧
              (∀ t u (x : levelSet F c), Φ (t + u) x = Φ t (Φ u x)) ∧
              (∀ t : ℝ, Function.Bijective (Φ t)) := by
          intro i
          let v : E n.succ → E n.succ := fun z =>
            Support.hamVec
              (fun k : Fin n.succ => idxP k)
              (fun k : Fin n.succ => idxQ k)
              (fderiv ℝ (F i) z)
          have hl : ∀ y ∈ levelSet F c,
                ∃ K : NNReal, ∃ W ∈ nhds y, LipschitzOnWith K v W := by
            intro y hy
            obtain ⟨K,W,hW,hWU,hL⟩ := hv_lipschitz i y (_hMc_sub hy)
            exact ⟨K,W,hW,hL⟩
          obtain ⟨Φ,h0,hd,ha,hb⟩ :=
            Support.exists_global_flow_action
              (v := v) (M := levelSet F c) hl (hcomplete i)
          refine ⟨Φ, h0, ?_, ha, hb⟩
          intro x t
          simpa [v] using (hd x t)
        choose Φ hΦ0 hΦd hΦadd hΦbij using hflow
        have hΦjoint : ∀ i : Fin n.succ,
            Continuous (fun p : ℝ × (levelSet F c) => Φ i p.1 p.2) := by
          intro i
          let v : E n.succ → E n.succ := fun z =>
            Support.hamVec
              (fun k : Fin n.succ => idxP k)
              (fun k : Fin n.succ => idxQ k)
              (fderiv ℝ (F i) z)
          have hl : ∀ y ∈ levelSet F c,
                ∃ K : NNReal, ∃ W ∈ nhds y, LipschitzOnWith K v W := by
            intro y hy
            obtain ⟨K,W,hW,hWU,hL⟩ := hv_lipschitz i y (_hMc_sub hy)
            exact ⟨K,W,hW,hL⟩
          exact
            Support.continuous_joint_flow_of_compact
              (v := v) (M := levelSet F c) _hMc_compact hl
              (hΦ0 i)
              (by
                intro x t
                simpa [v] using (hΦd i x t))
        have hcomm_fields : ∀ (i j : Fin n.succ) (x : E n.succ), x ∈ U →
            fderiv ℝ
              (fun y : E n.succ =>
                Support.hamVec
                  (fun k : Fin n.succ => idxP k)
                  (fun k : Fin n.succ => idxQ k)
                  (fderiv ℝ (F j) y)) x
                (Support.hamVec
                  (fun k : Fin n.succ => idxP k)
                  (fun k : Fin n.succ => idxQ k)
                  (fderiv ℝ (F i) x)) =
              fderiv ℝ
                (fun y : E n.succ =>
                  Support.hamVec
                    (fun k : Fin n.succ => idxP k)
                    (fun k : Fin n.succ => idxQ k)
                    (fderiv ℝ (F i) y)) x
                  (Support.hamVec
                    (fun k : Fin n.succ => idxP k)
                    (fun k : Fin n.succ => idxQ k)
                    (fderiv ℝ (F j) x)) := by
          intro i j x hx
          rw [hp, hq]
          apply
            Support.lie_hamVec_zero_of_pair
              (U := U) _hU (_hLI.1 i) (_hLI.1 j) ?_ hx
          intro y hy
          have hh := htangent i j y hy
          rw [hp, hq] at hh
          exact hh
        have hvariation : ∀ (i j : Fin n.succ) (x : levelSet F c) (t : ℝ),
            HasDerivAt
              (fun s : ℝ =>
                Support.hamVec
                  (fun k : Fin n.succ => idxP k)
                  (fun k : Fin n.succ => idxQ k)
                  (fderiv ℝ (F j) (Φ i s x : E n.succ)))
              (fderiv ℝ
                (fun y : E n.succ =>
                  Support.hamVec
                    (fun k : Fin n.succ => idxP k)
                    (fun k : Fin n.succ => idxQ k)
                    (fderiv ℝ (F i) y))
                (Φ i t x : E n.succ)
                (Support.hamVec
                  (fun k : Fin n.succ => idxP k)
                  (fun k : Fin n.succ => idxQ k)
                  (fderiv ℝ (F j) (Φ i t x : E n.succ)))) t := by
          intro i j x t
          let v : E n.succ → E n.succ := fun y =>
            Support.hamVec
              (fun k : Fin n.succ => idxP k)
              (fun k : Fin n.succ => idxQ k)
              (fderiv ℝ (F i) y)
          let w : E n.succ → E n.succ := fun y =>
            Support.hamVec
              (fun k : Fin n.succ => idxP k)
              (fun k : Fin n.succ => idxQ k)
              (fderiv ℝ (F j) y)
          have hv' : DifferentiableOn ℝ v U :=
            (hv_smooth i).differentiableOn (by simp)
          have hw' : DifferentiableOn ℝ w U :=
            (hv_smooth j).differentiableOn (by simp)
          have hb' : ∀ y ∈ U, fderiv ℝ w y (v y) =
                fderiv ℝ v y (w y) := by
            intro y hy
            exact hcomm_fields i j y hy
          have hd' : ∀ r : ℝ,
                HasDerivAt (fun q : ℝ => ((Φ i q x : levelSet F c) : E n.succ))
                  (v (Φ i r x : E n.succ)) r := by
            intro r
            simpa [v] using (hΦd i x r)
          have hm' : ∀ r : ℝ, (Φ i r x : E n.succ) ∈ U := by
            intro r
            exact _hMc_sub (Φ i r x).property
          have hvar :=
            Support.field_along_curve_variation
              (V := E n.succ) (U := U) _hU hv' hw' hb'
              (α := fun r : ℝ => ((Φ i r x : levelSet F c) : E n.succ))
              hd' hm' t
          simpa [v, w] using hvar
        have hword : Continuous
            (fun p : (Fin n.succ → ℝ) × (levelSet F c) =>
              Support.wordFlow
                (fun i : Fin n.succ => Φ i)
                (Finset.univ.toList) p.1 p.2) := by
          exact
            Support.continuous_univ_wordFlow
              (ι := Fin n.succ) (X := levelSet F c) (φ := fun i => Φ i) hΦjoint
        rcases _hMc_connected.nonempty with ⟨xval, hxval⟩
        let xbase : levelSet F c := ⟨xval, hxval⟩
        let dev : (Fin n.succ → ℝ) → (levelSet F c) := fun u =>
          Support.wordFlow
            (fun i : Fin n.succ => Φ i) (Finset.univ.toList) u xbase
        have hdev : Continuous dev := by
          have hp : Continuous
              (fun u : (Fin n.succ → ℝ) => (u, xbase)) :=
            continuous_id.prodMk continuous_const
          simpa [dev, Function.comp_def] using hword.comp hp
        have hquot :
            Nonempty ((levelSet F c) ≃ₜ
              ((Fin n.succ → ℝ) ⧸
                Support.stdLattice (Fin n.succ))) := by
          obtain ⟨e, heq, hesurj⟩ :
              ∃ e : (Fin n.succ → ℝ) ≃L[ℝ] (Fin n.succ → ℝ),
                (∀ u v,
                  dev (e u) = dev (e v) ↔
                    u - v ∈
                      Support.stdLattice (Fin n.succ)) ∧
                Function.Surjective (fun u => dev (e u)) := by
              obtain ⟨L, hLrel, hLdisc, K, hK, hKrep, hsurj⟩ :
                  ∃ L : AddSubgroup (Fin n.succ → ℝ),
                    (∀ a b, dev a = dev b ↔ a - b ∈ L) ∧
                    IsDiscrete (L : Set (Fin n.succ → ℝ)) ∧
                    ∃ K : Set (Fin n.succ → ℝ), IsCompact K ∧
                      (∀ u : Fin n.succ → ℝ, ∃ k ∈ K, u - k ∈ L) ∧
                      Function.Surjective dev := by
                let Ψ : (Fin n.succ → ℝ) → (levelSet F c) → (levelSet F c) := fun u z =>
                  Support.wordFlow (fun i : Fin n.succ => Φ i) (Finset.univ.toList) u z
                obtain ⟨hc, hd, hl⟩ :
                    (∀ i j : Fin n.succ, ∀ t u : ℝ, ∀ z : levelSet F c, Φ i t (Φ j u z) = Φ j u (Φ i t z)) ∧
                    IsDiscrete ({u : Fin n.succ → ℝ | Ψ u xbase = xbase} : Set _) ∧
                    (∀ y : levelSet F c, ∃ C : Set (Fin n.succ → ℝ), IsCompact C ∧ ∃ W ∈ nhds y, W ⊆ dev '' C) := by
                  have hc_from_mixed :
                      (∀ i j : Fin n.succ, i ≠ j → ∀ T : ℝ,
                        ∀ z : levelSet F c,
                          HasDerivAt
                            (fun r : ℝ =>
                              ((Φ i T (Φ j r z) : levelSet F c) : E n.succ))
                            (Support.hamVec
                              (fun q : Fin n.succ => idxP q)
                              (fun q : Fin n.succ => idxQ q)
                              (fderiv ℝ (F j) (Φ i T z : E n.succ))) 0) →
                      (∀ i j : Fin n.succ, ∀ T u : ℝ,
                        ∀ z : levelSet F c,
                          Φ i T (Φ j u z) = Φ j u (Φ i T z)) := by
                    intro hm
                    let X : Fin n.succ → E n.succ → E n.succ := fun j z =>
                      Support.hamVec
                        (fun q : Fin n.succ => idxP q)
                        (fun q : Fin n.succ => idxQ q)
                        (fderiv ℝ (F j) z)
                    have hloc : ∀ j : Fin n.succ, ∀ z ∈ levelSet F c,
                        ∃ K : NNReal, ∃ W ∈ nhds z, LipschitzOnWith K (X j) W := by
                      intro j z hz
                      obtain ⟨K,W,hW,hWU,hLW⟩ :=
                        hv_lipschitz j z (_hMc_sub hz)
                      exact ⟨K,W,hW,by simpa [X] using hLW⟩
                    exact
                      Support.commute_family_of_mixed_zero
                        (M := levelSet F c) (X := X) (Φ := Φ) hloc
                        hΦ0
                        (by
                          intro j z t
                          simpa [X] using (hΦd j z t))
                        hΦadd
                        (by
                          intro i j hne T z
                          simpa [X] using (hm i j hne T z))
                  have hmixed :
                      ∀ i j : Fin n.succ, i ≠ j → ∀ T : ℝ,
                        ∀ z : levelSet F c,
                          HasDerivAt
                            (fun r : ℝ =>
                              ((Φ i T (Φ j r z) : levelSet F c) : E n.succ))
                            (Support.hamVec
                              (fun q : Fin n.succ => idxP q)
                              (fun q : Fin n.succ => idxQ q)
                              (fderiv ℝ (F j) (Φ i T z : E n.succ))) 0 := by
                    intro i j hij
                    let v : E n.succ → E n.succ := fun z =>
                      Support.hamVec
                        (fun q : Fin n.succ => idxP q)
                        (fun q : Fin n.succ => idxQ q)
                        (fderiv ℝ (F i) z)
                    let w : E n.succ → E n.succ := fun z =>
                      Support.hamVec
                        (fun q : Fin n.succ => idxP q)
                        (fun q : Fin n.succ => idxQ q)
                        (fderiv ℝ (F j) z)
                    have hv' : DifferentiableOn ℝ v U :=
                      (hv_smooth i).differentiableOn (by simp)
                    have hcv : ContinuousOn (fderiv ℝ v) U :=
                      (hv_smooth i).continuousOn_fderiv_of_isOpen _hU (by simp)
                    have hlc : LocallyLipschitzOn (levelSet F c) v := by
                      intro a ha
                      obtain ⟨K,W,hW,hWU,hLW⟩ :=
                        hv_lipschitz i a (_hMc_sub ha)
                      exact ⟨K,W, mem_nhdsWithin_of_mem_nhds hW,
                        by simpa [v] using hLW⟩
                    obtain ⟨L,hL⟩ := hlc.exists_lipschitzOnWith_of_compact _hMc_compact
                    exact
                      Support.deriv_initial_all
                        (V:= E n.succ) (M:= levelSet F c) (U:=U)
                        (v:=v) (w:=w)
                        _hMc_compact _hMc_connected.nonempty _hU _hMc_sub
                        hv' hcv L hL
                        (φ:= Φ i) (ψ:= Φ j) (hΦ0 i)
                        (by
                          intro a t
                          simpa [v] using (hΦd i a t))
                        (hΦ0 j)
                        (by
                          intro a
                          simpa [w, hΦ0 j a] using (hΦd j a 0))
                        (by
                          intro a t
                          simpa [v, w] using (hvariation i j a t))
                  have hc' :
                      ∀ i j : Fin n.succ, ∀ t u : ℝ,
                        ∀ z : levelSet F c,
                          Φ i t (Φ j u z) = Φ j u (Φ i t z) :=
                    hc_from_mixed hmixed
                  refine ⟨hc', ?_⟩
                  obtain ⟨hΨ0, hΨadd⟩ :=
                    Support.wordFlow_action
                      (X:= levelSet F c) (ι:= Fin n.succ)
                      (φ:= fun i : Fin n.succ => Φ i)
                      hΦ0 hΦadd hc' (Finset.univ.toList)
                  have horbit_chart : ∀ z : levelSet F c,
                      ∃ r : ℝ, 0 < r ∧
                        Set.InjOn (fun u : (Fin n.succ → ℝ) => Ψ u z)
                          (Metric.ball 0 r) ∧
                        ∃ W ∈ nhds z,
                          W ⊆ (fun u : (Fin n.succ → ℝ) => Ψ u z) ''
                            (Metric.ball 0 r) := by
                    intro z
                    let X : Fin n.succ → E n.succ → E n.succ := fun i y =>
                      Support.hamVec
                        (fun q : Fin n.succ => idxP q)
                        (fun q : Fin n.succ => idxQ q)
                        (fderiv ℝ (F i) y)
                    let g : (Fin n.succ → ℝ) → E n.succ := fun u =>
                      ((Ψ u z : levelSet F c) : E n.succ)
                    let f0 : E n.succ → (Fin n.succ → ℝ) := fun y i => F i y
                    have hzU : (z : E n.succ) ∈ U := _hMc_sub z.property
                    let R : E n.succ →ₗ[ℝ] (Fin n.succ → ℝ) :=
                      Support.rowsMap
                        (ι := Fin n.succ) (E n.succ)
                        (fun i => fderiv ℝ (F i) (z : E n.succ))
                    let w0 : Fin n.succ → E n.succ := fun i => X i (z : E n.succ)
                    have hRs : Function.Surjective R := by
                      dsimp [R]
                      exact hsubm (z : E n.succ) hzU
                    have hwi : LinearIndependent ℝ w0 := by
                      dsimp [w0, X]
                      exact hfields (z : E n.succ) hzU
                    have hke : Submodule.span ℝ (Set.range w0) = LinearMap.ker R := by
                      dsimp [w0, R, X]
                      exact hspan (z : E n.succ) hzU
                    obtain ⟨q, hqfirst, hqrow⟩ :=
                      Support.exists_frame_equiv
                        R hRs w0 hwi hke
                    have hFstrict (i : Fin n.succ) :
                        HasStrictFDerivAt (F i)
                          (fderiv ℝ (F i) (z : E n.succ)) (z : E n.succ) := by
                      have hi : ContDiffAt ℝ ∞ (F i) (z : E n.succ) :=
                        (_hLI.1 i).contDiffAt (_hU.mem_nhds hzU)
                      exact hi.hasStrictFDerivAt (by simp)
                    have hfpi : HasStrictFDerivAt f0
                        (ContinuousLinearMap.pi
                          (fun i : Fin n.succ => fderiv ℝ (F i) (z : E n.succ)))
                        (z : E n.succ) := by
                      exact (hasStrictFDerivAt_pi).2 (fun i => hFstrict i)
                    have hfmap :
                        (ContinuousLinearMap.pi
                          (fun i : Fin n.succ => fderiv ℝ (F i) (z : E n.succ))) =
                          (ContinuousLinearMap.snd ℝ
                            (Fin n.succ → ℝ) (Fin n.succ → ℝ)).comp
                              (q.symm : E n.succ →L[ℝ]
                                ((Fin n.succ → ℝ) × (Fin n.succ → ℝ))) := by
                      apply ContinuousLinearMap.ext
                      intro y
                      funext k
                      have hy := hqrow (q.symm y)
                      have hy' : R y = (q.symm y).2 := by
                        simpa using hy
                      exact congrFun hy' k
                    have hfstr : HasStrictFDerivAt f0
                        ((ContinuousLinearMap.snd ℝ
                          (Fin n.succ → ℝ) (Fin n.succ → ℝ)).comp
                            (q.symm : E n.succ →L[ℝ]
                              ((Fin n.succ → ℝ) × (Fin n.succ → ℝ))))
                        (z : E n.succ) := by
                      rw [← hfmap]
                      exact hfpi
                    have hsingle : ∀ i : Fin n.succ, ∀ t : ℝ,
                        ∀ x : levelSet F c,
                        Ψ (Function.update (0 : Fin n.succ → ℝ) i t) x =
                          Φ i t x := by
                      intro i t x
                      simpa [Ψ] using
                        (Support.univ_wordFlow_update_zero
                          (φ := fun i : Fin n.succ => Φ i)
                          (fun i x => hΦ0 i x) i t x)
                    have hpsicont : Continuous (fun u : (Fin n.succ → ℝ) => Ψ u z) := by
                      have hpair : Continuous
                          (fun u : (Fin n.succ → ℝ) => (u, z)) :=
                        continuous_id.prodMk continuous_const
                      simpa [Ψ, Function.comp_def] using hword.comp hpair
                    have hcoordcont : ∀ i : Fin n.succ,
                        Continuous (fun u : (Fin n.succ → ℝ) => X i (g u)) := by
                      intro i
                      have hXiU : ContinuousOn (X i) U := by
                        simpa [X] using (hv_smooth i).continuousOn
                      have hXiM : Continuous
                          (fun x : levelSet F c => X i (x : E n.succ)) := by
                        exact hXiU.comp_continuous continuous_subtype_val
                          (fun y : levelSet F c => _hMc_sub y.property)
                      exact (hXiM.comp hpsicont)
                    have hgpi_all : ∀ u : (Fin n.succ → ℝ),
                        HasStrictFDerivAt g
                          (Support.coordCLM
                            (fun i : Fin n.succ => X i
                              ((Ψ u z : levelSet F c) : E n.succ))) u := by
                      have hh :=
                        Support.hasStrictFDerivAt_orbit_of_action
                          (emb := fun x : levelSet F c => (x : E n.succ))
                          (φ := fun i : Fin n.succ => Φ i) (Ψ := Ψ) (Y := X)
                          (fun i x => hΦ0 i x) hΨadd hsingle
                          (by
                            intro i x t
                            simpa [X] using (hΦd i x t)) z hcoordcont
                      simpa [g] using hh
                    have hYmap :
                        Support.coordCLM w0 =
                          (q : ((Fin n.succ → ℝ) × (Fin n.succ → ℝ)) →L[ℝ]
                            E n.succ).comp
                            (ContinuousLinearMap.inl ℝ
                              (Fin n.succ → ℝ) (Fin n.succ → ℝ)) := by
                      apply ContinuousLinearMap.ext
                      intro u
                      have hu := hqfirst u
                      simpa [Support.coordCLM_apply]
                        using hu.symm
                    have hgstr : HasStrictFDerivAt g
                        ((q : ((Fin n.succ → ℝ) × (Fin n.succ → ℝ)) →L[ℝ]
                          E n.succ).comp
                          (ContinuousLinearMap.inl ℝ
                            (Fin n.succ → ℝ) (Fin n.succ → ℝ)))
                        (0 : Fin n.succ → ℝ) := by
                      have h := hgpi_all (0 : Fin n.succ → ℝ)
                      have hwz : (fun i : Fin n.succ =>
                            X i ((Ψ (0 : Fin n.succ → ℝ) z : levelSet F c) : E n.succ)) =
                            w0 := by
                        funext i
                        simp [Ψ, hΨ0 z, w0]
                      rw [hwz, hYmap] at h
                      exact h
                    have hgzero : g (0 : Fin n.succ → ℝ) = (z : E n.succ) := by
                      simp [g, Ψ, hΨ0 z]
                    have hlevel : ∀ u : Fin n.succ → ℝ, f0 (g u) = f0 (z : E n.succ) := by
                      intro u
                      funext i
                      change F i ((Ψ u z : levelSet F c) : E n.succ) = F i (z : E n.succ)
                      calc
                        F i ((Ψ u z : levelSet F c) : E n.succ) = c i := (Ψ u z).property i
                        _ = F i (z : E n.succ) := (z.property i).symm
                    obtain ⟨r, hr, hrinj, N, hN, hNs⟩ :=
                      Support.local_level_chart_of_frame
                        q (z : E n.succ) f0 g hgzero hfstr hgstr hlevel
                    refine ⟨r, hr, ?_, ?_⟩
                    · intro a ha b hb hab
                      apply hrinj ha hb
                      exact congrArg (fun x : levelSet F c => (x : E n.succ)) hab
                    · let W : Set (levelSet F c) :=
                        (fun x : levelSet F c => (x : E n.succ)) ⁻¹' N
                      have hW : W ∈ nhds z := by
                        exact (continuous_subtype_val.continuousAt).preimage_mem_nhds hN
                      refine ⟨W, hW, ?_⟩
                      intro y hy
                      have hyN : (y : E n.succ) ∈ N := hy
                      have hfy : f0 (y : E n.succ) = f0 (z : E n.succ) := by
                        funext i
                        change F i (y : E n.succ) = F i (z : E n.succ)
                        exact (y.property i).trans (z.property i).symm
                      obtain ⟨u, hu, huval⟩ := hNs (y : E n.succ) hyN hfy
                      refine ⟨u, hu, ?_⟩
                      apply Subtype.ext
                      exact huval
                  have hcharts : ∀ z : levelSet F c,
                      ∃ D : Set (Fin n.succ → ℝ), IsCompact D ∧
                        ∃ W ∈ nhds z, W ⊆
                          (fun u : (Fin n.succ → ℝ) => Ψ u z) '' D := by
                    apply Support.compact_chart_of_ball
                    intro z
                    obtain ⟨r,hr,hinj,W,hW,hs⟩ := horbit_chart z
                    exact ⟨r,hr,W,hW,hs⟩
                  have hdiscId :
                      IsDiscrete ({u : Fin n.succ → ℝ | Ψ u xbase = xbase} :
                        Set (Fin n.succ → ℝ)) := by
                    obtain ⟨r,hr,hinj,W,hW,hsub⟩ := horbit_chart xbase
                    apply
                      Support.action_stabilizer_discrete_of_isolated
                        (Ψ:= Ψ) (z:= xbase) hΨ0 hΨadd
                    refine ⟨Metric.ball (0 : Fin n.succ → ℝ) r,
                      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr), ?_⟩
                    intro a ha hax
                    have hz : Ψ 0 xbase = xbase := by simpa [Ψ] using hΨ0 xbase
                    have heq : Ψ a xbase = Ψ 0 xbase := hax.trans hz.symm
                    exact hinj ha (Metric.mem_ball_self hr) heq
                  refine ⟨hdiscId, ?_⟩
                  letI : PreconnectedSpace (levelSet F c) :=
                    Subtype.preconnectedSpace _hMc_connected.isPreconnected
                  letI : Nonempty (levelSet F c) := ⟨xbase⟩
                  intro y
                  obtain ⟨C,hC,W,hW,hsub⟩ :=
                    Support.compact_lifts_of_local_orbit_charts
                      (A := Fin n.succ → ℝ) (X := levelSet F c)
                      Ψ hΨ0 hΨadd hcharts xbase y
                  refine ⟨C,hC,W,hW,?_⟩
                  simpa [dev, Ψ] using hsub
                obtain ⟨hz,ha⟩ := Support.wordFlow_action (X:=levelSet F c) (ι:=Fin n.succ) (φ:=fun i : Fin n.succ => Φ i) hΦ0 hΦadd hc (Finset.univ.toList)
                obtain ⟨L,hfix,hrel⟩ := Support.orbit_stabilizer_addsubgroup (Ψ:=Ψ) hz ha xbase
                have hdev' : ∀ u, dev u = Ψ u xbase := by intro u; rfl
                have hcarrier : (L : Set (Fin n.succ → ℝ)) =
                      {u : Fin n.succ → ℝ | Ψ u xbase = xbase} := by
                    ext u
                    exact hfix u
                have hdisc : IsDiscrete (L : Set (Fin n.succ → ℝ)) := by
                  rw [hcarrier]
                  exact hd
                letI : CompactSpace (levelSet F c) := (isCompact_iff_compactSpace.mp _hMc_compact)
                obtain ⟨K,hK,hkl⟩ := Support.exists_compact_cover_of_local_compact_lifts (isCompact_univ : IsCompact (Set.univ : Set (levelSet F c))) dev hl
                refine ⟨L, ?_, hdisc, K, hK, ?_, ?_⟩
                · intro a b; simpa [hdev'] using (hrel a b)
                · intro u
                  obtain ⟨k,hk,hv⟩ := hkl (dev u)
                  exact ⟨k,hk,(hrel _ _).1 (by simpa [hdev'] using hv.symm)⟩
                · intro y; obtain ⟨k,hk,hv⟩ := hkl y; exact ⟨k,hv⟩
              have hLspan : Submodule.span ℝ
                  (L : Set (Fin n.succ → ℝ)) = ⊤ :=
                Support.span_eq_top_of_compact_addsubgroup_cover
                  L hK hKrep
              obtain ⟨e, he_mem⟩ :=
                Support.exists_linear_equiv_mem_std_of_discrete_span
                  L hLdisc hLspan
              refine ⟨e, ?_, ?_⟩
              · intro u v
                rw [hLrel]
                simpa using (he_mem (u-v))
              · intro y
                rcases hsurj y with ⟨u,rfl⟩
                refine ⟨e.symm u, ?_⟩
                simp
          have hecont : Continuous (fun u : (Fin n.succ → ℝ) => dev (e u)) :=
            hdev.comp e.continuous
          exact
            Support.nonempty_homeomorph_stdQuotient_of_orbit
              (a := fun u : (Fin n.succ → ℝ) => dev (e u)) hecont heq hesurj
        rcases hquot with ⟨hquot⟩
        rcases Support.stdQuotient_homeomorph_torus
          (ι := Fin n.succ) with ⟨htorus⟩
        exact ⟨hquot.trans htorus⟩
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
