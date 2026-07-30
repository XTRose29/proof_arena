import Mathlib
import ChallengeDeps

namespace Submission.Helpers

open Function Module Set Topology
open scoped ContDiff NNReal Topology BigOperators

/-- The coordinatewise quotient map from Euclidean space to the unit additive torus. -/
def torusQuotientMap (n : ℕ) : (Fin n → ℝ) → (Fin n → AddCircle (1 : ℝ)) :=
  fun x i ↦ (x i : AddCircle (1 : ℝ))

theorem continuous_torusQuotientMap (n : ℕ) : Continuous (torusQuotientMap n) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' 1).comp (continuous_apply i)

theorem surjective_torusQuotientMap (n : ℕ) : Surjective (torusQuotientMap n) := by
  intro y
  choose x hx using fun i ↦ QuotientAddGroup.mk_surjective (y i)
  exact ⟨x, funext hx⟩

theorem isOpenMap_torusQuotientMap (n : ℕ) : IsOpenMap (torusQuotientMap n) := by
  change IsOpenMap (Pi.map fun _ : Fin n ↦
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)) : ℝ → AddCircle (1 : ℝ)))
  apply IsOpenMap.piMap
  · intro i
    exact QuotientAddGroup.isOpenMap_coe
  · filter_upwards [] with i
    exact QuotientAddGroup.mk_surjective

theorem isOpenQuotientMap_torusQuotientMap (n : ℕ) :
    IsOpenQuotientMap (torusQuotientMap n) :=
  ⟨surjective_torusQuotientMap n, continuous_torusQuotientMap n,
    isOpenMap_torusQuotientMap n⟩

theorem torusQuotientMap_eq_iff {n : ℕ} (x y : Fin n → ℝ) :
    torusQuotientMap n x = torusQuotientMap n y ↔
      ∀ i, ∃ z : ℤ, (z : ℝ) = x i - y i := by
  rw [funext_iff]
  constructor
  · intro h i
    have hi : ((x i - y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, sub_eq_zero]
      exact h i
    rw [AddCircle.coe_eq_zero_iff] at hi
    simpa using hi
  · intro h i
    change (x i : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ))
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    simpa using h i

section Lattice

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Coordinates associated to a `ℤ`-basis of a full lattice. -/
noncomputable def latticeCoordinates (b : Basis ι ℤ L) : E ≃L[ℝ] (ι → ℝ) :=
  (b.ofZLatticeBasis ℝ).equivFunL

theorem mem_lattice_iff_coordinates_integral (b : Basis ι ℤ L) (x : E) :
    x ∈ L ↔ ∀ i, ∃ z : ℤ, (z : ℝ) = latticeCoordinates L b x i := by
  constructor
  · intro hx i
    refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
    exact (b.ofZLatticeBasis_repr_apply ℝ L ⟨x, hx⟩ i).symm
  · intro hx
    choose z hz using hx
    let v : L := ∑ i, z i • b i
    have hvcoord (i : ι) : latticeCoordinates L b (v : E) i = (z i : ℝ) := by
      simp [latticeCoordinates, v, Finsupp.single_apply]
    have hv : (v : E) = x := by
      apply (latticeCoordinates L b).injective
      ext i
      rw [hvcoord i, hz i]
    rw [← hv]
    exact v.property

end Lattice

section LatticeQuotient

variable {n : ℕ} {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- An open quotient by a full lattice is homeomorphic to a unit additive torus. -/
noncomputable def homeomorphTorusOfLatticeQuotient
    (b : Basis (Fin n) ℤ L) (f : E → M) (hf : IsQuotientMap f)
    (hker : ∀ x y, f x = f y ↔ x - y ∈ L) :
    M ≃ₜ (Fin n → AddCircle (1 : ℝ)) := by
  let e := latticeCoordinates L b
  let fc : C(E, M) := ⟨f, hf.continuous⟩
  let qc : C(Fin n → ℝ, Fin n → AddCircle (1 : ℝ)) :=
    ⟨torusQuotientMap n, continuous_torusQuotientMap n⟩
  have hrel (x y : E) : Setoid.ker fc x y ↔
      Setoid.ker qc (e x) (e y) := by
    change f x = f y ↔ torusQuotientMap n (e x) = torusQuotientMap n (e y)
    rw [hker, torusQuotientMap_eq_iff,
      mem_lattice_iff_coordinates_integral L b (x - y)]
    simp [e]
  let h₁ : M ≃ₜ Quotient (Setoid.ker fc) :=
    (Topology.IsQuotientMap.homeomorph
      (X := E) (Y := M) (f := fc) hf).symm
  let h₂ : Quotient (Setoid.ker fc) ≃ₜ
      Quotient (Setoid.ker qc) :=
    Homeomorph.Quotient.congr e.toHomeomorph hrel
  let h₃ : Quotient (Setoid.ker qc) ≃ₜ
      (Fin n → AddCircle (1 : ℝ)) :=
    Topology.IsQuotientMap.homeomorph
      (X := Fin n → ℝ) (Y := Fin n → AddCircle (1 : ℝ))
      (f := qc)
      (isOpenQuotientMap_torusQuotientMap n).isQuotientMap
  exact h₁.trans (h₂.trans h₃)

end LatticeQuotient

section CompactQuotient

variable {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [CompactSpace M]
  (L : Submodule ℤ E) [DiscreteTopology L]

set_option maxHeartbeats 800000 in
/-- A discrete subgroup with a compact topological quotient spans the ambient real vector space. -/
theorem isZLattice_of_compact_quotient
    (f : E → M) (hf : IsQuotientMap f)
    (hker : ∀ x y, f x = f y ↔ x - y ∈ L) : IsZLattice ℝ L := by
  constructor
  let W : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  by_contra hW
  have hW' : W ≠ ⊤ := by simpa [W] using hW
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ W := by
    by_contra h
    push Not at h
    exact hW' (eq_top_iff.mpr fun y _ ↦ h y)
  letI : IsClosed (W : Set E) := W.closed_of_finiteDimensional
  let g : C(E, ℝ) :=
    ⟨fun y ↦ ‖W.mkQL y‖, W.mkQL.continuous.norm⟩
  have hg : Function.FactorsThrough g f := by
    intro a b hab
    have habL : a - b ∈ L := (hker a b).mp hab
    have habW : a - b ∈ W := Submodule.subset_span habL
    have heq : W.mkQL a = W.mkQL b := by
      rw [← sub_eq_zero, ← map_sub]
      change (Submodule.Quotient.mk (a - b) : E ⧸ W) = 0
      exact (Submodule.Quotient.mk_eq_zero W).2 habW
    exact congrArg norm heq
  let fc : C(E, M) := ⟨f, hf.continuous⟩
  have hfc : IsQuotientMap fc := hf
  have hgc : Function.FactorsThrough g fc := hg
  let gbar : C(M, ℝ) := hfc.lift g hgc
  letI : Nonempty M := ⟨f 0⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    gbar.continuous.continuousOn
  have hcomp (y : E) : gbar (f y) = g y := by
    change hfc.lift g hgc (fc y) = g y
    exact DFunLike.congr_fun (hfc.lift_comp g hgc) y
  have hm_nonneg : 0 ≤ gbar m := by
    obtain ⟨y, rfl⟩ := hf.surjective m
    rw [hcomp]
    change 0 ≤ ‖W.mkQL y‖
    exact norm_nonneg _
  have hnorm : 0 < ‖W.mkQL x‖ := by
    rw [norm_pos_iff]
    simpa [Submodule.Quotient.mk_eq_zero] using hx
  let t : ℝ := (gbar m + 1) / ‖W.mkQL x‖
  have ht : 0 < t := div_pos (by linarith) hnorm
  have hlarge : g (t • x) = gbar m + 1 := by
    simp only [g, ContinuousMap.coe_mk, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht, t]
    exact div_mul_cancel₀ _ hnorm.ne'
  have hle : g (t • x) ≤ gbar m := by
    rw [← hcomp]
    exact hm (Set.mem_univ _)
  rw [hlarge] at hle
  linarith

/-- A compact open quotient of `ℝⁿ` by a discrete additive subgroup is an `n`-torus. -/
theorem nonempty_homeomorph_torus_of_compact_discrete_quotient
    {n : ℕ} [T2Space M] (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L]
    (f : (Fin n → ℝ) → M) (hf : IsQuotientMap f)
    (hker : ∀ x y, f x = f y ↔ x - y ∈ L) :
    Nonempty (M ≃ₜ (Fin n → AddCircle (1 : ℝ))) := by
  letI : IsZLattice ℝ L := isZLattice_of_compact_quotient L f hf hker
  exact ⟨homeomorphTorusOfLatticeQuotient L (IsZLattice.basis L) f hf hker⟩

end CompactQuotient

section FlowQuotient

variable {V M : Type*} [TopologicalSpace V] [AddCommGroup V] [ContinuousAdd V]
  [TopologicalSpace M]

/-- The additive stabilizer of a point under a flow. -/
def flowStabilizerAddSubgroup (φ : Flow V M) (x : M) : AddSubgroup V where
  carrier := {t | φ t x = x}
  zero_mem' := φ.map_zero_apply x
  add_mem' {a b} ha hb := by
    change φ (a + b) x = x
    rw [φ.map_add, hb, ha]
  neg_mem' {a} ha := by
    calc
      φ (-a) x = φ (-a) (φ a x) := congrArg (φ (-a)) ha.symm
      _ = φ (-a + a) x := (φ.map_add (-a) a x).symm
      _ = x := by simp [φ.map_zero_apply]

/-- The stabilizer, regarded as a `ℤ`-submodule. -/
def flowStabilizer (φ : Flow V M) (x : M) : Submodule ℤ V :=
  (flowStabilizerAddSubgroup φ x).toIntSubmodule

theorem flow_orbitMap_eq_iff {φ : Flow V M} {x : M} (a b : V) :
    φ a x = φ b x ↔ a - b ∈ flowStabilizer φ x := by
  change φ a x = φ b x ↔ φ (a - b) x = x
  constructor
  · intro h
    calc
      φ (a - b) x = φ (-b + a) x := by rw [sub_eq_add_neg, add_comm]
      _ = φ (-b) (φ a x) := φ.map_add (-b) a x
      _ = φ (-b) (φ b x) := congrArg (φ (-b)) h
      _ = φ (-b + b) x := (φ.map_add (-b) b x).symm
      _ = x := by simp [φ.map_zero_apply]
  · intro h
    calc
      φ a x = φ (b + (a - b)) x := by congr 1; abel
      _ = φ b (φ (a - b) x) := φ.map_add b (a - b) x
      _ = φ b x := congrArg (φ b) h

variable [T2Space M] [CompactSpace M]

/-- A transitive locally free `ℝⁿ`-flow on a compact Hausdorff space presents that space as a
torus. The local-freeness hypothesis is expressed by discreteness of the stabilizer. -/
theorem nonempty_homeomorph_torus_of_flow
    {n : ℕ} (φ : Flow (Fin n → ℝ) M) (x : M)
    (hsurj : Surjective fun t ↦ φ t x)
    [DiscreteTopology (flowStabilizer φ x)] :
    Nonempty (M ≃ₜ (Fin n → AddCircle (1 : ℝ))) := by
  letI : AddAction (Fin n → ℝ) M := φ.toAddAction
  letI : ContinuousVAdd (Fin n → ℝ) M := ⟨φ.cont'⟩
  letI : AddAction.IsPretransitive (Fin n → ℝ) M := by
    constructor
    intro y z
    obtain ⟨a, rfl⟩ := hsurj y
    obtain ⟨b, rfl⟩ := hsurj z
    refine ⟨b - a, ?_⟩
    change φ (b - a) (φ a x) = φ b x
    rw [← φ.map_add]
    congr 1
    abel
  have hcont : Continuous (fun t ↦ φ t x) := φ.continuous continuous_id continuous_const
  have hopen : IsOpenMap (fun t ↦ φ t x) := isOpenMap_vadd_of_sigmaCompact x
  have hquot : IsQuotientMap (fun t ↦ φ t x) :=
    (⟨hsurj, hcont, hopen⟩ : IsOpenQuotientMap fun t ↦ φ t x).isQuotientMap
  exact nonempty_homeomorph_torus_of_compact_discrete_quotient
    (flowStabilizer φ x) (fun t ↦ φ t x) hquot (flow_orbitMap_eq_iff · ·)

variable [PreconnectedSpace M] [Nonempty M]

/-- A flow whose orbit maps are local homeomorphisms has a single orbit on a preconnected space;
its stabilizers are automatically discrete. On a compact Hausdorff space this yields a torus. -/
theorem nonempty_homeomorph_torus_of_local_homeomorph_orbits
    {n : ℕ} (φ : Flow (Fin n → ℝ) M)
    (hlocal : ∀ y : M, IsLocalHomeomorph fun t ↦ φ t y) :
    Nonempty (M ≃ₜ (Fin n → AddCircle (1 : ℝ))) := by
  let x : M := Classical.choice (inferInstance : Nonempty M)
  let orbit : Set M := Set.range fun t ↦ φ t x
  have hopen_orbit : IsOpen orbit := by
    change IsOpen (Set.range fun t ↦ φ t x)
    rw [← Set.image_univ]
    exact (hlocal x).isOpenMap _ isOpen_univ
  have hopen_compl : IsOpen orbitᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    let yorbit : Set M := Set.range fun t ↦ φ t y
    have hopen_yorbit : IsOpen yorbit := by
      change IsOpen (Set.range fun t ↦ φ t y)
      rw [← Set.image_univ]
      exact (hlocal y).isOpenMap _ isOpen_univ
    apply Filter.mem_of_superset (hopen_yorbit.mem_nhds ⟨0, φ.map_zero_apply y⟩)
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzx
    obtain ⟨t, rfl⟩ := hz
    obtain ⟨a, ha⟩ := hzx
    apply hy
    refine ⟨-t + a, ?_⟩
    calc
      φ (-t + a) x = φ (-t) (φ a x) := φ.map_add (-t) a x
      _ = φ (-t) (φ t y) := congrArg (φ (-t)) ha
      _ = φ (-t + t) y := (φ.map_add (-t) t y).symm
      _ = y := by simp [φ.map_zero_apply]
  have horbit : orbit = Set.univ := by
    apply IsClopen.eq_univ ⟨isOpen_compl_iff.mp hopen_compl, hopen_orbit⟩
    exact ⟨x, ⟨0, φ.map_zero_apply x⟩⟩
  have hsurj : Surjective fun t ↦ φ t x := by
    rw [← Set.range_eq_univ]
    exact horbit
  have himage :
      (fun t ↦ φ t x) '' (flowStabilizer φ x : Set (Fin n → ℝ)) = {x} := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · rintro rfl
      exact ⟨0, φ.map_zero_apply x, φ.map_zero_apply x⟩
  letI : DiscreteTopology
      ((fun t ↦ φ t x) '' (flowStabilizer φ x : Set (Fin n → ℝ))) := by
    rw [himage]
    infer_instance
  letI : DiscreteTopology (flowStabilizer φ x) :=
    (hlocal x).isLocalHomeomorphOn.discreteTopology_of_image
  exact nonempty_homeomorph_torus_of_flow φ x hsurj

end FlowQuotient

section CompleteVectorField

open Metric ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v : E → E} {K L : ℝ≥0}

theorem exists_integralCurveOn_symmetric_of_lipschitz_bounded
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L)
    (x : E) {a : ℝ} (ha : 0 < a) :
    ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Ioo (-a) a, HasDerivAt γ (v (γ t)) t := by
  let aNN : ℝ≥0 := ⟨a, ha.le⟩
  let t0 : Icc (-a) a := ⟨0, by simp [ha.le]⟩
  have hpl : IsPicardLindelof (fun _ : ℝ ↦ v) t0 x (L * aNN) 0 L K := by
    apply IsPicardLindelof.of_time_independent
    · intro y _
      exact hbound y
    · exact hv.lipschitzOnWith
    · norm_num [t0]
      rw [show (aNN : ℝ) = a by rfl]
  obtain ⟨γ, hγ0, hγ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨γ, hγ0, fun t ht ↦ ?_⟩
  exact (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

omit [CompleteSpace E] in
theorem integralCurveOn_Ioo_eqOn_of_lipschitz
    (hv : LipschitzWith K v) {γ γ' : ℝ → E} {a b t0 : ℝ}
    (ht0 : t0 ∈ Ioo a b)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (v (γ t)) t)
    (hγ' : ∀ t ∈ Ioo a b, HasDerivAt γ' (v (γ' t)) t)
    (heq : γ t0 = γ' t0) : EqOn γ γ' (Ioo a b) := by
  apply ODE_solution_unique_of_mem_Ioo
    (s := fun _ ↦ Set.univ) (K := K) (t₀ := t0)
      (fun _ _ ↦ hv.lipschitzOnWith) ht0
  · exact fun t ht ↦ ⟨hγ t ht, Set.mem_univ _⟩
  · exact fun t ht ↦ ⟨hγ' t ht, Set.mem_univ _⟩
  · exact heq

omit [CompleteSpace E] in
theorem eqOn_of_integralCurveOn_symmetric
    (hv : LipschitzWith K v) {x : E} (γ : ℝ → ℝ → E)
    (hγx : ∀ a, γ a 0 = x)
    (hγ : ∀ a > 0, ∀ t ∈ Ioo (-a) a, HasDerivAt (γ a) (v (γ a t)) t)
    {a a' : ℝ} (hpos : 0 < a') (hle : a' ≤ a) :
    EqOn (γ a') (γ a) (Ioo (-a') a') := by
  apply integralCurveOn_Ioo_eqOn_of_lipschitz hv (t0 := 0)
  · exact ⟨neg_lt_zero.mpr hpos, hpos⟩
  · exact hγ a' hpos
  · exact fun t ht ↦ hγ a (hpos.trans_le hle) t
      (Ioo_subset_Ioo (neg_le_neg hle) hle ht)
  · rw [hγx a', hγx a]

omit [CompleteSpace E] in
theorem eqOn_abs_add_one_of_integralCurveOn_symmetric
    (hv : LipschitzWith K v) {x : E} (γ : ℝ → ℝ → E)
    (hγx : ∀ a, γ a 0 = x)
    (hγ : ∀ a > 0, ∀ t ∈ Ioo (-a) a, HasDerivAt (γ a) (v (γ a t)) t)
    {a : ℝ} : EqOn (fun t ↦ γ (|t| + 1) t) (γ a) (Ioo (-a) a) := by
  intro t ht
  by_cases hlt : |t| + 1 < a
  · exact eqOn_of_integralCurveOn_symmetric hv γ hγx hγ
      (by positivity) hlt.le (abs_lt.mp <| lt_add_one _)
  · exact eqOn_of_integralCurveOn_symmetric hv γ hγx hγ
      (neg_lt_self_iff.mp <| lt_trans ht.1 ht.2) (le_of_not_gt hlt) ht |>.symm

/-- A globally Lipschitz bounded autonomous vector field has a global integral curve through every
point. -/
theorem exists_global_integralCurve_of_lipschitz_bounded
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (v (γ t)) t := by
  choose γ hγx hγ using fun a : ℝ ↦
    exists_integralCurveOn_symmetric_of_lipschitz_bounded hv hbound x
      (show 0 < |a| + 1 by positivity)
  have hγ' : ∀ a > 0, ∀ t ∈ Ioo (-a) a,
      HasDerivAt (γ a) (v (γ a t)) t := by
    intro a ha t ht
    apply hγ a t
    rw [mem_Ioo] at ht ⊢
    have haa : |a| = a := abs_of_pos ha
    constructor <;> rw [haa] <;> linarith
  let γglobal : ℝ → E := fun t ↦ γ (|t| + 1) t
  refine ⟨γglobal, ?_, fun t ↦ ?_⟩
  · simp [γglobal, hγx]
  · have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
      rw [mem_Ioo]
      exact ⟨lt_of_lt_of_le (by linarith) (neg_abs_le t),
        lt_of_le_of_lt (le_abs_self t) (lt_add_one _)⟩
    have heq : γglobal =ᶠ[nhds t] γ (|t| + 1) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact eqOn_abs_add_one_of_integralCurveOn_symmetric hv
        γ hγx hγ' hs
    apply HasDerivAt.congr_of_eventuallyEq
      (hγ' (|t| + 1) (by positivity) t ht) heq

end CompleteVectorField

section Hamiltonian

open LeanEval.Geometry.LiouvilleArnold

@[simp]
theorem idxP_inj_iff {n : ℕ} {i j : Fin n} : idxP i = idxP j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    simpa [idxP] using congrArg Fin.val h
  · exact congrArg idxP

@[simp]
theorem idxQ_inj_iff {n : ℕ} {i j : Fin n} : idxQ i = idxQ j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have := congrArg Fin.val h
    simp only [idxQ] at this
    omega
  · exact congrArg idxQ

@[simp]
theorem idxP_ne_idxQ {n : ℕ} (i j : Fin n) : idxP i ≠ idxQ j := by
  intro h
  have := congrArg Fin.val h
  simp only [idxP, idxQ] at this
  omega

@[simp]
theorem idxQ_ne_idxP {n : ℕ} (i j : Fin n) : idxQ i ≠ idxP j :=
  ne_comm.mp (idxP_ne_idxQ j i)

theorem exists_eq_idxP_or_eq_idxQ {n : ℕ} (k : Fin (2 * n)) :
    (∃ i : Fin n, k = idxP i) ∨ (∃ i : Fin n, k = idxQ i) := by
  by_cases hk : k.val < n
  · left
    exact ⟨⟨k.val, hk⟩, Fin.ext rfl⟩
  · right
    have hk' : k.val - n < n := by omega
    refine ⟨⟨k.val - n, hk'⟩, Fin.ext ?_⟩
    simp only [idxQ]
    omega

/-- The Hamiltonian vector field associated to a real-valued function in the standard
symplectic coordinates. -/
noncomputable def hamiltonianVector {n : ℕ} (f : E n → ℝ) (x : E n) : E n :=
  ∑ i : Fin n,
    (fderiv ℝ f x (EuclideanSpace.single (idxP i) (1 : ℝ)) •
        EuclideanSpace.single (idxQ i) (1 : ℝ) -
      fderiv ℝ f x (EuclideanSpace.single (idxQ i) (1 : ℝ)) •
        EuclideanSpace.single (idxP i) (1 : ℝ))

@[simp]
theorem hamiltonianVector_apply_idxP {n : ℕ} (f : E n → ℝ) (x : E n) (i : Fin n) :
    hamiltonianVector f x (idxP i) =
      -fderiv ℝ f x (EuclideanSpace.single (idxQ i) (1 : ℝ)) := by
  classical
  simp [hamiltonianVector, Finset.sum_apply, Pi.single_apply, idxP_inj_iff]

@[simp]
theorem hamiltonianVector_apply_idxQ {n : ℕ} (f : E n → ℝ) (x : E n) (i : Fin n) :
    hamiltonianVector f x (idxQ i) =
      fderiv ℝ f x (EuclideanSpace.single (idxP i) (1 : ℝ)) := by
  classical
  simp [hamiltonianVector, Finset.sum_apply, Pi.single_apply, idxQ_inj_iff]

/-- The constant linear map taking a covector to its standard Hamiltonian vector. -/
noncomputable def hamiltonianCLM (n : ℕ) :
    (E n →L[ℝ] ℝ) →L[ℝ] E n :=
  ∑ i : Fin n,
    (ContinuousLinearMap.smulRight
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single (idxP i) (1 : ℝ)))
        (EuclideanSpace.single (idxQ i) (1 : ℝ)) -
      ContinuousLinearMap.smulRight
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single (idxQ i) (1 : ℝ)))
        (EuclideanSpace.single (idxP i) (1 : ℝ)))

@[simp]
theorem hamiltonianCLM_apply {n : ℕ} (l : E n →L[ℝ] ℝ) :
    hamiltonianCLM n l =
      ∑ i : Fin n,
        (l (EuclideanSpace.single (idxP i) (1 : ℝ)) •
            EuclideanSpace.single (idxQ i) (1 : ℝ) -
          l (EuclideanSpace.single (idxQ i) (1 : ℝ)) •
            EuclideanSpace.single (idxP i) (1 : ℝ)) := by
  simp [hamiltonianCLM]

theorem hamiltonianVector_eq_hamiltonianCLM {n : ℕ} (f : E n → ℝ) (x : E n) :
    hamiltonianVector f x = hamiltonianCLM n (fderiv ℝ f x) := by
  simp [hamiltonianVector]

/-- The standard symplectic duality is skew-symmetric. -/
theorem hamiltonianCLM_skew {n : ℕ} (l m : E n →L[ℝ] ℝ) :
    m (hamiltonianCLM n l) = -l (hamiltonianCLM n m) := by
  simp only [hamiltonianCLM_apply, map_sum, map_sub, map_smul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fderiv_hamiltonianVector_field {n : ℕ} {f : E n → ℝ} {x : E n}
    (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (hamiltonianVector f) x =
      (hamiltonianCLM n).comp (fderiv ℝ (fderiv ℝ f) x) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [show hamiltonianVector f = hamiltonianCLM n ∘ fderiv ℝ f from
    funext fun y ↦ hamiltonianVector_eq_hamiltonianCLM f y]
  exact ((hamiltonianCLM n).hasFDerivAt.comp x hdf.hasFDerivAt).fderiv

theorem fderiv_hamiltonianVector {n : ℕ} (f g : E n → ℝ) (x : E n) :
    fderiv ℝ g x (hamiltonianVector f x) = poissonBracket f g x := by
  simp only [hamiltonianVector, map_sum, map_sub,
    ContinuousLinearMap.map_smul_of_tower, poissonBracket]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem poissonBracket_eq_fderiv_hamiltonianVector {n : ℕ}
    (f g : E n → ℝ) (x : E n) :
    poissonBracket f g x = fderiv ℝ g x (hamiltonianVector f x) := by
  exact (fderiv_hamiltonianVector f g x).symm

/-- The Lie bracket of standard Hamiltonian vector fields is the Hamiltonian vector field of
the Poisson bracket. -/
theorem lieBracket_hamiltonianVector {n : ℕ} {f g : E n → ℝ} {x : E n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    VectorField.lieBracket ℝ (hamiltonianVector f) (hamiltonianVector g) x =
      hamiltonianVector (poissonBracket f g) x := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hXf : DifferentiableAt ℝ (hamiltonianVector f) x := by
    rw [show hamiltonianVector f = hamiltonianCLM n ∘ fderiv ℝ f from
      funext fun y ↦ hamiltonianVector_eq_hamiltonianCLM f y]
    fun_prop
  rw [VectorField.lieBracket, fderiv_hamiltonianVector_field hg,
    fderiv_hamiltonianVector_field hf,
    hamiltonianVector_eq_hamiltonianCLM (poissonBracket f g) x]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← map_sub]
  congr 1
  rw [show poissonBracket f g =
      fun y ↦ fderiv ℝ g y (hamiltonianVector f y) from
    funext fun y ↦ poissonBracket_eq_fderiv_hamiltonianVector f g y]
  rw [fderiv_clm_apply hdg hXf]
  apply ContinuousLinearMap.ext
  intro v
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    fderiv_hamiltonianVector_field hf]
  rw [hamiltonianCLM_skew,
    ← hamiltonianVector_eq_hamiltonianCLM g x,
    (hf.isSymmSndFDerivAt (by norm_num) v (hamiltonianVector g x)),
    (hg.isSymmSndFDerivAt (by norm_num) v (hamiltonianVector f x))]
  abel

theorem lieBracket_hamiltonianVector_eq_zero_on {n : ℕ} {f g : E n → ℝ}
    {U : Set (E n)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g U)
    (hfg : ∀ y ∈ U, poissonBracket f g y = 0) {x : E n} (hx : x ∈ U) :
    VectorField.lieBracket ℝ (hamiltonianVector f) (hamiltonianVector g) x = 0 := by
  rw [lieBracket_hamiltonianVector
    ((hf x hx).contDiffAt (hU.mem_nhds hx) |>.of_le
      (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
    ((hg x hx).contDiffAt (hU.mem_nhds hx) |>.of_le
      (ENat.LEInfty.out (m := (2 : ℕ∞ω))))]
  have heq : poissonBracket f g =ᶠ[nhds x] 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hfg y hy
  have hd : fderiv ℝ (poissonBracket f g) x = 0 := by
    rw [heq.fderiv_eq]
    simp
  simp [hamiltonianVector, hd]

theorem linearCombination_fderiv_eq_zero_of_hamiltonian_eq_zero
    {n : ℕ} (F : Fin n → E n → ℝ) (x : E n) (a : Fin n → ℝ)
    (h : ∑ i, a i • hamiltonianVector (F i) x = 0) :
    ∑ i, a i • fderiv ℝ (F i) x = 0 := by
  have hp (k : Fin n) :
      ∑ i, a i * fderiv ℝ (F i) x (EuclideanSpace.single (idxP k) (1 : ℝ)) = 0 := by
    have hk := congrArg (fun v : E n ↦ v (idxQ k)) h
    simpa [Finset.sum_apply] using hk
  have hq (k : Fin n) :
      ∑ i, a i * fderiv ℝ (F i) x (EuclideanSpace.single (idxQ k) (1 : ℝ)) = 0 := by
    have hk := congrArg (fun v : E n ↦ v (idxP k)) h
    simpa [Finset.sum_apply, ← Finset.sum_neg_distrib] using congrArg Neg.neg hk
  apply ContinuousLinearMap.ext
  intro v
  simp only [zero_apply]
  have hv : ∑ k : Fin (2 * n), v k • EuclideanSpace.single k (1 : ℝ) = v := by
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).sum_repr_symm
        ((EuclideanSpace.basisFun (Fin (2 * n)) ℝ).repr v)
  rw [← hv]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro k _
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := exists_eq_idxP_or_eq_idxQ k
  · simp [hp i]
  · simp [hq i]

theorem linearIndependent_hamiltonianVector
    {n : ℕ} (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x) :
    LinearIndependent ℝ fun i ↦ hamiltonianVector (F i) x := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  exact (Fintype.linearIndependent_iff.mp hF a
    (linearCombination_fderiv_eq_zero_of_hamiltonian_eq_zero F x a ha)) i

theorem contDiffOn_hamiltonianVector
    {n : ℕ} {f : E n → ℝ} {U : Set (E n)}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (hamiltonianVector f) U := by
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU (by simp)
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sub
  · exact (hdf.clm_apply contDiffOn_const).smul contDiffOn_const
  · exact (hdf.clm_apply contDiffOn_const).smul contDiffOn_const

end Hamiltonian

end Submission.Helpers
