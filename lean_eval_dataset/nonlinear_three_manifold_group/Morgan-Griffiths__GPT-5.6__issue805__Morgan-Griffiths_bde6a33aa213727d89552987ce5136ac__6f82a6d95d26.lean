import ChallengeDeps
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Module.Submodule.Union

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/CoverBasics.lean
section

/-!
A quotient of a manifold by a covering action is locally a manifold.  `ChartedSpace` does not
ask for compatibility of charts; the following small handoff from a surjective local
homeomorphism is often convenient.  It is just the ordinary construction with a chosen sheet
over every point of the base.  We keep the choices explicit to avoid requiring a topology on the
group of deck transformations.
-/
open Set
noncomputable section
namespace NonlinearThreeManifoldSupport

/-- Transfer just the topological charts along a surjective local homeomorphism.  Notice the
asymmetry: the local inverse has source in `X`, which is what is wanted for a chart on `X`.
`OpenPartialHomeomorph.trans` already makes the requisite domain intersection with the old
chart. -/
@[implicit_reducible] noncomputable def ChartedSpace.ofSurjectiveLocalHomeomorph
    (H E X : Type*) [TopologicalSpace H] [TopologicalSpace E] [TopologicalSpace X]
    [ChartedSpace H E]
    (p : E → X) (hp : IsLocalHomeomorph p) (hs : Function.Surjective p) :
    ChartedSpace H X := by
  classical
  let t (x : X) : E := Function.surjInv hs x
  have ht (x : X) : p (t x) = x := Function.rightInverse_surjInv hs x
  let c (x : X) : OpenPartialHomeomorph X H :=
    (hp.localInverseAt (t x)).trans (chartAt H (t x))
  have hc (x : X) : x ∈ (c x).source := by
    -- first enter the chosen sheet, then the preferred chart on that sheet
    rw [show c x = (hp.localInverseAt (t x)).trans (chartAt H (t x)) from rfl,
      OpenPartialHomeomorph.trans_source]
    constructor
    · -- the chosen point of the sheet
      have hx := hp.apply_self_mem_localInverseAt_source (x := t x)
      simpa [ht x] using hx
    · -- the inverse sends it back to the chosen lift
      have hx : hp.localInverseAt (t x) (p (t x)) = t x :=
        hp.localInverseAt_apply_self
      -- replacing the value of `p (t x)` avoids any cast at the source
      change hp.localInverseAt (t x) x ∈ (chartAt H (t x)).source
      have hx' : hp.localInverseAt (t x) x = t x :=
        (congrArg (fun y : X => hp.localInverseAt (t x) y) (ht x).symm).trans hx
      rw [hx']
      exact mem_chart_source H (t x)
  exact
  { atlas := Set.range c
    chartAt := c
    mem_chart_source := hc
    chart_mem_atlas := fun x ↦ ⟨x, rfl⟩ }

end NonlinearThreeManifoldSupport

open scoped Topology
open Topology unitInterval
open CategoryTheory
noncomputable section
namespace NonlinearThreeManifoldSupport

/-- For a simply connected covering space, evaluating the lifted endpoint at one chosen
sheet is a *bijection of sets* between the fundamental group of the base and the fibre.
This set version has no left/right convention for deck multiplication and is sufficient
for keeping central elements of a finite deck group apart. -/
lemma IsCoveringMap.monodromy_bijective_of_simplyConnected
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : IsCoveringMap p) [SimplyConnectedSpace E]
    (e : E) :
    Function.Bijective
      (fun a : FundamentalGroup X (p e) =>
        cov.monodromy a (⟨e, rfl⟩ : p ⁻¹' ({p e} : Set X))) := by
  classical
  constructor
  · intro a b h
    change Path.Homotopic.Quotient (p e) (p e) at a b
    induction a using Quotient.inductionOn with | _ pa => ?_
    induction b using Quotient.inductionOn with | _ pb => ?_
    let la : C(I, E) := cov.liftPath pa e pa.source
    let lb : C(I, E) := cov.liftPath pb e pb.source
    have la0 : la 0 = e := cov.liftPath_zero _ _ _
    have lb0 : lb 0 = e := cov.liftPath_zero _ _ _
    have ends : la 1 = lb 1 := congrArg Subtype.val h
    let A : Path e (la 1) := { toContinuousMap := la, source' := la0, target' := rfl }
    let B : Path e (la 1) := { toContinuousMap := lb, source' := lb0,
                               target' := ends.symm }
    have hh : Path.Homotopic A B := SimplyConnectedSpace.paths_homotopic _ _
    have hm : Path.Homotopic (A.map cov.continuous)
        (B.map cov.continuous) := by
      exact Path.Homotopic.map hh ⟨p, cov.continuous⟩
    have ee : p e = p e := rfl
    have et : p e = p (la 1) := by
      -- evaluate the projection of the first lift at 1
      symm
      exact (congr_fun (cov.liftPath_lifts pa e pa.source) 1).trans pa.target
    have hm' : Path.Homotopic ((A.map cov.continuous).cast ee et)
        ((B.map cov.continuous).cast ee et) := hm.pathCast _ _
    have ea : (A.map cov.continuous).cast ee et = pa := by
      apply Path.ext
      -- casts have the same underlying function
      exact cov.liftPath_lifts pa e pa.source
    have eb : (B.map cov.continuous).cast ee et = pb := by
      apply Path.ext
      exact cov.liftPath_lifts pb e pb.source
    exact Quotient.sound (ea ▸ eb ▸ hm')
  · intro e'
    have ep : p e'.1 = p e := e'.2
    let L : Path e (e'.1) := PathConnectedSpace.somePath _ _
    let q : Path.Homotopic.Quotient e (e'.1) := ⟦L⟧
    let γ : Path.Homotopic.Quotient (p e) (p e) :=
      (q.map ⟨p, cov.continuous⟩).cast rfl ep.symm
    refine ⟨γ, ?_⟩
    apply Subtype.ext
    change _ = e'.1
    dsimp [γ, q]
    -- expose the chosen representative of the cast path
    change cov.liftPath
      ((L.map cov.continuous).cast rfl ep.symm) e ((L.map cov.continuous).cast rfl ep.symm).source 1 = e'.1
    have funeq : p ∘ (L : I → E) =
          (((L.map cov.continuous).cast rfl ep.symm) : I → X) := by
      exact (Path.map_coe L cov.continuous).symm
    have liftEq : (L : C(I,E)) =
        cov.liftPath ((L.map cov.continuous).cast rfl ep.symm) e ((L.map cov.continuous).cast rfl ep.symm).source :=
      
      (cov.eq_liftPath_iff' _).2 ⟨funeq, L.source⟩
    exact (congrArg (fun (T : C(I,E)) => T 1) liftEq).symm.trans L.target

end NonlinearThreeManifoldSupport

noncomputable section
namespace NonlinearThreeManifoldSupport
variable {H E : Type*}

/-- The quotient by a *free finite* continuous action has charts in the same model.  Combining
this with the elementary compact/second-countable quotient instances is a lean way to construct
spherical space forms as `Closed3Manifold`s; no smooth groupoid compatibility is involved. -/
@[implicit_reducible] noncomputable def ChartedSpace.orbitFinite
    (H E G : Type*) [TopologicalSpace H] [TopologicalSpace E]
    [ChartedSpace H E]
    [Group G] [MulAction G E] [ContinuousConstSMul G E] [Finite G]
    [IsCancelSMul G E]
    [LocallyCompactSpace E] [T2Space E] :
    ChartedSpace H (Quotient (MulAction.orbitRel G E)) := by
  let f : E → Quotient (MulAction.orbitRel G E) :=
    Quotient.mk (MulAction.orbitRel G E)
  have hf : IsQuotientCoveringMap f G :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  exact ChartedSpace.ofSurjectiveLocalHomeomorph H E _ f
    hf.isCoveringMap.isLocalHomeomorph hf.surjective

-- These are separately useful when packaging the structure; they are stated as examples
-- with the same assumptions to record exactly which instances on a future action are needed.
example (G E : Type*) [Group G] [MulAction G E]
    [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E]
    [ContinuousConstSMul G E] [Finite G] :
    T2Space (Quotient (MulAction.orbitRel G E)) := inferInstance
example (G E : Type*) [Group G] [MulAction G E]
    [TopologicalSpace E] [ContinuousConstSMul G E] [Finite G]
    [SecondCountableTopology E] :
    SecondCountableTopology (Quotient (MulAction.orbitRel G E)) :=
  ContinuousConstSMul.secondCountableTopology

end NonlinearThreeManifoldSupport

end
end
end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/CoverBasics.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/ExplicitQ.lean
section
open scoped Quaternion RealInnerProductSpace
noncomputable section
namespace NonlinearThreeManifoldSupport.ExplicitQ8

@[simp] lemma fin3zero_z : (0 : Fin (3+1)) = (0 : ZMod 4) := by decide
@[simp] lemma fin3one_z : (1 : Fin (3+1)) = (1 : ZMod 4) := by decide
@[simp] lemma fin3two_z : (2 : Fin (3+1)) = (2 : ZMod 4) := by decide
@[simp] lemma fin3three_z : (3 : Fin (3+1)) = (3 : ZMod 4) := by decide
abbrev H := Quaternion ℝ
noncomputable def qi : H := {re := 0, imI := 1, imJ := 0, imK := 0 }
noncomputable def qj : H := {re := 0, imI := 0, imJ := 1, imK := 0 }
noncomputable def qk : H := {re := 0, imI := 0, imJ := 0, imK := 1 }
noncomputable def qa (t : ZMod 4) : H :=
 if t = 0 then 1 else if t = 1 then qi else if t = 2 then (-1) else -qi
noncomputable def qx (t : ZMod 4) : H :=
 if t = 0 then qj else if t = 1 then -qk else if t = 2 then -qj else qk
set_option maxRecDepth 5000 in
lemma qa_add : ∀ r s : ZMod 4, qa (r+s) = qa r * qa s := by
  intro r s
  fin_cases r <;> fin_cases s <;>
    ext <;> simp +decide [qa, qi, Quaternion.re_mul, Quaternion.imI_mul,
       Quaternion.imJ_mul, Quaternion.imK_mul] <;> norm_num
set_option maxRecDepth 5000 in
lemma qa_xa : ∀ r s : ZMod 4, qx (s-r) = qa r * qx s := by
  intro r s
  fin_cases r <;> fin_cases s <;>
    ext <;> simp +decide [qa,qx, qi,qj,qk, Quaternion.re_mul, Quaternion.imI_mul,
       Quaternion.imJ_mul, Quaternion.imK_mul] <;> norm_num
set_option maxRecDepth 5000 in
lemma qx_a : ∀ r s : ZMod 4, qx (r+s) = qx r * qa s := by
  intro r s
  fin_cases r <;> fin_cases s <;>
    ext <;> simp +decide [qa,qx, qi,qj,qk, Quaternion.re_mul, Quaternion.imI_mul,
       Quaternion.imJ_mul, Quaternion.imK_mul] <;> norm_num
set_option maxRecDepth 5000 in
lemma qx_xa : ∀ r s : ZMod 4, qa ((2 : ZMod 4) + s - r) = qx r * qx s := by
  intro r s
  fin_cases r <;> fin_cases s <;>
    ext <;> simp +decide [qa,qx, qi,qj,qk, Quaternion.re_mul, Quaternion.imI_mul,
       Quaternion.imJ_mul, Quaternion.imK_mul] <;> norm_num
noncomputable def q8rho_fun : QuaternionGroup 2 → Quaternion ℝ
| .a t => qa t
| .xa t => qx t
set_option maxRecDepth 5000 in
noncomputable def q8rho : QuaternionGroup 2 →* Quaternion ℝ where
 toFun := q8rho_fun
 map_one' := by
   change qa 0 = 1
   simp [qa]
 map_mul' := by
   intro a b
   cases a with
   | a r => cases b with
     | a s => exact qa_add r s
     | xa s => exact qa_xa r s
   | xa r => cases b with
     | a s => exact qx_a r s
     | xa s => exact qx_xa r s
set_option maxRecDepth 5000 in
set_option maxRecDepth 8000 in
lemma q8rho_injective : Function.Injective q8rho := by
  intro x y e
  have coord :
    (q8rho x).re = (q8rho y).re ∧
    (q8rho x).imI = (q8rho y).imI ∧
    (q8rho x).imJ = (q8rho y).imJ ∧
    (q8rho x).imK = (q8rho y).imK :=
      ⟨congrArg QuaternionAlgebra.re e,
       congrArg QuaternionAlgebra.imI e,
       congrArg QuaternionAlgebra.imJ e,
       congrArg QuaternionAlgebra.imK e⟩
  cases x with
  | a r =>
    cases y with
    | a s =>
      fin_cases r <;> fin_cases s
      all_goals try rfl
      all_goals exfalso; dsimp [q8rho, q8rho_fun] at coord; simp +decide [qa,qx,qi,qj,qk] at coord <;> norm_num at coord
    | xa s =>
      fin_cases r <;> fin_cases s <;>
        exfalso <;> dsimp [q8rho, q8rho_fun] at coord <;>
        simp +decide [qa,qx, qi,qj,qk] at coord <;> norm_num at coord
  | xa r =>
    cases y with
    | a s =>
      fin_cases r <;> fin_cases s <;>
        exfalso <;> dsimp [q8rho, q8rho_fun] at coord <;>
        simp +decide [qa,qx, qi,qj,qk] at coord <;> norm_num at coord
    | xa s =>
      fin_cases r <;> fin_cases s
      all_goals try rfl
      all_goals exfalso; dsimp [q8rho, q8rho_fun] at coord; simp +decide [qa,qx,qi,qj,qk] at coord <;> norm_num at coord
--norm
lemma hn1 (u : H) (hu : Quaternion.normSq u = 1) : ‖u‖ = 1 := by
  have h := Quaternion.normSq_eq_norm_mul_self u
  rw [hu] at h
  nlinarith [norm_nonneg u]
set_option maxRecDepth 5000 in
lemma q8rho_norm : ∀ g : QuaternionGroup 2, ‖q8rho g‖ = 1 := by
  intro g
  cases g with
  | a r =>
    apply hn1
    fin_cases r <;> dsimp [q8rho, q8rho_fun] <;> simp +decide [ qa, qi, Quaternion.normSq_def'] <;> norm_num
  | xa r =>
    apply hn1
    fin_cases r <;> dsimp [q8rho, q8rho_fun] <;> simp +decide [ qa,qx, qi,qj,qk, Quaternion.normSq_def'] <;> norm_num
end NonlinearThreeManifoldSupport.ExplicitQ8

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/ExplicitQ.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/GlueCharted.lean
section

noncomputable section
open scoped Topology Manifold
open Set TopologicalSpace Topology CategoryTheory
namespace NonlinearThreeManifoldSupport

/-! A small and quite general convenience fact needed for a connected sum:
local charts paste along open embeddings.  `ChartedSpace` carries no transition
conditions, so this is purely an assertion about local homeomorphisms.  We state
it first for an arbitrary open cover by parametrised spaces and then for
`TopCat.GlueData`. -/

universe u v

section Cover
variable {H : Type u} [TopologicalSpace H]
variable {X : Type u} [TopologicalSpace X]
variable {ι : Type u}
-- The spaces in the cover all live in the same universe; this is exactly the
-- situation of `TopCat.GlueData`.
variable (A : ι → Type u) [topA : ∀ i, TopologicalSpace (A i)]
variable [chA : ∀ i, ChartedSpace H (A i)]
variable (f : ∀ i, A i → X)
variable (openf : ∀ i, IsOpenEmbedding (f i))
variable (cover : ∀ x : X, ∃ (i : ι) (a : A i), f i a = x)

private noncomputable def __GlueCharted_ix (x : X) : ι := Classical.choose (cover x)
private noncomputable def __GlueCharted_ax (x : X) : A (__GlueCharted_ix A f cover x) :=
  Classical.choose (Classical.choose_spec (cover x))
private lemma __GlueCharted_fax (x : X) :
    f (__GlueCharted_ix A f cover x) (__GlueCharted_ax A f cover x) = x :=
  Classical.choose_spec (Classical.choose_spec (cover x))

/-- The local chart furnished by the member of the open cover containing `x`.
Its first factor is the inverse of the chosen open embedding; this is why the
embedding has to be *open*, not just an embedding of a closed patch. -/
private noncomputable def __GlueCharted_localChart (x : X) : OpenPartialHomeomorph X H := by
  classical
  let i : ι := __GlueCharted_ix A f cover x
  let a : A i := __GlueCharted_ax A f cover x
  letI : Nonempty (A i) := ⟨a⟩
  -- restrict the inverse of the open embedding to the usual chart
  exact ((openf i).toOpenPartialHomeomorph (f i)).symm.trans (chartAt H a)

private lemma __GlueCharted_mem_localChart (x : X) :
    x ∈ (__GlueCharted_localChart (A:=A) f openf cover (H:=H) x).source := by
  classical
  let i : ι := __GlueCharted_ix A f cover x
  let a : A i := __GlueCharted_ax A f cover x
  letI : Nonempty (A i) := ⟨a⟩
  have hx : f i a = x := __GlueCharted_fax A f cover x
  change x ∈
    (((openf i).toOpenPartialHomeomorph (f i)).symm.trans
      (chartAt H a)).source
  rw [OpenPartialHomeomorph.trans_source]
  -- the inverse chart for an open embedding is defined on its range
  have hr : x ∈
      ((openf i).toOpenPartialHomeomorph (f i)).symm.source := by
    change x ∈ ((openf i).toOpenPartialHomeomorph (f i)).target
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨a, hx⟩
  refine ⟨hr, ?_⟩
  -- and it really sends this point to `a`
  have inv :
      ((openf i).toOpenPartialHomeomorph (f i)).symm x = a := by
    -- use the left inverse on the full source
    have ha : a ∈ ((openf i).toOpenPartialHomeomorph (f i)).source := by
      simp
    -- the coercions to local equiv are easier to rewrite before `hx`
    have h :=
      ((openf i).toOpenPartialHomeomorph (f i)).left_inv ha
    -- `left_inv` talks about the inverse applied to the image
    simpa [hx] using h
  -- the second chart is the preferred one at `a`
  simpa [inv] using (mem_chart_source H a)

/-- A space covered by open embedded charted spaces is charted.  This lemma is
merely a convenient constructor: no compatibility of the charts is asserted
(or required by mathlib's `ChartedSpace`). -/
@[implicit_reducible] noncomputable def chartedSpaceOfOpenCover :
    ChartedSpace H X where
  atlas := Set.range (__GlueCharted_localChart (A:=A) f openf cover (H:=H))
  chartAt := __GlueCharted_localChart (A:=A) f openf cover (H:=H)
  mem_chart_source := __GlueCharted_mem_localChart (A:=A) f openf cover (H:=H)
  chart_mem_atlas x := ⟨x, rfl⟩

end Cover

section Glue
open TopCat
variable {H : Type u} [TopologicalSpace H]
variable (D : TopCat.GlueData.{u})
variable [chD : ∀ i : D.J, ChartedSpace H (D.U i)]

/-- The glued space of a family of open subsets of charted spaces is again
charted.  This is the local half of most cut-and-paste constructions of
manifolds.  It is separated from separation/compactness on purpose: gluing
*open* patches is always locally a manifold, while Hausdorffness is a genuine
global condition. -/
@[implicit_reducible] noncomputable def gluedChartedSpace :
    ChartedSpace H D.toGlueData.glued := by
  classical
  let F : ∀ i : D.J, ((D.U i : Type u)) → D.toGlueData.glued :=
    fun i => D.toGlueData.ι i
  have ho : ∀ i : D.J, IsOpenEmbedding (F i) := by
    intro i
    exact D.ι_isOpenEmbedding i
  have hc : ∀ x : D.toGlueData.glued,
      ∃ (i : D.J) (a : (D.U i : Type u)), F i a = x := by
    intro x
    simpa [F] using (D.ι_jointly_surjective x)
  exact chartedSpaceOfOpenCover (H:=H) (A:= fun i : D.J => (D.U i : Type u))
    F ho hc

end Glue
end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open Set Topology TopologicalSpace CategoryTheory
open TopCat
universe u

/-- If all of the open patches are connected and every pair of patches overlaps, the
open gluing is connected.  The pairwise hypothesis is more than is needed (a
connected nerve is enough), but it is exactly the two-patch situation in a
neck.  Keeping this global bookkeeping out of the local charts is handy. -/
lemma glued_isConnected_univ_of_pairwise
    (D : TopCat.GlueData.{u}) [Nonempty D.J]
    [conn : ∀ i : D.J, ConnectedSpace (D.U i)]
    (meet : ∀ i j : D.J, Nonempty (D.V (i,j))) :
    IsConnected (Set.univ : Set D.toGlueData.glued) := by
  classical
  let S : D.J → Set D.toGlueData.glued := fun i => Set.range (D.toGlueData.ι i)
  have hSi : ∀ i, IsConnected (S i) := by
    intro i
    exact isConnected_range (D.toGlueData.ι i).hom.continuous
  have hinter : ∀ i j, (S i ∩ S j).Nonempty := by
    intro i j
    obtain ⟨v⟩ := meet i j
    -- an overlap point belongs to the two images by the glue condition
    refine ⟨D.toGlueData.ι i (D.f i j v), ⟨?_, ?_⟩⟩
    · exact Set.mem_range_self _
    · refine ⟨D.f j i (D.t i j v), ?_⟩
      -- the two descriptions of an overlap are identified in the colimit
      exact (D.glue_condition_apply i j v)
  have hc : IsConnected (⋃ i, S i) := by
    -- use the standard connected-nerve lemma; pairwise intersections give a
    -- one-step path in the nerve
    refine IsConnected.iUnion_of_reflTransGen hSi ?_
    intro i j
    exact Relation.ReflTransGen.single (hinter i j)
  have hu : (⋃ i, S i) = (Set.univ : Set D.toGlueData.glued) := by
    ext x
    constructor
    · intro; trivial
    · intro _
      obtain ⟨i,a,rfl⟩ := D.ι_jointly_surjective x
      exact Set.mem_iUnion_of_mem i (Set.mem_range_self a)
  rw [← hu]
  exact hc

/-- Instance form of `glued_isConnected_univ_of_pairwise`. -/
noncomputable def gluedConnectedSpace
    (D : TopCat.GlueData.{u}) [Nonempty D.J]
    [∀ i : D.J, ConnectedSpace (D.U i)]
    (meet : ∀ i j : D.J, Nonempty (D.V (i,j))) :
    ConnectedSpace D.toGlueData.glued :=
  connectedSpace_iff_univ.mpr (glued_isConnected_univ_of_pairwise D meet)

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open Set Topology TopologicalSpace CategoryTheory
open TopCat
universe u
/-- A countable open gluing of second countable patches is second countable.
This is the global bookkeeping part of a two-patch neck; unlike Hausdorffness
it needs no condition on the seams. -/
noncomputable def gluedSecondCountable
    (D : TopCat.GlueData.{u}) [Countable D.J]
    [∀ i : D.J, SecondCountableTopology (D.U i)] :
    SecondCountableTopology D.toGlueData.glued := by
  classical
  let U : D.J → Set D.toGlueData.glued := fun i => Set.range (D.toGlueData.ι i)
  have Uo : ∀ i, IsOpen (U i) := by
    intro i
    exact (D.ι_isOpenEmbedding i).isOpen_range
  haveI patch : ∀ i : D.J, SecondCountableTopology (U i) := by
    intro i
    have e := (D.ι_isOpenEmbedding i).isEmbedding.toHomeomorph
    -- `e : U_i ≃ₜ range`; use it in the reverse direction
    exact e.symm.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover Uo ?_
  ext x
  constructor
  · intro hx; trivial
  · intro _
    obtain ⟨i,a,rfl⟩ := D.ι_jointly_surjective x
    exact Set.mem_iUnion_of_mem i (Set.mem_range_self a)
end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits
open TopCat
universe u
section descend
variable (D : TopCat.GlueData.{u})
variable {Y : Type u} [TopologicalSpace Y]
/-- A convenient noncategorical eliminator for the open gluing.  Pinch maps are
usually given by their continuous formulas on the two punctured blocks; only
this compatibility on the overlap is required. -/
noncomputable def continuousMapFromGlue
    (g : ∀ i : D.J, C((D.U i : Type u),Y))
    (h : ∀ (i j : D.J) (v : D.V (i,j)),
       g i (D.f i j v) = g j (D.f j i (D.t i j v))) :
    C(D.toGlueData.glued, Y) := by
  -- the colimit is in `TopCat`; forget its resulting morphism
  refine (Multicoequalizer.desc D.toGlueData.diagram (TopCat.of Y)
    (fun i => TopCat.ofHom (g i)) ?_).hom
  rintro ⟨i,j⟩
  ext v
  -- on an overlap the two descriptions supplied by `g` agree
  exact h i j v

@[simp]
lemma continuousMapFromGlue_ι
    (g : ∀ i : D.J, C((D.U i : Type u),Y))
    (h : ∀ (i j : D.J) (v : D.V (i,j)),
       g i (D.f i j v) = g j (D.f j i (D.t i j v)))
    (i : D.J) (x : D.U i) :
    (continuousMapFromGlue D g h) (D.toGlueData.ι i x) = g i x := by
  -- this is the defining colimit equation, not a choice of representatives
  have E := Multicoequalizer.π_desc D.toGlueData.diagram (TopCat.of Y)
    (fun k => TopCat.ofHom (g k)) (by
      rintro ⟨a,b⟩
      ext v
      exact h a b v) i
  exact CategoryTheory.congr_fun E x
end descend
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/GlueCharted.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/PinchBasics.lean
section
/-!
 A little based bookkeeping for the proposed connected-sum step.  In this file there is
 no claim that a connected sum exists.  The point is just to make precise which maps suffice.
 Carrying the point in a structure rather than silently identifying fibres avoids a common
 trap with `FundamentalGroup.map` (its target is based at `f x`).
-/
noncomputable section
open scoped Topology

namespace NonlinearThreeManifoldSupport

/-- A continuous map with a specified image of the base point. -/
structure BasedCMap (X : Type*) [TopologicalSpace X] (x : X)
    (Y : Type*) [TopologicalSpace Y] (y : Y) where
  toContinuousMap : C(X,Y)
  map_pt : toContinuousMap x = y

namespace BasedCMap
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]
variable {x : X} {y : Y} {z : Z}

/-- The honest, *based* map on end loops.  `mapOfEq` is important here: using
`map` and forgetting its endpoint makes the two pinch maps appear composable
when they need not be. -/
noncomputable def piOne (f : BasedCMap X x Y y) :
    FundamentalGroup X x →* FundamentalGroup Y y :=
  FundamentalGroup.mapOfEq f.toContinuousMap f.map_pt

/-- Compose based maps. -/
noncomputable def comp (g : BasedCMap Y y Z z)
    (f : BasedCMap X x Y y) : BasedCMap X x Z z where
  toContinuousMap := g.toContinuousMap.comp f.toContinuousMap
  map_pt := by
    simpa using (congrArg (fun t => g.toContinuousMap t) f.map_pt).trans g.map_pt

/-- Identity, with its definitional basepoint. -/
noncomputable def identity (X : Type*) [TopologicalSpace X]
    (x : X) : BasedCMap X x X x :=
  { toContinuousMap := ContinuousMap.id X, map_pt := rfl }

/-- Constant based map. -/
noncomputable def constant (X : Type*) [TopologicalSpace X] (x : X)
    (Y : Type*) [TopologicalSpace Y] (y : Y) : BasedCMap X x Y y :=
  { toContinuousMap := ContinuousMap.const _ y, map_pt := rfl }

/-- Functoriality at the based level.  This elementary fact is easy to get subtly wrong
because the casts at the endpoints of `mapOfEq` are on both sides.  Eliminating the two
basepoint equalities reduces it to maps of a representative path. -/
@[simp] lemma piOne_comp (g : BasedCMap Y y Z z) (f : BasedCMap X x Y y) :
    piOne (comp g f) = (piOne g).comp (piOne f) := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      -- after these substitutions there are no endpoint transports.  In particular the
      -- two occurrences of `Path.cast` below are both reflexive casts.
      subst y
      subst z
      ext a
      change Path.Homotopic.Quotient x x at a
      induction a using Quotient.inductionOn with | _ p => ?_
      dsimp [piOne, comp]
      change
        (FundamentalGroup.mapOfEq (g.comp f) _)
            (FundamentalGroup.fromPath (.mk p)) =
          (FundamentalGroup.mapOfEq g _)
            ((FundamentalGroup.mapOfEq f _)
              (FundamentalGroup.fromPath (.mk p)))
      simp only [FundamentalGroup.mapOfEq_apply]
      congr 2

@[simp] lemma piOne_identity {X : Type*} [TopologicalSpace X] (x : X) :
    piOne (identity X x) = MonoidHom.id (FundamentalGroup X x) := by
  ext a
  change Path.Homotopic.Quotient x x at a
  induction a using Quotient.inductionOn with | _ p => ?_
  dsimp [piOne, identity]
  change (FundamentalGroup.mapOfEq (ContinuousMap.id X) _)
    (FundamentalGroup.fromPath (.mk p)) = _
  rw [FundamentalGroup.mapOfEq_apply]
  congr 2

@[simp] lemma piOne_constant_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (a : FundamentalGroup X x) :
    piOne (constant X x Y y) a = (1 : FundamentalGroup Y y) := by
  change Path.Homotopic.Quotient x x at a
  induction a using Quotient.inductionOn with | _ p => ?_
  dsimp [piOne, constant]
  change (FundamentalGroup.mapOfEq (ContinuousMap.const _ y) _)
    (FundamentalGroup.fromPath (.mk p)) = _
  rw [FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk _ = _
  change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk (Path.refl y)
  congr 1

/-- If actual continuous pinch maps are strict sections/constant, they give exactly the
 four algebraic arrows used in `SplitPacket`.  Often a proof will only produce the weaker
 `piOne` hypotheses of `split_from_piOne`; the strict form is convenient for charts with
 an explicit collar. -/
lemma split_from_based
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y)
    (E : QuaternionGroup 2 ≃* FundamentalGroup Y y)
    (i j : BasedCMap Y y X x) (r s : BasedCMap X x Y y)
    (hi : comp r i = identity Y y)
    (hj : comp s j = identity Y y)
    (hk : comp r j = constant Y y Y y) :
    ∃ (u v : QuaternionGroup 2 →* FundamentalGroup X x)
      (R S : FundamentalGroup X x →* QuaternionGroup 2),
      R.comp u = MonoidHom.id (QuaternionGroup 2) ∧
      S.comp v = MonoidHom.id (QuaternionGroup 2) ∧
      R (v (.a 2)) = 1 := by
  let u : QuaternionGroup 2 →* FundamentalGroup X x := (piOne i).comp E.toMonoidHom
  let v : QuaternionGroup 2 →* FundamentalGroup X x := (piOne j).comp E.toMonoidHom
  let R : FundamentalGroup X x →* QuaternionGroup 2 := E.symm.toMonoidHom.comp (piOne r)
  let S : FundamentalGroup X x →* QuaternionGroup 2 := E.symm.toMonoidHom.comp (piOne s)
  refine ⟨u, v, R, S, ?_, ?_, ?_⟩
  · ext a
    change E.symm (piOne r (piOne i (E a))) = a
    rw [← MonoidHom.comp_apply]
    rw [← piOne_comp]
    rw [hi]
    rw [piOne_identity]
    simp
  · ext a
    change E.symm (piOne s (piOne j (E a))) = a
    rw [← MonoidHom.comp_apply]
    rw [← piOne_comp]
    rw [hj]
    rw [piOne_identity]
    simp
  · change E.symm (piOne r (piOne j (E (.a 2)))) = 1
    rw [← MonoidHom.comp_apply]
    rw [← piOne_comp]
    rw [hk]
    rw [piOne_constant_apply]
    simp

/-- A useful slightly weaker version.  This is normally what pinch maps give: their
composites with the inclusions are *based homotopic* to the identity/constant, rather
than equal as functions.  All the topology in a connected-sum construction is before
these three small equations. -/
lemma split_from_piOne
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y)
    (E : QuaternionGroup 2 ≃* FundamentalGroup Y y)
    (i j : BasedCMap Y y X x) (r s : BasedCMap X x Y y)
    (hi : (piOne r).comp (piOne i) = MonoidHom.id (FundamentalGroup Y y))
    (hj : (piOne s).comp (piOne j) = MonoidHom.id (FundamentalGroup Y y))
    (hk : ∀ a : FundamentalGroup Y y, piOne r (piOne j a) = 1) :
    ∃ (u v : QuaternionGroup 2 →* FundamentalGroup X x)
      (R S : FundamentalGroup X x →* QuaternionGroup 2),
      R.comp u = MonoidHom.id (QuaternionGroup 2) ∧
      S.comp v = MonoidHom.id (QuaternionGroup 2) ∧
      R (v (.a 2)) = 1 := by
  let u : QuaternionGroup 2 →* FundamentalGroup X x := (piOne i).comp E.toMonoidHom
  let v : QuaternionGroup 2 →* FundamentalGroup X x := (piOne j).comp E.toMonoidHom
  let R : FundamentalGroup X x →* QuaternionGroup 2 := E.symm.toMonoidHom.comp (piOne r)
  let S : FundamentalGroup X x →* QuaternionGroup 2 := E.symm.toMonoidHom.comp (piOne s)
  refine ⟨u, v, R, S, ?_, ?_, ?_⟩
  · ext a
    change E.symm (piOne r (piOne i (E a))) = a
    have t : piOne r (piOne i (E a)) = E a := DFunLike.congr_fun hi (E a)
    rw [t]
    simp
  · ext a
    change E.symm (piOne s (piOne j (E a))) = a
    have t : piOne s (piOne j (E a)) = E a := DFunLike.congr_fun hj (E a)
    rw [t]
    simp
  · change E.symm (piOne r (piOne j (E (.a 2)))) = 1
    rw [hk]
    simp

/-- In fact the block need not have *exactly* quaternion fundamental group.  A
quaternion retract of it is enough; this slightly weaker cut is useful if one
has only the relevant part of the spherical covering calculation. -/
lemma split_from_block_retract
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y)
    (E : QuaternionGroup 2 →* FundamentalGroup Y y)
    (D : FundamentalGroup Y y →* QuaternionGroup 2)
    (de : D.comp E = MonoidHom.id (QuaternionGroup 2))
    (i j : BasedCMap Y y X x) (r s : BasedCMap X x Y y)
    (hi : (piOne r).comp (piOne i) = MonoidHom.id (FundamentalGroup Y y))
    (hj : (piOne s).comp (piOne j) = MonoidHom.id (FundamentalGroup Y y))
    (hk : ∀ a : FundamentalGroup Y y, piOne r (piOne j a) = 1) :
    ∃ (u v : QuaternionGroup 2 →* FundamentalGroup X x)
      (R S : FundamentalGroup X x →* QuaternionGroup 2),
      R.comp u = MonoidHom.id (QuaternionGroup 2) ∧
      S.comp v = MonoidHom.id (QuaternionGroup 2) ∧
      R (v (.a 2)) = 1 := by
  let u : QuaternionGroup 2 →* FundamentalGroup X x := (piOne i).comp E
  let v : QuaternionGroup 2 →* FundamentalGroup X x := (piOne j).comp E
  let R : FundamentalGroup X x →* QuaternionGroup 2 := D.comp (piOne r)
  let S : FundamentalGroup X x →* QuaternionGroup 2 := D.comp (piOne s)
  refine ⟨u, v, R, S, ?_, ?_, ?_⟩
  · ext a
    change D (piOne r (piOne i (E a))) = a
    have t : piOne r (piOne i (E a)) = E a := DFunLike.congr_fun hi _
    rw [t]
    exact DFunLike.congr_fun de a
  · ext a
    change D (piOne s (piOne j (E a))) = a
    have t : piOne s (piOne j (E a)) = E a := DFunLike.congr_fun hj _
    rw [t]
    exact DFunLike.congr_fun de a
  · change D (piOne r (piOne j (E (.a 2)))) = 1
    rw [hk]
    simp

end BasedCMap
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/PinchBasics.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/QPacket.lean
section

/-! The elementary algebra needed once one has two quaternion subgroups. -/
open QuaternionGroup
namespace NonlinearThreeManifoldSupport

/-- A convenient set of generators for the binary quaternion group.  We spell this out with
`QuaternionGroup 2` rather than with quaternions, so that there are no choices of presentation
later on when a deck group has been identified. -/
lemma quaternion_two_packet :
    let i : QuaternionGroup 2 := .a 1
    let j : QuaternionGroup 2 := .xa 0
    let z : QuaternionGroup 2 := .a 2
    z * z = 1 ∧ i * i = z ∧ j * j = z ∧
      z * i = i * z ∧ z * j = j * z ∧
      j * i = z * (i * j) ∧ z ≠ 1 := by
  dsimp
  constructor
  · change (QuaternionGroup.a 4 : QuaternionGroup 2) = 1
    rw [← QuaternionGroup.a_zero]
    congr 1
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num <;> decide
  constructor
  · norm_num <;> decide
  · intro h
    rw [← QuaternionGroup.a_zero] at h
    cases h

/-- The group-theoretic interface for the eventual connected-sum calculation.  Separate
injections of the two summands are enough; no facts about normal forms in a free product are
used by the linear obstruction.

Stating this lemma makes endpoint/choice issues in a topological construction much less
error-prone: it suffices to construct two *based* maps from `QuaternionGroup 2` and prove that
their central involutions differ. -/
lemma quaternion_packets_of_embeddings {G : Type*} [Group G]
    (u v : QuaternionGroup 2 →* G) (hu : Function.Injective u)
    (hv : Function.Injective v)
    (huv : u (.a 2) ≠ v (.a 2)) :
    ∃ (i j z i' j' z' : G),
      z * z = 1 ∧ i * i = z ∧ j * j = z ∧
      z * i = i * z ∧ z * j = j * z ∧ j * i = z * (i * j) ∧
      z' * z' = 1 ∧ i' * i' = z' ∧ j' * j' = z' ∧
      z' * i' = i' * z' ∧ z' * j' = j' * z' ∧
      j' * i' = z' * (i' * j') ∧
      z ≠ 1 ∧ z' ≠ 1 ∧ z ≠ z' := by
  let qi : QuaternionGroup 2 := .a 1
  let qj : QuaternionGroup 2 := .xa 0
  let qz : QuaternionGroup 2 := .a 2
  have hQ : qz * qz = 1 ∧ qi * qi = qz ∧ qj * qj = qz ∧
      qz * qi = qi * qz ∧ qz * qj = qj * qz ∧
      qj * qi = qz * (qi * qj) ∧ qz ≠ 1 := quaternion_two_packet
  refine ⟨u qi, u qj, u qz, v qi, v qj, v qz, ?_⟩
  rcases hQ with ⟨hq2, hi2, hj2, hzi, hzj, hji, hn⟩
  have mapRel (w : QuaternionGroup 2 →* G) {a b c : QuaternionGroup 2}
      (h : a * b = c) : w a * w b = w c := by
    simpa only [map_mul] using congrArg w h
  have mapRel3 (w : QuaternionGroup 2 →* G) {a b c d : QuaternionGroup 2}
      (h : a * b = c * d) : w a * w b = w c * w d := by
    simpa only [map_mul] using congrArg w h
  refine ⟨?_, mapRel u hi2, mapRel u hj2,
    mapRel3 u hzi, mapRel3 u hzj, ?_,
    ?_, mapRel v hi2, mapRel v hj2,
    mapRel3 v hzi, mapRel3 v hzj, ?_, ?_, ?_, ?_⟩
  · simpa only [map_one] using (mapRel u hq2)
  · -- one extra multiplication on the right of the braided relation
    simpa only [map_mul] using (mapRel3 u hji)
  · simpa only [map_one] using (mapRel v hq2)
  · simpa only [map_mul] using (mapRel3 v hji)
  · intro e
    have : qz = (1 : QuaternionGroup 2) := hu (by simpa using e)
    exact hn this
  · intro e
    have : qz = (1 : QuaternionGroup 2) := hv (by simpa using e)
    exact hn this
  · exact huv

end NonlinearThreeManifoldSupport

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/QPacket.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/QuaternionObstruction.lean
section

/-!
A small, purely linear obstruction which can be useful as an alternative
source of examples over the real field.  The point is especially simple over
`ℝ` and in *real* dimension four.

Suppose a group contains elements `i,j,z` satisfying the quaternion relations
```
z^2=1,  i^2=j^2=z,  zi=iz, zj=jz, ji=z(ij), z≠1.
```
In any faithful real four dimensional representation the image of `z` is
`-1`.  Consequently two different such centres in a group prohibit a
faithful `GL (Fin 4) ℝ` representation.  No topology is involved in the
lemmas in this file.  For a manifold application one still has to *realise*
such subgroups in a fundamental group; for example this is what happens for
the two quaternion factors in the free product attached to suitable connected
sums of spherical manifolds.  Here the obstruction is kept separate from that
(real and difficult) topological step.

One convenient advantage of formulating the proof with `Module.End` is that
there is no classification of real representations.  On the minus
Eigenspace the two operators are the quaternion generators.  A vector and
its three quaternion translates are linearly independent (multiply a putative
linear relation by its conjugate), so in dimension four the minus eigenspace
is the whole space.
-/

noncomputable section
open Matrix

namespace NonlinearThreeManifoldSupport

/-- The elementary norm identity in a ring containing two quaternion units.
`noncomm_ring` leaves the scalar coefficients as module expressions; `module`
then finishes the commutative scalar calculation.  This version doesn't
assume the ring is a division ring -- later it will be an endomorphism ring. -/
private lemma __QuaternionObstruction_quat_norm {R : Type*} [Ring R] [Algebra ℝ R]
    (I J : R) (hI : I * I = -(1 : R)) (hJ : J * J = -(1 : R))
    (hJI : J * I = -I * J) (a b c d : ℝ) :
    (a • (1 : R) - b • I - c • J - d • (I * J)) *
        (a • (1 : R) + b • I + c • J + d • (I * J)) =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • (1 : R) := by
  have hIIJ : I * (I * J) = -J := by
    rw [← mul_assoc, hI, neg_mul, one_mul]
  have hJIJ : J * (I * J) = I := by
    calc
      _ = -(I * J) * J := by rw [← mul_assoc, hJI, neg_mul]
      _ = -(I * (J * J)) := by rw [neg_mul, mul_assoc]
      _ = I := by rw [hJ, mul_neg, mul_one, neg_neg]
  have hIJIJ : I * (J * (I * J)) = -(1 : R) := by
    rw [hJIJ, hI]
  noncomm_ring [hI, hJ, hJI, hIIJ, hJIJ, hIJIJ]
  module

/-- In real dimension four an involution satisfying the relations for the
central element of a quaternion subgroup must be `-1`, unless it is `1`.

The statement is on endomorphisms, so it also applies to any four dimensional
real representation, without choosing matrices or bases.  It is useful to
keep `finrank` as an explicit hypothesis for re-use before a basis has been
chosen. -/
lemma quaternion_centre_forces_minus
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S I J : Module.End ℝ V)
    (hSS : S * S = 1)
    (hII : I * I = S) (hJJ : J * J = S)
    (hSI : S * I = I * S) (hSJ : S * J = J * S)
    (hJI : J * I = S * (I * J))
    (hS : S ≠ 1)
    [FiniteDimensional ℝ V]
    (hfin : Module.finrank ℝ V = 4) :
    S = -(1 : Module.End ℝ V) := by
  classical
  -- A nonidentity involution has a nonzero vector on which it is `-1`.
  have hex : ∃ w : V, S w ≠ w := by
    by_contra h
    push Not at h
    apply hS
    ext x
    simpa using h x
  choose w hw using hex
  let v : V := w - S w
  have hv0 : v ≠ 0 := by
    dsimp [v]
    exact sub_ne_zero.mpr (Ne.symm hw)
  have hvS : S v = -v := by
    dsimp [v]
    rw [map_sub]
    have hsw : S (S w) = w := by
      change (S * S) w = w
      rw [hSS]
      rfl
    rw [hsw]
    module

  -- Work on the minus eigenspace.  This avoids any characteristic-polynomial
  -- arguments; its definition as a kernel makes the restriction of the two
  -- maps very painless.
  let W : Submodule ℝ V := LinearMap.ker (S + 1)
  have wmem (x : V) (hx : S x = -x) : x ∈ W := by
    change (S + 1) x = 0
    change S x + x = 0
    rw [hx]
    simp
  have veig : v ∈ W := wmem v hvS
  let vv : W := ⟨v, veig⟩
  have vv0 : vv ≠ 0 := by
    intro h
    have he : v = 0 := congrArg (fun t : W => (t : V)) h
    exact hv0 he

  have hIcomm (x : V) : S (I x) = I (S x) := by
    simpa [Module.End.mul_apply] using
      congrArg (fun t : Module.End ℝ V => t x) hSI
  have hJcomm (x : V) : S (J x) = J (S x) := by
    simpa [Module.End.mul_apply] using
      congrArg (fun t : Module.End ℝ V => t x) hSJ
  have iInv (x : W) : I (x : V) ∈ W := by
    apply wmem
    rw [hIcomm]
    have hx : S (x : V) = -(x : V) := by
      have hm : (S + 1) (x : V) = 0 := x.property
      change S (x : V) + (x : V) = 0 at hm
      exact eq_neg_of_add_eq_zero_left hm
    rw [hx, map_neg]
  have jInv (x : W) : J (x : V) ∈ W := by
    apply wmem
    rw [hJcomm]
    have hx : S (x : V) = -(x : V) := by
      have hm : (S + 1) (x : V) = 0 := x.property
      change S (x : V) + (x : V) = 0 at hm
      exact eq_neg_of_add_eq_zero_left hm
    rw [hx, map_neg]

  let IW : Module.End ℝ W :=
    LinearMap.codRestrict W (I.comp W.subtype) (fun x => by
      change I (x : V) ∈ W
      exact iInv x)
  let JW : Module.End ℝ W :=
    LinearMap.codRestrict W (J.comp W.subtype) (fun x => by
      change J (x : V) ∈ W
      exact jInv x)

  have Hii : IW * IW = -(1 : Module.End ℝ W) := by
    ext x
    change I (I (x : V)) = _
    change (I * I) (x : V) = _
    rw [hII]
    have hx : S (x : V) = -(x : V) := by
      have hm : (S + 1) (x : V) = 0 := x.property
      change S (x : V) + (x : V) = 0 at hm
      exact eq_neg_of_add_eq_zero_left hm
    simpa using hx
  have Hjj : JW * JW = -(1 : Module.End ℝ W) := by
    ext x
    change J (J (x : V)) = _
    change (J * J) (x : V) = _
    rw [hJJ]
    have hx : S (x : V) = -(x : V) := by
      have hm : (S + 1) (x : V) = 0 := x.property
      change S (x : V) + (x : V) = 0 at hm
      exact eq_neg_of_add_eq_zero_left hm
    simpa using hx
  have Hji : JW * IW = -IW * JW := by
    ext x
    change J (I (x : V)) = _
    change (J * I) (x : V) = _
    rw [hJI]
    change S (I (J (x : V))) = _
    have hxW : I (J (x : V)) ∈ W := iInv ⟨J (x : V), jInv x⟩
    have hx : S (I (J (x : V))) = -(I (J (x : V))) := by
      have hm : (S + 1) (I (J (x : V))) = 0 := hxW
      change S (I (J (x : V))) + I (J (x : V)) = 0 at hm
      exact eq_neg_of_add_eq_zero_left hm
    change S (I (J (x : V))) = -(I (J (x : V)))
    exact hx

  -- Four independent vectors in the minus eigenspace.
  let b : Fin 4 → W := ![vv, IW vv, JW vv, IW (JW vv)]
  have bind : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have hg' :
        g 0 • vv + g 1 • IW vv + g 2 • JW vv + g 3 • IW (JW vv) = 0 := by
      simpa [Fin.sum_univ_four, b] using hg
    have hop :
        (g 0 • (1 : Module.End ℝ W) + g 1 • IW + g 2 • JW +
          g 3 • (IW * JW)) vv = 0 := by
      simpa [Module.End.mul_apply] using hg'
    have hnorm := __QuaternionObstruction_quat_norm IW JW Hii Hjj Hji (g 0) (g 1) (g 2) (g 3)
    let D : Module.End ℝ W :=
        g 0 • (1 : Module.End ℝ W) - g 1 • IW - g 2 • JW -
          g 3 • (IW * JW)
    have hzv : ((g 0) ^ 2 + (g 1) ^ 2 + (g 2) ^ 2 + (g 3) ^ 2) • vv = 0 := by
      have happ := congrArg (fun T : Module.End ℝ W => T vv) hnorm
      change
        D ((g 0 • (1 : Module.End ℝ W) + g 1 • IW + g 2 • JW +
              g 3 • (IW * JW)) vv) =
          (((g 0) ^ 2 + (g 1) ^ 2 + (g 2) ^ 2 + (g 3) ^ 2) •
              (1 : Module.End ℝ W)) vv at happ
      rw [hop, map_zero] at happ
      simpa using happ.symm
    have hsq : (g 0) ^ 2 + (g 1) ^ 2 + (g 2) ^ 2 + (g 3) ^ 2 = 0 := by
      by_contra hn
      exact vv0 (smul_eq_zero.mp hzv |>.resolve_left hn)
    have h0 : g 0 = 0 := by
      nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    have h1 : g 1 = 0 := by
      nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    have h2 : g 2 = 0 := by
      nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    have h3 : g 3 = 0 := by
      nlinarith [sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    fin_cases k <;> assumption

  have Wfin : Module.finrank ℝ W = Module.finrank ℝ V := by
    have lower := bind.fintype_card_le_finrank
    have upper := Submodule.finrank_le W
    simp [hfin] at lower upper ⊢
    omega
  have Wtop : W = ⊤ := Submodule.eq_top_of_finrank_eq Wfin
  ext x
  have hxW : x ∈ W := by rw [Wtop]; trivial
  have hm : (S + 1) x = 0 := hxW
  change S x + x = 0 at hm
  have hx : S x = -x := eq_neg_of_add_eq_zero_left hm
  simpa using hx

/-- A group-theoretic corollary, stated directly for the target of the problem.
If a group contains *two different* quaternion centres, no injective hom from
it to `GL (Fin 4) ℝ` exists.  All the hypotheses are relations in the source
group; in particular no faithfulness assumptions on the six elements are
smuggled in.  `hn1` and `hn2` just say the two central involutions are
nontrivial. -/
theorem no_GL4_of_two_quaternion_centres
    {G : Type*} [Group G]
    (i j z : G) (i' j' z' : G)
    (hz2 : z * z = 1) (hi2 : i * i = z) (hj2 : j * j = z)
    (hzi : z * i = i * z) (hzj : z * j = j * z)
    (hji : j * i = z * (i * j))
    (hz2' : z' * z' = 1) (hi2' : i' * i' = z') (hj2' : j' * j' = z')
    (hzi' : z' * i' = i' * z') (hzj' : z' * j' = j' * z')
    (hji' : j' * i' = z' * (i' * j'))
    (hn1 : z ≠ 1) (hn2 : z' ≠ 1) (hne : z ≠ z') :
    ∀ f : G →* GL (Fin 4) ℝ, ¬ Function.Injective f := by
  intro f hf
  let U : G →* (Module.End ℝ (Fin 4 → ℝ))ˣ :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp f
  let val (g : G) : Module.End ℝ (Fin 4 → ℝ) :=
    (U g : Module.End ℝ (Fin 4 → ℝ))
  have val_mul (a b : G) : val (a * b) = val a * val b := by
    dsimp [val]
    rw [map_mul]
    rfl
  have val_one : val (1 : G) = 1 := by
    change ((↑(U 1)) : Module.End ℝ (Fin 4 → ℝ)) = 1
    rw [map_one]
    rfl
  have val_ne_one {g : G} (hg : g ≠ 1) : val g ≠ 1 := by
    intro h
    have hu : U g = 1 := Units.ext h
    have he : f g = 1 := by
      have hx := congrArg
        (fun k : (Module.End ℝ (Fin 4 → ℝ))ˣ =>
          Matrix.GeneralLinearGroup.toLin.symm k) hu
      simpa [U] using hx
    have heq : g = 1 := hf (by simpa using he)
    exact hg heq
  have forces (a b c : G)
      (hcs : c * c = 1) (has : a * a = c) (hbs : b * b = c)
      (hcai : c * a = a * c) (hcbi : c * b = b * c)
      (hba : b * a = c * (a * b)) (hc : c ≠ 1) :
      val c = -(1 : Module.End ℝ (Fin 4 → ℝ)) := by
    apply quaternion_centre_forces_minus (val c) (val a) (val b)
    · rw [← val_mul, hcs, val_one]
    · rw [← val_mul, has]
    · rw [← val_mul, hbs]
    · rw [← val_mul, hcai, val_mul]
    · rw [← val_mul, hcbi, val_mul]
    · rw [← val_mul, hba, val_mul, val_mul]
    · exact val_ne_one hc
    · simp
  have h1 := forces i j z hz2 hi2 hj2 hzi hzj hji hn1
  have h2 := forces i' j' z' hz2' hi2' hj2' hzi' hzj' hji' hn2
  have heval : val z = val z' := h1.trans h2.symm
  have hu : U z = U z' := Units.ext heval
  have hfg : f z = f z' := by
    have hx := congrArg
      (fun k : (Module.End ℝ (Fin 4 → ℝ))ˣ =>
        Matrix.GeneralLinearGroup.toLin.symm k) hu
    simpa [U] using hx
  exact hne (hf hfg)

end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/QuaternionObstruction.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/RadialNeck.lean
section

noncomputable section
open Set Topology TopologicalSpace
open scoped Topology
namespace NonlinearThreeManifoldSupport

/-! Elementary radial inversion of a punctured vector ball.  In a connected
sum the coordinate at a deleted point is a punctured ball.  The useful
transition on that end keeps the direction and changes the radius `r` to
`R-r`.  These lemmas are deliberately coordinate only; they don't use any
manifold package. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- points of the punctured `R`-ball about zero. -/
def radialSet (R : ℝ) : Set E := {x | x ≠ 0 ∧ ‖x‖ < R}

lemma radialSet_open (R : ℝ) : IsOpen (radialSet (E:=E) R) := by
  -- remove the closed origin from the open norm ball
  have h1 : IsOpen ({(0:E)}ᶜ : Set E) := isClosed_singleton.isOpen_compl
  have h2 : IsOpen {x : E | ‖x‖ < R} := by
    exact isOpen_lt continuous_norm continuous_const
  have h := h1.inter h2
  -- coerce complement singleton to nonzero
  convert h using 1 <;> ext x <;> simp [radialSet]


/-- The radial involution on a punctured ball.  We use the formula about zero;
a chart is translated before applying it. -/
def radialFlip (R : ℝ) (x : E) : E := ((R - ‖x‖) / ‖x‖) • x

lemma radialFlip_norm {R : ℝ} (hR : 0 < R)
    {x : E} (hx : x ∈ radialSet (E:=E) R) :
    ‖radialFlip R x‖ = R - ‖x‖ := by
  rcases hx with ⟨hx0, hxR⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hp : 0 < R - ‖x‖ := sub_pos.mpr hxR
  rw [radialFlip, norm_smul]
  -- for real norm of scalar
  rw [Real.norm_eq_abs, abs_of_pos (div_pos hp hxpos)]
  field_simp

lemma radialFlip_mem {R : ℝ} (hR : 0 < R)
    {x : E} (hx : x ∈ radialSet (E:=E) R) :
    radialFlip R x ∈ radialSet (E:=E) R := by
  rcases hx with ⟨hx0, hxR⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hp : 0 < R - ‖x‖ := sub_pos.mpr hxR
  have hnorm := radialFlip_norm (E:=E) hR (x:=x) ⟨hx0,hxR⟩
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg norm h
    rw [hnorm] at this
    simp at this
    linarith
  · rw [hnorm]
    linarith

lemma radialFlip_invol {R : ℝ} (hR : 0 < R)
    {x : E} (hx : x ∈ radialSet (E:=E) R) :
    radialFlip R (radialFlip R x) = x := by
  rcases hx with ⟨hx0, hxR⟩
  have nx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have py : 0 < R - ‖x‖ := sub_pos.mpr hxR
  have nflip : ‖radialFlip R x‖ = R - ‖x‖ :=
    radialFlip_norm (E:=E) hR (x:=x) ⟨hx0,hxR⟩
  change ((R - ‖radialFlip R x‖) / ‖radialFlip R x‖) •
       ( ((R - ‖x‖) / ‖x‖) • x) = x
  rw [nflip]
  rw [smul_smul]
  -- cancellation of two inverse positive scales
  have hcalc : ((R - (R - ‖x‖)) / (R - ‖x‖)) *
        ((R - ‖x‖) / ‖x‖) = (1:ℝ) := by
    have hn0 : ‖x‖ ≠ 0 := ne_of_gt nx
    have hp0 : R - ‖x‖ ≠ 0 := ne_of_gt py
    field_simp
    ring
  rw [hcalc]
  exact one_smul _ _

/-- Continuity of the radial formula away from the origin. -/
lemma radialFlip_continuousOn (R : ℝ) :
    ContinuousOn (radialFlip (E:=E) R) (radialSet (E:=E) R) := by
  intro x hx
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx.1
  -- build by continuousAt; division is safe on the subtype set
  have hnorm : Continuous (fun y : E => ‖y‖) := continuous_norm
  have hdiv : ContinuousAt (fun y : E => (R - ‖y‖) / ‖y‖) x := by
    fun_prop
  have hmul : ContinuousAt (fun y : E =>
      ((R - ‖y‖) / ‖y‖) • y) x := by
    fun_prop
  exact hmul.continuousWithinAt

/-- Bundled self homeomorphism of a punctured ball.  This is the local
transition map for a two-open connected sum. -/
noncomputable def radialFlipHomeo (R : ℝ) (hR : 0 < R) :
    (radialSet (E:=E) R : Set E) ≃ₜ (radialSet (E:=E) R : Set E) := by
  let f : (radialSet (E:=E) R : Set E) →
      (radialSet (E:=E) R : Set E) :=
    fun x => ⟨radialFlip R (x:E), radialFlip_mem (E:=E) hR x.property⟩
  have fi (x : (radialSet (E:=E) R : Set E)) : f (f x) = x := by
    apply Subtype.ext
    exact radialFlip_invol (E:=E) hR x.property
  have fc : Continuous f := by
    -- induced topology on the subtype
    apply continuous_induced_rng.2
    -- domain is also induced
    have h := (radialFlip_continuousOn (E:=E) R).restrict
    exact h
  -- the previous line awkward; replace with the standard `ContinuousOn.restrict`
  exact {
    toEquiv := ⟨f, f, fi, fi⟩
    continuous_toFun := fc
    continuous_invFun := fc }

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open Set Topology TopologicalSpace
open scoped Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

/-- Radius data for one chart about the deleted point.  Keeping it explicit is
helpful: no compatibility of charts is used in the neck. -/
structure ChartBall (b : Y) where
  R : ℝ
  pos : 0 < R
  sub : Metric.ball ((chartAt E b) b) R ⊆ (chartAt E b).target

/-- Every chart contains a closed positive smaller open ball about its centre.
Only the open ball is needed later. -/
lemma existsChartBall (b : Y) : Nonempty (ChartBall (E:=E) b) := by
  have hb : (chartAt E b) b ∈ (chartAt E b).target :=
    (chartAt E b).map_source (mem_chart_source E b)
  obtain ⟨ε,hε,he⟩ := (Metric.isOpen_iff.1 (chartAt E b).open_target)
       ((chartAt E b) b) hb
  exact ⟨⟨ε, hε, he⟩⟩

/-- The open punctured chart-end, as a set in `Y`. -/
def chartEndSet (b : Y) (A : ChartBall (E:=E) b) : Set Y :=
  let φ := chartAt E b
  let p : E := φ b
  φ.source ∩ φ ⁻¹' {z : E | z - p ∈ radialSet (E:=E) A.R}

lemma chartEndSet_open (b : Y) (A : ChartBall (E:=E) b) :
    IsOpen (chartEndSet (E:=E) b A) := by
  let φ := chartAt E b
  let p : E := φ b
  have hs : IsOpen {z : E | z - p ∈ radialSet (E:=E) A.R} := by
    have hc : Continuous (fun z : E => z - p) := continuous_id.sub continuous_const
    exact (radialSet_open (E:=E) A.R).preimage hc
  exact (chartAt E b).isOpen_inter_preimage hs

lemma chartEndSet_sub_compl (b : Y) (A : ChartBall (E:=E) b) :
    chartEndSet (E:=E) b A ⊆ ({b} : Set Y)ᶜ := by
  intro x hx
  rcases hx with ⟨hxS,hxrad⟩
  change x ∈ ({b} : Set Y)ᶜ
  have nz : (chartAt E b) x - (chartAt E b) b ≠ (0:E) := hxrad.1
  -- if the point were b the difference would vanish
  intro ex
  have : x = b := by simpa using ex
  apply nz
  simp [this]

/-- The punctured chart end as an open subset of the punctured manifold. -/
def chartEnd (b : Y) (A : ChartBall (E:=E) b) :
    Opens (TopCat.of (({b} : Set Y)ᶜ : Set Y)) where
  carrier := {x : (({b}:Set Y)ᶜ : Set Y) | (x:Y) ∈ chartEndSet (E:=E) b A}
  is_open' := (chartEndSet_open (E:=E) b A).preimage continuous_subtype_val

-- maps between chart end and the coordinate punctured ball
private def __RadialNeck_chartEnd_to (b : Y) (A : ChartBall (E:=E) b) :
    (chartEnd (E:=E) b A : Type _) →
      (radialSet (E:=E) A.R : Set E) :=
  fun x => ⟨(chartAt E b) (x.1.1) - (chartAt E b) b, x.2.2⟩

private def __RadialNeck_chartEnd_from (b : Y) (A : ChartBall (E:=E) b) :
    (radialSet (E:=E) A.R : Set E) →
      (chartEnd (E:=E) b A : Type _) := fun z => by
  let φ := chartAt E b
  let p : E := φ b
  have ht : p + (z:E) ∈ φ.target := by
    apply A.sub
    have hn := z.property.2
    -- distance to centre is the norm of the displacement
    rw [Metric.mem_ball, dist_eq_norm]
    have hvec : p + (z:E) - (chartAt E b) b = (z:E) := by
      dsimp [p, φ]
      abel
    simpa [hvec] using hn
  let y : Y := φ.symm (p + (z:E))
  have ys : y ∈ φ.source := φ.symm.map_source ht
  have yy : φ y = p + (z:E) := φ.right_inv ht
  have yr : φ y - p ∈ radialSet (E:=E) A.R := by
    simpa [yy] using z.property
  have ycomp : y ∈ ({b}:Set Y)ᶜ :=
    chartEndSet_sub_compl (E:=E) b A ⟨ys, yr⟩
  exact ⟨⟨y, ycomp⟩, ⟨ys, yr⟩⟩

lemma chartEnd_left (b : Y) (A : ChartBall (E:=E) b)
    (x : (chartEnd (E:=E) b A : Type _)) :
    __RadialNeck_chartEnd_from (E:=E) b A (__RadialNeck_chartEnd_to (E:=E) b A x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  -- inverse chart cancels on the source
  change (chartAt E b).symm
       ((chartAt E b) b + ((chartAt E b) (x.1.1) - (chartAt E b) b)) = x.1.1
  have hvec : (chartAt E b) b +
      ((chartAt E b) (x.1.1) - (chartAt E b) b) =
        (chartAt E b) (x.1.1) := by abel
  rw [hvec]
  exact (chartAt E b).left_inv x.property.1

lemma chartEnd_right (b : Y) (A : ChartBall (E:=E) b)
    (z : (radialSet (E:=E) A.R : Set E)) :
    __RadialNeck_chartEnd_to (E:=E) b A (__RadialNeck_chartEnd_from (E:=E) b A z) = z := by
  apply Subtype.ext
  change (chartAt E b)
      ((chartAt E b).symm ((chartAt E b) b + (z:E))) - (chartAt E b) b = z
  have ht : (chartAt E b) b + (z:E) ∈ (chartAt E b).target := by
    apply A.sub
    simpa [dist_eq_norm] using z.property.2
  rw [(chartAt E b).right_inv ht]
  exact add_sub_cancel_left _ _

/-- Coordinates identify the chart end with the model punctured vector ball. -/
noncomputable def chartEndHomeo (b : Y) (A : ChartBall (E:=E) b) :
    (chartEnd (E:=E) b A : Type _) ≃ₜ (radialSet (E:=E) A.R : Set E) := by
  refine {
    toEquiv := ⟨__RadialNeck_chartEnd_to (E:=E) b A, __RadialNeck_chartEnd_from (E:=E) b A,
      chartEnd_left (E:=E) b A, chartEnd_right (E:=E) b A⟩
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · -- chart is continuous on its source
    apply continuous_induced_rng.2
    -- function from the end to E
    have ch := (chartAt E b).continuousOn.restrict
    -- restrict currently to entire chart source; easier pointwise with is open?
    -- use continuity at points via factor through subtype source
    -- build `end -> source`
    let u : (chartEnd (E:=E) b A : Type _) →
        ((chartAt E b).source : Set Y) :=
      fun x => ⟨x.1.1, x.property.1⟩
    have uc : Continuous u := by fun_prop
    change Continuous (fun x : (chartEnd (E:=E) b A : Type _) =>
      (chartAt E b) (x.1.1) - (chartAt E b) b)
    exact ( ( (chartAt E b).continuousOn.restrict ).comp uc).sub continuous_const
  · -- inverse chart continuous on the open target; inclusion of coordinates lies there
    -- target is the open end (subtype of subtype); prove through both inductions
    apply continuous_induced_rng.2
    apply continuous_induced_rng.2
    let v : (radialSet (E:=E) A.R : Set E) →
         ((chartAt E b).target : Set E) := fun z => by
       refine ⟨(chartAt E b) b + (z:E), ?_⟩
       apply A.sub
       simpa [dist_eq_norm] using z.property.2
    have vc : Continuous v := by
      apply continuous_induced_rng.2
      change Continuous (fun z : (radialSet (E:=E) A.R : Set E) =>
        (chartAt E b) b + (z:E))
      fun_prop
    change Continuous (fun z : (radialSet (E:=E) A.R : Set E) =>
      (chartAt E b).symm ((chartAt E b) b + (z:E)))
    exact ((chartAt E b).symm.continuousOn.restrict).comp vc

/-- Radial transition on a punctured chart.  This is the actual `e` asked for
in the two-patch cut; it is not an arbitrary self-equivalence and hence
exchanges the two ends. -/
noncomputable def chartEndFlip (b : Y) (A : ChartBall (E:=E) b) :
    (chartEnd (E:=E) b A : Type _) ≃ₜ
      (chartEnd (E:=E) b A : Type _) :=
  (chartEndHomeo (E:=E) b A).trans
    ((radialFlipHomeo (E:=E) A.R A.pos).trans
      (chartEndHomeo (E:=E) b A).symm)

lemma chartEndFlip_invol (b : Y) (A : ChartBall (E:=E) b)
    (x : (chartEnd (E:=E) b A : Type _)) :
    chartEndFlip (E:=E) b A (chartEndFlip (E:=E) b A x) = x := by
  -- in coordinates this is `R-r` twice
  apply (chartEndHomeo (E:=E) b A).injective
  change (chartEndHomeo (E:=E) b A)
      (chartEndFlip (E:=E) b A (chartEndFlip (E:=E) b A x)) = _
  change _ = _
  simp only [chartEndFlip, Homeomorph.trans_apply]
  simp only [Homeomorph.apply_symm_apply]
  change (radialFlipHomeo (E:=E) A.R A.pos)
        ((radialFlipHomeo (E:=E) A.R A.pos)
          ((chartEndHomeo (E:=E) b A) x)) =
      (chartEndHomeo (E:=E) b A) x
  apply Subtype.ext
  exact radialFlip_invol (E:=E) A.pos
     (((chartEndHomeo (E:=E) b A) x).property)

end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
lemma radialSet_nonempty (R : ℝ) (hR : 0 < R) :
    (radialSet (E:=E) R : Set E).Nonempty := by
  obtain ⟨v,hv⟩ : ∃ v : E, v ≠ 0 := exists_ne 0
  have nv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let t : ℝ := R / (2 * ‖v‖)
  have tp : 0 < t := div_pos hR (mul_pos (by norm_num) nv)
  refine ⟨t • v, ?_, ?_⟩
  · exact smul_ne_zero (ne_of_gt tp) hv
  · rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos tp]
    dsimp [t]
    have hn0 : ‖v‖ ≠ 0 := ne_of_gt nv
    field_simp
    nlinarith [hR]
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/RadialNeck.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/SpherePaths.lean
section
open scoped Topology RealInnerProductSpace
open Topology Set Metric unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport

/-- Normalize a nonzero vector to the unit metric sphere.  This elementary
construction is useful for writing down path homotopies without choosing
stereographic charts. -/
def sphereNormalize {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : V) (hv : v ≠ 0) : Metric.sphere (0:V) 1 := by
  refine ⟨(‖v‖)⁻¹ • v, ?_⟩
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  -- membership of the metric sphere at zero is just a norm equation
  change dist ((‖v‖)⁻¹ • v) 0 = 1
  rw [dist_zero_right, norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

@[simp] lemma sphereNormalize_val {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (v : V) (hv : v ≠ 0) :
    (sphereNormalize v hv : V) = (‖v‖)⁻¹ • v := rfl

/-- Normalizing a vector which is already on the unit sphere does nothing. -/
lemma sphereNormalize_of_mem {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (x : Metric.sphere (0:V) 1) (hx : (x:V) ≠ 0) :
    sphereNormalize (x:V) hx = x := by
  apply Subtype.ext
  have nx : ‖(x:V)‖ = 1 := by
    have h := x.property
    change dist (x:V) 0 = 1 at h
    simpa [dist_zero_right] using h
  change (‖(x:V)‖)⁻¹ • (x:V) = (x:V)
  rw [nx]
  simp

/-- The radial, straight-line formula for homotoping two paths on a sphere.
The hypothesis is intentionally the exact obstruction: for no parameter is
one interpolating vector zero.  This makes the lemma apply without local
coordinates or a compactness argument.  Endpoints are fixed by construction. -/
lemma sphere_paths_homotopic_of_segment_ne_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x y : Metric.sphere (0:V) 1}
    (p q : Path x y)
    (hzero : ∀ (u t : I),
      ( (1 - (u:ℝ)) • (p t : V) + (u:ℝ) • (q t : V)) ≠ 0) :
    Path.Homotopic p q := by
  let raw : I × I → V := fun st =>
    (1 - (st.1:ℝ)) • (p st.2 : V) + (st.1:ℝ) • (q st.2 : V)
  have raw_ne (st : I × I) : raw st ≠ 0 := hzero st.1 st.2
  have raw_cont : Continuous raw := by
    dsimp [raw]
    fun_prop
  -- Normalisation varies continuously because the norm never vanishes.
  have norm_ne (st : I × I) : ‖raw st‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (raw_ne st)
  let toS : I × I → Metric.sphere (0:V) 1 :=
    fun st => sphereNormalize (raw st) (raw_ne st)
  have toS_cont : Continuous toS := by
    -- prove continuity after the subtype coercion
    apply continuous_induced_rng.2
    change Continuous (fun st : I × I => (sphereNormalize (raw st) (raw_ne st) : V))
    change Continuous (fun st : I × I => (‖raw st‖)⁻¹ • raw st)
    have hn : Continuous (fun st : I × I => ‖raw st‖) :=
      continuous_norm.comp raw_cont
    have hi : Continuous (fun st : I × I => (‖raw st‖)⁻¹) := by
      -- inversion in the reals is continuous away from zero
      fun_prop (disch := aesop)
    fun_prop
  refine ⟨({
    toFun := toS
    continuous_toFun := toS_cont
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ } : p.Homotopy q)⟩
  · intro t
    have hp0 : (p t : V) ≠ 0 := by
      -- its norm is one
      intro hz
      have h := (p t).property
      change dist (p t : V) 0 = 1 at h
      simpa [hz] using h
    have eraw : raw (0, t) = (p t : V) := by
      dsimp [raw]
      simp
    -- equality of the normalized subtype
    change sphereNormalize (raw (0,t)) (raw_ne (0,t)) = p t
    apply Subtype.ext
    have npt : ‖(p t : V)‖ = 1 := by
      have h := (p t).property
      change dist (p t : V) 0 = 1 at h
      simpa [dist_zero_right] using h
    change (‖raw (0,t)‖)⁻¹ • raw (0,t) = (p t : V)
    rw [eraw, npt]
    simp
  · intro t
    have eraw : raw (1, t) = (q t : V) := by
      dsimp [raw]
      simp
    change sphereNormalize (raw (1,t)) (raw_ne (1,t)) = q t
    apply Subtype.ext
    have nqt : ‖(q t : V)‖ = 1 := by
      have h := (q t).property
      change dist (q t : V) 0 = 1 at h
      simpa [dist_zero_right] using h
    change (‖raw (1,t)‖)⁻¹ • raw (1,t) = (q t : V)
    rw [eraw, nqt]
    simp
  · intro u t ht
    -- fixed on the two endpoints of the path
    have ep : (p t : V) = (q t : V) := by
      rcases ht with ht | ht
      · change t = (0:I) at ht
        subst t
        -- both paths start at `x`
        have a := p.source
        have b := q.source
        exact congrArg Subtype.val (a.trans b.symm)
      · have ht' : t = (1:I) := by simpa using ht
        subst t
        have a := p.target
        have b := q.target
        exact congrArg Subtype.val (a.trans b.symm)
    have eraw : raw (u,t) = (p t : V) := by
      dsimp [raw]
      rw [← ep]
      rw [← add_smul]
      have hsc : (1 - (u:ℝ)) + (u:ℝ) = 1 := by ring
      rw [hsc]
      simp
    change sphereNormalize (raw (u,t)) (raw_ne (u,t)) = p t
    apply Subtype.ext
    have npt : ‖(p t : V)‖ = 1 := by
      have h := (p t).property
      change dist (p t : V) 0 = 1 at h
      simpa [dist_zero_right] using h
    change (‖raw (u,t)‖)⁻¹ • raw (u,t) = (p t : V)
    rw [eraw, npt]
    simp

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open scoped RealInnerProductSpace
/-- A convenient sufficient condition for the radial formula: if two paths lie
in the same open hemisphere, containing vector `c`, their pointwise segments
miss the origin. -/
lemma sphere_paths_homotopic_of_inner_pos
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x y : Metric.sphere (0:V) 1}
    (p q : Path x y) (c : V)
    (hp : ∀ t : I, 0 < @inner ℝ V _ c (p t : V))
    (hq : ∀ t : I, 0 < @inner ℝ V _ c (q t : V)) :
    Path.Homotopic p q := by
  apply sphere_paths_homotopic_of_segment_ne_zero p q
  intro u t hz
  have hz' := congrArg (fun w : V => @inner ℝ V _ c w) hz
  have zcalc :
      (1 - (u:ℝ)) * (@inner ℝ V _ c (p t : V)) +
      (u:ℝ) * (@inner ℝ V _ c (q t : V)) = 0 := by
    simpa [inner_add_right, inner_smul_right] using hz'
  have hu0 : 0 ≤ (u:ℝ) := u.property.1
  have hu1 : (u:ℝ) ≤ 1 := u.property.2
  have a := hp t
  have b := hq t
  -- a convex combination of two positive reals is positive
  have pos : 0 <
      (1 - (u:ℝ)) * (@inner ℝ V _ c (p t : V)) +
      (u:ℝ) * (@inner ℝ V _ c (q t : V)) := by
    by_cases h1 : (u:ℝ) = 1
    · simp [h1, b]
    · have hlt : (u:ℝ) < 1 := lt_of_le_of_ne hu1 h1
      have leftpos : 0 < (1 - (u:ℝ)) *
          (@inner ℝ V _ c (p t : V)) :=
        mul_pos (sub_pos.mpr hlt) a
      have rightnon : 0 ≤ (u:ℝ) *
          (@inner ℝ V _ c (q t : V)) :=
        mul_nonneg hu0 (le_of_lt b)
      linarith
  linarith
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
/-- A small gluing convenience: it suffices to put a third path in radial
position with each of two given paths.  The transitivity is in the path
homotopy relation, so endpoints are preserved. -/
lemma sphere_paths_homotopic_of_middle
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x y : Metric.sphere (0:V) 1}
    (p q : Path x y)
    (r : Path x y)
    (hpr : ∀ (u t : I),
      ((1 - (u:ℝ)) • (p t : V) + (u:ℝ) • (r t : V)) ≠ 0)
    (hrq : ∀ (u t : I),
      ((1 - (u:ℝ)) • (r t : V) + (u:ℝ) • (q t : V)) ≠ 0) :
    Path.Homotopic p q :=
  (sphere_paths_homotopic_of_segment_ne_zero p r hpr).trans
    (sphere_paths_homotopic_of_segment_ne_zero r q hrq)
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
/-- On a real norm sphere a chord passes through the origin only for an
antipodal pair.  This pointwise version removes the homotopy parameter from
subsequent path bookkeeping. -/
lemma sphere_segment_ne_zero_of_ne_neg
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x y : Metric.sphere (0:V) 1)
    (hne : (y:V) ≠ - (x:V)) (u : I) :
    ((1 - (u:ℝ)) • (x:V) + (u:ℝ) • (y:V)) ≠ 0 := by
  intro hz
  let a : ℝ := (u:ℝ)
  have ha0 : 0 ≤ a := u.property.1
  have ha1 : a ≤ 1 := u.property.2
  have nx : ‖(x:V)‖ = 1 := by
    have h := x.property
    change dist (x:V) 0 = 1 at h
    simpa [dist_zero_right] using h
  have ny : ‖(y:V)‖ = 1 := by
    have h := y.property
    change dist (y:V) 0 = 1 at h
    simpa [dist_zero_right] using h
  have lin : (1-a) • (x:V) = -(a • (y:V)) := by
    dsimp [a]
    -- move the second summand in the zero equation
    exact eq_neg_of_add_eq_zero_left hz
  -- comparing norms pins the parameter to 1/2
  have nlin := congrArg norm lin
  have tabs : |1-a| = |a| := by
    simpa [norm_smul, Real.norm_eq_abs, nx, ny]
      using nlin
  have ta : a = (1/2:ℝ) := by
    have h1 : |a| = a := abs_of_nonneg ha0
    have h2 : |1-a| = 1-a := abs_of_nonneg (sub_nonneg.mpr ha1)
    rw [h1, h2] at tabs
    linarith
  rw [ta] at lin
  have half : (1-(1/2:ℝ)) = (1/2:ℝ) := by norm_num
  rw [half] at lin
  have hcancel : (x:V) = -(y:V) := by
    -- cancel the nonzero real scalar
    have : (1/2:ℝ) • (x:V) = (1/2:ℝ) • (-(y:V)) := by
      simpa using lin
    exact (smul_right_injective V (by norm_num : (1/2:ℝ) ≠ 0) this)
  apply hne
  have hnxy : -(x:V) = (y:V) := by
    simpa using (congrArg Neg.neg hcancel)
  exact hnxy.symm

/-- Thus a middle path need only avoid the antipodes pointwise. -/
lemma sphere_paths_homotopic_of_middle_ne_neg
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x y : Metric.sphere (0:V) 1}
    (p q : Path x y) (r : Path x y)
    (hpr : ∀ t : I, (r t : V) ≠ -(p t : V))
    (hrq : ∀ t : I, (q t : V) ≠ -(r t : V)) :
    Path.Homotopic p q := by
  apply sphere_paths_homotopic_of_middle p q r
  · intro u t
    exact sphere_segment_ne_zero_of_ne_neg (p t) (r t) (hpr t) u
  · intro u t
    -- segment from r to q; the hypothesis has the right orientation
    exact sphere_segment_ne_zero_of_ne_neg (r t) (q t) (hrq t) u
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
/-- Direct corollary: two paths which are never pointwise antipodal are
already in radial position. -/
lemma sphere_paths_homotopic_of_forall_ne_neg
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x y : Metric.sphere (0:V) 1}
    (p q : Path x y)
    (h : ∀ t : I, (q t : V) ≠ -(p t : V)) :
    Path.Homotopic p q := by
  apply sphere_paths_homotopic_of_segment_ne_zero p q
  intro u t
  exact sphere_segment_ne_zero_of_ne_neg (p t) (q t) (h t) u
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/SpherePaths.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/SplitPacket.lean
section
/-!
A pair of splitting maps is a cheaper replacement for the free-product calculation in the
connected-sum step.  For a connected sum it should come from the two pinch maps: the other
punctured component is killed by each pinch.  Thus one need not know full van Kampen to keep
the two order-two elements apart.
-/
namespace NonlinearThreeManifoldSupport
variable {P : Type*} [Group P]

@[simp] lemma q8_centre_ne_one : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by
  -- the order of `a 1` is four, or just the two distinct residues
  intro h
  change (QuaternionGroup.a (n:=2) (2 : ZMod 4) : QuaternionGroup 2) = QuaternionGroup.a (n:=2) (0 : ZMod 4) at h
  injection h with z
  have nz : (2 : ZMod 4) ≠ 0 := by decide
  exact nz z

/-- In a group `P`, sections for the two quaternion factors which can be separated by pinch
maps already give exactly the pair of embeddings used by the obstruction.  `r ∘ v` need
only kill the central element, not the whole factor -- this version is handy with the based
maps from a punctured block. -/
lemma q8_embeddings_of_splittings
    (u v : QuaternionGroup 2 →* P)
    (r s : P →* QuaternionGroup 2)
    (hu : r.comp u = MonoidHom.id (QuaternionGroup 2))
    (hv : s.comp v = MonoidHom.id (QuaternionGroup 2))
    (hkill : r (v (.a 2)) = 1) :
    Function.Injective u ∧ Function.Injective v ∧ u (.a 2) ≠ v (.a 2) := by
  have iu : Function.Injective u := by
    intro a b e
    have er : r (u a) = r (u b) := congrArg r e
    have compa : r (u a) = a := by
      have t := DFunLike.congr_fun hu a
      exact t
    have compb : r (u b) = b := by
      have t := DFunLike.congr_fun hu b
      exact t
    rwa [compa, compb] at er
  have iv : Function.Injective v := by
    intro a b e
    have es : s (v a) = s (v b) := congrArg s e
    have compa : s (v a) = a := DFunLike.congr_fun hv a
    have compb : s (v b) = b := DFunLike.congr_fun hv b
    rwa [compa, compb] at es
  refine ⟨iu, iv, ?_⟩
  intro w
  have w' : r (u (.a 2)) = r (v (.a 2)) := congrArg r w
  have t : r (u (.a 2)) = (.a 2) := DFunLike.congr_fun hu _
  have bad : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 :=
    t ▸ (w'.trans hkill)
  exact q8_centre_ne_one bad
end NonlinearThreeManifoldSupport

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/SplitPacket.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/BasedHomotopy.lean
section
open scoped Topology
open Set Topology unitInterval
noncomputable section
open NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport.BasedCMap
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}
lemma piOne_homotopyRel (f g : BasedCMap X x Y y)
    (F : ContinuousMap.HomotopyRel f.toContinuousMap g.toContinuousMap {x}) :
    piOne f = piOne g := by
  -- quotient induction
  ext a
  change Path.Homotopic.Quotient x x at a
  induction a using Quotient.inductionOn with | _ p => ?_
  dsimp [piOne]
  change
    (FundamentalGroup.mapOfEq f.toContinuousMap _)
      (FundamentalGroup.fromPath (.mk p)) =
    (FundamentalGroup.mapOfEq g.toContinuousMap _)
      (FundamentalGroup.fromPath (.mk p))
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  -- endpoints casts
  have hpath :
      Path.Homotopic
        ((p.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm)
        ((p.map g.toContinuousMap.continuous).cast g.map_pt.symm g.map_pt.symm) := by
    -- build a square from F
    let Q : Path.Homotopy
        ((p.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm)
        ((p.map g.toContinuousMap.continuous).cast g.map_pt.symm g.map_pt.symm) := by
      -- abbreviate casts values defeq
      refine { toFun := fun ts => F (ts.1, p ts.2),
               continuous_toFun := ?_,
               map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }
      · exact ContinuousMap.HomotopyWith.continuous F |>.comp (by fun_prop)
      · intro t
        change F (0, p t) = _
        simpa using (ContinuousMap.HomotopyWith.apply_zero F (p t))
      · intro t
        change F (1, p t) = _
        simpa using (ContinuousMap.HomotopyWith.apply_one F (p t))
      · intro t s hs
        rcases hs with (rfl | h)
        · change F (t, p 0) = _
          rw [p.source]
          have rhs :
              ((p.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm) 0 = y :=
            Path.source _
          change F (t, x) =
            ((p.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm) 0
          -- the fixed-edge value of the ambient homotopy is `f x`
          rw [rhs]
          exact (F.eq_fst t (show x ∈ ({x}:Set X) by simp)).trans f.map_pt
        · have hh : s = 1 := by simpa using h
          subst s
          change F (t, p 1) = _
          rw [p.target]
          have rhs :
              ((p.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm) 1 = y :=
            Path.target _
          change F (t, x) =
            ((p.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm) 1
          rw [rhs]
          exact (F.eq_fst t (show x ∈ ({x}:Set X) by simp)).trans f.map_pt
    exact ⟨Q⟩
  exact Quotient.sound hpath
end NonlinearThreeManifoldSupport.BasedCMap

namespace NonlinearThreeManifoldSupport.BasedCMap
open scoped Topology
open Set Topology
/-- A relative homotopy is the right sufficient datum for the *incoming*
neck maps.  Recording this once avoids treating `FundamentalGroup.map` as
literally functorial at incorrectly identified end-points. -/
lemma three_piOne_equations_of_homotopies
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y}
    (i j : BasedCMap Y y X x) (r s : BasedCMap X x Y y)
    (hi : ContinuousMap.HomotopyRel
      (comp r i).toContinuousMap (identity Y y).toContinuousMap {y})
    (hj : ContinuousMap.HomotopyRel
      (comp s j).toContinuousMap (identity Y y).toContinuousMap {y})
    (hk : ContinuousMap.HomotopyRel
      (comp r j).toContinuousMap
        (constant Y y Y y).toContinuousMap {y}) :
    (piOne r).comp (piOne i) = MonoidHom.id (FundamentalGroup Y y) ∧
    (piOne s).comp (piOne j) = MonoidHom.id (FundamentalGroup Y y) ∧
    (∀ a : FundamentalGroup Y y, piOne r (piOne j a) = 1) := by
  have Ei := piOne_homotopyRel (comp r i) (identity Y y) hi
  have Ej := piOne_homotopyRel (comp s j) (identity Y y) hj
  have Ek := piOne_homotopyRel (comp r j) (constant Y y Y y) hk
  refine ⟨?_, ?_, ?_⟩
  · rw [← piOne_comp]
    rw [Ei]
    exact piOne_identity y
  · rw [← piOne_comp]
    rw [Ej]
    exact piOne_identity y
  · intro a
    have h := DFunLike.congr_fun Ek a
    rw [piOne_comp] at h
    exact h.trans (piOne_constant_apply y y a)
end NonlinearThreeManifoldSupport.BasedCMap

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/BasedHomotopy.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/DoubleGlue.lean
section
noncomputable section
open Set Topology TopologicalSpace CategoryTheory
open TopCat
namespace NonlinearThreeManifoldSupport
-- all carriers in the target theorem are small; using `Bool` as a literal
-- index keeps the dependent equalities in `mk'` transparent.
universe u


/-! A convenient two-chart `GlueData`.  Nothing in the colimit APIs makes the
standard two-patch situation particularly pleasant to instantiate: all triple
pullbacks have to be specified.  `mk'` avoids them, but still leaves several
small dependent equalities.  In a neck there are just two identical patches
and an involution of an open end.  We record that case here.  Separation or
compactness of the resulting colimit are intentionally **not** asserted --
an arbitrary self gluing can of course be non-Hausdorff. -/

/-- The transition core for two copies of `X`, identified on `V` by an
involutive homeomorphism.  The index `false` and `true` have the same open
patch, but no second identifications are made off of `V`. -/
noncomputable def doubleCore (X : TopCat.{0}) (V : Opens X)
    (e : (V : Type) ≃ₜ (V : Type))
    (he : ∀ x : (V : Type), e (e x) = x) : TopCat.GlueData.MkCore := by
  let U : Bool → TopCat.{0} := fun _ => X
  let W : ∀ i : Bool, Bool → Opens (U i)
    | false, false => ⊤
    | false, true => V
    | true, false => V
    | true, true => ⊤
  let T : ∀ i j : Bool,
      (Opens.toTopCat _).obj (W i j) ⟶ (Opens.toTopCat _).obj (W j i)
    | false, false => 𝟙 _
    | true, true => 𝟙 _
    | false, true => TopCat.ofHom ⟨(fun x => e x), e.continuous⟩
    | true, false => TopCat.ofHom ⟨(fun x => e x), e.continuous⟩
  refine { J := Bool, U := U, V := W, t := T, V_id := ?_, t_id := ?_,
           t_inter := ?_, cocycle := ?_ }
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · intro i j k x hx
    cases i <;> cases j <;> cases k
    all_goals
      first
      | trivial
      | exact hx
      | (change ( (e (x : (V : Type))) : X) ∈ (V : Set X); exact (e x).property)
  · intro i j k x hx
    cases i <;> cases j <;> cases k
    all_goals
      -- equality of points of the ambient patch; the coercions in MkCore
      -- discard their subtype proofs, so only the pointwise involution is
      -- relevant.
      change _ = (_ : X)
    · rfl
    · rfl
    · exact congrArg Subtype.val (he x)
    · rfl
    · rfl
    · exact congrArg Subtype.val (he x)
    · rfl
    · rfl

/-- The actual two-open glued datum.  Its two patch images are open embeddings
and their intersection is `V`.  This lemma is useful even before proving any
Hausdorff theorem about a specific end. -/
noncomputable def doubleGlueData (X : TopCat.{0}) (V : Opens X)
    (e : (V : Type) ≃ₜ (V : Type)) (he : ∀ x : (V : Type), e (e x) = x) :
    TopCat.GlueData.{0} :=
  TopCat.GlueData.mk' (doubleCore X V e he)

@[simp] lemma doubleCore_U (X : TopCat.{0}) (V : Opens X)
    (e : (V : Type) ≃ₜ (V : Type)) (he : ∀ x : (V : Type), e (e x) = x)
    (i : Bool) : (doubleGlueData X V e he).U i = X := rfl

-- simp lemmas for extracting a representative of this colimit are deliberately
-- not included: `ι_jointly_surjective` and `continuousMapFromGlue` are usually
-- less brittle than reducing the quotient expression.

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open Set Topology TopologicalSpace CategoryTheory TopCat

@[simp] lemma doubleGlue_J (X : TopCat.{0}) (V : Opens X)
    (e : (V : Type) ≃ₜ (V : Type)) (he : ∀ x : (V : Type), e (e x) = x) :
    (doubleGlueData X V e he).J = Bool := rfl

@[simp] lemma doubleGlue_V00 (X : TopCat.{0}) (V : Opens X)
    (e : (V : Type) ≃ₜ (V : Type)) (he : ∀ x : (V : Type), e (e x) = x) :
    ((doubleGlueData X V e he).V (false,false) : TopCat) =
      (Opens.toTopCat X).obj (⊤ : Opens X) := rfl
@[simp] lemma doubleGlue_V01 (X : TopCat.{0}) (V : Opens X)
    (e : (V : Type) ≃ₜ (V : Type)) (he : ∀ x : (V : Type), e (e x) = x) :
    ((doubleGlueData X V e he).V (false,true) : TopCat) =
      (Opens.toTopCat X).obj V := rfl
@[simp] lemma doubleGlue_V10 (X : TopCat.{0}) (V : Opens X)
    (e : (V : Type) ≃ₜ (V : Type)) (he : ∀ x : (V : Type), e (e x) = x) :
    ((doubleGlueData X V e he).V (true,false) : TopCat) =
      (Opens.toTopCat X).obj V := rfl
@[simp] lemma doubleGlue_V11 (X : TopCat.{0}) (V : Opens X)
    (e : (V : Type) ≃ₜ (V : Type)) (he : ∀ x : (V : Type), e (e x) = x) :
    ((doubleGlueData X V e he).V (true,true) : TopCat) =
      (Opens.toTopCat X).obj (⊤ : Opens X) := rfl

/-- All the two chart images meet when the end is inhabited.  This is the
small point required by `gluedConnectedSpace`; none of separation is hidden in it. -/
lemma doubleGlue_meet (X : TopCat.{0}) (V : Opens X)
    (e : (V : Type) ≃ₜ (V : Type)) (he : ∀ x : (V : Type), e (e x) = x)
    (hv : Nonempty (V : Type)) :
    ∀ i j : (doubleGlueData X V e he).J,
      Nonempty ((doubleGlueData X V e he).V (i,j)) := by
  classical
  intro i j
  change Bool at i
  change Bool at j
  obtain ⟨v⟩ := hv
  cases i <;> cases j
  · exact ⟨⟨v.1, trivial⟩⟩
  · exact ⟨v⟩
  · exact ⟨v⟩
  · exact ⟨⟨v.1, trivial⟩⟩

end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/DoubleGlue.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/MiddleAvoid.lean
section
open scoped Topology RealInnerProductSpace Quaternion
open Topology Set Metric unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport

/-- A unit vector over the reals is not its own antipode.  The little
pointwise lemma is convenient when one of the paths used to compare loops is
constant. -/
lemma sphere_val_ne_neg_self
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : Metric.sphere (0:V) 1) : (x:V) ≠ -(x:V) := by
  intro h
  have hadd : (x:V) + (x:V) = 0 :=
    (eq_neg_iff_add_eq_zero).1 h
  have hsm : (2:ℝ) • (x:V) = 0 := by
    simpa [two_smul ℝ] using hadd
  have hx0 : (x:V) = 0 :=
    (smul_eq_zero.mp hsm).resolve_left (by norm_num : (2:ℝ) ≠ 0)
  have hxnorm : ‖(x:V)‖ = 1 := by
    have hx := x.property
    change dist (x:V) 0 = 1 at hx
    simpa [dist_zero_right] using hx
  have : (0:ℝ) = 1 := by simpa [hx0] using hxnorm
  norm_num at this

/-- Swapping the two ends of "not antipodal" is harmless.  This avoids
having to orient this condition every time the middle path is constant. -/
lemma ne_neg_swap
    {V : Type*} [AddCommGroup V]
    {x y : V} (h : x ≠ -y) : y ≠ -x := by
  intro hy
  apply h
  -- negate the putative equality
  have t := congrArg Neg.neg hy
  -- t : -y = - -x
  simpa using t.symm

/-- If a based loop in a real norm sphere misses the antipode of its base
point, no moving middle loop at all is necessary: the constant loop is in
radial position with it.  In later applications only loops which actually
hit the antipode contain any topology. -/
lemma sphere_loop_middle_of_avoid_base_antipode
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : Metric.sphere (0:V) 1)
    (a : Path w w)
    (ha : ∀ t : I, (a t : V) ≠ -(w:V)) :
    ∃ c : Path w w,
      (∀ t : I, (c t : V) ≠ -(a t : V)) ∧
      (∀ t : I, ((Path.refl w) t : V) ≠ -(c t : V)) := by
  refine ⟨Path.refl w, ?_, ?_⟩
  · intro t
    change (w:V) ≠ -(a t : V)
    exact ne_neg_swap (ha t)
  · intro t
    change (w:V) ≠ -(w:V)
    exact sphere_val_ne_neg_self w

/-- Thus the middle-loop test may be restricted to loops which actually hit
the antipodal point.  This formulation is a useful, and surprisingly easy to
miss, shrinking of the pointed simple-connectedness calculation. -/
lemma sphere_loop_middle_of_hitting_tests
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : Metric.sphere (0:V) 1)
    (H : ∀ (a : Path w w),
      (∃ t : I, (a t : V) = -(w:V)) →
      ∃ c : Path w w,
        (∀ t : I, (c t : V) ≠ -(a t : V)) ∧
        (∀ t : I, ((Path.refl w) t : V) ≠ -(c t : V))) :
    ∀ (a : Path w w),
      ∃ c : Path w w,
        (∀ t : I, (c t : V) ≠ -(a t : V)) ∧
        (∀ t : I, ((Path.refl w) t : V) ≠ -(c t : V)) := by
  intro a
  classical
  by_cases hit : ∃ t : I, (a t : V) = -(w:V)
  · exact H a hit
  · apply sphere_loop_middle_of_avoid_base_antipode w a
    intro t ht
    exact hit ⟨t, ht⟩

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open scoped Topology RealInnerProductSpace
open Topology Metric unitInterval
/-- The two ends of a based loop on a genuine unit sphere cannot be the
antipodal base point.  Thus every occurrence which remains after
`sphere_loop_middle_of_avoid_base_antipode` is in the *interior* of the
parameter interval.  Stating this with `I` instead of real inequalities
makes it handy when paths are later cut and pasted. -/
lemma sphere_loop_hit_antipode_ne_ends
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : Metric.sphere (0:V) 1)
    (a : Path w w) (t : I)
    (ht : (a t : V) = -(w:V)) :
    t ≠ (0 : I) ∧ t ≠ (1 : I) := by
  constructor
  · intro e
    subst t
    have hs := a.source
    have hs' : (a (0:I) : V) = (w:V) := congrArg Subtype.val hs
    have hn : (w:V) = -(w:V) := hs'.symm.trans ht
    exact sphere_val_ne_neg_self w hn
  · intro e
    subst t
    have hs := a.target
    have hs' : (a (1:I) : V) = (w:V) := congrArg Subtype.val hs
    have hn : (w:V) = -(w:V) := hs'.symm.trans ht
    exact sphere_val_ne_neg_self w hn
end NonlinearThreeManifoldSupport


namespace NonlinearThreeManifoldSupport
open scoped Topology RealInnerProductSpace
open Topology Set Metric unitInterval
/-- A first genuinely moving middle path.  If a loop lives in the kernel of a
continuous linear coordinate, move it a little in a transverse coordinate.
The bump `t*(1-t)` is nonzero at every interior time.  Applying the coordinate
to the unnormalised chord proves at once that the new point is neither the
antipode of the old path nor that of the base point.  This includes all loops
in a fixed proper coordinate great sphere, and isolates what is left for
loops using every coordinate direction. -/
lemma sphere_loop_middle_of_linear_kernel
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 (w : Metric.sphere (0:V) 1) (a : Path w w)
 (f : V →L[ℝ] ℝ) (v : V)
 (fw : f (w:V)=0) (fa : ∀ t : I, f (a t : V)=0)
 (fv : f v = 1) :
 ∃ c : Path w w,
      (∀ t : I, (c t : V) ≠ -(a t : V)) ∧
      (∀ t : I, ((Path.refl w) t : V) ≠ -(c t : V)) := by
 let bump : I → ℝ := fun t => (t:ℝ) * (1 - (t:ℝ))
 have bumpcont : Continuous bump := by dsimp [bump]; fun_prop
 have bumpne (t:I) (h0 : t ≠ (0:I)) (h1 : t ≠ (1:I)) : bump t ≠ 0 := by
   dsimp [bump]
   have hp0 : (t:ℝ) ≠ 0 := by
     intro e
     apply h0
     apply Subtype.ext
     simpa using e
   have hp1 : (1 - (t:ℝ)) ≠ 0 := by
     intro e
     have te : (t:ℝ) = 1 := by linarith
     apply h1
     apply Subtype.ext
     simpa using te
   exact mul_ne_zero hp0 hp1
 let raw : I → V := fun t => (w:V) + (1/2:ℝ) • (a t : V) + (bump t) • v
 have rawc : Continuous raw := by dsimp [raw]; fun_prop
 have fraw (t:I) : f (raw t) = bump t := by
   dsimp [raw]
   simp [map_add, map_smul, fw, fa, fv]
 have raw_ne (t:I) : raw t ≠ 0 := by
   classical
   by_cases h0 : t = (0:I)
   · subst t
     have wne : (w:V) ≠ 0 := by
       intro h
       have hnorm : ‖(w:V)‖ = 1 := by
         have h' := w.property
         change dist (w:V) 0 = 1 at h'
         simpa [dist_zero_right] using h'
       have : (0:ℝ)=1 := by simpa [h] using hnorm
       norm_num at this
     dsimp [raw, bump]
     have asrc : (a (0:I) : V) = (w:V) := congrArg Subtype.val a.source
     rw [asrc]
     intro hz
     have : ((3/2:ℝ) • (w:V)) = 0 := by
       convert hz using 1 <;> module
     exact wne ((smul_eq_zero.mp this).resolve_left (by norm_num : (3/2:ℝ) ≠ 0))
   · by_cases h1 : t = (1:I)
     · subst t
       have wne : (w:V) ≠ 0 := by
         intro h
         have hnorm : ‖(w:V)‖ = 1 := by
           have h' := w.property
           change dist (w:V) 0 = 1 at h'
           simpa [dist_zero_right] using h'
         have : (0:ℝ)=1 := by simpa [h] using hnorm
         norm_num at this
       dsimp [raw, bump]
       have asrc : (a (1:I) : V) = (w:V) := congrArg Subtype.val a.target
       rw [asrc]
       intro hz
       have : ((3/2:ℝ) • (w:V)) = 0 := by
         convert hz using 1 <;> module
       exact wne ((smul_eq_zero.mp this).resolve_left (by norm_num : (3/2:ℝ) ≠ 0))
     · intro hz
       have e : bump t = 0 := by rw [← fraw t, hz]; simp
       exact bumpne t h0 h1 e
 have norm_ne (t:I) : ‖raw t‖ ≠ 0 := norm_ne_zero_iff.mpr (raw_ne t)
 let toS : I → Metric.sphere (0:V) 1 := fun t => sphereNormalize (raw t) (raw_ne t)
 have toSc : Continuous toS := by
   apply continuous_induced_rng.2
   change Continuous (fun t : I => (sphereNormalize (raw t) (raw_ne t) : V))
   change Continuous (fun t : I => (‖raw t‖)⁻¹ • raw t)
   have hn : Continuous (fun t : I => ‖raw t‖) := continuous_norm.comp rawc
   have hi : Continuous (fun t : I => (‖raw t‖)⁻¹) := by
     fun_prop (disch := aesop)
   fun_prop
 have end0 : toS 0 = w := by
   apply Subtype.ext
   change (‖raw 0‖)⁻¹ • raw 0 = (w:V)
   have ar : raw 0 = (3/2:ℝ) • (w:V) := by
     dsimp [raw, bump]
     have asrc : (a (0:I) : V) = (w:V) := congrArg Subtype.val a.source
     rw [asrc]
     module
   rw [ar, norm_smul]
   have nw : ‖(w:V)‖ = 1 := by
     have h' := w.property
     change dist (w:V) 0 = 1 at h'
     simpa [dist_zero_right] using h'
   rw [nw]
   norm_num
   rw [smul_smul]
   norm_num
 have end1 : toS 1 = w := by
   apply Subtype.ext
   change (‖raw 1‖)⁻¹ • raw 1 = (w:V)
   have ar : raw 1 = (3/2:ℝ) • (w:V) := by
     dsimp [raw, bump]
     have asrc : (a (1:I) : V) = (w:V) := congrArg Subtype.val a.target
     rw [asrc]
     module
   rw [ar, norm_smul]
   have nw : ‖(w:V)‖ = 1 := by
     have h' := w.property
     change dist (w:V) 0 = 1 at h'
     simpa [dist_zero_right] using h'
   rw [nw]
   norm_num
   rw [smul_smul]
   norm_num
 let c : Path w w := ⟨⟨toS, toSc⟩, end0, end1⟩
 refine ⟨c, ?_, ?_⟩
 · intro t eqn
   by_cases h0 : t = (0:I)
   · subst t
     have av : (a (0:I):V) = (w:V) := congrArg Subtype.val a.source
     change (toS 0 : V) = -(a (0:I) : V) at eqn
     have cv : (toS 0:V) = (w:V) := congrArg Subtype.val end0
     rw [cv, av] at eqn
     exact sphere_val_ne_neg_self w eqn
   · by_cases h1 : t = (1:I)
     · subst t
       have av : (a (1:I):V) = (w:V) := congrArg Subtype.val a.target
       change (toS 1 : V) = -(a (1:I) : V) at eqn
       have cv : (toS 1:V) = (w:V) := congrArg Subtype.val end1
       rw [cv, av] at eqn
       exact sphere_val_ne_neg_self w eqn
     · change (toS t : V) = -(a t : V) at eqn
       have frc : f (toS t : V) = (‖raw t‖)⁻¹ * bump t := by
         change f ((‖raw t‖)⁻¹ • raw t) = _
         rw [f.map_smul, fraw]
         simp
       have far : f (-(a t : V)) = 0 := by simp [fa]
       have prod : (‖raw t‖)⁻¹ * bump t = 0 := by
         rw [← frc, eqn, far]
       exact (mul_ne_zero (inv_ne_zero (norm_ne t)) (bumpne t h0 h1)) prod
 · intro t eqn
   change (w:V) = -(c t : V) at eqn
   by_cases h0 : t = (0:I)
   · subst t
     have cv : (c (0:I):V) = (w:V) := congrArg Subtype.val end0
     rw [cv] at eqn
     exact sphere_val_ne_neg_self w eqn
   · by_cases h1 : t = (1:I)
     · subst t
       have cv : (c (1:I):V) = (w:V) := congrArg Subtype.val end1
       rw [cv] at eqn
       exact sphere_val_ne_neg_self w eqn
     · have fec : f (c t : V) = (‖raw t‖)⁻¹ * bump t := by
         change f ((‖raw t‖)⁻¹ • raw t) = _
         rw [f.map_smul, fraw]
         simp
       have feq : f (-(c t : V)) = - ((‖raw t‖)⁻¹ * bump t) := by rw [map_neg, fec]
       have fwe := congrArg f eqn
       rw [feq, fw] at fwe
       have z : (‖raw t‖)⁻¹ * bump t = 0 := by linarith
       exact (mul_ne_zero (inv_ne_zero (norm_ne t)) (bumpne t h0 h1)) z

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open scoped Topology RealInnerProductSpace
open Topology Metric unitInterval
/-- A nonzero real coordinate can always be rescaled to take value one. -/
lemma continuousLinearMap_has_one_of_ne_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V →L[ℝ] ℝ) (hf : f ≠ 0) : ∃ v : V, f v = 1 := by
  classical
  have nz : ∃ u : V, f u ≠ 0 := by
    by_contra all
    push_neg at all
    have eq : f = (0 : V →L[ℝ] ℝ) := by
      ext u
      simpa using all u
    exact hf eq
  rcases nz with ⟨u, hu⟩
  refine ⟨(f u)⁻¹ • u, ?_⟩
  rw [f.map_smul]
  -- scalar multiplication in the target field is multiplication
  exact inv_mul_cancel₀ hu

/-- Kernel version without the choice of a named transverse vector. The
existential vector in `sphere_loop_middle_of_linear_kernel` costs nothing for
a nonzero real functional. -/
lemma sphere_loop_middle_of_nonzero_kernel
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : Metric.sphere (0:V) 1) (a : Path w w)
    (f : V →L[ℝ] ℝ) (hf : f ≠ 0)
    (fw : f (w:V)=0) (fa : ∀ t : I, f (a t : V)=0) :
    ∃ c : Path w w,
      (∀ t : I, (c t : V) ≠ -(a t : V)) ∧
      (∀ t : I, ((Path.refl w) t : V) ≠ -(c t : V)) := by
  obtain ⟨v,hv⟩ := continuousLinearMap_has_one_of_ne_zero f hf
  exact sphere_loop_middle_of_linear_kernel w a f v fw fa hv
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/MiddleAvoid.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckBoundary.lean
section

open scoped Topology
open Set Metric Topology unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport

/-- A ball is enough for comparing based paths; writing the homotopy
explicitly is useful when a small spherical boundary is subsequently included
in a manifold chart. -/
lemma ball_paths_homotopic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) {x y : (Metric.ball (0:E) R : Set E)}
    (p q : Path x y) : Path.Homotopic p q := by
  let raw : I × I → E := fun st =>
    (1 - (st.1 : ℝ)) • (p st.2 : E) + (st.1 : ℝ) • (q st.2 : E)
  have mem (st : I × I) : raw st ∈ Metric.ball (0:E) R := by
    have ht : (st.1 : ℝ) ∈ Set.Icc (0:ℝ) 1 := st.1.property
    have hm := (convex_ball (0:E) R).lineMap_mem
      (show (p st.2 : E) ∈ Metric.ball (0:E) R from (p st.2).property)
      (show (q st.2 : E) ∈ Metric.ball (0:E) R from (q st.2).property)
      ht
    -- `lineMap` is the same convex combination.
    simpa [raw, AffineMap.lineMap_apply, sub_smul, one_smul,
      vsub_eq_sub, add_comm, add_left_comm, add_assoc,
      sub_eq_add_neg, add_smul] using hm
  let F : I × I → (Metric.ball (0:E) R : Set E) :=
    fun st => ⟨raw st, mem st⟩
  have Fc : Continuous F := by
    apply continuous_induced_rng.2
    change Continuous raw
    dsimp [raw]
    fun_prop
  refine ⟨({ toFun := F
             continuous_toFun := Fc
             map_zero_left := ?_
             map_one_left := ?_
             prop' := ?_ } : p.Homotopy q)⟩
  · intro t
    apply Subtype.ext
    change (1 - (0:ℝ)) • (p t : E) + (0:ℝ) • (q t : E) = (p t : E)
    simp
  · intro t
    apply Subtype.ext
    change (1 - (1:ℝ)) • (p t : E) + (1:ℝ) • (q t : E) = (q t : E)
    simp
  · intro u t ht
    have ep : p t = q t := by
      rcases ht with ht | ht
      · change t = (0:I) at ht
        subst t
        exact p.source.trans q.source.symm
      · have ht' : t = (1:I) := by simpa using ht
        subst t
        exact p.target.trans q.target.symm
    apply Subtype.ext
    change (1 - (u:ℝ)) • (p t : E) + (u:ℝ) • (q t : E) = (p t : E)
    have ev : (q t : E) = (p t : E) := congrArg Subtype.val ep.symm
    rw [ev, ← add_smul]
    have hh : (1 - (u:ℝ)) + (u:ℝ) = (1:ℝ) := by ring
    rw [hh, one_smul]

section chartBoundary
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

/-- The inverse of a pointed chart on the little ball chosen by `ChartBall`.
All coordinates here are translated so that the marked point is zero. -/
noncomputable def chartBallMap (b : Y) (A : ChartBall (E:=E) b) :
    C((Metric.ball (0:E) A.R : Set E), Y) := by
  let φ := chartAt E b
  let v : (Metric.ball (0:E) A.R : Set E) → (φ.target : Set E) := fun z => by
    refine ⟨φ b + (z:E), ?_⟩
    apply A.sub
    change dist ((chartAt E b) b + (z:E)) ((chartAt E b) b) < A.R
    rw [dist_eq_norm]
    have hvec : (chartAt E b) b + (z:E) - (chartAt E b) b = (z:E) := by abel
    rw [hvec]
    have h := z.property
    exact (mem_ball_zero_iff.mp h)
  have vc : Continuous v := by
    apply continuous_induced_rng.2
    change Continuous (fun z : (Metric.ball (0:E) A.R : Set E) =>
      (chartAt E b) b + (z:E))
    fun_prop
  exact ⟨(fun z => φ.symm (v z : E)),
    ((φ.symm.continuousOn.restrict).comp vc)⟩

@[simp] lemma chartBallMap_apply (b : Y) (A : ChartBall (E:=E) b)
    (z : (Metric.ball (0:E) A.R : Set E)) :
    chartBallMap (E:=E) b A z =
      (chartAt E b).symm ((chartAt E b) b + (z:E)) := rfl

/-- A positive (strictly smaller) spherical cross section of the open end,
in the original block rather than in the punctured subtype. -/
noncomputable def chartSmallSphere (b : Y) (A : ChartBall (E:=E) b)
    (r : ℝ) (hr : r < A.R) : C((Metric.sphere (0:E) r : Set E), Y) := by
  let inc : (Metric.sphere (0:E) r : Set E) →
      (Metric.ball (0:E) A.R : Set E) := fun z => by
        refine ⟨(z:E), ?_⟩
        have nz : ‖(z:E)‖ = r := by
          have t := z.property
          simpa [dist_zero_right] using t
        have : dist (z:E) (0:E) = r := z.property
        simpa [this] using hr
  have ic : Continuous inc := by
    apply continuous_induced_rng.2
    fun_prop
  exact (chartBallMap (E:=E) b A).comp ⟨inc, ic⟩

@[simp] lemma chartSmallSphere_apply (b : Y) (A : ChartBall (E:=E) b)
    (r : ℝ) (hr : r < A.R) (z : (Metric.sphere (0:E) r : Set E)) :
    chartSmallSphere (E:=E) b A r hr z =
      (chartAt E b).symm ((chartAt E b) b + (z:E)) := rfl

/-- Every path comparison on the little boundary becomes trivial in the
block. This is the exact based fact one uses when filling a deleted ball in a
pinch map. Notice that it asks for no calculation of the fundamental group of
`Y`; both representatives stay in the chosen chart ball. -/
lemma chartSmallSphere_paths
    (b : Y) (A : ChartBall (E:=E) b)
    (r : ℝ) (hr : r < A.R)
    {z : (Metric.sphere (0:E) r : Set E)} (L : Path z z) :
    Path.Homotopic
      (L.map (chartSmallSphere (E:=E) b A r hr).continuous)
      (Path.refl (chartSmallSphere (E:=E) b A r hr z)) := by
  let inc : (Metric.sphere (0:E) r : Set E) →
      (Metric.ball (0:E) A.R : Set E) := fun t => by
        refine ⟨(t:E), ?_⟩
        have tt : dist (t:E) (0:E) = r := t.property
        simpa [tt] using hr
  have ic : Continuous inc := by
    apply continuous_induced_rng.2
    fun_prop
  let inz : (Metric.ball (0:E) A.R : Set E) := inc z
  let LL : Path inz inz := L.map ic
  let RR : Path inz inz := Path.refl inz
  have H : Path.Homotopic LL RR := ball_paths_homotopic A.R LL RR
  have HH := H.map (chartBallMap (E:=E) b A)
  -- mapping after inclusion is precisely the displayed boundary map
  -- and mapping a constant path stays constant. Path extensionality avoids
  -- any transports of endpoints.
  have left : LL.map (chartBallMap (E:=E) b A).continuous =
      L.map (chartSmallSphere (E:=E) b A r hr).continuous := by
    apply Path.ext
    rfl
  have right : RR.map (chartBallMap (E:=E) b A).continuous =
      Path.refl (chartSmallSphere (E:=E) b A r hr z) := by
    apply Path.ext
    rfl
  exact left ▸ right ▸ HH

/-- Formulation in the fundamental group: the small chart boundary has zero
map on based loops when it is viewed in the whole block. -/
lemma chartSmallSphere_piOne_zero
    (b : Y) (A : ChartBall (E:=E) b)
    (r : ℝ) (hr : r < A.R)
    (z : (Metric.sphere (0:E) r : Set E))
    (a : FundamentalGroup (Metric.sphere (0:E) r : Set E) z) :
    FundamentalGroup.map (chartSmallSphere (E:=E) b A r hr) z a =
      (1 : FundamentalGroup Y
        (chartSmallSphere (E:=E) b A r hr z)) := by
  change Path.Homotopic.Quotient z z at a
  induction a using Quotient.inductionOn with
  | _ L =>
    change Path.Homotopic.Quotient.mk _ = _
    change Path.Homotopic.Quotient.mk _ =
      Path.Homotopic.Quotient.mk (Path.refl
        (chartSmallSphere (E:=E) b A r hr z))
    exact Quotient.sound (chartSmallSphere_paths (E:=E) b A r hr L)

end chartBoundary
end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open Set Metric Topology unitInterval
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

/-- The same boundary, now landing in the open punctured patch. This records
which boundary subgroup occurs on the two sides of `doubleGlueData`. -/
noncomputable def chartEndSmallSphere (b : Y) (A : ChartBall (E:=E) b)
    (r : ℝ) (hr0 : 0 < r) (hr : r < A.R) :
    C((Metric.sphere (0:E) r : Set E),
      (({b}:Set Y)ᶜ : Set Y)) := by
  let u : (Metric.sphere (0:E) r : Set E) →
      (radialSet (E:=E) A.R : Set E) := fun z => by
        refine ⟨(z:E), ?_, ?_⟩
        · intro zz
          have hz : ‖(z:E)‖ = r := by
            simpa [dist_zero_right] using z.property
          rw [zz, norm_zero] at hz
          linarith
        · have hz : ‖(z:E)‖ = r := by
            simpa [dist_zero_right] using z.property
          rw [hz]
          exact hr
  have uc : Continuous u := by
    apply continuous_induced_rng.2
    fun_prop
  let fend : C((radialSet (E:=E) A.R : Set E),
      (chartEnd (E:=E) b A : Type _)) :=
    ⟨(chartEndHomeo (E:=E) b A).symm, (chartEndHomeo (E:=E) b A).symm.continuous⟩
  let drop : C((chartEnd (E:=E) b A : Type _),
        (({b}:Set Y)ᶜ : Set Y)) :=
    { toFun := fun t => t.1
      continuous_toFun := by fun_prop }
  exact drop.comp (fend.comp ⟨u, uc⟩)

/-- Coercing the punctured boundary back to the block is definitionally the
inverse chart on the translated coordinates. -/
lemma chartEndSmallSphere_val (b : Y) (A : ChartBall (E:=E) b)
    (r : ℝ) (hr0 : 0 < r) (hr : r < A.R)
    (z : (Metric.sphere (0:E) r : Set E)) :
    ((chartEndSmallSphere (E:=E) b A r hr0 hr z :
        (({b}:Set Y)ᶜ : Set Y)) : Y) =
      chartSmallSphere (E:=E) b A r hr z := by
  dsimp [chartEndSmallSphere, chartSmallSphere, chartBallMap]
  rfl

/-- Hence the boundary loop in the *punctured* patch dies as soon as it is
included into the whole block. This is often the local input in the neck
(or equivalently in a based pinch calculation). -/
lemma chartEndSmallSphere_piOne_in_block
    (b : Y) (A : ChartBall (E:=E) b)
    (r : ℝ) (hr0 : 0 < r) (hr : r < A.R)
    (z : (Metric.sphere (0:E) r : Set E))
    (a : FundamentalGroup (Metric.sphere (0:E) r : Set E) z) :
    let incl : C((({b}:Set Y)ᶜ : Set Y), Y) :=
       { toFun := fun y => (y:Y), continuous_toFun := continuous_subtype_val }
    let h : C((Metric.sphere (0:E) r : Set E), Y) :=
       incl.comp (chartEndSmallSphere (E:=E) b A r hr0 hr)
    FundamentalGroup.map h z a =
      (1 : FundamentalGroup Y (h z)) := by
  let incl : C((({b}:Set Y)ᶜ : Set Y), Y) :=
       { toFun := fun y => (y:Y), continuous_toFun := continuous_subtype_val }
  let h : C((Metric.sphere (0:E) r : Set E), Y) :=
       incl.comp (chartEndSmallSphere (E:=E) b A r hr0 hr)
  have eqmap : h = chartSmallSphere (E:=E) b A r hr := by
    ext t
    exact chartEndSmallSphere_val (E:=E) b A r hr0 hr t
  change FundamentalGroup.map h z a = (1 : FundamentalGroup Y (h z))
  subst h
  exact chartSmallSphere_piOne_zero (E:=E) b A r hr z a

end
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
open Set Metric Topology unitInterval
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

/-- Inclusion of the whole punctured chart end in the block. Working on the
open subtype (rather than just a chosen sphere) is handy for the overlap of
two punctured charts: every based loop in this overlap already dies in the
uncut block. -/
noncomputable def chartEndInBlock (b : Y) (A : ChartBall (E:=E) b) :
    C((chartEnd (E:=E) b A : Type _), Y) :=
  { toFun := fun z => (z.1.1 : Y)
    continuous_toFun := by fun_prop }

/-- Forget that a punctured-ball coordinate is nonzero. -/
noncomputable def chartEndToBall (b : Y) (A : ChartBall (E:=E) b) :
    C((chartEnd (E:=E) b A : Type _),
      (Metric.ball (0:E) A.R : Set E)) := by
  let forget : (radialSet (E:=E) A.R : Set E) →
      (Metric.ball (0:E) A.R : Set E) := fun z => by
        refine ⟨(z:E), ?_⟩
        exact mem_ball_zero_iff.mpr z.property.2
  have fc : Continuous forget := by
    apply continuous_induced_rng.2
    fun_prop
  exact ⟨forget ∘ (chartEndHomeo (E:=E) b A), fc.comp
      (chartEndHomeo (E:=E) b A).continuous⟩

lemma chartEndToBall_inv (b : Y) (A : ChartBall (E:=E) b)
    (z : (chartEnd (E:=E) b A : Type _)) :
    chartBallMap (E:=E) b A (chartEndToBall (E:=E) b A z) =
      chartEndInBlock (E:=E) b A z := by
  -- on the chart source inverse and direct coordinates cancel
  change (chartAt E b).symm
     ((chartAt E b) b +
       ((chartAt E b) (z.1.1) - (chartAt E b) b)) = z.1.1
  have hv : (chartAt E b) b +
       ((chartAt E b) (z.1.1) - (chartAt E b) b) =
       (chartAt E b) (z.1.1) := by abel
  rw [hv]
  exact (chartAt E b).left_inv z.property.1

-- Passing all the way from this open end to based concatenations uses an
-- endpoint cast. The spherical cross-section above is the formulation used
-- for the pinch.
end
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckBoundary.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/SphericalQ.lean
section

open scoped RealInnerProductSpace Quaternion Topology
open Set Metric
noncomputable section
namespace NonlinearThreeManifoldSupport

/-- The universal sphere in the quaternions.  Keeping quaternion coordinates (rather
than matrices in `Fin 4`) makes the left multiplication action literal. -/
abbrev qSphere : Type := Metric.sphere (0 : Quaternion ℝ) 1

private lemma __SphericalQ_qfinrank : Module.finrank ℝ (Quaternion ℝ) = 3 + 1 := by
  simpa using (Quaternion.finrank_eq_four (R := ℝ))

noncomputable instance qSphereCharted :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) qSphere := by
  letI : Fact (Module.finrank ℝ (Quaternion ℝ) = 3 + 1) := ⟨__SphericalQ_qfinrank⟩
  exact EuclideanSpace.instChartedSpaceSphere

private lemma __SphericalQ_qrank : 1 < Module.rank ℝ (Quaternion ℝ) := by
  rw [← Module.finrank_eq_rank, Quaternion.finrank_eq_four]
  exact_mod_cast (by decide : (1:ℕ) < 4)

noncomputable instance : ConnectedSpace qSphere := by
  let h := isPathConnected_sphere __SphericalQ_qrank (0 : Quaternion ℝ) (by norm_num : (0:ℝ) ≤ 1)
  exact Subtype.connectedSpace h.isConnected

noncomputable instance : PathConnectedSpace qSphere := by
  let h := isPathConnected_sphere __SphericalQ_qrank (0 : Quaternion ℝ) (by norm_num : (0:ℝ) ≤ 1)
  exact (isPathConnected_iff_pathConnectedSpace).1 h

-- the remaining compact/Hausdorff/second-countable structures are inherited from the
-- normed four-space.
example : T2Space qSphere := inferInstance
example : CompactSpace qSphere := inferInstance
example : SecondCountableTopology qSphere := inferInstance
example : LocallyCompactSpace qSphere := inferInstance

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open scoped Quaternion

/-- Once a finite free action on the quaternionic sphere has been supplied, the quotient has
all the elementary pieces of a closed three manifold.  This is the handy packaging in the
problem's *topological*, not smooth, convention of `ChartedSpace`.  No assertion about π₁ is
hidden in this definition. -/
abbrev qOrbit (G : Type*) [Group G] [MulAction G qSphere] :=
    Quotient (MulAction.orbitRel G qSphere)

section Orbit
variable (G : Type*) [Group G] [MulAction G qSphere]
variable [ContinuousConstSMul G qSphere] [Finite G] [IsCancelSMul G qSphere]

noncomputable instance qOrbitCharted :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) (qOrbit G) :=
  ChartedSpace.orbitFinite (EuclideanSpace ℝ (Fin 3)) qSphere G

noncomputable instance qOrbitConnected : ConnectedSpace (qOrbit G) := by
  let f : qSphere → qOrbit G := Quotient.mk _
  have hf : Continuous f :=
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (E := qSphere) (G := G)).continuous
  exact Function.Surjective.connectedSpace Quotient.mk_surjective hf

noncomputable instance qOrbitPathConnected : PathConnectedSpace (qOrbit G) := by
  let f : qSphere → qOrbit G := Quotient.mk _
  have hf : Continuous f :=
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (E := qSphere) (G := G)).continuous
  exact Function.Surjective.pathConnectedSpace Quotient.mk_surjective hf

example : CompactSpace (qOrbit G) := inferInstance
example : T2Space (qOrbit G) := inferInstance
example : SecondCountableTopology (qOrbit G) := ContinuousConstSMul.secondCountableTopology

/-- The quotient projection in this package is an honest covering map. -/
lemma qOrbitIsCovering : IsCoveringMap (Quotient.mk
    (MulAction.orbitRel G qSphere) : qSphere → qOrbit G) :=
  (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    (E := qSphere) (G := G)).isCoveringMap

end Orbit
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/SphericalQ.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/HemisphereAvoid.lean
section
open scoped Topology RealInnerProductSpace Quaternion
open Topology Set Metric unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport
/-- Variant of the moving middle path for a closed hemisphere.  It is not
necessary that the old loop be in a coordinate equator.  If a transverse
coordinate, vanishing on the base point, is non-negative on the loop, the
same `t(1-t)` bump as in `sphere_loop_middle_of_linear_kernel` is *strictly*
positive in that coordinate in the interior.  Its antipodal point has the
opposite sign. -/
lemma sphere_loop_middle_of_linear_halfspace
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 (w : Metric.sphere (0 : V) 1) (a : Path w w)
 (f : V →L[ℝ] ℝ) (v : V)
 (fw : f (w : V) = 0) (fa : ∀ t : I, 0 ≤ f (a t : V))
 (fv : f v = 1) :
 ∃ c : Path w w,
      (∀ t : I, (c t : V) ≠ -(a t : V)) ∧
      (∀ t : I, ((Path.refl w) t : V) ≠ -(c t : V)) := by
 let bump : I → ℝ := fun t => (t:ℝ) * (1 - (t:ℝ))
 have bumpcont : Continuous bump := by dsimp [bump]; fun_prop
 have bumppos (t:I) (h0 : t ≠ (0:I)) (h1 : t ≠ (1:I)) : 0 < bump t := by
   dsimp [bump]
   have hp0le : 0 ≤ (t:ℝ) := t.property.1
   have hp0 : (t:ℝ) ≠ 0 := by
     intro e
     apply h0
     apply Subtype.ext
     simpa using e
   have hp0' : 0 < (t:ℝ) := lt_of_le_of_ne hp0le (Ne.symm hp0)
   have hp1le : (t:ℝ) ≤ 1 := t.property.2
   have hp1 : (t:ℝ) ≠ 1 := by
     intro e
     apply h1
     apply Subtype.ext
     simpa using e
   have hp1' : (t:ℝ) < 1 := lt_of_le_of_ne hp1le hp1
   exact mul_pos hp0' (sub_pos.mpr hp1')
 let raw : I → V := fun t => (w:V) + (1/2:ℝ) • (a t : V) + (bump t) • v
 have rawc : Continuous raw := by dsimp [raw]; fun_prop
 have fraw (t:I) : f (raw t) = (1/2:ℝ) * f (a t : V) + bump t := by
   dsimp [raw]
   simp [map_add, map_smul, fw, fv]
 have fraw_pos (t:I) (h0:t ≠ (0:I)) (h1:t ≠ (1:I)) : 0 < f (raw t) := by
   rw [fraw]
   have hn : 0 ≤ f (a t : V) := fa t
   have hb : 0 < bump t := bumppos t h0 h1
   positivity
 have raw_ne (t:I) : raw t ≠ 0 := by
   classical
   by_cases h0 : t = (0:I)
   · subst t
     have wne : (w:V) ≠ 0 := by
       intro h
       have hnorm : ‖(w:V)‖ = 1 := by
         have h' := w.property
         change dist (w:V) 0 = 1 at h'
         simpa [dist_zero_right] using h'
       have : (0:ℝ)=1 := by simpa [h] using hnorm
       norm_num at this
     dsimp [raw, bump]
     have asrc : (a (0:I) : V) = (w:V) := congrArg Subtype.val a.source
     rw [asrc]
     intro hz
     have : ((3/2:ℝ) • (w:V)) = 0 := by
       convert hz using 1 <;> module
     exact wne ((smul_eq_zero.mp this).resolve_left (by norm_num : (3/2:ℝ) ≠ 0))
   · by_cases h1 : t = (1:I)
     · subst t
       have wne : (w:V) ≠ 0 := by
         intro h
         have hnorm : ‖(w:V)‖ = 1 := by
           have h' := w.property
           change dist (w:V) 0 = 1 at h'
           simpa [dist_zero_right] using h'
         have : (0:ℝ)=1 := by simpa [h] using hnorm
         norm_num at this
       dsimp [raw, bump]
       have asrc : (a (1:I) : V) = (w:V) := congrArg Subtype.val a.target
       rw [asrc]
       intro hz
       have : ((3/2:ℝ) • (w:V)) = 0 := by
         convert hz using 1 <;> module
       exact wne ((smul_eq_zero.mp this).resolve_left (by norm_num : (3/2:ℝ) ≠ 0))
     · intro hz
       have pos := fraw_pos t h0 h1
       have e : f (raw t) = 0 := by rw [hz]; simp
       linarith
 have norm_ne (t:I) : ‖raw t‖ ≠ 0 := norm_ne_zero_iff.mpr (raw_ne t)
 let toS : I → Metric.sphere (0:V) 1 := fun t => sphereNormalize (raw t) (raw_ne t)
 have toSc : Continuous toS := by
   apply continuous_induced_rng.2
   change Continuous (fun t : I => (sphereNormalize (raw t) (raw_ne t) : V))
   change Continuous (fun t : I => (‖raw t‖)⁻¹ • raw t)
   have hn : Continuous (fun t : I => ‖raw t‖) := continuous_norm.comp rawc
   have hi : Continuous (fun t : I => (‖raw t‖)⁻¹) := by
     fun_prop (disch := aesop)
   fun_prop
 have end0 : toS 0 = w := by
   apply Subtype.ext
   change (‖raw 0‖)⁻¹ • raw 0 = (w:V)
   have ar : raw 0 = (3/2:ℝ) • (w:V) := by
     dsimp [raw, bump]
     have asrc : (a (0:I) : V) = (w:V) := congrArg Subtype.val a.source
     rw [asrc]
     module
   rw [ar, norm_smul]
   have nw : ‖(w:V)‖ = 1 := by
     have h' := w.property
     change dist (w:V) 0 = 1 at h'
     simpa [dist_zero_right] using h'
   rw [nw]
   norm_num
   rw [smul_smul]
   norm_num
 have end1 : toS 1 = w := by
   apply Subtype.ext
   change (‖raw 1‖)⁻¹ • raw 1 = (w:V)
   have ar : raw 1 = (3/2:ℝ) • (w:V) := by
     dsimp [raw, bump]
     have asrc : (a (1:I) : V) = (w:V) := congrArg Subtype.val a.target
     rw [asrc]
     module
   rw [ar, norm_smul]
   have nw : ‖(w:V)‖ = 1 := by
     have h' := w.property
     change dist (w:V) 0 = 1 at h'
     simpa [dist_zero_right] using h'
   rw [nw]
   norm_num
   rw [smul_smul]
   norm_num
 let c : Path w w := ⟨⟨toS, toSc⟩, end0, end1⟩
 refine ⟨c, ?_, ?_⟩
 · intro t eqn
   by_cases h0 : t = (0:I)
   · subst t
     have av : (a (0:I):V) = (w:V) := congrArg Subtype.val a.source
     change (toS 0 : V) = -(a (0:I) : V) at eqn
     have cv : (toS 0:V) = (w:V) := congrArg Subtype.val end0
     rw [cv, av] at eqn
     exact sphere_val_ne_neg_self w eqn
   · by_cases h1 : t = (1:I)
     · subst t
       have av : (a (1:I):V) = (w:V) := congrArg Subtype.val a.target
       change (toS 1 : V) = -(a (1:I) : V) at eqn
       have cv : (toS 1:V) = (w:V) := congrArg Subtype.val end1
       rw [cv, av] at eqn
       exact sphere_val_ne_neg_self w eqn
     · change (toS t : V) = -(a t : V) at eqn
       have frc : f (toS t : V) = (‖raw t‖)⁻¹ * f (raw t) := by
         change f ((‖raw t‖)⁻¹ • raw t) = _
         rw [f.map_smul]
         simp
       have posinv : 0 < (‖raw t‖)⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (raw_ne t))
       have fpos : 0 < f (toS t : V) := by
         rw [frc]
         exact mul_pos posinv (fraw_pos t h0 h1)
       have farle : f (-(a t : V)) ≤ 0 := by
         rw [map_neg]
         exact neg_nonpos.mpr (fa t)
       have feq := congrArg f eqn
       have zle : f (toS t : V) ≤ 0 := by
         calc
           f (toS t : V) = f (-(a t : V)) := feq
           _ ≤ 0 := farle
       exact (not_lt_of_ge zle) fpos
 · intro t eqn
   change (w:V) = -(c t : V) at eqn
   by_cases h0 : t = (0:I)
   · subst t
     have cv : (c (0:I):V) = (w:V) := congrArg Subtype.val end0
     rw [cv] at eqn
     exact sphere_val_ne_neg_self w eqn
   · by_cases h1 : t = (1:I)
     · subst t
       have cv : (c (1:I):V) = (w:V) := congrArg Subtype.val end1
       rw [cv] at eqn
       exact sphere_val_ne_neg_self w eqn
     · have frc : f (toS t : V) = (‖raw t‖)⁻¹ * f (raw t) := by
         change f ((‖raw t‖)⁻¹ • raw t) = _
         rw [f.map_smul]
         simp
       have fpos : 0 < f (c t : V) := by
         change 0 < f (toS t : V)
         rw [frc]
         exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (raw_ne t)))
           (fraw_pos t h0 h1)
       have feq := congrArg f eqn
       have fneg : f (-(c t : V)) < 0 := by
         rw [map_neg]
         exact neg_neg_of_pos fpos
       rw [fw] at feq
       -- the equality asserts that this negative number is zero
       have terrible : (0:ℝ) < 0 := by
         -- `feq : 0 = f (-c)` after using the value of the base point.
         simpa [← feq] using fneg
       exact lt_irrefl 0 terrible

/-- A nonzero transverse coordinate puts a loop living in either closed
hemisphere into the previous construction.  Stating the disjunction here is
useful when cutting down the genuinely oscillating loops. -/
lemma sphere_loop_middle_of_nonzero_halfspace
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 (w : Metric.sphere (0 : V) 1) (a : Path w w)
 (f : V →L[ℝ] ℝ) (hf : f ≠ 0)
 (fw : f (w : V) = 0)
 (fa : (∀ t : I, 0 ≤ f (a t : V)) ∨ (∀ t : I, f (a t : V) ≤ 0)) :
 ∃ c : Path w w,
      (∀ t : I, (c t : V) ≠ -(a t : V)) ∧
      (∀ t : I, ((Path.refl w) t : V) ≠ -(c t : V)) := by
 cases fa with
 | inl hp =>
   obtain ⟨v,hv⟩ := continuousLinearMap_has_one_of_ne_zero f hf
   exact sphere_loop_middle_of_linear_halfspace w a f v fw hp hv
 | inr hn =>
   -- turn the negative hemisphere over
   let f' : V →L[ℝ] ℝ := - f
   have ff' : f' ≠ 0 := by
     intro h
     apply hf
     have z : - f' = 0 := by simp [h]
     simpa [f'] using z
   have fw' : f' (w:V) = 0 := by simp [f', fw]
   have fa' : ∀ t : I, 0 ≤ f' (a t : V) := by
     intro t
     change 0 ≤ (- f) (a t : V)
     simp only [ContinuousLinearMap.neg_apply]
     exact neg_nonneg.mpr (hn t)
   obtain ⟨v,hv⟩ := continuousLinearMap_has_one_of_ne_zero f' ff'
   exact sphere_loop_middle_of_linear_halfspace w a f' v fw' fa' hv
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/HemisphereAvoid.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckCompact.lean
section

noncomputable section
open Set Topology TopologicalSpace CategoryTheory
open TopCat
open scoped Topology Manifold
namespace NonlinearThreeManifoldSupport

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

/-- The (translated) bit of a chart ball of radius `s` about the marked point,
 including the marked point.  For `s < R` this lies in the chosen chart target.
 Its complement is a compact core of a compact block. -/
def chartLocalBall (b : Y) (s : ℝ) : Set Y :=
  (chartAt E b).source ∩
    (chartAt E b) ⁻¹' {q : E | ‖q - (chartAt E b) b‖ < s}

lemma chartLocalBall_open (b : Y) (s : ℝ) :
    IsOpen (chartLocalBall (E:=E) b s) := by
  have h : IsOpen {q : E | ‖q - (chartAt E b) b‖ < s} := by
    exact isOpen_lt (continuous_norm.comp
      (continuous_id.sub continuous_const)) continuous_const
  exact (chartAt E b).isOpen_inter_preimage h

lemma chartLocalBall_mem (b : Y) {s : ℝ} (hs : 0 < s) :
    b ∈ chartLocalBall (E:=E) b s := by
  refine ⟨mem_chart_source E b, ?_⟩
  change ‖(chartAt E b) b - (chartAt E b) b‖ < s
  simpa using hs

lemma chartEndSet_iff_local (b : Y) (A : ChartBall (E:=E) b) {y : Y} :
    y ∈ chartEndSet (E:=E) b A ↔
      y ∈ (chartAt E b).source ∧
       ((chartAt E b) y - (chartAt E b) b) ≠ 0 ∧
       ‖(chartAt E b) y - (chartAt E b) b‖ < A.R := by
  rfl

lemma chartLocalBall_end {b : Y} (A : ChartBall (E:=E) b)
    {s : ℝ} (hs : 0 < s) (hsR : s ≤ A.R) {y : Y}
    (hy : y ∈ chartLocalBall (E:=E) b s) (hyb : y ≠ b) :
    y ∈ chartEndSet (E:=E) b A := by
  refine ⟨hy.1, ?_⟩
  refine ⟨?_, lt_of_lt_of_le hy.2 hsR⟩
  intro h
  have ee : (chartAt E b) y = (chartAt E b) b := sub_eq_zero.mp h
  have yb := (chartAt E b).injOn (mem_chart_source E b |> fun h => hy.1) -- dummy
  exact hyb ((chartAt E b).injOn hy.1 (mem_chart_source E b) ee)

-- fix the previous line simplification

lemma chartEndHomeo_point (b : Y) (A : ChartBall (E:=E) b)
    (x : (chartEnd (E:=E) b A : Type _)) :
    ((chartEndHomeo (E:=E) b A x : E)) =
       (chartAt E b) (x.1.1) - (chartAt E b) b := rfl

/-- The coordinate norm on the end after the radial exchange. -/
lemma chartEndFlip_size (b : Y) (A : ChartBall (E:=E) b)
    (x : (chartEnd (E:=E) b A : Type _)) :
    ‖(chartAt E b) ((chartEndFlip (E:=E) b A x).1.1) -
        (chartAt E b) b‖ =
      A.R - ‖(chartAt E b) (x.1.1) - (chartAt E b) b‖ := by
  have h := radialFlip_norm (E:=E) A.pos
       (((chartEndHomeo (E:=E) b A) x).property)
  have eq : (chartEndHomeo (E:=E) b A)
       ((chartEndFlip (E:=E) b A) x) =
       (radialFlipHomeo (E:=E) A.R A.pos)
         ((chartEndHomeo (E:=E) b A) x) := by
    -- just the conjugation defining the transition
    simp [chartEndFlip, Homeomorph.trans_apply]
  change ‖((chartEndHomeo (E:=E) b A)
       ((chartEndFlip (E:=E) b A) x) : E)‖ = _
  rw [eq]
  change ‖radialFlip A.R
        (((chartEndHomeo (E:=E) b A) x) : E)‖ = _
  -- the right hand coordinate is the defining chart-end coordinate
  exact h

/-- The complement of the small chart ball injects into the punctured block. -/
def chartCoreInPunct {b : Y} {s : ℝ} (hs : 0 < s) :
    ((chartLocalBall (E:=E) b s)ᶜ : Set Y) →
       (({b} : Set Y)ᶜ : Set Y) :=
  fun y => ⟨(y:Y), by
    intro hb; have : (y:Y) = b := by simpa using hb
    have hm : b ∈ chartLocalBall (E:=E) b s :=
      chartLocalBall_mem (E:=E) b hs
    exact y.property (by simpa [this] using hm)⟩

lemma chartCoreInPunct_cont {b : Y} {s : ℝ} (hs : 0 < s) :
    Continuous (chartCoreInPunct (E:=E) (b:=b) hs) := by
  apply continuous_induced_rng.2
  exact continuous_subtype_val

/-- A compact core together with the exchanged core covers the punctured
 patch. This elementary assertion is the compactness engine for the open
 double: a point closer than halfway to the deleted point is represented in
 the other copy further than halfway. -/
lemma punct_core_or_flip {b : Y} (A : ChartBall (E:=E) b)
    (x : (({b} : Set Y)ᶜ : Set Y)) :
    ( (x:Y) ∈ (chartLocalBall (E:=E) b (A.R/2))ᶜ ) ∨
    ∃ v : (chartEnd (E:=E) b A : Type _),
       (v.1.1 : Y) = x ∧
       (((chartEndFlip (E:=E) b A) v).1.1 : Y) ∈
          (chartLocalBall (E:=E) b (A.R/2))ᶜ := by
  classical
  by_cases hx : (x:Y) ∈ chartLocalBall (E:=E) b (A.R/2)
  · right
    have hpos : 0 < A.R / 2 := by linarith [A.pos]
    have hend : (x:Y) ∈ chartEndSet (E:=E) b A :=
      chartLocalBall_end (E:=E) A hpos (by linarith [A.pos]) hx (by
        intro q; exact x.property (by simpa [q]))
    let v : (chartEnd (E:=E) b A : Type _) := ⟨x, hend⟩
    refine ⟨v, rfl, ?_⟩
    intro hm
    have hsmall :
        ‖(chartAt E b) (((chartEndFlip (E:=E) b A) v).1.1) -
            (chartAt E b) b‖ < A.R/2 := hm.2
    have hsize := chartEndFlip_size (E:=E) b A v
    have hvlt : ‖(chartAt E b) (v.1.1) - (chartAt E b) b‖ < A.R/2 := by
      -- this is exactly membership of `x` in the small local ball
      simpa [v] using hx.2
    linarith
  · left; exact hx

/-- The radial double of a compact block is compact.  Notice that the gluing
 uses *open punctured* blocks; compactness is not inherited from either open
 patch. The compact cores at radius `R/2` are what make this true. -/
lemma doubleGlue_chartEnd_compact
    {b : Y} [CompactSpace Y] (A : ChartBall (E:=E) b) :
    let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
    let V : Opens X := chartEnd (E:=E) b A
    let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
    let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
    CompactSpace (doubleGlueData X V e he).toGlueData.glued := by
  classical
  dsimp
  -- names make the little colimit legible below
  let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
  let V : Opens X := chartEnd (E:=E) b A
  let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
  let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
  let D : TopCat.GlueData.{0} := doubleGlueData X V e he
  let K : Set Y := (chartLocalBall (E:=E) b (A.R/2))ᶜ
  have hp : 0 < A.R/2 := by linarith [A.pos]
  have hK : IsCompact K :=
    (chartLocalBall_open (E:=E) b (A.R/2)).isClosed_compl.isCompact
  let u : K → (({b}:Set Y)ᶜ : Set Y) :=
    chartCoreInPunct (E:=E) (b:=b) hp
  have uc : Continuous u := chartCoreInPunct_cont (b:=b) hp
  -- the two compact legs
  let L0 : K → D.toGlueData.glued :=
    fun z => D.toGlueData.ι false (u z)
  let L1 : K → D.toGlueData.glued :=
    fun z => D.toGlueData.ι true (u z)
  have L0c : Continuous L0 := by
    exact (D.toGlueData.ι false).hom.continuous_toFun.comp uc
  have L1c : Continuous L1 := by
    exact (D.toGlueData.ι true).hom.continuous_toFun.comp uc
  have KI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace K := KI
  have cc0 : IsCompact (Set.range L0) := isCompact_range L0c
  have cc1 : IsCompact (Set.range L1) := isCompact_range L1c
  have hall : Set.univ ⊆ Set.range L0 ∪ Set.range L1 := by
    intro q hq
    obtain ⟨i,x,hxq⟩ := D.ι_jointly_surjective q
    -- the index is literally `Bool`
    change Bool at i
    -- eliminating it first makes the patch representative definitional
    rcases i with _|_
    · change (({b}:Set Y)ᶜ : Set Y) at x
      have dich := punct_core_or_flip (E:=E) A x
      rcases dich with hx | ⟨v,hv,hflip⟩
      · left
        let k : K := ⟨(x:Y), hx⟩
        refine ⟨k, ?_⟩
        simpa [L0, u, chartCoreInPunct] using hxq
      · right
        let k : K := ⟨(((chartEndFlip (E:=E) b A) v).1.1 : Y), hflip⟩
        refine ⟨k, ?_⟩
        have eq := D.toGlueData.glue_condition_apply false true v
        change D.toGlueData.ι true ((e v).1) =
            D.toGlueData.ι false (v.1) at eq
        have xv : (v.1) = x := by apply Subtype.ext; exact hv
        have hvq : D.toGlueData.ι false (v.1) = q := by
          rw [xv]
          exact hxq
        simpa [L1, u, chartCoreInPunct, k, e] using eq.trans hvq
    · change (({b}:Set Y)ᶜ : Set Y) at x
      have dich := punct_core_or_flip (E:=E) A x
      rcases dich with hx | ⟨v,hv,hflip⟩
      · right
        let k : K := ⟨(x:Y), hx⟩
        refine ⟨k, ?_⟩
        simpa [L1, u, chartCoreInPunct] using hxq
      · left
        let k : K := ⟨(((chartEndFlip (E:=E) b A) v).1.1 : Y), hflip⟩
        refine ⟨k, ?_⟩
        have eq := D.toGlueData.glue_condition_apply true false v
        change D.toGlueData.ι false ((e v).1) =
            D.toGlueData.ι true (v.1) at eq
        have xv : (v.1) = x := by apply Subtype.ext; exact hv
        have hvq : D.toGlueData.ι true (v.1) = q := by
          rw [xv]
          exact hxq
        simpa [L0, u, chartCoreInPunct, k, e] using eq.trans hvq

  have uni : IsCompact (Set.univ : Set D.toGlueData.glued) := by
    have eq : (Set.univ : Set D.toGlueData.glued) =
        Set.range L0 ∪ Set.range L1 :=
      Set.Subset.antisymm hall (by intro z hz; trivial)
    rw [eq]
    exact cc0.union cc1
  exact isCompact_univ_iff.mp uni

end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckCompact.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckEndKill.lean
section
open scoped Topology
open Set Metric Topology unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

/-- Not just a chosen little cross section: *every* based loop in the open
punctured chart end dies on entering the block.  Although the punctured ball
itself need not be simply connected in arbitrary dimension, the inclusion
factors through the honest ball, which is convex.  This version is useful for
transition loops of the two open patches. -/
lemma chartEnd_paths_in_block
    (b : Y) (A : ChartBall (E:=E) b)
    {z : (chartEnd (E:=E) b A : Type _)} (L : Path z z) :
    Path.Homotopic
      (L.map (chartEndInBlock (E:=E) b A).continuous)
      (Path.refl (chartEndInBlock (E:=E) b A z)) := by
  let T : C((chartEnd (E:=E) b A : Type _), Y) :=
    (chartBallMap (E:=E) b A).comp (chartEndToBall (E:=E) b A)
  have eqmap : T = chartEndInBlock (E:=E) b A := by
    ext t
    exact chartEndToBall_inv (E:=E) b A t
  -- Substitute the whole map, rather than the image of just its marked
  -- point. This avoids a dependent endpoint cast in `Path.map`.
  rw [← eqmap]
  let bz : (Metric.ball (0:E) A.R : Set E) := chartEndToBall (E:=E) b A z
  let LL : Path bz bz := L.map (chartEndToBall (E:=E) b A).continuous
  let RR : Path bz bz := Path.refl bz
  have H : Path.Homotopic LL RR := ball_paths_homotopic A.R LL RR
  have H' := H.map (chartBallMap (E:=E) b A)
  have left : LL.map (chartBallMap (E:=E) b A).continuous =
      L.map T.continuous := by
    apply Path.ext
    rfl
  have right : RR.map (chartBallMap (E:=E) b A).continuous =
      Path.refl (T z) := by
    apply Path.ext
    rfl
  exact left ▸ right ▸ H'

lemma chartEnd_piOne_in_block
    (b : Y) (A : ChartBall (E:=E) b)
    (z : (chartEnd (E:=E) b A : Type _))
    (a : FundamentalGroup (chartEnd (E:=E) b A : Type _) z) :
    FundamentalGroup.map (chartEndInBlock (E:=E) b A) z a =
      (1 : FundamentalGroup Y (chartEndInBlock (E:=E) b A z)) := by
  change Path.Homotopic.Quotient z z at a
  induction a using Quotient.inductionOn with
  | _ L =>
    change Path.Homotopic.Quotient.mk _ = _
    change Path.Homotopic.Quotient.mk _ =
      Path.Homotopic.Quotient.mk (Path.refl (chartEndInBlock (E:=E) b A z))
    exact Quotient.sound (chartEnd_paths_in_block (E:=E) b A L)
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckEndKill.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NormAction.lean
section
open scoped Quaternion RealInnerProductSpace
open Metric Set
noncomputable section
namespace NonlinearThreeManifoldSupport
variable {G : Type*} [Group G]
/-- Restrict multiplication by unit norm quaternions to the sphere.  The definition is
kept reducible: this makes the `SMul` projection definitionally the literal product, which
is convenient both for continuity and for cancellation. -/
@[reducible] def unitSphereAction (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1) :
    MulAction G qSphere where
  smul g x := ⟨ρ g * (x : Quaternion ℝ), by
    have hx : ‖(x : Quaternion ℝ)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    exact mem_sphere_zero_iff_norm.mpr (by rw [norm_mul, hn, hx]; norm_num)⟩
  one_smul x := by
    apply Subtype.ext
    change ρ 1 * (x : Quaternion ℝ) = _
    rw [map_one, one_mul]
  mul_smul g h x := by
    apply Subtype.ext
    change ρ (g * h) * (x : Quaternion ℝ) =
      ρ g * (ρ h * (x : Quaternion ℝ))
    rw [map_mul, mul_assoc]

/-- Explicit `SMul` underlying `unitSphereAction`.  Spelling this projection out avoids
synthesising a new, unrelated instance of `SMul` in downstream lemmas. -/
abbrev unitSphereSMul (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1) : SMul G qSphere :=
  @SemigroupAction.toSMul _ _ _
    (@MulAction.toSemigroupAction _ _ _ (unitSphereAction ρ hn))

lemma unitSphereAction_smul (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1)
    (g : G) (x : qSphere) :
    (@HSMul.hSMul G qSphere qSphere (@instHSMul G qSphere (unitSphereSMul ρ hn))
       g x).1 = ρ g * (x : Quaternion ℝ) := rfl

/-- Each left multiplier gives a continuous self-map of the sphere. -/
lemma unitSphereAction_cont (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1) :
    @ContinuousConstSMul G qSphere _ (unitSphereSMul ρ hn) := by
  letI : MulAction G qSphere := unitSphereAction ρ hn
  constructor
  intro g
  apply continuous_induced_rng.mpr
  change Continuous (fun x : qSphere => ρ g * (x : Quaternion ℝ))
  exact (continuous_subtype_val.const_mul _)

lemma unitSphereAction_left_cancel (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1) :
    @IsLeftCancelSMul G qSphere (unitSphereSMul ρ hn) := by
  letI : MulAction G qSphere := unitSphereAction ρ hn
  constructor
  intro a b c e
  apply Subtype.ext
  have eq : ρ a * (b : Quaternion ℝ) = ρ a * (c : Quaternion ℝ) :=
    congrArg (fun w : qSphere => (w : Quaternion ℝ)) e
  have nz : ρ a ≠ 0 := by
    intro z
    have hh := hn a
    rw [z, norm_zero] at hh
    norm_num at hh
  exact mul_left_cancel₀ nz eq

/-- Freeness of the restricted action.  Only the injectivity of the chosen quaternion
representation enters on the right; no topology is involved here. -/
lemma unitSphereAction_cancel (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1)
    (hinj : Function.Injective ρ) :
    @IsCancelSMul G qSphere (unitSphereSMul ρ hn) := by
  letI : MulAction G qSphere := unitSphereAction ρ hn
  letI lc : @IsLeftCancelSMul G qSphere (unitSphereSMul ρ hn) :=
    unitSphereAction_left_cancel ρ hn
  constructor
  intro g h x eq
  have e : ρ g * (x : Quaternion ℝ) = ρ h * (x : Quaternion ℝ) :=
    congrArg (fun w : qSphere => (w : Quaternion ℝ)) eq
  have nx : (x : Quaternion ℝ) ≠ 0 := by
    intro z
    have hx : ‖(x : Quaternion ℝ)‖ = (1 : ℝ) := mem_sphere_zero_iff_norm.mp x.property
    rw [z, norm_zero] at hx
    norm_num at hx
  exact hinj (mul_right_cancel₀ nx e)
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NormAction.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/OrbitEndpoint.lean
section
open scoped Topology
open Topology unitInterval CategoryTheory Set
noncomputable section
namespace NonlinearThreeManifoldSupport
lemma IsCoveringMap.monodromy_surj_of_pathConnected
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : IsCoveringMap p) [PathConnectedSpace E]
    (e : E) :
    Function.Surjective
      (fun a : FundamentalGroup X (p e) =>
        cov.monodromy a (⟨e, rfl⟩ : p ⁻¹' ({p e} : Set X))) := by
  intro e'
  have ep : p e'.1 = p e := e'.2
  let L : Path e (e'.1) := PathConnectedSpace.somePath _ _
  let q : Path.Homotopic.Quotient e (e'.1) := ⟦L⟧
  let γ : Path.Homotopic.Quotient (p e) (p e) :=
    (q.map ⟨p, cov.continuous⟩).cast rfl ep.symm
  refine ⟨γ, ?_⟩
  apply Subtype.ext
  change _ = e'.1
  dsimp [γ, q]
  change cov.liftPath
    ((L.map cov.continuous).cast rfl ep.symm) e
      ((L.map cov.continuous).cast rfl ep.symm).source 1 = e'.1
  have funeq : p ∘ (L : I → E) =
        (((L.map cov.continuous).cast rfl ep.symm) : I → X) := by
    exact (Path.map_coe L cov.continuous).symm
  have liftEq : (L : C(I,E)) =
      cov.liftPath ((L.map cov.continuous).cast rfl ep.symm) e
        ((L.map cov.continuous).cast rfl ep.symm).source :=
    (cov.eq_liftPath_iff' _).2 ⟨funeq, L.source⟩
  exact (congrArg (fun (T : C(I,E)) => T 1) liftEq).symm.trans L.target
end NonlinearThreeManifoldSupport
-- import placed late illegal? lean allows
open scoped Quaternion
namespace NonlinearThreeManifoldSupport
lemma orbit_endpoint_surj
    (G : Type*) [Group G] [MulAction G qSphere]
    [ContinuousConstSMul G qSphere] [Finite G] [IsCancelSMul G qSphere]
    (e : qSphere) :
    Function.Surjective
      (fun a : FundamentalGroup (qOrbit G)
          ((Quotient.mk (MulAction.orbitRel G qSphere)) e) =>
        (qOrbitIsCovering G).monodromy a
          (⟨e, rfl⟩ :
            (Quotient.mk (MulAction.orbitRel G qSphere)) ⁻¹'
              ({(Quotient.mk (MulAction.orbitRel G qSphere)) e} : Set (qOrbit G)))) := by
  exact IsCoveringMap.monodromy_surj_of_pathConnected (qOrbitIsCovering G) e
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
lemma IsQuotientCoveringMap.endpoint_group_surj
 {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
 [Group G] [MulAction G E]
 {p : E → X} (hp : IsQuotientCoveringMap p G)
 [PathConnectedSpace E]
 (e : E) :
 Function.Surjective
   (fun a : FundamentalGroup X (p e) =>
     hp.fiberEquivGroup (⟨e, rfl⟩ : p ⁻¹' {p e})
       (hp.isCoveringMap.monodromy a (⟨e, rfl⟩ : p ⁻¹' {p e}))) := by
  intro g
  let target : p ⁻¹' {p e} := (hp.fiberEquivGroup (⟨e, rfl⟩ : p ⁻¹' {p e})).symm g
  obtain ⟨a, ha⟩ :=
    IsCoveringMap.monodromy_surj_of_pathConnected hp.isCoveringMap e target
  refine ⟨a, ?_⟩
  change hp.fiberEquivGroup (⟨e, rfl⟩ : p ⁻¹' {p e})
      (hp.isCoveringMap.monodromy a (⟨e, rfl⟩ : p ⁻¹' {p e})) = g
  have h' := congrArg (hp.fiberEquivGroup (⟨e, rfl⟩ : p ⁻¹' {p e})) ha
  simpa [target] using h'
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/OrbitEndpoint.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/DeckEndpoint.lean
section
open NonlinearThreeManifoldSupport
open scoped Topology
open Topology unitInterval CategoryTheory Set
noncomputable section
namespace NonlinearThreeManifoldSupport
lemma monodromy_smul
 {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
 [Group G] [MulAction G E]
 {p : E → X} (hp : IsQuotientCoveringMap p G)
 {x : X} (γ : Path.Homotopic.Quotient x x)
 (e : p ⁻¹' ({x} : Set X)) (g : G) :
   (hp.isCoveringMap.monodromy γ
     (⟨g • (e:E), (hp.map_smul g).trans e.2⟩ : p ⁻¹' ({x}:Set X))).1
      = g • (hp.isCoveringMap.monodromy γ e).1 := by
  letI : ContinuousConstSMul G E := hp.toContinuousConstSMul
  induction γ using Quotient.inductionOn with | _ q =>
    -- q : Path x x
    dsimp [IsCoveringMap.monodromy]
    change hp.isCoveringMap.liftPath q (g • (e:E)) _ 1 =
      g • ((hp.isCoveringMap.liftPath q (e:E) _) 1)
    have he0 : q 0 = p (e:E) := q.source.trans e.2.symm
    have heg : q 0 = p (g • (e:E)) := he0.trans (hp.map_smul g).symm
    let A : C(unitInterval,E) := hp.isCoveringMap.liftPath q (e:E) he0
    let GA : C(unitInterval,E) :=
      { toFun := fun t => g • A t
        continuous_toFun :=
          (ContinuousConstSMul.continuous_const_smul g).comp A.continuous }
    have eqGA : GA = hp.isCoveringMap.liftPath q (g • (e:E)) heg := by
      apply (hp.isCoveringMap.eq_liftPath_iff' heg).2
      constructor
      · funext t
        dsimp [GA]
        exact (hp.map_smul g).trans
          (congr_fun (hp.isCoveringMap.liftPath_lifts q (e:E) he0) t)
      · dsimp [GA, A]
        rw [hp.isCoveringMap.liftPath_zero]
    have ep := congrArg (fun (T : C(unitInterval,E)) => T 1) eqGA
    dsimp [GA, A] at ep
    exact ep.symm
lemma f_mul
 {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
 [Group G] [MulAction G E]
 {p : E → X} (hp : IsQuotientCoveringMap p G)
 {x : X}
 (e : p ⁻¹' ({x} : Set X))
 (a b : FundamentalGroup X x) :
 hp.fiberEquivGroup e (hp.isCoveringMap.monodromy (a*b) e) =
   hp.fiberEquivGroup e (hp.isCoveringMap.monodromy b e) *
   hp.fiberEquivGroup e (hp.isCoveringMap.monodromy a e) := by
 letI : ContinuousConstSMul G E := hp.toContinuousConstSMul
 let α := hp.fiberEquivGroup e (hp.isCoveringMap.monodromy a e)
 let β := hp.fiberEquivGroup e (hp.isCoveringMap.monodromy b e)
 have ha : (hp.isCoveringMap.monodromy a e).1 = α • (e:E) := by
   symm
   exact hp.fiberEquivGroup_smul_self e
 have hb : (hp.isCoveringMap.monodromy b e).1 = β • (e:E) := by
   symm
   exact hp.fiberEquivGroup_smul_self e
 apply (hp.fiberEquivGroup_eq_iff e _ _).2
 change (hp.isCoveringMap.monodromy (a*b) e).1 = _
 -- monodromy product
 have trans := hp.isCoveringMap.monodromy_trans_apply (γ:= (FundamentalGroup.toPath b))
     (γ' := (FundamentalGroup.toPath a)) e
 change (hp.isCoveringMap.monodromy (a*b) e) = _ at trans
 rw [trans]
 -- endpoint equality after rewrite using equivariance for starting beta
 have ha' := monodromy_smul hp (FundamentalGroup.toPath a) e β
 -- replace inside
 change (hp.isCoveringMap.monodromy a (hp.isCoveringMap.monodromy b e)).1 = _
 -- use hb for subtype equality
 have hbsub : hp.isCoveringMap.monodromy b e =
      (⟨β • (e:E), (hp.map_smul β).trans e.2⟩ : p ⁻¹' {x}) := by
   apply Subtype.ext
   exact hb
 rw [hbsub]
 rw [ha']
 rw [ha]
 have hβ : hp.fiberEquivGroup e
      (⟨β • (e:E), (hp.map_smul β).trans e.2⟩ : p ⁻¹' {x}) = β :=
   (hp.fiberEquivGroup_eq_iff e _ _).2 rfl
 rw [hβ]
 change β • (α • (e:E)) = (β * α) • (e:E)
 rw [mul_smul]
noncomputable def deckHom
 {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
 [Group G] [MulAction G E]
 {p : E → X} (hp : IsQuotientCoveringMap p G)
 {x : X} (e : p ⁻¹' ({x} : Set X)) : FundamentalGroup X x →* G :=
 MonoidHom.mk'
  (fun a => (hp.fiberEquivGroup e (hp.isCoveringMap.monodromy a e))⁻¹)
  (by
    intro a b
    rw [f_mul hp e]
    simp)
noncomputable def deckHom0
 {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
 [Group G] [MulAction G E]
 {p : E → X} (hp : IsQuotientCoveringMap p G) (e : E) :
 FundamentalGroup X (p e) →* G :=
 deckHom hp (⟨e, rfl⟩ : p ⁻¹' ({p e}: Set X))
lemma deckHom0_surj
 {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
 [Group G] [MulAction G E]
 {p : E → X} (hp : IsQuotientCoveringMap p G)
 [PathConnectedSpace E]
 (e : E) :
 Function.Surjective (deckHom0 hp e) := by
 intro g
 obtain ⟨a, ha⟩ :=
   NonlinearThreeManifoldSupport.IsQuotientCoveringMap.endpoint_group_surj hp e (g⁻¹)
 refine ⟨a, ?_⟩
 change (hp.fiberEquivGroup (⟨e,rfl⟩ : p ⁻¹' {p e})
    (hp.isCoveringMap.monodromy a (⟨e,rfl⟩ : p ⁻¹' {p e})))⁻¹ = g
 dsimp at ha
 rw [ha, inv_inv]
lemma deckHom0_inj
 {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
 [Group G] [MulAction G E]
 {p : E → X} (hp : IsQuotientCoveringMap p G)
 [SimplyConnectedSpace E]
 (e : E) :
 Function.Injective (deckHom0 hp e) := by
 intro a b eqab
 change (hp.fiberEquivGroup (⟨e,rfl⟩ : p ⁻¹' {p e})
    (hp.isCoveringMap.monodromy a (⟨e,rfl⟩ : p ⁻¹' {p e})))⁻¹ =
    (hp.fiberEquivGroup (⟨e,rfl⟩ : p ⁻¹' {p e})
    (hp.isCoveringMap.monodromy b (⟨e,rfl⟩ : p ⁻¹' {p e})))⁻¹ at eqab
 have eqF := inv_injective eqab
 have eqfiber := (hp.fiberEquivGroup (⟨e,rfl⟩ : p ⁻¹' {p e})).injective eqF
 exact (NonlinearThreeManifoldSupport.IsCoveringMap.monodromy_bijective_of_simplyConnected
    hp.isCoveringMap e).1 eqfiber
lemma block_retract_of_sc
 {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
 [Group G] [MulAction G E]
 {p : E → X} (hp : IsQuotientCoveringMap p G)
 [SimplyConnectedSpace E]
 (e : E) : ∃ (u : G →* FundamentalGroup X (p e))
   (d : FundamentalGroup X (p e) →* G),
   d.comp u = MonoidHom.id G := by
 let φ : FundamentalGroup X (p e) ≃* G :=
   MulEquiv.ofBijective (deckHom0 hp e)
     ⟨deckHom0_inj hp e, deckHom0_surj hp e⟩
 refine ⟨φ.symm.toMonoidHom, φ.toMonoidHom, ?_⟩
 ext g
 exact φ.apply_symm_apply g

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open scoped Quaternion
/-- Applied to a norm-one quaternion action. This deliberately keeps simply connectedness
of the universal quaternionic sphere as an explicit assumption: the algebraic endpoint
map and its deck convention do not need any sphere-coordinate calculation. -/
lemma qOrbit_block_retract_of_sc
    {G : Type*} [Group G] [Finite G]
    (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1)
    (hi : Function.Injective ρ) [SimplyConnectedSpace qSphere]
    (e : qSphere) :
    letI : MulAction G qSphere := unitSphereAction ρ hn
    letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
    letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
    ∃ (u : G →* FundamentalGroup (qOrbit G)
        ((Quotient.mk (MulAction.orbitRel G qSphere)) e))
      (d : FundamentalGroup (qOrbit G)
        ((Quotient.mk (MulAction.orbitRel G qSphere)) e) →* G),
        d.comp u = MonoidHom.id G := by
  letI : MulAction G qSphere := unitSphereAction ρ hn
  letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
  letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
  exact block_retract_of_sc
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (E := qSphere) (G := G)) e
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
open scoped Quaternion
/-- Even before one has null-homotopies on the sphere, loop lifting gives an honest
*epimorphism* from the fundamental group of the spherical quotient.  The inverse
at the endpoint corrects the order of multiplication in `End`. -/
lemma qOrbit_deck_epimorphism
    {G : Type*} [Group G] [Finite G]
    (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1)
    (hi : Function.Injective ρ)
    (e : qSphere) :
    letI : MulAction G qSphere := unitSphereAction ρ hn
    letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
    letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
    ∃ d : FundamentalGroup (qOrbit G)
        ((Quotient.mk (MulAction.orbitRel G qSphere)) e) →* G,
        Function.Surjective d := by
  letI : MulAction G qSphere := unitSphereAction ρ hn
  letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
  letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
  let hp :=
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (E := qSphere) (G := G))
  exact ⟨deckHom0 hp e, deckHom0_surj hp e⟩
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
/-- It is not necessary to formalize every equality of the fundamental group of the
sphere to split off the deck group. Injectivity of the endpoint **at this one sheet**
is enough. This is frequently a smaller target than a global universal-cover API. -/
lemma deckHom0_inj_of_endpoint
 {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
 [Group G] [MulAction G E]
 {p : E → X} (hp : IsQuotientCoveringMap p G)
 (e : E)
 (h : Function.Injective
      (fun a : FundamentalGroup X (p e) =>
        hp.isCoveringMap.monodromy a
          (⟨e, rfl⟩ : p ⁻¹' ({p e} : Set X)))) :
 Function.Injective (deckHom0 hp e) := by
 intro a b hab
 change (hp.fiberEquivGroup (⟨e,rfl⟩ : p ⁻¹' {p e})
    (hp.isCoveringMap.monodromy a (⟨e,rfl⟩ : p ⁻¹' {p e})))⁻¹ =
    (hp.fiberEquivGroup (⟨e,rfl⟩ : p ⁻¹' {p e})
    (hp.isCoveringMap.monodromy b (⟨e,rfl⟩ : p ⁻¹' {p e})))⁻¹ at hab
 have q := inv_injective hab
 exact h ((hp.fiberEquivGroup (⟨e,rfl⟩ : p ⁻¹' {p e})).injective q)

lemma block_retract_of_endpoint
 {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
 [Group G] [MulAction G E]
 {p : E → X} (hp : IsQuotientCoveringMap p G)
 [PathConnectedSpace E]
 (e : E)
 (h : Function.Injective
      (fun a : FundamentalGroup X (p e) =>
        hp.isCoveringMap.monodromy a
          (⟨e, rfl⟩ : p ⁻¹' ({p e} : Set X)))) :
 ∃ (u : G →* FundamentalGroup X (p e))
   (d : FundamentalGroup X (p e) →* G),
   d.comp u = MonoidHom.id G := by
 let φ : FundamentalGroup X (p e) ≃* G :=
   MulEquiv.ofBijective (deckHom0 hp e)
     ⟨deckHom0_inj_of_endpoint hp e h, deckHom0_surj hp e⟩
 refine ⟨φ.symm.toMonoidHom, φ.toMonoidHom, ?_⟩
 ext g
 exact φ.apply_symm_apply g

open scoped Quaternion
lemma qOrbit_block_retract_of_endpoint
    {G : Type*} [Group G] [Finite G]
    (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1)
    (hi : Function.Injective ρ)
    (e : qSphere) :
    letI : MulAction G qSphere := unitSphereAction ρ hn
    letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
    letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
    (Function.Injective
      (fun a : FundamentalGroup (qOrbit G)
          ((Quotient.mk (MulAction.orbitRel G qSphere)) e) =>
        (qOrbitIsCovering G).monodromy a
          (⟨e, rfl⟩ :
            (Quotient.mk (MulAction.orbitRel G qSphere)) ⁻¹'
              ({(Quotient.mk (MulAction.orbitRel G qSphere)) e} : Set (qOrbit G))))) →
    ∃ (u : G →* FundamentalGroup (qOrbit G)
        ((Quotient.mk (MulAction.orbitRel G qSphere)) e))
      (d : FundamentalGroup (qOrbit G)
        ((Quotient.mk (MulAction.orbitRel G qSphere)) e) →* G),
        d.comp u = MonoidHom.id G := by
  letI : MulAction G qSphere := unitSphereAction ρ hn
  letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
  letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
  intro h
  exact block_retract_of_endpoint
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (E := qSphere) (G := G)) e h
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
open scoped Quaternion
/-- A convenient specified sheet for the quaternionic sphere.  Keeping a literal
point, rather than a bare `Nonempty`, avoids a later choice every time the
`FundamentalGroup.mapOfEq` basepoint is used. -/
noncomputable def qNorth : qSphere := ⟨1, by simp⟩
end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open scoped Topology
open Topology unitInterval CategoryTheory Set
/-- The exact local null-homotopy input used by loop endpoints.  In particular no
path-connectedness assertion on unrelated components of `E` is tested.  For a
sphere it suffices to compare paths out of the chosen north sheet. -/
lemma IsCoveringMap.endpoint_inj_of_start_paths
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : IsCoveringMap p) (e : E)
    (H : ∀ (z : E) (a b : Path e z), Path.Homotopic a b) :
    Function.Injective
      (fun a : FundamentalGroup X (p e) =>
        cov.monodromy a (⟨e, rfl⟩ : p ⁻¹' ({p e} : Set X))) := by
  intro a b h
  change Path.Homotopic.Quotient (p e) (p e) at a b
  induction a using Quotient.inductionOn with | _ pa =>
   induction b using Quotient.inductionOn with | _ pb =>
    let la : C(unitInterval, E) := cov.liftPath pa e pa.source
    let lb : C(unitInterval, E) := cov.liftPath pb e pb.source
    have la0 : la 0 = e := cov.liftPath_zero _ _ _
    have lb0 : lb 0 = e := cov.liftPath_zero _ _ _
    have ends : la 1 = lb 1 := congrArg Subtype.val h
    let A : Path e (la 1) :=
      { toContinuousMap := la, source' := la0, target' := rfl }
    let B : Path e (la 1) :=
      { toContinuousMap := lb, source' := lb0, target' := ends.symm }
    have hh : Path.Homotopic A B := H (la 1) A B
    have hm : Path.Homotopic (A.map cov.continuous)
        (B.map cov.continuous) := by
      exact Path.Homotopic.map hh ⟨p, cov.continuous⟩
    have ee : p e = p e := rfl
    have et : p e = p (la 1) := by
      symm
      exact (congr_fun (cov.liftPath_lifts pa e pa.source) 1).trans pa.target
    have hm' : Path.Homotopic ((A.map cov.continuous).cast ee et)
        ((B.map cov.continuous).cast ee et) := hm.pathCast _ _
    have ea : (A.map cov.continuous).cast ee et = pa := by
      apply Path.ext
      exact cov.liftPath_lifts pa e pa.source
    have eb : (B.map cov.continuous).cast ee et = pb := by
      apply Path.ext
      exact cov.liftPath_lifts pb e pb.source
    exact Quotient.sound (ea ▸ eb ▸ hm')

open scoped Quaternion
/-- A particularly pointed cut for the quaternion block: construct only
homotopies of paths *beginning at this sheet* of the norm sphere. Those
homotopies imply the endpoint hypothesis used in `qOrbit_block_retract_of_endpoint`.
This is weaker than installing `SimplyConnectedSpace qSphere`. -/
lemma qOrbit_endpoint_inj_of_start_paths
    {G : Type*} [Group G] [Finite G]
    (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1)
    (hi : Function.Injective ρ)
    (e : qSphere)
    (H : ∀ (z : qSphere) (a b : Path e z), Path.Homotopic a b) :
    letI : MulAction G qSphere := unitSphereAction ρ hn
    letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
    letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
    Function.Injective
      (fun a : FundamentalGroup (qOrbit G)
          ((Quotient.mk (MulAction.orbitRel G qSphere)) e) =>
        (qOrbitIsCovering G).monodromy a
          (⟨e, rfl⟩ :
            (Quotient.mk (MulAction.orbitRel G qSphere)) ⁻¹'
              ({(Quotient.mk (MulAction.orbitRel G qSphere)) e} : Set (qOrbit G)))) := by
  letI : MulAction G qSphere := unitSphereAction ρ hn
  letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
  letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
  exact IsCoveringMap.endpoint_inj_of_start_paths (qOrbitIsCovering G) e H
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/DeckEndpoint.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/DirectionalAvoid.lean
section
open scoped Topology RealInnerProductSpace Quaternion
open Topology Set Metric unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport
/-- A fixed transverse vector is often enough even when the coordinate of the
old loop changes sign.  The only dangerous negative heights are the points
where the old loop is in the **two plane** generated by the base point and
that transverse vector.  Indeed, apply the transverse coordinate to a
putative antipodal chord; it must be negative.  The vector equation then puts
it in exactly this two plane.

This is convenient for isolating the genuinely winding direction cases: the
loop may take both signs, just not line up with this chosen direction while it
is below the equator. -/
lemma sphere_loop_middle_of_avoids_negative_plane
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 (w : Metric.sphere (0 : V) 1) (a : Path w w)
 (f : V →L[ℝ] ℝ) (u : V)
 (fw : f (w : V) = 0) (fu : f u = 1)
 (ha : ∀ t : I, t ≠ (0:I) → t ≠ (1:I) → f (a t : V) < 0 →
       ¬ ∃ r s : ℝ, (a t : V) = r • (w : V) + s • u) :
 ∃ c : Path w w,
      (∀ t : I, (c t : V) ≠ -(a t : V)) ∧
      (∀ t : I, ((Path.refl w) t : V) ≠ -(c t : V)) := by
 let bump : I → ℝ := fun t => (t:ℝ) * (1 - (t:ℝ))
 have bumpcont : Continuous bump := by dsimp [bump]; fun_prop
 have bumppos (t:I) (h0:t ≠ (0:I)) (h1:t ≠ (1:I)) : 0 < bump t := by
   dsimp [bump]
   have hp0 : 0 < (t:ℝ) := by
     have le := t.property.1
     have ne : (t:ℝ) ≠ 0 := by
       intro e; apply h0; apply Subtype.ext; simpa using e
     exact lt_of_le_of_ne le (Ne.symm ne)
   have hp1 : (t:ℝ) < 1 := by
     have le := t.property.2
     have ne : (t:ℝ) ≠ 1 := by
       intro e; apply h1; apply Subtype.ext; simpa using e
     exact lt_of_le_of_ne le ne
   exact mul_pos hp0 (sub_pos.mpr hp1)
 let raw : I → V := fun t => (w:V) + (1/2:ℝ) • (a t : V) + (bump t) • u
 have rawc : Continuous raw := by dsimp [raw]; fun_prop
 have fraw (t:I) : f (raw t) = (1/2:ℝ) * f (a t : V) + bump t := by
   dsimp [raw]
   simp [map_add, map_smul, fw, fu]
 have raw_ne (t:I) : raw t ≠ 0 := by
   classical
   by_cases h0 : t = (0:I)
   · subst t
     have wne : (w:V) ≠ 0 := by
       intro h
       have hnorm : ‖(w:V)‖ = 1 := by
         have h' := w.property; change dist (w:V) 0 = 1 at h'; simpa [dist_zero_right] using h'
       have : (0:ℝ)=1 := by simpa [h] using hnorm
       norm_num at this
     dsimp [raw, bump]
     have asrc : (a (0:I) : V) = (w:V) := congrArg Subtype.val a.source
     rw [asrc]
     intro hz
     have z : ((3/2:ℝ) • (w:V)) = 0 := by convert hz using 1 <;> module
     exact wne ((smul_eq_zero.mp z).resolve_left (by norm_num : (3/2:ℝ) ≠ 0))
   · by_cases h1 : t = (1:I)
     · subst t
       have wne : (w:V) ≠ 0 := by
         intro h
         have hnorm : ‖(w:V)‖ = 1 := by
           have h' := w.property; change dist (w:V) 0 = 1 at h'; simpa [dist_zero_right] using h'
         have : (0:ℝ)=1 := by simpa [h] using hnorm
         norm_num at this
       dsimp [raw, bump]
       have asrc : (a (1:I) : V) = (w:V) := congrArg Subtype.val a.target
       rw [asrc]
       intro hz
       have z : ((3/2:ℝ) • (w:V)) = 0 := by convert hz using 1 <;> module
       exact wne ((smul_eq_zero.mp z).resolve_left (by norm_num : (3/2:ℝ) ≠ 0))
     · intro hz
       have fb : 0 < bump t := bumppos t h0 h1
       have eqf : (1/2:ℝ) * f (a t : V) + bump t = 0 := by
         rw [← fraw t, hz]; simp
       have negfa : f (a t : V) < 0 := by linarith
       have noplane := ha t h0 h1 negfa
       apply noplane
       refine ⟨(-2:ℝ), -(2*bump t), ?_⟩
       -- the raw vector is zero, so solve its affine equation
       dsimp [raw] at hz
       -- tiny linear calculation in a real module
       -- all coefficients are scalars, so `module` can normalize it
       calc
         (a t : V) = (a t : V) - 2 •
             ((w:V) + (1/2:ℝ) • (a t : V) + (bump t) • u) := by
               rw [hz]
               module
         _ = (-2:ℝ) • (w:V) + (-(2*bump t)) • u := by module
 have norm_ne (t:I) : ‖raw t‖ ≠ 0 := norm_ne_zero_iff.mpr (raw_ne t)
 let toS : I → Metric.sphere (0:V) 1 := fun t => sphereNormalize (raw t) (raw_ne t)
 have toSc : Continuous toS := by
   apply continuous_induced_rng.2
   change Continuous (fun t : I => (sphereNormalize (raw t) (raw_ne t) : V))
   change Continuous (fun t : I => (‖raw t‖)⁻¹ • raw t)
   have hn : Continuous (fun t : I => ‖raw t‖) := continuous_norm.comp rawc
   have hi : Continuous (fun t : I => (‖raw t‖)⁻¹) := by
     fun_prop (disch := aesop)
   fun_prop
 have end0 : toS 0 = w := by
   apply Subtype.ext
   change (‖raw 0‖)⁻¹ • raw 0 = (w:V)
   have ar : raw 0 = (3/2:ℝ) • (w:V) := by
     dsimp [raw, bump]
     have asrc : (a (0:I) : V) = (w:V) := congrArg Subtype.val a.source
     rw [asrc]
     module
   rw [ar, norm_smul]
   have nw : ‖(w:V)‖ = 1 := by
     have h' := w.property; change dist (w:V) 0 = 1 at h'; simpa [dist_zero_right] using h'
   rw [nw]
   norm_num
   rw [smul_smul]
   norm_num
 have end1 : toS 1 = w := by
   apply Subtype.ext
   change (‖raw 1‖)⁻¹ • raw 1 = (w:V)
   have ar : raw 1 = (3/2:ℝ) • (w:V) := by
     dsimp [raw, bump]
     have asrc : (a (1:I) : V) = (w:V) := congrArg Subtype.val a.target
     rw [asrc]
     module
   rw [ar, norm_smul]
   have nw : ‖(w:V)‖ = 1 := by
     have h' := w.property; change dist (w:V) 0 = 1 at h'; simpa [dist_zero_right] using h'
   rw [nw]
   norm_num
   rw [smul_smul]
   norm_num
 -- Multiplying an antipodal equality back by the (nonzero) norm removes all
 -- divisions.  Keeping this little calculation out of the two cases below
 -- makes the plane equations quite transparent.
 have back {t:I} {y:V}
     (e : (‖raw t‖)⁻¹ • raw t = y) : raw t = ‖raw t‖ • y := by
   calc
     raw t = (‖raw t‖ * (‖raw t‖)⁻¹) • raw t := by
       rw [mul_inv_cancel₀ (norm_ne t), one_smul]
     _ = ‖raw t‖ • ((‖raw t‖)⁻¹ • raw t) := by rw [smul_smul]
     _ = _ := by rw [e]
 let c : Path w w := ⟨⟨toS, toSc⟩, end0, end1⟩
 refine ⟨c, ?_, ?_⟩
 · intro t eqn
   by_cases h0 : t = (0:I)
   · subst t
     have av : (a (0:I):V) = (w:V) := congrArg Subtype.val a.source
     change (toS 0 : V) = -(a (0:I) : V) at eqn
     have cv : (toS 0:V) = (w:V) := congrArg Subtype.val end0
     rw [cv, av] at eqn
     exact sphere_val_ne_neg_self w eqn
   · by_cases h1 : t = (1:I)
     · subst t
       have av : (a (1:I):V) = (w:V) := congrArg Subtype.val a.target
       change (toS 1 : V) = -(a (1:I) : V) at eqn
       have cv : (toS 1:V) = (w:V) := congrArg Subtype.val end1
       rw [cv, av] at eqn
       exact sphere_val_ne_neg_self w eqn
     · change ((‖raw t‖)⁻¹ • raw t) = -(a t : V) at eqn
       have br : raw t = ‖raw t‖ • (-(a t : V)) := back eqn
       have posb := bumppos t h0 h1
       have coeffpos : 0 < (‖raw t‖ + (1/2:ℝ)) := by
         have hn : 0 ≤ ‖raw t‖ := norm_nonneg _
         linarith
       have fe : (1/2:ℝ) * f (a t : V) + bump t =
                     ‖raw t‖ * (-(f (a t : V))) := by
         calc
           _ = f (raw t) := (fraw t).symm
           _ = f (‖raw t‖ • (-(a t : V))) := congrArg f br
           _ = _ := by simp
       have negfa : f (a t : V) < 0 := by
         nlinarith
       have noplane := ha t h0 h1 negfa
       apply noplane
       let k : ℝ := ‖raw t‖ + (1/2:ℝ)
       have kne : k ≠ 0 := ne_of_gt coeffpos
       have vec : k • (a t : V) = -(w:V) - (bump t) • u := by
         -- `br` is exactly this affine equation
         calc
           k • (a t : V) = k • (a t : V) - raw t + raw t := by module
           _ = k • (a t : V) - raw t +
                 ‖raw t‖ • (-(a t : V)) :=
                   congrArg (fun z : V => k • (a t : V) - raw t + z) br
           _ = -(w:V) - (bump t) • u := by
             dsimp [k, raw]
             module
       refine ⟨- k⁻¹, - (k⁻¹ * bump t), ?_⟩
       calc
         (a t : V) = k⁻¹ • (k • (a t : V)) := by
           rw [smul_smul]
           rw [inv_mul_cancel₀ kne]
           simp
         _ = k⁻¹ • (-(w:V) - (bump t) • u) := by rw [vec]
         _ = (- k⁻¹) • (w:V) + (- (k⁻¹ * bump t)) • u := by
           module
 · intro t eqn
   change (w:V) = -(c t : V) at eqn
   by_cases h0 : t = (0:I)
   · subst t
     have cv : (c (0:I):V) = (w:V) := congrArg Subtype.val end0
     rw [cv] at eqn
     exact sphere_val_ne_neg_self w eqn
   · by_cases h1 : t = (1:I)
     · subst t
       have cv : (c (1:I):V) = (w:V) := congrArg Subtype.val end1
       rw [cv] at eqn
       exact sphere_val_ne_neg_self w eqn
     · change (w:V) = - ((‖raw t‖)⁻¹ • raw t) at eqn
       have rev : (‖raw t‖)⁻¹ • raw t = -(w:V) := by
         -- negate `eqn`
         have q := congrArg Neg.neg eqn
         simpa using q.symm
       have br : raw t = ‖raw t‖ • (-(w:V)) := back rev
       have posb := bumppos t h0 h1
       have fe : (1/2:ℝ) * f (a t : V) + bump t = 0 := by
         calc
           _ = f (raw t) := (fraw t).symm
           _ = f (‖raw t‖ • (-(w:V))) := congrArg f br
           _ = _ := by simp [fw]
       have negfa : f (a t : V) < 0 := by linarith
       have noplane := ha t h0 h1 negfa
       apply noplane
       refine ⟨- (2:ℝ) * (‖raw t‖ + 1), -(2 * bump t), ?_⟩
       -- solve the remaining affine equation for `a`
       calc
         (a t : V) = (a t : V) - 2 • raw t +
               2 • raw t := by module
         _ = (a t : V) - 2 • raw t +
               2 • (‖raw t‖ • (-(w:V))) :=
                 congrArg (fun z : V => (a t : V) - 2 • raw t + 2 • z) br
         _ = (-(2:ℝ) * (‖raw t‖ + 1)) • (w:V) +
               (-(2 * bump t)) • u := by
           dsimp [raw]
           module
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/DirectionalAvoid.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckSeparation.lean
section
noncomputable section
open Set Topology TopologicalSpace CategoryTheory
open TopCat
open scoped Topology Manifold
namespace NonlinearThreeManifoldSupport
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

def chartLocalClosed (b : Y) (s : ℝ) : Set Y :=
  (chartAt E b).source ∩
    (chartAt E b) ⁻¹' {q : E | ‖q - (chartAt E b) b‖ ≤ s}

lemma chartLocalClosed_compact (b : Y) (A : ChartBall (E:=E) b)
    {s : ℝ} (hs : 0 ≤ s) (hsR : s < A.R) :
    IsCompact (chartLocalClosed (E:=E) b s) := by
  let F : (Metric.closedBall (0:E) s : Set E) → Y :=
    fun z => (chartAt E b).symm ((chartAt E b) b + (z:E))
  have targ (z : (Metric.closedBall (0:E) s : Set E)) :
      (chartAt E b) b + (z:E) ∈ (chartAt E b).target := by
    apply A.sub
    rw [Metric.mem_ball, dist_eq_norm]
    have hvec : (chartAt E b) b + (z:E) - (chartAt E b) b = (z:E) := by abel
    rw [hvec]
    have hz : ‖(z:E)‖ ≤ s := by
      have h := z.property
      rw [Metric.mem_closedBall] at h
      change dist (z:E) 0 ≤ s at h
      simpa using h
    exact lt_of_le_of_lt hz hsR
  have Fc : Continuous F := by
    let FF : (Metric.closedBall (0:E) s : Set E) →
       ((chartAt E b).target : Set E) := fun z =>
         ⟨(chartAt E b) b + (z:E), targ z⟩
    have ffc : Continuous FF := by
      apply continuous_induced_rng.2
      change Continuous (fun z : (Metric.closedBall (0:E) s : Set E) =>
        (chartAt E b) b + (z:E))
      fun_prop
    exact ((chartAt E b).symm.continuousOn.restrict).comp ffc
  have image : Set.range F = chartLocalClosed (E:=E) b s := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      refine ⟨(chartAt E b).symm.map_source (targ z), ?_⟩
      change ‖(chartAt E b) ((chartAt E b).symm ((chartAt E b) b + (z:E))) -
          (chartAt E b) b‖ ≤ s
      rw [(chartAt E b).right_inv (targ z)]
      have hz : ‖(z:E)‖ ≤ s := by
        have h := z.property
        rw [Metric.mem_closedBall] at h
        change dist (z:E) 0 ≤ s at h
        simpa using h
      simpa using hz
    · intro hy
      have ht : (chartAt E b) y = _ := rfl
      have mem : ((chartAt E b) y - (chartAt E b) b) ∈ Metric.closedBall (0:E) s := by
        
        rw [Metric.mem_closedBall]
        change dist ((chartAt E b) y - (chartAt E b) b) 0 ≤ s
        simpa using hy.2
      refine ⟨⟨_, mem⟩, ?_⟩
      change (chartAt E b).symm
        ((chartAt E b) b + ((chartAt E b) y - (chartAt E b) b)) = y
      have v : (chartAt E b) b + ((chartAt E b) y - (chartAt E b) b) =
          (chartAt E b) y := by abel
      rw [v]
      exact (chartAt E b).left_inv hy.1
  rw [← image]
  exact isCompact_range Fc

lemma chartLocalClosed_closed (b : Y) (A : ChartBall (E:=E) b)
    {s : ℝ} (hs : 0 ≤ s) (hsR : s < A.R) :
    IsClosed (chartLocalClosed (E:=E) b s) :=
  (chartLocalClosed_compact (E:=E) b A hs hsR).isClosed

lemma mem_closed_of_end_le (b : Y) (A : ChartBall (E:=E) b)
    {y : Y} (hy : y ∈ chartEndSet (E:=E) b A)
    {s : ℝ} (hs : ‖(chartAt E b) y - (chartAt E b) b‖ ≤ s) :
    y ∈ chartLocalClosed (E:=E) b s := ⟨hy.1, hs⟩


end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckSeparation.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/PunctureConnected.lean
section
noncomputable section
open Set Topology TopologicalSpace
open scoped Topology Manifold
namespace NonlinearThreeManifoldSupport
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma radialSet_isConnected (R : ℝ) (hR : 0 < R)
    (hrank : 1 < Module.rank ℝ E) :
    IsConnected (radialSet (E:=E) R) := by
  -- squash the complement of zero into the ball
  let g : E → E := fun x => (R / (1 + ‖x‖)) • x
  have gc : Continuous g := by
    have h : ∀ x : E, (1 + ‖x‖ : ℝ) ≠ 0 := by
      intro x
      have : 0 ≤ ‖x‖ := norm_nonneg x
      linarith
    dsimp [g]
    fun_prop
  have im : g '' ({(0:E)}ᶜ) = radialSet (E:=E) R := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have xn : x ≠ 0 := by simpa using hx
      have xp : 0 < ‖x‖ := norm_pos_iff.mpr xn
      have den : 0 < (1 + ‖x‖ : ℝ) := by linarith
      refine ⟨?_, ?_⟩
      · change g x ≠ 0
        exact smul_ne_zero (div_ne_zero (ne_of_gt hR) (ne_of_gt den)) xn
      · change ‖g x‖ < R
        dsimp [g]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR den)]
        rw [div_mul_eq_mul_div]
        exact (div_lt_iff₀ den).2 (by nlinarith [hR])
    · intro hy
      rcases hy with ⟨yn,hyR⟩
      have yp : 0 < ‖y‖ := norm_pos_iff.mpr yn
      have rp : 0 < R - ‖y‖ := sub_pos.mpr hyR
      let x : E := (R - ‖y‖)⁻¹ • y
      have xn : x ≠ 0 := smul_ne_zero (inv_ne_zero (ne_of_gt rp)) yn
      refine ⟨x, (by simpa using xn), ?_⟩
      dsimp [g, x]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr rp)]
      rw [smul_smul]
      have hcalc : R / (1 + (R - ‖y‖)⁻¹ * ‖y‖) * (R - ‖y‖)⁻¹ = (1:ℝ) := by
        have nz : R - ‖y‖ ≠ 0 := ne_of_gt rp
        field_simp
        ring
      rw [hcalc, one_smul]
  have pc := isPathConnected_compl_singleton_of_one_lt_rank hrank (0:E)
  have ic : IsConnected (g '' ({(0:E)}ᶜ)) := (pc.image gc).isConnected
  rw [← im]
  exact ic

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open Set Topology TopologicalSpace
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

lemma chartEnd_connected (b : Y) (A : ChartBall (E:=E) b)
    (hrank : 1 < Module.rank ℝ E) :
    ConnectedSpace (chartEnd (E:=E) b A : Type _) := by
  apply (chartEndHomeo (E:=E) b A).connectedSpace_iff.mpr
  -- a subtype is connected precisely when its underlying set is connected
  exact isConnected_iff_connectedSpace.mp
    (radialSet_isConnected (E:=E) A.R A.pos hrank)
end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open Set Topology TopologicalSpace
open scoped Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

/-- Removing a point does not disconnect a connected charted manifold modelled
on a real vector space of rank greater than one. Only a single chart is used:
its punctured ball is connected. A clopen subset of the complement is therefore
constant on that ball; adjoining (or not adjoining) the centre makes it a
clopen subset of the whole manifold. -/
theorem punctured_connected [ConnectedSpace Y]
    (b : Y) (A : ChartBall (E:=E) b)
    (hrank : 1 < Module.rank ℝ E) :
    ConnectedSpace (({b}:Set Y)ᶜ : Set Y) := by
  classical
  let P : Type _ := (({b}:Set Y)ᶜ : Set Y)
  let T : Type _ := (chartEnd (E:=E) b A : Type _)
  letI tc : ConnectedSpace T := chartEnd_connected (E:=E) b A hrank
  let inc : T → P := fun z => z.1
  have incc : Continuous inc := by
    dsimp [inc, T, P]
    fun_prop
  have neP : Nonempty P := by
    let z : T := Classical.choice (ConnectedSpace.toNonempty)
    exact ⟨inc z⟩
  -- openness of the punctured block inclusion
  have openP : IsOpen ({b}ᶜ : Set Y) := isOpen_compl_singleton
  have valopen : IsOpenEmbedding (fun p : P => (p:Y)) :=
    openP.isOpenEmbedding_subtypeVal
  rw [connectedSpace_iff_clopen]
  refine ⟨neP, ?_⟩
  intro s hs
  have pull : IsClopen (inc ⁻¹' s) := hs.preimage incc
  have two : inc ⁻¹' s = (∅ : Set T) ∨ inc ⁻¹' s = Set.univ :=
    (connectedSpace_iff_clopen.mp (inferInstance : ConnectedSpace T)).2 _ pull
  -- images of open subsets of the punctured block are open in the block
  -- manifold itself
  have opens_image {q : Set P} (hq : IsOpen q) :
      IsOpen ((fun p : P => (p:Y)) '' q) := valopen.isOpenMap q hq
  have all_or : ∀ (t : Set P), IsClopen t →
      (∀ z : T, inc z ∈ t) → t = (Set.univ : Set P) := by
    intro t ht hinc
    let S : Set Y := {b} ∪ ((fun p : P => (p:Y)) '' t)
    let C : Set P := tᶜ
    have so : IsOpen t := ht.2
    have co : IsOpen C := ht.1.isOpen_compl
    have endsub : ∀ z : T, (z.1.1:Y) ∈
          ((fun p : P => (p:Y)) '' t) := by
      intro z; exact ⟨inc z, hinc z, rfl⟩
    have ballsub : chartLocalBall (E:=E) b A.R ⊆ S := by
      intro y hy
      by_cases yy : y = b
      · left; simpa [yy]
      · right
        have ee : y ∈ chartEndSet (E:=E) b A :=
          chartLocalBall_end (E:=E) A A.pos (le_rfl) hy yy
        let z : T := ⟨⟨y, chartEndSet_sub_compl (E:=E) b A ee⟩, ee⟩
        exact endsub z
    have bmem : b ∈ chartLocalBall (E:=E) b A.R :=
      chartLocalBall_mem (E:=E) b A.pos
    have Sunion : S =
        ((fun p : P => (p:Y)) '' t) ∪ chartLocalBall (E:=E) b A.R := by
      apply Set.Subset.antisymm
      · intro y hy
        rcases hy with hy|hy
        · right
          have yb : y = b := by simpa using hy
          simpa [yb] using bmem
        · left; exact hy
      · intro y hy
        rcases hy with hy|hy
        · right; exact hy
        · exact ballsub hy
    have Sopen : IsOpen S := by
      rw [Sunion]
      exact (opens_image so).union (chartLocalBall_open (E:=E) b A.R)
    have Scompl : Sᶜ = ((fun p : P => (p:Y)) '' C) := by
      ext y
      constructor
      · intro hy
        have yb : y ≠ b := by
          intro e; apply hy; left; simpa [e]
        let p : P := ⟨y, by simpa using yb⟩
        have pn : p ∉ t := by
          intro hp; apply hy; right; exact ⟨p,hp,rfl⟩
        exact ⟨p, pn, rfl⟩
      · rintro ⟨p,hp,rfl⟩ hbad
        rcases hbad with hb|hb
        · have : (p:Y) ≠ b := by
            intro e; exact p.property (by simpa [e])
          exact this (by simpa using hb)
        · rcases hb with ⟨q,hq,he⟩
          have qq : q = p := Subtype.ext he
          exact hp (qq ▸ hq)
    have Sclosed : IsClosed S := by
      rw [← isOpen_compl_iff]
      rw [Scompl]
      exact opens_image co
    have cl : IsClopen S := ⟨Sclosed, Sopen⟩
    have alt : S = ∅ ∨ S = Set.univ :=
      (connectedSpace_iff_clopen.mp (inferInstance : ConnectedSpace Y)).2 _ cl
    have Su : S = (Set.univ : Set Y) := alt.resolve_left (by
      intro he; have : b ∈ S := by left; rfl
      simpa [he] using this)
    apply Set.eq_univ_of_forall
    intro p
    have memS : (p:Y) ∈ S := by rw [Su]; trivial
    rcases memS with hm|hm
    · -- the punctured point is not the centre
      exfalso
      have ne : (p:Y) ≠ b := by
        intro e; exact p.property (by simpa [e])
      exact ne (by simpa using hm)
    · rcases hm with ⟨q,hq,eq⟩
      have eqq : q = p := Subtype.ext eq
      exact eqq ▸ hq
  rcases two with empty | full
  · left
    -- no end lies in s; apply the preceding argument to its complement
    have avoid : ∀ z : T, inc z ∈ (sᶜ : Set P) := by
      intro z hz
      have : z ∈ (∅ : Set T) := by
        rw [← empty]
        exact hz
      simpa using this
    have hccl : IsClopen (sᶜ : Set P) :=
      ⟨hs.2.isClosed_compl, hs.1.isOpen_compl⟩
    have cu : sᶜ = (Set.univ : Set P) := all_or _ hccl avoid
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨p,hp⟩
    have hnot : p ∈ (sᶜ : Set P) := by rw [cu]; trivial
    exact hnot hp
  · right
    apply all_or s hs
    intro z
    have : z ∈ (Set.univ : Set T) := trivial
    rw [← full] at this
    exact this
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/PunctureConnected.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/LoopCut.lean
section
noncomputable section
open scoped Topology
open Topology
namespace NonlinearThreeManifoldSupport
/-- Only loops at the chosen initial sheet, rather than all pairs of end
sheets, are needed for the pointed path comparison.  Work in the path
quotient so reassociation and cancellation are just groupoid simp. -/
lemma start_paths_of_loops_at
    {E : Type*} [TopologicalSpace E] (e : E)
    (H : ∀ L : Path e e, Path.Homotopic L (Path.refl e)) :
    ∀ (z : E) (a b : Path e z), Path.Homotopic a b := by
  intro z a b
  -- the loop `a · b⁻¹` is trivial by the pointed assumption
  have hloop := H (a.trans b.symm)
  have heq :
      Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk a)
        (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk b)) =
        Path.Homotopic.Quotient.refl e := by
    -- replace representatives of trans and symm
    
    -- all three operations on representatives reduce definitionally
    change @Eq (Path.Homotopic.Quotient e e)
      (Path.Homotopic.Quotient.mk (a.trans b.symm))
      (Path.Homotopic.Quotient.mk (Path.refl e))
    exact Quotient.sound hloop
  have hab : (Path.Homotopic.Quotient.mk a) =
        (Path.Homotopic.Quotient.mk b) := by
    -- append b and simplify in the fundamental groupoid
    calc
      Path.Homotopic.Quotient.mk a =
          (Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk a)
              (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk b)))
            (Path.Homotopic.Quotient.mk b)) := by simp
      _ = Path.Homotopic.Quotient.mk b := by rw [heq]; simp
  exact Path.Homotopic.Quotient.exact hab

/-- Endpoint version of that pointed cut. -/
lemma IsCoveringMap.endpoint_inj_of_loops_at
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : IsCoveringMap p) (e : E)
    (H : ∀ L : Path e e, Path.Homotopic L (Path.refl e)) :
    Function.Injective
      (fun a : FundamentalGroup X (p e) =>
        cov.monodromy a (⟨e, rfl⟩ : p ⁻¹' ({p e} : Set X))) := by
  exact IsCoveringMap.endpoint_inj_of_start_paths cov e
    (start_paths_of_loops_at e H)
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/LoopCut.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckT2.lean
section
open Set Topology TopologicalSpace CategoryTheory
open TopCat
open scoped Topology Manifold
noncomputable section
namespace NonlinearThreeManifoldSupport
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

/-- The points of the punctured block outside the closed core of radius `R/2`.
We use this only as a neighbourhood of points which are not on the chart end.
It is open in the punctured block, even though the latter has no chosen metric. -/
def punctFar (b : Y) (s : ℝ) :
    Set (({b} : Set Y)ᶜ : Set Y) :=
  (fun x : (({b}:Set Y)ᶜ : Set Y) => (x:Y)) ⁻¹'
    (chartLocalClosed (E:=E) b s)ᶜ

lemma punctFar_open (b : Y) (A : ChartBall (E:=E) b)
    {s : ℝ} (hs : 0 ≤ s) (hsR : s < A.R) :
    IsOpen (punctFar (E:=E) b s) := by
  exact (chartLocalClosed_closed (E:=E) b A hs hsR).isOpen_compl.preimage
    continuous_subtype_val

lemma punct_not_end_far (b : Y) (A : ChartBall (E:=E) b)
    (x : (({b}:Set Y)ᶜ : Set Y))
    (hx : ¬ (x:Y) ∈ chartEndSet (E:=E) b A) :
    x ∈ punctFar (E:=E) b (A.R/2) := by
  -- A point in the half closed ball, other than the removed centre, is
  -- automatically on the chart end.
  intro h
  rcases h with ⟨hs, hn⟩
  have nz : (chartAt E b) (x:Y) - (chartAt E b) b ≠ (0:E) := by
    intro h0
    have eq : (chartAt E b) (x:Y) = (chartAt E b) b := sub_eq_zero.mp h0
    have xb : (x:Y) = b := (chartAt E b).injOn hs (mem_chart_source E b) eq
    exact x.property (by simpa [xb])
  apply hx
  refine ⟨hs, ?_⟩
  refine ⟨nz, ?_⟩
  exact lt_of_le_of_lt hn (by linarith [A.pos])

lemma end_mem_far_norm_gt (b : Y) (A : ChartBall (E:=E) b)
    (v : (chartEnd (E:=E) b A : Type _))
    (hv : (v.1 : (({b}:Set Y)ᶜ : Set Y)) ∈
       punctFar (E:=E) b (A.R/2)) :
    A.R/2 < ‖(chartAt E b) (v.1.1:Y) - (chartAt E b) b‖ := by
  by_contra hle
  have hle' : ‖(chartAt E b) (v.1.1:Y) - (chartAt E b) b‖ ≤ A.R/2 :=
    le_of_not_gt hle
  exact hv ⟨v.property.1, hle'⟩

/-- On the far neighbourhoods on the two sides equality in the colimit is
impossible.  A transition must be made on the chart end. There the two
coordinate radii add to `R`, so two radii both greater than `R/2` cannot be
paired. -/
lemma doubleGlue_far_disjoint
    (b : Y) (A : ChartBall (E:=E) b) :
    let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
    let V : Opens X := chartEnd (E:=E) b A
    let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
    let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
    let D : TopCat.GlueData.{0} := doubleGlueData X V e he
    Disjoint
      (D.toGlueData.ι false '' punctFar (E:=E) b (A.R/2))
      (D.toGlueData.ι true '' punctFar (E:=E) b (A.R/2)) := by
  classical
  dsimp
  let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
  let V : Opens X := chartEnd (E:=E) b A
  let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
  let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
  let D : TopCat.GlueData.{0} := doubleGlueData X V e he
  rw [Set.disjoint_left]
  intro q hq0 hq1
  rcases hq0 with ⟨x,hxf,hxq⟩
  rcases hq1 with ⟨y,hyf,hyq⟩
  change (({b}:Set Y)ᶜ : Set Y) at x
  change (({b}:Set Y)ᶜ : Set Y) at y
  have eqxy : D.toGlueData.ι false x = D.toGlueData.ι true y :=
    hxq.trans hyq.symm
  rcases (D.ι_eq_iff_rel false true x y).mp eqxy with ⟨v,hv,hv'⟩
  change (v.1) = x at hv
  change ((e v).1) = y at hv'
  have fx : (v.1 : (({b}:Set Y)ᶜ : Set Y)) ∈ punctFar (E:=E) b (A.R/2) := by
    change (v.1.1 : Y) ∈ (chartLocalClosed (E:=E) b (A.R/2))ᶜ
    have hh : (x:Y) ∈ (chartLocalClosed (E:=E) b (A.R/2))ᶜ := hxf
    have hxV : (v.1 : (({b}:Set Y)ᶜ : Set Y)) = x := hv
    have vv : (v.1.1:Y) = (x:Y) := congrArg (fun z : (({b}:Set Y)ᶜ : Set Y) => (z:Y)) hxV
    rw [vv]
    exact hh
  have fy : ((e v).1 : (({b}:Set Y)ᶜ : Set Y)) ∈ punctFar (E:=E) b (A.R/2) := by
    change ((e v).1.1 : Y) ∈ (chartLocalClosed (E:=E) b (A.R/2))ᶜ
    have hh : (y:Y) ∈ (chartLocalClosed (E:=E) b (A.R/2))ᶜ := hyf
    have hyV : ((e v).1 : (({b}:Set Y)ᶜ : Set Y)) = y := hv'
    have vv : ((e v).1.1:Y) = (y:Y) := congrArg (fun z : (({b}:Set Y)ᶜ : Set Y) => (z:Y)) hyV
    rw [vv]
    exact hh
  have nx := end_mem_far_norm_gt (E:=E) b A v fx
  have ny := end_mem_far_norm_gt (E:=E) b A (e v) fy
  have flip := chartEndFlip_size (E:=E) b A v
  -- these say `R/2 < n` and `R/2 < R-n`.
  dsimp [e] at hv' fy ny
  linarith

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open Set Topology TopologicalSpace CategoryTheory TopCat
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

/-- The radial double is separated.  The possible non-Hausdorffness of doubling
an arbitrary open subset is just the double-boundary phenomenon.  For a chart
end one boundary is the removed centre: its radial exchange takes radii near
`R` to radii near zero, so it is not present on the other punctured patch. -/
theorem doubleGlue_chartEnd_t2
    {b : Y} (A : ChartBall (E:=E) b) :
    let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
    let V : Opens X := chartEnd (E:=E) b A
    let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
    let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
    T2Space (doubleGlueData X V e he).toGlueData.glued := by
  classical
  dsimp
  let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
  let V : Opens X := chartEnd (E:=E) b A
  let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
  let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
  let D : TopCat.GlueData.{0} := doubleGlueData X V e he
  -- within a single patch separation is just separation in the block: the
  -- chart images are open embeddings.
  have same (k : Bool) (x y : (({b}:Set Y)ᶜ : Set Y))
      (hxy : D.toGlueData.ι k x ≠ D.toGlueData.ι k y) :
      ∃ u v : Set D.toGlueData.glued,
        IsOpen u ∧ IsOpen v ∧
        D.toGlueData.ι k x ∈ u ∧ D.toGlueData.ι k y ∈ v ∧ Disjoint u v := by
    have xy : x ≠ y := by
      intro h; exact hxy (congrArg _ h)
    obtain ⟨u,v,hu,hv,hxu,hyv,hd⟩ := t2_separation xy
    refine ⟨ D.toGlueData.ι k '' u,
             D.toGlueData.ι k '' v, ?_, ?_, ?_, ?_, ?_ ⟩
    · exact (D.ι_isOpenEmbedding k).isOpenMap u hu
    · exact (D.ι_isOpenEmbedding k).isOpenMap v hv
    · exact ⟨x,hxu,rfl⟩
    · exact ⟨y,hyv,rfl⟩
    · exact Set.disjoint_image_of_injective (D.ι_injective k) hd
  refine ⟨?_⟩
  intro q₁ q₂ hq
  obtain ⟨i,x,hx⟩ := D.ι_jointly_surjective q₁
  obtain ⟨j,y,hy⟩ := D.ι_jointly_surjective q₂
  -- replace the arbitrary representatives by patch representatives
  subst q₁
  subst q₂
  change Bool at i
  change Bool at j
  rcases i with _|_ <;> rcases j with _|_
  · -- same (false) chart
    change (({b}:Set Y)ᶜ : Set Y) at x
    change (({b}:Set Y)ᶜ : Set Y) at y
    exact same false x y hq
  · -- the two different charts
    change (({b}:Set Y)ᶜ : Set Y) at x
    change (({b}:Set Y)ᶜ : Set Y) at y
    -- if the representative on the first side is in the transition end,
    -- move it to the second chart and use the same-chart case.
    by_cases ex : (x:Y) ∈ chartEndSet (E:=E) b A
    · let vx : (V : Type) := ⟨x, ex⟩
      have eq : D.toGlueData.ι true ((e vx).1) =
          D.toGlueData.ι false x := by
        have h := D.toGlueData.glue_condition_apply false true vx
        change D.toGlueData.ι true ((e vx).1) = D.toGlueData.ι false (vx.1) at h
        simpa [vx] using h
      have hn : D.toGlueData.ι true ((e vx).1) ≠
          D.toGlueData.ι true y := by
        intro h
        exact hq (eq ▸ h)
      obtain ⟨u,v,hu,hv,hxu,hyv,hd⟩ := same true ((e vx).1) y hn
      exact ⟨u,v,hu,hv, eq ▸ hxu, hyv, hd⟩
    · -- likewise if the second representative is on the end
      by_cases ey : (y:Y) ∈ chartEndSet (E:=E) b A
      · let vy : (V : Type) := ⟨y, ey⟩
        have eq : D.toGlueData.ι false ((e vy).1) =
            D.toGlueData.ι true y := by
          have h := D.toGlueData.glue_condition_apply true false vy
          change D.toGlueData.ι false ((e vy).1) =
            D.toGlueData.ι true (vy.1) at h
          simpa [vy] using h
        have hn : D.toGlueData.ι false x ≠
            D.toGlueData.ι false ((e vy).1) := by
          intro h
          exact hq (h.trans eq)
        obtain ⟨u,v,hu,hv,hxu,hyv,hd⟩ :=
          same false x ((e vy).1) hn
        exact ⟨u,v,hu,hv,hxu, eq ▸ hyv, hd⟩
      · -- neither point is on the end; their far neighbourhoods cannot meet
        let W : Set (({b}:Set Y)ᶜ : Set Y) := punctFar (E:=E) b (A.R/2)
        refine ⟨D.toGlueData.ι false '' W,
                D.toGlueData.ι true '' W, ?_, ?_, ?_, ?_, ?_⟩
        · exact (D.ι_isOpenEmbedding false).isOpenMap W
            (punctFar_open (E:=E) b A (by linarith [A.pos])
              (by linarith [A.pos]))
        · exact (D.ι_isOpenEmbedding true).isOpenMap W
            (punctFar_open (E:=E) b A (by linarith [A.pos])
              (by linarith [A.pos]))
        · exact ⟨x, punct_not_end_far (E:=E) b A x ex, rfl⟩
        · exact ⟨y, punct_not_end_far (E:=E) b A y ey, rfl⟩
        · exact doubleGlue_far_disjoint (E:=E) b A
  · -- true/false is the symmetric situation; swap the open sets.
    change (({b}:Set Y)ᶜ : Set Y) at x
    change (({b}:Set Y)ᶜ : Set Y) at y
    -- repeat the preceding argument with names interchanged
    by_cases ey : (y:Y) ∈ chartEndSet (E:=E) b A
    · let vy : (V : Type) := ⟨y, ey⟩
      have eq : D.toGlueData.ι true x = D.toGlueData.ι true ((e vy).1) → False := by
        intro h
        apply hq
        have t := D.toGlueData.glue_condition_apply false true vy
        change D.toGlueData.ι true ((e vy).1) = D.toGlueData.ι false (vy.1) at t
        -- the required equality is `ι true x = ι false y`
        exact h.trans (by simpa [vy] using t)
      have hn : D.toGlueData.ι true x ≠ D.toGlueData.ι true ((e vy).1) := eq
      obtain ⟨u,v,hu,hv,hxu,hyv,hd⟩ := same true x ((e vy).1) hn
      have eqy : D.toGlueData.ι true ((e vy).1) =
          D.toGlueData.ι false y := by
        have t := D.toGlueData.glue_condition_apply false true vy
        change D.toGlueData.ι true ((e vy).1) = D.toGlueData.ι false (vy.1) at t
        simpa [vy] using t
      exact ⟨u,v,hu,hv,hxu, eqy ▸ hyv, hd⟩
    · by_cases ex : (x:Y) ∈ chartEndSet (E:=E) b A
      · let vx : (V : Type) := ⟨x, ex⟩
        have eqx : D.toGlueData.ι false ((e vx).1) =
            D.toGlueData.ι true x := by
          have t := D.toGlueData.glue_condition_apply true false vx
          change D.toGlueData.ι false ((e vx).1) = D.toGlueData.ι true (vx.1) at t
          simpa [vx] using t
        have hn : D.toGlueData.ι false ((e vx).1) ≠
            D.toGlueData.ι false y := by
          intro h
          exact hq (eqx.symm.trans h)
        obtain ⟨u,v,hu,hv,hxu,hyv,hd⟩ := same false ((e vx).1) y hn
        exact ⟨u,v,hu,hv, eqx ▸ hxu, hyv, hd⟩
      · -- image-neighbourhoods on the outside, reversed
        let W : Set (({b}:Set Y)ᶜ : Set Y) := punctFar (E:=E) b (A.R/2)
        have d0 : Disjoint (D.toGlueData.ι false '' W)
                         (D.toGlueData.ι true '' W) :=
          doubleGlue_far_disjoint (E:=E) b A
        refine ⟨D.toGlueData.ι true '' W,
                D.toGlueData.ι false '' W, ?_, ?_, ?_, ?_, d0.symm⟩
        · exact (D.ι_isOpenEmbedding true).isOpenMap W
            (punctFar_open (E:=E) b A (by linarith [A.pos])
              (by linarith [A.pos]))
        · exact (D.ι_isOpenEmbedding false).isOpenMap W
            (punctFar_open (E:=E) b A (by linarith [A.pos])
              (by linarith [A.pos]))
        · exact ⟨x, punct_not_end_far (E:=E) b A x ex, rfl⟩
        · exact ⟨y, punct_not_end_far (E:=E) b A y ey, rfl⟩
  · -- same (true) chart
    change (({b}:Set Y)ᶜ : Set Y) at x
    change (({b}:Set Y)ᶜ : Set Y) at y
    exact same true x y hq
end NonlinearThreeManifoldSupport

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckT2.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckPinch.lean
section
open scoped Topology Manifold
open Set Topology TopologicalSpace CategoryTheory TopCat
noncomputable section
set_option maxHeartbeats 3000000
namespace NonlinearThreeManifoldSupport
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

/- A small cut-off used on the first half of the neck.  It is zero up to
radius R/2 and is the identity coefficient from radius 3R/4 on. -/
private def __NeckPinch_neckScale (R r : ℝ) : ℝ :=
  min 1 (max 0 ((r - R/2) / (R/4)))

private lemma __NeckPinch_neckScale_cont (R : ℝ) : Continuous (fun r : ℝ => __NeckPinch_neckScale R r) := by
  unfold __NeckPinch_neckScale
  fun_prop
private lemma __NeckPinch_neckScale_nonneg (R r : ℝ) : 0 ≤ __NeckPinch_neckScale R r := by
  unfold __NeckPinch_neckScale
  have h : 0 ≤ max 0 ((r - R/2)/(R/4)) := le_max_left _ _
  exact le_min (by norm_num) h -- oops min lower bound
private lemma __NeckPinch_neckScale_le (R r : ℝ) : __NeckPinch_neckScale R r ≤ 1 := by
  unfold __NeckPinch_neckScale
  exact min_le_left _ _
private lemma __NeckPinch_neckScale_zero {R r : ℝ} (h : r ≤ R/2) (hR : 0 < R) :
    __NeckPinch_neckScale R r = 0 := by
  unfold __NeckPinch_neckScale
  have den : 0 < R/4 := by linarith
  have q : (r - R/2) / (R/4) ≤ 0 := (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (le_of_lt den))
  have mx : max 0 ((r - R/2) / (R/4)) = 0 := max_eq_left q
  rw [mx]
  norm_num
private lemma __NeckPinch_neckScale_one {R r : ℝ} (h : 3*R/4 ≤ r) (hR : 0 < R) :
    __NeckPinch_neckScale R r = 1 := by
  unfold __NeckPinch_neckScale
  have den : 0 < R/4 := by linarith
  have ge : (1:ℝ) ≤ (r - R/2) / (R/4) := by
    apply (le_div_iff₀ den).2
    linarith
  have mx : (1:ℝ) ≤ max 0 ((r - R/2) / (R/4)) := le_trans ge (le_max_right _ _)
  exact min_eq_left mx

private def __NeckPinch_neckVec (R : ℝ) (z : E) : E := (__NeckPinch_neckScale R ‖z‖) • z
private lemma __NeckPinch_neckVec_cont (R : ℝ) : Continuous (__NeckPinch_neckVec (E:=E) R) := by
  unfold __NeckPinch_neckVec
  exact ((__NeckPinch_neckScale_cont R).comp continuous_norm).smul continuous_id
private lemma __NeckPinch_neckVec_norm_le (R : ℝ) (z : E) : ‖__NeckPinch_neckVec R z‖ ≤ ‖z‖ := by
  rw [__NeckPinch_neckVec, norm_smul, Real.norm_eq_abs, abs_of_nonneg (__NeckPinch_neckScale_nonneg _ _)]
  have h0 := __NeckPinch_neckScale_nonneg R ‖z‖
  have h1 := __NeckPinch_neckScale_le R ‖z‖
  nlinarith [norm_nonneg z]
private lemma __NeckPinch_neckVec_zero {R : ℝ} (hR : 0 < R) {z : E} (h : ‖z‖ ≤ R/2) :
    __NeckPinch_neckVec R z = 0 := by
  rw [__NeckPinch_neckVec, __NeckPinch_neckScale_zero h hR, zero_smul]
private lemma __NeckPinch_neckVec_id {R : ℝ} (hR : 0 < R) {z : E} (h : 3*R/4 ≤ ‖z‖) :
    __NeckPinch_neckVec R z = z := by
  rw [__NeckPinch_neckVec, __NeckPinch_neckScale_one h hR, one_smul]

/-- A self map of a block, squeezed near the distinguished point. The cut-off
makes it literally the identity near the rim of the chosen chart; this is the
minor detail which lets the opposite half of the pinch be constant on an
open neighbourhood of the missing point. -/
noncomputable def neckShrink (b : Y) (A : ChartBall (E:=E) b) (y : Y) : Y := by
  classical
  exact if h : y ∈ chartLocalBall (E:=E) b A.R then
    (chartAt E b).symm ((chartAt E b) b +
      __NeckPinch_neckVec (E:=E) A.R ((chartAt E b) y - (chartAt E b) b))
  else y

private lemma __NeckPinch_neckShrink_target (b : Y) (A : ChartBall (E:=E) b)
    {y : Y} (hy : y ∈ chartLocalBall (E:=E) b A.R) :
    (chartAt E b) b +
       __NeckPinch_neckVec (E:=E) A.R ((chartAt E b) y - (chartAt E b) b)
       ∈ (chartAt E b).target := by
  apply A.sub
  rw [Metric.mem_ball, dist_eq_norm]
  have v : (chartAt E b) b + __NeckPinch_neckVec (E:=E) A.R
       ((chartAt E b) y - (chartAt E b) b) - (chartAt E b) b =
       __NeckPinch_neckVec (E:=E) A.R ((chartAt E b) y - (chartAt E b) b) := by abel
  rw [v]
  exact lt_of_le_of_lt (__NeckPinch_neckVec_norm_le A.R _) hy.2

private lemma __NeckPinch_neckShrink_formula_cont (b : Y) (A : ChartBall (E:=E) b) :
    ContinuousOn (fun y : Y =>
      (chartAt E b).symm ((chartAt E b) b +
        __NeckPinch_neckVec (E:=E) A.R ((chartAt E b) y - (chartAt E b) b)))
      (chartLocalBall (E:=E) b A.R) := by
  -- factor both partial charts through their open source/target
  let src : (chartLocalBall (E:=E) b A.R : Set Y) →
      ((chartAt E b).source : Set Y) := fun u => ⟨u.1, u.property.1⟩
  have srcc : Continuous src := by
    apply continuous_induced_rng.2
    exact continuous_subtype_val
  have coord : Continuous (fun u : (chartLocalBall (E:=E) b A.R : Set Y) =>
      (chartAt E b) (u:Y)) := by
    exact ((chartAt E b).continuousOn.restrict).comp srcc
  let tar : (chartLocalBall (E:=E) b A.R : Set Y) →
      ((chartAt E b).target : Set E) := fun u =>
       ⟨(chartAt E b) b + __NeckPinch_neckVec (E:=E) A.R
          ((chartAt E b) (u:Y) - (chartAt E b) b),
        __NeckPinch_neckShrink_target (E:=E) b A u.property⟩
  have tarc : Continuous tar := by
    apply continuous_induced_rng.2
    change Continuous (fun u : (chartLocalBall (E:=E) b A.R : Set Y) =>
      (chartAt E b) b + __NeckPinch_neckVec (E:=E) A.R
          ((chartAt E b) (u:Y) - (chartAt E b) b))
    exact continuous_const.add ((__NeckPinch_neckVec_cont (E:=E) A.R).comp
      (coord.sub continuous_const))
  have fc : Continuous (fun u : (chartLocalBall (E:=E) b A.R : Set Y) =>
      (chartAt E b).symm
        ((chartAt E b) b + __NeckPinch_neckVec (E:=E) A.R
          ((chartAt E b) (u:Y) - (chartAt E b) b))) :=
    ((chartAt E b).symm.continuousOn.restrict).comp tarc
  exact (continuousOn_iff_continuous_restrict).2 fc

lemma neckShrink_of_small (b : Y) (A : ChartBall (E:=E) b)
    {y : Y} (hy : y ∈ chartEndSet (E:=E) b A)
    (hsmall : ‖(chartAt E b) y - (chartAt E b) b‖ ≤ A.R/2) :
    neckShrink (E:=E) b A y = b := by
  have hl : y ∈ chartLocalBall (E:=E) b A.R := ⟨hy.1, hy.2.2⟩
  rw [neckShrink, dif_pos hl, __NeckPinch_neckVec_zero (E:=E) A.pos hsmall]
  simp

lemma neckShrink_of_large (b : Y) (A : ChartBall (E:=E) b)
    {y : Y} (hy : y ∈ chartLocalBall (E:=E) b A.R)
    (hl : 3*A.R/4 ≤ ‖(chartAt E b) y - (chartAt E b) b‖) :
    neckShrink (E:=E) b A y = y := by
  rw [neckShrink, dif_pos hy, __NeckPinch_neckVec_id (E:=E) A.pos hl]
  have v : (chartAt E b) b + ((chartAt E b) y - (chartAt E b) b) =
      (chartAt E b) y := by abel
  rw [v]
  exact (chartAt E b).left_inv hy.1

/-- The squeezed map is continuous globally, not only on the chart. Outside a
closed subball it is literally the identity. -/
lemma neckShrink_continuous (b : Y) (A : ChartBall (E:=E) b) :
    Continuous (neckShrink (E:=E) b A) := by
  -- continuity is local; use the open big chart and the complement of a
  -- slightly smaller closed ball
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ chartLocalBall (E:=E) b A.R
  · have op := chartLocalBall_open (E:=E) b A.R
    have ev : (neckShrink (E:=E) b A) =ᶠ[𝓝 y]
        (fun t : Y => (chartAt E b).symm ((chartAt E b) b +
          __NeckPinch_neckVec (E:=E) A.R ((chartAt E b) t - (chartAt E b) b))) := by
      filter_upwards [op.mem_nhds hy] with z hz
      simp [neckShrink, hz]
    exact (((__NeckPinch_neckShrink_formula_cont (E:=E) b A y hy).continuousAt
        (chartLocalBall_open (E:=E) b A.R |>.mem_nhds hy)).congr_of_eventuallyEq ev)
  · let s : ℝ := 7*A.R/8
    have hs0 : 0 ≤ s := by dsimp [s]; linarith [A.pos]
    have hsR : s < A.R := by dsimp [s]; linarith [A.pos]
    let T : Set Y := (chartLocalClosed (E:=E) b s)ᶜ
    have Top : IsOpen T := (chartLocalClosed_closed (E:=E) b A hs0 hsR).isOpen_compl
    have hym : y ∈ T := by
      intro hh
      exact hy ⟨hh.1, lt_of_le_of_lt hh.2 hsR⟩
    have eqid : (neckShrink (E:=E) b A) =ᶠ[𝓝 y] (fun t : Y => t) := by
      filter_upwards [Top.mem_nhds hym] with z hz
      classical
      by_cases hz' : z ∈ chartLocalBall (E:=E) b A.R
      · have lg : 3*A.R/4 ≤ ‖(chartAt E b) z - (chartAt E b) b‖ := by
          by_contra hn
          have le' : ‖(chartAt E b) z - (chartAt E b) b‖ < 7*A.R/8 := by
            have : ‖(chartAt E b) z - (chartAt E b) b‖ < 3*A.R/4 := lt_of_not_ge hn
            linarith [A.pos]
          have : z ∈ chartLocalClosed (E:=E) b s := ⟨hz'.1, le_of_lt (by simpa [s] using le')⟩
          exact hz this
        exact neckShrink_of_large (E:=E) b A hz' lg
      · simp [neckShrink, hz']
    exact (continuousAt_id.congr_of_eventuallyEq eqid) -- orientation?


/-- Squeezing a point of the coordinate ball stays in that same ball.  The
slightly boring source part is useful: it lets us lift paths through a pinch
back to a genuinely convex ball rather than juggling partial chart maps. -/
lemma neckShrink_mem_local (b : Y) (A : ChartBall (E:=E) b)
    {y : Y} (hy : y ∈ chartLocalBall (E:=E) b A.R) :
    neckShrink (E:=E) b A y ∈ chartLocalBall (E:=E) b A.R := by
  classical
  let z : E := (chartAt E b) b +
       __NeckPinch_neckVec (E:=E) A.R ((chartAt E b) y - (chartAt E b) b)
  have zt : z ∈ (chartAt E b).target := by
    dsimp [z]
    exact __NeckPinch_neckShrink_target (E:=E) b A hy
  have zs : (chartAt E b).symm z ∈ (chartAt E b).source :=
    (chartAt E b).map_target zt
  have coord : (chartAt E b) ((chartAt E b).symm z) = z :=
    (chartAt E b).right_inv zt
  rw [neckShrink, dif_pos hy]
  change (chartAt E b).symm z ∈ chartLocalBall (E:=E) b A.R
  change (chartAt E b).symm z ∈ (chartAt E b).source ∩
    (chartAt E b) ⁻¹' {q : E | ‖q - (chartAt E b) b‖ < A.R}
  refine ⟨zs, ?_⟩
  change ‖(chartAt E b) ((chartAt E b).symm z) - (chartAt E b) b‖ < A.R
  rw [coord]
  change ‖z - (chartAt E b) b‖ < A.R
  have zv : z - (chartAt E b) b =
      __NeckPinch_neckVec (E:=E) A.R ((chartAt E b) y - (chartAt E b) b) := by
    dsimp [z]
    abel
  rw [zv]
  exact lt_of_le_of_lt (__NeckPinch_neckVec_norm_le (E:=E) A.R _) hy.2

/-- The formula on the opposite punctured patch. On the open end turn it
around and use `neckShrink`; off the end it is the collapsed point. -/
noncomputable def neckCollapse (b : Y) (A : ChartBall (E:=E) b)
    (y : (({b}:Set Y)ᶜ : Set Y)) : Y := by
  classical
  exact if h : (y:Y) ∈ chartEndSet (E:=E) b A then
    neckShrink (E:=E) b A
      (((chartEndFlip (E:=E) b A) (⟨y,h⟩ :
        (chartEnd (E:=E) b A : Type _))).1.1 : Y)
  else b

lemma neckCollapse_on_end (b : Y) (A : ChartBall (E:=E) b)
    (v : (chartEnd (E:=E) b A : Type _)) :
    neckCollapse (E:=E) b A v.1 =
      neckShrink (E:=E) b A (((chartEndFlip (E:=E) b A) v).1.1 : Y) := by
  classical
  unfold neckCollapse
  dsimp
  split
  · congr 2
  · rename_i hbad
    exact (hbad v.property).elim

lemma neckCollapse_far (b : Y) (A : ChartBall (E:=E) b)
    {y : (({b}:Set Y)ᶜ : Set Y)}
    (hy : y ∈ punctFar (E:=E) b (A.R/2)) :
    neckCollapse (E:=E) b A y = b := by
  classical
  by_cases h : (y:Y) ∈ chartEndSet (E:=E) b A
  · let v : (chartEnd (E:=E) b A : Type _) := ⟨y,h⟩
    rw [show y = v.1 from rfl, neckCollapse_on_end]
    have ngt : A.R/2 <
        ‖(chartAt E b) (v.1.1:Y) - (chartAt E b) b‖ :=
      end_mem_far_norm_gt (E:=E) b A v hy
    have sz := chartEndFlip_size (E:=E) b A v
    have small : ‖(chartAt E b)
          (((chartEndFlip (E:=E) b A) v).1.1:Y) - (chartAt E b) b‖ ≤ A.R/2 := by
      rw [sz]
      linarith
    exact neckShrink_of_small (E:=E) b A
      (((chartEndFlip (E:=E) b A) v).property) small
  · simp [neckCollapse, h]


lemma neckCollapse_mem_local (b : Y) (A : ChartBall (E:=E) b)
    (y : (({b}:Set Y)ᶜ : Set Y)) :
    neckCollapse (E:=E) b A y ∈ chartLocalBall (E:=E) b A.R := by
  classical
  by_cases h : (y:Y) ∈ chartEndSet (E:=E) b A
  · let v : (chartEnd (E:=E) b A : Type _) := ⟨y,h⟩
    rw [show y = v.1 from rfl, neckCollapse_on_end]
    have loc : (((chartEndFlip (E:=E) b A) v).1.1:Y) ∈
        chartLocalBall (E:=E) b A.R :=
      ⟨((chartEndFlip (E:=E) b A) v).property.1,
       ((chartEndFlip (E:=E) b A) v).property.2.2⟩
    exact neckShrink_mem_local (E:=E) b A loc
  · simp [neckCollapse, h]
    exact chartLocalBall_mem (E:=E) b A.pos


lemma neckCollapse_continuous (b : Y) (A : ChartBall (E:=E) b) :
    Continuous (neckCollapse (E:=E) b A) := by
  rw [continuous_iff_continuousAt]
  intro y
  classical
  by_cases h : (y:Y) ∈ chartEndSet (E:=E) b A
  · -- on this open set it is a conjugate of the preceding continuous map
    let W : Set (({b}:Set Y)ᶜ : Set Y) :=
      {t | (t:Y) ∈ chartEndSet (E:=E) b A}
    have Wo : IsOpen W := (chartEndSet_open (E:=E) b A).preimage continuous_subtype_val
    have Wy : y ∈ W := h
    let lift : W → (chartEnd (E:=E) b A : Type _) := fun u => ⟨u.1, u.property⟩
    have lc : Continuous lift := by
      apply continuous_induced_rng.2
      exact continuous_subtype_val
    have F : Continuous (fun u : W =>
        neckShrink (E:=E) b A (((chartEndFlip (E:=E) b A) (lift u)).1.1:Y)) :=
      (neckShrink_continuous (E:=E) b A).comp
        (continuous_subtype_val.comp
          (continuous_subtype_val.comp
            ((chartEndFlip (E:=E) b A).continuous.comp lc)))
    -- avoid dependent dummy: use eventual equality with a local extension
    have Le : ∀ t : W,
        neckCollapse (E:=E) b A t.1 =
          neckShrink (E:=E) b A
            (((chartEndFlip (E:=E) b A) (lift t)).1.1:Y) := by
      intro t
      exact neckCollapse_on_end (E:=E) b A (lift t)
    -- continuity at open set from continuous subtype restriction
    have cW : ContinuousOn (neckCollapse (E:=E) b A) W := by
      apply (continuousOn_iff_continuous_restrict).2
      -- restriction equal to the displayed continuous function
      have eq : W.restrict (neckCollapse (E:=E) b A) =
          (fun t : W => neckShrink (E:=E) b A
            (((chartEndFlip (E:=E) b A) (lift t)).1.1:Y)) := by
        funext t; exact Le t
      rw [eq]
      exact F
    exact (cW y Wy).continuousAt (Wo.mem_nhds Wy)
  · have far : y ∈ punctFar (E:=E) b (A.R/2) :=
        punct_not_end_far (E:=E) b A y h
    have fo : IsOpen (punctFar (E:=E) b (A.R/2)) :=
      punctFar_open (E:=E) b A (by linarith [A.pos]) (by linarith [A.pos])
    apply ContinuousAt.congr_of_eventuallyEq (continuousAt_const)
    filter_upwards [fo.mem_nhds far] with t ht
    exact neckCollapse_far (E:=E) b A ht

open CategoryTheory
private def __NeckPinch_neckLeg0 (b : Y) (A : ChartBall (E:=E) b) :
    C((({b}:Set Y)ᶜ : Set Y), Y) :=
  ⟨(fun y => neckShrink (E:=E) b A (y:Y)),
    (neckShrink_continuous (E:=E) b A).comp continuous_subtype_val⟩
private def __NeckPinch_neckLeg1 (b : Y) (A : ChartBall (E:=E) b) :
    C((({b}:Set Y)ᶜ : Set Y), Y) :=
  ⟨neckCollapse (E:=E) b A,
     neckCollapse_continuous (E:=E) b A⟩

/-- One of the two actual pinch maps out of the radial double.  The first leg
is a squeezed identity of the block.  The other leg is genuinely constant
off an annular end; this fact is what makes descent to the *open* gluing
continuous. -/
noncomputable def radialPinch (b : Y) (A : ChartBall (E:=E) b) :
    let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
    let V : Opens X := chartEnd (E:=E) b A
    let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
    let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
    C((doubleGlueData X V e he).toGlueData.glued, Y) := by
  dsimp
  let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
  let V : Opens X := chartEnd (E:=E) b A
  let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
  let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
  let D : TopCat.GlueData.{0} := doubleGlueData X V e he
  let gg : ∀ i : D.J, C((D.U i : Type), Y) := fun i =>
    Bool.casesOn i (__NeckPinch_neckLeg0 (E:=E) b A) (__NeckPinch_neckLeg1 (E:=E) b A)
  have compat : ∀ (i j : D.J) (v : D.V (i,j)),
      gg i (D.f i j v) = gg j (D.f j i (D.t i j v)) := by
    intro i j v
    change Bool at i; change Bool at j
    rcases i with _|_ <;> rcases j with _|_
    · rfl
    · change neckShrink (E:=E) b A (v.1.1:Y) =
        neckCollapse (E:=E) b A ((e v).1)
      rw [neckCollapse_on_end]
      rw [he]
    · change neckCollapse (E:=E) b A (v.1) =
        neckShrink (E:=E) b A ((e v).1.1:Y)
      rw [neckCollapse_on_end]
    · rfl
  exact continuousMapFromGlue D gg compat

/-- The symmetric pinch, with the two Boolean patches exchanged. -/
noncomputable def radialPinch' (b : Y) (A : ChartBall (E:=E) b) :
    let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
    let V : Opens X := chartEnd (E:=E) b A
    let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
    let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
    C((doubleGlueData X V e he).toGlueData.glued, Y) := by
  dsimp
  let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
  let V : Opens X := chartEnd (E:=E) b A
  let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
  let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
  let D : TopCat.GlueData.{0} := doubleGlueData X V e he
  let gg : ∀ i : D.J, C((D.U i : Type), Y) := fun i =>
    Bool.casesOn i (__NeckPinch_neckLeg1 (E:=E) b A) (__NeckPinch_neckLeg0 (E:=E) b A)
  have compat : ∀ (i j : D.J) (v : D.V (i,j)),
      gg i (D.f i j v) = gg j (D.f j i (D.t i j v)) := by
    intro i j v
    change Bool at i; change Bool at j
    rcases i with _|_ <;> rcases j with _|_
    · rfl
    · change neckCollapse (E:=E) b A (v.1) =
        neckShrink (E:=E) b A ((e v).1.1:Y)
      rw [neckCollapse_on_end]
    · change neckShrink (E:=E) b A (v.1.1:Y) =
        neckCollapse (E:=E) b A ((e v).1)
      rw [neckCollapse_on_end]
      rw [he]
    · rfl
  exact continuousMapFromGlue D gg compat
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
open Set Topology TopologicalSpace CategoryTheory TopCat
open scoped Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]
-- Usable computation rule: on the first open patch the first pinch is the
-- squeezed block coordinate. The categorical descent was the annoying part;
-- callers doing chosen-basepoint bookkeeping should not unfold it.
lemma radialPinch_ι0 (b : Y) (A : ChartBall (E:=E) b)
    (y : (({b}:Set Y)ᶜ : Set Y)) :
    let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
    let V : Opens X := chartEnd (E:=E) b A
    let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
    let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
    radialPinch (E:=E) b A
      ((doubleGlueData X V e he).toGlueData.ι false y) =
       neckShrink (E:=E) b A (y:Y) := by
  dsimp [radialPinch]
  -- now this is the defining equation of the colimit eliminator
  apply continuousMapFromGlue_ι
lemma radialPinch'_ι0 (b : Y) (A : ChartBall (E:=E) b)
    (y : (({b}:Set Y)ᶜ : Set Y)) :
    let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
    let V : Opens X := chartEnd (E:=E) b A
    let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
    let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
    radialPinch' (E:=E) b A
      ((doubleGlueData X V e he).toGlueData.ι false y) =
       neckCollapse (E:=E) b A y := by
  dsimp [radialPinch']
  apply continuousMapFromGlue_ι
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckPinch.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/SphereEndpointSmall.lean
section
open scoped Quaternion Topology RealInnerProductSpace
open Topology Set Metric unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport
/-- A pointed, concrete formulation of the only remaining topology in the
Q8 block.  Instead of a class instance for simply-connectedness it asks for
middle paths in radial position.  `sphere_paths_homotopic_of_middle` turns
this check on the round norm sphere into exactly the endpoint injectivity
used by the covering argument. -/
lemma qOrbit_endpoint_inj_of_middle_paths
    {G : Type*} [Group G] [Finite G]
    (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1)
    (hi : Function.Injective ρ)
    (e : qSphere)
    (H : ∀ (z : qSphere) (a b : Path e z),
      ∃ c : Path e z,
        (∀ (u t : I),
          ((1 - (u:ℝ)) • (a t : Quaternion ℝ) +
            (u:ℝ) • (c t : Quaternion ℝ)) ≠ 0) ∧
        (∀ (u t : I),
          ((1 - (u:ℝ)) • (c t : Quaternion ℝ) +
            (u:ℝ) • (b t : Quaternion ℝ)) ≠ 0)) :
    letI : MulAction G qSphere := unitSphereAction ρ hn
    letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
    letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
    Function.Injective
      (fun a : FundamentalGroup (qOrbit G)
          ((Quotient.mk (MulAction.orbitRel G qSphere)) e) =>
        (qOrbitIsCovering G).monodromy a
          (⟨e, rfl⟩ :
            (Quotient.mk (MulAction.orbitRel G qSphere)) ⁻¹'
              ({(Quotient.mk (MulAction.orbitRel G qSphere)) e} : Set (qOrbit G)))) := by
  classical
  -- the action has no role in the little radial calculation
  apply qOrbit_endpoint_inj_of_start_paths ρ hn hi e
  intro z a b
  obtain ⟨c, hc, hc'⟩ := H z a b
  exact sphere_paths_homotopic_of_middle a b c hc hc'
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
open scoped Quaternion Topology RealInnerProductSpace
open Topology Set Metric unitInterval
/-- Pointwise-antipode version of the previous cut.  The parameter of the
radial homotopy has disappeared; for a chord in a real norm sphere zero is
possible exactly at an antipodal pair. -/
lemma qOrbit_endpoint_inj_of_middle_ne_neg
    {G : Type*} [Group G] [Finite G]
    (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1)
    (hi : Function.Injective ρ)
    (e : qSphere)
    (H : ∀ (z : qSphere) (a b : Path e z),
      ∃ c : Path e z,
        (∀ t : I, (c t : Quaternion ℝ) ≠ -(a t : Quaternion ℝ)) ∧
        (∀ t : I, (b t : Quaternion ℝ) ≠ -(c t : Quaternion ℝ))) :
    letI : MulAction G qSphere := unitSphereAction ρ hn
    letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
    letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
    Function.Injective
      (fun a : FundamentalGroup (qOrbit G)
          ((Quotient.mk (MulAction.orbitRel G qSphere)) e) =>
        (qOrbitIsCovering G).monodromy a
          (⟨e, rfl⟩ :
            (Quotient.mk (MulAction.orbitRel G qSphere)) ⁻¹'
              ({(Quotient.mk (MulAction.orbitRel G qSphere)) e} : Set (qOrbit G)))) := by
  apply qOrbit_endpoint_inj_of_start_paths ρ hn hi e
  intro z a b
  obtain ⟨c, hc, hc'⟩ := H z a b
  exact sphere_paths_homotopic_of_middle_ne_neg a b c hc hc'
end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open scoped Quaternion Topology
open Topology Set unitInterval
/-- The based-loop version is smaller still: quotient injectivity only
compares loops upstairs at one initial sheet.  A middle loop relative to the
constant loop is enough. -/
lemma qOrbit_endpoint_inj_of_loop_middle_ne_neg
    {G : Type*} [Group G] [Finite G]
    (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1)
    (hi : Function.Injective ρ) (e : qSphere)
    (H : ∀ (a : Path e e), ∃ c : Path e e,
      (∀ t : I, (c t : Quaternion ℝ) ≠ -(a t : Quaternion ℝ)) ∧
      (∀ t : I, ((Path.refl e) t : Quaternion ℝ) ≠
        -(c t : Quaternion ℝ))) :
    letI : MulAction G qSphere := unitSphereAction ρ hn
    letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
    letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
    Function.Injective
      (fun a : FundamentalGroup (qOrbit G)
        ((Quotient.mk (MulAction.orbitRel G qSphere)) e) =>
       (qOrbitIsCovering G).monodromy a
        (⟨e, rfl⟩ : (Quotient.mk (MulAction.orbitRel G qSphere)) ⁻¹'
            ({(Quotient.mk (MulAction.orbitRel G qSphere)) e} :
              Set (qOrbit G)))) := by
  letI : MulAction G qSphere := unitSphereAction ρ hn
  letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
  letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
  apply IsCoveringMap.endpoint_inj_of_loops_at (qOrbitIsCovering G) e
  intro a
  obtain ⟨c, hc, hc'⟩ := H a
  exact sphere_paths_homotopic_of_middle_ne_neg a (Path.refl e) c hc hc'
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/SphereEndpointSmall.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/CutRepresentative.lean
section

open scoped Quaternion Topology RealInnerProductSpace
open Topology Set Metric unitInterval
noncomputable section

namespace NonlinearThreeManifoldSupport

/-- A `middle` path is slightly more informative than the way it is used in
`SphereEndpointSmall`.  It gives an honest representative of the old loop
which misses the antipode of the basepoint.  Keeping this harmless conversion
around is useful for cut-and-paste constructions: afterwards it is the
representative, rather than a chosen radial formula, which is threaded through
small deleted balls. -/
lemma sphere_loop_representative_of_middle
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : Metric.sphere (0 : V) 1) (a : Path w w)
    (H : ∃ c : Path w w,
      (∀ t : I, (c t : V) ≠ -(a t : V)) ∧
      (∀ t : I, ((Path.refl w) t : V) ≠ -(c t : V))) :
    ∃ c : Path w w, Path.Homotopic a c ∧
      (∀ t : I, (c t : V) ≠ -(w : V)) := by
  rcases H with ⟨c,hc,hcw⟩
  refine ⟨c, sphere_paths_homotopic_of_forall_ne_neg a c hc, ?_⟩
  intro t
  have h : (w : V) ≠ -(c t : V) := by
    simpa using hcw t
  exact ne_neg_swap h

/-- Representatives which miss the antipodal point already do the whole
pointed loop comparison.  This formulation is a good interface for local
modifications of paths: no coherence between the representatives for
*different* loops is being requested. -/
lemma sphere_loops_null_of_avoid_representatives
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : Metric.sphere (0 : V) 1)
    (H : ∀ a : Path w w, ∃ c : Path w w,
      Path.Homotopic a c ∧
      (∀ t : I, (c t : V) ≠ -(w : V))) :
    ∀ a : Path w w, Path.Homotopic a (Path.refl w) := by
  intro a
  rcases H a with ⟨c,hac,hc⟩
  have hc' : ∀ t : I, ((Path.refl w) t : V) ≠ -(c t : V) := by
    intro t
    change (w : V) ≠ -(c t : V)
    exact ne_neg_swap (hc t)
  exact hac.trans (sphere_paths_homotopic_of_forall_ne_neg c (Path.refl w) hc')

/-- The endpoint map for an orbit cover only needs the preceding pointed
statement.  In particular a later deleted-ball argument can output
representatives and never mentions a `MulAction` or a deck group. -/
lemma qOrbit_endpoint_inj_of_loop_avoid_representatives
    {G : Type*} [Group G] [Finite G]
    (ρ : G →* Quaternion ℝ) (hn : ∀ g, ‖ρ g‖ = 1)
    (hi : Function.Injective ρ) (e : qSphere)
    (H : ∀ a : Path e e, ∃ c : Path e e,
      Path.Homotopic a c ∧
      (∀ t : I, (c t : Quaternion ℝ) ≠ -(e : Quaternion ℝ))) :
    letI : MulAction G qSphere := unitSphereAction ρ hn
    letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
    letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
    Function.Injective
      (fun a : FundamentalGroup (qOrbit G)
        ((Quotient.mk (MulAction.orbitRel G qSphere)) e) =>
       (qOrbitIsCovering G).monodromy a
        (⟨e, rfl⟩ : (Quotient.mk (MulAction.orbitRel G qSphere)) ⁻¹'
            ({(Quotient.mk (MulAction.orbitRel G qSphere)) e} :
              Set (qOrbit G)))) := by
  letI : MulAction G qSphere := unitSphereAction ρ hn
  letI : ContinuousConstSMul G qSphere := unitSphereAction_cont ρ hn
  letI : IsCancelSMul G qSphere := unitSphereAction_cancel ρ hn hi
  exact IsCoveringMap.endpoint_inj_of_loops_at (qOrbitIsCovering G) e
    (sphere_loops_null_of_avoid_representatives e H)

/-- Three soft cases of the deleted-direction problem, phrased at the
representative level.  The last disjunct says that in one transverse
direction no negative point of the old loop actually lies on the two-plane
spanned by that direction and the base vector.  Notice that there is no
premise on the *set of parameters* at which the loop crosses the equator.

The proof is just the three radial bump formulae, followed by
`sphere_loop_representative_of_middle`.  It is handy to isolate them before
attacking a genuine one-dimensional cut: a loop still to be treated must
oscillate on both sides of every transverse plane **and** meet each such
negative plane. -/
lemma sphere_loop_avoid_representative_of_soft_cases
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : Metric.sphere (0 : V) 1) (a : Path w w)
    (H :
      (∀ t : I, (a t : V) ≠ -(w : V)) ∨
      (∃ (f : V →L[ℝ] ℝ), f ≠ 0 ∧ f (w : V) = 0 ∧
        ((∀ t : I, 0 ≤ f (a t : V)) ∨
         (∀ t : I, f (a t : V) ≤ 0))) ∨
      (∃ (f : V →L[ℝ] ℝ) (u : V),
        f (w : V) = 0 ∧ f u = 1 ∧
        (∀ t : I, t ≠ (0:I) → t ≠ (1:I) → f (a t : V) < 0 →
          ¬ ∃ r s : ℝ, (a t : V) = r • (w : V) + s • u))) :
    ∃ c : Path w w, Path.Homotopic a c ∧
      (∀ t : I, (c t : V) ≠ -(w : V)) := by
  rcases H with h | h
  · exact sphere_loop_representative_of_middle w a
      (sphere_loop_middle_of_avoid_base_antipode w a h)
  · rcases h with h | h
    · rcases h with ⟨f,hf,hw,ha⟩
      exact sphere_loop_representative_of_middle w a
        (sphere_loop_middle_of_nonzero_halfspace w a f hf hw ha)
    · rcases h with ⟨f,u,hw,hu,ha⟩
      exact sphere_loop_representative_of_middle w a
        (sphere_loop_middle_of_avoids_negative_plane w a f u hw hu ha)

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport

/-- A bare, vector-valued version of the last local problem.  It is often
much easier to draw a small perturbation in the ambient vector space than on
the norm sphere.  The only forbidden loci for it are two **negative rays**.
Normalising gives the missing representative and the pointwise radial
homotopy back to the old path.

There is deliberately no openness or boundedness hypothesis on `z`; the
non-vanishing and the two ray tests are exactly what normalisation consumes.
For instance, in a local chart one may glue finitely many tiny orthogonal
kinks and check these tests before any division by a norm. -/
lemma sphere_loop_avoid_representative_of_tilt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : Metric.sphere (0 : V) 1) (a : Path w w)
    (z : I → V) (zcont : Continuous z)
    (z0 : z 0 = (w : V)) (z1 : z 1 = (w : V))
    (zne : ∀ t : I, z t ≠ 0)
    (oldray : ∀ t : I, ¬ ∃ r : ℝ, r < 0 ∧ z t = r • (a t : V))
    (baseray : ∀ t : I, ¬ ∃ r : ℝ, r < 0 ∧ z t = r • (w : V)) :
    ∃ c : Path w w, Path.Homotopic a c ∧
      (∀ t : I, (c t : V) ≠ -(w : V)) := by
  have znorm (t : I) : ‖z t‖ ≠ 0 := norm_ne_zero_iff.mpr (zne t)
  let toS : I → Metric.sphere (0 : V) 1 :=
    fun t => sphereNormalize (z t) (zne t)
  have toSc : Continuous toS := by
    apply continuous_induced_rng.2
    change Continuous (fun t : I => (sphereNormalize (z t) (zne t) : V))
    change Continuous (fun t : I => (‖z t‖)⁻¹ • z t)
    have hn : Continuous (fun t : I => ‖z t‖) := continuous_norm.comp zcont
    have hi : Continuous (fun t : I => (‖z t‖)⁻¹) := by
      fun_prop (disch := aesop)
    fun_prop
  have wn : ‖(w : V)‖ = 1 := by
    have h := w.property
    change dist (w : V) 0 = 1 at h
    simpa [dist_zero_right] using h
  have end0 : toS 0 = w := by
    apply Subtype.ext
    change (‖z 0‖)⁻¹ • z 0 = (w : V)
    rw [z0, wn]
    simp
  have end1 : toS 1 = w := by
    apply Subtype.ext
    change (‖z 1‖)⁻¹ • z 1 = (w : V)
    rw [z1, wn]
    simp
  let c : Path w w := ⟨⟨toS, toSc⟩, end0, end1⟩
  -- Clear the norm once.  The same little equation is used at both
  -- forbidden rays.
  have back {t : I} {y : V}
      (eqn : (‖z t‖)⁻¹ • z t = y) : z t = ‖z t‖ • y := by
    calc
      z t = (‖z t‖ * (‖z t‖)⁻¹) • z t := by
        rw [mul_inv_cancel₀ (znorm t), one_smul]
      _ = ‖z t‖ • ((‖z t‖)⁻¹ • z t) := by rw [smul_smul]
      _ = _ := by rw [eqn]
  have npos (t : I) : 0 < ‖z t‖ := norm_pos_iff.mpr (zne t)
  have againstOld (t : I) : (c t : V) ≠ -(a t : V) := by
    intro e
    have e' : (‖z t‖)⁻¹ • z t = -(a t : V) := e
    have b := back e'
    apply oldray t
    refine ⟨- ‖z t‖, (neg_lt_zero.mpr (npos t)), ?_⟩
    calc
      z t = ‖z t‖ • (-(a t : V)) := b
      _ = (- ‖z t‖) • (a t : V) := by module
  have againstBase (t : I) : (c t : V) ≠ -(w : V) := by
    intro e
    have e' : (‖z t‖)⁻¹ • z t = -(w : V) := e
    have b := back e'
    apply baseray t
    refine ⟨- ‖z t‖, (neg_lt_zero.mpr (npos t)), ?_⟩
    calc
      z t = ‖z t‖ • (-(w : V)) := b
      _ = (- ‖z t‖) • (w : V) := by module
  exact ⟨c, sphere_paths_homotopic_of_forall_ne_neg a c againstOld,
    againstBase⟩

/-- A convenient orthogonality check for the two ray tests above.  In a real
inner product space a nonzero vector perpendicular to `v` cannot at the
same time be a multiple of `v`. -/
lemma not_smul_of_inner_zero_of_nonzero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u v : V} (hu : u ≠ 0)
    (huv : @inner ℝ V _ u v = 0) (hv : v ≠ 0) :
    ¬ ∃ r : ℝ, u = r • v := by
  rintro ⟨r,hr⟩
  have t := congrArg (fun x : V => @inner ℝ V _ x v) hr
  have rv : r = 0 := by
    have vv : 0 < @inner ℝ V _ v v := real_inner_self_pos.mpr hv
    -- scalar is on the real first coordinate
    simp [inner_smul_left, huv] at t
    rcases t with h | h
    · exact h
    · exact (hv h).elim
  apply hu
  simpa [rv] using hr

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open scoped RealInnerProductSpace
/-- Orthogonal bumps are a particularly simple way to produce the vector
path in `sphere_loop_avoid_representative_of_tilt`.  They may vanish; the
only place this is disallowed is at a negative multiple of the base vector.
There is one spare perpendicular dimension over every small subarc in the
quaternion sphere, so this is the convenient gluing problem left to a local
cut. -/
lemma sphere_loop_avoid_representative_of_orthogonal_bump
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (w : Metric.sphere (0 : V) 1) (a : Path w w)
    (k : I → V) (kc : Continuous k)
    (k0 : k 0 = 0) (k1 : k 1 = 0)
    (ka : ∀ t : I, @inner ℝ V _ (k t) (a t : V) = 0)
    (kw : ∀ t : I, @inner ℝ V _ (k t) (w : V) = 0)
    (khit : ∀ t : I, k t = 0 →
       ¬ ∃ r : ℝ, r < 0 ∧ (a t : V) = r • (w : V)) :
    ∃ c : Path w w, Path.Homotopic a c ∧
      (∀ t : I, (c t : V) ≠ -(w : V)) := by
  let z : I → V := fun t => (a t : V) + k t
  have zc : Continuous z := by
    dsimp [z]
    fun_prop
  have z0 : z 0 = (w : V) := by
    dsimp [z]
    have e := congrArg Subtype.val a.source
    rw [e, k0]
    simp
  have z1 : z 1 = (w : V) := by
    dsimp [z]
    have e := congrArg Subtype.val a.target
    rw [e, k1]
    simp
  have anorm (t : I) : ‖(a t : V)‖ = 1 := by
    have h := (a t).property
    change dist (a t : V) 0 = 1 at h
    simpa [dist_zero_right] using h
  have az (t : I) : @inner ℝ V _ (a t : V) (k t) = 0 := by
    rw [← real_inner_comm]
    exact ka t
  have zne (t : I) : z t ≠ 0 := by
    intro h
    have e := congrArg (fun x : V => @inner ℝ V _ (a t : V) x) h
    dsimp [z] at e
    simp [inner_add_right, az t, real_inner_self_eq_norm_sq, anorm t] at e
  have oldray (t : I) : ¬ ∃ r : ℝ, r < 0 ∧ z t = r • (a t : V) := by
    rintro ⟨r,hr,e⟩
    have ee := congrArg (fun x : V => @inner ℝ V _ (a t : V) x) e
    dsimp [z] at ee
    simp [inner_add_right, inner_smul_right, az t,
      real_inner_self_eq_norm_sq, anorm t] at ee
    linarith
  have baseray (t : I) : ¬ ∃ r : ℝ, r < 0 ∧ z t = r • (w : V) := by
    rintro ⟨r,hr,e⟩
    have ee := congrArg (fun x : V => @inner ℝ V _ (k t) x) e
    have ez : @inner ℝ V _ (k t) (z t) =
        @inner ℝ V _ (k t) (k t) := by
      dsimp [z]
      rw [inner_add_right, ka t, zero_add]
    have ee0 : @inner ℝ V _ (k t) (k t) = 0 := by
      rw [← ez, ee]
      simp [inner_smul_right, kw t]
    have kz : k t = 0 := by
      have q : ‖k t‖ ^ 2 = (0:ℝ) := by
        rw [← real_inner_self_eq_norm_sq]
        exact ee0
      have nq : ‖k t‖ = 0 := by nlinarith [norm_nonneg (k t)]
      exact norm_eq_zero.mp nq
    apply khit t kz
    refine ⟨r,hr,?_⟩
    -- after the bump has vanished this was the very same negative ray
    simpa [z, kz] using e
  exact sphere_loop_avoid_representative_of_tilt w a z zc z0 z1 zne
    oldray baseray

end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/CutRepresentative.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckLoopPinch.lean
section
open scoped Topology Manifold
open Set Topology TopologicalSpace unitInterval Metric
noncomputable section
namespace NonlinearThreeManifoldSupport
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]
/-- The `other` leg of the open radial pinch is already null on every
punctured-block loop. Its image is in the *honest* coordinate ball (including
the centre). This is much weaker than, and doesn't assert, a section of the
pinch as a map of spaces. -/
lemma neckCollapse_paths (b : Y) (A : ChartBall (E:=E) b)
    {z : (({b}:Set Y)ᶜ : Set Y)} (L : Path z z) :
    let D : C((({b}:Set Y)ᶜ : Set Y),Y) :=
      ⟨neckCollapse (E:=E) b A, neckCollapse_continuous (E:=E) b A⟩
    Path.Homotopic (L.map D.continuous) (Path.refl (D z)) := by
  dsimp
  let D : C((({b}:Set Y)ᶜ : Set Y),Y) :=
    ⟨neckCollapse (E:=E) b A, neckCollapse_continuous (E:=E) b A⟩
  have inside (t : unitInterval) :
      D (L t) ∈ chartLocalBall (E:=E) b A.R :=
    neckCollapse_mem_local (E:=E) b A (L t)
  have insz : D z ∈ chartLocalBall (E:=E) b A.R :=
    neckCollapse_mem_local (E:=E) b A z
  let q : (Metric.ball (0:E) A.R : Set E) :=
    ⟨(chartAt E b) (D z) - (chartAt E b) b,
     (mem_ball_zero_iff.mpr insz.2)⟩
  let lift : unitInterval → (Metric.ball (0:E) A.R : Set E) := fun t =>
    ⟨(chartAt E b) (D (L t)) - (chartAt E b) b,
      (mem_ball_zero_iff.mpr (inside t).2)⟩
  have liftc : Continuous lift := by
    apply continuous_induced_rng.2
    let src : unitInterval → ((chartAt E b).source : Set Y) := fun t =>
      ⟨D (L t), (inside t).1⟩
    have srcc : Continuous src := by
      apply continuous_induced_rng.2
      exact D.continuous.comp L.continuous
    have coord : Continuous (fun t : unitInterval => (chartAt E b) (D (L t))) := by
      exact ((chartAt E b).continuousOn.restrict).comp srcc
    exact coord.sub continuous_const
  have lift0 : lift 0 = q := by
    apply Subtype.ext
    dsimp [lift, q]
    rw [L.source]
  have lift1 : lift 1 = q := by
    apply Subtype.ext
    dsimp [lift, q]
    rw [L.target]
  let LL : Path q q :=
    { toFun := lift, continuous_toFun := liftc,
      source' := lift0, target' := lift1 }
  have BH : Path.Homotopic LL (Path.refl q) :=
    ball_paths_homotopic A.R LL (Path.refl q)
  let F : C((Metric.ball (0:E) A.R : Set E), Y) := chartBallMap (E:=E) b A
  have base : F q = D z := by
    dsimp [F, q, chartBallMap]
    have mem : (chartAt E b) (D z) ∈ (chartAt E b).target :=
      (chartAt E b).map_source insz.1
    have v : (chartAt E b) b +
        ((chartAt E b) (D z) - (chartAt E b) b) = (chartAt E b) (D z) := by abel
    -- the inverse chart on its target
    simpa [v] using ((chartAt E b).left_inv insz.1)
  have BM := BH.map F
  let P : Path (D z) (D z) :=
    (LL.map F.continuous).cast base.symm base.symm
  let Q : Path (D z) (D z) :=
    ((Path.refl q).map F.continuous).cast base.symm base.symm
  have BM' : Path.Homotopic P Q := by
    rcases BM with ⟨HH⟩
    refine ⟨{
      toFun := HH.toFun
      continuous_toFun := HH.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro t
      exact HH.map_zero_left t
    · intro t
      exact HH.map_one_left t
    · intro t u hu
      -- only the boundary values of the old square are used, casts are
      -- definitionally invisible as functions
      exact HH.prop' t u hu
  have same : P = L.map D.continuous := by
    apply Path.ext
    funext t
    change (chartAt E b).symm ((chartAt E b) b +
      ((chartAt E b) (D (L t)) - (chartAt E b) b)) = D (L t)
    have sr := (inside t).1
    have v : (chartAt E b) b +
        ((chartAt E b) (D (L t)) - (chartAt E b) b) =
          (chartAt E b) (D (L t)) := by abel
    simpa [v] using ((chartAt E b).left_inv sr)
  have rr : Q = Path.refl (D z) := by
    apply Path.ext
    funext t
    dsimp [Q]
    exact base
  rw [same, rr] at BM'
  exact BM'
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
open Set Topology unitInterval
open scoped Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]
/-- Monodromy formulation of `neckCollapse_paths`. It only talks about the
*open* punctured chart, so no van Kampen or connected-sum assumptions enter. -/
lemma neckCollapse_piOne (b : Y) (A : ChartBall (E:=E) b)
    (z : (({b}:Set Y)ᶜ : Set Y))
    (a : FundamentalGroup (({b}:Set Y)ᶜ : Set Y) z) :
    let D : C((({b}:Set Y)ᶜ : Set Y),Y) :=
      ⟨neckCollapse (E:=E) b A, neckCollapse_continuous (E:=E) b A⟩
    FundamentalGroup.map D z a =
      (1 : FundamentalGroup Y (D z)) := by
  dsimp
  change Path.Homotopic.Quotient z z at a
  induction a using Quotient.inductionOn with
  | _ L =>
    change Path.Homotopic.Quotient.mk _ = _
    change Path.Homotopic.Quotient.mk _ =
      Path.Homotopic.Quotient.mk (Path.refl (neckCollapse (E:=E) b A z))
    exact Quotient.sound (neckCollapse_paths (E:=E) b A L)
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
open scoped Topology Manifold
open Set Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y Z : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]
variable [TopologicalSpace Z]
/-- In particular the other pinch kills every incoming map which factors
through the *second open punctured patch*. This is the useful loop-level
replacement for asking that whole manifolds be homotopy retractions. -/
lemma BasedCMap.collapse_comp_piOne
    (b : Y) (A : ChartBall (E:=E) b)
    {w : Z} {z : (({b}:Set Y)ᶜ : Set Y)}
    (k : BasedCMap Z w (({b}:Set Y)ᶜ : Set Y) z)
    (a : FundamentalGroup Z w) :
    let D : C((({b}:Set Y)ᶜ : Set Y),Y) :=
      ⟨neckCollapse (E:=E) b A, neckCollapse_continuous (E:=E) b A⟩
    let r : BasedCMap (({b}:Set Y)ᶜ : Set Y) z Y (D z) :=
      { toContinuousMap := D, map_pt := rfl }
    BasedCMap.piOne (BasedCMap.comp r k) a =
      (1 : FundamentalGroup Y (D z)) := by
  dsimp
  let D : C((({b}:Set Y)ᶜ : Set Y),Y) :=
      ⟨neckCollapse (E:=E) b A, neckCollapse_continuous (E:=E) b A⟩
  let r : BasedCMap (({b}:Set Y)ᶜ : Set Y) z Y (D z) :=
      { toContinuousMap := D, map_pt := rfl }
  change BasedCMap.piOne (BasedCMap.comp r k) a = _
  rw [BasedCMap.piOne_comp]
  change BasedCMap.piOne r (BasedCMap.piOne k a) = _
  have er : BasedCMap.piOne r = FundamentalGroup.map D z := by
    ext u
    change Path.Homotopic.Quotient z z at u
    induction u using Quotient.inductionOn with
    | _ p =>
      change (FundamentalGroup.mapOfEq D _) (FundamentalGroup.fromPath (.mk p)) = _
      rw [FundamentalGroup.mapOfEq_apply]
      rfl
  rw [er]
  exact neckCollapse_piOne (E:=E) b A z (BasedCMap.piOne k a)

end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckLoopPinch.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckSections.lean
section
/-!
 A first pointed fact about the two explicit pinches.  The maps on the
 colimit are descended in `NeckPinch`; in particular one should not try to
 choose the base point at the deleted centre -- that point is in neither
 open chart.  The equatorial cross section of the end is in both charts,
 however, and both squeezed maps are literally the centre there.  Keeping
 this choice explicit is useful before attempting any path/section
 construction.
-/
open scoped Topology Manifold
open Set Topology TopologicalSpace CategoryTheory TopCat
noncomputable section
set_option maxHeartbeats 3000000
namespace NonlinearThreeManifoldSupport
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

/-- A punctured radial ball has a point on its middle sphere.  This tiny
sharpening of `radialSet_nonempty` is what is needed for the *based* two
pinches: at a general point of the overlap their base images are different. -/
lemma radialSet_middle (R : ℝ) (hR : 0 < R) [Nontrivial E] :
    ∃ z : E, z ∈ radialSet (E:=E) R ∧ ‖z‖ = R/2 := by
  obtain ⟨v,hv⟩ : ∃ v : E, v ≠ 0 := exists_ne 0
  have nv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let t : ℝ := R / (2 * ‖v‖)
  have tp : 0 < t := div_pos hR (mul_pos (by norm_num) nv)
  refine ⟨t • v, ?_, ?_⟩
  · constructor
    · exact smul_ne_zero (ne_of_gt tp) hv
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos tp]
      dsimp [t]
      have hn0 : ‖v‖ ≠ 0 := ne_of_gt nv
      field_simp
      nlinarith [hR]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos tp]
    dsimp [t]
    have hn0 : ‖v‖ ≠ 0 := ne_of_gt nv
    field_simp

/-- The two descended pinches have a common marked fibre.  The point is on
radius `R/2` in the first end.  `chartEndFlip_size` says its representative
in the other end has the same radius, so the small half of `neckShrink` is
used on both sides.

This lemma does not assert anything about maps *into* the colimit.  It is
only the based bookkeeping: `b` itself is absent from both open patches and
using it as a representative is a subtle but fatal error. -/
lemma radialPinches_common_point (b : Y) (A : ChartBall (E:=E) b)
    [Nontrivial E] :
    let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
    let V : Opens X := chartEnd (E:=E) b A
    let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
    let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
    ∃ x : (doubleGlueData X V e he).toGlueData.glued,
      radialPinch (E:=E) b A x = b ∧
      radialPinch' (E:=E) b A x = b := by
  dsimp
  let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
  let V : Opens X := chartEnd (E:=E) b A
  let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
  let he : ∀ z : (V : Type), e (e z) = z := chartEndFlip_invol (E:=E) b A
  let D : TopCat.GlueData.{0} := doubleGlueData X V e he
  obtain ⟨q,hq,hq'⟩ := radialSet_middle (E:=E) A.R A.pos
  let m : (chartEnd (E:=E) b A : Type _) :=
    (chartEndHomeo (E:=E) b A).symm ⟨q,hq⟩
  let y : (({b}:Set Y)ᶜ : Set Y) := m.1
  let x : D.toGlueData.glued := D.toGlueData.ι false y
  refine ⟨x, ?_, ?_⟩
  · -- first Boolean patch is squeezed directly
    have eq0 : radialPinch (E:=E) b A
        ((doubleGlueData X V e he).toGlueData.ι false y) =
          neckShrink (E:=E) b A (y:Y) := by
      simpa [X, V, e, he] using radialPinch_ι0 (E:=E) b A y
    change radialPinch (E:=E) b A
        ((doubleGlueData X V e he).toGlueData.ι false y) = b
    rw [eq0]
    apply neckShrink_of_small (E:=E) b A (y:= (y:Y))
    · exact m.property
    · have coord :
          (chartEndHomeo (E:=E) b A) m =
            (⟨q,hq⟩ : (radialSet (E:=E) A.R : Set E)) :=
          (chartEndHomeo (E:=E) b A).apply_symm_apply ⟨q,hq⟩
      have cval : (chartAt E b) (m.1.1:Y) - (chartAt E b) b = q :=
        congrArg Subtype.val coord
      change ‖(chartAt E b) (m.1.1:Y) - (chartAt E b) b‖ ≤ A.R/2
      rw [cval, hq']
  · -- on the second pinch the first representative is turned around
    have eq1 : radialPinch' (E:=E) b A
        ((doubleGlueData X V e he).toGlueData.ι false y) =
          neckCollapse (E:=E) b A y := by
      simpa [X, V, e, he] using radialPinch'_ι0 (E:=E) b A y
    change radialPinch' (E:=E) b A
        ((doubleGlueData X V e he).toGlueData.ι false y) = b
    rw [eq1]
    have col : neckCollapse (E:=E) b A y =
        neckShrink (E:=E) b A
          (((chartEndFlip (E:=E) b A) m).1.1 : Y) := by
      exact neckCollapse_on_end (E:=E) b A m
    rw [col]
    apply neckShrink_of_small (E:=E) b A
      (y:= (((chartEndFlip (E:=E) b A) m).1.1 : Y))
    · exact ((chartEndFlip (E:=E) b A) m).property
    · have sz := chartEndFlip_size (E:=E) b A m
      have coord :
          (chartEndHomeo (E:=E) b A) m =
            (⟨q,hq⟩ : (radialSet (E:=E) A.R : Set E)) :=
          (chartEndHomeo (E:=E) b A).apply_symm_apply ⟨q,hq⟩
      have cval : (chartAt E b) (m.1.1:Y) - (chartAt E b) b = q :=
        congrArg Subtype.val coord
      -- the reversed radius is `R - R/2`
      rw [sz]
      rw [cval, hq']
      linarith

/-- A middle representative before passing to the colimit. Keeping the
representative (rather than just its class) is useful for loops in a single
open patch. -/
lemma collapse_middle_rep (b : Y) (A : ChartBall (E:=E) b)
    [Nontrivial E] :
    ∃ y : (({b}:Set Y)ᶜ : Set Y),
      neckShrink (E:=E) b A (y:Y) = b ∧ neckCollapse (E:=E) b A y = b := by
  let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
  let V : Opens X := chartEnd (E:=E) b A
  obtain ⟨q,hq,hq'⟩ := radialSet_middle (E:=E) A.R A.pos
  let m : (chartEnd (E:=E) b A : Type _) :=
    (chartEndHomeo (E:=E) b A).symm ⟨q,hq⟩
  let y : (({b}:Set Y)ᶜ : Set Y) := m.1
  refine ⟨y, ?_, ?_⟩
  · apply neckShrink_of_small (E:=E) b A (y:=(y:Y))
    · exact m.property
    · have coord :
          (chartEndHomeo (E:=E) b A) m =
            (⟨q,hq⟩ : (radialSet (E:=E) A.R : Set E)) :=
          (chartEndHomeo (E:=E) b A).apply_symm_apply ⟨q,hq⟩
      have cval : (chartAt E b) (m.1.1:Y) - (chartAt E b) b = q :=
        congrArg Subtype.val coord
      change ‖(chartAt E b) (m.1.1:Y) - (chartAt E b) b‖ ≤ A.R/2
      rw [cval, hq']
  · have col : neckCollapse (E:=E) b A y =
        neckShrink (E:=E) b A
          (((chartEndFlip (E:=E) b A) m).1.1 : Y) :=
        neckCollapse_on_end (E:=E) b A m
    rw [col]
    apply neckShrink_of_small (E:=E) b A
      (y:= (((chartEndFlip (E:=E) b A) m).1.1 : Y))
    · exact ((chartEndFlip (E:=E) b A) m).property
    · have sz := chartEndFlip_size (E:=E) b A m
      have coord :
          (chartEndHomeo (E:=E) b A) m =
            (⟨q,hq⟩ : (radialSet (E:=E) A.R : Set E)) :=
          (chartEndHomeo (E:=E) b A).apply_symm_apply ⟨q,hq⟩
      have cval : (chartAt E b) (m.1.1:Y) - (chartAt E b) b = q :=
        congrArg Subtype.val coord
      rw [sz, cval, hq']
      linarith

end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckSections.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckPatch.lean
section
open scoped Topology Manifold
open Set Topology TopologicalSpace CategoryTheory TopCat
noncomputable section
namespace NonlinearThreeManifoldSupport
universe u
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

abbrev neckSpace (b:Y) (A:ChartBall (E:=E) b) :=
 let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
 let V : Opens X := chartEnd (E:=E) b A
 let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
 let he : ∀ z : (V : Type), e (e z)=z := chartEndFlip_invol (E:=E) b A
 ((doubleGlueData X V e he).toGlueData.glued : Type)

/-- The two tautological open patches of the radial sum, as actual continuous maps. -/
def neckIn (b:Y) (A:ChartBall (E:=E) b) (k:Bool) :
    C((({b}:Set Y)ᶜ : Set Y), neckSpace (E:=E) b A) := by
  dsimp [neckSpace]
  let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
  let V : Opens X := chartEnd (E:=E) b A
  let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
  let he : ∀ z : (V : Type), e (e z)=z := chartEndFlip_invol (E:=E) b A
  let D : TopCat.GlueData.{0} := doubleGlueData X V e he
  exact (ConcreteCategory.hom (D.toGlueData.ι k) : C((D.U k : Type), (D.toGlueData.glued : Type)))

@[simp] lemma radialPinch_neckIn0 (b:Y) (A:ChartBall (E:=E) b)
    (y: (({b}:Set Y)ᶜ : Set Y)) :
    radialPinch (E:=E) b A (neckIn (E:=E) b A false y) =
      neckShrink (E:=E) b A (y:Y) := by
  change _ = _
  -- representation is definitional
  exact radialPinch_ι0 (E:=E) b A y

@[simp] lemma radialPinch'_neckIn0 (b:Y) (A:ChartBall (E:=E) b)
    (y: (({b}:Set Y)ᶜ : Set Y)) :
    radialPinch' (E:=E) b A (neckIn (E:=E) b A false y) =
      neckCollapse (E:=E) b A y := by
  exact radialPinch'_ι0 (E:=E) b A y

@[simp] lemma radialPinch_neckIn1 (b:Y) (A:ChartBall (E:=E) b)
    (y: (({b}:Set Y)ᶜ : Set Y)) :
    radialPinch (E:=E) b A (neckIn (E:=E) b A true y) =
      neckCollapse (E:=E) b A y := by
  dsimp [neckIn, neckSpace, radialPinch]
  apply continuousMapFromGlue_ι

@[simp] lemma radialPinch'_neckIn1 (b:Y) (A:ChartBall (E:=E) b)
    (y: (({b}:Set Y)ᶜ : Set Y)) :
    radialPinch' (E:=E) b A (neckIn (E:=E) b A true y) =
      neckShrink (E:=E) b A (y:Y) := by
  dsimp [neckIn, neckSpace, radialPinch']
  apply continuousMapFromGlue_ι

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open Set Topology TopologicalSpace CategoryTheory TopCat
open scoped Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

def shrinkOnPuncture (b:Y) (A:ChartBall (E:=E) b) : C((({b}:Set Y)ᶜ : Set Y),Y) :=
 ⟨fun y => neckShrink (E:=E) b A (y:Y),
  (neckShrink_continuous (E:=E) b A).comp continuous_subtype_val⟩
def collapseOnPuncture (b:Y) (A:ChartBall (E:=E) b) : C((({b}:Set Y)ᶜ : Set Y),Y) :=
 ⟨neckCollapse (E:=E) b A, neckCollapse_continuous (E:=E) b A⟩

lemma collapseMap_piOne (b:Y) (A:ChartBall (E:=E) b)
 (y: (({b}:Set Y)ᶜ : Set Y))
 (hy : collapseOnPuncture (E:=E) b A y = b)
 (a : FundamentalGroup (({b}:Set Y)ᶜ : Set Y) y) :
 BasedCMap.piOne ({ toContinuousMap := collapseOnPuncture (E:=E) b A, map_pt := hy } :
   BasedCMap (({b}:Set Y)ᶜ : Set Y) y Y b) a = 1 := by
  change Path.Homotopic.Quotient y y at a
  induction a using Quotient.inductionOn with
  | _ p =>
    change (FundamentalGroup.mapOfEq _ hy)
        (FundamentalGroup.fromPath (.mk p)) = _
    rw [FundamentalGroup.mapOfEq_apply]
    change Path.Homotopic.Quotient.mk _ =
       Path.Homotopic.Quotient.mk (Path.refl b)
    have HH := neckCollapse_paths (E:=E) b A p
    dsimp [collapseOnPuncture] at *
    rcases HH with ⟨H⟩
    refine Quotient.sound ⟨{
      toFun := H.toFun,
      continuous_toFun := H.continuous,
      map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }⟩
    · intro t
      -- casts do not change values
      exact H.map_zero_left t
    · intro t
      -- at the right edge the old value is the old base point
      change H (1,t) = b
      exact (H.map_one_left t).trans hy
    · intro t u hu
      rcases hu with hu|hu
      · change H (t,u) = _
        exact H.prop' t u (Or.inl hu)
      · have hu' : u = (1:unitInterval) := by simpa using hu
        subst u
        -- the cast path has the same values as the old one
        exact H.prop' t (1:unitInterval) (Or.inr rfl)

/-- Middle point equipped with both representatives.  This is a less lossy
form of `collapse_middle_rep`: the flipped representative is indispensable
when the two incoming maps have different domains. -/
lemma collapse_middle_end (b:Y) (A:ChartBall (E:=E) b) [Nontrivial E] :
 ∃ m : (chartEnd (E:=E) b A : Type _),
   neckShrink (E:=E) b A (m.1.1:Y) = b ∧
   neckShrink (E:=E) b A ((((chartEndFlip (E:=E) b A) m).1.1):Y) = b := by
  obtain ⟨q,hq,hq'⟩ := radialSet_middle (E:=E) A.R A.pos
  let m : (chartEnd (E:=E) b A : Type _) :=
    (chartEndHomeo (E:=E) b A).symm ⟨q,hq⟩
  refine ⟨m, ?_, ?_⟩
  · apply neckShrink_of_small (E:=E) b A (y:=(m.1.1:Y)) m.property
    have coord : (chartEndHomeo (E:=E) b A) m =
         (⟨q,hq⟩ : (radialSet (E:=E) A.R : Set E)) :=
       (chartEndHomeo (E:=E) b A).apply_symm_apply ⟨q,hq⟩
    have cv : (chartAt E b) (m.1.1:Y) - (chartAt E b) b = q :=
      congrArg Subtype.val coord
    rw [cv, hq']
  · apply neckShrink_of_small (E:=E) b A
       (y:=((((chartEndFlip (E:=E) b A) m).1.1):Y))
       (((chartEndFlip (E:=E) b A) m).property)
    have sz := chartEndFlip_size (E:=E) b A m
    have coord : (chartEndHomeo (E:=E) b A) m =
         (⟨q,hq⟩ : (radialSet (E:=E) A.R : Set E)) :=
       (chartEndHomeo (E:=E) b A).apply_symm_apply ⟨q,hq⟩
    have cv : (chartAt E b) (m.1.1:Y) - (chartAt E b) b = q :=
      congrArg Subtype.val coord
    rw [sz, cv, hq']
    linarith

lemma neckIn_middle_eq (b:Y) (A:ChartBall (E:=E) b)
    (m : (chartEnd (E:=E) b A : Type _)) :
    neckIn (E:=E) b A false m.1 =
      neckIn (E:=E) b A true (((chartEndFlip (E:=E) b A) m).1) := by
  let X : TopCat := TopCat.of (({b}:Set Y)ᶜ : Set Y)
  let V : Opens X := chartEnd (E:=E) b A
  let e : (V : Type) ≃ₜ (V : Type) := chartEndFlip (E:=E) b A
  let he : ∀ z : (V : Type), e (e z)=z := chartEndFlip_invol (E:=E) b A
  let D : TopCat.GlueData.{0} := doubleGlueData X V e he
  change D.toGlueData.ι false m.1 = D.toGlueData.ι true (((chartEndFlip (E:=E) b A) m).1)
  apply (D.ι_eq_iff_rel false true _ _).mpr
  refine ⟨m, ?_, ?_⟩ <;> rfl

/-- Pure algebra once the two punctured patch groups split the squeezed map.
This version, unlike a spurious continuous section of a closed summand, is
actually what connected sum supplies. -/
lemma BasedCMap.split_of_patch_sections
 {P W Y : Type*} [TopologicalSpace P] [TopologicalSpace W] [TopologicalSpace Y]
 {y₀ y₁ : P} {x:W} {b:Y}
 (k₀ : BasedCMap P y₀ W x) (k₁ : BasedCMap P y₁ W x)
 (t₀ : BasedCMap P y₀ Y b) (t₁ : BasedCMap P y₁ Y b)
 (r s : BasedCMap W x Y b)
 (h₀ : (BasedCMap.piOne r).comp (BasedCMap.piOne k₀) = BasedCMap.piOne t₀)
 (h₁ : (BasedCMap.piOne s).comp (BasedCMap.piOne k₁) = BasedCMap.piOne t₁)
 (hkill : ∀ a : FundamentalGroup P y₁,
      BasedCMap.piOne r (BasedCMap.piOne k₁ a) = 1)
 (e₀ : QuaternionGroup 2 →* FundamentalGroup Y b)
 (L₀ : QuaternionGroup 2 →* FundamentalGroup P y₀)
 (L₁ : QuaternionGroup 2 →* FundamentalGroup P y₁)
 (hs₀ : (BasedCMap.piOne t₀).comp L₀ = e₀)
 (hs₁ : (BasedCMap.piOne t₁).comp L₁ = e₀)
 (d : FundamentalGroup Y b →* QuaternionGroup 2)
 (ed : d.comp e₀ = MonoidHom.id (QuaternionGroup 2)) :
 ∃ (u v : QuaternionGroup 2 →* FundamentalGroup W x)
   (R S : FundamentalGroup W x →* QuaternionGroup 2),
   R.comp u = MonoidHom.id (QuaternionGroup 2) ∧
   S.comp v = MonoidHom.id (QuaternionGroup 2) ∧ R (v (.a 2)) = 1 := by
  let u := (BasedCMap.piOne k₀).comp L₀
  let v := (BasedCMap.piOne k₁).comp L₁
  let R := d.comp (BasedCMap.piOne r)
  let S := d.comp (BasedCMap.piOne s)
  refine ⟨u,v,R,S,?_,?_,?_⟩
  · ext q
    change d (BasedCMap.piOne r (BasedCMap.piOne k₀ (L₀ q))) = q
    have hh := DFunLike.congr_fun h₀ (L₀ q)
    change BasedCMap.piOne r (BasedCMap.piOne k₀ (L₀ q)) = _ at hh
    rw [hh]
    have hsec := DFunLike.congr_fun hs₀ q
    change BasedCMap.piOne t₀ (L₀ q) = e₀ q at hsec
    rw [hsec]
    exact DFunLike.congr_fun ed q
  · ext q
    change d (BasedCMap.piOne s (BasedCMap.piOne k₁ (L₁ q))) = q
    have hh := DFunLike.congr_fun h₁ (L₁ q)
    change BasedCMap.piOne s (BasedCMap.piOne k₁ (L₁ q)) = _ at hh
    rw [hh]
    have hsec := DFunLike.congr_fun hs₁ q
    change BasedCMap.piOne t₁ (L₁ q) = e₀ q at hsec
    rw [hsec]
    exact DFunLike.congr_fun ed q
  · change d (BasedCMap.piOne r (BasedCMap.piOne k₁ (L₁ (.a 2)))) = 1
    rw [hkill]
    exact map_one d

end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
open Set Topology TopologicalSpace CategoryTheory TopCat
open scoped Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

private lemma __NeckPatch_based_ext {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
 {x:X} {y:Y} (f g : BasedCMap X x Y y)
 (h : f.toContinuousMap = g.toContinuousMap) : f=g := by
 cases f with | mk f hf =>
  cases g with | mk g hg =>
   cases h
   rfl

/-- Patch-level package. No map from a *closed* summand is asserted: such a
space section of a connected-sum pinch generally cannot exist. The two maps
are from the punctured patches, where they are simply the open embeddings. -/
lemma radial_patch_data (b:Y) (A:ChartBall (E:=E) b) [Nontrivial E] :
 ∃ (y₀ y₁ : (({b}:Set Y)ᶜ : Set Y)) (x : neckSpace (E:=E) b A)
   (k₀ : BasedCMap (({b}:Set Y)ᶜ : Set Y) y₀ (neckSpace (E:=E) b A) x)
   (k₁ : BasedCMap (({b}:Set Y)ᶜ : Set Y) y₁ (neckSpace (E:=E) b A) x)
   (t₀ : BasedCMap (({b}:Set Y)ᶜ : Set Y) y₀ Y b)
   (t₁ : BasedCMap (({b}:Set Y)ᶜ : Set Y) y₁ Y b)
   (r s : BasedCMap (neckSpace (E:=E) b A) x Y b),
   t₀.toContinuousMap = shrinkOnPuncture (E:=E) b A ∧
   t₁.toContinuousMap = shrinkOnPuncture (E:=E) b A ∧
   (BasedCMap.piOne r).comp (BasedCMap.piOne k₀) = BasedCMap.piOne t₀ ∧
   (BasedCMap.piOne s).comp (BasedCMap.piOne k₁) = BasedCMap.piOne t₁ ∧
   (∀ a : FundamentalGroup (({b}:Set Y)ᶜ : Set Y) y₁,
       BasedCMap.piOne r (BasedCMap.piOne k₁ a) = 1) := by
  classical
  obtain ⟨m, hm, hm'⟩ := collapse_middle_end (E:=E) b A
  let y₀ : (({b}:Set Y)ᶜ : Set Y) := m.1
  let y₁ : (({b}:Set Y)ᶜ : Set Y) := ((chartEndFlip (E:=E) b A) m).1
  have ecol : neckCollapse (E:=E) b A y₁ = b := by
    have h := neckCollapse_on_end (E:=E) b A
          ((chartEndFlip (E:=E) b A) m)
    -- two reversals
    rw [chartEndFlip_invol (E:=E) b A m] at h
    exact h.trans hm
  have esmall0 : shrinkOnPuncture (E:=E) b A y₀ = b := hm
  have esmall1 : shrinkOnPuncture (E:=E) b A y₁ = b := hm'
  have ec0 : collapseOnPuncture (E:=E) b A y₁ = b := ecol
  let x : neckSpace (E:=E) b A := neckIn (E:=E) b A false y₀
  have ex1 : neckIn (E:=E) b A true y₁ = x :=
    (neckIn_middle_eq (E:=E) b A m).symm
  let k₀ : BasedCMap (({b}:Set Y)ᶜ : Set Y) y₀ (neckSpace (E:=E) b A) x :=
    { toContinuousMap := neckIn (E:=E) b A false, map_pt := rfl }
  let k₁ : BasedCMap (({b}:Set Y)ᶜ : Set Y) y₁ (neckSpace (E:=E) b A) x :=
    { toContinuousMap := neckIn (E:=E) b A true, map_pt := ex1 }
  let t₀ : BasedCMap (({b}:Set Y)ᶜ : Set Y) y₀ Y b :=
    { toContinuousMap := shrinkOnPuncture (E:=E) b A, map_pt := esmall0 }
  let t₁ : BasedCMap (({b}:Set Y)ᶜ : Set Y) y₁ Y b :=
    { toContinuousMap := shrinkOnPuncture (E:=E) b A, map_pt := esmall1 }
  have rx : radialPinch (E:=E) b A x = b := by
    change radialPinch (E:=E) b A (neckIn (E:=E) b A false y₀) = b
    rw [radialPinch_neckIn0]
    exact hm
  have sx : radialPinch' (E:=E) b A x = b := by
    rw [← ex1]
    rw [radialPinch'_neckIn1]
    exact hm'
  let r : BasedCMap (neckSpace (E:=E) b A) x Y b :=
    { toContinuousMap := radialPinch (E:=E) b A, map_pt := rx }
  let s : BasedCMap (neckSpace (E:=E) b A) x Y b :=
    { toContinuousMap := radialPinch' (E:=E) b A, map_pt := sx }
  have maps0 : BasedCMap.comp r k₀ = t₀ := by
    apply __NeckPatch_based_ext
    ext z
    exact radialPinch_neckIn0 (E:=E) b A z
  have maps1 : BasedCMap.comp s k₁ = t₁ := by
    apply __NeckPatch_based_ext
    ext z
    exact radialPinch'_neckIn1 (E:=E) b A z
  have mapskill : BasedCMap.comp r k₁ =
        ({ toContinuousMap := collapseOnPuncture (E:=E) b A,
           map_pt := ec0 } : BasedCMap (({b}:Set Y)ᶜ : Set Y) y₁ Y b) := by
    apply __NeckPatch_based_ext
    ext z
    exact radialPinch_neckIn1 (E:=E) b A z
  refine ⟨y₀,y₁,x,k₀,k₁,t₀,t₁,r,s,rfl,rfl,?_,?_,?_⟩
  · rw [← BasedCMap.piOne_comp, maps0]
  · rw [← BasedCMap.piOne_comp, maps1]
  · intro a
    change ((BasedCMap.piOne r).comp (BasedCMap.piOne k₁)) a = _
    rw [← BasedCMap.piOne_comp, mapskill]
    exact collapseMap_piOne (E:=E) b A y₁ ec0 a
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/NeckPatch.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/PolynomialCut.lean
section
open scoped Quaternion Topology RealInnerProductSpace
open Topology Set Metric unitInterval Filter
noncomputable section
namespace NonlinearThreeManifoldSupport

/-- A small, honest regularisation of the still missing cut argument.  A loop
on a finite dimensional real sphere may first be replaced by the radial
normalisation of a *polynomial* (Bernstein) curve.  The latter has the same
end points.  Moreover the unnormalised curve is uniformly close to the old
loop, so it never vanishes and it never lies on a negative ray of the old
loop.

This is useful here because space filling loops really do occur: it is not
legitimate to choose a direction outside the image of an arbitrary
continuous interval map. After this replacement that issue is only an
algebraic, polynomial-curve issue.  The lemma does **not** assert the other
ray test (the ray of the fixed base point). -/
lemma sphere_loop_bernstein_tilt
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (w : Metric.sphere (0 : V) 1) (a : Path w w) :
    ∃ (n : ℕ), n ≠ 0 ∧
      let f : C(I, V) :=
        ⟨(fun t : I => (a t : V)), by fun_prop⟩
      let z : I → V := fun t => bernsteinApproximation n f t
      Continuous z ∧ z 0 = (w : V) ∧ z 1 = (w : V) ∧
      (∀ t : I, ‖z t - (a t : V)‖ < (1/2 : ℝ)) ∧
      (∀ t : I, z t ≠ 0) ∧
      (∀ t : I, ¬ ∃ r : ℝ, r < 0 ∧ z t = r • (a t : V)) := by
  -- The topology on `C(I,V)` is the uniform/norm topology (`I` is compact).
  -- Thus Bernstein convergence gives a *single* polynomial close at every
  -- point, not a different approximant for every parameter.
  let f : C(I, V) :=
    ⟨(fun t : I => (a t : V)), by fun_prop⟩
  have ht : Filter.Tendsto (fun n : ℕ => bernsteinApproximation n f)
        Filter.atTop (𝓝 f) := bernsteinApproximation_uniform f
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 ht) (1/2 : ℝ)
    (by norm_num : (0:ℝ) < (1/2:ℝ))
  let n : ℕ := max N 1
  have hnN : N ≤ n := le_max_left _ _
  have hnpos : n ≠ 0 := by
    have h : 1 ≤ n := le_max_right _ _
    omega
  have close : dist (bernsteinApproximation n f) f < (1/2 : ℝ) :=
    hN n hnN
  let z : I → V := fun t => bernsteinApproximation n f t
  have zcont : Continuous z := by
    exact (bernsteinApproximation n f).continuous
  have zpoint (t : I) : ‖z t - (a t : V)‖ < (1/2 : ℝ) := by
    have H : dist (bernsteinApproximation n f t) (f t) ≤
        dist (bernsteinApproximation n f) f :=
      (ContinuousMap.dist_le (α := I) (β := V) (f := bernsteinApproximation n f)
        (g := f) (C := dist (bernsteinApproximation n f) f) (dist_nonneg)).1 (le_rfl) t
    have H' : dist (bernsteinApproximation n f t) (f t) < (1/2:ℝ) :=
      lt_of_le_of_lt H close
    simpa [z, f, dist_eq_norm] using H'
  have anorm (t : I) : ‖(a t : V)‖ = 1 := by
    have h := (a t).property
    change dist (a t : V) 0 = 1 at h
    simpa [dist_zero_right] using h
  have zne (t : I) : z t ≠ 0 := by
    intro e
    have q := zpoint t
    rw [e] at q
    -- distance from zero to a unit vector is one
    have : ‖(0:V) - (a t : V)‖ = (1:ℝ) := by
      rw [zero_sub, norm_neg, anorm]
    rw [this] at q
    norm_num at q
  have oldray (t : I) : ¬ ∃ r : ℝ, r < 0 ∧ z t = r • (a t : V) := by
    rintro ⟨r,hr,e⟩
    have q := zpoint t
    rw [e] at q
    have vec : r • (a t : V) - (a t : V) =
        (r - 1) • (a t : V) := by module
    rw [vec, norm_smul, anorm t, mul_one, Real.norm_eq_abs] at q
    have habs : |r - 1| = 1 - r := by
      rw [abs_of_nonpos] <;> linarith
    rw [habs] at q
    linarith
  have z0 : z 0 = (w : V) := by
    dsimp [z]
    simpa [f] using
      (bernsteinApproximation.apply_zero n f)
  have z1 : z 1 = (w : V) := by
    dsimp [z]
    have h := bernsteinApproximation.apply_one hnpos f
    simpa [f] using h
  refine ⟨n, hnpos, ?_⟩
  -- Keep the definitions in the conclusion reducible. This makes the lemma
  -- convenient to use as the input `z` to `..._of_tilt`.
  dsimp
  exact ⟨zcont, z0, z1, zpoint, zne, oldray⟩

/-- With the *remaining* negative-base-ray test on the polynomial curve,
the whole representative cut follows. This packages the many metric
bookkeeping steps above and the already proved radial normalisation lemma.
Only a polynomial curve now appears in the unsolved ray test. -/
lemma sphere_loop_representative_of_bernstein_base_test
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (w : Metric.sphere (0 : V) 1) (a : Path w w)
    (H : ∀ (n : ℕ), n ≠ 0 →
      (let f : C(I, V) :=
        ⟨(fun t : I => (a t : V)), by fun_prop⟩
       let z : I → V := fun t => bernsteinApproximation n f t
       (∀ t : I, ‖z t - (a t : V)‖ < (1/2 : ℝ)) →
       ∀ t : I, ¬ ∃ r : ℝ, r < 0 ∧ z t = r • (w : V))) :
    ∃ c : Path w w, Path.Homotopic a c ∧
      (∀ t : I, (c t : V) ≠ -(w : V)) := by
  obtain ⟨n,hn,hc,h0,h1,hclose,hne,hold⟩ :=
    sphere_loop_bernstein_tilt w a
  let f : C(I,V) := ⟨(fun t : I => (a t : V)), by fun_prop⟩
  let z : I → V := fun t => bernsteinApproximation n f t
  have hbase : ∀ t : I, ¬ ∃ r : ℝ, r < 0 ∧ z t = r • (w : V) :=
    H n hn (by simpa [z, f] using hclose)
  exact sphere_loop_avoid_representative_of_tilt w a z
    (by simpa [z, f] using hc)
    (by simpa [z, f] using h0)
    (by simpa [z, f] using h1)
    (by simpa [z, f] using hne)
    (by simpa [z, f] using hold)
    hbase
end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
/-- Once an ambient vector path is less than distance one from the old unit
loop, its old-ray and nonzero tests do not have to be checked any more.
This version of `...of_tilt` is useful when a small second perturbation is
made to a Bernstein curve.  Notice the strict constant `1`; a negative
multiple of a unit vector is farther than (indeed strictly greater than) one
from it. -/
lemma sphere_loop_avoid_representative_of_close_base_test
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (w : Metric.sphere (0 : V) 1) (a : Path w w)
    (z : I → V) (zc : Continuous z)
    (z0 : z 0 = (w : V)) (z1 : z 1 = (w : V))
    (hclose : ∀ t : I, ‖z t - (a t : V)‖ < (1:ℝ))
    (hbase : ∀ t : I, ¬ ∃ r : ℝ, r < 0 ∧ z t = r • (w : V)) :
    ∃ c : Path w w, Path.Homotopic a c ∧
       (∀ t : I, (c t : V) ≠ -(w : V)) := by
  have anorm (t : I) : ‖(a t : V)‖ = 1 := by
    have h := (a t).property
    change dist (a t : V) 0 = 1 at h
    simpa [dist_zero_right] using h
  have zne (t : I) : z t ≠ 0 := by
    intro e
    have q := hclose t
    rw [e] at q
    have one : ‖(0:V) - (a t : V)‖ = (1:ℝ) := by
      rw [zero_sub, norm_neg, anorm]
    rw [one] at q
    linarith
  have old (t : I) : ¬ ∃ r : ℝ, r < 0 ∧ z t = r • (a t : V) := by
    rintro ⟨r,hr,e⟩
    have q := hclose t
    rw [e] at q
    have vec : r • (a t : V) - (a t : V) =
        (r - 1) • (a t : V) := by module
    rw [vec, norm_smul, anorm t, mul_one, Real.norm_eq_abs] at q
    have habs : |r - 1| = 1 - r := by
      rw [abs_of_nonpos] <;> linarith
    rw [habs] at q
    linarith
  exact sphere_loop_avoid_representative_of_tilt w a z zc z0 z1 zne old hbase
end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open scoped RealInnerProductSpace
/-- Finite bad parameters can always be removed with *one* tiny linear bump.
Here `L z` is a transverse coordinate already known to have finitely many
zeros (later it will be a nonzero polynomial). The bump is in `ker L`; a
second coordinate `K` reads off its coefficient. Only finitely many real
coefficients are forbidden, so it can be as small as desired.

No differentiability is hidden here; the root-finiteness hypothesis is the
only trace of polynomiality. This avoids the invalid "an interval map can't
fill space" shortcut for the original continuous loop. -/
lemma transverse_small_bump_of_finite_roots
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (w : Metric.sphere (0 : V) 1)
    (z : I → V) (zc : Continuous z)
    (z0 : z 0 = (w : V)) (z1 : z 1 = (w : V))
    (L K : V →L[ℝ] ℝ) (u : V)
    (Lw : L (w : V) = 0) (Lu : L u = 0)
    (Kw : K (w : V) = 0) (Ku : K u = 1)
    (S : Set I) (Sf : S.Finite)
    (roots : ∀ t : I, L (z t) = 0 → t ∈ S) :
    ∃ g : I → V, Continuous g ∧ g 0 = 0 ∧ g 1 = 0 ∧
       (∀ t : I, ‖g t‖ < (1/2 : ℝ)) ∧
       (∀ t : I, ¬ ∃ r : ℝ, r < 0 ∧ z t + g t = r • (w : V)) := by
  let bump : I → ℝ := fun t => (t:ℝ) * (1 - (t:ℝ))
  have bc : Continuous bump := by dsimp [bump]; fun_prop
  have bpos {t:I} (h0 : t ≠ (0:I)) (h1 : t ≠ (1:I)) : 0 < bump t := by
    dsimp [bump]
    have h0' : 0 < (t:ℝ) := by
      have h := t.property.1
      have ne : (t:ℝ) ≠ 0 := by
        intro e; apply h0; apply Subtype.ext; simpa using e
      exact lt_of_le_of_ne h (Ne.symm ne)
    have h1' : (t:ℝ) < 1 := by
      have h := t.property.2
      have ne : (t:ℝ) ≠ 1 := by
        intro e; apply h1; apply Subtype.ext; simpa using e
      exact lt_of_le_of_ne h ne
    exact mul_pos h0' (sub_pos.mpr h1')
  have b_le (t:I) : bump t ≤ 1 := by
    dsimp [bump]
    have h0 := t.property.1
    have h1 := t.property.2
    nlinarith [mul_self_nonneg ((t:ℝ) - 1)]
  have b_nonneg (t:I) : 0 ≤ bump t :=
    mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2)
  -- the finitely many coefficients which a negative ray could ask for
  let bad : Set ℝ := (fun t : I => -(K (z t)) / (bump t)) '' S
  have badf : bad.Finite := Sf.image _
  let δ : ℝ := (4 * (‖u‖ + 1))⁻¹
  have δpos : 0 < δ := by
    dsimp [δ]
    positivity
  have inf : (Set.Ioo (0:ℝ) δ \ bad).Infinite :=
    (Set.Ioo_infinite δpos).diff badf
  obtain ⟨c,hcI,hcbad⟩ : ∃ c : ℝ, c ∈ Set.Ioo (0:ℝ) δ ∧ c ∉ bad := by
    have hn : (Set.Ioo (0:ℝ) δ \ bad).Nonempty := inf.nonempty
    rcases hn with ⟨c,hc⟩
    exact ⟨c,hc.1,hc.2⟩
  have cpos : 0 < c := hcI.1
  have csmall : c < δ := hcI.2
  let g : I → V := fun t => (c * bump t) • u
  have gc : Continuous g := by
    dsimp [g]
    fun_prop
  have g_zero (t:I) (h:t = (0:I) ∨ t = (1:I)) : g t = 0 := by
    rcases h with rfl | rfl <;> simp [g, bump]
  refine ⟨g, gc, g_zero 0 (Or.inl rfl), g_zero 1 (Or.inr rfl), ?_, ?_⟩
  · intro t
    change ‖(c * bump t) • u‖ < (1/2:ℝ)
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (le_of_lt cpos) (b_nonneg t))]
    have nm : 0 ≤ ‖u‖ := norm_nonneg _
    have den : 0 < 4 * (‖u‖ + 1) := by positivity
    have small' : c * (4 * (‖u‖ + 1)) < 1 := by
      exact (lt_div_iff₀ den).1 (by simpa [δ] using csmall)
    have first : c * bump t * ‖u‖ ≤ c * 1 * ‖u‖ := by
      have bc' := b_le t
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left bc' (le_of_lt cpos)) nm
    calc
      c * bump t * ‖u‖ ≤ c * 1 * ‖u‖ := first
      _ < (1/2:ℝ) := by nlinarith
  · intro t
    rintro ⟨r,hr, e⟩
    by_cases h0 : t = (0:I)
    · subst t
      have ev : (w : V) = r • (w : V) := by simpa [z0, g, bump] using e
      have zz : (1-r) • (w : V) = 0 := by
        calc
          (1-r) • (w : V) = (w : V) - r • (w : V) := by module
          _ = 0 := sub_eq_zero.mpr ev
      have wn : (w : V) ≠ 0 := by
        intro q
        have q' := w.property
        change dist (w : V) 0 = 1 at q'
        simp [q] at q'
      have no : (1-r) = 0 :=
        (smul_eq_zero.mp zz).resolve_right wn
      linarith
    · by_cases h1 : t = (1:I)
      · subst t
        have ev : (w : V) = r • (w : V) := by simpa [z1, g, bump] using e
        have zz : (1-r) • (w : V) = 0 := by
          calc
            (1-r) • (w : V) = (w : V) - r • (w : V) := by module
            _ = 0 := sub_eq_zero.mpr ev
        have wn : (w : V) ≠ 0 := by
          intro q
          have q' := w.property
          change dist (w : V) 0 = 1 at q'
          simp [q] at q'
        have no : (1-r) = 0 :=
          (smul_eq_zero.mp zz).resolve_right wn
        linarith
      · have bn : bump t ≠ 0 := ne_of_gt (bpos h0 h1)
        have eqL := congrArg L e
        have root : L (z t) = 0 := by
          have eqL' : L (z t) + (c * bump t) * L u =
                r * L (w : V) := by
            simpa [g, map_add, map_smul] using eqL
          simpa [Lu, Lw] using eqL'
        have mem : t ∈ S := roots t root
        apply hcbad
        refine ⟨t, mem, ?_⟩
        have eqK := congrArg K e
        have eqK' : K (z t) + (c * bump t) * K u =
                r * K (w : V) := by
          simpa [g, map_add, map_smul] using eqK
        have eq0 : K (z t) + (c * bump t) = 0 := by
          simpa [Ku, Kw] using eqK'
        -- unravel the chosen forbidden value
        change -(K (z t)) / bump t = c
        field_simp
        linarith
end NonlinearThreeManifoldSupport

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/PolynomialCut.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/DeletedPi.lean
section
noncomputable section
open scoped Topology Manifold
open Set Topology
namespace NonlinearThreeManifoldSupport
namespace BasedCMap
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}
/-- The representative-level criterion for the deleted chart.  It is useful
not to choose representatives compatibly with concatenation: equality and
monoid laws in the quotient follow just from injectivity. -/
lemma piOne_bijective_of_loops (f : BasedCMap X x Y y)
    (lift : ∀ p : Path y y, ∃ q : Path x x,
      Path.Homotopic
        ((q.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm) p)
    (faithful : ∀ a b : Path x x,
      Path.Homotopic
        ((a.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm)
        ((b.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm) →
      Path.Homotopic a b) :
    Function.Bijective (piOne f) := by
  constructor
  · intro u v h
    change Path.Homotopic.Quotient x x at u v
    induction u using Quotient.inductionOn with | _ a => ?_
    induction v using Quotient.inductionOn with | _ b => ?_
    change (FundamentalGroup.mapOfEq f.toContinuousMap _)
         (FundamentalGroup.fromPath (.mk a)) =
       (FundamentalGroup.mapOfEq f.toContinuousMap _)
         (FundamentalGroup.fromPath (.mk b)) at h
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply] at h
    have hh : Path.Homotopic
        ((a.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm)
        ((b.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm) := by
      exact Path.Homotopic.Quotient.exact h
    exact Quotient.sound (faithful a b hh)
  · intro z
    change Path.Homotopic.Quotient y y at z
    induction z using Quotient.inductionOn with | _ p => ?_
    obtain ⟨q,hq⟩ := lift p
    let z' : FundamentalGroup X x := FundamentalGroup.fromPath (.mk q)
    refine ⟨z', ?_⟩
    change (FundamentalGroup.mapOfEq f.toContinuousMap _)
        (FundamentalGroup.fromPath (.mk q)) =
        (FundamentalGroup.fromPath (.mk p))
    rw [FundamentalGroup.mapOfEq_apply]
    exact Quotient.sound hq


/-- For the two-dimensional (injective) half it is enough to treat a loop
which bounds at the puncture. Cancellation is done in the groupoid quotient,
not by reassociating `Path.trans`. -/
lemma piOne_injective_of_null_loops (f : BasedCMap X x Y y)
    (null : ∀ a : Path x x,
      Path.Homotopic
        ((a.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm)
        (Path.refl y) →
      Path.Homotopic a (Path.refl x)) :
    Function.Injective (piOne f) := by
  have ker : ∀ z : FundamentalGroup X x,
      piOne f z = 1 → z = (1 : FundamentalGroup X x) := by
    intro z hz
    change Path.Homotopic.Quotient x x at z
    induction z using Quotient.inductionOn with | _ a => ?_
    change (FundamentalGroup.mapOfEq f.toContinuousMap _)
         (FundamentalGroup.fromPath (.mk a)) = _ at hz
    rw [FundamentalGroup.mapOfEq_apply] at hz
    change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk (Path.refl y) at hz
    exact Quotient.sound (null a (Path.Homotopic.Quotient.exact hz))
  intro a b h
  have z : piOne f (a * b⁻¹) = (1 : FundamentalGroup Y y) := by
    rw [map_mul, map_inv, h]
    simp
  have z' := ker (a * b⁻¹) z
  apply eq_of_div_eq_one
  simpa [div_eq_mul_inv] using z'

lemma piOne_bijective_of_lift_null (f : BasedCMap X x Y y)
    (lift : ∀ p : Path y y, ∃ q : Path x x,
      Path.Homotopic
        ((q.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm) p)
    (null : ∀ a : Path x x,
      Path.Homotopic
        ((a.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm)
        (Path.refl y) →
      Path.Homotopic a (Path.refl x)) :
    Function.Bijective (piOne f) := by
  refine ⟨piOne_injective_of_null_loops f null, ?_⟩
  intro z
  change Path.Homotopic.Quotient y y at z
  induction z using Quotient.inductionOn with | _ p => ?_
  obtain ⟨q,hq⟩ := lift p
  refine ⟨FundamentalGroup.fromPath (.mk q), ?_⟩
  change (FundamentalGroup.mapOfEq f.toContinuousMap _)
        (FundamentalGroup.fromPath (.mk q)) =
        (FundamentalGroup.fromPath (.mk p))
  rw [FundamentalGroup.mapOfEq_apply]
  exact Quotient.sound hq

lemma piOne_split_of_lift_null (f : BasedCMap X x Y y)
    (lift : ∀ p : Path y y, ∃ q : Path x x,
      Path.Homotopic
        ((q.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm) p)
    (null : ∀ a : Path x x,
      Path.Homotopic
        ((a.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm)
        (Path.refl y) →
      Path.Homotopic a (Path.refl x)) :
    ∃ g : FundamentalGroup Y y →* FundamentalGroup X x,
      (piOne f).comp g = MonoidHom.id (FundamentalGroup Y y) := by
  let e : FundamentalGroup X x ≃* FundamentalGroup Y y :=
    MulEquiv.ofBijective (piOne f) (piOne_bijective_of_lift_null f lift null)
  refine ⟨e.symm.toMonoidHom, ?_⟩
  ext a
  exact e.apply_symm_apply a

lemma piOne_split_of_loops (f : BasedCMap X x Y y)
    (lift : ∀ p : Path y y, ∃ q : Path x x,
      Path.Homotopic
        ((q.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm) p)
    (faithful : ∀ a b : Path x x,
      Path.Homotopic
        ((a.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm)
        ((b.map f.toContinuousMap.continuous).cast f.map_pt.symm f.map_pt.symm) →
      Path.Homotopic a b) :
    ∃ g : FundamentalGroup Y y →* FundamentalGroup X x,
      (piOne f).comp g = MonoidHom.id (FundamentalGroup Y y) := by
  let e : FundamentalGroup X x ≃* FundamentalGroup Y y :=
    MulEquiv.ofBijective (piOne f) (piOne_bijective_of_loops f lift faithful)
  refine ⟨e.symm.toMonoidHom, ?_⟩
  ext a
  exact e.apply_symm_apply a
end BasedCMap
end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open Set Topology unitInterval Metric
open scoped Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {T : Type} [TopologicalSpace T] [T2Space T] [ChartedSpace E T]
/-- In the path half of deletion there is nothing to do to loops confined to
the coordinate ball: that whole ball, including its centre, is convex in the
chart and null as a based loop. Thus only passages through the rim require a
local cut. -/
lemma chartLocalBall_loops_null (b : T) (A : ChartBall (E:=E) b)
    (L : Path b b)
    (inside : ∀ t : unitInterval, L t ∈ chartLocalBall (E:=E) b A.R) :
    Path.Homotopic L (Path.refl b) := by
  have insz : b ∈ chartLocalBall (E:=E) b A.R :=
    chartLocalBall_mem (E:=E) b A.pos
  let q : (Metric.ball (0:E) A.R : Set E) :=
    ⟨(0:E), (by simpa using A.pos)⟩
  let lift : unitInterval → (Metric.ball (0:E) A.R : Set E) := fun t =>
    ⟨(chartAt E b) (L t) - (chartAt E b) b,
      (mem_ball_zero_iff.mpr (inside t).2)⟩
  have liftc : Continuous lift := by
    apply continuous_induced_rng.2
    let src : unitInterval → ((chartAt E b).source : Set T) := fun t =>
      ⟨L t, (inside t).1⟩
    have srcc : Continuous src := by
      apply continuous_induced_rng.2
      exact L.continuous
    have coord : Continuous (fun t : unitInterval => (chartAt E b) (L t)) :=
      ((chartAt E b).continuousOn.restrict).comp srcc
    exact coord.sub continuous_const
  have lift0 : lift 0 = q := by
    apply Subtype.ext
    dsimp [lift,q]
    rw [L.source]
    simp
  have lift1 : lift 1 = q := by
    apply Subtype.ext
    dsimp [lift,q]
    rw [L.target]
    simp
  let LL : Path q q :=
    { toFun := lift, continuous_toFun := liftc,
      source' := lift0, target' := lift1 }
  have BH : Path.Homotopic LL (Path.refl q) :=
    ball_paths_homotopic A.R LL (Path.refl q)
  let F : C((Metric.ball (0:E) A.R : Set E), T) := chartBallMap (E:=E) b A
  have base : F q = b := by
    dsimp [F,q, chartBallMap]
    simp
  have BM := BH.map F
  let P : Path b b :=
    (LL.map F.continuous).cast base.symm base.symm
  let Q : Path b b :=
    ((Path.refl q).map F.continuous).cast base.symm base.symm
  have BM' : Path.Homotopic P Q := by
    rcases BM with ⟨HH⟩
    refine ⟨{
      toFun := HH.toFun
      continuous_toFun := HH.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro t; exact HH.map_zero_left t
    · intro t; exact HH.map_one_left t
    · intro t u hu; exact HH.prop' t u hu
  have same : P = L := by
    apply Path.ext
    funext t
    change (chartAt E b).symm ((chartAt E b) b +
      ((chartAt E b) (L t) - (chartAt E b) b)) = L t
    have sr := (inside t).1
    have v : (chartAt E b) b +
        ((chartAt E b) (L t) - (chartAt E b) b) =
          (chartAt E b) (L t) := by abel
    simpa [v] using ((chartAt E b).left_inv sr)
  have rr : Q = Path.refl b := by
    apply Path.ext
    funext t
    dsimp [Q]
    exact base
  rw [same,rr] at BM'
  exact BM'
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/DeletedPi.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/QuaternionPolynomialBump.lean
section
open scoped Quaternion RealInnerProductSpace Topology
open Topology Set Metric unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport
lemma clm_bernstein_eval
 {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 (n:ℕ) (f:C(I,E)) (L:E→L[ℝ] ℝ) (t:I) :
 L (bernsteinApproximation n f t) =
 Polynomial.eval (t:ℝ)
   (∑ k : Fin (n+1), Polynomial.C (L (f (bernstein.z k))) *
          bernsteinPolynomial ℝ n k) := by
 rw [Polynomial.eval_finset_sum]
 rw [bernsteinApproximation.apply]
 rw [map_sum]
 apply Finset.sum_congr rfl
 intro k hk
 rw [map_smul]
 rw [Polynomial.eval_mul, Polynomial.eval_C]
 -- show eval bernstein poly equals bernstein function
 change (bernstein n (k:ℕ) t) * L (f (bernstein.z k)) =
   L (f (bernstein.z k)) * Polynomial.eval (t:ℝ) (bernsteinPolynomial ℝ n (k:ℕ)) -- maybe orientation

 rw [bernstein_apply]
 simp [bernsteinPolynomial]
 ring
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
lemma clm_bernstein_finite_roots
 {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 (n:ℕ) (f:C(I,E)) (L:E→L[ℝ] ℝ) (t0:I)
 (hnz : L (bernsteinApproximation n f t0) ≠ 0) :
 ∃ S : Set I, S.Finite ∧
   ∀ t:I, L (bernsteinApproximation n f t) = 0 → t ∈ S := by
 let P : Polynomial ℝ :=
   ∑ k : Fin (n+1), Polynomial.C (L (f (bernstein.z k))) * bernsteinPolynomial ℝ n k
 have heval (t:I) : L (bernsteinApproximation n f t) = Polynomial.eval (t:ℝ) P :=
   clm_bernstein_eval n f L t
 have Pnz : P ≠ 0 := by
   intro hp
   have h := heval t0
   rw [hp] at h
   simp at h
   exact hnz h
 let T : Set ℝ := {x | P.IsRoot x}
 have Tf : T.Finite := Polynomial.finite_setOf_isRoot Pnz
 let S : Set I := Subtype.val ⁻¹' T
 have Sf : S.Finite := Set.Finite.preimage (fun a _ b _ h => Subtype.ext h) Tf
 refine ⟨S,Sf,?_⟩
 intro t ht
 have e : Polynomial.eval (t:ℝ) P = 0 := (heval t).symm.trans ht
 -- IsRoot def
 change (t:ℝ) ∈ T
 change Polynomial.IsRoot P (t:ℝ)
 exact e
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
noncomputable def qi : Quaternion ℝ →L[ℝ] ℝ :=
 ContinuousLinearMap.mk (QuaternionAlgebra.imIₗ (-1:ℝ) (0:ℝ) (-1:ℝ)) Quaternion.continuous_imI
noncomputable def qj : Quaternion ℝ →L[ℝ] ℝ :=
 ContinuousLinearMap.mk (QuaternionAlgebra.imJₗ (-1:ℝ) (0:ℝ) (-1:ℝ)) Quaternion.continuous_imJ
noncomputable def qk : Quaternion ℝ →L[ℝ] ℝ :=
 ContinuousLinearMap.mk (QuaternionAlgebra.imKₗ (-1:ℝ) (0:ℝ) (-1:ℝ)) Quaternion.continuous_imK
lemma qnorth_some_imag
 (a:Path qNorth qNorth) (n:ℕ) (hn:n≠0)
 (hanti : ¬ ∀ t:I, (a t : Quaternion ℝ) ≠ -(qNorth : Quaternion ℝ))
 (hnear : let f:C(I,Quaternion ℝ) := ⟨(fun t => (a t : Quaternion ℝ)), by fun_prop⟩
          ∀ t:I, ‖bernsteinApproximation n f t - (a t : Quaternion ℝ)‖ < (1/2:ℝ)) :
 let f:C(I,Quaternion ℝ) := ⟨(fun t => (a t : Quaternion ℝ)), by fun_prop⟩
 ∃ t:I, (bernsteinApproximation n f t).imI ≠ 0 ∨
        (bernsteinApproximation n f t).imJ ≠ 0 ∨
        (bernsteinApproximation n f t).imK ≠ 0 := by
 dsimp at hnear ⊢
 -- abbreviated
 classical
 push_neg at hanti
 obtain ⟨tbad, hbad⟩ := hanti
 by_contra H
 push_neg at H
 -- H : forall t, coord =0 all
 let f : C(I,Quaternion ℝ) := ⟨(fun t => (a t : Quaternion ℝ)), by fun_prop⟩
 let z : I → Quaternion ℝ := fun t => bernsteinApproximation n f t
 have zcoe (t:I) : z t = ((z t).re : ℝ) := by
   dsimp [z, f]
   apply Quaternion.ext <;> simp [H t]
 have zc : Continuous z := (bernsteinApproximation n f).continuous
 have near (t:I) : ‖z t - (a t : Quaternion ℝ)‖ < (1/2:ℝ) := hnear t
 have neg : (z tbad).re < 0 := by
   have ht := near tbad
   rw [hbad, zcoe] at ht
   -- norm coe real
   -- -(qNorth) val = -1 coerces
   change ‖(((z tbad).re : ℝ) : Quaternion ℝ) - (- (1:Quaternion ℝ))‖ < (1/2:ℝ) at ht
   have sub : (((z tbad).re : ℝ) : Quaternion ℝ) - (- (1:Quaternion ℝ)) =
       (((z tbad).re + 1 : ℝ) : Quaternion ℝ) := by
         norm_num
   rw [sub, Quaternion.norm_coe, Real.norm_eq_abs] at ht
   have lo : - (1/2:ℝ) < (z tbad).re + 1 := (abs_lt.mp ht).1
   have hi : (z tbad).re + 1 < (1/2:ℝ) := (abs_lt.mp ht).2
   linarith
 have atzero : (z (0:I)).re = 1 := by
   dsimp [z]
   rw [bernsteinApproximation.apply_zero]
   -- source
   dsimp [f]
   have e : (a (0:I) : Quaternion ℝ) = 1 := congrArg Subtype.val a.source
   simpa [qNorth] using congrArg QuaternionAlgebra.re e
 have rc : Continuous (fun t:I => (z t).re) := Quaternion.continuous_re.comp zc
 have zerole : (0:ℝ) ∈ Set.Icc ((z tbad).re) ((z 0).re) := by
   rw [atzero]
   exact ⟨le_of_lt neg, by norm_num⟩
 obtain ⟨s, hs⟩ := (intermediate_value_univ tbad (0:I) rc) zerole
 have rez : (z s).re = 0 := hs
 have zzero : z s = 0 := by rw [zcoe s, rez]; norm_num
 have badnear := near s
 rw [zzero] at badnear
 have anorm : ‖(a s : Quaternion ℝ)‖ = 1 := by
   have e := (a s).property
   change dist (a s : Quaternion ℝ) 0 = 1 at e
   simpa [dist_zero_right] using e
 have : ‖(0:Quaternion ℝ) - (a s : Quaternion ℝ)‖ = 1 := by simp [anorm]
 rw [this] at badnear
 norm_num at badnear
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
lemma qnorth_bernstein_bump
 (a:Path qNorth qNorth) (n:ℕ) (hn:n≠0)
 (hanti : ¬ ∀ t:I, (a t : Quaternion ℝ) ≠ -(qNorth : Quaternion ℝ))
 (hnear : let f:C(I,Quaternion ℝ) := ⟨(fun t => (a t : Quaternion ℝ)), by fun_prop⟩
          let z:I→Quaternion ℝ := fun t => bernsteinApproximation n f t
          ∀ t:I, ‖z t - (a t : Quaternion ℝ)‖ < (1/2:ℝ)) :
 let f:C(I,Quaternion ℝ) := ⟨(fun t => (a t : Quaternion ℝ)), by fun_prop⟩
 let z:I→Quaternion ℝ := fun t => bernsteinApproximation n f t
 ∃ g:I→Quaternion ℝ, Continuous g ∧ g 0 = 0 ∧ g 1 = 0 ∧
  (∀ t:I, ‖g t‖ < (1/2:ℝ)) ∧
  (∀ t:I, ¬ ∃ r:ℝ, r < 0 ∧ z t + g t = r • (qNorth : Quaternion ℝ)) := by
 dsimp at hnear ⊢
 let f:C(I,Quaternion ℝ) := ⟨(fun t => (a t : Quaternion ℝ)), by fun_prop⟩
 let z:I→Quaternion ℝ := fun t => bernsteinApproximation n f t
 have img := qnorth_some_imag a n hn hanti (by simpa [f, z] using hnear)
 dsimp at img
 rcases img with ⟨t, hI | hJ | hK⟩
 · -- I coordinate
   have hnz : qi (bernsteinApproximation n f t) ≠ 0 := hI
   obtain ⟨S,Sf,roots⟩ := clm_bernstein_finite_roots n f qi t hnz
   have zc : Continuous z := (bernsteinApproximation n f).continuous
   have z0 : z 0 = (qNorth : Quaternion ℝ) := by
     dsimp [z]; simpa [f] using (bernsteinApproximation.apply_zero n f)
   have z1 : z 1 = (qNorth : Quaternion ℝ) := by
     dsimp [z]; simpa [f] using (bernsteinApproximation.apply_one hn f)
   let u : Quaternion ℝ := QuaternionAlgebra.mk 0 0 1 0
   have Lu : qi u = 0 := rfl
   have Ku : qj u = 1 := rfl
   exact transverse_small_bump_of_finite_roots qNorth z zc z0 z1 qi qj u
     (by rfl) Lu (by rfl) Ku S Sf (by
       intro t ht; apply roots t; exact ht)
 · -- J coordinate
   have hnz : qj (bernsteinApproximation n f t) ≠ 0 := hJ
   obtain ⟨S,Sf,roots⟩ := clm_bernstein_finite_roots n f qj t hnz
   have zc : Continuous z := (bernsteinApproximation n f).continuous
   have z0 : z 0 = (qNorth : Quaternion ℝ) := by
     dsimp [z]; simpa [f] using (bernsteinApproximation.apply_zero n f)
   have z1 : z 1 = (qNorth : Quaternion ℝ) := by
     dsimp [z]; simpa [f] using (bernsteinApproximation.apply_one hn f)
   let u : Quaternion ℝ := QuaternionAlgebra.mk 0 1 0 0
   exact transverse_small_bump_of_finite_roots qNorth z zc z0 z1 qj qi u
     (by rfl) (by rfl) (by rfl) (by rfl) S Sf (by
       intro t ht; apply roots t; exact ht)
 · -- K coordinate
   have hnz : qk (bernsteinApproximation n f t) ≠ 0 := hK
   obtain ⟨S,Sf,roots⟩ := clm_bernstein_finite_roots n f qk t hnz
   have zc : Continuous z := (bernsteinApproximation n f).continuous
   have z0 : z 0 = (qNorth : Quaternion ℝ) := by
     dsimp [z]; simpa [f] using (bernsteinApproximation.apply_zero n f)
   have z1 : z 1 = (qNorth : Quaternion ℝ) := by
     dsimp [z]; simpa [f] using (bernsteinApproximation.apply_one hn f)
   let u : Quaternion ℝ := QuaternionAlgebra.mk 0 1 0 0
   exact transverse_small_bump_of_finite_roots qNorth z zc z0 z1 qk qi u
     (by rfl) (by rfl) (by rfl) (by rfl) S Sf (by
       intro t ht; apply roots t; exact ht)
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/QuaternionPolynomialBump.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/BallDeleteSoft.lean
section
noncomputable section
open scoped Topology Manifold
open Set Topology unitInterval Metric
namespace NonlinearThreeManifoldSupport
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {T : Type} [TopologicalSpace T] [T2Space T] [ChartedSpace E T]

/-- `chartLocalBall_loops_null` with a base point different from the centre.
It is intentionally stated just for loops contained in the small chart. This
is the completely soft case in a deleted-chart proof. -/
lemma chartLocalBall_loops_at (b : T) (A : ChartBall (E:=E) b)
    (z : T) (hz : z ∈ chartLocalBall (E:=E) b A.R)
    (L : Path z z)
    (inside : ∀ t : I, L t ∈ chartLocalBall (E:=E) b A.R) :
    Path.Homotopic L (Path.refl z) := by
  let base : (Metric.ball (0:E) A.R : Set E) :=
    ⟨(chartAt E b) z - (chartAt E b) b,
      (mem_ball_zero_iff.mpr hz.2)⟩
  let lift : I → (Metric.ball (0:E) A.R : Set E) := fun t =>
    ⟨(chartAt E b) (L t) - (chartAt E b) b,
      (mem_ball_zero_iff.mpr (inside t).2)⟩
  have liftc : Continuous lift := by
    apply continuous_induced_rng.2
    let src : I → ((chartAt E b).source : Set T) := fun t =>
      ⟨L t, (inside t).1⟩
    have srcc : Continuous src := by
      apply continuous_induced_rng.2
      exact L.continuous
    have coord : Continuous (fun t : I => (chartAt E b) (L t)) :=
      ((chartAt E b).continuousOn.restrict).comp srcc
    exact coord.sub continuous_const
  have lift0 : lift 0 = base := by
    apply Subtype.ext
    dsimp [lift, base]
    rw [L.source]
  have lift1 : lift 1 = base := by
    apply Subtype.ext
    dsimp [lift, base]
    rw [L.target]
  let LL : Path base base :=
    { toFun := lift, continuous_toFun := liftc,
      source' := lift0, target' := lift1 }
  have BH : Path.Homotopic LL (Path.refl base) :=
    ball_paths_homotopic A.R LL (Path.refl base)
  let F : C((Metric.ball (0:E) A.R : Set E), T) := chartBallMap (E:=E) b A
  have bz : F base = z := by
    dsimp [F, base, chartBallMap]
    have sr := hz.1
    have v : (chartAt E b) b +
        ((chartAt E b) z - (chartAt E b) b) =
          (chartAt E b) z := by abel
    simpa [v] using ((chartAt E b).left_inv sr)
  have BM := BH.map F
  let P : Path z z := (LL.map F.continuous).cast bz.symm bz.symm
  let Q : Path z z := ((Path.refl base).map F.continuous).cast bz.symm bz.symm
  have BM' : Path.Homotopic P Q := by
    rcases BM with ⟨HH⟩
    refine ⟨{
      toFun := HH.toFun
      continuous_toFun := HH.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro t; exact HH.map_zero_left t
    · intro t; exact HH.map_one_left t
    · intro t u hu; exact HH.prop' t u hu
  have same : P = L := by
    apply Path.ext
    funext t
    change (chartAt E b).symm ((chartAt E b) b +
      ((chartAt E b) (L t) - (chartAt E b) b)) = L t
    have sr := (inside t).1
    have v : (chartAt E b) b +
        ((chartAt E b) (L t) - (chartAt E b) b) =
          (chartAt E b) (L t) := by abel
    simpa [v] using ((chartAt E b).left_inv sr)
  have rr : Q = Path.refl z := by
    apply Path.ext
    funext t
    dsimp [Q]
    exact bz
  rw [same, rr] at BM'
  exact BM'

/-- A loop entirely confined to the little coordinate ball already has a
representative in the deleted space: the constant loop at its (noncentral)
base point. The only hard paths in a deleted-chart comparison are the ones
that go out through the rim and return. -/
lemma chartLocalBall_lift_soft (b : T) (A : ChartBall (E:=E) b)
    (z : (({b}:Set T)ᶜ : Set T))
    (hz : (z:T) ∈ chartLocalBall (E:=E) b A.R)
    (p : Path (z:T) (z:T))
    (inside : ∀ t : I, p t ∈ chartLocalBall (E:=E) b A.R) :
    ∃ q : Path z z,
      Path.Homotopic (q.map continuous_subtype_val) p := by
  refine ⟨Path.refl z, ?_⟩
  have hp := chartLocalBall_loops_at (E:=E) b A (z:T) hz p inside
  have eq : (Path.refl z).map continuous_subtype_val = Path.refl (z:T) := by
    apply Path.ext
    funext t
    rfl
  rw [eq]
  exact hp.symm
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/BallDeleteSoft.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/PuncturedLifts.lean
section
noncomputable section
open scoped Quaternion Topology RealInnerProductSpace
open Topology Set Metric unitInterval
namespace NonlinearThreeManifoldSupport

/-- Every loop on the quaternion norm sphere beginning at the north pole has
an antipode-avoiding representative. This is a useful pointed version of
simple-connectedness: it uses a polynomial approximation followed by a tiny
transverse bump, so it doesn't make the invalid non-space-filling argument for
an arbitrary continuous loop. -/
lemma qnorth_loop_representative (a : Path qNorth qNorth) :
    ∃ c : Path qNorth qNorth, Path.Homotopic a c ∧
      ∀ t : I, (c t : Quaternion ℝ) ≠ -(qNorth : Quaternion ℝ) := by
  classical
  by_cases avoid : ∀ t : I, (a t : Quaternion ℝ) ≠ -(qNorth : Quaternion ℝ)
  · exact ⟨a, Path.Homotopic.refl a, avoid⟩
  · obtain ⟨n,hn,hc,h0,h1,hnear,hne,hold⟩ :=
      sphere_loop_bernstein_tilt qNorth a
    let f : C(I, Quaternion ℝ) :=
      ⟨(fun t : I => (a t : Quaternion ℝ)), by fun_prop⟩
    let z : I → Quaternion ℝ := fun t => bernsteinApproximation n f t
    have hnear' : ∀ t:I, ‖z t - (a t : Quaternion ℝ)‖ < (1/2:ℝ) := by
      simpa [z, f] using hnear
    obtain ⟨g,gc,g0,g1,gsmall,gbase⟩ :=
      qnorth_bernstein_bump a n hn avoid (by simpa [z, f] using hnear')
    let zz : I → Quaternion ℝ := fun t => z t + g t
    have zc : Continuous z := by simpa [z,f] using hc
    have z0 : z 0 = (qNorth : Quaternion ℝ) := by simpa [z,f] using h0
    have z1 : z 1 = (qNorth : Quaternion ℝ) := by simpa [z,f] using h1
    have zzc : Continuous zz := by dsimp [zz]; fun_prop
    have zz0 : zz 0 = (qNorth : Quaternion ℝ) := by simp [zz, z0, g0]
    have zz1 : zz 1 = (qNorth : Quaternion ℝ) := by simp [zz, z1, g1]
    have close : ∀ t:I, ‖zz t - (a t : Quaternion ℝ)‖ < (1:ℝ) := by
      intro t
      calc
        ‖zz t - (a t : Quaternion ℝ)‖ =
            ‖(z t - (a t : Quaternion ℝ)) + g t‖ := by congr 1 <;> simp [zz]; abel
        _ ≤ ‖z t - (a t : Quaternion ℝ)‖ + ‖g t‖ := norm_add_le _ _
        _ < (1:ℝ) := by linarith [hnear' t, gsmall t]
    have base : ∀ t:I, ¬ ∃ r:ℝ, r < 0 ∧ zz t = r • (qNorth : Quaternion ℝ) := by
      intro t
      simpa [zz,z,f] using (gbase t)
    exact sphere_loop_avoid_representative_of_close_base_test qNorth a zz zzc zz0 zz1 close base

lemma qnorth_loops_null : ∀ a : Path qNorth qNorth,
    Path.Homotopic a (Path.refl qNorth) := by
  exact sphere_loops_null_of_avoid_representatives qNorth qnorth_loop_representative

end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
open scoped Quaternion Topology
/-- The standard Q8 block has the deck group as a retract in its fundamental
group, with no simply-connected typeclass. The only needed upstairs fact is
the pointed loop calculation at the specified north sheet. -/
lemma explicitQ8_block_retract :
    letI : MulAction (QuaternionGroup 2) qSphere :=
      unitSphereAction ExplicitQ8.q8rho ExplicitQ8.q8rho_norm
    letI : ContinuousConstSMul (QuaternionGroup 2) qSphere :=
      unitSphereAction_cont ExplicitQ8.q8rho ExplicitQ8.q8rho_norm
    letI : IsCancelSMul (QuaternionGroup 2) qSphere :=
      unitSphereAction_cancel ExplicitQ8.q8rho ExplicitQ8.q8rho_norm ExplicitQ8.q8rho_injective
    ∃ (u : QuaternionGroup 2 →* FundamentalGroup (qOrbit (QuaternionGroup 2))
        ((Quotient.mk (MulAction.orbitRel (QuaternionGroup 2) qSphere)) qNorth))
      (d : FundamentalGroup (qOrbit (QuaternionGroup 2))
        ((Quotient.mk (MulAction.orbitRel (QuaternionGroup 2) qSphere)) qNorth) →* QuaternionGroup 2),
       d.comp u = MonoidHom.id (QuaternionGroup 2) := by
  letI : MulAction (QuaternionGroup 2) qSphere :=
      unitSphereAction ExplicitQ8.q8rho ExplicitQ8.q8rho_norm
  letI : ContinuousConstSMul (QuaternionGroup 2) qSphere :=
      unitSphereAction_cont ExplicitQ8.q8rho ExplicitQ8.q8rho_norm
  letI : IsCancelSMul (QuaternionGroup 2) qSphere :=
      unitSphereAction_cancel ExplicitQ8.q8rho ExplicitQ8.q8rho_norm ExplicitQ8.q8rho_injective
  apply qOrbit_block_retract_of_endpoint
    ExplicitQ8.q8rho ExplicitQ8.q8rho_norm ExplicitQ8.q8rho_injective qNorth
  exact IsCoveringMap.endpoint_inj_of_loops_at
    (qOrbitIsCovering (QuaternionGroup 2)) qNorth qnorth_loops_null
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/PuncturedLifts.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/ShrinkHomotopy.lean
section
open scoped Topology Manifold
open Set Topology unitInterval Metric
noncomputable section
namespace NonlinearThreeManifoldSupport
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

/-- The straight strip from the squeezed chart to the identity. This is useful in
using the deleted-point statement with `neckShrink`: it records explicitly the
basepoint track. On the rim of the ball it is stationay, so the conditional
definition is global, not just on the chart. -/
noncomputable def shrinkAlong (b : Y) (A : ChartBall (E:=E) b)
    (s : I × Y) : Y := by
  classical
  exact if h : s.2 ∈ chartLocalBall (E:=E) b A.R then
    (chartAt E b).symm ((chartAt E b) b +
      ((1 - (s.1:ℝ)) • ((chartAt E b) (neckShrink (E:=E) b A s.2) -
          (chartAt E b) b) +
        (s.1:ℝ) • ((chartAt E b) s.2 - (chartAt E b) b)))
  else s.2

private lemma __ShrinkHomotopy_convex_norm_lt {v w : E} {r α : ℝ}
    (hv : ‖v‖ < r) (hw : ‖w‖ < r) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ‖(1-α) • v + α • w‖ < r := by
  calc
    ‖(1-α) • v + α • w‖ ≤ ‖(1-α) • v‖ + ‖α • w‖ := norm_add_le _ _
    _ = (1-α) * ‖v‖ + α * ‖w‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg h0, abs_of_nonneg (sub_nonneg.mpr h1)]
    _ < r := by
      by_cases az : α = 0
      · simp [az, hv]
      by_cases ao : α = 1
      · simp [ao, hw]
      have ap : 0 < α := lt_of_le_of_ne h0 (Ne.symm az)
      have om : 0 < 1-α := sub_pos.mpr (lt_of_le_of_ne h1 ao)
      have p₁ : (1-α)*‖v‖ < (1-α)*r := mul_lt_mul_of_pos_left hv om
      have p₂ : α*‖w‖ < α*r := mul_lt_mul_of_pos_left hw ap
      linarith

private lemma __ShrinkHomotopy_along_target (b : Y) (A : ChartBall (E:=E) b)
    (s : I × Y) (hy : s.2 ∈ chartLocalBall (E:=E) b A.R) :
    (chartAt E b) b +
      ((1 - (s.1:ℝ)) • ((chartAt E b) (neckShrink (E:=E) b A s.2) -
          (chartAt E b) b) +
        (s.1:ℝ) • ((chartAt E b) s.2 - (chartAt E b) b)) ∈
      (chartAt E b).target := by
  apply A.sub
  rw [Metric.mem_ball, dist_eq_norm]
  have eqn : (chartAt E b) b +
      ((1 - (s.1:ℝ)) • ((chartAt E b) (neckShrink (E:=E) b A s.2) -
          (chartAt E b) b) + (s.1:ℝ) • ((chartAt E b) s.2 - (chartAt E b) b)) -
        (chartAt E b) b =
      (1 - (s.1:ℝ)) • ((chartAt E b) (neckShrink (E:=E) b A s.2) -
          (chartAt E b) b) + (s.1:ℝ) • ((chartAt E b) s.2 - (chartAt E b) b) := by abel
  rw [eqn]
  have hm := neckShrink_mem_local (E:=E) b A hy
  exact __ShrinkHomotopy_convex_norm_lt hm.2 hy.2 s.1.property.1 s.1.property.2

private lemma __ShrinkHomotopy_alongIn_cont (b : Y) (A : ChartBall (E:=E) b) :
    ContinuousOn (fun s : I × Y =>
      (chartAt E b).symm ((chartAt E b) b +
        ((1 - (s.1:ℝ)) • ((chartAt E b) (neckShrink (E:=E) b A s.2) -
          (chartAt E b) b) +
         (s.1:ℝ) • ((chartAt E b) s.2 - (chartAt E b) b))))
      ((Prod.snd) ⁻¹' (chartLocalBall (E:=E) b A.R)) := by
  -- Work on the subtype of the open chart to feed both partial charts.
  rw [continuousOn_iff_continuous_restrict]
  let S : Set (I × Y) := Prod.snd ⁻¹' (chartLocalBall (E:=E) b A.R)
  let yy : S → Y := fun z => z.1.2
  have yyc : Continuous yy := continuous_snd.comp continuous_subtype_val
  have ymem (z : S) : yy z ∈ chartLocalBall (E:=E) b A.R := z.property
  let xx : S → I := fun z => z.1.1
  have xxc : Continuous xx := continuous_fst.comp continuous_subtype_val
  let src1 : S → ((chartAt E b).source : Set Y) := fun z => ⟨yy z, (ymem z).1⟩
  have src1c : Continuous src1 := by
    apply continuous_induced_rng.2
    exact yyc
  have cy : Continuous (fun z : S => (chartAt E b) (yy z)) :=
    ((chartAt E b).continuousOn.restrict).comp src1c
  have nc : Continuous (fun z : S => neckShrink (E:=E) b A (yy z)) :=
    (neckShrink_continuous (E:=E) b A).comp yyc
  let src2 : S → ((chartAt E b).source : Set Y) := fun z =>
    ⟨neckShrink (E:=E) b A (yy z), (neckShrink_mem_local (E:=E) b A (ymem z)).1⟩
  have src2c : Continuous src2 := by
    apply continuous_induced_rng.2
    exact nc
  have cn : Continuous (fun z : S => (chartAt E b) (neckShrink (E:=E) b A (yy z))) :=
    ((chartAt E b).continuousOn.restrict).comp src2c
  let val : S → E := fun z => (chartAt E b) b +
        ((1 - ((xx z):ℝ)) • ((chartAt E b) (neckShrink (E:=E) b A (yy z)) -
          (chartAt E b) b) +
         ((xx z):ℝ) • ((chartAt E b) (yy z) - (chartAt E b) b))
  have valc : Continuous val := by
    dsimp [val]
    have xr : Continuous (fun z : S => ((xx z) : ℝ)) :=
      continuous_subtype_val.comp xxc
    fun_prop
  let tar : S → ((chartAt E b).target : Set E) := fun z =>
    ⟨val z, __ShrinkHomotopy_along_target (E:=E) b A z.1 (ymem z)⟩
  have tarc : Continuous tar := by
    apply continuous_induced_rng.2
    exact valc
  have fin : Continuous (fun z : S => (chartAt E b).symm (val z)) :=
    ((chartAt E b).symm.continuousOn.restrict).comp tarc
  -- the definitional `S` is the set in the restriction
  change Continuous (fun z : (Prod.snd ⁻¹' chartLocalBall (E:=E) b A.R : Set (I × Y)) =>
    (chartAt E b).symm ((chartAt E b) b +
        ((1 - ((z.1.1):ℝ)) • ((chartAt E b) (neckShrink (E:=E) b A z.1.2) -
          (chartAt E b) b) +
         ((z.1.1):ℝ) • ((chartAt E b) z.1.2 - (chartAt E b) b))))
  simpa [S, yy, xx, val] using fin

/-- `shrinkAlong` is a genuine continuous strip on the whole manifold.
Near the rim it is constant in the strip parameter since `neckShrink` is the
identity there. -/
lemma shrinkAlong_continuous (b : Y) (A : ChartBall (E:=E) b) :
    Continuous (shrinkAlong (E:=E) b A) := by
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : s.2 ∈ chartLocalBall (E:=E) b A.R
  · let S : Set (I × Y) := Prod.snd ⁻¹' (chartLocalBall (E:=E) b A.R)
    have Sop : IsOpen S := (chartLocalBall_open (E:=E) b A.R).preimage continuous_snd
    have ss : s ∈ S := hs
    let inside : I × Y → Y := fun t =>
      (chartAt E b).symm ((chartAt E b) b +
        ((1 - (t.1:ℝ)) • ((chartAt E b) (neckShrink (E:=E) b A t.2) -
          (chartAt E b) b) +
         (t.1:ℝ) • ((chartAt E b) t.2 - (chartAt E b) b)))
    have cin : ContinuousWithinAt inside S s :=
      (__ShrinkHomotopy_alongIn_cont (E:=E) b A) s hs
    have ca : ContinuousAt inside s := cin.continuousAt (Sop.mem_nhds ss)
    have ev : shrinkAlong (E:=E) b A =ᶠ[𝓝 s] inside := by
      filter_upwards [Sop.mem_nhds ss] with t ht
      change _ = _
      change t.2 ∈ chartLocalBall (E:=E) b A.R at ht
      simp [shrinkAlong, inside, ht]
    exact ca.congr_of_eventuallyEq ev
  · -- off the chart choose a smaller closed rim; on its complement the strip
    -- is independent of the first coordinate.
    let r : ℝ := 7*A.R/8
    have r0 : 0 ≤ r := by dsimp [r]; linarith [A.pos]
    have rR : r < A.R := by dsimp [r]; linarith [A.pos]
    let U : Set Y := (chartLocalClosed (E:=E) b r)ᶜ
    have Uop : IsOpen U := (chartLocalClosed_closed (E:=E) b A r0 rR).isOpen_compl
    have mem : s.2 ∈ U := by
      intro hn
      exact hs ⟨hn.1, lt_of_le_of_lt hn.2 rR⟩
    let S : Set (I × Y) := Prod.snd ⁻¹' U
    have Sop : IsOpen S := Uop.preimage continuous_snd
    have ss : s ∈ S := mem
    have same : ∀ t : I × Y, t ∈ S → shrinkAlong (E:=E) b A t = t.2 := by
      intro t ht
      have hU : t.2 ∈ U := ht
      by_cases hh : t.2 ∈ chartLocalBall (E:=E) b A.R
      · have large : 3*A.R/4 ≤ ‖(chartAt E b) t.2 - (chartAt E b) b‖ := by
          have notsmall : ¬ ‖(chartAt E b) t.2 - (chartAt E b) b‖ ≤ r := by
            intro ll
            exact hU ⟨hh.1, ll⟩
          have gt : r < ‖(chartAt E b) t.2 - (chartAt E b) b‖ := lt_of_not_ge notsmall
          dsimp [r] at gt ⊢
          linarith [A.pos]
        have eqid : neckShrink (E:=E) b A t.2 = t.2 :=
          neckShrink_of_large (E:=E) b A hh large
        rw [shrinkAlong, dif_pos hh, eqid]
        have vec : (1 - (t.1:ℝ)) • ((chartAt E b) t.2 - (chartAt E b) b) +
              (t.1:ℝ) • ((chartAt E b) t.2 - (chartAt E b) b) =
              (chartAt E b) t.2 - (chartAt E b) b := by module
        rw [vec]
        have add : (chartAt E b) b + ((chartAt E b) t.2 - (chartAt E b) b) =
            (chartAt E b) t.2 := by abel
        rw [add]
        exact (chartAt E b).left_inv hh.1
      · simp [shrinkAlong, hh]
    have ev : shrinkAlong (E:=E) b A =ᶠ[𝓝 s] (fun t : I × Y => t.2) := by
      filter_upwards [Sop.mem_nhds ss] with t ht
      exact same t ht
    exact (continuousAt_snd.congr_of_eventuallyEq ev)

lemma shrinkAlong_zero (b : Y) (A : ChartBall (E:=E) b) (y : Y) :
    shrinkAlong (E:=E) b A (0,y) = neckShrink (E:=E) b A y := by
  classical
  by_cases h : y ∈ chartLocalBall (E:=E) b A.R
  · rw [shrinkAlong, dif_pos h]
    have hm := neckShrink_mem_local (E:=E) b A h
    simp
    exact (chartAt E b).left_inv hm.1
  · rw [shrinkAlong, dif_neg h]
    simp [neckShrink, h]

lemma shrinkAlong_one (b : Y) (A : ChartBall (E:=E) b) (y : Y) :
    shrinkAlong (E:=E) b A (1,y) = y := by
  classical
  by_cases h : y ∈ chartLocalBall (E:=E) b A.R
  · rw [shrinkAlong, dif_pos h]
    simp
    have add : (chartAt E b) b + ((chartAt E b) y - (chartAt E b) b) =
        (chartAt E b) y := by abel
    -- `simp` above has already performed this addition.
    exact (chartAt E b).left_inv h.1
  · simp [shrinkAlong, h]

/-- The natural basepoint track of the squeezed map. -/
noncomputable def shrinkTrack (b : Y) (A : ChartBall (E:=E) b) (y : Y)
    (hy : neckShrink (E:=E) b A y = b) : Path b y :=
 { toFun := fun t => shrinkAlong (E:=E) b A (t,y)
   continuous_toFun := (shrinkAlong_continuous (E:=E) b A).comp
     (Continuous.prodMk continuous_id continuous_const)
   source' := (shrinkAlong_zero (E:=E) b A y).trans hy
   target' := shrinkAlong_one (E:=E) b A y }

end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
open unitInterval Set Topology
open scoped Topology Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]

noncomputable def shrinkMap (b:Y) (A:ChartBall (E:=E) b) : C(Y,Y) :=
  ⟨neckShrink (E:=E) b A, neckShrink_continuous (E:=E) b A⟩
noncomputable def shrinkHomotopy (b:Y) (A:ChartBall (E:=E) b) :
    (shrinkMap (E:=E) b A).Homotopy (ContinuousMap.id Y) :=
 { toFun := shrinkAlong (E:=E) b A
   continuous_toFun := shrinkAlong_continuous (E:=E) b A
   map_zero_left := shrinkAlong_zero (E:=E) b A
   map_one_left := shrinkAlong_one (E:=E) b A }
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
open Set Topology
open scoped Manifold Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace E Y]
lemma shrink_base_inside (b:Y) (A:ChartBall (E:=E) b)
    (y : (({b}:Set Y)ᶜ : Set Y))
    (hy : shrinkOnPuncture (E:=E) b A y = b) :
    (y:Y) ∈ chartLocalBall (E:=E) b A.R := by
  classical
  by_contra hn
  have eq : neckShrink (E:=E) b A (y:Y) = (y:Y) := by
    simp [neckShrink, hn]
  have yb : (y:Y) = b := eq.symm.trans hy
  exact y.property (by simpa [yb])
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/ShrinkHomotopy.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/TrackIso.lean
section
open scoped Topology
open Topology Set
noncomputable section
namespace NonlinearThreeManifoldSupport.BasedCMap
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {b y : Y}
/-- Moving the base point along a path does not change the loop comparison.
    This version is deliberately at the representative level.  It is the
    useful interface for an *unbased* homotopy: its naturality square says
    `F(a) · k = k · i(a)` for every representative loop.
-/
lemma piOne_bijective_of_track (i : BasedCMap X x Y y)
    (f : BasedCMap X x Y b) (k : Path b y)
    (sq : ∀ a : Path x x,
      Path.Homotopic
        (((a.map f.toContinuousMap.continuous).cast
            f.map_pt.symm f.map_pt.symm).trans k)
        (k.trans ((a.map i.toContinuousMap.continuous).cast
            i.map_pt.symm i.map_pt.symm)))
    (hi : Function.Bijective (piOne i)) :
    Function.Bijective (piOne f) := by
  -- Work in the fundamental groupoid.  There composition and cancellation of
  -- the whiskering path are just the groupoid simp lemmas; no reassociation
  -- of path `trans` on representatives is required.
  let K : Path.Homotopic.Quotient b y := Path.Homotopic.Quotient.mk k
  have eqn (a : Path x x) :
      Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk
          ((a.map f.toContinuousMap.continuous).cast
            f.map_pt.symm f.map_pt.symm)) K =
      Path.Homotopic.Quotient.trans K
        (Path.Homotopic.Quotient.mk
          ((a.map i.toContinuousMap.continuous).cast
            i.map_pt.symm i.map_pt.symm)) := by
    change Path.Homotopic.Quotient.mk
       (((a.map f.toContinuousMap.continuous).cast
            f.map_pt.symm f.map_pt.symm).trans k) =
      Path.Homotopic.Quotient.mk
       (k.trans ((a.map i.toContinuousMap.continuous).cast
            i.map_pt.symm i.map_pt.symm))
    exact Quotient.sound (sq a)
  -- Formula obtained by removing the last `k` in the square.
  have form (a : Path x x) :
      Path.Homotopic.Quotient.mk
          ((a.map f.toContinuousMap.continuous).cast
            f.map_pt.symm f.map_pt.symm) =
      Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.trans K
          (Path.Homotopic.Quotient.mk
            ((a.map i.toContinuousMap.continuous).cast
              i.map_pt.symm i.map_pt.symm)))
        (Path.Homotopic.Quotient.symm K) := by
    -- append `K⁻¹` to `eqn`; simp is the groupoid simp normal form
    calc
      _ = Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.mk
              ((a.map f.toContinuousMap.continuous).cast
                f.map_pt.symm f.map_pt.symm)) K)
          (Path.Homotopic.Quotient.symm K) := by simp
      _ = Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.trans K
            (Path.Homotopic.Quotient.mk
              ((a.map i.toContinuousMap.continuous).cast
                i.map_pt.symm i.map_pt.symm)))
          (Path.Homotopic.Quotient.symm K) := by rw [eqn a]
  constructor
  · intro A B hAB
    change Path.Homotopic.Quotient x x at A B
    induction A using Quotient.inductionOn with | _ a => ?_
    induction B using Quotient.inductionOn with | _ d => ?_
    -- read both maps on the representatives
    change (FundamentalGroup.mapOfEq f.toContinuousMap _)
        (FundamentalGroup.fromPath (.mk a)) =
      (FundamentalGroup.mapOfEq f.toContinuousMap _)
        (FundamentalGroup.fromPath (.mk d)) at hAB
    rw [FundamentalGroup.mapOfEq_apply,
        FundamentalGroup.mapOfEq_apply] at hAB
    -- remove the same two whiskers, using the displayed formula.
    have core : Path.Homotopic.Quotient.mk
          ((a.map i.toContinuousMap.continuous).cast
            i.map_pt.symm i.map_pt.symm) =
        Path.Homotopic.Quotient.mk
          ((d.map i.toContinuousMap.continuous).cast
            i.map_pt.symm i.map_pt.symm) := by
      have wing :
          Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans K
              (Path.Homotopic.Quotient.mk
                ((a.map i.toContinuousMap.continuous).cast
                  i.map_pt.symm i.map_pt.symm)))
            (Path.Homotopic.Quotient.symm K) =
          Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans K
              (Path.Homotopic.Quotient.mk
                ((d.map i.toContinuousMap.continuous).cast
                  i.map_pt.symm i.map_pt.symm)))
            (Path.Homotopic.Quotient.symm K) :=
        (form a).symm.trans (hAB.trans (form d))
      -- cancel the two groupoid whiskers by composing with them
      have right1 := congrArg (fun z => Path.Homotopic.Quotient.trans z K) wing
      have right2 :
          Path.Homotopic.Quotient.trans K
            (Path.Homotopic.Quotient.mk
              ((a.map i.toContinuousMap.continuous).cast
                i.map_pt.symm i.map_pt.symm)) =
          Path.Homotopic.Quotient.trans K
            (Path.Homotopic.Quotient.mk
              ((d.map i.toContinuousMap.continuous).cast
                i.map_pt.symm i.map_pt.symm)) := by
        simpa using right1
      have left := congrArg (fun z => Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.symm K) z) right2
      simpa [← Path.Homotopic.Quotient.trans_assoc] using left
    apply hi.1
    change (FundamentalGroup.mapOfEq i.toContinuousMap _)
        (FundamentalGroup.fromPath (.mk a)) =
      (FundamentalGroup.mapOfEq i.toContinuousMap _)
        (FundamentalGroup.fromPath (.mk d))
    rw [FundamentalGroup.mapOfEq_apply,
        FundamentalGroup.mapOfEq_apply]
    exact core
  · intro z
    change Path.Homotopic.Quotient b b at z
    -- the loop at the old base obtained by conjugating with the track
    let old : Path.Homotopic.Quotient y y :=
      Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm K) z) K
    -- use surjectivity of the old based map
    have oldhit := hi.2 old
    rcases oldhit with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    change Path.Homotopic.Quotient x x at u
    induction u using Quotient.inductionOn with | _ a => ?_
    change (FundamentalGroup.mapOfEq i.toContinuousMap _)
        (FundamentalGroup.fromPath (.mk a)) = old at hu
    rw [FundamentalGroup.mapOfEq_apply] at hu
    change Path.Homotopic.Quotient.mk
      ((a.map i.toContinuousMap.continuous).cast
        i.map_pt.symm i.map_pt.symm) = old at hu
    change (FundamentalGroup.mapOfEq f.toContinuousMap _)
      (FundamentalGroup.fromPath (.mk a)) = z
    rw [FundamentalGroup.mapOfEq_apply]
    change Path.Homotopic.Quotient.mk
      ((a.map f.toContinuousMap.continuous).cast
        f.map_pt.symm f.map_pt.symm) = z
    rw [form a, hu]
    -- the two conjugations cancel
    dsimp [old]
    simp [← Path.Homotopic.Quotient.trans_assoc]
    simp
end NonlinearThreeManifoldSupport.BasedCMap
namespace NonlinearThreeManifoldSupport.BasedCMap
open Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
/-- Unpointed homotopy, with its endpoint track. Keeping the base points
    definitional in this lemma makes all endpoint casts `rfl`; arbitrary
    written endpoints can be recovered by `cases` on their equalities. -/
lemma piOne_bijective_comp_of_homotopy (g : C(X,Y)) (x : X)
    (S : C(Y,Y)) (H : S.Homotopy (ContinuousMap.id Y))
    (hi : Function.Bijective
      (piOne ({ toContinuousMap := g, map_pt := rfl } :
        BasedCMap X x Y (g x)))) :
    Function.Bijective
      (piOne ({ toContinuousMap := S.comp g, map_pt := rfl } :
        BasedCMap X x Y (S (g x)))) := by
  let i : BasedCMap X x Y (g x) :=
    { toContinuousMap := g, map_pt := rfl }
  let f : BasedCMap X x Y (S (g x)) :=
    { toContinuousMap := S.comp g, map_pt := rfl }
  apply piOne_bijective_of_track i f (H.evalAt (g x)) ?_ hi
  intro a
  change Path.Homotopic
    (((a.map (S.comp g).continuous).cast rfl rfl).trans (H.evalAt (g x)))
    ((H.evalAt (g x)).trans
      ((a.map g.continuous).cast rfl rfl))
  simpa using (Path.Homotopic.map_trans_evalAt H (a.map g.continuous))
end NonlinearThreeManifoldSupport.BasedCMap
namespace NonlinearThreeManifoldSupport.BasedCMap
open Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
lemma piOne_bijective_comp_of_homotopy_eq (g : C(X,Y)) (x : X)
    (S : C(Y,Y)) (H : S.Homotopy (ContinuousMap.id Y))
    (y b : Y) (hy : g x = y) (hb : S y = b)
    (hi : Function.Bijective
      (piOne ({ toContinuousMap := g, map_pt := hy } :
        BasedCMap X x Y y))) :
    Function.Bijective
      (piOne ({ toContinuousMap := S.comp g,
                map_pt := (congrArg (fun u => S u) hy).trans hb } :
        BasedCMap X x Y b)) := by
  subst y
  subst b
  simpa using piOne_bijective_comp_of_homotopy g x S H hi
end NonlinearThreeManifoldSupport.BasedCMap

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/TrackIso.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/BallDeleteStar.lean
section
noncomputable section
open scoped Topology Manifold
open Set Topology unitInterval Metric
namespace NonlinearThreeManifoldSupport
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {T : Type} [TopologicalSpace T] [T2Space T] [ChartedSpace E T]

/-- A small second soft case for deletion.  In translated coordinates a
straight contraction to the base point is valid even in the punctured chart,
provided its line segments do not run through the origin.  This deliberately
keeps that test explicit.  It is often useful to clear all loops which stay on
one star-shaped side of the missing point before attempting a relative cut of
a disc.

Notice the homotopy is in the *deleted* type.  The superficially similar
`chartLocalBall_loops_at` contracts in the ambient manifold and is not enough
for injectivity of deletion. -/
lemma chartLocalBall_star_null_deleted (b : T) (A : ChartBall (E:=E) b)
    (z : (({b}:Set T)ᶜ : Set T))
    (hz : (z:T) ∈ chartLocalBall (E:=E) b A.R)
    (L : Path z z)
    (inside : ∀ t : I, (L t:T) ∈ chartLocalBall (E:=E) b A.R)
    (away : ∀ s t : I,
      (1 - (s:ℝ)) • ((chartAt E b) (L t:T) - (chartAt E b) b) +
          (s:ℝ) • ((chartAt E b) (z:T) - (chartAt E b) b) ≠ (0:E)) :
    Path.Homotopic L (Path.refl z) := by
  let c : I → E := fun t =>
    (chartAt E b) (L t:T) - (chartAt E b) b
  let w : E := (chartAt E b) (z:T) - (chartAt E b) b
  have cc : Continuous c := by
    let src : I → ((chartAt E b).source : Set T) := fun t =>
      ⟨(L t:T), (inside t).1⟩
    have srcc : Continuous src := by
      apply continuous_induced_rng.2
      change Continuous (fun t : I => (L t : T))
      exact continuous_subtype_val.comp L.continuous
    have hcoord : Continuous (fun t : I => (chartAt E b) (L t:T)) :=
      ((chartAt E b).continuousOn.restrict).comp srcc
    exact hcoord.sub continuous_const
  have cmem (t : I) : c t ∈ Metric.ball (0:E) A.R := by
    exact mem_ball_zero_iff.mpr (inside t).2
  have wmem : w ∈ Metric.ball (0:E) A.R :=
    mem_ball_zero_iff.mpr hz.2
  let raw : I × I → E := fun st =>
    (1 - (st.1:ℝ)) • c st.2 + (st.1:ℝ) • w
  have rawmem (st : I × I) : raw st ∈ Metric.ball (0:E) A.R := by
    have ht : (st.1 : ℝ) ∈ Set.Icc (0:ℝ) 1 := st.1.property
    have hm := (convex_ball (0:E) A.R).lineMap_mem (cmem st.2) wmem ht
    simpa [raw, AffineMap.lineMap_apply, sub_smul, one_smul,
      vsub_eq_sub, add_comm, add_left_comm, add_assoc,
      sub_eq_add_neg, add_smul] using hm
  let cv : I × I → (Metric.ball (0:E) A.R : Set E) :=
    fun st => ⟨raw st, rawmem st⟩
  have cvc : Continuous cv := by
    apply continuous_induced_rng.2
    change Continuous raw
    dsimp [raw]
    fun_prop
  let F0 : I × I → T := fun st => chartBallMap (E:=E) b A (cv st)
  have F0c : Continuous F0 :=
    (chartBallMap (E:=E) b A).continuous.comp cvc
  -- The inverse chart of a nonzero translated vector is not the centre.
  have F0ne (st : I × I) : F0 st ≠ b := by
    intro eqb
    have targ : (chartAt E b) b + raw st ∈ (chartAt E b).target := by
      apply A.sub
      change dist ((chartAt E b) b + raw st) ((chartAt E b) b) < A.R
      rw [dist_eq_norm]
      have hv : (chartAt E b) b + raw st - (chartAt E b) b = raw st := by
        abel
      rw [hv]
      exact mem_ball_zero_iff.mp (rawmem st)
    have ce := congrArg (fun x : T => (chartAt E b) x) eqb
    have ce' : (chartAt E b) b + raw st = (chartAt E b) b := by
      -- `right_inv` is the only inverse fact needed here; both points are
      -- in the little target chosen by `ChartBall`.
      change (chartAt E b)
        ((chartAt E b).symm ((chartAt E b) b + raw st)) =
            (chartAt E b) b at ce
      rw [(chartAt E b).right_inv targ] at ce
      exact ce
    have rr : raw st = (0:E) := by
      apply add_left_cancel (a := (chartAt E b) b)
      simpa using ce'
    have av := away st.1 st.2
    exact av (by simpa [raw, c, w] using rr)
  let F : I × I → (({b}:Set T)ᶜ : Set T) := fun st =>
    ⟨F0 st, (by
      have hne := F0ne st
      simpa using hne)⟩
  have Fc : Continuous F := by
    apply continuous_induced_rng.2
    exact F0c
  refine ⟨({ toFun := F
             continuous_toFun := Fc
             map_zero_left := ?_
             map_one_left := ?_
             prop' := ?_ } : L.Homotopy (Path.refl z))⟩
  · intro t
    apply Subtype.ext
    change (chartAt E b).symm
      ((chartAt E b) b +
        ((1 - (0:ℝ)) • c t + (0:ℝ) • w)) = (L t:T)
    have vv : (chartAt E b) b + c t = (chartAt E b) (L t:T) := by
      dsimp [c]
      abel
    simpa [vv] using ((chartAt E b).left_inv (inside t).1)
  · intro t
    apply Subtype.ext
    change (chartAt E b).symm
      ((chartAt E b) b +
        ((1 - (1:ℝ)) • c t + (1:ℝ) • w)) = (z:T)
    have vv : (chartAt E b) b + w = (chartAt E b) (z:T) := by
      dsimp [w]
      abel
    simpa [vv] using ((chartAt E b).left_inv hz.1)
  · intro s t ht
    -- on either horizontal edge `L` is its own base point `z`
    have et : (L t : (({b}:Set T)ᶜ : Set T)) = z := by
      rcases ht with ht | ht
      · change t = (0:I) at ht
        subst t
        exact L.source
      · have ht' : t = (1:I) := by simpa using ht
        subst t
        exact L.target
    have ec : c t = w := by
      dsimp [c, w]
      rw [et]
    apply Subtype.ext
    change (chartAt E b).symm
      ((chartAt E b) b +
        ((1 - (s:ℝ)) • c t + (s:ℝ) • w)) = (L t:T)
    rw [ec]
    rw [← add_smul]
    have hs : (1 - (s:ℝ)) + (s:ℝ) = (1:ℝ) := by ring
    rw [hs, one_smul]
    have vv : (chartAt E b) b + w = (chartAt E b) (z:T) := by
      dsimp [w]
      abel
    have ev : (L t:T) = (z:T) := congrArg Subtype.val et
    rw [ev]
    simpa [vv] using ((chartAt E b).left_inv hz.1)
end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open scoped Topology Manifold
open Set Topology unitInterval Metric
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {T : Type} [TopologicalSpace T] [T2Space T] [ChartedSpace E T]
/-- Representative version; no choices have to respect concatenation.  This
is the right interface when the next cut of a disc first changes the boundary
loop. -/
lemma chartLocalBall_star_rep_null_deleted (b : T) (A : ChartBall (E:=E) b)
    (z : (({b}:Set T)ᶜ : Set T))
    (hz : (z:T) ∈ chartLocalBall (E:=E) b A.R)
    (K : Path z z)
    (rep : ∃ L : Path z z, Path.Homotopic K L ∧
      (∀ t : I, (L t:T) ∈ chartLocalBall (E:=E) b A.R) ∧
      (∀ s t : I,
        (1 - (s:ℝ)) • ((chartAt E b) (L t:T) - (chartAt E b) b) +
          (s:ℝ) • ((chartAt E b) (z:T) - (chartAt E b) b) ≠ (0:E))) :
    Path.Homotopic K (Path.refl z) := by
  rcases rep with ⟨L,hKL,hinside,hstar⟩
  exact hKL.trans
    (chartLocalBall_star_null_deleted (E:=E) b A z hz L hinside hstar)
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/BallDeleteStar.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/PuncturedSphereOne.lean
section
open scoped Topology RealInnerProductSpace Quaternion
open Topology Set Metric unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport

/-- Paths with the same endpoints in a real topological vector space are homotopic
rel their endpoints. Kept in an elementary path form since useful with stereographic
charts (no `SimplyConnectedSpace` bookkeeping). -/
lemma vector_paths_homotopic {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {x y : V} (p q : Path x y) :
    Path.Homotopic p q := by
  let h : I × I → V := fun z =>
    (1 - (z.1 : ℝ)) • p z.2 + (z.1 : ℝ) • q z.2
  have hc : Continuous h := by
    dsimp [h]
    fun_prop
  refine ⟨{
    toFun := h
    continuous_toFun := hc
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    change (1 - (0:ℝ)) • p t + (0:ℝ) • q t = p t
    simp
  · intro t
    change (1 - (1:ℝ)) • p t + (1:ℝ) • q t = q t
    simp
  · intro s t ht
    have eqv : p t = q t := by
      rcases ht with ht | ht
      · change t = (0:I) at ht
        subst t
        exact p.source.trans q.source.symm
      · have ht' : t = (1:I) := by simpa using ht
        subst t
        exact p.target.trans q.target.symm
    change (1 - (s:ℝ)) • p t + (s:ℝ) • q t = p t
    rw [← eqv]
    rw [← add_smul]
    have hh : (1 - (s:ℝ)) + (s:ℝ) = 1 := by ring
    rw [hh, one_smul]

/-- Same lemma for a vector-space copy given by a homeomorphism. -/
lemma paths_homotopic_of_homeo_vector {X V : Type*}
    [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : X ≃ₜ V) {x y : X} (p q : Path x y) : Path.Homotopic p q := by
  let h : I × I → X := fun z => e.symm
      ((1 - (z.1 : ℝ)) • e (p z.2) + (z.1 : ℝ) • e (q z.2))
  have hc : Continuous h := by
    dsimp [h]
    fun_prop
  refine ⟨{
    toFun := h
    continuous_toFun := hc
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    change e.symm ((1 - (0:ℝ)) • e (p t) + (0:ℝ) • e (q t)) = p t
    simp
  · intro t
    change e.symm ((1 - (1:ℝ)) • e (p t) + (1:ℝ) • e (q t)) = q t
    simp
  · intro s t ht
    have eqv : p t = q t := by
      rcases ht with ht | ht
      · change t = (0:I) at ht
        subst t
        exact p.source.trans q.source.symm
      · have ht' : t = (1:I) := by simpa using ht
        subst t
        exact p.target.trans q.target.symm
    change e.symm ((1 - (s:ℝ)) • e (p t) + (s:ℝ) • e (q t)) = p t
    rw [← eqv]
    rw [← add_smul]
    have hh : (1 - (s:ℝ)) + (s:ℝ) = 1 := by ring
    rw [hh, one_smul]
    exact e.symm_apply_apply _

/-- The actual stereographic chart is global on the deleted north pole. It
makes that particular deletion completely harmless for based loops.  This
small lemma often avoids doing a local perturbation when a lifted loop misses
all deck translates except a chosen sheet. -/
lemma sphere_delete_one_paths
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (c : Metric.sphere (0:V) 1) {x y : (({c} : Set (Metric.sphere (0:V) 1))ᶜ : Set (Metric.sphere (0:V) 1))}
    (p q : Path x y) : Path.Homotopic p q := by
  let O := stereographic (norm_eq_of_mem_sphere c)
  have src : O.source = ({c} : Set (Metric.sphere (0:V) 1))ᶜ := by
    simpa [O] using (stereographic_source (norm_eq_of_mem_sphere c))
  let ee := O.toHomeomorphSourceTarget
  /- Target is the subtype of `univ`; identify it with the orthogonal
     hyperplane itself rather than asking a contractibility instance for a
     partial chart. -/
  let univHomeo : (Set.univ : Set ((ℝ ∙ (c:V))ᗮ)) ≃ₜ ((ℝ ∙ (c:V))ᗮ) :=
    Homeomorph.Set.univ ((ℝ ∙ (c:V))ᗮ)
  have tgt : O.target = (Set.univ : Set ((ℝ ∙ (c:V))ᗮ)) := rfl
  -- first identify the source subtype by the formula for the source
  let srcHomeo :
      (({c} : Set (Metric.sphere (0:V) 1))ᶜ : Set (Metric.sphere (0:V) 1)) ≃ₜ
        O.source :=
    Homeomorph.setCongr src.symm
  let tgtHomeo : O.target ≃ₜ ((ℝ ∙ (c:V))ᗮ) := by
    rw [tgt]
    exact univHomeo
  let Ehome :
      (({c} : Set (Metric.sphere (0:V) 1))ᶜ : Set (Metric.sphere (0:V) 1)) ≃ₜ
        ((ℝ ∙ (c:V))ᗮ) :=
    srcHomeo.trans (ee.trans tgtHomeo)
  exact paths_homotopic_of_homeo_vector Ehome p q

lemma sphere_delete_one_loop_null
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (c : Metric.sphere (0:V) 1)
    (x : (({c} : Set (Metric.sphere (0:V) 1))ᶜ : Set (Metric.sphere (0:V) 1)))
    (p : Path x x) : Path.Homotopic p (Path.refl x) :=
  sphere_delete_one_paths c p (Path.refl x)

end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/PuncturedSphereOne.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/SphereFiniteAvoid.lean
section
open scoped Quaternion RealInnerProductSpace Topology
open Topology Set Metric unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport
/-- A path on the quaternion sphere can avoid a prescribed nonempty finite set;
this is the useful one-dimensional part of deleting a point downstairs. -/
lemma qSphere_path_avoid_finite (F : Set qSphere) (hf : F.Finite)
    (hn : F.Nonempty) (x y : qSphere) (hx : x ∉ F) (hy : y ∉ F) :
    ∃ p : Path x y, ∀ t : unitInterval, p t ∉ F := by
  classical
  obtain ⟨c,hc⟩ := hn
  have cnorm : ‖(c : Quaternion ℝ)‖ = 1 := by
    have h := c.property
    change dist (c : Quaternion ℝ) 0 = 1 at h
    simpa [dist_zero_right] using h
  let O := stereographic cnorm
  let W := ((ℝ ∙ (c : Quaternion ℝ))ᗮ)
  have src : O.source = ({c} : Set qSphere)ᶜ := by
    simpa [O] using (stereographic_source cnorm)
  have tgt : O.target = (Set.univ : Set W) := rfl
  have xs : x ∈ O.source := by
    rw [src]; simp [ne_of_mem_of_not_mem hc hx |>.symm]
  have ys : y ∈ O.source := by
    rw [src]; simp [ne_of_mem_of_not_mem hc hy |>.symm]
  let bad : Set W := O '' (F ∩ O.source)
  have badf : bad.Finite := (hf.inter_of_left _).image _
  have xb : O x ∈ badᶜ := by
    intro h
    rcases h with ⟨z, hz, ez⟩
    have eqz : z = x := O.injOn hz.2 xs ez
    exact hx (eqz ▸ hz.1)
  have yb : O y ∈ badᶜ := by
    intro h
    rcases h with ⟨z, hz, ez⟩
    have eqz : z = y := O.injOn hz.2 ys ez
    exact hy (eqz ▸ hz.1)
  have fspan : Module.finrank ℝ (ℝ ∙ (c : Quaternion ℝ)) = 1 := by
    apply finrank_span_singleton
    intro h
    have hh := cnorm
    simp [h] at hh
  have fw : Module.finrank ℝ W = 3 := by
    have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ (c : Quaternion ℝ))
    have fq : Module.finrank ℝ (Quaternion ℝ) = 4 := Quaternion.finrank_eq_four (R := ℝ)
    rw [fspan, fq] at h
    change 1 + Module.finrank ℝ W = 4 at h
    omega
  have wrank : 1 < Module.rank ℝ W := by
    rw [← Module.finrank_eq_rank]
    rw [fw]
    exact_mod_cast (by decide : (1:ℕ) < 3)
  have pc : IsPathConnected badᶜ :=
    Set.Countable.isPathConnected_compl_of_one_lt_rank wrank badf.countable
  let j : JoinedIn badᶜ (O x) (O y) := pc.joinedIn (O x) xb (O y) yb
  let r : Path (O x) (O y) := j.somePath
  have Osym : Continuous (O.symm : W → qSphere) := by
    rw [continuous_iff_continuousAt]
    intro w
    have hc := O.continuousOn_symm
    rw [tgt] at hc
    exact (continuousOn_univ.mp hc).continuousAt
  let p0 := r.map Osym
  have e0 : O.symm (O x) = x := O.left_inv xs
  have e1 : O.symm (O y) = y := O.left_inv ys
  let p : Path x y := p0.cast e0.symm e1.symm
  refine ⟨p, ?_⟩
  intro t ht
  have rt : r t ∈ badᶜ := j.somePath_mem t
  have rtar : r t ∈ O.target := by rw [tgt]; trivial
  have invsrc : O.symm (r t) ∈ O.source := O.symm.map_source rtar
  have oi : O (O.symm (r t)) = r t := O.right_inv rtar
  have eqval : p t = O.symm (r t) := rfl
  rw [eqval] at ht
  have badmem : O (O.symm (r t)) ∈ bad := ⟨O.symm (r t), ⟨ht, invsrc⟩, rfl⟩
  exact rt (oi ▸ badmem)
end NonlinearThreeManifoldSupport
namespace NonlinearThreeManifoldSupport
/-- Pointed calculation at north gives path uniqueness between arbitrary two sheets. -/
lemma qSphere_any_paths (x y : qSphere) (p q : Path x y) :
    Path.Homotopic p q := by
  let j : JoinedIn (Set.univ : Set qSphere) qNorth x :=
    isPathConnected_univ.joinedIn _ (by trivial) _ (by trivial)
  let k : Path qNorth x := j.somePath
  have h := start_paths_of_loops_at qNorth qnorth_loops_null y (k.trans p) (k.trans q)
  -- Cancel the whisker `k` on homotopies themselves.  Keeping all
  -- intermediate endpoints typed avoids relying on the ambiguous relation
  -- `trans` (there are both path and quotient transitivity operations).
  have cancel (r : Path x y) :
      Path.Homotopic (k.symm.trans (k.trans r)) r := by
    have hassoc :
        Path.Homotopic ((k.symm.trans k).trans r)
          (k.symm.trans (k.trans r)) :=
      Path.Homotopic.trans_assoc k.symm k r
    have hkk : Path.Homotopic (k.symm.trans k) (Path.refl x) :=
      Path.Homotopic.symm_trans k
    have hstep :
        Path.Homotopic ((k.symm.trans k).trans r)
          ((Path.refl x).trans r) :=
      Path.Homotopic.hcomp hkk (Path.Homotopic.refl r)
    have hunit : Path.Homotopic ((Path.refl x).trans r) r :=
      Path.Homotopic.refl_trans r
    exact Path.Homotopic.trans
      (Path.Homotopic.symm hassoc)
      (Path.Homotopic.trans hstep hunit)
  have hmid :
      Path.Homotopic (k.symm.trans (k.trans p))
        (k.symm.trans (k.trans q)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _) h
  exact Path.Homotopic.trans (Path.Homotopic.symm (cancel p))
    (Path.Homotopic.trans hmid (cancel q))
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/SphereFiniteAvoid.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/OrbitDeleteBasics.lean
section
open scoped Quaternion RealInnerProductSpace Topology
open Topology Set Metric unitInterval
open CategoryTheory
noncomputable section
namespace NonlinearThreeManifoldSupport

-- the fiber of an orbit quotient over a chosen sheet is a finite set
lemma orbit_fiber_finite (G : Type*) [Group G] [MulAction G qSphere]
    [Finite G] (c : qSphere) :
    ({z : qSphere |
       (Quotient.mk (MulAction.orbitRel G qSphere)) z =
        (Quotient.mk (MulAction.orbitRel G qSphere)) c}).Finite := by
  classical
  -- every point of this fiber is a translate of `c`
  let f : G → qSphere := fun g => g • c
  have hr : Set.range f |>.Finite := Set.finite_range _
  refine hr.subset ?_
  intro z hz
  have rel : (MulAction.orbitRel G qSphere).r z c :=
    (_root_.Quotient.eq).1 hz
  -- the orbit relation is membership in the orbit of the right member
  change z ∈ MulAction.orbit G c at rel
  obtain ⟨g, hg⟩ := (MulAction.mem_orbit_iff).1 rel
  exact ⟨g, hg⟩

/-- Any loop in a finite quaternionic spherical quotient has a representative
avoiding a specified point of the quotient.  Only the path part of general
position is used here: lift it, join the lifted endpoints in the complement
of the finite fibre, and use path uniqueness on the whole 3-sphere. -/
lemma qOrbit_delete_point_surj
    (G : Type*) [Group G] [MulAction G qSphere]
    [ContinuousConstSMul G qSphere] [Finite G]
    [IsCancelSMul G qSphere]
    (b : qOrbit G) (y : (({b} : Set (qOrbit G))ᶜ : Set (qOrbit G)))
    (p : Path (y : qOrbit G) (y : qOrbit G)) :
    ∃ q : Path y y, Path.Homotopic (q.map continuous_subtype_val) p := by
  classical
  let π : qSphere → qOrbit G := Quotient.mk (MulAction.orbitRel G qSphere)
  let cov : IsCoveringMap (π) := qOrbitIsCovering G
  obtain ⟨e, he⟩ := Quotient.exists_rep (y:qOrbit G)
  -- spelling out the quotient map assists `liftPath`
  change π e = (y:qOrbit G) at he
  have e0 : p 0 = π e := p.source.trans he.symm
  let l : C(unitInterval, qSphere) := cov.liftPath p e e0
  have l0 : l 0 = e := cov.liftPath_zero _ _ _
  let e' : qSphere := l 1
  have e1 : π e' = (y:qOrbit G) :=
    (congr_fun (cov.liftPath_lifts p e e0) 1).trans p.target
  -- choose a sheet `c` above the forbidden point
  obtain ⟨c, hc⟩ := Quotient.exists_rep b
  change π c = b at hc
  let F : Set qSphere := {z | π z = π c}
  have Ffin : F.Finite := by
    change ({z : qSphere | (Quotient.mk (MulAction.orbitRel G qSphere)) z =
      (Quotient.mk (MulAction.orbitRel G qSphere)) c}).Finite
    exact orbit_fiber_finite G c
  have Fnon : F.Nonempty := ⟨c, rfl⟩
  have ene : e ∉ F := by
    intro h
    have yy : (y:qOrbit G) = b := by
      have : π e = π c := h
      exact he.symm.trans (this.trans hc)
    exact y.property (by simpa using yy)
  have ene' : e' ∉ F := by
    intro h
    have yy : (y:qOrbit G) = b := by
      have : π e' = π c := h
      exact e1.symm.trans (this.trans hc)
    exact y.property (by simpa using yy)
  obtain ⟨r, hr⟩ := qSphere_path_avoid_finite F Ffin Fnon e e' ene ene'
  -- project this new upstairs path to the deleted base
  have projmiss : ∀ t : unitInterval, π (r t) ≠ b := by
    intro t eq
    apply (hr t)
    -- membership in this fibre is equality with `π c`
    exact eq.trans hc.symm
  let val : unitInterval → (({b} : Set (qOrbit G))ᶜ : Set (qOrbit G)) :=
    fun t => ⟨π (r t), (by
      change π (r t) ∉ ({b}:Set (qOrbit G))
      simpa using projmiss t)⟩
  have valc : Continuous val := by
    apply continuous_induced_rng.2
    exact (cov.continuous.comp r.continuous)
  have val0 : val 0 = y := by
    apply Subtype.ext
    change π (r 0) = (y:qOrbit G)
    rw [r.source]
    exact he
  have val1 : val 1 = y := by
    apply Subtype.ext
    change π (r 1) = (y:qOrbit G)
    rw [r.target]
    exact e1
  let q : Path y y :=
    { toFun := val, continuous_toFun := valc,
      source' := val0, target' := val1 }
  refine ⟨q, ?_⟩
  -- compare after projection. The old path is the projection of its lift;
  -- on the sphere that lift and `r` have the same endpoints.
  let L : Path e e' :=
    { toContinuousMap := l, source' := l0, target' := rfl }
  have hLR : Path.Homotopic L r := qSphere_any_paths e e' L r
  have hm : Path.Homotopic (L.map cov.continuous)
       (r.map cov.continuous) :=
    Path.Homotopic.map hLR ⟨π, cov.continuous⟩
  -- both projected paths have endpoints `π e`, `π e'`; cast them to the
  -- recorded basepoint before comparing with `p`.
  have hm' : Path.Homotopic
       ((L.map cov.continuous).cast he.symm e1.symm)
       ((r.map cov.continuous).cast he.symm e1.symm) :=
    hm.pathCast _ _
  have left : (L.map cov.continuous).cast he.symm e1.symm = p := by
    apply Path.ext
    exact cov.liftPath_lifts p e e0
  have right : q.map continuous_subtype_val =
        (r.map cov.continuous).cast he.symm e1.symm := by
    apply Path.ext
    funext t
    rfl
  rw [right, ← left]
  exact hm'.symm

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
/-- The null-loop half of deleting a point in a spherical quotient reduces
literally to null loops upstairs after deleting its finite fibre.  Kept
separate from the Euclidean finite-complement argument. -/
lemma qOrbit_delete_point_inj_of_upstairs
    (G : Type*) [Group G] [MulAction G qSphere]
    [ContinuousConstSMul G qSphere] [Finite G]
    [IsCancelSMul G qSphere]
    (up : ∀ (F : Set qSphere), F.Finite → F.Nonempty →
       ∀ (z : (Fᶜ : Set qSphere)) (a : Path z z),
          Path.Homotopic a (Path.refl z))
    (b : qOrbit G) (y : (({b} : Set (qOrbit G))ᶜ : Set (qOrbit G)))
    (a : Path y y) :
    Path.Homotopic (a.map continuous_subtype_val) (Path.refl (y:qOrbit G)) →
    Path.Homotopic a (Path.refl y) := by
  classical
  intro ha
  let π : qSphere → qOrbit G := Quotient.mk (MulAction.orbitRel G qSphere)
  let cov : IsCoveringMap (π) := qOrbitIsCovering G
  let p : Path (y:qOrbit G) (y:qOrbit G) := a.map continuous_subtype_val
  obtain ⟨e, he⟩ := Quotient.exists_rep (y:qOrbit G)
  change π e = (y:qOrbit G) at he
  have e0 : p 0 = π e := p.source.trans he.symm
  let l : C(unitInterval, qSphere) := cov.liftPath p e e0
  have l0 : l 0 = e := cov.liftPath_zero _ _ _
  -- the homotopy to the constant path forces this lift to close.
  have lp_end : l 1 = e := by
    rcases ha with ⟨HH⟩
    have HH' : p.Homotopy (Path.refl (y:qOrbit G)) := by
      exact HH
    have hrel : ContinuousMap.HomotopicRel
        (p : C(unitInterval, qOrbit G))
        (Path.refl (y:qOrbit G) : C(unitInterval, qOrbit G)) {0,1} :=
      ⟨HH'⟩
    have eqends := cov.liftPath_apply_one_eq_of_homotopicRel
       hrel e e0 ((Path.refl (y:qOrbit G)).source.trans he.symm)
    -- the lift of the constant path is constant
    have k := cov.liftPath_const (e := e) he.symm
    -- k : liftPath (const ...) = const
    -- normalize its value at one
    change l 1 = e
    exact eqends.trans (by
      -- `liftPath_const` uses a continuous constant map
      have kv := congrArg (fun (T : C(unitInterval, qSphere)) => T 1) k
      change (cov.liftPath (ContinuousMap.const unitInterval (y:qOrbit G)) e _) 1 = e
      exact kv)
  obtain ⟨c, hc⟩ := Quotient.exists_rep b
  change π c = b at hc
  let F : Set qSphere := {z | π z = π c}
  have Ff : F.Finite := by
    change ({z : qSphere | (Quotient.mk (MulAction.orbitRel G qSphere)) z =
      (Quotient.mk (MulAction.orbitRel G qSphere)) c}).Finite
    exact orbit_fiber_finite G c
  have Fn : F.Nonempty := ⟨c, rfl⟩
  have lemiss : ∀ t : unitInterval, l t ∈ Fᶜ := by
    intro t bad
    have hb' : π (l t) = b := bad.trans hc
    have liftv : π (l t) = p t := congr_fun (cov.liftPath_lifts p e e0) t
    have av : (a t : qOrbit G) ≠ b := by
      have na := (a t).property
      intro eq; exact na (by simpa using eq)
    exact av (liftv.symm.trans hb')
  let z : (Fᶜ : Set qSphere) := ⟨e, (by
    rw [← l0]
    exact lemiss 0)⟩
  let val : unitInterval → (Fᶜ : Set qSphere) := fun t => ⟨l t, lemiss t⟩
  have valc : Continuous val := by
    apply continuous_induced_rng.2
    exact l.continuous
  have val0 : val 0 = z := by apply Subtype.ext; exact l0
  have val1 : val 1 = z := by apply Subtype.ext; exact lp_end
  let L : Path z z :=
    { toFun := val, continuous_toFun := valc,
      source' := val0, target' := val1 }
  have nullL : Path.Homotopic L (Path.refl z) := up F Ff Fn z L
  -- project this null homotopy to the deleted quotient
  let m : (Fᶜ : Set qSphere) → (({b}:Set (qOrbit G))ᶜ : Set (qOrbit G)) :=
    fun v => ⟨π (v:qSphere), (by
      change π (v:qSphere) ∉ ({b}:Set (qOrbit G))
      have nv : (v:qSphere) ∉ F := v.property
      have ne : π (v:qSphere) ≠ b := by
        intro h
        apply nv
        exact h.trans hc.symm
      simpa using ne)⟩
  have mc : Continuous m := by
    apply continuous_induced_rng.2
    exact cov.continuous.comp continuous_subtype_val
  have hm := Path.Homotopic.map nullL (⟨m, mc⟩ : C((Fᶜ : Set qSphere), (({b}:Set (qOrbit G))ᶜ : Set (qOrbit G))))
  -- both sides of this path homotopy are the old lift projected, and its
  -- constant path; cast endpoints from `π e` with `he` below.
  have mz : m z = y := by
    apply Subtype.ext
    exact he
  have hm' : Path.Homotopic
       ((L.map mc).cast mz.symm mz.symm)
       (((Path.refl z).map mc).cast mz.symm mz.symm) :=
    hm.pathCast _ _
  have left : (L.map mc).cast mz.symm mz.symm = a := by
    apply Path.ext
    funext t
    apply Subtype.ext
    exact congr_fun (cov.liftPath_lifts p e e0) t
  have right : ((Path.refl z).map mc).cast mz.symm mz.symm =
        Path.refl y := by
    apply Path.ext
    funext t
    apply Subtype.ext
    exact he
  rw [← left, ← right]
  exact hm'

end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/OrbitDeleteBasics.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/FiniteDeleteReduction.lean
section
open scoped Quaternion RealInnerProductSpace Topology
open Topology Set Metric unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport
/-- Stereographic reduction of the finite puncture problem on the quaternion
sphere. The remaining assertion `U` is purely in a real three-dimensional
vector space. -/
lemma qSphere_delete_finite_of_vector
 (U : ∀ (c : qSphere) (T : Set ((ℝ ∙ (c : Quaternion ℝ))ᗮ)),
        T.Finite → ∀ (v : (Tᶜ : Set ((ℝ ∙ (c : Quaternion ℝ))ᗮ)))
          (p : Path v v), Path.Homotopic p (Path.refl v)) :
 ∀ (F : Set qSphere), F.Finite → F.Nonempty →
       ∀ (z : (Fᶜ : Set qSphere)) (a : Path z z),
          Path.Homotopic a (Path.refl z) := by
 classical
 intro F hf hn z a
 obtain ⟨c,hc⟩ := hn
 have cn : ‖(c:Quaternion ℝ)‖ = 1 := by
   have h := c.property
   change dist (c:Quaternion ℝ) 0 = 1 at h
   simpa [dist_zero_right] using h
 let O := stereographic cn
 let W := ((ℝ ∙ (c : Quaternion ℝ))ᗮ)
 have src : O.source = ({c}:Set qSphere)ᶜ := by
   simpa [O] using (stereographic_source cn)
 have tgt : O.target = (Set.univ : Set W) := rfl
 let T : Set W := O '' (F ∩ O.source)
 have Tf : T.Finite := (hf.inter_of_left _).image _
 have ins (v : (Fᶜ : Set qSphere)) : (v:qSphere) ∈ O.source := by
   rw [src]
   have ne : (v:qSphere) ≠ c := by
     intro h; exact v.property (h ▸ hc)
   simpa using ne
 have invt (w : W) : w ∈ O.target := by rw [tgt]; trivial
 let φ : (Fᶜ : Set qSphere) → (Tᶜ : Set W) := fun v =>
   ⟨O (v:qSphere), (by
     intro h
     rcases h with ⟨u, hu, eq⟩
     have uv : u = (v:qSphere) := O.injOn hu.2 (ins v) eq
     exact v.property (uv ▸ hu.1))⟩
 have φc : Continuous φ := by
   apply continuous_induced_rng.2
   exact O.continuousOn.comp_continuous continuous_subtype_val ins
 -- the inverse is defined on the whole complement of the finite image;
 -- membership follows by applying the partial equivalence.
 let ψ : (Tᶜ : Set W) → (Fᶜ : Set qSphere) := fun w =>
   ⟨O.symm (w:W), (by
      intro bad
      have isrc : O.symm (w:W) ∈ O.source := O.symm.map_source (invt w)
      have eqw : O (O.symm (w:W)) = (w:W) := O.right_inv (invt w)
      exact w.property (⟨O.symm (w:W), ⟨bad, isrc⟩, eqw⟩ : (w:W) ∈ T))⟩
 have ψc : Continuous ψ := by
   apply continuous_induced_rng.2
   exact O.continuousOn_symm.comp_continuous continuous_subtype_val (fun w : (Tᶜ : Set W) => invt (w:W))
 have left (v : (Fᶜ : Set qSphere)) : ψ (φ v) = v := by
   apply Subtype.ext
   exact O.left_inv (ins v)
 let v : (Tᶜ : Set W) := φ z
 let r : Path v v := a.map φc
 have hr : Path.Homotopic r (Path.refl v) := U c T Tf v r
 have hm := Path.Homotopic.map hr (⟨ψ, ψc⟩ : C((Tᶜ : Set W), (Fᶜ : Set qSphere)))
 have hm' : Path.Homotopic
     ((r.map ψc).cast (left z).symm (left z).symm)
     (((Path.refl v).map ψc).cast (left z).symm (left z).symm) :=
   hm.pathCast _ _
 have lft : (r.map ψc).cast (left z).symm (left z).symm = a := by
   apply Path.ext
   funext t
   exact left (a t)
 have rgt : ((Path.refl v).map ψc).cast (left z).symm (left z).symm
       = Path.refl z := by
   apply Path.ext
   funext t
   change ψ (φ z) = z
   exact left z
 rw [← lft, ← rgt]
 exact hm'
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/FiniteDeleteReduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/VectorDeleteStar.lean
section
open scoped Topology RealInnerProductSpace
open Topology Set Metric unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport
lemma vector_delete_star
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 (T : Set V) (v : (Tᶜ : Set V)) (p : Path v v)
 (avoid : ∀ s t : unitInterval,
   (1 - (s:ℝ)) • ((p t : (Tᶜ : Set V)) : V) +
        (s:ℝ) • (v:V) ∉ T) :
 Path.Homotopic p (Path.refl v) := by
 let h : unitInterval × unitInterval → (Tᶜ : Set V) := fun z =>
   ⟨(1 - (z.1:ℝ)) • ((p z.2 : (Tᶜ : Set V)) : V) +
        (z.1:ℝ) • (v:V), by
      exact avoid z.1 z.2⟩
 have hc : Continuous h := by
   apply continuous_induced_rng.2
   dsimp [h]
   fun_prop
 refine ⟨{
   toFun := h, continuous_toFun := hc,
   map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }⟩
 · intro t
   apply Subtype.ext
   simp [h]
 · intro t
   apply Subtype.ext
   simp [h]
 · intro s t ht
   apply Subtype.ext
   have pv : p t = v := by
     rcases ht with z | z
     · change t = (0:unitInterval) at z
       subst t
       exact p.source
     · have z' : t = (1:unitInterval) := by simpa using z
       subst t
       exact p.target
   have ev : ((p t : (Tᶜ : Set V)) : V) = (v:V) := congrArg Subtype.val pv
   change (1 - (s:ℝ)) • ((p t : (Tᶜ : Set V)) : V)
        + (s:ℝ) • (v:V) = ((p t : (Tᶜ : Set V)) : V)
   rw [ev, ← add_smul]
   have : (1 - (s:ℝ)) + (s:ℝ) = 1 := by ring
   rw [this, one_smul]
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/VectorDeleteStar.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/VectorRayReduction.lean
section
open scoped Topology RealInnerProductSpace
open Topology Set Metric unitInterval Filter
noncomputable section
namespace NonlinearThreeManifoldSupport

/-- A based radial contraction only sees the rays which start at the base
and go through a deleted point.  Writing this criterion without divisions is
handy for subsequent small perturbations of a path. -/
lemma vector_segment_avoids_of_no_rays
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 (T : Set V) (v : (Tᶜ : Set V)) (q : Path v v)
 (rays : ∀ t : unitInterval, ∀ a ∈ T,
   ¬ ∃ r : ℝ, 1 ≤ r ∧
       (((q t : (Tᶜ : Set V)) : V) - (v:V)) = r • (a - (v:V))) :
 ∀ s t : unitInterval,
   (1 - (s:ℝ)) • ((q t : (Tᶜ : Set V)) : V) + (s:ℝ) • (v:V) ∉ T := by
  intro s t ha
  classical
  have vnot : (v:V) ∉ T := v.property
  by_cases hs : (s:ℝ) = 1
  · have eqv : (1 - (s:ℝ)) • ((q t : (Tᶜ : Set V)) : V)
          + (s:ℝ) • (v:V) = (v:V) := by simp [hs]
    exact vnot (eqv ▸ ha)
  · let u : ℝ := 1 - (s:ℝ)
    have u0 : 0 < u := sub_pos.mpr (lt_of_le_of_ne s.property.2 hs)
    have une : u ≠ 0 := ne_of_gt u0
    -- If the segment contains `a`, it expresses `q-v` on the bad ray,
    -- with coefficient `(1-s)⁻¹`.
    apply (rays t _ ha)
    refine ⟨u⁻¹, ?_, ?_⟩
    · have ule : u ≤ 1 := by
        dsimp [u]
        linarith [s.property.1]
      change (1:ℝ) ≤ u⁻¹
      rw [inv_eq_one_div]
      exact (le_div_iff₀ u0).2 (by simpa using ule)
    · have seg : u • ((q t : (Tᶜ : Set V)) : V)
             + (s:ℝ) • (v:V) ∈ T := by
          simpa [u] using ha
      -- name the alleged point of T in the formula; it is the very
      -- expression on the segment
      let a : V := u • ((q t : (Tᶜ : Set V)) : V) + (s:ℝ) • (v:V)
      have ae : a = u • ((q t : (Tᶜ : Set V)) : V) + (s:ℝ) • (v:V) := rfl
      -- after replacing `a`, this is a module identity and `u ≠ 0`.
      change ((q t : (Tᶜ : Set V)) : V) - (v:V) =
          u⁻¹ •
            ((u • ((q t : (Tᶜ : Set V)) : V)
                 + (s:ℝ) • (v:V)) - (v:V))
      have us : u + (s:ℝ) = 1 := by dsimp [u]; ring
      -- `module` can distribute the two scalar multiplications once the
      -- scalar inverse is simplified.
      have ui : u⁻¹ * u = (1:ℝ) := inv_mul_cancel₀ une
      calc
        ((q t : (Tᶜ : Set V)) : V) - (v:V)
            = ((q t : (Tᶜ : Set V)) : V) + (-1:ℝ) • (v:V) := by module
        _ = (u⁻¹ * u) • ((q t : (Tᶜ : Set V)) : V)
              + (u⁻¹ * ((s:ℝ) - 1)) • (v:V) := by
                rw [ui]
                have invs : u⁻¹ * ((s:ℝ) - 1) = (-1:ℝ) := by
                  have : (s:ℝ) - 1 = -u := by dsimp [u]; ring
                  rw [this]
                  calc u⁻¹ * -u = -(u⁻¹ * u) := by ring
                       _ = (-1:ℝ) := by rw [ui]
                rw [invs]
                simp
        _ = u⁻¹ •
              ((u • ((q t : (Tᶜ : Set V)) : V)
                  + (s:ℝ) • (v:V)) - (v:V)) := by module

/-- Algebraic version of the last reduction.  It is enough to replace a
loop by a homotopic representative which misses all the finitely many rays
past the punctures.  No comparison between representatives for different
loops is involved. -/
lemma vector_delete_of_ray_representative
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 (T : Set V) (v : (Tᶜ : Set V))
 (p : Path v v)
 (H : ∃ q : Path v v, Path.Homotopic p q ∧
     (∀ t : unitInterval, ∀ a ∈ T,
       ¬ ∃ r : ℝ, 1 ≤ r ∧
        (((q t : (Tᶜ : Set V)) : V) - (v:V)) = r • (a - (v:V)))) :
 Path.Homotopic p (Path.refl v) := by
  rcases H with ⟨q,hq,hr⟩
  exact hq.trans (vector_delete_star T v q
    (vector_segment_avoids_of_no_rays T v q hr))

/-- Pointwise interpolation is a useful way of changing representatives.
The premise is only avoidance of the deleted set on that interpolation;
in particular it can be discharged by an a-priori uniform closeness bound.
Keeping it in this small path form avoids quotient bookkeeping. -/
lemma vector_path_homotopy_of_interpolation
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 (T : Set V) (v : (Tᶜ : Set V)) (p : Path v v)
 (z : unitInterval → V) (zc : Continuous z)
 (z0 : z 0 = (v:V)) (z1 : z 1 = (v:V))
 (safe : ∀ s t : unitInterval,
    (1 - (s:ℝ)) • ((p t : (Tᶜ : Set V)) : V) +
      (s:ℝ) • z t ∉ T) :
 ∃ q : Path v v, Path.Homotopic p q ∧
    (∀ t : unitInterval, ((q t : (Tᶜ : Set V)) : V) = z t) := by
  let val : unitInterval → (Tᶜ : Set V) := fun t =>
    ⟨z t, by simpa using (safe (1:unitInterval) t)⟩
  have valc : Continuous val := by
    apply continuous_induced_rng.2
    exact zc
  have e0 : val 0 = v := by
    apply Subtype.ext
    exact z0
  have e1 : val 1 = v := by
    apply Subtype.ext
    exact z1
  let q : Path v v :=
    { toFun := val, continuous_toFun := valc,
      source' := e0, target' := e1 }
  let h : unitInterval × unitInterval → (Tᶜ : Set V) := fun st =>
    ⟨(1 - (st.1:ℝ)) • ((p st.2 : (Tᶜ : Set V)) : V) +
      (st.1:ℝ) • z st.2, safe st.1 st.2⟩
  have hc : Continuous h := by
    apply continuous_induced_rng.2
    dsimp [h]
    fun_prop
  have hpq : Path.Homotopic p q := by
    refine ⟨{
      toFun := h, continuous_toFun := hc,
      map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }⟩
    · intro t
      apply Subtype.ext
      simp [h]
    · intro t
      apply Subtype.ext
      simp [h, q, val]
    · intro s t ht
      apply Subtype.ext
      have eqv : ((p t : (Tᶜ : Set V)) : V) = z t := by
        rcases ht with e | e
        · change t = (0:unitInterval) at e
          subst t
          have ep := congrArg Subtype.val p.source
          exact ep.trans z0.symm
        · have e' : t = (1:unitInterval) := by simpa using e
          subst t
          have ep := congrArg Subtype.val p.target
          exact ep.trans z1.symm
      change (1 - (s:ℝ)) • ((p t : (Tᶜ : Set V)) : V)
          + (s:ℝ) • z t = ((p t : (Tᶜ : Set V)) : V)
      rw [← eqv, ← add_smul]
      have : (1 - (s:ℝ)) + (s:ℝ) = 1 := by ring
      rw [this, one_smul]
  refine ⟨q, hpq, ?_⟩
  intro t
  rfl

end NonlinearThreeManifoldSupport

namespace NonlinearThreeManifoldSupport
open scoped Topology
open Set Metric unitInterval Filter
/-- A path in the complement of a finite set has a *uniform* positive
clearance from that set.  Keeping the statement in terms of norms is
particularly convenient for polynomial approximations. -/
lemma finite_path_clearance
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 (T : Set V) (hf : T.Finite) (v : (Tᶜ : Set V)) (p : Path v v) :
 ∃ ε : ℝ, 0 < ε ∧
   ∀ (t : unitInterval) (a : V), a ∈ T →
     ε ≤ ‖ ((p t : (Tᶜ : Set V)) : V) - a‖ := by
  classical
  let A : Finset V := hf.toFinset
  by_cases AE : A.Nonempty
  · -- minimize each of the finitely many continuous distance functions on I
    have each (a : V) (ha : a ∈ T) :
        ∃ x : unitInterval,
          ∀ t : unitInterval,
            ‖ ((p x : (Tᶜ : Set V)) : V) - a‖ ≤
            ‖ ((p t : (Tᶜ : Set V)) : V) - a‖ := by
      have cc : Continuous (fun t : unitInterval =>
          ‖ ((p t : (Tᶜ : Set V)) : V) - a‖) := by fun_prop
      obtain ⟨x,hx,hmin⟩ :=
        (isCompact_univ : IsCompact (Set.univ : Set unitInterval)).exists_isMinOn
          (⟨(0:unitInterval), by trivial⟩) cc.continuousOn
      exact ⟨x, fun t => hmin (by trivial)⟩
    choose x hx using (fun a : V => fun ha : a ∈ T => each a ha)
    let m : V → ℝ := fun a =>
       if ha : a ∈ T then
         ‖ ((p (x a ha) : (Tᶜ : Set V)) : V) - a‖
       else 1
    have mpos (a : V) (ha : a ∈ T) : 0 < m a := by
      simp only [m, dif_pos ha]
      apply norm_pos_iff.mpr
      intro e
      have eq : ((p (x a ha) : (Tᶜ : Set V)) : V) = a := sub_eq_zero.mp e
      apply (p (x a ha)).property
      rw [eq]
      exact ha
    obtain ⟨a,haA,least⟩ := Finset.exists_min_image A m AE
    have ha : a ∈ T := by simpa [A] using haA
    refine ⟨m a, mpos a ha, ?_⟩
    intro t b hb
    have hbA : b ∈ A := by simpa [A] using hb
    calc
      m a ≤ m b := least b hbA
      _ ≤ ‖ ((p t : (Tᶜ : Set V)) : V) - b‖ := by
        simp only [m, dif_pos hb]
        exact hx b hb t
  · have empty : T = (∅ : Set V) := by
      have e : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp AE
      exact Set.Finite.toFinset_eq_empty.mp e
    refine ⟨1, by norm_num, ?_⟩
    intro t a ha
    have : False := by simpa [empty] using ha
    contradiction

/-- Uniform closeness below the clearance radius guarantees that the
pointwise interpolation remains in the deleted set. The strict version is
more ergonomic with `bernsteinApproximation_uniform`. -/
lemma interpolation_safe_of_close
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 (T : Set V) (v : (Tᶜ : Set V)) (p : Path v v)
 (ε : ℝ)
 (clear : ∀ (t : unitInterval) (a : V), a ∈ T →
      ε ≤ ‖ ((p t : (Tᶜ : Set V)) : V) - a‖)
 (z : unitInterval → V)
 (close : ∀ t : unitInterval,
      ‖z t - ((p t : (Tᶜ : Set V)) : V)‖ < ε) :
 ∀ s t : unitInterval,
    (1 - (s:ℝ)) • ((p t : (Tᶜ : Set V)) : V) +
      (s:ℝ) • z t ∉ T := by
  intro s t bad
  have low := clear t _ bad
  -- if the convex segment hit a puncture it would be strictly closer to the
  -- original point than `ε`.
  have eqd :
      ((p t : (Tᶜ : Set V)) : V) -
        ((1 - (s:ℝ)) • ((p t : (Tᶜ : Set V)) : V) + (s:ℝ) • z t)
        = (s:ℝ) • (((p t : (Tᶜ : Set V)) : V) - z t) := by module
  have upper : ‖((p t : (Tᶜ : Set V)) : V) - z t‖ < ε := by
    simpa [norm_sub_rev] using close t
  rw [eqd, norm_smul, Real.norm_eq_abs, abs_of_nonneg s.property.1] at low
  have sle : (s:ℝ) ≤ 1 := s.property.2
  have sn : 0 ≤ (s:ℝ) := s.property.1
  have nnon : 0 ≤ ‖((p t : (Tᶜ : Set V)) : V) - z t‖ := norm_nonneg _
  nlinarith

/-- Polynomial regularisation of a loop in a finite deletion. The resulting
vector path still has the correct endpoints and is joined to the old loop
inside the deletion.  All that remains for a radial proof is to perturb this
*polynomial* path away from the finitely many based rays. -/
lemma vector_delete_bernstein_representative
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 (T : Set V) (hf : T.Finite) (v : (Tᶜ : Set V)) (p : Path v v) :
 ∃ (n : ℕ), n ≠ 0 ∧
   let f : C(unitInterval,V) :=
     ⟨(fun t : unitInterval => ((p t : (Tᶜ : Set V)) : V)), by fun_prop⟩
   let z : unitInterval → V := fun t => bernsteinApproximation n f t
   z 0 = (v:V) ∧ z 1 = (v:V) ∧
     ∃ q : Path v v, Path.Homotopic p q ∧
       (∀ t : unitInterval, ((q t : (Tᶜ : Set V)) : V) = z t) := by
  classical
  obtain ⟨ε,epos,clear⟩ := finite_path_clearance T hf v p
  let f : C(unitInterval,V) :=
     ⟨(fun t : unitInterval => ((p t : (Tᶜ : Set V)) : V)), by fun_prop⟩
  have lim := bernsteinApproximation_uniform f
  obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.1 lim) ε epos
  let n : ℕ := max N 1
  have hnN : N ≤ n := le_max_left _ _
  have hn : n ≠ 0 := by have h : 1 ≤ n := le_max_right _ _; omega
  have close0 : dist (bernsteinApproximation n f) f < ε := hN n hnN
  let z : unitInterval → V := fun t => bernsteinApproximation n f t
  have close : ∀ t : unitInterval,
       ‖z t - ((p t : (Tᶜ : Set V)) : V)‖ < ε := by
    intro t
    have le := ContinuousMap.dist_apply_le_dist (f := bernsteinApproximation n f) (g := f) t
    have : dist (bernsteinApproximation n f t) (f t) < ε :=
      lt_of_le_of_lt le close0
    simpa [z, f, dist_eq_norm] using this
  have safe := interpolation_safe_of_close T v p ε clear z close
  have zc : Continuous z := (bernsteinApproximation n f).continuous
  have z0 : z 0 = (v:V) := by
    dsimp [z]
    simpa [f] using (bernsteinApproximation.apply_zero n f)
  have z1 : z 1 = (v:V) := by
    dsimp [z]
    simpa [f] using (bernsteinApproximation.apply_one hn f)
  obtain ⟨q,hq,hval⟩ := vector_path_homotopy_of_interpolation T v p z zc z0 z1 safe
  refine ⟨n, hn, ?_⟩
  dsimp
  exact ⟨z0,z1, q, hq, by simpa [z, f] using hval⟩
end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/VectorRayReduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/FiniteRayBump.lean
section
open scoped Topology RealInnerProductSpace
open Topology Set Metric unitInterval
noncomputable section
namespace NonlinearThreeManifoldSupport

lemma clm_bernstein_shift_finite_roots
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 (n:ℕ) (f:C(I,V)) (L:V→L[ℝ] ℝ) (v:V) (t0:I)
 (hnz : L (bernsteinApproximation n f t0 - v) ≠ 0) :
 ∃ S : Set I, S.Finite ∧
   ∀ t:I, L (bernsteinApproximation n f t - v) = 0 → t ∈ S := by
 let P : Polynomial ℝ :=
   (∑ k : Fin (n+1), Polynomial.C (L (f (bernstein.z k))) * bernsteinPolynomial ℝ n k)
     - Polynomial.C (L v)
 have heval (t:I) : L (bernsteinApproximation n f t - v) = Polynomial.eval (t:ℝ) P := by
   dsimp [P]
   rw [map_sub, Polynomial.eval_sub]
   rw [clm_bernstein_eval, Polynomial.eval_C]
 have Pnz : P ≠ 0 := by
   intro hp
   have h := heval t0
   rw [hp] at h
   simp at h
   exact hnz (by simpa using h)
 let T : Set ℝ := {x | P.IsRoot x}
 have Tf : T.Finite := Polynomial.finite_setOf_isRoot Pnz
 let S : Set I := Subtype.val ⁻¹' T
 have Sf : S.Finite := Set.Finite.preimage (fun a _ b _ h => Subtype.ext h) Tf
 refine ⟨S,Sf,?_⟩
 intro t ht
 change (t:ℝ) ∈ T
 change Polynomial.IsRoot P (t:ℝ)
 exact (heval t).symm.trans ht


/-- A Bernstein arc in dimension at least three can be moved, keeping its
endpoints, off the finitely many rays based at a point.  The small movement
is a single parabolic bump in a generic direction. -/
lemma polynomial_finite_ray_bump
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 [FiniteDimensional ℝ V]
 (h3 : 2 < Module.finrank ℝ V)
 (T : Set V) (hT : T.Finite) (v : (Tᶜ : Set V))
 (n : ℕ) (f : C(I,V))
 (z0 : bernsteinApproximation n f 0 = (v:V))
 (z1 : bernsteinApproximation n f 1 = (v:V))
 (ε : ℝ) (εp : 0 < ε) :
 ∃ w : I → V, Continuous w ∧ w 0 = (v:V) ∧ w 1 = (v:V) ∧
   (∀ t:I, ‖w t - bernsteinApproximation n f t‖ < ε) ∧
   (∀ t:I, ∀ a ∈ T, ¬ ∃ r:ℝ, 1 ≤ r ∧
        w t - (v:V) = r • (a - (v:V))) := by
 classical
 let z : I → V := fun t => bernsteinApproximation n f t
 letI ft : Fintype {a // a ∈ T} := Set.Finite.fintype hT
 let d : {a // a ∈ T} → V := fun a => (a.1:V) - (v:V)
 let col : {a // a ∈ T} → Prop := fun a =>
   ∀ t:I, z t - (v:V) ∈ ℝ ∙ (d a)
 let tc : {a // a ∈ T} → I := fun a =>
   if h : col a then 0 else Classical.choose (not_forall.mp h)
 let e : {a // a ∈ T} → V := fun a => z (tc a) - (v:V)
 have enz (a : {a // a ∈ T}) (ha : ¬ col a) :
     e a ∉ ℝ ∙ d a := by
   dsimp [e, tc]
   split <;> rename_i h
   · contradiction
   · exact Classical.choose_spec (not_forall.mp ha)
 have ezero (a : {a // a ∈ T}) (ha : col a) : e a = 0 := by
   dsimp [e, tc]
   simp [ha, z, z0]
 let P : {a // a ∈ T} → Submodule ℝ V :=
   fun a => Submodule.span ℝ ({d a, e a} : Set V)
 have Pne (a : {a // a ∈ T}) : P a ≠ ⊤ := by
   have card : ({d a, e a} : Set V).toFinset.card < Module.finrank ℝ V := by
     have le : ({d a, e a} : Set V).toFinset.card ≤ 2 := by
       rw [Set.toFinset_insert, Set.toFinset_singleton]
       simpa using (Finset.card_insert_le (d a) ({e a} : Finset V))
     omega
   exact ne_of_lt (span_lt_top_of_card_lt_finrank card)
 obtain ⟨u, hu⟩ :=
   Submodule.exists_forall_notMem_of_forall_ne_top P Pne
 -- the chosen direction is independent from each of the indicated planes
 have ud (a : {a // a ∈ T}) : u ∉ ℝ ∙ d a := by
   intro h
   apply hu a
   exact (Submodule.span_mono (by
     intro x hx
     have : x = d a := (Set.mem_singleton_iff.mp hx)
     subst x
     simp)) h

 have dne (a : {a // a ∈ T}) : d a ≠ 0 := by
   dsimp [d]
   intro eq
   have av : (a.1:V) = (v:V) := sub_eq_zero.mp eq
   exact v.property (by rw [← av]; exact a.property)
 -- if the arc is not on the line of `d`, our generic choice also keeps the
 -- witness `e` outside the plane generated by `d` and `u`.
 have enplane (a : {a // a ∈ T}) (ha : ¬ col a) :
     e a ∉ Submodule.span ℝ ({d a, u} : Set V) := by
   intro he
   have repr := (Submodule.mem_span_insert).1 he
   rcases repr with ⟨A,z',hz',eq⟩
   have hzsingle : z' ∈ ℝ ∙ u := by simpa using hz'
   rcases (Submodule.mem_span_singleton).1 hzsingle with ⟨B,hB⟩
   have eq' : e a = A • d a + B • u := by simpa [hB] using eq
   have Bne : B ≠ 0 := by
     intro B0
     apply enz a ha
     rw [eq', B0]
     simp
     exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton.mpr ⟨1, by simp⟩)
   apply hu a
   -- solve the last displayed equality for `u`
   have form : u = (- B⁻¹ * A) • d a + B⁻¹ • e a := by
     -- pure module calculation
     calc
       u = (B⁻¹ * B) • u := by rw [inv_mul_cancel₀ Bne]; simp
       _ = B⁻¹ • (B • u) := by rw [mul_smul]
       _ = B⁻¹ • (e a - A • d a) := by rw [eq']; module
       _ = (- B⁻¹ * A) • d a + B⁻¹ • e a := by module
   rw [form]
   apply Submodule.add_mem
   · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
   · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
 -- produce annihilating coordinates.  In the non-collinear case `la` kills
 -- the `d,u` plane and reads `1` on `e`; `ka` kills `d` and reads `1` on `u`.
 -- Defaults in the collinear case never enter the finite-root calculation.
 let la : {a // a ∈ T} → (V →ₗ[ℝ] ℝ) := fun a =>
   if h : col a then 0 else
     Classical.choose
       (LinearMap.exists_extend_of_notMem
         (0 : (Submodule.span ℝ ({d a, u} : Set V)) →ₗ[ℝ] ℝ)
         (enplane a h) (1:ℝ))
 let ka : {a // a ∈ T} → (V →ₗ[ℝ] ℝ) := fun a =>
   Classical.choose
     (LinearMap.exists_extend_of_notMem
       (0 : (ℝ ∙ d a : Submodule ℝ V) →ₗ[ℝ] ℝ)
       (ud a) (1:ℝ))
 have la_plane (a : {a // a ∈ T}) (ha : ¬ col a) :
     ∀ x ∈ Submodule.span ℝ ({d a,u} : Set V), la a x = 0 := by
   intro x hx
   dsimp [la]
   split <;> rename_i h
   · contradiction
   · let Q := Submodule.span ℝ ({d a,u} : Set V)
     have ext := (LinearMap.exists_extend_of_notMem
           (0 : Q →ₗ[ℝ] ℝ) (enplane a ha) (1:ℝ))
     have prop := Classical.choose_spec ext
     -- on the old submodule it agrees with zero
     have := congrArg (fun g : Q →ₗ[ℝ] ℝ => g ⟨x,hx⟩) prop.1
     simpa [Q] using this
 have lae (a : {a // a ∈ T}) (ha : ¬ col a) : la a (e a) = 1 := by
   dsimp [la]
   split <;> rename_i h
   · contradiction
   · exact (Classical.choose_spec
       (LinearMap.exists_extend_of_notMem
         (0 : (Submodule.span ℝ ({d a, u} : Set V)) →ₗ[ℝ] ℝ)
         (enplane a ha) (1:ℝ))).2
 have lad (a : {a // a ∈ T}) (ha : ¬ col a) : la a (d a) = 0 :=
   la_plane a ha _ (Submodule.subset_span (by simp))
 have lau (a : {a // a ∈ T}) (ha : ¬ col a) : la a u = 0 :=
   la_plane a ha _ (Submodule.subset_span (by simp))
 have kad (a : {a // a ∈ T}) : ka a (d a) = 0 := by
   dsimp [ka]
   let Q : Submodule ℝ V := ℝ ∙ d a
   have prop := Classical.choose_spec
       (LinearMap.exists_extend_of_notMem
         (0 : Q →ₗ[ℝ] ℝ) (ud a) (1:ℝ))
   have memd : d a ∈ Q := Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
   have zz := congrArg (fun g : Q →ₗ[ℝ] ℝ => g ⟨d a,memd⟩) prop.1
   simpa [Q] using zz
 have kau (a : {a // a ∈ T}) : ka a u = 1 := by
   exact (Classical.choose_spec
       (LinearMap.exists_extend_of_notMem
         (0 : (ℝ ∙ d a : Submodule ℝ V) →ₗ[ℝ] ℝ)
         (ud a) (1:ℝ))).2
 let LA (a : {a // a ∈ T}) : V →L[ℝ] ℝ :=
   ⟨la a, (la a).continuous_of_finiteDimensional⟩
 -- finite lists of possible parameters for every non-collinear direction
 have roots_exist (a : {a // a ∈ T}) (ha : ¬ col a) :
     ∃ S : Set I, S.Finite ∧
       ∀ t:I, (la a) (z t - (v:V)) = 0 → t ∈ S := by
   have nonzero : LA a (bernsteinApproximation n f (tc a) - (v:V)) ≠ 0 := by
     change la a (e a) ≠ 0
     rw [lae a ha]
     norm_num
   simpa [z, LA] using
     (clm_bernstein_shift_finite_roots n f (LA a) (v:V) (tc a) nonzero)
 let Sa : {a // a ∈ T} → Set I := fun a =>
   if h : col a then ∅ else Classical.choose (roots_exist a h)
 have Saf (a : {a // a ∈ T}) : (Sa a).Finite := by
   dsimp [Sa]
   split <;> rename_i h
   · exact Set.finite_empty
   · exact (Classical.choose_spec (roots_exist a h)).1
 have Saroot (a : {a // a ∈ T}) (ha : ¬ col a) :
    ∀ t:I, la a (z t - (v:V)) = 0 → t ∈ Sa a := by
    dsimp [Sa]
    split <;> rename_i h
    · contradiction
    · exact (Classical.choose_spec (roots_exist a ha)).2
 let bump : I → ℝ := fun t => (t:ℝ) * (1 - (t:ℝ))
 have bc : Continuous bump := by dsimp [bump]; fun_prop
 have bnon (t:I) : 0 ≤ bump t :=
   mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2)
 have ble (t:I) : bump t ≤ 1 := by
   dsimp [bump]
   nlinarith [t.property.1, t.property.2,
     mul_self_nonneg ((t:ℝ) - (1/2:ℝ))]
 have bpos (t:I) (h0:t≠(0:I)) (h1:t≠(1:I)) : 0 < bump t := by
   dsimp [bump]
   have t0 : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (by
     intro e; apply h0; apply Subtype.ext; simpa using e.symm)
   have t1 : (t:ℝ) < 1 := lt_of_le_of_ne t.property.2 (by
     intro e; apply h1; apply Subtype.ext; simpa using e)
   positivity
 -- collect all forbidden bump coefficients (only finitely many roots above)
 let bad : Set ℝ := ⋃ a : {a // a ∈ T},
    if h : col a then ∅ else
      (fun t : I => - (ka a (z t - (v:V))) / bump t) '' (Sa a)
 have badf : bad.Finite := by
   dsimp [bad]
   apply Set.finite_iUnion
   intro a
   split <;> rename_i h
   · exact Set.finite_empty
   · exact (Saf a).image _
 let δ : ℝ := ε / (‖u‖ + 1)
 have δp : 0 < δ := by dsimp [δ]; positivity
 obtain ⟨C, hCI, hCb⟩ : ∃ C:ℝ, C ∈ Set.Ioo (0:ℝ) δ ∧ C ∉ bad := by
   have inf : (Set.Ioo (0:ℝ) δ \ bad).Infinite :=
      (Set.Ioo_infinite δp).diff badf
   rcases inf.nonempty with ⟨x,hx⟩
   exact ⟨x,hx.1,hx.2⟩
 have Cp : 0 < C := hCI.1
 have Cl : C < δ := hCI.2
 let w : I → V := fun t => z t + (C * bump t) • u
 have wc : Continuous w := by
   dsimp [w, z]
   fun_prop
 have w0 : w 0 = (v:V) := by simp [w, bump, z, z0]
 have w1 : w 1 = (v:V) := by simp [w, bump, z, z1]
 refine ⟨w, wc, w0, w1, ?_, ?_⟩
 · intro t
   change ‖(z t + (C * bump t) • u) - bernsteinApproximation n f t‖ < ε
   change ‖(z t + (C * bump t) • u) - z t‖ < ε
   rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
     abs_of_nonneg (mul_nonneg (le_of_lt Cp) (bnon t))]
   have bound : C * bump t * ‖u‖ ≤ C * 1 * ‖u‖ := by
     exact mul_le_mul_of_nonneg_right
       (mul_le_mul_of_nonneg_left (ble t) (le_of_lt Cp)) (norm_nonneg _)
   have small : C * (‖u‖ + 1) < ε := (lt_div_iff₀ (by positivity : 0 < ‖u‖ + (1:ℝ))).1 (by simpa [δ] using Cl)
   calc
     C * bump t * ‖u‖ ≤ C * 1 * ‖u‖ := bound
     _ < ε := by nlinarith
 · intro t a ha
   let ai : {a // a ∈ T} := ⟨a,ha⟩
   rintro ⟨r,hr,eqr⟩
   change w t - (v:V) = r • d ai at eqr
   by_cases ht0 : t = (0:I)
   · subst t
     have zer : (0:V) = r • d ai := by simpa [w0] using eqr
     have rz : r = 0 := by
       exact (smul_eq_zero.mp zer.symm).resolve_right (dne ai)
     linarith
   by_cases ht1 : t = (1:I)
   · subst t
     have zer : (0:V) = r • d ai := by simpa [w1] using eqr
     have rz : r = 0 := (smul_eq_zero.mp zer.symm).resolve_right (dne ai)
     linarith
   have bp := bpos t ht0 ht1
   by_cases hcol : col ai
   · -- on a collinear polynomial, any nonzero bump immediately leaves the line
     have zmem : z t - (v:V) ∈ ℝ ∙ d ai := hcol t
     have memcu : (C * bump t) • u ∈ ℝ ∙ d ai := by
       have memr : r • d ai ∈ ℝ ∙ d ai :=
         Submodule.smul_mem _ _ (Submodule.mem_span_singleton.mpr ⟨1, by simp⟩)
       have E : (C * bump t) • u = r • d ai - (z t - (v:V)) := by
         have := eqr
         dsimp [w] at this
         -- rearrange
         calc
           (C * bump t) • u = (z t + (C * bump t) • u - (v:V)) - (z t - (v:V)) := by module
           _ = r • d ai - (z t - (v:V)) := by rw [this]
       rw [E]
       exact Submodule.sub_mem _ memr zmem
     have cne : (C * bump t) ≠ 0 := mul_ne_zero (ne_of_gt Cp) (ne_of_gt bp)
     have umem : u ∈ ℝ ∙ d ai := by
       exact ( (ℝ ∙ d ai : Submodule ℝ V).smul_mem_iff cne).mp memcu
     exact ud ai umem
   · -- otherwise the first coordinate restricts `t` to its finite root set
     have eqL := congrArg (fun x : V => la ai x) eqr
     have root : la ai (z t - (v:V)) = 0 := by
       dsimp [w] at eqL
       rw [map_smul, lad ai hcol] at eqL
       simp at eqL
       -- also the bump is killed by `la`
       simpa [map_sub, map_add, map_smul, lau ai hcol] using eqL
     have ts : t ∈ Sa ai := Saroot ai hcol t root
     have eqK := congrArg (fun x : V => ka ai x) eqr
     have cform : C = - (ka ai (z t - (v:V))) / bump t := by
       dsimp [w] at eqK
       rw [map_smul, kad ai] at eqK
       simp at eqK
       -- `eqK`: ka z + C*b - ka v = 0
       have bn : bump t ≠ 0 := ne_of_gt bp
       apply (eq_div_iff bn).2
       rw [map_sub]
       rw [kau ai] at eqK
       nlinarith [eqK]
     apply hCb
     dsimp [bad]
     apply Set.mem_iUnion.2
     refine ⟨ai, ?_⟩
     rw [if_neg hcol]
     exact ⟨t, ts, cform.symm⟩

end NonlinearThreeManifoldSupport

end

end
-- END INLINED FILE: Mathlib/Support/nonlinear_three_manifold_group_f4a913ac99/FiniteRayBump.lean

-- BEGIN INLINED MAIN PRELUDE
open LeanEval.Topology
open Matrix
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem nonlinear_three_manifold_group :
    ∃ (M : Closed3Manifold) (x : M.carrier),
      ∀ f : FundamentalGroup M.carrier x →* GL (Fin 4) ℝ, ¬ Function.Injective f :=
/-ResultProofBegin-/by
  classical
  -- An algebraic obstruction which isolates the remaining topological step: it
  -- is enough to realise two different quaternion centres in one fundamental
  -- group.  All of the linear algebra is contained in the support lemma; the
  -- goal left below is exactly the absent connected-sum/van Kampen input.
  suffices h : ∃ (M : Closed3Manifold) (x : M.carrier)
        (i j z i' j' z' : FundamentalGroup M.carrier x),
        z * z = 1 ∧ i * i = z ∧ j * j = z ∧
        z * i = i * z ∧ z * j = j * z ∧ j * i = z * (i * j) ∧
        z' * z' = 1 ∧ i' * i' = z' ∧ j' * j' = z' ∧
        z' * i' = i' * z' ∧ z' * j' = j' * z' ∧
        j' * i' = z' * (i' * j') ∧
        z ≠ 1 ∧ z' ≠ 1 ∧ z ≠ z' by
    rcases h with ⟨M, x, i, j, z, i', j', z',
      hz2, hi2, hj2, hzi, hzj, hji,
      hz2', hi2', hj2', hzi', hzj', hji', hn1, hn2, hne⟩
    refine ⟨M, x, ?_⟩
    exact
      NonlinearThreeManifoldSupport.no_GL4_of_two_quaternion_centres
        i j z i' j' z'
        hz2 hi2 hj2 hzi hzj hji
        hz2' hi2' hj2' hzi' hzj' hji'
        hn1 hn2 hne
  -- From this point on we only need two based injections of the *standard*
  -- quaternion group.  Working with this concrete presentation is useful in a
  -- later covering-space/connected-sum construction; all the choices of
  -- generators have been discharged in `quaternion_packets_of_embeddings`.
  suffices emb : ∃ (M : Closed3Manifold) (x : M.carrier)
        (u v : QuaternionGroup 2 →* FundamentalGroup M.carrier x),
        Function.Injective u ∧ Function.Injective v ∧
          u (.a 2) ≠ v (.a 2) by
    rcases emb with ⟨M, x, u, v, hu, hv, huv⟩
    rcases NonlinearThreeManifoldSupport.quaternion_packets_of_embeddings u v hu hv huv with
      ⟨i, j, z, i', j', z', hq⟩
    exact ⟨M, x, i, j, z, i', j', z', hq⟩
  -- The remaining input is geometric: one may obtain these injections from the
  -- two factors in a connected sum of quaternionic space forms.  All relation
  -- checking in `QuaternionGroup 2` (including nontriviality of the chosen
  -- centre `.a 2`) is now below this cut.
  -- First elementary piece of the missing construction.  For *any* finite
  -- free quaternionic-sphere action the quotient already meets exactly the
  -- closed-three-manifold bundle in the question; there is no model-space
  -- cast or connectedness issue left at this stage.  Later one has to choose
  -- the Q8 action and analyse/glue its based covering.
  let orbitWitness (G : Type)
      [Group G] [MulAction G NonlinearThreeManifoldSupport.qSphere]
      [ContinuousConstSMul G NonlinearThreeManifoldSupport.qSphere]
      [Finite G] [IsCancelSMul G NonlinearThreeManifoldSupport.qSphere] :
      Closed3Manifold := by
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (NonlinearThreeManifoldSupport.qOrbit G) :=
      NonlinearThreeManifoldSupport.qOrbitCharted G
    letI : ConnectedSpace (NonlinearThreeManifoldSupport.qOrbit G) :=
      NonlinearThreeManifoldSupport.qOrbitConnected G
    letI : SecondCountableTopology (NonlinearThreeManifoldSupport.qOrbit G) :=
      ContinuousConstSMul.secondCountableTopology
    exact { carrier := NonlinearThreeManifoldSupport.qOrbit G }
  -- Multiplication by norm-one quaternions is a particularly useful source of
  -- actions to which `orbitWitness` applies.  This little hand-off is often
  -- fiddly: `MulAction`, `ContinuousConstSMul`, and the *right* cancellation
  -- part of `IsCancelSMul` all have to be the *same* smul instance.  Keeping the
  -- projections definitional avoids any choice of a topology on the group of
  -- deck transformations.
  let sphericalForm
      (ρ : QuaternionGroup 2 →* Quaternion ℝ)
      (hn : ∀ g, ‖ρ g‖ = 1)
      (hi : Function.Injective ρ) : Closed3Manifold := by
    letI act : MulAction (QuaternionGroup 2)
        NonlinearThreeManifoldSupport.qSphere :=
      NonlinearThreeManifoldSupport.unitSphereAction ρ hn
    letI cont : ContinuousConstSMul (QuaternionGroup 2)
        NonlinearThreeManifoldSupport.qSphere :=
      NonlinearThreeManifoldSupport.unitSphereAction_cont ρ hn
    letI free : IsCancelSMul (QuaternionGroup 2)
        NonlinearThreeManifoldSupport.qSphere :=
      NonlinearThreeManifoldSupport.unitSphereAction_cancel ρ hn hi
    exact orbitWitness (QuaternionGroup 2)
  -- Thus the missing topological input really starts *after* the space forms
  -- have been built: for example `sphericalForm ρ hn hi` is a closed connected
  -- three-manifold for every faithful norm-one quaternion realization.  To
  -- finish `emb` one still needs based injections of the two deck groups into
  -- the fundamental group of a connected sum.  There is at present no
  -- connected-sum/van Kampen theorem for `ChartedSpace` in `mathlib`.
  -- For the sum it is not necessary to compute a free product.  Pinch maps with
  -- sections on the punctured components suffice; in particular it is enough
  -- to build the following splitting data.  `hkill` is weaker than saying the
  -- whole second factor is contracted.
  suffices split : ∃ (M : Closed3Manifold) (x : M.carrier)
        (u v : QuaternionGroup 2 →* FundamentalGroup M.carrier x)
        (r s : FundamentalGroup M.carrier x →* QuaternionGroup 2),
        r.comp u = MonoidHom.id (QuaternionGroup 2) ∧
        s.comp v = MonoidHom.id (QuaternionGroup 2) ∧
        r (v (.a 2)) = 1 by
    rcases split with ⟨M,x,u,v,r,s,ru,sv,kill⟩
    obtain ⟨iu,iv,d⟩ :=
      NonlinearThreeManifoldSupport.q8_embeddings_of_splittings u v r s ru sv kill
    exact ⟨M,x,u,v,iu,iv,d⟩
  -- At least the block needed for each punctured component is now completely
  -- explicit (rather than conditional on a nonexistent quaternion
  -- realisation): eight coordinate calculations give the norm-one faithful
  -- Q8 action.  The remaining data `split` is precisely the construction of
  -- the two pinch maps for the connected sum and their based covering loops.
  let B : Closed3Manifold :=
    sphericalForm
      NonlinearThreeManifoldSupport.ExplicitQ8.q8rho
      NonlinearThreeManifoldSupport.ExplicitQ8.q8rho_norm
      NonlinearThreeManifoldSupport.ExplicitQ8.q8rho_injective
  -- Work with punctured patches; the inclusions of *closed* summands as
  -- continuous sections do not exist.  All that the algebra needs are
  -- sections on their fundamental groups.
  letI blockAct : MulAction (QuaternionGroup 2)
      NonlinearThreeManifoldSupport.qSphere :=
    NonlinearThreeManifoldSupport.unitSphereAction
      NonlinearThreeManifoldSupport.ExplicitQ8.q8rho
      NonlinearThreeManifoldSupport.ExplicitQ8.q8rho_norm
  letI blockCont : ContinuousConstSMul (QuaternionGroup 2)
      NonlinearThreeManifoldSupport.qSphere :=
    NonlinearThreeManifoldSupport.unitSphereAction_cont
      NonlinearThreeManifoldSupport.ExplicitQ8.q8rho
      NonlinearThreeManifoldSupport.ExplicitQ8.q8rho_norm
  letI blockFree : IsCancelSMul (QuaternionGroup 2)
      NonlinearThreeManifoldSupport.qSphere :=
    NonlinearThreeManifoldSupport.unitSphereAction_cancel
      NonlinearThreeManifoldSupport.ExplicitQ8.q8rho
      NonlinearThreeManifoldSupport.ExplicitQ8.q8rho_norm
      NonlinearThreeManifoldSupport.ExplicitQ8.q8rho_injective
  let b : B.carrier :=
    ((Quotient.mk (MulAction.orbitRel (QuaternionGroup 2)
      NonlinearThreeManifoldSupport.qSphere))
      NonlinearThreeManifoldSupport.qNorth)
  let A : NonlinearThreeManifoldSupport.ChartBall
        (E:= EuclideanSpace ℝ (Fin 3)) b :=
    Classical.choice
      (NonlinearThreeManifoldSupport.existsChartBall
        (E:= EuclideanSpace ℝ (Fin 3)) b)
  let P := (({b}:Set B.carrier)ᶜ : Set B.carrier)
  let Uend : TopologicalSpace.Opens B.carrier :=
    { carrier := ({b} : Set B.carrier)ᶜ,
      is_open' := isOpen_compl_singleton }
  let X : TopCat := TopCat.of P
  let V : TopologicalSpace.Opens X :=
    NonlinearThreeManifoldSupport.chartEnd
      (E:= EuclideanSpace ℝ (Fin 3)) b A
  let e : (V : Type) ≃ₜ (V : Type) :=
    NonlinearThreeManifoldSupport.chartEndFlip
      (E:= EuclideanSpace ℝ (Fin 3)) b A
  have he : ∀ z : (V : Type), e (e z) = z := by
    intro z
    exact NonlinearThreeManifoldSupport.chartEndFlip_invol
      (E:= EuclideanSpace ℝ (Fin 3)) b A z
  let D : TopCat.GlueData.{0} :=
    NonlinearThreeManifoldSupport.doubleGlueData X V e he
  let NW := (NonlinearThreeManifoldSupport.neckSpace
        (E:= EuclideanSpace ℝ (Fin 3)) b A)
  letI chP : ChartedSpace (EuclideanSpace ℝ (Fin 3)) P := by
    change ChartedSpace (EuclideanSpace ℝ (Fin 3))
       (({b}:Set B.carrier)ᶜ : Set B.carrier)
    exact TopologicalSpace.Opens.instChartedSpace Uend
  letI baseSC : SecondCountableTopology B.carrier :=
    Closed3Manifold.secondCountable (self := B)
  letI scP : SecondCountableTopology P := by
    change SecondCountableTopology (({b}:Set B.carrier)ᶜ : Set B.carrier)
    infer_instance
  letI coP : ConnectedSpace P := by
    change ConnectedSpace (({b}:Set B.carrier)ᶜ : Set B.carrier)
    exact NonlinearThreeManifoldSupport.punctured_connected
      (E := EuclideanSpace ℝ (Fin 3)) (Y := B.carrier) b A (by
        rw [← Module.finrank_eq_rank]
        norm_num [Module.finrank_fin_fun])
  letI chD : ∀ k : D.J, ChartedSpace
       (EuclideanSpace ℝ (Fin 3)) (D.U k) := by
    intro k
    change ChartedSpace (EuclideanSpace ℝ (Fin 3)) P
    exact chP
  letI cntD : Countable D.J := by
    change Countable Bool
    infer_instance
  letI nzD : Nonempty D.J := by
    change Nonempty Bool
    infer_instance
  letI coD : ∀ k : D.J, ConnectedSpace (D.U k) := by
    intro k
    change ConnectedSpace P
    exact coP
  letI scD : ∀ k : D.J, SecondCountableTopology (D.U k) := by
    intro k
    change SecondCountableTopology P
    exact scP
  have meetD : ∀ k l : D.J, Nonempty (D.V (k,l)) := by
    dsimp [D]
    exact NonlinearThreeManifoldSupport.doubleGlue_meet X V e he (by
      obtain ⟨z,hz⟩ := NonlinearThreeManifoldSupport.radialSet_nonempty
        (E:= EuclideanSpace ℝ (Fin 3)) A.R A.pos
      exact ⟨(NonlinearThreeManifoldSupport.chartEndHomeo
        (E:= EuclideanSpace ℝ (Fin 3)) b A).symm ⟨z,hz⟩⟩)
  letI tD : T2Space D.toGlueData.glued := by
    dsimp [D, X, V, e, P]
    exact NonlinearThreeManifoldSupport.doubleGlue_chartEnd_t2
      (E := EuclideanSpace ℝ (Fin 3)) (Y := B.carrier) A
  letI cmpD : CompactSpace D.toGlueData.glued := by
    dsimp [D, X, V, e, P]
    exact NonlinearThreeManifoldSupport.doubleGlue_chartEnd_compact
      (E := EuclideanSpace ℝ (Fin 3)) (Y := B.carrier) A
  letI chartW : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        D.toGlueData.glued :=
    NonlinearThreeManifoldSupport.gluedChartedSpace D
  letI connW : ConnectedSpace D.toGlueData.glued :=
    NonlinearThreeManifoldSupport.gluedConnectedSpace D meetD
  letI secW : SecondCountableTopology D.toGlueData.glued :=
    NonlinearThreeManifoldSupport.gluedSecondCountable D
  let M : Closed3Manifold := { carrier := D.toGlueData.glued }
  -- all maps below have sources the punctured pieces
  obtain ⟨y₀,y₁,x,k₀,k₁,t₀,t₁,r,s,T0,T1,hk₀,hk₁,hcross⟩ :=
    NonlinearThreeManifoldSupport.radial_patch_data
      (E:= EuclideanSpace ℝ (Fin 3)) (Y:=B.carrier) b A
  -- This is the residual lifting fact.  It involves the fundamental group
  -- of just a punctured spherical block.  In particular it no longer asks
  -- for a continuous map of a closed summand into the double.
  suffices punctured_lifts :
      ∃ (e₀ : QuaternionGroup 2 →* FundamentalGroup B.carrier b)
        (d₀ : FundamentalGroup B.carrier b →* QuaternionGroup 2)
        (L₀ : QuaternionGroup 2 →*
          FundamentalGroup (({b}:Set B.carrier)ᶜ : Set B.carrier) y₀)
        (L₁ : QuaternionGroup 2 →*
          FundamentalGroup (({b}:Set B.carrier)ᶜ : Set B.carrier) y₁),
        d₀.comp e₀ = MonoidHom.id (QuaternionGroup 2) ∧
        (NonlinearThreeManifoldSupport.BasedCMap.piOne t₀).comp L₀ = e₀ ∧
        (NonlinearThreeManifoldSupport.BasedCMap.piOne t₁).comp L₁ = e₀ by
    rcases punctured_lifts with ⟨e₀,d₀,L₀,L₁,hd,h0,h1⟩
    obtain ⟨u,v,R,S,hR,hS,hbad⟩ :=
      NonlinearThreeManifoldSupport.BasedCMap.split_of_patch_sections
        k₀ k₁ t₀ t₁ r s hk₀ hk₁ hcross e₀ L₀ L₁ h0 h1 d₀ hd
    -- carriers of the double agree definitionally with `neckSpace`
    have eqcar : M.carrier =
        NonlinearThreeManifoldSupport.neckSpace
          (E:= EuclideanSpace ℝ (Fin 3)) b A := rfl
    exact ⟨M, x, u, v, R, S, hR, hS, hbad⟩
  -- A small collar calculation packages all of the seam work in the last
  -- display above.  The outstanding point is only lifting Q8 paths through a
  -- *punctured block*: the squeezed map on that single open set is an
  -- isomorphism on the Q8 subgroup. No false space-section of a connected
  -- sum is hidden in this assertion.
  suffices one_punctured_sheet :
      ∃ (e₀ : QuaternionGroup 2 →* FundamentalGroup B.carrier b)
        (d₀ : FundamentalGroup B.carrier b →* QuaternionGroup 2),
        d₀.comp e₀ = MonoidHom.id (QuaternionGroup 2) ∧
        ∀ (y : (({b}:Set B.carrier)ᶜ : Set B.carrier))
          (hy : NonlinearThreeManifoldSupport.shrinkOnPuncture
             (E:= EuclideanSpace ℝ (Fin 3)) b A y = b),
          ∃ L : QuaternionGroup 2 →*
              FundamentalGroup (({b}:Set B.carrier)ᶜ : Set B.carrier) y,
            (NonlinearThreeManifoldSupport.BasedCMap.piOne
              ({ toContinuousMap :=
                    NonlinearThreeManifoldSupport.shrinkOnPuncture
                      (E:= EuclideanSpace ℝ (Fin 3)) b A,
                 map_pt := hy } :
                NonlinearThreeManifoldSupport.BasedCMap
                  (({b}:Set B.carrier)ᶜ : Set B.carrier) y B.carrier b)).comp L = e₀ by
    rcases one_punctured_sheet with ⟨e₀,d₀,hd,hl⟩
    -- `t₀` and `t₁` are literally these squeezed maps.  No endpoint
    -- conjugations are suppressed here: their `map_pt` fields are kept.
    have hy0 : NonlinearThreeManifoldSupport.shrinkOnPuncture
          (E:= EuclideanSpace ℝ (Fin 3)) b A y₀ = b := by
      rw [← T0]
      exact t₀.map_pt
    have hy1 : NonlinearThreeManifoldSupport.shrinkOnPuncture
          (E:= EuclideanSpace ℝ (Fin 3)) b A y₁ = b := by
      rw [← T1]
      exact t₁.map_pt
    obtain ⟨L₀,hL₀⟩ := hl y₀ hy0
    obtain ⟨L₁,hL₁⟩ := hl y₁ hy1
    refine ⟨e₀,d₀,L₀,L₁,hd,?_,?_⟩
    · have eq0 : t₀ =
          ({ toContinuousMap :=
               NonlinearThreeManifoldSupport.shrinkOnPuncture
                 (E:= EuclideanSpace ℝ (Fin 3)) b A,
             map_pt := hy0 } : NonlinearThreeManifoldSupport.BasedCMap
               (({b}:Set B.carrier)ᶜ : Set B.carrier) y₀ B.carrier b) := by
            cases t₀ with | mk f hf =>
              dsimp at T0
              cases T0
              rfl
      rw [eq0]
      exact hL₀
    · have eq1 : t₁ =
          ({ toContinuousMap :=
               NonlinearThreeManifoldSupport.shrinkOnPuncture
                 (E:= EuclideanSpace ℝ (Fin 3)) b A,
             map_pt := hy1 } : NonlinearThreeManifoldSupport.BasedCMap
               (({b}:Set B.carrier)ᶜ : Set B.carrier) y₁ B.carrier b) := by
            cases t₁ with | mk f hf =>
              dsimp at T1
              cases T1
              rfl
      rw [eq1]
      exact hL₁
  -- For the closed block itself the deck calculation is now honest.  The
  -- endpoint injectivity is proved upstairs, at the indicated sheet, by
  -- polynomially moving loops on the quaternion sphere; no simply-connected
  -- typeclass or presentation of π₁ is being assumed here.
  obtain ⟨e₀,d₀,hd⟩ :=
    NonlinearThreeManifoldSupport.explicitQ8_block_retract
  refine ⟨e₀, d₀, hd, ?_⟩
  -- What still survives is the ordinary deleted-point theorem in dimension
  -- three.  A genuine group section of the squeezed deleted chart is
  -- enough; after composing that section with the already constructed deck
  -- embedding no pointwise choices of loop representatives remain.
  intro y hy
  suffices hpunct : ∃ J : FundamentalGroup B.carrier b →*
          FundamentalGroup (({b}:Set B.carrier)ᶜ : Set B.carrier) y,
      (NonlinearThreeManifoldSupport.BasedCMap.piOne
        ({ toContinuousMap :=
              NonlinearThreeManifoldSupport.shrinkOnPuncture
                (E:= EuclideanSpace ℝ (Fin 3)) b A,
           map_pt := hy } : NonlinearThreeManifoldSupport.BasedCMap
             (({b}:Set B.carrier)ᶜ : Set B.carrier) y B.carrier b)).comp J =
        MonoidHom.id (FundamentalGroup B.carrier b) by
    rcases hpunct with ⟨J, hJ⟩
    refine ⟨J.comp e₀, ?_⟩
    calc
      (NonlinearThreeManifoldSupport.BasedCMap.piOne
        ({ toContinuousMap :=
              NonlinearThreeManifoldSupport.shrinkOnPuncture
                (E:= EuclideanSpace ℝ (Fin 3)) b A,
           map_pt := hy } : NonlinearThreeManifoldSupport.BasedCMap
             (({b}:Set B.carrier)ᶜ : Set B.carrier) y B.carrier b)).comp
          (J.comp e₀) =
          ((NonlinearThreeManifoldSupport.BasedCMap.piOne
            ({ toContinuousMap :=
                  NonlinearThreeManifoldSupport.shrinkOnPuncture
                    (E:= EuclideanSpace ℝ (Fin 3)) b A,
               map_pt := hy } : NonlinearThreeManifoldSupport.BasedCMap
                 (({b}:Set B.carrier)ᶜ : Set B.carrier) y B.carrier b)).comp J).comp e₀ := by
                   rfl
      _ = e₀ := by rw [hJ]; rfl
  -- Throw the harmless collar deformation away before doing any deletion.
  -- Its base point moves; at the quotient level the two whiskers cancel.
  -- `TrackIso` records this unbased naturality calculation in the
  -- fundamental groupoid.
  let g : C((({b}:Set B.carrier)ᶜ : Set B.carrier), B.carrier) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let inc : NonlinearThreeManifoldSupport.BasedCMap
      (({b}:Set B.carrier)ᶜ : Set B.carrier) y
      B.carrier (y:B.carrier) := { toContinuousMap := g, map_pt := rfl }
  suffices hinc : Function.Bijective
        (NonlinearThreeManifoldSupport.BasedCMap.piOne inc) by
    let S := NonlinearThreeManifoldSupport.shrinkMap
       (E:= EuclideanSpace ℝ (Fin 3)) b A
    let H := NonlinearThreeManifoldSupport.shrinkHomotopy
       (E:= EuclideanSpace ℝ (Fin 3)) b A
    have bij0 :=
      NonlinearThreeManifoldSupport.BasedCMap.piOne_bijective_comp_of_homotopy_eq
        g y S H (y:B.carrier) b rfl hy hinc
    have bij : Function.Bijective
        (NonlinearThreeManifoldSupport.BasedCMap.piOne
          ({ toContinuousMap :=
                NonlinearThreeManifoldSupport.shrinkOnPuncture
                  (E:= EuclideanSpace ℝ (Fin 3)) b A,
             map_pt := hy } : NonlinearThreeManifoldSupport.BasedCMap
                  (({b}:Set B.carrier)ᶜ : Set B.carrier) y B.carrier b)) := by
      exact bij0
    let eiso : FundamentalGroup (({b}:Set B.carrier)ᶜ : Set B.carrier) y ≃*
          FundamentalGroup B.carrier b :=
      MulEquiv.ofBijective
        (NonlinearThreeManifoldSupport.BasedCMap.piOne
          ({ toContinuousMap :=
                NonlinearThreeManifoldSupport.shrinkOnPuncture
                  (E:= EuclideanSpace ℝ (Fin 3)) b A,
             map_pt := hy } : NonlinearThreeManifoldSupport.BasedCMap
                  (({b}:Set B.carrier)ᶜ : Set B.carrier) y B.carrier b)) bij
    refine ⟨eiso.symm.toMonoidHom, ?_⟩
    ext a
    exact eiso.apply_symm_apply a
  -- The only input which remains is the local general-position statement
  -- for the *ordinary* inclusion of a deleted point.  Notice that the
  -- squeezed neck and its moving endpoint no longer occur in either clause.
  suffices avoid :
      ( (∀ p : Path (y:B.carrier) (y:B.carrier),
          ∃ q : Path y y,
            Path.Homotopic (q.map continuous_subtype_val) p) ∧
        (∀ a : Path y y,
          Path.Homotopic (a.map continuous_subtype_val)
            (Path.refl (y:B.carrier)) →
          Path.Homotopic a (Path.refl y))) by
    exact NonlinearThreeManifoldSupport.BasedCMap.piOne_bijective_of_lift_null
      inc (by simpa [inc, g] using avoid.1) (by simpa [inc, g] using avoid.2)
  -- Paths which already miss the point lift literally; no chart is involved.
  -- Separating this case is helpful because the relative perturbation theorem
  -- is only about parameters actually hitting the centre.
  suffices hard :
      ( (∀ p : Path (y:B.carrier) (y:B.carrier),
          ¬ (∀ t : unitInterval, (p t) ≠ b) →
          ∃ q : Path y y,
            Path.Homotopic (q.map continuous_subtype_val) p) ∧
        (∀ a : Path y y,
          Path.Homotopic (a.map continuous_subtype_val)
            (Path.refl (y:B.carrier)) →
          Path.Homotopic a (Path.refl y))) by
    refine ⟨?_, hard.2⟩
    intro p
    by_cases hp : ∀ t : unitInterval, (p t) ≠ b
    · let lift : unitInterval → (({b}:Set B.carrier)ᶜ : Set B.carrier) :=
        fun t => ⟨p t, (by simpa using hp t)⟩
      have liftc : Continuous lift := by
        apply continuous_induced_rng.2
        exact p.continuous
      have h0 : lift 0 = y := by
        apply Subtype.ext
        exact p.source
      have h1 : lift 1 = y := by
        apply Subtype.ext
        exact p.target
      let q : Path y y :=
        { toFun := lift, continuous_toFun := liftc,
          source' := h0, target' := h1 }
      refine ⟨q, ?_⟩
      have eqn : q.map continuous_subtype_val = p := by
        apply Path.ext
        funext t
        rfl
      rw [eqn]
    · exact hard.1 p hp
  -- This is the remaining relative deleted-chart square.  Only paths which
  -- actually pass through the chart centre survive the first clause.  The
  -- second is its two-parameter (null square) analogue.
  -- Loops which never leave the distinguished coordinate ball need no
  -- perturbation at all: that ball is convex through its chart.  In
  -- particular the constant loop is already a deleted representative.
  -- Isolating this case leaves only visits through the rim for the
  -- relative-cut argument.
  have hbase : (y : B.carrier) ∈
        NonlinearThreeManifoldSupport.chartLocalBall
          (E:= EuclideanSpace ℝ (Fin 3)) b A.R :=
    NonlinearThreeManifoldSupport.shrink_base_inside
      (E:= EuclideanSpace ℝ (Fin 3)) b A y hy
  have punct_ne (z : (({b}:Set B.carrier)ᶜ : Set B.carrier)) :
      (z:B.carrier) ≠ b := by
    have hz : (z:B.carrier) ∉ ({b}:Set B.carrier) := z.property
    intro e
    exact hz (by simpa only [Set.mem_singleton_iff] using e)
  suffices rim :
      ((∀ p : Path (y:B.carrier) (y:B.carrier),
          ¬ (∀ t : unitInterval, (p t) ≠ b) →
          ¬ (∀ t : unitInterval, p t ∈
              NonlinearThreeManifoldSupport.chartLocalBall
                (E:= EuclideanSpace ℝ (Fin 3)) b A.R) →
          ∃ q : Path y y,
            Path.Homotopic (q.map continuous_subtype_val) p) ∧
        (∀ a : Path y y,
          Path.Homotopic (a.map continuous_subtype_val)
            (Path.refl (y:B.carrier)) →
          Path.Homotopic a (Path.refl y))) by
    refine ⟨?_, rim.2⟩
    intro p hp
    classical
    by_cases hc : ∀ t : unitInterval, p t ∈
        NonlinearThreeManifoldSupport.chartLocalBall
          (E:= EuclideanSpace ℝ (Fin 3)) b A.R
    · exact NonlinearThreeManifoldSupport.chartLocalBall_lift_soft
        (E:= EuclideanSpace ℝ (Fin 3)) b A y hbase p hc
    · exact rim.1 p hp hc
  -- A homotopy already living in the deleted set lifts just by the
  -- induced topology.  Peel this harmless case off from the null square;
  -- the genuine relative square still to be cut must hit the centre.
  suffices core :
      ((∀ p : Path (y:B.carrier) (y:B.carrier),
          (∃ t : unitInterval,
              t ≠ (0 : unitInterval) ∧ t ≠ (1 : unitInterval) ∧ p t = b) →
          (∃ t : unitInterval,
              t ≠ (0 : unitInterval) ∧ t ≠ (1 : unitInterval) ∧
              p t ∉ NonlinearThreeManifoldSupport.chartLocalBall
                (E:= EuclideanSpace ℝ (Fin 3)) b A.R) →
          ¬ Path.Homotopic p (Path.refl (y:B.carrier)) →
          ∃ q : Path y y,
            Path.Homotopic (q.map continuous_subtype_val) p) ∧
       (∀ (a : Path y y)
          (HH : (a.map continuous_subtype_val).Homotopy
              (Path.refl (y:B.carrier))),
          a ≠ Path.refl y →
          (¬ ∃ KK : (a.map continuous_subtype_val).Homotopy
              (Path.refl (y:B.carrier)),
                (∀ s t : unitInterval, KK.toFun (s,t) ≠ b)) →
          (∃ s t : unitInterval,
             s ≠ (0:unitInterval) ∧ s ≠ (1:unitInterval) ∧
             t ≠ (0:unitInterval) ∧ t ≠ (1:unitInterval) ∧
             HH.toFun (s,t) = b) →
          Path.Homotopic a (Path.refl y))) by
    constructor
    · intro p hp hout
      by_cases hnull : Path.Homotopic p (Path.refl (y:B.carrier))
      · refine ⟨Path.refl y, ?_⟩
        have er : (Path.refl y).map continuous_subtype_val =
            Path.refl (y:B.carrier) := by
          apply Path.ext
          funext t
          rfl
        rw [er]
        exact hnull.symm
      · classical
        apply core.1 p _ _ hnull
        · rcases not_forall.mp hp with ⟨t, ht⟩
          have eqt : p t = b := not_ne_iff.mp ht
          have t0 : t ≠ (0:unitInterval) := by
            intro h
            subst t
            have yne : (y:B.carrier) ≠ b := punct_ne y
            apply yne
            exact p.source.symm.trans eqt
          have t1 : t ≠ (1:unitInterval) := by
            intro h
            subst t
            have yne : (y:B.carrier) ≠ b := punct_ne y
            apply yne
            exact p.target.symm.trans eqt
          exact ⟨t,t0,t1,eqt⟩
        · rcases not_forall.mp hout with ⟨t, ht⟩
          have t0 : t ≠ (0:unitInterval) := by
            intro h
            subst t
            apply ht
            rw [p.source]
            exact hbase
          have t1 : t ≠ (1:unitInterval) := by
            intro h
            subst t
            apply ht
            rw [p.target]
            exact hbase
          exact ⟨t,t0,t1,ht⟩
    · intro a ha
      classical
      by_cases hrefl : a = Path.refl y
      · subst a
        exact Path.Homotopic.refl _
      by_cases good : ∃ HH : (a.map continuous_subtype_val).Homotopy
              (Path.refl (y:B.carrier)),
                (∀ s t : unitInterval, HH.toFun (s,t) ≠ b)
      · rcases good with ⟨HH,hav⟩
        -- if one null square misses the point, it is literally a
        -- square in the complement (no perturbation or charts).
        let lift : unitInterval × unitInterval →
            (({b}:Set B.carrier)ᶜ : Set B.carrier) := fun z =>
          ⟨HH.toFun z, (by simpa using (hav z.1 z.2))⟩
        have liftc : Continuous lift := by
          apply continuous_induced_rng.2
          exact HH.continuous
        refine ⟨{
          toFun := lift,
          continuous_toFun := liftc,
          map_zero_left := ?_,
          map_one_left := ?_,
          prop' := ?_ }⟩
        · intro t
          apply Subtype.ext
          exact HH.map_zero_left t
        · intro t
          apply Subtype.ext
          exact HH.map_one_left t
        · intro s t ht
          apply Subtype.ext
          exact HH.prop' s t ht
      · rcases ha with ⟨HH⟩
        have hav : ¬ (∀ s t : unitInterval, HH.toFun (s,t) ≠ b) := by
          intro h; exact good ⟨HH,h⟩
        apply core.2 a HH hrefl good
        -- endpoints of a based homotopy lie on the deleted base path, so a
        -- meeting with the centre has both parameters in the open interval.
        rcases not_forall.mp hav with ⟨s, hs⟩
        rcases not_forall.mp hs with ⟨t, ht⟩
        have eqt : HH.toFun (s,t) = b := not_ne_iff.mp ht
        have sval0 : s ≠ (0:unitInterval) := by
          intro h; subst s
          have zne : ((a t : (({b}:Set B.carrier)ᶜ : Set B.carrier)) : B.carrier) ≠ b := punct_ne (a t)
          apply zne
          have hz := HH.map_zero_left t
          exact hz.symm.trans eqt
        have sval1 : s ≠ (1:unitInterval) := by
          intro h; subst s
          have zne : (y:B.carrier) ≠ b := punct_ne y
          apply zne
          have hz := HH.map_one_left t
          exact hz.symm.trans eqt
        have tval0 : t ≠ (0:unitInterval) := by
          intro h; subst t
          have zne : (y:B.carrier) ≠ b := punct_ne y
          apply zne
          have hz := HH.prop' s (0:unitInterval) (by simp)
          have az : (a (0:unitInterval) : (({b}:Set B.carrier)ᶜ : Set B.carrier)) = y := a.source
          have hz' : HH.toFun (s,(0:unitInterval)) = (y:B.carrier) := by
            simpa [az] using hz
          exact hz'.symm.trans eqt
        have tval1 : t ≠ (1:unitInterval) := by
          intro h; subst t
          have zne : (y:B.carrier) ≠ b := punct_ne y
          apply zne
          have hz := HH.prop' s (1:unitInterval) (by simp)
          have az : (a (1:unitInterval) : (({b}:Set B.carrier)ᶜ : Set B.carrier)) = y := a.target
          have hz' : HH.toFun (s,(1:unitInterval)) = (y:B.carrier) := by
            simpa [az] using hz
          exact hz'.symm.trans eqt
        exact ⟨s,t,sval0,sval1,tval0,tval1,eqt⟩
  -- what remains really meets both the centre and the outside of the little
  -- ball; and a null square for it has to meet the centre as well. Neither
  -- behaviour occurs in a single convex chart. This is the genuine
  -- relative cut through the collar.
  -- The contraction is useful also after changing the representative of
  -- the boundary loop inside the deleted type.  Peel that off too; no
  -- representative choices have to respect products in `π₁`.
  suffices deep :
      ((∀ p : Path (y:B.carrier) (y:B.carrier),
          (∃ t : unitInterval,
              t ≠ (0 : unitInterval) ∧ t ≠ (1 : unitInterval) ∧ p t = b) →
          (∃ t : unitInterval,
              t ≠ (0 : unitInterval) ∧ t ≠ (1 : unitInterval) ∧
              p t ∉ NonlinearThreeManifoldSupport.chartLocalBall
                (E:= EuclideanSpace ℝ (Fin 3)) b A.R) →
          ¬ Path.Homotopic p (Path.refl (y:B.carrier)) →
          ∃ q : Path y y,
            Path.Homotopic (q.map continuous_subtype_val) p) ∧
       (∀ (a : Path y y)
          (HH : (a.map continuous_subtype_val).Homotopy
              (Path.refl (y:B.carrier))),
          a ≠ Path.refl y →
          (¬ ∃ KK : (a.map continuous_subtype_val).Homotopy
              (Path.refl (y:B.carrier)),
                (∀ s t : unitInterval, KK.toFun (s,t) ≠ b)) →
          (∃ s t : unitInterval,
             s ≠ (0:unitInterval) ∧ s ≠ (1:unitInterval) ∧
             t ≠ (0:unitInterval) ∧ t ≠ (1:unitInterval) ∧
             HH.toFun (s,t) = b) →
          (¬ ∃ c : Path y y,
             Path.Homotopic a c ∧
             (∀ t : unitInterval,
                ((c t : (({b}:Set B.carrier)ᶜ : Set B.carrier)) : B.carrier) ∈
                  NonlinearThreeManifoldSupport.chartLocalBall
                    (E:= EuclideanSpace ℝ (Fin 3)) b A.R) ∧
             (∀ s t : unitInterval,
                (1 - (s:ℝ)) •
                    ((chartAt (EuclideanSpace ℝ (Fin 3)) b)
                        ((c t : (({b}:Set B.carrier)ᶜ : Set B.carrier)) : B.carrier) -
                      (chartAt (EuclideanSpace ℝ (Fin 3)) b) b) +
                  (s:ℝ) •
                    ((chartAt (EuclideanSpace ℝ (Fin 3)) b) (y:B.carrier) -
                      (chartAt (EuclideanSpace ℝ (Fin 3)) b) b) ≠
                    (0 : EuclideanSpace ℝ (Fin 3)))) →
          Path.Homotopic a (Path.refl y))) by
    constructor
    · exact deep.1
    · intro a HH hn hg hh
      classical
      by_cases rep : ∃ c : Path y y,
             Path.Homotopic a c ∧
             (∀ t : unitInterval,
                ((c t : (({b}:Set B.carrier)ᶜ : Set B.carrier)) : B.carrier) ∈
                  NonlinearThreeManifoldSupport.chartLocalBall
                    (E:= EuclideanSpace ℝ (Fin 3)) b A.R) ∧
             (∀ s t : unitInterval,
                (1 - (s:ℝ)) •
                    ((chartAt (EuclideanSpace ℝ (Fin 3)) b)
                        ((c t : (({b}:Set B.carrier)ᶜ : Set B.carrier)) : B.carrier) -
                      (chartAt (EuclideanSpace ℝ (Fin 3)) b) b) +
                  (s:ℝ) •
                    ((chartAt (EuclideanSpace ℝ (Fin 3)) b) (y:B.carrier) -
                      (chartAt (EuclideanSpace ℝ (Fin 3)) b) b) ≠
                    (0 : EuclideanSpace ℝ (Fin 3)))
      · exact
          NonlinearThreeManifoldSupport.chartLocalBall_star_rep_null_deleted
            (E:= EuclideanSpace ℝ (Fin 3)) b A y hbase a rep
      · exact deep.2 a HH hn hg hh rep
  -- Thus a remaining null disc has a loop for which even its radial
  -- contraction in the small chart passes through the origin (or it crosses
  -- the rim).  This is the actual two-dimensional general-position cut.
  constructor
  · intro p hp hc hn
    -- this uses only the covering presentation of `B`; the centre/rim
    -- assumptions were needed only for a chart proof, not for paths.
    exact NonlinearThreeManifoldSupport.qOrbit_delete_point_surj
      (QuaternionGroup 2) b y p
  · intro a HH hn hg hit nrep
    -- upstairs this is the familiar finite set of deck translates of the
    -- puncture.  No compatibility with products is needed downstairs.
    suffices up : ∀ (F : Set NonlinearThreeManifoldSupport.qSphere),
        F.Finite → F.Nonempty →
        ∀ (z : (Fᶜ : Set NonlinearThreeManifoldSupport.qSphere))
          (L : Path z z), Path.Homotopic L (Path.refl z) by
      apply NonlinearThreeManifoldSupport.qOrbit_delete_point_inj_of_upstairs
        (QuaternionGroup 2) up b y a
      exact ⟨HH⟩
    -- choose a forbidden pole and stereographically identify its complement.
    -- This cuts away all group/covering structure: the unresolved kernel is
    -- only the familiar finite-puncture fact in a three-dimensional real
    -- vector space.
    apply NonlinearThreeManifoldSupport.qSphere_delete_finite_of_vector
    intro c T hf
    classical
    by_cases hnT : T.Nonempty
    · -- Peel off the radial case as well.  The last case is a loop in
      -- `ℝ³` whose straight based contraction meets one of finitely many
      -- points.
      intro v p
      by_cases star : ∀ s t : unitInterval,
          (1 - (s:ℝ)) •
              ((p t : (Tᶜ : Set ((ℝ ∙ (c : Quaternion ℝ))ᗮ))) :
                ((ℝ ∙ (c : Quaternion ℝ))ᗮ)) +
            (s:ℝ) • (v : ((ℝ ∙ (c : Quaternion ℝ))ᗮ)) ∉ T
      · exact NonlinearThreeManifoldSupport.vector_delete_star T v p star
      · -- The arbitrary loop can first be replaced, quite harmlessly, by a
        -- polynomial vector path.  Unlike the original interval map this
        -- cannot be space filling.  The exact metric estimate and the
        -- endpoint-fixed interpolation are isolated in VectorRayReduction.
        obtain ⟨n,hn,hz0,hz1,q,hpq,hq⟩ :=
          NonlinearThreeManifoldSupport.vector_delete_bernstein_representative
            T hf v p
        refine hpq.trans ?_
        -- From now on all the topology is in a finite-ray perturbation of
        -- this *one* polynomial curve, not in a general square in a
        -- manifold.
        obtain ⟨ε,he,clear⟩ :=
          NonlinearThreeManifoldSupport.finite_path_clearance T hf v q
        let f : C(unitInterval,
              ((ℝ ∙ (c : Quaternion ℝ))ᗮ)) :=
          ⟨(fun t : unitInterval =>
              ((p t : (Tᶜ : Set ((ℝ ∙ (c : Quaternion ℝ))ᗮ))) :
                 ((ℝ ∙ (c : Quaternion ℝ))ᗮ))), by fun_prop⟩
        let z : unitInterval → ((ℝ ∙ (c : Quaternion ℝ))ᗮ) :=
          fun t => bernsteinApproximation n f t
        have hz (t : unitInterval) : z t =
             ((q t : (Tᶜ : Set ((ℝ ∙ (c : Quaternion ℝ))ᗮ))) :
                 ((ℝ ∙ (c : Quaternion ℝ))ᗮ)) := by
          simpa [z, f] using (hq t).symm
        -- It remains only to move a polynomial arc a tiny amount so that it
        -- misses the finitely many rays based at v past T. Closeness is enough
        -- for the homotopy to the original loop; no disk occurs any more.
        suffices perturb : ∃ w : unitInterval →
              ((ℝ ∙ (c : Quaternion ℝ))ᗮ),
            Continuous w ∧ w 0 = (v : ((ℝ ∙ (c : Quaternion ℝ))ᗮ)) ∧
              w 1 = (v : ((ℝ ∙ (c : Quaternion ℝ))ᗮ)) ∧
            (∀ t : unitInterval, ‖w t - z t‖ < ε) ∧
            (∀ t : unitInterval,
              ∀ a ∈ T, ¬ ∃ r : ℝ, 1 ≤ r ∧
                (w t - (v : ((ℝ ∙ (c : Quaternion ℝ))ᗮ))) =
                   r • (a - (v : ((ℝ ∙ (c : Quaternion ℝ))ᗮ)))) by
          rcases perturb with ⟨w,wc,w0,w1,wclose,wray⟩
          have closeq : ∀ t : unitInterval,
              ‖w t - ((q t :
                 (Tᶜ : Set ((ℝ ∙ (c : Quaternion ℝ))ᗮ))) :
                     ((ℝ ∙ (c : Quaternion ℝ))ᗮ))‖ < ε := by
            intro t
            simpa [hz t] using wclose t
          have safe :=
            NonlinearThreeManifoldSupport.interpolation_safe_of_close
              T v q ε clear w closeq
          obtain ⟨r,hqr,hr⟩ :=
            NonlinearThreeManifoldSupport.vector_path_homotopy_of_interpolation
              T v q w wc w0 w1 safe
          exact NonlinearThreeManifoldSupport.vector_delete_of_ray_representative
            T v q ⟨r, hqr, (by
              intro t a ha
              simpa [hr t] using (wray t a ha))⟩
        classical
        by_cases zr : ∀ t : unitInterval, ∀ a ∈ T,
            ¬ ∃ r : ℝ, 1 ≤ r ∧
              (z t - (v : ((ℝ ∙ (c : Quaternion ℝ))ᗮ))) =
                r • (a - (v : ((ℝ ∙ (c : Quaternion ℝ))ᗮ)))
        · refine ⟨z, ?_, ?_, ?_, ?_, zr⟩
          · -- it is a genuine polynomial, in particular continuous
            exact (bernsteinApproximation n f).continuous
          · have e := congrArg Subtype.val q.source
            exact (hz 0).trans e
          · have e := congrArg Subtype.val q.target
            exact (hz 1).trans e
          · intro t
            simpa using he
        · -- Thus the last outstanding vector cut is not about closeness or
          -- endpoints: this polynomial actually meets one of the based
          -- deleted rays.  In three dimensions a tiny transverse polynomial
          -- bump avoids finitely many such coincidences.
          push_neg at zr
          rcases zr with ⟨tt, aa, ha, rr, hrr, hray⟩
          -- a generic parabolic bump of a polynomial arc misses all finite
          -- rays at once.  The choice of direction uses the spare third
          -- dimension of the stereographic target.
          have cn : ‖(c:Quaternion ℝ)‖ = 1 := by
            have h := c.property
            change dist (c:Quaternion ℝ) 0 = 1 at h
            simpa [dist_zero_right] using h
          have fspan : Module.finrank ℝ (ℝ ∙ (c : Quaternion ℝ)) = 1 := by
            apply finrank_span_singleton
            intro h
            have hh := cn
            simp [h] at hh
          have fw : Module.finrank ℝ ((ℝ ∙ (c : Quaternion ℝ))ᗮ) = 3 := by
            have hh := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ (c : Quaternion ℝ))
            have fq : Module.finrank ℝ (Quaternion ℝ) = 4 := Quaternion.finrank_eq_four (R:=ℝ)
            rw [fspan, fq] at hh
            omega
          have hthree : 2 < Module.finrank ℝ ((ℝ ∙ (c : Quaternion ℝ))ᗮ) := by
            rw [fw]
            omega
          -- endpoints of this Bernstein curve are the base vector
          have zz0 : bernsteinApproximation n f 0 =
               (v : ((ℝ ∙ (c : Quaternion ℝ))ᗮ)) := by
            exact hz0
          have zz1 : bernsteinApproximation n f 1 =
               (v : ((ℝ ∙ (c : Quaternion ℝ))ᗮ)) := by
            exact hz1
          exact NonlinearThreeManifoldSupport.polynomial_finite_ray_bump
            hthree T hf v n f zz0 zz1 ε he
    · have eqT : Tᶜ = (Set.univ : Set ((ℝ ∙ (c : Quaternion ℝ))ᗮ)) := by
        have em : T = (∅ : Set ((ℝ ∙ (c : Quaternion ℝ))ᗮ)) :=
          Set.not_nonempty_iff_eq_empty.mp hnT
        simp [em]
      intro v p
      let ee : (Tᶜ : Set ((ℝ ∙ (c : Quaternion ℝ))ᗮ)) ≃ₜ
            ((ℝ ∙ (c : Quaternion ℝ))ᗮ) :=
        (Homeomorph.setCongr eqT).trans
          (Homeomorph.Set.univ ((ℝ ∙ (c : Quaternion ℝ))ᗮ))
      exact NonlinearThreeManifoldSupport.paths_homotopic_of_homeo_vector
        ee p (Path.refl v)/-ResultProofEnd-/
/-ResultEnd-/

end Submission
