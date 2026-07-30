import Submission.JacFunctorial.ChallengeLaws

/-!
# Cross-universe functorial API (`X : Type u`, `Y : Type v`, `Z : Type w`)

Unit: jacobian-functoriality (shim-support extension, for the lean-eval submission shim whose
template states `pushforward`/`pullback`/`degree` and their laws with three independent
universes).

The one-universe restriction of `Jacobian.inducedHom`
(`Jacobian/JacobianConstruction/Functorial.lean`) is an artifact of its variable block, not of
the construction: the linear core `RS.inducedHom` acts between the `Type 0` quotients
`RS.Jac₀ X → RS.Jac₀ Y`, and only the `ULift` shells carry the universes — and
`ULift.up`/`ULift.down` (bundled as `RS.uliftUpHom`/`RS.uliftDownHom`) are already
cross-universe. This file re-elaborates the substrate and the challenge-level functorial API
with independent, **explicit** universes `u v w` (ground universe binders everywhere, never
`Type*` — elaborating a `Jacobian X`-to-`Jacobian Y` declaration at distinct universe
*metavariables* sends the unifier into the documented `ULift`/quotient defeq grind, but with
ground universes elaboration is immediate):

* `Jacobian.inducedHomCU` / `Jacobian.contMDiff_inducedHomCU` /
  `Jacobian.inducedHomCU_apply_up_mk` — the one-universe `inducedHom` definition body and proof
  scripts, verbatim, at `X : Type u`, `Y : Type v`.
* `RS.pushforwardT_compCU` / `RS.pullbackT_compCU` / `RS.pushforwardT_pullbackT_applyCU` — the
  `T`-level laws of `ChallengeLaws.lean` re-proved (same scripts) with the surfaces in
  independent universes: the statements live entirely in `Type 0` (period coordinates), the
  universes enter only through the surface parameters, so the one-universe originals simply
  cannot be *instantiated* cross-universe — but their proofs re-run unchanged (all the
  `Form1`-level inputs `Form1.pullback_comp`/`Form1.trace_comp`/`Form1.trace_pullback` are
  already cross-universe).
* `RS.Jacobian.pushforwardCU` / `RS.Jacobian.pullbackCU`, their `contMDiff` lemmas (same
  inherited `[DiscreteTopology (periodSubgroup _).topologicalClosure]` gates, globally
  discharged since `Jacobian/CechCount/Final.lean`), and the five challenge laws
  (`pushforwardCU_id_apply`, `pushforwardCU_comp_apply`, `pullbackCU_id_apply`,
  `pullbackCU_comp_apply`, `pushforwardCU_pullbackCU`) — proofs are `ChallengeLaws.lean`'s
  representative-level computations, verbatim, through `inducedHomCU_apply_up_mk`.

At `u = v = w` every `*CU` declaration is definitionally the corresponding one-universe one
(identical bodies).
-/

open scoped ContDiff Manifold
open IsManifold Module

noncomputable section

universe u v w

section InducedHomCU

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

namespace Jacobian

/-- Cross-universe `Jacobian.inducedHom` (`X : Type u`, `Y : Type v`): a `ℂ`-linear map on the
ambient period spaces respecting the period subgroups induces `Jacobian X →ₜ+ Jacobian Y`. Same
body as the one-universe original — the `Type 0` core `RS.inducedHom` never sees `u`, `v`; only
the (cross-universe) `ULift` shells do. -/
noncomputable def inducedHomCU {T : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ)}
    (hT : RS.periodSubgroup X ≤ (RS.periodSubgroup Y).topologicalClosure.comap T.toAddMonoidHom) :
    Jacobian.{u} X →ₜ+ Jacobian.{v} Y :=
  RS.uliftUpHom.comp
    ((RS.inducedHom (RS.periodSubgroup X).topologicalClosure
        (RS.periodSubgroup Y).topologicalClosure T
        (AddSubgroup.topologicalClosure_minimal (RS.periodSubgroup X) hT
          (((RS.periodSubgroup Y).isClosed_topologicalClosure).preimage
            T.continuous_of_finiteDimensional))).comp
      RS.uliftDownHom)

/-- Cross-universe `Jacobian.contMDiff_inducedHom`: the induced map is `ω`-smooth, given
discreteness of both period-subgroup closures. Same proof as the one-universe original. -/
theorem contMDiff_inducedHomCU {T : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ)}
    (hT : RS.periodSubgroup X ≤ (RS.periodSubgroup Y).topologicalClosure.comap T.toAddMonoidHom)
    [DiscreteTopology (RS.periodSubgroup X).topologicalClosure]
    [DiscreteTopology (RS.periodSubgroup Y).topologicalClosure] :
    ContMDiff 𝓘(ℂ, Fin (genus X) → ℂ) 𝓘(ℂ, Fin (genus Y) → ℂ) ω (inducedHomCU hT) := by
  unfold inducedHomCU
  have hclosure : (RS.periodSubgroup X).topologicalClosure ≤
      (RS.periodSubgroup Y).topologicalClosure.comap T.toAddMonoidHom :=
    AddSubgroup.topologicalClosure_minimal (RS.periodSubgroup X) hT
      (((RS.periodSubgroup Y).isClosed_topologicalClosure).preimage
        T.continuous_of_finiteDimensional)
  have h1 := RS.contMDiff_uliftUp (RS.periodSubgroup Y).topologicalClosure
  have h2 := RS.contMDiff_inducedHom (L := (RS.periodSubgroup X).topologicalClosure)
    (L' := (RS.periodSubgroup Y).topologicalClosure) hclosure
  have h3 := RS.contMDiff_uliftDown (RS.periodSubgroup X).topologicalClosure
  have := (h1.comp h2).comp h3
  exact this

/-- `Jacobian.inducedHomCU` on representatives (cross-universe
`RS.Jacobian.inducedHom_apply_up_mk`, same proof). -/
theorem inducedHomCU_apply_up_mk
    {T : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ)}
    (hT : RS.periodSubgroup X ≤ (RS.periodSubgroup Y).topologicalClosure.comap
      T.toAddMonoidHom) (z : Fin (genus X) → ℂ) :
    inducedHomCU hT (ULift.up (QuotientAddGroup.mk z))
      = ULift.up (QuotientAddGroup.mk (T z)) := by
  have h : inducedHomCU hT (ULift.up (QuotientAddGroup.mk z))
      = RS.uliftUpHom (RS.inducedHom (RS.periodSubgroup X).topologicalClosure
          (RS.periodSubgroup Y).topologicalClosure T
          (AddSubgroup.topologicalClosure_minimal (RS.periodSubgroup X) hT
            (((RS.periodSubgroup Y).isClosed_topologicalClosure).preimage
              T.continuous_of_finiteDimensional))
          (RS.uliftDownHom ((ULift.up (QuotientAddGroup.mk z)) : Jacobian.{u} X))) := rfl
  rw [h]
  simp [RS.inducedHom_apply_mk]

end Jacobian

end InducedHomCU

namespace RS

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-! ### The cross-universe maps -/

/-- Cross-universe `RS.Jacobian.pushforward` (`X : Type u`, `Y : Type v`). -/
noncomputable def Jacobian.pushforwardCU (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian.{u} X →ₜ+ Jacobian.{v} Y :=
  Jacobian.inducedHomCU (periodSubgroup_le_comap_pushforwardT f hf)

/-- Cross-universe `RS.Jacobian.pullback` (`X : Type u`, `Y : Type v`). Equal to the zero map
if the map on curves is constant (`Form1.trace`'s convention). -/
noncomputable def Jacobian.pullbackCU (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian.{v} Y →ₜ+ Jacobian.{u} X :=
  Jacobian.inducedHomCU (periodSubgroup_le_comap_pullbackT f hf)

/-- Cross-universe `RS.Jacobian.pushforward_contMDiff` (same inherited discreteness gates,
globally discharged in the full library). -/
theorem Jacobian.pushforwardCU_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    [DiscreteTopology (RS.periodSubgroup X).topologicalClosure]
    [DiscreteTopology (RS.periodSubgroup Y).topologicalClosure] :
    ContMDiff 𝓘(ℂ, Fin (genus X) → ℂ) 𝓘(ℂ, Fin (genus Y) → ℂ) ω
      (Jacobian.pushforwardCU f hf) :=
  Jacobian.contMDiff_inducedHomCU (periodSubgroup_le_comap_pushforwardT f hf)

/-- Cross-universe `RS.Jacobian.pullback_contMDiff` (same inherited discreteness gates,
globally discharged in the full library). -/
theorem Jacobian.pullbackCU_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    [DiscreteTopology (RS.periodSubgroup X).topologicalClosure]
    [DiscreteTopology (RS.periodSubgroup Y).topologicalClosure] :
    ContMDiff 𝓘(ℂ, Fin (genus Y) → ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω
      (Jacobian.pullbackCU f hf) :=
  Jacobian.contMDiff_inducedHomCU (periodSubgroup_le_comap_pullbackT f hf)

/-! ### `T`-level laws, cross-universe -/

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

/-- Cross-universe `RS.pushforwardT_comp` (same proof; the one-universe original cannot be
instantiated at three distinct universes). -/
theorem pushforwardT_compCU (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pushforwardT (g ∘ f) (hg.comp hf) = (pushforwardT g hg).comp (pushforwardT f hf) := by
  unfold pushforwardT
  rw [Form1.pullback_comp f hf g hg, ← LinearMap.dualMap_comp_dualMap]
  ext z i
  simp

/-- Cross-universe `RS.pullbackT_comp` (same proof). -/
theorem pullbackT_compCU (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pullbackT (g ∘ f) (hg.comp hf) = (pullbackT f hf).comp (pullbackT g hg) := by
  unfold pullbackT
  rw [Form1.trace_comp f hf g hg, ← LinearMap.dualMap_comp_dualMap]
  ext z i
  simp

/-- Cross-universe `RS.pushforwardT_pullbackT_apply` (same proof): the composed period map of
`pullback` then `pushforward` is multiplication by the degree. -/
theorem pushforwardT_pullbackT_applyCU (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (z : Fin (genus Y) → ℂ) :
    pushforwardT f hf (pullbackT f hf z) = (ContMDiff.degree f hf : ℂ) • z := by
  funext i
  show periodCoordEquiv Y ((Form1.pullback f hf).dualMap
      ((periodCoordEquiv X).symm (periodCoordEquiv X ((Form1.trace f hf).dualMap
        ((periodCoordEquiv Y).symm z))))) i = _
  rw [(periodCoordEquiv X).symm_apply_apply, periodCoordEquiv_apply,
    LinearMap.dualMap_apply, LinearMap.dualMap_apply, Form1.trace_pullback f hf (basis Y i),
    map_smul]
  have hbase : ((periodCoordEquiv Y).symm z) (RS.basis Y i) = z i := by
    rw [← periodCoordEquiv_apply, (periodCoordEquiv Y).apply_symm_apply]
  rw [hbase]
  simp

/-! ### The challenge laws, cross-universe -/

/-- Cross-universe `RS.Jacobian.pushforward_id_apply` (same proof). -/
theorem Jacobian.pushforwardCU_id_apply (P : Jacobian.{u} X) :
    Jacobian.pushforwardCU id contMDiff_id P = P := by
  obtain ⟨z, rfl⟩ := Jacobian.exists_rep P
  show Jacobian.inducedHomCU _ (ULift.up (QuotientAddGroup.mk z)) = _
  rw [Jacobian.inducedHomCU_apply_up_mk, pushforwardT_id]
  rfl

/-- Cross-universe `RS.Jacobian.pullback_id_apply` (same proof). -/
theorem Jacobian.pullbackCU_id_apply (P : Jacobian.{u} X) :
    Jacobian.pullbackCU id contMDiff_id P = P := by
  obtain ⟨z, rfl⟩ := Jacobian.exists_rep P
  show Jacobian.inducedHomCU _ (ULift.up (QuotientAddGroup.mk z)) = _
  rw [Jacobian.inducedHomCU_apply_up_mk, pullbackT_id]
  rfl

/-- Cross-universe `RS.Jacobian.pushforward_comp_apply` (same proof, through
`pushforwardT_compCU`). -/
theorem Jacobian.pushforwardCU_comp_apply (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (P : Jacobian.{u} X) :
    Jacobian.pushforwardCU (g ∘ f) (hg.comp hf) P
      = Jacobian.pushforwardCU g hg (Jacobian.pushforwardCU f hf P) := by
  obtain ⟨z, rfl⟩ := Jacobian.exists_rep P
  show Jacobian.inducedHomCU _ (ULift.up (QuotientAddGroup.mk z))
    = Jacobian.pushforwardCU g hg (Jacobian.inducedHomCU _ (ULift.up (QuotientAddGroup.mk z)))
  rw [Jacobian.inducedHomCU_apply_up_mk, Jacobian.inducedHomCU_apply_up_mk]
  show _ = Jacobian.inducedHomCU _ (ULift.up (QuotientAddGroup.mk (pushforwardT f hf z)))
  rw [Jacobian.inducedHomCU_apply_up_mk, pushforwardT_compCU f hf g hg]
  rfl

/-- Cross-universe `RS.Jacobian.pullback_comp_apply` (same proof, through
`pullbackT_compCU`). -/
theorem Jacobian.pullbackCU_comp_apply (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (P : Jacobian.{w} Z) :
    Jacobian.pullbackCU (g.comp f) (hg.comp hf) P
      = Jacobian.pullbackCU f hf (Jacobian.pullbackCU g hg P) := by
  obtain ⟨z, rfl⟩ := Jacobian.exists_rep P
  show Jacobian.inducedHomCU _ (ULift.up (QuotientAddGroup.mk z))
    = Jacobian.pullbackCU f hf (Jacobian.inducedHomCU _ (ULift.up (QuotientAddGroup.mk z)))
  rw [Jacobian.inducedHomCU_apply_up_mk, Jacobian.inducedHomCU_apply_up_mk]
  show _ = Jacobian.inducedHomCU _ (ULift.up (QuotientAddGroup.mk (pullbackT g hg z)))
  rw [Jacobian.inducedHomCU_apply_up_mk, pullbackT_compCU f hf g hg]
  rfl

/-- Cross-universe `RS.Jacobian.pushforward_pullback` (same proof, through
`pushforwardT_pullbackT_applyCU`): the projection formula
`pushforward f ∘ pullback f = deg f`. -/
theorem Jacobian.pushforwardCU_pullbackCU (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (P : Jacobian.{v} Y) :
    Jacobian.pushforwardCU f hf (Jacobian.pullbackCU f hf P)
      = (ContMDiff.degree f hf) • P := by
  obtain ⟨z, rfl⟩ := Jacobian.exists_rep P
  show Jacobian.pushforwardCU f hf
      (Jacobian.inducedHomCU _ (ULift.up (QuotientAddGroup.mk z))) = _
  rw [Jacobian.inducedHomCU_apply_up_mk]
  show Jacobian.inducedHomCU _ (ULift.up (QuotientAddGroup.mk (pullbackT f hf z))) = _
  rw [Jacobian.inducedHomCU_apply_up_mk, pushforwardT_pullbackT_applyCU f hf z,
    Nat.cast_smul_eq_nsmul]
  have h1 : QuotientAddGroup.mk (s := (RS.periodSubgroup Y).topologicalClosure)
      (ContMDiff.degree f hf • z)
      = ContMDiff.degree f hf
        • QuotientAddGroup.mk (s := (RS.periodSubgroup Y).topologicalClosure) z := by
    exact map_nsmul (QuotientAddGroup.mk' _) (ContMDiff.degree f hf) z
  rw [h1]
  exact map_nsmul (RS.uliftUpHom.toAddMonoidHom
    (A := (Fin (genus Y) → ℂ) ⧸ (RS.periodSubgroup Y).topologicalClosure))
    (ContMDiff.degree f hf) _

end RS

end
