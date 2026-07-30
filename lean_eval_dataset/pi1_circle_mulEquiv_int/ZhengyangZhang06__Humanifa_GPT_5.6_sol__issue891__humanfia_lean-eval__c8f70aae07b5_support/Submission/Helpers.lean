import Mathlib

noncomputable section

open Function

namespace IsAddQuotientCoveringMap

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} [AddCommGroup G] [AddAction G E]

lemma fiberEquivAddGroup_eq_iff (qcov : IsAddQuotientCoveringMap p G)
    {x : X} (e e' : p ⁻¹' {x}) (g : G) :
    qcov.fiberEquivAddGroup e e' = g ↔ e' = g +ᵥ (e : E) := by
  rw [fiberEquivAddGroup, Equiv.symm_apply_eq, Equiv.ofBijective_apply,
    Subtype.mk.injEq]

lemma monodromy_vadd (qcov : IsAddQuotientCoveringMap p G)
    {x y : X} (γ : Path.Homotopic.Quotient x y) (g : G) (e : p ⁻¹' {x}) :
    (qcov.isCoveringMap.monodromy γ
      ⟨g +ᵥ (e : E), (qcov.map_vadd g).trans e.2⟩).1 =
        g +ᵥ (qcov.isCoveringMap.monodromy γ e).1 := by
  letI : ContinuousConstVAdd G E := qcov.toContinuousConstVAdd
  refine Quotient.inductionOn γ ?_
  intro γ
  have hlift :
      (fun t ↦ g +ᵥ qcov.isCoveringMap.liftPath γ e
        (γ.source.trans e.2.symm) t) =
        qcov.isCoveringMap.liftPath γ (g +ᵥ (e : E))
          (γ.source.trans ((qcov.map_vadd g).trans e.2).symm) := by
    apply (qcov.isCoveringMap.eq_liftPath_iff _).2
    refine ⟨by fun_prop, ?_, ?_⟩
    · funext t
      simp only [Function.comp_apply]
      rw [qcov.map_vadd]
      exact congr_fun
        (qcov.isCoveringMap.liftPath_lifts γ e (γ.source.trans e.2.symm)) t
    · rw [qcov.isCoveringMap.liftPath_zero]
  exact (congr_fun hlift 1).symm

noncomputable def deckIndex (qcov : IsAddQuotientCoveringMap p G) (e : E) :
    FundamentalGroup X (p e) → G :=
  fun γ ↦ qcov.fiberEquivAddGroup ⟨e, rfl⟩
    (qcov.isCoveringMap.monodromy γ ⟨e, rfl⟩)

lemma deckIndex_refl (qcov : IsAddQuotientCoveringMap p G) (e : E) :
    qcov.deckIndex e (Path.Homotopic.Quotient.refl (p e)) = 0 := by
  apply (fiberEquivAddGroup_eq_iff qcov ⟨e, rfl⟩ _ 0).2
  change (qcov.isCoveringMap.monodromy (.refl (p e)) ⟨e, rfl⟩).1 =
    (0 : G) +ᵥ (e : E)
  rw [qcov.isCoveringMap.monodromy_refl]
  simp

lemma deckIndex_trans (qcov : IsAddQuotientCoveringMap p G) (e : E)
    (γ δ : Path.Homotopic.Quotient (p e) (p e)) :
    qcov.deckIndex e (γ.trans δ) = qcov.deckIndex e γ + qcov.deckIndex e δ := by
  let b : p ⁻¹' {p e} := ⟨e, rfl⟩
  let g := qcov.deckIndex e γ
  let h := qcov.deckIndex e δ
  change qcov.fiberEquivAddGroup b
    (qcov.isCoveringMap.monodromy (γ.trans δ) b) = g + h
  apply (fiberEquivAddGroup_eq_iff qcov b _ (g + h)).2
  change (qcov.isCoveringMap.monodromy (γ.trans δ) b).1 = (g + h) +ᵥ e
  rw [qcov.isCoveringMap.monodromy_trans_apply]
  have hγ : qcov.isCoveringMap.monodromy γ b =
      ⟨g +ᵥ (b : E), (qcov.map_vadd g).trans b.2⟩ := by
    apply Subtype.ext
    exact (fiberEquivAddGroup_eq_iff qcov b _ g).1 rfl
  rw [hγ]
  have hδ := (fiberEquivAddGroup_eq_iff qcov b
    (qcov.isCoveringMap.monodromy δ b) h).1 rfl
  change (qcov.isCoveringMap.monodromy δ b).1 = h +ᵥ e at hδ
  calc
    (qcov.isCoveringMap.monodromy δ
      ⟨g +ᵥ (b : E), (qcov.map_vadd g).trans b.2⟩).1 =
        g +ᵥ (qcov.isCoveringMap.monodromy δ b).1 :=
      monodromy_vadd qcov δ g b
    _ = g +ᵥ (h +ᵥ e) := congr_arg (g +ᵥ ·) hδ
    _ = (g + h) +ᵥ e := (add_vadd g h e).symm

lemma deckIndex_injective [SimplyConnectedSpace E]
    (qcov : IsAddQuotientCoveringMap p G) (e : E) :
    Injective (qcov.deckIndex e) := by
  intro γ
  refine Quotient.inductionOn γ ?_
  intro γ δ
  refine Quotient.inductionOn δ ?_
  intro δ h
  apply Quotient.sound
  let b : p ⁻¹' {p e} := ⟨e, rfl⟩
  let hγ0 : γ 0 = p e := γ.source
  let hδ0 : δ 0 = p e := δ.source
  let Γ := qcov.isCoveringMap.liftPath γ e hγ0
  let Δ := qcov.isCoveringMap.liftPath δ e hδ0
  have hfiber : qcov.isCoveringMap.monodromy (.mk γ) b =
      qcov.isCoveringMap.monodromy (.mk δ) b := by
    apply (qcov.fiberEquivAddGroup b).injective
    exact h
  have hend : Γ 1 = Δ 1 := congr_arg Subtype.val hfiber
  let γ' : Path e (Γ 1) :=
    ⟨Γ, qcov.isCoveringMap.liftPath_zero .., rfl⟩
  let δ' : Path e (Γ 1) :=
    ⟨Δ, qcov.isCoveringMap.liftPath_zero .., hend.symm⟩
  let p' : C(E, X) := ⟨p, qcov.continuous⟩
  have hlift : (γ'.map qcov.continuous).Homotopic
      (δ'.map qcov.continuous) :=
    (SimplyConnectedSpace.paths_homotopic γ' δ').map p'
  have htarget : p e = p (Γ 1) :=
    ((congr_fun (qcov.isCoveringMap.liftPath_lifts γ e hγ0) 1).trans
      γ.target).symm
  have hγ : (γ'.map qcov.continuous).cast rfl htarget = γ := by
    ext t
    exact congr_fun (qcov.isCoveringMap.liftPath_lifts γ e hγ0) t
  have hδ : (δ'.map qcov.continuous).cast rfl htarget = δ := by
    ext t
    exact congr_fun (qcov.isCoveringMap.liftPath_lifts δ e hδ0) t
  rw [← hγ, ← hδ]
  exact hlift.pathCast rfl htarget

lemma deckIndex_surjective [SimplyConnectedSpace E]
    (qcov : IsAddQuotientCoveringMap p G) (e : E) :
    Surjective (qcov.deckIndex e) := by
  intro g
  let γ := PathConnectedSpace.somePath e (g +ᵥ e)
  let loop : Path (p e) (p e) :=
    (γ.map qcov.continuous).cast rfl (qcov.map_vadd g).symm
  refine ⟨Path.Homotopic.Quotient.mk loop, ?_⟩
  change qcov.fiberEquivAddGroup ⟨e, rfl⟩
    (qcov.isCoveringMap.monodromy (.mk loop) ⟨e, rfl⟩) = g
  apply (fiberEquivAddGroup_eq_iff qcov ⟨e, rfl⟩ _ g).2
  let hloop0 : loop 0 = p e := loop.source
  let Γ := qcov.isCoveringMap.liftPath loop e hloop0
  change Γ 1 = g +ᵥ e
  have hγ : γ.toContinuousMap = Γ := by
    apply (qcov.isCoveringMap.eq_liftPath_iff' _).2
    refine ⟨?_, γ.source⟩
    funext t
    rfl
  calc
    Γ 1 = γ 1 := DFunLike.congr_fun hγ.symm 1
    _ = g +ᵥ e := γ.target

noncomputable def fundamentalGroupToDeck [SimplyConnectedSpace E]
    (qcov : IsAddQuotientCoveringMap p G) (e : E) :
    FundamentalGroup X (p e) →* Multiplicative G where
  toFun γ := Multiplicative.ofAdd (qcov.deckIndex e γ)
  map_one' := by
    change qcov.deckIndex e (.refl (p e)) = 0
    exact qcov.deckIndex_refl e
  map_mul' γ δ := by
    change qcov.deckIndex e (δ.trans γ) =
      qcov.deckIndex e γ + qcov.deckIndex e δ
    rw [qcov.deckIndex_trans, add_comm]

noncomputable def fundamentalGroupMulEquiv [SimplyConnectedSpace E]
    (qcov : IsAddQuotientCoveringMap p G) (e : E) :
    FundamentalGroup X (p e) ≃* Multiplicative G :=
  MulEquiv.ofBijective (qcov.fundamentalGroupToDeck e) <| by
    constructor
    · intro γ δ h
      exact qcov.deckIndex_injective e h
    · intro g
      obtain ⟨γ, hγ⟩ := qcov.deckIndex_surjective e (Multiplicative.toAdd g)
      refine ⟨γ, ?_⟩
      calc
        Multiplicative.ofAdd (qcov.deckIndex e γ) =
            Multiplicative.ofAdd (Multiplicative.toAdd g) :=
          congr_arg Multiplicative.ofAdd hγ
        _ = g := ofAdd_toAdd g

end IsAddQuotientCoveringMap

namespace Submission.Helpers

def intToZMultiples (T : ℝ) : ℤ →+ AddSubgroup.zmultiples T where
  toFun n := ⟨n • T, AddSubgroup.zsmul_mem_zmultiples T n⟩
  map_zero' := by ext; simp
  map_add' n m := by ext; simp [add_mul]

noncomputable def zMultiplesEquivInt (T : ℝ) (hT : T ≠ 0) :
    AddSubgroup.zmultiples T ≃+ ℤ :=
  (AddEquiv.ofBijective (intToZMultiples T) <| by
    constructor
    · intro n m h
      have h' := congr_arg Subtype.val h
      simp only [intToZMultiples, zsmul_eq_mul] at h'
      exact_mod_cast mul_right_cancel₀ hT h'
    · intro x
      obtain ⟨n, hn⟩ := x.2
      exact ⟨n, Subtype.ext hn⟩).symm

end Submission.Helpers

end
