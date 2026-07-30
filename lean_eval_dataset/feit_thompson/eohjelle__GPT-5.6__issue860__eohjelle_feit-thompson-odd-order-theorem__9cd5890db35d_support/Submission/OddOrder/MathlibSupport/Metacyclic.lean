import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
A small interface for metacyclic groups.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable (G : Type u) [Group G]

/-- A group is metacyclic when it has a cyclic normal subgroup with cyclic
quotient.  The normality witness is bound dependently so that the quotient
group instance is available in the final conjunct. -/
def IsMetacyclic : Prop :=
  ∃ (S : Subgroup G) (hS : S.Normal),
    IsCyclic S ∧
      letI : S.Normal := hS
      IsCyclic (G ⧸ S)

/-- Constructor form of `IsMetacyclic`. -/
theorem isMetacyclic_of_normal_cyclic_quotient
    (S : Subgroup G) (hS : S.Normal) (hScyclic : IsCyclic S)
    (hQcyclic : letI : S.Normal := hS; IsCyclic (G ⧸ S)) :
    IsMetacyclic G :=
  ⟨S, hS, hScyclic, hQcyclic⟩

/-- Cyclic groups are metacyclic. -/
theorem isMetacyclic_of_isCyclic (hG : IsCyclic G) : IsMetacyclic G := by
  let S : Subgroup G := ⊤
  have hSnormal : S.Normal := by dsimp [S]; infer_instance
  have hScyclic : IsCyclic S := by
    dsimp [S]
    exact Subgroup.topEquiv.isCyclic.mpr hG
  refine ⟨S, hSnormal, hScyclic, ?_⟩
  letI : S.Normal := hSnormal
  haveI : Subsingleton (G ⧸ S) := by
    dsimp [S]
    exact QuotientGroup.subsingleton_quotient_top
  exact isCyclic_of_subsingleton

/-- Metacyclicity is invariant under multiplicative equivalence. -/
theorem isMetacyclic_of_mulEquiv
    {H : Type*} [Group H] (e : G ≃* H) (hH : IsMetacyclic H) :
    IsMetacyclic G := by
  classical
  rcases hH with ⟨S, hSnormal, hScyclic, hQcyclic⟩
  letI : S.Normal := hSnormal
  let T : Subgroup G := S.comap e.toMonoidHom
  have hTnormal : T.Normal := by
    dsimp [T]
    infer_instance
  letI : T.Normal := hTnormal
  let eT : T ≃* S := by
    let eMap : T ≃* T.map e.toMonoidHom := by
      apply MulEquiv.ofBijective (e.toMonoidHom.subgroupMap T)
      exact ⟨fun _ _ h ↦ Subtype.ext
        (e.injective (congrArg Subtype.val h)),
        e.toMonoidHom.subgroupMap_surjective T⟩
    have hmap : T.map e.toMonoidHom = S := by
      dsimp [T]
      exact Subgroup.map_comap_eq_self_of_surjective e.surjective S
    exact eMap.trans (MulEquiv.subgroupCongr hmap)
  have hTcyclic : IsCyclic T := eT.isCyclic.mpr hScyclic
  let φ : G →* H ⧸ S := (QuotientGroup.mk' S).comp e.toMonoidHom
  have hφsurj : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective S).comp e.surjective
  have hker : T = φ.ker := by
    ext g
    change e g ∈ S ↔ φ g = 1
    exact (QuotientGroup.eq_one_iff (e g)).symm
  let eQ : G ⧸ T ≃* H ⧸ S :=
    QuotientGroup.liftEquiv T hφsurj hker
  have hQcyclic' : IsCyclic (G ⧸ T) := eQ.isCyclic.mpr hQcyclic
  exact ⟨T, hTnormal, hTcyclic, hQcyclic'⟩

/-- A direct product of two cyclic groups is metacyclic. -/
theorem isMetacyclic_prod_of_isCyclic
    {H K : Type*} [Group H] [Group K]
    (hH : IsCyclic H) (hK : IsCyclic K) : IsMetacyclic (H × K) := by
  let S : Subgroup (H × K) := (MonoidHom.snd H K).ker
  have hSnormal : S.Normal := by dsimp [S]; infer_instance
  let eS : H ≃* S := by
    apply MulEquiv.ofBijective ((MonoidHom.inl H K).codRestrict S (by
      intro h
      change (MonoidHom.snd H K) (h, 1) = 1
      rfl))
    constructor
    · intro x y hxy
      exact congrArg (fun z : S ↦ z.1.1) hxy
    · rintro ⟨⟨h, k⟩, hk⟩
      have hkOne : k = 1 := by
        change (MonoidHom.snd H K) (h, k) = 1 at hk
        exact hk
      subst k
      exact ⟨h, rfl⟩
  have hScyclic : IsCyclic S := eS.isCyclic.mp hH
  let eQ : (H × K) ⧸ S ≃* K :=
    QuotientGroup.liftEquiv (φ := MonoidHom.snd H K) S (by
      intro k
      exact ⟨(1, k), rfl⟩) (by
        dsimp [S])
  have hQcyclic : IsCyclic ((H × K) ⧸ S) := eQ.isCyclic.mpr hK
  exact ⟨S, hSnormal, hScyclic, hQcyclic⟩

/-- Lift the cyclic normal factor in a metacyclic quotient.  This packages
the two third-isomorphism transports used in Huppert's induction. -/
theorem exists_normal_over_of_quotient_isMetacyclic
    [Finite G] (T : Subgroup G) (hTnormal : T.Normal)
    (hmeta : letI : T.Normal := hTnormal; IsMetacyclic (G ⧸ T)) :
    ∃ (X : Subgroup G) (hXnormal : X.Normal),
      T ≤ X ∧
        (letI : X.Normal := hXnormal
         let TX : Subgroup X := T.subgroupOf X
         IsCyclic (X ⧸ TX)) ∧
        (letI : X.Normal := hXnormal
         IsCyclic (G ⧸ X)) := by
  classical
  letI : T.Normal := hTnormal
  rcases hmeta with ⟨Xbar, hXbarNormal, hXbarCyclic, hOuterCyclic⟩
  letI : Xbar.Normal := hXbarNormal
  let q : G →* G ⧸ T := QuotientGroup.mk' T
  let X : Subgroup G := Xbar.comap q
  have hXnormal : X.Normal := by
    dsimp [X]
    infer_instance
  letI : X.Normal := hXnormal
  have hTX : T ≤ X := by
    intro t ht
    change q t ∈ Xbar
    have hqt : q t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
    rw [hqt]
    exact Xbar.one_mem
  let TX : Subgroup X := T.subgroupOf X
  have hTXnormal : TX.Normal := by
    dsimp [TX]
    infer_instance
  letI : TX.Normal := hTXnormal
  have hXmap : X.map q = Xbar := by
    dsimp [X, q]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective T) Xbar
  let eInner : X ⧸ TX ≃* Xbar :=
    (QuotientGroup.liftEquiv TX (q.subgroupMap_surjective X) (by
      dsimp [TX, q]
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])).trans
      (MulEquiv.subgroupCongr hXmap)
  have hInnerCyclic : IsCyclic (X ⧸ TX) :=
    eInner.isCyclic.mpr hXbarCyclic
  let eOuter : (G ⧸ T) ⧸ Xbar ≃* G ⧸ X :=
    (QuotientGroup.quotientMulEquivOfEq hXmap).symm.trans
      (QuotientGroup.quotientQuotientEquivQuotient T X hTX)
  have hOuterCyclic' : IsCyclic (G ⧸ X) :=
    eOuter.isCyclic.mp hOuterCyclic
  exact ⟨X, hXnormal, hTX, hInnerCyclic, hOuterCyclic'⟩

end Submission.OddOrder.MathlibSupport
