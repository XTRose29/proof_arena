import Submission.OddOrder.BG.Section03.OddPrimeSemidirectTheorem
import Submission.OddOrder.BG.Section03.OddPrimeElementaryAbelianCentralizer
import Submission.OddOrder.MathlibSupport.AmbientFitting
import Submission.OddOrder.MathlibSupport.ChiefFactorFaithfulPCore
import Submission.OddOrder.MathlibSupport.ChiefStabilizerFitting
import Submission.OddOrder.MathlibSupport.CoprimeCommutatorIdempotent
import Submission.OddOrder.MathlibSupport.CoprimeFittingCentralizer
import Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy
import Submission.OddOrder.MathlibSupport.SylowFunctorial

/-!
# Prime actions and the Fitting subgroup

This file ports `BGsection3.v: odd_sdprod_primact_commg_sub_Fitting`
(Bender--Glauberman Theorem 3.8).  The source calls an action *semiprime*
when every nontrivial subgroup of the acting factor has the same fixed-point
subgroup in the normal factor.  The predicate is repeated here, below the
Section 13 dependency boundary, because Theorem 3.8 is needed by Section 15
and must not import Section 13.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u

noncomputable section

/-- MathComp's `semiprime K R`, kept in Section 3 so later users do not
create a dependency cycle through Section 13. -/
def IsSemiprimeAction
    {G : Type u} [Group G] (K R : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ R → X ≠ ⊥ →
    centralizerWithin K X = centralizerWithin K R

namespace IsSemiprimeAction

/-- Restrict the normal factor of a semiprime action. -/
theorem mono_left
    {G : Type u} [Group G] {L K R : Subgroup G}
    (hLK : L ≤ K) (h : IsSemiprimeAction K R) :
    IsSemiprimeAction L R := by
  intro X hXR hX
  have hcent := h X hXR hX
  change L ⊓ Subgroup.centralizer (X : Set G) =
    L ⊓ Subgroup.centralizer (R : Set G)
  change K ⊓ Subgroup.centralizer (X : Set G) =
    K ⊓ Subgroup.centralizer (R : Set G) at hcent
  apply le_antisymm
  · intro x hx
    have hxKX : x ∈ K ⊓ Subgroup.centralizer (X : Set G) :=
      ⟨hLK hx.1, hx.2⟩
    exact ⟨hx.1, hcent.le hxKX |>.2⟩
  · intro x hx
    have hxKR : x ∈ K ⊓ Subgroup.centralizer (R : Set G) :=
      ⟨hLK hx.1, hx.2⟩
    exact ⟨hx.1, hcent.ge hxKR |>.2⟩

/-- Every nontrivial actor subgroup has the source centralizer. -/
theorem centralizer_eq
    {G : Type u} [Group G] {K R X : Subgroup G}
    (h : IsSemiprimeAction K R) (hXR : X ≤ R) (hX : X ≠ ⊥) :
    centralizerWithin K X = centralizerWithin K R :=
  h X hXR hX

end IsSemiprimeAction

/-- The ambient normalizer supplied by the internal semidirect product. -/
private theorem complement_le_normalizer_of_normal
    {G : Type u} [Group G] {K R : Subgroup G}
    (hK : K.Normal) : R ≤ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr hK]
  exact le_top

/-- Quotient step in the source proof.  If a nontrivial actor subgroup has
the same centralizer as the whole actor and its commutator is killed by a
normal subgroup, then the whole mixed commutator is killed as well. -/
private theorem commutator_le_of_actor_subgroup
    {G : Type u} [Group G] [Finite G]
    {N K R X : Subgroup G} [N.Normal] [IsSolvable R]
    (hNK : N ≤ K) (hXR : X ≤ R)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hcent : centralizerWithin K X = centralizerWithin K R)
    (hcommX : ⁅K, X⁆ ≤ N) :
    ⁅K, R⁆ ≤ N := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Kq : Subgroup (G ⧸ N) := K.map q
  let Rq : Subgroup (G ⧸ N) := R.map q
  let Xq : Subgroup (G ⧸ N) := X.map q
  have hcopNR : Nat.Coprime (Nat.card N) (Nat.card R) :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hNK)
  have hcopNX : Nat.Coprime (Nat.card N) (Nat.card X) :=
    hcopNR.coprime_dvd_right (Subgroup.card_dvd_of_le hXR)
  letI : IsSolvable X :=
    isSolvable_of_injective (Subgroup.inclusion hXR)
      (Subgroup.inclusion_injective hXR)
  have hmapCentR :
      (centralizerWithin K R).map q = centralizerWithin Kq Rq := by
    simpa [q, Kq, Rq] using
      (map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
        (N := N) (Y := K) (R := R) hNK hcopNR)
  have hmapCentX :
      (centralizerWithin K X).map q = centralizerWithin Kq Xq := by
    simpa [q, Kq, Xq] using
      (map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
        (N := N) (Y := K) (R := X) hNK hcopNX)
  have hmapCommX : ⁅K, X⁆.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    simpa [q, QuotientGroup.ker_mk'] using hcommX
  have hcommXq : ⁅Kq, Xq⁆ = ⊥ := by
    rw [← Subgroup.map_commutator]
    exact hmapCommX
  have hcentXq : centralizerWithin Kq Xq = Kq := by
    apply le_antisymm (centralizerWithin_le_left Kq Xq)
    exact le_inf le_rfl
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommXq)
  have hcentRq : centralizerWithin Kq Rq = Kq := by
    calc
      centralizerWithin Kq Rq =
          (centralizerWithin K R).map q := hmapCentR.symm
      _ = (centralizerWithin K X).map q := by rw [hcent]
      _ = centralizerWithin Kq Xq := hmapCentX
      _ = Kq := hcentXq
  have hcommRq : ⁅Kq, Rq⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro k hk
    have hk' : k ∈ centralizerWithin Kq Rq := by
      rw [hcentRq]
      exact hk
    exact hk'.2
  have hmapCommR : ⁅K, R⁆.map q = ⊥ := by
    rw [Subgroup.map_commutator]
    exact hcommRq
  have hleKer : ⁅K, R⁆ ≤ q.ker :=
    (Subgroup.map_eq_bot_iff ⁅K, R⁆).mp hmapCommR
  simpa [q, QuotientGroup.ker_mk'] using hleKer

/-- The Fitting core is invariant under a group equivalence. -/
private theorem map_fittingCore_mulEquiv
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) :
    (fittingCore A).map e.toMonoidHom = fittingCore B := by
  rw [fittingCore, fittingCore, Subgroup.map_iSup]
  apply iSup_congr
  intro p
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  have hker : IsPGroup (p : ℕ) e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    exact IsPGroup.of_bot
  exact map_pCore_eq_of_surjective_of_ker_isPGroup
    e.toMonoidHom e.surjective hker

/-- Mapping the Fitting subgroup of a restricted subgroup back to the
original ambient type recovers the original Fitting subgroup. -/
private theorem map_fittingWithin_subgroupOf_eq
    {G : Type u} [Group G] [Finite G] {K J : Subgroup G}
    (hKJ : K ≤ J) :
    (fittingWithin (K.subgroupOf J)).map J.subtype = fittingWithin K := by
  let e : K.subgroupOf J ≃* K := Subgroup.subgroupOfEquivOfLe hKJ
  have hfit :
      (fittingCore (K.subgroupOf J)).map e.toMonoidHom = fittingCore K :=
    map_fittingCore_mulEquiv e
  change
    ((fittingCore (K.subgroupOf J)).map (K.subgroupOf J).subtype).map
        J.subtype =
      (fittingCore K).map K.subtype
  rw [← hfit, Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f : K.subgroupOf J →* G ↦
    (fittingCore (K.subgroupOf J)).map f)
  ext x
  rfl

/-- Centralizers commute with restricting both factors to an intermediate
ambient subgroup. -/
private theorem map_centralizerWithin_subgroupOf_eq
    {G : Type u} [Group G] {K R J : Subgroup G}
    (hKJ : K ≤ J) (hRJ : R ≤ J) :
    (centralizerWithin (K.subgroupOf J) (R.subgroupOf J)).map J.subtype =
      centralizerWithin K R := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨hx.1, ?_⟩
    intro r hr
    let rJ : J := ⟨r, hRJ hr⟩
    have hrJ : rJ ∈ R.subgroupOf J := hr
    exact congrArg Subtype.val (hx.2 rJ hrJ)
  · intro x hx
    let xJ : J := ⟨x, hKJ hx.1⟩
    have hxJ : xJ ∈ centralizerWithin
        (K.subgroupOf J) (R.subgroupOf J) := by
      refine ⟨hx.1, ?_⟩
      intro r hr
      apply Subtype.ext
      exact hx.2 (r : G) hr
    exact ⟨xJ, hxJ, rfl⟩

/-- A raw semiprime action restricts to an intermediate ambient subgroup. -/
private theorem semiprimeAction_subgroupOf
    {G : Type u} [Group G] {K R J : Subgroup G}
    (hKJ : K ≤ J) (hRJ : R ≤ J)
    (hprime : IsSemiprimeAction K R) :
    IsSemiprimeAction (K.subgroupOf J) (R.subgroupOf J) := by
  intro X hXR hX
  let XG : Subgroup G := X.map J.subtype
  have hXGR : XG ≤ R := by
    intro x hx
    rcases hx with ⟨xJ, hxJ, rfl⟩
    exact hXR hxJ
  have hXGne : XG ≠ ⊥ := by
    intro hbot
    apply hX
    apply le_bot_iff.mp
    intro x hx
    have hxmap : ((x : J) : G) ∈ XG :=
      Subgroup.mem_map_of_mem J.subtype hx
    rw [hbot] at hxmap
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (Subgroup.mem_bot.mp hxmap))
  refine (Subgroup.map_injective J.subtype_injective) ?_
  calc
    (centralizerWithin (K.subgroupOf J) X).map J.subtype =
        centralizerWithin K XG := by
      have hXJ : XG ≤ J := Subgroup.map_subtype_le X
      have hXeq : XG.subgroupOf J = X := by
        change (X.map J.subtype).comap J.subtype = X
        exact Subgroup.comap_map_eq_self_of_injective
          J.subtype_injective X
      rw [← hXeq]
      exact map_centralizerWithin_subgroupOf_eq hKJ hXJ
    _ = centralizerWithin K R := hprime XG hXGR hXGne
    _ = (centralizerWithin (K.subgroupOf J)
          (R.subgroupOf J)).map J.subtype :=
      (map_centralizerWithin_subgroupOf_eq hKJ hRJ).symm

/-- The source lemma `Fitting_stab_chief`, repeated locally because the
existing Section 3 proof keeps its copy private. -/
private theorem fittingCore_stabilizes_chiefFactor_3_8
    {G : Type u} [Group G] [Finite G]
    {V U : Subgroup G} [V.Normal]
    (hchief : IsChiefFactor V U)
    (hUF : U ≤ fittingCore G) :
    ⁅fittingCore G, U⁆ ≤ V := by
  classical
  let F : Subgroup G := fittingCore G
  let q : G →* G ⧸ V := QuotientGroup.mk' V
  let Fq : Subgroup (G ⧸ V) := F.map q
  let Uq : Subgroup (G ⧸ V) := U.map q
  have hUqFq : Uq ≤ Fq := Subgroup.map_mono hUF
  let VF : Subgroup F := V.subgroupOf F
  letI : VF.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : V.Normal) F
  letI : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  let eF : (F ⧸ VF) ≃* Fq :=
    QuotientGroup.liftEquiv VF (q.subgroupMap_surjective F) (by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])
  have hFqnil : Group.IsNilpotent Fq :=
    Group.nilpotent_of_mulEquiv eF
  letI : Group.IsNilpotent Fq := hFqnil
  letI : Fq.Normal :=
    Subgroup.Normal.map (inferInstance : F.Normal) q
      (QuotientGroup.mk'_surjective V)
  letI : Uq.Normal :=
    Subgroup.Normal.map hchief.upper_normal q
      (QuotientGroup.mk'_surjective V)
  let UF : Subgroup Fq := Uq.subgroupOf Fq
  letI : UF.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : Uq.Normal) Fq
  have hUFne : UF ≠ ⊥ := by
    intro hbot
    apply hchief.quotient_minimal_normal.ne_bot
    have hmapped := congrArg (fun S : Subgroup Fq ↦ S.map Fq.subtype) hbot
    simpa [UF, Subgroup.map_subgroupOf_eq_of_le hUqFq] using hmapped
  let Zq : Subgroup (G ⧸ V) :=
    (Subgroup.center Fq).map Fq.subtype
  have hZqnormal : Zq.Normal := by
    constructor
    intro z hz g
    exact characteristic_map_subtype_invariant_under_normalizer
      Fq ⊤ (Subgroup.center Fq) (by rw [Fq.normalizer_eq_top])
      g trivial z hz
  letI : Zq.Normal := hZqnormal
  let C : Subgroup (G ⧸ V) := Uq ⊓ Zq
  letI : C.Normal := by
    dsimp [C]
    infer_instance
  let M : Subgroup Fq := UF ⊓ Subgroup.center Fq
  have hMne : M ≠ ⊥ := by
    dsimp [M]
    exact nilpotent_normal_inf_center_ne_bot UF hUFne
  have hmapM : M.map Fq.subtype = C := by
    dsimp [M, C, Zq, UF]
    rw [Subgroup.map_inf _ _ _ Fq.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hUqFq]
  have hCne : C ≠ ⊥ := by
    rw [← hmapM]
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      M Fq.subtype_injective)).mpr hMne
  have hCU : C = Uq :=
    hchief.quotient_minimal_normal.eq_of_normal_le
      (inferInstance : C.Normal) inf_le_left hCne
  have hUqZ : Uq ≤ Zq := by
    rw [← hCU]
    exact inf_le_right
  have hcentral : Fq ≤
      Subgroup.centralizer (Uq : Set (G ⧸ V)) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨zF, hzF, rfl⟩ := hUqZ hz
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzF ⟨f, hf⟩)).symm
  have hcommq : ⁅Fq, Uq⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
  have hmap : ⁅F, U⁆.map q = ⊥ := by
    rw [Subgroup.map_commutator]
    exact hcommq
  have hker : ⁅F, U⁆ ≤ q.ker :=
    (Subgroup.map_eq_bot_iff ⁅F, U⁆).mp hmap
  simpa [F, q, QuotientGroup.ker_mk'] using hker

/-- A nilpotent ambient-normal subgroup centralizes every ambient chief
factor lying below it.  This is the form of `Fitting_stab_chief` needed for
the Fitting subgroup of a normal factor. -/
private theorem nilpotent_normal_stabilizes_chiefFactor_3_8
    {G : Type u} [Group G] [Finite G]
    {F V U : Subgroup G} [F.Normal] [V.Normal]
    (hFnil : Group.IsNilpotent F)
    (hchief : IsChiefFactor V U)
    (hUF : U ≤ F) :
    ⁅F, U⁆ ≤ V := by
  classical
  let q : G →* G ⧸ V := QuotientGroup.mk' V
  let Fq : Subgroup (G ⧸ V) := F.map q
  let Uq : Subgroup (G ⧸ V) := U.map q
  have hUqFq : Uq ≤ Fq := Subgroup.map_mono hUF
  let VF : Subgroup F := V.subgroupOf F
  letI : VF.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : V.Normal) F
  letI : Group.IsNilpotent F := hFnil
  let eF : (F ⧸ VF) ≃* Fq :=
    QuotientGroup.liftEquiv VF (q.subgroupMap_surjective F) (by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])
  have hFqnil : Group.IsNilpotent Fq :=
    Group.nilpotent_of_mulEquiv eF
  letI : Group.IsNilpotent Fq := hFqnil
  letI : Fq.Normal :=
    Subgroup.Normal.map (inferInstance : F.Normal) q
      (QuotientGroup.mk'_surjective V)
  letI : Uq.Normal :=
    Subgroup.Normal.map hchief.upper_normal q
      (QuotientGroup.mk'_surjective V)
  let UF : Subgroup Fq := Uq.subgroupOf Fq
  letI : UF.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : Uq.Normal) Fq
  have hUFne : UF ≠ ⊥ := by
    intro hbot
    apply hchief.quotient_minimal_normal.ne_bot
    have hmapped := congrArg (fun S : Subgroup Fq ↦ S.map Fq.subtype) hbot
    simpa [UF, Subgroup.map_subgroupOf_eq_of_le hUqFq] using hmapped
  let Zq : Subgroup (G ⧸ V) :=
    (Subgroup.center Fq).map Fq.subtype
  have hZqnormal : Zq.Normal := by
    constructor
    intro z hz g
    exact characteristic_map_subtype_invariant_under_normalizer
      Fq ⊤ (Subgroup.center Fq) (by rw [Fq.normalizer_eq_top])
      g trivial z hz
  letI : Zq.Normal := hZqnormal
  let C : Subgroup (G ⧸ V) := Uq ⊓ Zq
  letI : C.Normal := by
    dsimp [C]
    infer_instance
  let M : Subgroup Fq := UF ⊓ Subgroup.center Fq
  have hMne : M ≠ ⊥ := by
    dsimp [M]
    exact nilpotent_normal_inf_center_ne_bot UF hUFne
  have hmapM : M.map Fq.subtype = C := by
    dsimp [M, C, Zq, UF]
    rw [Subgroup.map_inf _ _ _ Fq.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hUqFq]
  have hCne : C ≠ ⊥ := by
    rw [← hmapM]
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      M Fq.subtype_injective)).mpr hMne
  have hCU : C = Uq :=
    hchief.quotient_minimal_normal.eq_of_normal_le
      (inferInstance : C.Normal) inf_le_left hCne
  have hUqZ : Uq ≤ Zq := by
    rw [← hCU]
    exact inf_le_right
  have hcentral : Fq ≤
      Subgroup.centralizer (Uq : Set (G ⧸ V)) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨zF, hzF, rfl⟩ := hUqZ hz
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzF ⟨f, hf⟩)).symm
  have hcommq : ⁅Fq, Uq⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
  have hmap : ⁅F, U⁆.map q = ⊥ := by
    rw [Subgroup.map_commutator]
    exact hcommq
  have hker : ⁅F, U⁆ ≤ q.ker :=
    (Subgroup.map_eq_bot_iff ⁅F, U⁆).mp hmap
  simpa [q, QuotientGroup.ker_mk'] using hker

/-- Every nontrivial ambient-normal subgroup occurs as the upper term of an
ambient chief factor. -/
private theorem exists_ambient_chiefFactor_eq_upper_3_8
    {G : Type u} [Group G] [Finite G] {U : Subgroup G}
    (hUnormal : U.Normal) (hU : U ≠ ⊥) :
    ∃ (V : Subgroup G) (hVnormal : V.Normal),
      @IsChiefFactor G _ V U hVnormal := by
  let Good : Subgroup G → Prop := fun V ↦ V.Normal ∧ V < U
  have hbot : Good (⊥ : Subgroup G) :=
    ⟨by infer_instance, bot_lt_iff_ne_bot.mpr hU⟩
  obtain ⟨V, _hbotV, hVgood, hVmax⟩ :=
    Finite.exists_le_maximal (p := Good) hbot
  letI : V.Normal := hVgood.1
  let q : G →* G ⧸ V := QuotientGroup.mk' V
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective V
  refine ⟨V, hVgood.1, hVgood.2.le, hUnormal, ?_⟩
  refine ⟨?_, Subgroup.Normal.map hUnormal q hqsurj, ?_⟩
  · intro hmap
    have hUV : U ≤ V := by
      have hker : U ≤ q.ker := (Subgroup.map_eq_bot_iff U).mp hmap
      simpa [q, QuotientGroup.ker_mk'] using hker
    exact (not_le_of_gt hVgood.2) hUV
  · intro N hNnormal hNU hN
    let W : Subgroup G := N.comap q
    have hWnormal : W.Normal := by
      dsimp [W]
      exact Subgroup.Normal.comap hNnormal q
    have hVW : V ≤ W := by
      dsimp [W, q]
      exact QuotientGroup.le_comap_mk' V N
    have hWU : W ≤ U := by
      have hkerU : q.ker ≤ U := by
        simpa [q, QuotientGroup.ker_mk'] using hVgood.2.le
      calc
        W ≤ (U.map q).comap q := Subgroup.comap_mono hNU
        _ = U := Subgroup.comap_map_eq_self hkerU
    by_contra hUN
    have hnUW : ¬ U ≤ W := by
      intro hUW
      apply hUN
      exact Subgroup.map_le_iff_le_comap.mpr hUW
    have hWltU : W < U :=
      lt_of_le_of_ne hWU (fun hWUeq ↦ hnUW hWUeq.ge)
    have hWV : W ≤ V := hVmax ⟨hWnormal, hWltU⟩ hVW
    have hWVeq : W = V := le_antisymm hWV hVW
    apply hN
    calc
      N = W.map q :=
        (Subgroup.map_comap_eq_self_of_surjective hqsurj N).symm
      _ = V.map q := congrArg (fun X : Subgroup G ↦ X.map q) hWVeq
      _ = ⊥ := QuotientGroup.map_mk'_self V

/-- The top of a solvable chief factor has derived subgroup in the lower
term. -/
private theorem commutator_le_lower_of_ambient_chiefFactor_3_8
    {G : Type u} [Group G] [IsSolvable G]
    {V U : Subgroup G} [V.Normal]
    (hchief : IsChiefFactor V U) : ⁅U, U⁆ ≤ V := by
  let q : G →* G ⧸ V := QuotientGroup.mk' V
  let M : Subgroup (G ⧸ V) := U.map q
  have hMcomm : IsMulCommutative M :=
    hchief.quotient_minimal_normal.isMulCommutative
  have hMM : ⁅M, M⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hMcomm
  have hmap : ⁅U, U⁆.map q = ⊥ := by
    rw [Subgroup.map_commutator]
    exact hMM
  have hker : ⁅U, U⁆ ≤ q.ker :=
    (Subgroup.map_eq_bot_iff ⁅U, U⁆).mp hmap
  simpa [q, QuotientGroup.ker_mk'] using hker

/-- Strict lower-central descent under the ambient chief-factor
stabilizer hypothesis. -/
private theorem commutator_lt_of_stabilizes_ambient_chiefFactors_3_8
    {G : Type u} [Group G] [Finite G]
    {F H L U : Subgroup G}
    (hLH : L ≤ H) (hU : U.Normal) (hUne : U ≠ ⊥)
    (hUF : U ≤ F)
    (hstab :
      ∀ (V W : Subgroup G) [V.Normal],
        IsChiefFactor V W → W ≤ F → ⁅H, W⁆ ≤ V) :
    ⁅U, L⁆ < U := by
  obtain ⟨V, hVnormal, hchief⟩ :=
    exists_ambient_chiefFactor_eq_upper_3_8 hU hUne
  letI : V.Normal := hVnormal
  have hUL : ⁅U, L⁆ ≤ ⁅U, H⁆ :=
    Subgroup.commutator_mono le_rfl hLH
  have hUH : ⁅U, H⁆ ≤ ⁅H, U⁆ :=
    Subgroup.commutator_comm_le U H
  exact lt_of_le_of_lt
    (hUL.trans (hUH.trans (hstab V U hchief hUF))) hchief.lt

/-- The normal-subgroup form of `BGsection1.chief_stab_sub_Fitting` used by
Theorem 3.8.  Ambient chief factors are essential: the complement need not
normalize every chief factor of `K` considered merely as an abstract group. -/
private theorem normal_le_fittingWithin_of_stabilizes_ambient_chiefFactors
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {K H : Subgroup G} (hKnormal : K.Normal) (hHnormal : H.Normal)
    (hHK : H ≤ K)
    (hstab :
      ∀ (V U : Subgroup G) [V.Normal],
        IsChiefFactor V U →
        U ≤ fittingWithin K →
        ⁅H, U⁆ ≤ V) :
    H ≤ fittingWithin K := by
  by_contra hHF
  let F : Subgroup G := fittingWithin K
  let Bad : Subgroup G → Prop := fun L ↦
    L.Normal ∧ L ≤ H ∧ ¬ L ≤ F
  have hHbad : Bad H := ⟨hHnormal, le_rfl, hHF⟩
  obtain ⟨L, _hLH, hLmin⟩ := Finite.exists_le_minimal hHbad
  have hLnormal : L.Normal := hLmin.1.1
  have hLH : L ≤ H := hLmin.1.2.1
  have hLF : ¬ L ≤ F := hLmin.1.2.2
  have hLne : L ≠ ⊥ := by
    intro hL
    apply hLF
    rw [hL]
    exact bot_le
  obtain ⟨V, hVnormal, hchief⟩ :=
    exists_ambient_chiefFactor_eq_upper_3_8 hLnormal hLne
  letI : V.Normal := hVnormal
  have hVF : V ≤ F := by
    by_contra hVF
    have hVbad : Bad V :=
      ⟨by infer_instance, hchief.le.trans hLH, hVF⟩
    have hLV : L ≤ V := hLmin.eq_of_ge hVbad hchief.le |>.le
    exact (not_le_of_gt hchief.lt) hLV
  have hderived : ⁅L, L⁆ ≤ V :=
    commutator_le_lower_of_ambient_chiefFactor_3_8 hchief
  have hseriesOne : L.lowerCentralSeries 1 ≤ V := by
    simpa [Subgroup.lowerCentralSeries_succ] using hderived
  have hseriesF : ∀ n : ℕ, L.lowerCentralSeries (n + 1) ≤ F := by
    intro n
    exact
      (L.lowerCentralSeries_antitone
        (Nat.succ_le_succ (Nat.zero_le n))).trans
      (hseriesOne.trans hVF)
  have hseriesTerminates : ∃ n : ℕ, L.lowerCentralSeries n = ⊥ := by
    by_contra hnone
    have hnonzero : ∀ n : ℕ, L.lowerCentralSeries n ≠ ⊥ := by
      intro n hn
      exact hnone ⟨n, hn⟩
    let S : ℕ → Subgroup G := fun n ↦ L.lowerCentralSeries (n + 1)
    have hSstrict : ∀ n : ℕ, S (n + 1) < S n := by
      intro n
      have hnormal : (S n).Normal := by
        dsimp [S]
        exact Subgroup.lowerCentralSeries_normal L (n + 1)
      have hne : S n ≠ ⊥ := hnonzero (n + 1)
      have hdesc :=
        commutator_lt_of_stabilizes_ambient_chiefFactors_3_8
          (F := F) (H := H) (L := L) hLH hnormal hne
          (hseriesF n) (by simpa [F] using hstab)
      simpa [S, Subgroup.lowerCentralSeries_succ, Nat.add_assoc] using hdesc
    have hinj : Function.Injective S :=
      (strictAnti_nat_of_succ_lt hSstrict).injective
    exact (Finite.of_injective S hinj).false
  have hLnil : Group.IsNilpotent L :=
    (Subgroup.isNilpotent_iff_lowerCentralSeries L).mpr hseriesTerminates
  have hLK : L ≤ K := hLH.trans hHK
  let LK : Subgroup K := L.subgroupOf K
  have hLKnormal : LK.Normal := by
    dsimp [LK]
    exact Subgroup.Normal.subgroupOf hLnormal K
  have hLKnil : Group.IsNilpotent LK := by
    letI : Group.IsNilpotent L := hLnil
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLK).symm
  have hLKfit : LK ≤ fittingCore K :=
    nilpotent_normal_le_fittingCore hLKnormal hLKnil
  apply hLF
  intro x hx
  let xK : K := ⟨x, hLK hx⟩
  exact ⟨xK, hLKfit hx, rfl⟩

/-- A subgroup acts trivially on a chief factor exactly when its mixed
commutator with the upper term lies in the lower term. -/
private theorem subgroup_le_ker_chiefFactorConjugationHom_iff_3_8
    {G : Type u} [Group G]
    {V U A : Subgroup G} [V.Normal]
    (hchief : IsChiefFactor V U) :
    A ≤ (chiefFactorConjugationHom hchief).ker ↔ ⁅A, U⁆ ≤ V := by
  letI : U.Normal := hchief.upper_normal
  constructor
  · intro hker
    apply Subgroup.commutator_le.mpr
    intro a ha x hx
    have ha' : (⟨a, trivial⟩ : (⊤ : Subgroup G)) ∈
        (subgroupConjugationFactorHom V U ⊤
          Subgroup.le_normalizer_of_normal
          Subgroup.le_normalizer_of_normal).ker := by
      simpa [chiefFactorConjugationHom] using hker ha
    exact (mem_ker_subgroupConjugationFactorHom_iff V U ⊤
      Subgroup.le_normalizer_of_normal
      Subgroup.le_normalizer_of_normal ⟨a, trivial⟩).mp ha' x hx
  · intro hcomm a ha
    have ha' : (⟨a, trivial⟩ : (⊤ : Subgroup G)) ∈
        (subgroupConjugationFactorHom V U ⊤
          Subgroup.le_normalizer_of_normal
          Subgroup.le_normalizer_of_normal).ker := by
      apply (mem_ker_subgroupConjugationFactorHom_iff V U ⊤
        Subgroup.le_normalizer_of_normal
        Subgroup.le_normalizer_of_normal ⟨a, trivial⟩).mpr
      intro x hx
      exact Subgroup.commutator_le.mp hcomm a ha x hx
    simpa [chiefFactorConjugationHom] using ha'

/-- Reduce the semiprime actor to one subgroup of prime order. -/
private theorem commutator_le_fittingWithin_of_prime_actor_cases_3_8
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {K R : Subgroup G} [K.Normal]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hprime : IsSemiprimeAction K R)
    (primeActor :
      ∀ X : Subgroup G, X ≤ R → (Nat.card X).Prime →
        centralizerWithin (fittingWithin K) X = ⊥ →
        ⁅K, X⁆ ≤ fittingWithin K)
    (hreg : centralizerWithin (fittingWithin K) R = ⊥) :
    ⁅K, R⁆ ≤ fittingWithin K := by
  classical
  by_cases hR : R = ⊥
  · subst R
    simpa only [Subgroup.commutator_bot_right] using
      (bot_le : (⊥ : Subgroup G) ≤ fittingWithin K)
  have hRcard : Nat.card R ≠ 1 :=
    (R.one_lt_card_iff_ne_bot.mpr hR).ne'
  obtain ⟨r, hr, hrR⟩ := Nat.exists_prime_and_dvd hRcard
  letI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := R) r hrR
  let X : Subgroup G := (Subgroup.zpowers x).map R.subtype
  have hXR : X ≤ R := by
    dsimp only [X]
    exact Subgroup.map_subtype_le _
  have hXcard : Nat.card X = r := by
    dsimp only [X]
    rw [Subgroup.card_map_of_injective R.subtype_injective,
      Nat.card_zpowers, hx]
  have hXprime : (Nat.card X).Prime := by
    rw [hXcard]
    exact hr
  have hXne : X ≠ ⊥ := by
    rw [← X.one_lt_card_iff_ne_bot, hXcard]
    exact hr.one_lt
  have hcentXK : centralizerWithin K X = centralizerWithin K R :=
    hprime.centralizer_eq hXR hXne
  have hcentXF :
      centralizerWithin (fittingWithin K) X =
        centralizerWithin (fittingWithin K) R :=
    hprime.mono_left (fittingWithin_le K) |>.centralizer_eq hXR hXne
  have hregX : centralizerWithin (fittingWithin K) X = ⊥ := by
    rw [hcentXF, hreg]
  have hcommX : ⁅K, X⁆ ≤ fittingWithin K :=
    primeActor X hXR hXprime hregX
  have hGnormK :
      (⊤ : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [K.normalizer_eq_top]
  have hGnormF :
      (⊤ : Subgroup G) ≤
        Subgroup.normalizer (fittingWithin K : Set G) :=
    le_normalizer_fittingWithin_of_le_normalizer hGnormK
  have hFnormal : (fittingWithin K).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_unique hGnormF)
  letI : (fittingWithin K).Normal := hFnormal
  exact commutator_le_of_actor_subgroup
    (N := fittingWithin K) (K := K) (R := R) (X := X)
    (fittingWithin_le K) hXR hcop hcentXK hcommX

/-- The cross-characteristic chief-factor calculation in Theorem 3.8. -/
private theorem crossPrime_chief_stabilized_3_8
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {K R P V U : Subgroup G} [K.Normal] [V.Normal]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hKR : K.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hRprime : (Nat.card R).Prime)
    (hreg : centralizerWithin (fittingWithin K) R = ⊥)
    (hPK : P ≤ K)
    (hPp : IsPGroup p P)
    (hRnormP : R ≤ Subgroup.normalizer (P : Set G))
    (hKPF : K ≤ P ⊔ fittingWithin K)
    (hchief : IsChiefFactor V U)
    (hUF : U ≤ fittingWithin K)
    (hWq : IsPGroup q (U.map (QuotientGroup.mk' V)))
    (hWpow : ∀ x : U.map (QuotientGroup.mk' V), x ^ q = 1)
    (hqp : q ≠ p) :
    ⁅⁅K, R⁆, U⁆ ≤ V := by
  classical
  let qV : G →* G ⧸ V := QuotientGroup.mk' V
  let Kq : Subgroup (G ⧸ V) := K.map qV
  let Rq : Subgroup (G ⧸ V) := R.map qV
  let Pq : Subgroup (G ⧸ V) := P.map qV
  let W : Subgroup (G ⧸ V) := U.map qV
  let C : Subgroup (G ⧸ V) :=
    Subgroup.centralizer (W : Set (G ⧸ V))
  let F : Subgroup G := fittingWithin K
  have hUK : U ≤ K := hUF.trans (fittingWithin_le K)
  have hVK : V ≤ K := hchief.le.trans hUK
  have hPKq : Pq ≤ Kq := Subgroup.map_mono hPK
  have hRqnormPq : Rq ≤ Subgroup.normalizer (Pq : Set (G ⧸ V)) :=
    (Subgroup.map_mono hRnormP).trans (Subgroup.le_normalizer_map qV)
  letI : IsSolvable (G ⧸ V) :=
    isSolvable_quotient_of_isSolvable V
  letI : IsSolvable R := isSolvable_subgroup_of_isSolvable R
  letI : Kq.Normal :=
    Subgroup.Normal.map (inferInstance : K.Normal) qV
      (QuotientGroup.mk'_surjective V)
  letI : W.Normal := by
    dsimp only [W]
    exact Subgroup.Normal.map hchief.upper_normal qV
      (QuotientGroup.mk'_surjective V)
  letI : C.Normal := by
    dsimp only [C]
    infer_instance
  have hGnormK :
      (⊤ : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [K.normalizer_eq_top]
  have hGnormF :
      (⊤ : Subgroup G) ≤ Subgroup.normalizer (F : Set G) :=
    le_normalizer_fittingWithin_of_le_normalizer hGnormK
  have hFnormal : F.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_unique hGnormF)
  letI : F.Normal := hFnormal
  have hFnil : Group.IsNilpotent F := by
    dsimp only [F]
    infer_instance
  have hFstab : ⁅F, U⁆ ≤ V :=
    nilpotent_normal_stabilizes_chiefFactor_3_8 hFnil hchief hUF
  have hFqC : F.map qV ≤ C := by
    have hbot : ⁅F.map qV, W⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
      simpa only [qV, QuotientGroup.ker_mk'] using hFstab
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hKqDecomp : Kq ≤ Pq ⊔ C := by
    have hmapped : Kq ≤ Pq ⊔ F.map qV := by
      dsimp only [Kq, Pq]
      rw [← Subgroup.map_sup]
      exact Subgroup.map_mono hKPF
    exact hmapped.trans (sup_le_sup le_rfl hFqC)
  have hcentUR : centralizerWithin U R = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxF : x ∈ centralizerWithin (fittingWithin K) R :=
      ⟨hUF hx.1, hx.2⟩
    rw [hreg] at hxF
    exact hxF
  have hcopVR : Nat.Coprime (Nat.card V) (Nat.card R) :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hVK)
  have hcentWRq : centralizerWithin W Rq = ⊥ := by
    have hm :=
      map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
        (N := V) (Y := U) (R := R) hchief.le hcopVR
    calc
      centralizerWithin W Rq =
          (centralizerWithin U R).map qV := by
        simpa only [W, Rq, qV] using hm.symm
      _ = ⊥ := by rw [hcentUR, Subgroup.map_bot]
  have hKRq : Kq.IsComplement' Rq := by
    simpa only [Kq, Rq, qV] using hKR.quotient_isComplement hVK
  let J : Subgroup (G ⧸ V) := Rq ⊔ Pq
  have hPJ : Pq ≤ J := le_sup_right
  have hRJ : Rq ≤ J := le_sup_left
  letI : (Pq.subgroupOf J).Normal := by
    dsimp only [J]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hRqnormPq
  have hcompJ :
      (Pq.subgroupOf J).IsComplement' (Rq.subgroupOf J) := by
    simpa only [J] using
      properKernel_subgroupOf_isComplement hKRq hPKq hRqnormPq
  have hPqRqCop : Nat.Coprime (Nat.card Pq) (Nat.card Rq) := by
    apply (hcop.coprime_dvd_left ?_).coprime_dvd_right
      (Subgroup.card_map_dvd R qV)
    exact (Subgroup.card_map_dvd P qV).trans
      (Subgroup.card_dvd_of_le hPK)
  letI : IsSolvable J := isSolvable_subgroup_of_isSolvable J
  have hoddJ : Odd (Nat.card J) :=
    odd_natCard_subgroup J (odd_natCard_quotient V hodd)
  have hcardRq : Nat.card Rq = Nat.card R := by
    let fR : R → Rq := qV.subgroupMap R
    exact (Nat.card_congr (Equiv.ofBijective fR
      ⟨hKR.quotientRight_subgroupMap_injective hVK,
        qV.subgroupMap_surjective R⟩)).symm
  have hRqPrime : (Nat.card Rq).Prime := by
    rw [hcardRq]
    exact hRprime
  have hWelem : IsElementaryAbelianGroup q W := by
    refine
      { isPGroup := by simpa only [W, qV] using hWq
        commutative := by
          simpa only [W, qV] using
            hchief.quotient_minimal_normal.isMulCommutative
        pow_eq_one := by simpa only [W, qV] using hWpow }
  have hJnormW : J ≤ Subgroup.normalizer (W : Set (G ⧸ V)) := by
    rw [W.normalizer_eq_top]
    exact le_top
  have hPqp : IsPGroup p Pq := hPp.map qV
  have hqPq : Nat.Coprime q (Nat.card Pq) := by
    obtain ⟨n, hn⟩ := hPqp.exists_card_eq
    rw [hn]
    exact ((Nat.coprime_primes
      (Fact.out : q.Prime) (Fact.out : p.Prime)).mpr hqp).pow_right n
  have hWne : W ≠ ⊥ := by
    simpa only [W, qV] using hchief.quotient_minimal_normal.ne_bot
  have hqW : q ∣ Nat.card W :=
    (show IsPGroup q W from hWelem.isPGroup).card_eq_or_dvd.resolve_left
      (fun hcard ↦ hWne (Subgroup.card_eq_one.mp hcard))
  have hqK : q ∣ Nat.card K :=
    hqW.trans ((Subgroup.card_map_dvd U qV).trans
      (Subgroup.card_dvd_of_le hUK))
  have hqRq : Nat.Coprime q (Nat.card Rq) :=
    (hcop.coprime_dvd_left hqK).coprime_dvd_right
      (Subgroup.card_map_dvd R qV)
  have hcardPJ : Nat.card (Pq.subgroupOf J) = Nat.card Pq :=
    natCard_subgroupOf_eq hPJ
  have hcardRJ : Nat.card (Rq.subgroupOf J) = Nat.card Rq :=
    natCard_subgroupOf_eq hRJ
  have hqJ : Nat.Coprime q (Nat.card J) := by
    rw [← hcompJ.card_mul, hcardPJ, hcardRJ]
    exact hqPq.mul_right hqRq
  have hJcard : (Nat.card J : ZMod q) ≠ 0 := by
    letI : NeZero (Nat.card J : ZMod q) :=
      NeZero.of_not_dvd (ZMod q)
        ((Fact.out : q.Prime).coprime_iff_not_dvd.mp hqJ)
    exact NeZero.ne _
  have hRPcent : ⁅Rq, Pq⁆ ≤ centralizerWithin Pq W :=
    odd_prime_sdprod_abelem_cent1 J Pq Rq W
      hPJ hRJ hcompJ hPqRqCop hoddJ hRqPrime hWelem hJnormW
      hJcard hcentWRq
  have hRPC : ⁅Rq, Pq⁆ ≤ C := hRPcent.trans inf_le_right
  have hRCC : ⁅Rq, C⁆ ≤ C := Subgroup.commutator_le_right Rq C
  have hRqKqC : ⁅Rq, Kq⁆ ≤ C :=
    commutator_le_of_le_sup_of_normal hKqDecomp hRPC hRCC
  have hKqRqC : ⁅Kq, Rq⁆ ≤ C :=
    (Subgroup.commutator_comm_le Kq Rq).trans hRqKqC
  have hmapKRC : ⁅K, R⁆.map qV ≤ C := by
    rw [Subgroup.map_commutator]
    exact hKqRqC
  have hmapFinal : ⁅⁅K, R⁆, U⁆.map qV = ⊥ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hmapKRC
  have hker : ⁅⁅K, R⁆, U⁆ ≤ qV.ker :=
    (Subgroup.map_eq_bot_iff ⁅⁅K, R⁆, U⁆).mp hmapFinal
  simpa only [qV, QuotientGroup.ker_mk'] using hker

/-- In the equal-characteristic branch, the action of `K` on the chief
factor is a quotient of the `p`-group `K / F(K)`.  Faithfulness of the chief
factor action therefore kills that quotient. -/
private theorem samePrime_chief_stabilized_3_8
    {G : Type u} [Group G] [Finite G]
    {K V U : Subgroup G} [K.Normal] [V.Normal]
    {p : ℕ} [Fact p.Prime]
    (hchief : IsChiefFactor V U)
    (hUF : U ≤ fittingWithin K)
    (hKquot : IsPGroup p (K ⧸ fittingCore K))
    (hfactor : IsPGroup p (U.map (QuotientGroup.mk' V))) :
    ⁅K, U⁆ ≤ V := by
  classical
  let F : Subgroup G := fittingWithin K
  have hGnormK :
      (⊤ : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [K.normalizer_eq_top]
  have hGnormF :
      (⊤ : Subgroup G) ≤ Subgroup.normalizer (F : Set G) :=
    le_normalizer_fittingWithin_of_le_normalizer hGnormK
  have hFnormal : F.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_unique hGnormF)
  letI : F.Normal := hFnormal
  have hFnil : Group.IsNilpotent F := by
    dsimp only [F]
    infer_instance
  have hFstab : ⁅F, U⁆ ≤ V :=
    nilpotent_normal_stabilizes_chiefFactor_3_8 hFnil hchief hUF
  let a : G →* MulAut (U ⧸ V.subgroupOf U) :=
    chiefFactorConjugationHom hchief
  have hFa : F ≤ a.ker := by
    exact (subgroup_le_ker_chiefFactorConjugationHom_iff_3_8
      hchief).mpr hFstab
  let qF : G →* G ⧸ F := QuotientGroup.mk' F
  let KF : Subgroup (G ⧸ F) := K.map qF
  let eKF : (K ⧸ F.subgroupOf K) ≃* KF :=
    QuotientGroup.liftEquiv (F.subgroupOf K)
      (qF.subgroupMap_surjective K) (by
        rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])
  have hKquotF : IsPGroup p (K ⧸ F.subgroupOf K) := by
    exact hKquot.of_equiv
      (QuotientGroup.quotientMulEquivOfEq
        (fittingWithin_subgroupOf_eq K)).symm
  have hKFp : IsPGroup p KF :=
    hKquotF.of_equiv eKF
  let qa : G →* G ⧸ a.ker := QuotientGroup.mk' a.ker
  have hFqa : F ≤ qa.ker := by
    simpa only [qa, QuotientGroup.ker_mk'] using hFa
  let f : (G ⧸ F) →* (G ⧸ a.ker) :=
    QuotientGroup.lift F qa hFqa
  have hmapK : KF.map f = K.map qa := by
    dsimp only [KF, qF, f]
    rw [Subgroup.map_map]
    rfl
  have hKqaP : IsPGroup p (K.map qa) := by
    rw [← hmapK]
    exact hKFp.map f
  have hKqaNormal : (K.map qa).Normal :=
    Subgroup.Normal.map (inferInstance : K.Normal) qa
      (QuotientGroup.mk'_surjective a.ker)
  have hKqaCore : K.map qa ≤ pCore p (G ⧸ a.ker) :=
    le_pCore hKqaP hKqaNormal
  have hcoreBot : pCore p (G ⧸ a.ker) = ⊥ := by
    simpa only [a] using
      pCore_quotient_ker_chiefFactorConjugationHom_eq_bot
        hchief hfactor
  have hKmapBot : K.map qa = ⊥ :=
    le_bot_iff.mp (hKqaCore.trans_eq hcoreBot)
  have hKa : K ≤ a.ker := by
    have hle := (Subgroup.map_eq_bot_iff K).mp hKmapBot
    simpa only [qa, QuotientGroup.ker_mk'] using hle
  exact (subgroup_le_ker_chiefFactorConjugationHom_iff_3_8
    hchief).mp hKa

/-- The prime-order actor endpoint once `K / F(K)` is a `p`-group. -/
private theorem prime_actor_commutator_le_fitting_of_quotient_isPGroup_3_8
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {K R : Subgroup G} [K.Normal]
    {p : ℕ} [Fact p.Prime]
    (hKR : K.IsComplement' R)
    (hodd : Odd (Nat.card G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hRprime : (Nat.card R).Prime)
    (hreg : centralizerWithin (fittingWithin K) R = ⊥)
    (hKquot : IsPGroup p (K ⧸ fittingCore K)) :
    ⁅K, R⁆ ≤ fittingWithin K := by
  classical
  have hRnormK : R ≤ Subgroup.normalizer (K : Set G) :=
    complement_le_normalizer_of_normal (inferInstance : K.Normal)
  obtain ⟨Ps, hRnormP⟩ :=
    exists_sylow_normalized_by_prime_subgroup
      (G := G) (K := K) (R := R) (Fact.out : p.Prime)
      hRnormK hRprime hcop.symm
  let P : Subgroup G := (Ps : Subgroup K).map K.subtype
  let F : Subgroup G := fittingWithin K
  have hPK : P ≤ K := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := Ps.isPGroup'.map K.subtype
  have hRnormP' : R ≤ Subgroup.normalizer (P : Set G) := by
    simpa only [P] using hRnormP
  let qK : K →* K ⧸ fittingCore K :=
    QuotientGroup.mk' (fittingCore K)
  have hPmap : (Ps : Subgroup K).map qK = ⊤ :=
    Sylow.map_eq_top_of_surjective_of_isPGroup Ps qK
      (QuotientGroup.mk'_surjective (fittingCore K)) hKquot
  have hKPF : K ≤ P ⊔ F := by
    intro k hk
    let kK : K := ⟨k, hk⟩
    have hkq : qK kK ∈ (Ps : Subgroup K).map qK := by
      rw [hPmap]
      trivial
    obtain ⟨y, hyP, hyk⟩ := hkq
    obtain ⟨z, hzF, hyz⟩ :=
      (QuotientGroup.mk'_eq_mk' (fittingCore K)).mp hyk
    have hyPG : (y : G) ∈ P := ⟨y, hyP, rfl⟩
    have hzFG : (z : G) ∈ F := ⟨z, hzF, rfl⟩
    have hyzG : (y : G) * (z : G) = k :=
      congrArg Subtype.val hyz
    rw [← hyzG]
    exact Subgroup.mul_mem_sup hyPG hzFG
  let H : Subgroup G := ⁅K, R⁆
  have hHnormal : H.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [← hKR.sup_eq_top]
    exact sup_le (Subgroup.normalizer_commutator_ge_left K R)
      (Subgroup.normalizer_commutator_ge_right K R)
  apply normal_le_fittingWithin_of_stabilizes_ambient_chiefFactors
    (K := K) (H := H) (inferInstance : K.Normal) hHnormal
    (Subgroup.commutator_le_left K R)
  intro V U hVnormal hchief hUF
  letI : V.Normal := hVnormal
  obtain ⟨q, hq, hWq, hWpow⟩ :=
    hchief.exists_prime_isPGroup_pow_eq_one
  letI : Fact q.Prime := ⟨hq⟩
  rcases eq_or_ne q p with hqp | hqp
  · subst q
    have hKU : ⁅K, U⁆ ≤ V :=
      samePrime_chief_stabilized_3_8 hchief hUF hKquot hWq
    exact (Subgroup.commutator_mono
      (Subgroup.commutator_le_left K R) le_rfl).trans hKU
  · exact crossPrime_chief_stabilized_3_8
      hKR hcop hodd hRprime hreg hPK hPp hRnormP' hKPF
      hchief hUF hWq hWpow hqp

/-- The source equality `F(P) = F(K)` for the characteristic inverse image
used in the outer induction. -/
private theorem fittingWithin_eq_of_normal_between_3_8
    {G : Type u} [Group G] [Finite G]
    {P K : Subgroup G} [P.Normal] [K.Normal]
    (hPK : P ≤ K) (hFKP : fittingWithin K ≤ P) :
    fittingWithin P = fittingWithin K := by
  have hFPnormal : (fittingWithin P).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    exact le_normalizer_fittingWithin_of_le_normalizer (by
      rw [P.normalizer_eq_top])
  have hFKnormal : (fittingWithin K).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    exact le_normalizer_fittingWithin_of_le_normalizer (by
      rw [K.normalizer_eq_top])
  apply le_antisymm
  · let L : Subgroup K := (fittingWithin P).subgroupOf K
    have hLPK : fittingWithin P ≤ K := (fittingWithin_le P).trans hPK
    have hLnormal : L.Normal := by
      dsimp only [L]
      exact Subgroup.Normal.subgroupOf hFPnormal K
    have hLnil : Group.IsNilpotent L := by
      letI : Group.IsNilpotent (fittingWithin P) := by infer_instance
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hLPK).symm
    have hLfit : L ≤ fittingCore K :=
      nilpotent_normal_le_fittingCore hLnormal hLnil
    intro x hx
    let xK : K := ⟨x, hLPK hx⟩
    have hxL : xK ∈ L := hx
    exact ⟨xK, hLfit hxL, rfl⟩
  · let M : Subgroup P := (fittingWithin K).subgroupOf P
    have hMnormal : M.Normal := by
      dsimp only [M]
      exact Subgroup.Normal.subgroupOf hFKnormal P
    have hMnil : Group.IsNilpotent M := by
      letI : Group.IsNilpotent (fittingWithin K) := by infer_instance
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hFKP).symm
    have hMfit : M ≤ fittingCore P :=
      nilpotent_normal_le_fittingCore hMnormal hMnil
    intro x hx
    let xP : P := ⟨x, hFKP hx⟩
    have hxM : xP ∈ M := hx
    exact ⟨xP, hMfit hxM, rfl⟩

/-- The initial WLOG step in the source proof: if `K / F(K)` is not a
`p`-group, pull the prime cores of its Fitting subgroup back to proper
characteristic subgroups of `K` and apply the outer induction there. -/
private theorem odd_sdprod_primact_commg_sub_Fitting_reduce_to_pgroup_3_8
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {K R : Subgroup G} [K.Normal]
    (hKR : K.IsComplement' R)
    (hodd : Odd (Nat.card G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hprime : IsSemiprimeAction K R)
    (hreg : centralizerWithin (fittingWithin K) R = ⊥)
    (ih : ∀ (J : Subgroup G) (L T : Subgroup J),
      L.Normal →
      Nat.card J < Nat.card G →
      L.IsComplement' T →
      IsSolvable J →
      Odd (Nat.card J) →
      Nat.Coprime (Nat.card L) (Nat.card T) →
      IsSemiprimeAction L T →
      centralizerWithin (fittingWithin L) T = ⊥ →
      ⁅L, T⁆ ≤ fittingWithin L)
    (pGroupCase : ∀ p : ℕ, p.Prime →
      IsPGroup p (K ⧸ fittingCore K) →
      ⁅K, R⁆ ≤ fittingWithin K) :
    ⁅K, R⁆ ≤ fittingWithin K := by
  classical
  let F : Subgroup G := fittingWithin K
  have hGnormK :
      (⊤ : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [K.normalizer_eq_top]
  have hFnormal : F.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    exact le_normalizer_fittingWithin_of_le_normalizer hGnormK
  letI : F.Normal := hFnormal
  let qF : G →* G ⧸ F := QuotientGroup.mk' F
  let Kq : Subgroup (G ⧸ F) := K.map qF
  let Rq : Subgroup (G ⧸ F) := R.map qF
  letI : Kq.Normal :=
    Subgroup.Normal.map (inferInstance : K.Normal) qF
      (QuotientGroup.mk'_surjective F)
  let Q := K ⧸ fittingCore K
  let qK : K →* Q := QuotientGroup.mk' (fittingCore K)
  let e : Q ≃* Kq :=
    QuotientGroup.liftEquiv (fittingCore K)
      (by simpa only [Kq] using qF.subgroupMap_surjective K)
      (by
        rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
        exact (fittingWithin_subgroupOf_eq K).symm)
  by_cases hpGroup : ∃ p : ℕ, p.Prime ∧ IsPGroup p Q
  · obtain ⟨p, hp, hQp⟩ := hpGroup
    exact pGroupCase p hp hQp
  have hcopq : Nat.Coprime (Nat.card Kq) (Nat.card Rq) :=
    (hcop.coprime_dvd_left (Subgroup.card_map_dvd K qF)).coprime_dvd_right
      (Subgroup.card_map_dvd R qF)
  have hsolKq : IsSolvable Kq := by infer_instance
  have hFitCentRq :
      (fittingCore Kq).map Kq.subtype ≤
        Subgroup.centralizer (Rq : Set (G ⧸ F)) := by
    rw [fittingCore, Subgroup.map_iSup]
    apply iSup_le
    intro pp
    letI : Fact (pp : ℕ).Prime := ⟨pp.property⟩
    let C0 : Subgroup Q := pCore (pp : ℕ) Q
    let P0 : Subgroup K := C0.comap qK
    letI : P0.Characteristic := by
      dsimp only [P0]
      exact Subgroup.Characteristic.comap_quotient_mk
        (show C0.Characteristic by infer_instance)
    let P : Subgroup G := P0.map K.subtype
    letI : P.Normal := by
      dsimp only [P]
      infer_instance
    have hPK : P ≤ K := Subgroup.map_subtype_le P0
    have hFKP : F ≤ P := by
      dsimp only [F, P]
      exact Subgroup.map_mono
        (QuotientGroup.le_comap_mk' (fittingCore K) C0)
    have hP0neTop : P0 ≠ ⊤ := by
      intro hP0top
      apply hpGroup
      refine ⟨(pp : ℕ), pp.property, ?_⟩
      have hC0top : C0 = ⊤ := by
        calc
          C0 = P0.map qK :=
            (Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective (fittingCore K)) C0).symm
          _ = (⊤ : Subgroup K).map qK := by rw [hP0top]
          _ = ⊤ := Subgroup.map_top_of_surjective qK
            (QuotientGroup.mk'_surjective (fittingCore K))
      have htopP : IsPGroup (pp : ℕ) (⊤ : Subgroup Q) := by
        rw [← hC0top]
        exact pCore_isPGroup
      exact htopP.of_equiv Subgroup.topEquiv
    have hP0lt : P0 < ⊤ := lt_top_iff_ne_top.mpr hP0neTop
    have hPltK : P < K := by
      rw [← K.range_subtype, MonoidHom.range_eq_map]
      exact Subgroup.map_subtype_lt_map_subtype.mpr hP0lt
    have hRnormP : R ≤ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : P.Normal)]
      exact le_top
    let J : Subgroup G := R ⊔ P
    let PJ : Subgroup J := P.subgroupOf J
    let RJ : Subgroup J := R.subgroupOf J
    have hPJ : P ≤ J := le_sup_right
    have hRJ : R ≤ J := le_sup_left
    letI : PJ.Normal := by
      dsimp only [PJ]
      exact Subgroup.Normal.subgroupOf (inferInstance : P.Normal) J
    have hcompJ : PJ.IsComplement' RJ := by
      simpa only [J, PJ, RJ] using
        properKernel_subgroupOf_isComplement hKR hPltK.le hRnormP
    have hJlt : Nat.card J < Nat.card G := by
      simpa only [J] using
        natCard_sup_lt_of_properKernel hKR hPltK hRnormP
    have hsolJ : IsSolvable J := isSolvable_sup
    have hoddJ : Odd (Nat.card J) := by
      exact odd_natCard_subgroup J hodd
    have hcopJ : Nat.Coprime (Nat.card PJ) (Nat.card RJ) := by
      simpa only [J, PJ, RJ] using
        (natCard_coprime_subgroupOf_properKernel
          (K := K) (R := R) (H := P) hcop hPK)
    have hsemP : IsSemiprimeAction P R :=
      IsSemiprimeAction.mono_left hPK hprime
    have hsemJ : IsSemiprimeAction PJ RJ :=
      semiprimeAction_subgroupOf hPJ hRJ hsemP
    have hfitPK : fittingWithin P = F := by
      simpa only [F] using
        (fittingWithin_eq_of_normal_between_3_8
          (P := P) (K := K) hPK hFKP)
    have hfitPJ : fittingWithin PJ = (fittingWithin P).subgroupOf J := by
      apply Subgroup.map_injective J.subtype_injective
      rw [map_fittingWithin_subgroupOf_eq hPJ,
        Subgroup.map_subgroupOf_eq_of_le ((fittingWithin_le P).trans hPJ)]
    have hcentMap :
        (centralizerWithin (fittingWithin PJ) RJ).map J.subtype =
          centralizerWithin (fittingWithin P) R := by
      rw [hfitPJ]
      exact map_centralizerWithin_subgroupOf_eq
        ((fittingWithin_le P).trans hPJ) hRJ
    have hcentJ : centralizerWithin (fittingWithin PJ) RJ = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective _
        J.subtype_injective).mp
      rw [hcentMap, hfitPK]
      exact hreg
    have hcommJ : ⁅PJ, RJ⁆ ≤ fittingWithin PJ :=
      ih J PJ RJ (by infer_instance) hJlt hcompJ hsolJ hoddJ hcopJ
        hsemJ hcentJ
    have hcommP : ⁅P, R⁆ ≤ fittingWithin P := by
      have hmapped := Subgroup.map_mono hcommJ (f := J.subtype)
      rw [Subgroup.map_commutator,
        Subgroup.map_subgroupOf_eq_of_le hPJ,
        Subgroup.map_subgroupOf_eq_of_le hRJ,
        map_fittingWithin_subgroupOf_eq hPJ] at hmapped
      exact hmapped
    have hcommPF : ⁅P, R⁆ ≤ F := hcommP.trans_eq hfitPK
    have hmapCore :
        C0.map e.toMonoidHom = pCore (pp : ℕ) Kq := by
      dsimp only [C0]
      apply map_pCore_eq_of_surjective_of_ker_isPGroup
        e.toMonoidHom e.surjective
      rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
      exact IsPGroup.of_bot
    have hcompMaps :
        qF.comp K.subtype =
          Kq.subtype.comp (e.toMonoidHom.comp qK) := by
      ext x
      rfl
    have hPmap :
        P.map qF = (pCore (pp : ℕ) Kq).map Kq.subtype := by
      calc
        P.map qF = P0.map (qF.comp K.subtype) := by
          dsimp only [P]
          rw [Subgroup.map_map]
        _ = P0.map (Kq.subtype.comp (e.toMonoidHom.comp qK)) := by
          rw [hcompMaps]
        _ = ((P0.map qK).map e.toMonoidHom).map Kq.subtype := by
          rw [Subgroup.map_map, Subgroup.map_map]
          apply le_antisymm
          · rintro _ ⟨x, hx, rfl⟩
            exact ⟨x, hx, rfl⟩
          · rintro _ ⟨x, hx, rfl⟩
            exact ⟨x, hx, rfl⟩
        _ = (C0.map e.toMonoidHom).map Kq.subtype := by
          rw [Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective (fittingCore K))]
        _ = (pCore (pp : ℕ) Kq).map Kq.subtype := by rw [hmapCore]
    have hmapComm : ⁅P, R⁆.map qF = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      simpa only [qF, QuotientGroup.ker_mk'] using hcommPF
    have hcoreComm :
        ⁅(pCore (pp : ℕ) Kq).map Kq.subtype, Rq⁆ = ⊥ := by
      rw [← hPmap]
      change ⁅P.map qF, R.map qF⁆ = ⊥
      rw [← Subgroup.map_commutator]
      exact hmapComm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcoreComm
  have hRqCentFit :
      Rq ≤ centralizerWithin Rq ((fittingCore Kq).map Kq.subtype) := by
    intro r hr
    refine ⟨hr, ?_⟩
    intro x hx
    have hxcent := hFitCentRq hx
    rw [Subgroup.mem_centralizer_iff] at hxcent
    exact (hxcent r hr).symm
  have hRqNormKq : Rq ≤ Subgroup.normalizer (Kq : Set (G ⧸ F)) :=
    Subgroup.le_normalizer_of_normal
  have hRqCentKq : Rq ≤ Subgroup.centralizer (Kq : Set (G ⧸ F)) :=
    hRqCentFit.trans (coprime_cent_fitting hRqNormKq hcopq hsolKq)
  have hKqCentRq : Kq ≤ Subgroup.centralizer (Rq : Set (G ⧸ F)) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrcent := hRqCentKq hr
    rw [Subgroup.mem_centralizer_iff] at hrcent
    exact (hrcent k hk).symm
  have hcommq : ⁅Kq, Rq⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKqCentRq
  have hmapCommKR : ⁅K, R⁆.map qF = ⊥ := by
    rw [Subgroup.map_commutator]
    exact hcommq
  have hleKer : ⁅K, R⁆ ≤ qF.ker :=
    (Subgroup.map_eq_bot_iff ⁅K, R⁆).mp hmapCommKR
  simpa only [qF, F, QuotientGroup.ker_mk'] using hleKer

private def OddSdprodPrimactCommgSubFittingStatement (n : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Nat.card G = n →
    ∀ (K R : Subgroup G),
      K.Normal →
      K.IsComplement' R →
      Odd (Nat.card G) →
      IsSolvable G →
      Nat.Coprime (Nat.card K) (Nat.card R) →
      IsSemiprimeAction K R →
      centralizerWithin (fittingWithin K) R = ⊥ →
      ⁅K, R⁆ ≤ fittingWithin K

private theorem oddSdprodPrimactCommgSubFittingStatement_all (n : ℕ) :
    OddSdprodPrimactCommgSubFittingStatement.{u} n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G _ _ hcard K R hKnormal hKR hodd hsol hcop hprime hreg
      classical
      letI : IsSolvable G := hsol
      letI : K.Normal := hKnormal
      apply odd_sdprod_primact_commg_sub_Fitting_reduce_to_pgroup_3_8
        hKR hodd hcop hprime hreg
      · intro J L T hLnormal hJlt hLT hsolJ hoddJ hcopLT hprimeLT hregLT
        exact ih (Nat.card J) (by simpa only [hcard] using hJlt)
          J rfl L T hLnormal hLT hoddJ hsolJ hcopLT hprimeLT hregLT
      · intro p hp hKquot
        letI : Fact p.Prime := ⟨hp⟩
        apply commutator_le_fittingWithin_of_prime_actor_cases_3_8
          hcop hprime
        · intro X hXR hXprime hregX
          by_cases hXRne : X = R
          · subst X
            exact prime_actor_commutator_le_fitting_of_quotient_isPGroup_3_8
              hKR hodd hcop hXprime hregX hKquot
          · have hXlt : X < R := lt_of_le_of_ne hXR hXRne
            have hXne : X ≠ ⊥ := by
              rw [← X.one_lt_card_iff_ne_bot]
              exact hXprime.one_lt
            let J : Subgroup G := X ⊔ K
            let KJ : Subgroup J := K.subgroupOf J
            let XJ : Subgroup J := X.subgroupOf J
            have hKJ : K ≤ J := le_sup_right
            have hXJ : X ≤ J := le_sup_left
            letI : KJ.Normal := by
              dsimp only [KJ]
              exact Subgroup.Normal.subgroupOf hKnormal J
            have hcompJ : KJ.IsComplement' XJ := by
              have hdis : Disjoint KJ XJ := by
                rw [disjoint_iff]
                apply le_antisymm _ bot_le
                intro z hz
                apply Subgroup.mem_bot.mpr
                apply Subtype.ext
                apply Subgroup.mem_bot.mp
                rw [← disjoint_iff.mp
                  (Disjoint.mono le_rfl hXR hKR.disjoint)]
                exact hz
              apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
              have hsup : KJ ⊔ XJ = ⊤ := by
                change K.subgroupOf J ⊔ X.subgroupOf J = ⊤
                rw [← Subgroup.subgroupOf_sup hKJ hXJ]
                simp [J, sup_comm]
              rw [← Subgroup.normal_mul KJ XJ, hsup]
              rfl
            have hJlt : Nat.card J < Nat.card G := by
              have hXcardlt : Nat.card X < Nat.card R := by
                have hle := Subgroup.card_le_of_le hXlt.le
                exact lt_of_le_of_ne hle fun heq ↦
                  hXlt.ne (Subgroup.eq_of_le_of_card_ge hXlt.le heq.ge)
              rw [← hcompJ.card_mul,
                natCard_subgroupOf_eq hKJ,
                natCard_subgroupOf_eq hXJ,
                ← hKR.card_mul]
              exact Nat.mul_lt_mul_of_pos_left hXcardlt Nat.card_pos
            have hsolJ : IsSolvable J :=
              isSolvable_subgroup_of_isSolvable J
            have hoddJ : Odd (Nat.card J) :=
              odd_natCard_subgroup J hodd
            have hcopJ : Nat.Coprime (Nat.card KJ) (Nat.card XJ) := by
              rw [natCard_subgroupOf_eq hKJ, natCard_subgroupOf_eq hXJ]
              exact hcop.coprime_dvd_right
                (Subgroup.card_dvd_of_le hXR)
            have hsemKX : IsSemiprimeAction K X := by
              intro Y hYX hYne
              calc
                centralizerWithin K Y = centralizerWithin K R :=
                  hprime Y (hYX.trans hXR) hYne
                _ = centralizerWithin K X :=
                  (hprime X hXR hXne).symm
            have hsemJ : IsSemiprimeAction KJ XJ :=
              semiprimeAction_subgroupOf hKJ hXJ hsemKX
            have hfitKJ :
                fittingWithin KJ = (fittingWithin K).subgroupOf J := by
              apply Subgroup.map_injective J.subtype_injective
              rw [map_fittingWithin_subgroupOf_eq hKJ,
                Subgroup.map_subgroupOf_eq_of_le
                  ((fittingWithin_le K).trans hKJ)]
            have hcentMap :
                (centralizerWithin (fittingWithin KJ) XJ).map J.subtype =
                  centralizerWithin (fittingWithin K) X := by
              rw [hfitKJ]
              exact map_centralizerWithin_subgroupOf_eq
                ((fittingWithin_le K).trans hKJ) hXJ
            have hregJ : centralizerWithin (fittingWithin KJ) XJ = ⊥ := by
              apply (Subgroup.map_eq_bot_iff_of_injective _
                J.subtype_injective).mp
              rw [hcentMap, hregX]
            have hcommJ : ⁅KJ, XJ⁆ ≤ fittingWithin KJ :=
              ih (Nat.card J) (by simpa only [hcard] using hJlt)
                J rfl KJ XJ (by infer_instance) hcompJ hoddJ hsolJ
                hcopJ hsemJ hregJ
            have hmapped := Subgroup.map_mono hcommJ (f := J.subtype)
            rw [Subgroup.map_commutator,
              Subgroup.map_subgroupOf_eq_of_le hKJ,
              Subgroup.map_subgroupOf_eq_of_le hXJ,
              map_fittingWithin_subgroupOf_eq hKJ] at hmapped
            exact hmapped
        · exact hreg

/-- `BGsection3.v: odd_sdprod_primact_commg_sub_Fitting`
(Bender--Glauberman Theorem 3.8). -/
theorem odd_sdprod_primact_commg_sub_Fitting
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G} [K.Normal]
    (hKR : K.IsComplement' R)
    (hodd : Odd (Nat.card G))
    (hsol : IsSolvable G)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hprime : IsSemiprimeAction K R)
    (hreg : centralizerWithin (fittingWithin K) R = ⊥) :
    ⁅K, R⁆ ≤ fittingWithin K :=
  oddSdprodPrimactCommgSubFittingStatement_all (Nat.card G)
    G rfl K R (inferInstance : K.Normal) hKR hodd hsol hcop hprime hreg

/-- Ambient-subgroup form of Theorem 3.8.  The first hypothesis is
definitionally the body of
`Submission.OddOrder.PF.IsInternalSemidirectProductIn K R M`; spelling it
out here avoids a dependency from BG Section 3 to PF Section 2 while letting
later callers pass that predicate directly. -/
theorem odd_sdprod_primact_commg_sub_Fitting_of_internal
    {G : Type u} [Group G] [Finite G]
    {K R M : Subgroup G}
    (hsd :
      K ≤ M ∧ R ≤ M ∧ (K.subgroupOf M).Normal ∧
        (K.subgroupOf M).IsComplement' (R.subgroupOf M))
    (hodd : Odd (Nat.card M))
    (hsol : IsSolvable M)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hprime : IsSemiprimeAction K R)
    (hreg : centralizerWithin (fittingWithin K) R = ⊥) :
    ⁅K, R⁆ ≤ fittingWithin K := by
  let KM : Subgroup M := K.subgroupOf M
  let RM : Subgroup M := R.subgroupOf M
  have hKM : K ≤ M := hsd.1
  have hRM : R ≤ M := hsd.2.1
  letI : KM.Normal := hsd.2.2.1
  letI : IsSolvable M := hsol
  have hcompM : KM.IsComplement' RM := hsd.2.2.2
  have hcopM : Nat.Coprime (Nat.card KM) (Nat.card RM) := by
    simpa only [KM, RM, natCard_subgroupOf_eq hKM,
      natCard_subgroupOf_eq hRM] using hcop
  have hprimeM : IsSemiprimeAction KM RM :=
    semiprimeAction_subgroupOf hKM hRM hprime
  have hfitKM :
      fittingWithin KM = (fittingWithin K).subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [map_fittingWithin_subgroupOf_eq hKM,
      Subgroup.map_subgroupOf_eq_of_le
        ((fittingWithin_le K).trans hKM)]
  have hregM : centralizerWithin (fittingWithin KM) RM = ⊥ := by
    rw [hfitKM]
    apply Subgroup.map_injective M.subtype_injective
    rw [map_centralizerWithin_subgroupOf_eq
      ((fittingWithin_le K).trans hKM) hRM, hreg, Subgroup.map_bot]
  have hlocal : ⁅KM, RM⁆ ≤ fittingWithin KM :=
    odd_sdprod_primact_commg_sub_Fitting
      hcompM hodd hsol hcopM hprimeM hregM
  have hmapped : ⁅KM, RM⁆.map M.subtype ≤
      (fittingWithin KM).map M.subtype :=
    Subgroup.map_mono hlocal
  simpa only [KM, RM, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hKM,
    Subgroup.map_subgroupOf_eq_of_le hRM,
    map_fittingWithin_subgroupOf_eq hKM] using hmapped

end

end Submission.OddOrder.BG.Section03
