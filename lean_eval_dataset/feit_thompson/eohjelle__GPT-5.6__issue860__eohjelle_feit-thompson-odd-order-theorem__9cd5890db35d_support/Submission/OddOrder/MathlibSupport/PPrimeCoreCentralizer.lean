import Submission.OddOrder.MathlibSupport.CoprimeNilpotentCentralizer
import Submission.OddOrder.MathlibSupport.FittingPCore
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient
import Submission.OddOrder.MathlibSupport.PPrimePCore
import Submission.OddOrder.MathlibSupport.SolvableQuotientCentralizer

/-!
The `p'`-core of the centralizer of a `p`-subgroup in a finite solvable
group is contained in the ambient `p'`-core.  This is the mathlib-shaped
form of Bender--Glauberman Proposition 7.5(b).
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement

private theorem map_pPrimeCore_centralizer_le_of_eq_bot
    {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    [IsSolvable K] {R : Subgroup K}
    (hRp : IsPGroup p R) (hcore : pPrimeCore p K = ⊥) :
    (pPrimeCore p (Subgroup.centralizer (R : Set K))).map
        (Subgroup.centralizer (R : Set K)).subtype ≤ pPrimeCore p K := by
  classical
  let C : Subgroup K := Subgroup.centralizer (R : Set K)
  let MC : Subgroup C := pPrimeCore p C
  let M : Subgroup K := MC.map C.subtype
  let T : Subgroup K := pCore p K
  let H : Subgroup K := R ⊔ T
  change M ≤ pPrimeCore p K
  rw [hcore]
  apply le_bot_iff.mpr
  have hMC : M ≤ C := by
    dsimp [M]
    exact Subgroup.map_subtype_le MC
  have hMprime : IsPPrimeSubgroup p M := by
    rw [IsPPrimeSubgroup]
    dsimp [M, MC]
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact pPrimeCore_coprime_card
  have hCnormM : C ≤ Subgroup.normalizer (M : Set K) := by
    intro c hc
    let cC : C := ⟨c, hc⟩
    have hcNorm : cC ∈ Subgroup.normalizer (MC : Set C) := by
      rw [MC.normalizer_eq_top]
      trivial
    exact MC.le_normalizer_map C.subtype
      (Subgroup.mem_map_of_mem C.subtype hcNorm)
  have hRnormT : R ≤ Subgroup.normalizer (T : Set K) := by
    rw [T.normalizer_eq_top]
    exact le_top
  have hTp : IsPGroup p T := pCore_isPGroup
  have hHp : IsPGroup p H :=
    hRp.to_sup_of_normal_right' hTp hRnormT
  have hMcentR : M ≤ Subgroup.centralizer (R : Set K) := hMC
  have hMnormR : M ≤ Subgroup.normalizer (R : Set K) :=
    hMcentR.trans (Subgroup.centralizer_le_normalizer (R : Set K))
  have hMnormT : M ≤ Subgroup.normalizer (T : Set K) := by
    rw [T.normalizer_eq_top]
    exact le_top
  have hMnormH : M ≤ Subgroup.normalizer (H : Set K) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    dsimp [H]
    rw [Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMnormR hm),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMnormT hm)]
  have hcopHM : Nat.Coprime (Nat.card H) (Nat.card M) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hHp
    rw [hn]
    exact hMprime.pow_left n
  have hdisMH : Disjoint M H :=
    Subgroup.disjoint_of_coprime_natCard hcopHM.symm
  let CHR : Subgroup K := centralizerWithin H R
  let CHM : Subgroup K := centralizerWithin H M
  have hCHRnormM : CHR ≤ Subgroup.normalizer (M : Set K) := by
    apply (show CHR ≤ C by
      intro x hx
      exact hx.2) |>.trans hCnormM
  have hcommM : ⁅M, CHR⁆ ≤ M :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hCHRnormM
  have hcommH : ⁅M, CHR⁆ ≤ H :=
    (Subgroup.commutator_mono le_rfl
      (centralizerWithin_le_left H R)).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hMnormH)
  have hcommBot : ⁅M, CHR⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← disjoint_iff.mp hdisMH]
    exact le_inf hcommM hcommH
  have hCHRcentM : CHR ≤ Subgroup.centralizer (M : Set K) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.commutator_comm]
    exact hcommBot
  have hRCHM : R ≤ CHM := by
    intro r hr
    refine ⟨(show R ≤ H from le_sup_left) hr, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro m hm
    exact (Subgroup.mem_centralizer_iff.mp (hMcentR hm) r hr).symm
  have hself : centralizerWithin H CHM ≤ CHM := by
    apply le_inf (centralizerWithin_le_left H CHM)
    exact (centralizerWithin_antitone_right hRCHM).trans hCHRcentM
  letI : Group.IsNilpotent H := hHp.isNilpotent
  have hMcentH : M ≤ Subgroup.centralizer (H : Set K) :=
    coprime_nilpotent_centralizes_of_selfCentralizing_fixedPoints
      hMnormH hcopHM hself
  have hMcentT : M ≤ Subgroup.centralizer (T : Set K) :=
    hMcentH.trans (Subgroup.centralizer_le fun _ ht ↦
      (show T ≤ H from le_sup_right) ht)
  have hMT : M ≤ T :=
    hMcentT.trans
      (centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hcore)
  have hdisTM : Disjoint T M := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTp
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hn]
    exact hMprime.pow_left n
  apply le_antisymm _ bot_le
  intro m hm
  have hmBot : m ∈ (⊥ : Subgroup K) := by
    rw [← disjoint_iff.mp hdisTM]
    exact ⟨hMT hm, hm⟩
  exact hmBot

private theorem map_pPrimeCore_centralizer_le
    {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    [IsSolvable K] {R : Subgroup K} (hRp : IsPGroup p R) :
    (pPrimeCore p (Subgroup.centralizer (R : Set K))).map
        (Subgroup.centralizer (R : Set K)).subtype ≤ pPrimeCore p K := by
  classical
  let O : Subgroup K := pPrimeCore p K
  letI : O.Normal := by
    dsimp [O]
    infer_instance
  let q : K →* K ⧸ O := QuotientGroup.mk' O
  let Rq : Subgroup (K ⧸ O) := R.map q
  let C : Subgroup K := Subgroup.centralizer (R : Set K)
  let Cq : Subgroup (K ⧸ O) := Subgroup.centralizer (Rq : Set (K ⧸ O))
  let MC : Subgroup C := pPrimeCore p C
  let M : Subgroup K := MC.map C.subtype
  change M ≤ O
  have hcopOR : Nat.Coprime (Nat.card O) (Nat.card R) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hRp
    rw [hn]
    exact (pPrimeCore_coprime_card (G := K) (p := p)).pow_left n |>.symm
  have hCmap : C.map q = Cq := by
    exact map_centralizer_quotient_eq_of_coprime hcopOR
  let f : C →* Cq :=
    { toFun := fun c ↦ ⟨q (c : K), by
          rw [← hCmap]
          exact Subgroup.mem_map_of_mem q c.property⟩
      map_one' := by
        apply Subtype.ext
        exact map_one q
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul q (a : K) (b : K) }
  have hfSurj : Function.Surjective f := by
    intro z
    have hz : (z : K ⧸ O) ∈ C.map q := by
      rw [hCmap]
      exact z.property
    rcases hz with ⟨c, hc, hcz⟩
    refine ⟨⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    exact hcz
  let MCq : Subgroup Cq := MC.map f
  letI : MCq.Normal := by
    dsimp [MCq]
    exact Subgroup.Normal.map (inferInstance : MC.Normal) f hfSurj
  have hMCqPrime : IsPPrimeSubgroup p MCq := by
    rw [IsPPrimeSubgroup]
    exact (pPrimeCore_coprime_card (G := C) (p := p)).coprime_dvd_right
      (Subgroup.card_map_dvd MC f)
  have hMCqCore : MCq ≤ pPrimeCore p Cq :=
    le_pPrimeCore hMCqPrime (inferInstance : MCq.Normal)
  have hmaps : M.map q = MCq.map Cq.subtype := by
    dsimp [M, MCq]
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hMqCore : M.map q ≤ (pPrimeCore p Cq).map Cq.subtype := by
    rw [hmaps]
    exact Subgroup.map_mono hMCqCore
  have hRqP : IsPGroup p Rq := hRp.map q
  have hQcore : pPrimeCore p (K ⧸ O) = ⊥ :=
    pPrimeCore_quotient_self_eq_bot (G := K) (p := p)
  have hbase := map_pPrimeCore_centralizer_le_of_eq_bot
    (K := K ⧸ O) (R := Rq) hRqP hQcore
  have hbaseBot := hbase.trans_eq hQcore
  change (pPrimeCore p Cq).map Cq.subtype ≤
    (⊥ : Subgroup (K ⧸ O)) at hbaseBot
  have hMqBot : M.map q ≤ (⊥ : Subgroup (K ⧸ O)) := by
    exact hMqCore.trans hbaseBot
  rw [← QuotientGroup.ker_mk' O, ← Subgroup.map_eq_bot_iff]
  exact le_antisymm hMqBot bot_le

/-- Bender--Glauberman Proposition 7.5(b): in a finite solvable subgroup,
the `p'`-core of the centralizer of a `p`-subgroup lies in the ambient
`p'`-core. -/
theorem map_pPrimeCore_centralizerWithin_le_map_pPrimeCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {X R : Subgroup G}
    (hRX : R ≤ X) (hRp : IsPGroup p R) (hXsol : IsSolvable X) :
    (pPrimeCore p (centralizerWithin X R)).map
        (centralizerWithin X R).subtype ≤
      (pPrimeCore p X).map X.subtype := by
  classical
  letI : IsSolvable X := hXsol
  let RX : Subgroup X := R.subgroupOf X
  let CX : Subgroup X := Subgroup.centralizer (RX : Set X)
  let C : Subgroup G := centralizerWithin X R
  let e : C ≃* CX :=
    { toFun := fun c ↦
        ⟨⟨(c : G), c.property.1⟩, by
          apply Subgroup.mem_centralizer_iff.mpr
          intro r hr
          apply Subtype.ext
          exact Subgroup.mem_centralizer_iff.mp c.property.2 (r : G) hr⟩
      invFun := fun c ↦
        ⟨((c : CX) : X), ⟨(c : X).property, by
          apply Subgroup.mem_centralizer_iff.mpr
          intro r hr
          let rX : X := ⟨r, hRX hr⟩
          have hcomm := Subgroup.mem_centralizer_iff.mp c.property rX hr
          exact congrArg (fun y : X ↦ (y : G)) hcomm⟩⟩
      left_inv := by
        intro c
        apply Subtype.ext
        rfl
      right_inv := by
        intro c
        apply Subtype.ext
        apply Subtype.ext
        rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  let C0 : Subgroup C := pPrimeCore p C
  let C0X : Subgroup CX := C0.map e.toMonoidHom
  have hC0XPrime : IsPPrimeSubgroup p C0X := by
    rw [IsPPrimeSubgroup]
    dsimp [C0X, C0]
    rw [Subgroup.card_map_of_injective e.injective]
    exact pPrimeCore_coprime_card
  have hC0XNormal : C0X.Normal := by
    dsimp [C0X]
    exact Subgroup.Normal.map (inferInstance : C0.Normal)
      e.toMonoidHom e.surjective
  have hC0XCore : C0X ≤ pPrimeCore p CX :=
    le_pPrimeCore hC0XPrime hC0XNormal
  have hRXp : IsPGroup p RX := by
    dsimp [RX]
    exact hRp.comap_subtype
  have hcoreCX : (pPrimeCore p CX).map CX.subtype ≤ pPrimeCore p X :=
    map_pPrimeCore_centralizer_le hRXp
  change (pPrimeCore p C).map C.subtype ≤ (pPrimeCore p X).map X.subtype
  calc
    (pPrimeCore p C).map C.subtype =
        (C0X.map CX.subtype).map X.subtype := by
      dsimp [C0X, C0]
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    _ ≤ ((pPrimeCore p CX).map CX.subtype).map X.subtype :=
      Subgroup.map_mono (Subgroup.map_mono hC0XCore)
    _ ≤ (pPrimeCore p X).map X.subtype :=
      Subgroup.map_mono hcoreCX

end Submission.OddOrder.MathlibSupport
