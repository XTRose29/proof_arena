import Submission.OddOrder.BG.Section05.NarrowCentralizerDirectProduct
import Submission.OddOrder.BG.Section05.OmegaUpperCentralMaximal
import Submission.OddOrder.BG.Section08.NonPCoreFittingMaximalOvergroup
import Submission.OddOrder.BG.Section10.SigmaDisjointness
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRankSylowTransport
import Submission.OddOrder.MathlibSupport.PGroupNormalizer
import Submission.OddOrder.MathlibSupport.PMaxElemSubtype

/-!
# Bender--Glauberman Section 10: basic maximal-elementary structure

This file ports the final block of `BGsection10.v`: Lemma 10.13 and
Proposition 10.14(a)--(d).  A line in an elementary-abelian subgroup is
represented by an elementary-abelian subgroup of cardinal rank one.  The
source's transitivity assertion is stated in its pairwise form, using the
same conjugation convention as the rest of the port.
-/

namespace Submission.OddOrder.BG.Section10

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section05
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section08
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative Pointwise

universe u

noncomputable section

/-- The Lean form of membership in MathComp's set `'E_p^1(A)`. -/
def RankOneLineIn
    {G : Type u} [Group G] (p : ℕ) (A X : Subgroup G) : Prop :=
  X ≤ A ∧ IsElementaryAbelianOfRank p 1 X

private theorem isNarrow_subgroup_iff_top
    {G : Type u} [Group G] {p : ℕ} [Fact p.Prime]
    (A : Subgroup G) :
    IsNarrow p A ↔ IsNarrow p (⊤ : Subgroup A) := by
  have hiff := isNarrow_map_iff_of_injective
    (p := p) A.subtype A.subtype_injective (⊤ : Subgroup A)
  have hmapTop :
      (⊤ : Subgroup A).map A.subtype = A := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hmapTop] at hiff
  exact hiff

private theorem isNarrow_top_mapSylow_iff
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime] (e : A ≃* B) (P : Sylow p A) :
    IsNarrow p (⊤ : Subgroup (P.mapSurjective
      (f := e.toMonoidHom) e.surjective)) ↔
      IsNarrow p (⊤ : Subgroup P) := by
  let Q : Sylow p B := P.mapSurjective
    (f := e.toMonoidHom) e.surjective
  let eP₀ : P ≃* ((P : Subgroup A).map e.toMonoidHom) :=
    e.subgroupMap (P : Subgroup A)
  let eP : P ≃* Q :=
    eP₀.trans (MulEquiv.subgroupCongr (by rfl))
  have hiff := isNarrow_map_mulEquiv_iff
    (p := p) eP (⊤ : Subgroup P)
  rw [Subgroup.map_top_of_surjective eP.toMonoidHom eP.surjective] at hiff
  simpa [Q] using hiff

private theorem not_isNarrow_sylow_of_mem_beta_top
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : p ∈ betaPrimes (⊤ : Subgroup G))
    (Q : Sylow p G) :
    ¬ IsNarrow p (Q : Subgroup G) := by
  letI : Fact p.Prime := ⟨hp.1⟩
  let e : G ≃* (⊤ : Subgroup G) := Subgroup.topEquiv.symm
  let P : Sylow p (⊤ : Subgroup G) :=
    Q.mapSurjective (f := e.toMonoidHom) e.surjective
  intro hQnarrow
  have hQtop : IsNarrow p (⊤ : Subgroup Q) :=
    (isNarrow_subgroup_iff_top (Q : Subgroup G)).mp hQnarrow
  have hPtop : IsNarrow p (⊤ : Subgroup P) := by
    exact (isNarrow_top_mapSylow_iff e Q).mpr hQtop
  exact hp.2 P hPtop

private theorem subgroup_characteristic_of_isCyclic
    {C : Type*} [Group C] [IsCyclic C] (H : Subgroup C) :
    H.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  obtain ⟨m, hm⟩ := e.toMonoidHom.map_cyclic
  rintro _ ⟨x, hx, rfl⟩
  rw [hm]
  exact H.zpow_mem hx m

private theorem exists_rankTwo_le_of_rankThree
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hE : IsElementaryAbelianOfRank p 3 E) :
    ∃ A : Subgroup G, A ≤ E ∧ IsElementaryAbelianOfRank p 2 A := by
  have hpTwo : p ^ 2 ≤ Nat.card E := by
    rw [hE.card_eq]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  obtain ⟨A₀, hA₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card
      (G := E) (Fact.out : p.Prime) hE.isPGroup hpTwo
  have hA₀ : IsElementaryAbelianOfRank p 2 A₀ := by
    letI : IsMulCommutative E := hE.commutative
    refine
      { isPGroup := hE.isPGroup.to_subgroup A₀
        commutative := by infer_instance
        pow_eq_one := ?_
        card_eq := hA₀card }
    intro x
    apply Subtype.ext
    exact hE.pow_eq_one (x : E)
  let A : Subgroup G := A₀.map E.subtype
  refine ⟨A, Subgroup.map_subtype_le A₀, ?_⟩
  exact hA₀.map_of_injective E.subtype E.subtype_injective

private theorem map_centralizerWithin_subgroupOf
    {G : Type u} [Group G]
    {J V A : Subgroup G} (hVJ : V ≤ J) (hAJ : A ≤ J) :
    (centralizerWithin (V.subgroupOf J) (A.subgroupOf J)).map J.subtype =
      centralizerWithin V A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨hy.1, ?_⟩
    intro a ha
    let aJ : J := ⟨a, hAJ ha⟩
    exact congrArg Subtype.val (hy.2 aJ ha)
  · intro hx
    let xJ : J := ⟨x, hVJ hx.1⟩
    refine ⟨xJ, ?_, rfl⟩
    refine ⟨hx.1, ?_⟩
    intro a ha
    apply Subtype.ext
    exact hx.2 a ha

private theorem rankTwo_distinct_lines
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A X Z : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hX : RankOneLineIn p A X) (hZ : RankOneLineIn p A Z)
    (hne : X ≠ Z) :
    Disjoint X Z ∧ X ⊔ Z = A := by
  have hdis : Disjoint X Z := by
    rw [disjoint_iff]
    by_contra hneBot
    have hdiv : Nat.card (X ⊓ Z : Subgroup G) ∣ p := by
      simpa [hX.2.card_eq, pow_one] using
        (Subgroup.card_dvd_of_le (show X ⊓ Z ≤ X from inf_le_left))
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv with
      hcardOne | hcardP
    · exact hneBot (Subgroup.eq_bot_of_card_eq (X ⊓ Z) hcardOne)
    · have hInfX : X ⊓ Z = X := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_left
        rw [hcardP, hX.2.card_eq, pow_one]
      have hXZ : X ≤ Z := by
        intro x hx
        have hxInf : x ∈ X ⊓ Z := by rw [hInfX]; exact hx
        exact hxInf.2
      have hcardEq : Nat.card X = Nat.card Z := by
        rw [hX.2.card_eq, hZ.2.card_eq]
      exact hne (Subgroup.eq_of_le_of_card_ge hXZ hcardEq.ge)
  refine ⟨hdis, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge (sup_le hX.1 hZ.1)
  rw [natCard_sup_eq_mul_of_disjoint_of_commute hdis,
    hX.2.card_eq, hZ.2.card_eq, hA.card_eq, pow_one, pow_two]
  intro x hx y hy
  letI : IsMulCommutative A := hA.commutative
  exact congrArg Subtype.val
    (mul_comm (⟨x, hX.1 hx⟩ : A) ⟨y, hZ.1 hy⟩)

private theorem exists_complementary_rankOneLine
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A Z : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hZ : RankOneLineIn p A Z) :
    ∃ X : Subgroup G,
      RankOneLineIn p A X ∧ X ≠ Z ∧ Disjoint X Z ∧ X ⊔ Z = A := by
  have hZAproper : Z < A := by
    refine lt_of_le_of_ne hZ.1 ?_
    intro hZA
    have hcard := congrArg (fun H : Subgroup G ↦ Nat.card H) hZA
    rw [hZ.2.card_eq, hA.card_eq, pow_one] at hcard
    have hpLt : p < p ^ 2 := by
      rw [pow_two]
      exact lt_mul_of_one_lt_right
        (Fact.out : p.Prime).pos (Fact.out : p.Prime).one_lt
    omega
  obtain ⟨x, hxA, hxZ⟩ := SetLike.exists_of_lt hZAproper
  let X : Subgroup G := Subgroup.zpowers x
  have hxne : x ≠ 1 := by
    intro hx
    apply hxZ
    rw [hx]
    exact Z.one_mem
  have hxpow : x ^ p = 1 :=
    congrArg Subtype.val (hA.pow_eq_one ⟨x, hxA⟩)
  have hxorder : orderOf x = p :=
    ((Nat.dvd_prime (Fact.out : p.Prime)).mp
      (orderOf_dvd_of_pow_eq_one hxpow)).resolve_left (by
        rw [orderOf_eq_one_iff]
        exact hxne)
  have hXcard : Nat.card X = p := by
    dsimp [X]
    rw [Nat.card_zpowers, hxorder]
  have hXA : X ≤ A := Subgroup.zpowers_le.mpr hxA
  have hX : IsElementaryAbelianOfRank p 1 X :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
  have hXneZ : X ≠ Z := by
    intro hEq
    apply hxZ
    rw [← hEq]
    exact Subgroup.mem_zpowers x
  obtain ⟨hdis, hsup⟩ :=
    rankTwo_distinct_lines hA ⟨hXA, hX⟩ hZ hXneZ
  exact ⟨X, ⟨hXA, hX⟩, hXneZ, hdis, hsup⟩

private abbrev RankOneLines
    {G : Type u} [Group G] (p : ℕ) (A : Subgroup G) :=
  {X : Subgroup G // RankOneLineIn p A X}

private abbrev OtherRankOneLines
    {G : Type u} [Group G] (p : ℕ) (A Z : Subgroup G) :=
  {X : RankOneLines p A // X.1 ≠ Z}

private theorem natCard_rankOneLines
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A) :
    Nat.card (RankOneLines p A) = p + 1 := by
  classical
  let Pointed :=
    Σ X : RankOneLines p A, {x : G // x ∈ X.1 ∧ x ≠ 1}
  let NonOne := {a : A // a ≠ 1}
  let e : Pointed ≃ NonOne :=
    { toFun := fun z ↦
        ⟨⟨z.2.1, z.1.2.1 z.2.2.1⟩, by
          intro h
          exact z.2.2.2 (congrArg (fun a : A ↦ (a : G)) h)⟩
      invFun := fun a ↦ by
        let X : Subgroup G := Subgroup.zpowers (a.1 : G)
        have hapow : (a.1 : G) ^ p = 1 :=
          congrArg Subtype.val (hA.pow_eq_one a.1)
        have haGne : (a.1 : G) ≠ 1 := by
          intro h
          apply a.2
          exact Subtype.ext h
        have haorder : orderOf (a.1 : G) = p :=
          ((Nat.dvd_prime (Fact.out : p.Prime)).mp
            (orderOf_dvd_of_pow_eq_one hapow)).resolve_left (by
              rw [orderOf_eq_one_iff]
              exact haGne)
        have hXcard : Nat.card X = p := by
          dsimp [X]
          rw [Nat.card_zpowers, haorder]
        have hXA : X ≤ A := Subgroup.zpowers_le.mpr a.1.2
        let XL : RankOneLines p A :=
          ⟨X, hXA, isElementaryAbelianOfRank_one_of_card_eq_prime hXcard⟩
        exact ⟨XL, ⟨(a.1 : G), Subgroup.mem_zpowers _, haGne⟩⟩
      left_inv := by
        rintro ⟨X, x⟩
        apply Sigma.subtype_ext
        · apply Subtype.ext
          apply Subgroup.eq_of_le_of_card_ge
          · exact Subgroup.zpowers_le.mpr x.2.1
          · rw [Nat.card_zpowers]
            have hxpow : x.1 ^ p = 1 :=
              congrArg Subtype.val (X.2.2.pow_eq_one ⟨x.1, x.2.1⟩)
            have hxorder : orderOf x.1 = p :=
              ((Nat.dvd_prime (Fact.out : p.Prime)).mp
                (orderOf_dvd_of_pow_eq_one hxpow)).resolve_left (by
                  rw [orderOf_eq_one_iff]
                  exact x.2.2)
            rw [hxorder, X.2.2.card_eq, pow_one]
        · rfl
      right_inv := by
        intro a
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  letI := Fintype.ofFinite (RankOneLines p A)
  letI (_X : RankOneLines p A) := Fintype.ofFinite
    {x : G // x ∈ _X.1 ∧ x ≠ 1}
  letI := Fintype.ofFinite NonOne
  have hfiber (X : RankOneLines p A) :
      Fintype.card {x : G // x ∈ X.1 ∧ x ≠ 1} = p - 1 := by
    letI := Fintype.ofFinite X.1
    let eX : {x : G // x ∈ X.1 ∧ x ≠ 1} ≃
        {x : X.1 // x ≠ 1} :=
      { toFun := fun x ↦ ⟨⟨x.1, x.2.1⟩, by
          intro h
          exact x.2.2 (congrArg Subtype.val h)⟩
        invFun := fun x ↦ ⟨x.1.1, x.1.2, by
          intro h
          exact x.2 (Subtype.ext h)⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    have hcardX : Fintype.card X.1 = p := by
      rw [← Nat.card_eq_fintype_card]
      simpa using X.2.2.card_eq
    rw [Fintype.card_congr eX,
      Fintype.card_subtype_compl (fun x : X.1 ↦ x = 1)]
    simp [hcardX]
  have hpointed :
      Fintype.card Pointed = Fintype.card (RankOneLines p A) * (p - 1) := by
    calc
      Fintype.card Pointed =
          ∑ X : RankOneLines p A,
            Fintype.card {x : G // x ∈ X.1 ∧ x ≠ 1} :=
        Fintype.card_sigma
      _ = Fintype.card (RankOneLines p A) * (p - 1) := by
        simp [hfiber]
  have hnonone : Fintype.card NonOne = p ^ 2 - 1 := by
    letI := Fintype.ofFinite A
    have hcardA : Fintype.card A = p ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hA.card_eq
    rw [Fintype.card_subtype_compl (fun a : A ↦ a = 1)]
    simp [hcardA]
  have heq :
      Fintype.card (RankOneLines p A) * (p - 1) = p ^ 2 - 1 := by
    rw [← hpointed, ← hnonone]
    exact Fintype.card_congr e
  have hpPred : 0 < p - 1 := by
    exact Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hfactor : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    simpa using (Nat.sq_sub_sq p 1)
  rw [hfactor] at heq
  rw [Nat.card_eq_fintype_card]
  exact Nat.eq_of_mul_eq_mul_right hpPred heq

private theorem natCard_otherRankOneLines
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A Z : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hZ : RankOneLineIn p A Z) :
    Nat.card (OtherRankOneLines p A Z) = p := by
  classical
  letI := Fintype.ofFinite (RankOneLines p A)
  letI := Fintype.ofFinite (OtherRankOneLines p A Z)
  have hcompl :=
    Fintype.card_subtype_compl (fun X : RankOneLines p A ↦ X.1 = Z)
  have hzcard :
      Fintype.card {X : RankOneLines p A // X.1 = Z} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨Z, hZ⟩, rfl⟩, ?_⟩
    rintro ⟨X, hXZ⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hXZ
  have hall := natCard_rankOneLines hA
  rw [hzcard, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, hall] at hcompl
  simpa [OtherRankOneLines] using hcompl

private theorem map_conj_eq_self_of_mem_of_le_centerWithin
    {G : Type u} [Group G] [Finite G]
    {P Z : Subgroup G} (hZP : Z ≤ centerWithin P) {x : G} (hxP : x ∈ P) :
    Z.map (MulAut.conj x).toMonoidHom = Z := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨z, hz, rfl⟩
    have hcomm : Commute z x := ((hZP hz).2 x hxP).symm
    have hconj : MulAut.conj x z = z := by
      rw [MulAut.conj_apply, ← hcomm.eq]
      group
    simpa [hconj] using hz
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

@[reducible] private def otherRankOneLinesConjAction
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P A Z : Subgroup G)
    (hZA : RankOneLineIn p A Z) (hZP : Z ≤ centerWithin P) :
    MulAction ↥(P ⊓ Subgroup.normalizer (A : Set G))
      (OtherRankOneLines p A Z) where
  smul x X := by
    let e : G ≃* G := MulAut.conj (x : G)
    have hAmap : A.map e.toMonoidHom = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp x.2.2
    have hline : RankOneLineIn p A (X.1.1.map e.toMonoidHom) := by
      constructor
      · exact (Subgroup.map_mono X.1.2.1).trans_eq hAmap
      · exact X.1.2.2.map_of_injective e.toMonoidHom e.injective
    have hZmap : Z.map e.toMonoidHom = Z :=
      map_conj_eq_self_of_mem_of_le_centerWithin hZP x.2.1
    refine ⟨⟨X.1.1.map e.toMonoidHom, hline⟩, ?_⟩
    intro hEq
    apply X.2
    have hEqSub : X.1.1.map e.toMonoidHom = Z := hEq
    calc
      X.1.1 =
          (X.1.1.map e.toMonoidHom).map e.symm.toMonoidHom := by
            ext y
            simp
      _ = Z.map e.symm.toMonoidHom := by rw [hEqSub]
      _ = Z := by
        have hZsymm := congrArg
          (Subgroup.map e.symm.toMonoidHom) hZmap
        simpa [Subgroup.map_map] using hZsymm.symm
  one_smul X := by
    apply Subtype.ext
    apply Subtype.ext
    change X.1.1.map (MulAut.conj (1 : G)).toMonoidHom = X.1.1
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      simpa using hz
    · intro z hz
      exact ⟨z, hz, by simp⟩
  mul_smul x y X := by
    apply Subtype.ext
    apply Subtype.ext
    change X.1.1.map
        (MulAut.conj (((x * y : ↥(P ⊓ Subgroup.normalizer (A : Set G)))) : G)).toMonoidHom =
      (X.1.1.map (MulAut.conj (y : G)).toMonoidHom).map
        (MulAut.conj (x : G)).toMonoidHom
    rw [Subgroup.map_map]
    ext z
    simp [MulAut.conj_apply, mul_assoc]

private theorem normalizerWithin_le_centralizerWithin_of_card_eq_prime
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P L : Subgroup G}
    (hPp : IsPGroup p P) (hLP : L ≤ P) (hLcard : Nat.card L = p) :
    P ⊓ Subgroup.normalizer (L : Set G) ≤
      centralizerWithin P L := by
  let N : Subgroup G := P ⊓ Subgroup.normalizer (L : Set G)
  let LN : Subgroup N := L.subgroupOf N
  have hLN : L ≤ N := le_inf hLP Subgroup.le_normalizer
  letI : LN.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr inf_le_right
  have hLNcard : Nat.card LN = p := by
    rw [natCard_subgroupOf_eq hLN, hLcard]
  have hLNcenter : LN ≤ Subgroup.center N :=
    normal_le_center_of_card_eq_prime Fact.out
      (hPp.to_le inf_le_left) LN hLNcard
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro l hl
  let xN : N := ⟨x, hx⟩
  let lN : LN := ⟨⟨l, hLN hl⟩, hl⟩
  exact congrArg (fun z : N ↦ (z : G))
    (Subgroup.mem_center_iff.mp (hLNcenter lN.2) xN).symm

private theorem isMulCommutative_sup_of_commute
    {G : Type u} [Group G]
    {H K : Subgroup G} (hH : IsMulCommutative H)
    (hK : IsMulCommutative K)
    (hHK : ∀ h ∈ H, ∀ k ∈ K, Commute h k) :
    IsMulCommutative (H ⊔ K : Subgroup G) := by
  letI : IsMulCommutative H := hH
  letI : IsMulCommutative K := hK
  apply isMulCommutative_iff.mpr
  intro x y
  have hnorm : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    apply Subgroup.centralizer_le_normalizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hHK h hh k hk).eq.symm
  have hxprod : (x : G) ∈ (H : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H K hnorm]
    exact x.2
  have hyprod : (y : G) ∈ (H : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H K hnorm]
    exact y.2
  rcases hxprod with ⟨h₁, hh₁, k₁, hk₁, hx⟩
  rcases hyprod with ⟨h₂, hh₂, k₂, hk₂, hy⟩
  apply Subtype.ext
  change (x : G) * y = (y : G) * x
  rw [← hx, ← hy]
  have hh : Commute h₁ h₂ :=
    congrArg Subtype.val (mul_comm (⟨h₁, hh₁⟩ : H) ⟨h₂, hh₂⟩)
  have hkk : Commute k₁ k₂ :=
    congrArg Subtype.val (mul_comm (⟨k₁, hk₁⟩ : K) ⟨k₂, hk₂⟩)
  have hh₁k₂ := hHK h₁ hh₁ k₂ hk₂
  have hh₂k₁ := hHK h₂ hh₂ k₁ hk₁
  calc
    (h₁ * k₁) * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
    _ = h₁ * (h₂ * k₁) * k₂ := by rw [hh₂k₁.eq.symm]
    _ = (h₂ * k₂) * (h₁ * k₁) := by
      calc
        h₁ * (h₂ * k₁) * k₂ = (h₁ * h₂) * (k₁ * k₂) := by group
        _ = (h₂ * h₁) * (k₁ * k₂) := by rw [hh.eq]
        _ = (h₂ * h₁) * (k₂ * k₁) := by rw [hkk.eq]
        _ = h₂ * (h₁ * k₂) * k₁ := by group
        _ = h₂ * (k₂ * h₁) * k₁ := by rw [hh₁k₂.eq]
        _ = (h₂ * k₂) * (h₁ * k₁) := by group

private theorem basic_p2_decomposition
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] (Q : Sylow p G)
    {A : Subgroup G} (hA : IsElementaryAbelianOfRank p 2 A)
    (hAQ : A ≤ (Q : Subgroup G))
    (hAmax : IsPMaxElem p (Q : Subgroup G) A)
    (hQnoncomm : ¬ IsMulCommutative Q) :
    ∃ Z Y : Subgroup G,
      RankOneLineIn p A Z ∧
      Z ≤ centerWithin (Q : Subgroup G) ∧
      IsCyclic Y ∧
      Z ≤ Y ∧
      A ⊓ Y = Z ∧
      (∀ a ∈ A, ∀ y ∈ Y, Commute a y) ∧
      A ⊔ Y = centralizerWithin (Q : Subgroup G) A := by
  classical
  let AQ : Subgroup Q := A.subgroupOf (Q : Subgroup G)
  have hAQrank : IsElementaryAbelianOfRank p 2 AQ := hA.subgroupOf hAQ
  have hAQmax : IsPMaxElem p (⊤ : Subgroup Q) AQ := hAmax.subgroupOf_top
  by_cases hRank3 : ∃ E : Subgroup Q,
      IsElementaryAbelianOfRank p 3 E
  · have hOhm := Ohm1_ucn_p2maxElem Q.isPGroup'
      (mFT_odd (Q : Subgroup G)) hRank3 hAQrank hAQmax
    let ZQ : Subgroup Q := omegaOneCenter p Q
    have hZQcard : Nat.card ZQ = p := by
      simpa [ZQ] using hOhm.2.1
    have hZQrank : IsElementaryAbelianOfRank p 1 ZQ :=
      isElementaryAbelianOfRank_one_of_card_eq_prime hZQcard
    have hZQAQ : ZQ ≤ AQ := omegaOneCenter_le_of_pmaxElem hAQmax
    obtain ⟨XQ, hXQline, hXQne, hXQZdis, hXQZsup⟩ :=
      exists_complementary_rankOneLine hAQrank ⟨hZQAQ, hZQrank⟩
    have hCentXA :
        centralizerWithin (⊤ : Subgroup Q) XQ =
          centralizerWithin (⊤ : Subgroup Q) AQ := by
      apply le_antisymm
      · intro q hq
        refine ⟨trivial, ?_⟩
        intro a ha
        have hnorm : XQ ≤ Subgroup.normalizer (ZQ : Set Q) := by
          intro x _
          apply Subgroup.centralizer_le_normalizer (ZQ : Set Q)
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          exact (Subgroup.mem_center_iff.mp
            (omegaOneCenter_le_center p hz) x).symm
        have haProd : a ∈ (XQ : Set Q) * (ZQ : Set Q) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right XQ ZQ hnorm]
          rw [hXQZsup]
          exact ha
        rcases haProd with ⟨x, hx, z, hz, hxa⟩
        have hqx : Commute q x := (hq.2 x hx).symm
        have hqz : Commute q z :=
          (Subgroup.mem_center_iff.mp
            (omegaOneCenter_le_center p hz) q)
        rw [← hxa]
        exact (hqx.mul_right hqz).symm
      · intro q hq
        exact ⟨trivial, fun x hx ↦ hq.2 x (hXQline.1 hx)⟩
    have hNoCentRank3 :
        ¬ ∃ F : Subgroup Q,
          F ≤ centralizerWithin (⊤ : Subgroup Q) XQ ∧
            IsElementaryAbelianOfRank p 3 F := by
      rintro ⟨F, hFC, hF⟩
      have hTorsion :
          pTorsionCentralizerWithin p (⊤ : Subgroup Q) AQ =
            (AQ : Set Q) :=
        isPMaxElem_iff_pTorsionCentralizerWithin.mp hAQmax
      have hFAQ : F ≤ AQ := by
        intro f hf
        have hfC : f ∈ centralizerWithin (⊤ : Subgroup Q) AQ := by
          rw [← hCentXA]
          exact hFC hf
        have hfp : f ^ p = 1 :=
          congrArg Subtype.val (hF.pow_eq_one ⟨f, hf⟩)
        have hfT : f ∈
            pTorsionCentralizerWithin p (⊤ : Subgroup Q) AQ :=
          ⟨trivial, hfC.2, hfp⟩
        rw [hTorsion] at hfT
        exact hfT
      have hpows : p ^ 3 ≤ p ^ 2 := by
        rw [← hF.card_eq, ← hAQrank.card_eq]
        exact Subgroup.card_le_of_le hFAQ
      have : (3 : ℕ) ≤ 2 :=
        (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hpows
      omega
    have hNarrow : IsNarrow p (⊤ : Subgroup Q) := by
      intro _
      exact ⟨AQ, hAQrank, hAQmax⟩
    let TQ : Subgroup Q := omegaUpperCentralTwoCentralizer p Q
    let YQ : Subgroup Q := centralizerWithin TQ XQ
    have hDprod := narrow_cent_dprod Q.isPGroup' (mFT_odd (Q : Subgroup G))
      hRank3 hNarrow (by simpa using hXQline.2.card_eq) hNoCentRank3
    change IsCyclic YQ ∧
      Disjoint XQ (commutator Q) ∧
      Disjoint XQ TQ ∧
      Disjoint XQ YQ ∧
      (∀ x ∈ XQ, ∀ y ∈ YQ, Commute x y) ∧
      XQ ⊔ YQ = centralizerWithin (⊤ : Subgroup Q) XQ at hDprod
    rcases hDprod with
      ⟨hYQcyc, _hXder, _hXT, hXYdis, hXYcomm, hXYsup⟩
    have hZQYQ : ZQ ≤ YQ := by
      intro z hz
      refine ⟨?_, ?_⟩
      · change z ∈ omegaUpperCentralTwoCentralizer p Q
        rw [omegaUpperCentralTwoCentralizer,
          Subgroup.mem_centralizer_iff]
        intro w hw
        exact Subgroup.mem_center_iff.mp
          (omegaOneCenter_le_center p hz) w
      · intro x hx
        exact Subgroup.mem_center_iff.mp
          (omegaOneCenter_le_center p hz) x
    have hAQinfYQ : AQ ⊓ YQ = ZQ := by
      apply le_antisymm
      · intro a ha
        have hnorm : XQ ≤ Subgroup.normalizer (ZQ : Set Q) := by
          intro x _
          apply Subgroup.centralizer_le_normalizer (ZQ : Set Q)
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          exact (Subgroup.mem_center_iff.mp
            (omegaOneCenter_le_center p hz) x).symm
        have haProd : a ∈ (XQ : Set Q) * (ZQ : Set Q) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right XQ ZQ hnorm]
          rw [hXQZsup]
          exact ha.1
        rcases haProd with ⟨x, hx, z, hz, rfl⟩
        have hxY : x ∈ YQ := by
          have hmul := YQ.mul_mem ha.2 (YQ.inv_mem (hZQYQ hz))
          simpa [mul_assoc] using hmul
        have hxBot : x ∈ (XQ ⊓ YQ : Subgroup Q) := ⟨hx, hxY⟩
        rw [disjoint_iff.mp hXYdis] at hxBot
        have hxOne : x = 1 := by simpa using hxBot
        simpa [hxOne] using hz
      · exact le_inf hZQAQ hZQYQ
    have hAQsupYQ :
        AQ ⊔ YQ = centralizerWithin (⊤ : Subgroup Q) AQ := by
      calc
        AQ ⊔ YQ = (XQ ⊔ ZQ) ⊔ YQ := by rw [hXQZsup]
        _ = XQ ⊔ YQ := by
          rw [sup_assoc, sup_eq_right.mpr hZQYQ]
        _ = centralizerWithin (⊤ : Subgroup Q) XQ := hXYsup
        _ = centralizerWithin (⊤ : Subgroup Q) AQ := hCentXA
    let Z : Subgroup G := ZQ.map (Q : Subgroup G).subtype
    let Y : Subgroup G := YQ.map (Q : Subgroup G).subtype
    have hmapAQ : AQ.map (Q : Subgroup G).subtype = A := by
      exact Subgroup.map_subgroupOf_eq_of_le hAQ
    have hZrank : IsElementaryAbelianOfRank p 1 Z := by
      dsimp [Z]
      exact hZQrank.map_of_injective (Q : Subgroup G).subtype
        (Q : Subgroup G).subtype_injective
    have hZA : Z ≤ A := by
      dsimp [Z]
      rw [← hmapAQ]
      exact Subgroup.map_mono hZQAQ
    have hZcenter : Z ≤ centerWithin (Q : Subgroup G) := by
      dsimp [Z]
      simpa [omegaOneCenterAmbient] using
        (omegaOneCenterAmbient_le_centerWithin p (Q : Subgroup G))
    have hYcyc : IsCyclic Y := by
      let eY : YQ ≃* Y :=
        YQ.equivMapOfInjective (Q : Subgroup G).subtype
          (Q : Subgroup G).subtype_injective
      exact eY.isCyclic.mp hYQcyc
    have hZY : Z ≤ Y := Subgroup.map_mono hZQYQ
    have hAYinf : A ⊓ Y = Z := by
      have hmapped := congrArg (Subgroup.map (Q : Subgroup G).subtype) hAQinfYQ
      simpa [Z, Y, Subgroup.map_inf AQ YQ (Q : Subgroup G).subtype
        (Q : Subgroup G).subtype_injective, hmapAQ] using hmapped
    have hAYsup : A ⊔ Y = centralizerWithin (Q : Subgroup G) A := by
      have hmapped := congrArg (Subgroup.map (Q : Subgroup G).subtype) hAQsupYQ
      have hmapCent := map_centralizerWithin_subgroupOf
        (J := (Q : Subgroup G)) (V := (Q : Subgroup G)) (A := A)
        le_rfl hAQ
      have hmapCent' :
          (centralizerWithin (⊤ : Subgroup Q) AQ).map
              (Q : Subgroup G).subtype =
            centralizerWithin (Q : Subgroup G) A := by
        simpa [AQ] using hmapCent
      simpa [Y, Subgroup.map_sup, hmapAQ] using hmapped.trans hmapCent'
    have hAYcomm : ∀ a ∈ A, ∀ y ∈ Y, Commute a y := by
      intro a ha y hy
      have hyC : y ∈ centralizerWithin (Q : Subgroup G) A := by
        rw [← hAYsup]
        exact (le_sup_right : Y ≤ A ⊔ Y) hy
      exact hyC.2 a ha
    exact ⟨Z, Y, ⟨hZA, hZrank⟩, hZcenter, hYcyc, hZY,
      hAYinf, hAYcomm, hAYsup⟩
  · obtain ⟨S, C, hSnoncomm, hScard, hSexp, hCcent,
        hSCsup, hCcyc, hOmega⟩ :=
      mFT_rank2_Sylow_cprod Q hRank3 hQnoncomm
    have hSQ : S ≤ (Q : Subgroup G) := by
      rw [← hSCsup]
      exact le_sup_left
    have hCQ : C ≤ (Q : Subgroup G) := by
      rw [← hSCsup]
      exact le_sup_right
    have hSp : IsPGroup p S := Q.isPGroup'.to_le hSQ
    have hSextra : IsExtraspecial S :=
      isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
        hSp hScard hSnoncomm
    have hCenterCard : Nat.card (Subgroup.center S) = p :=
      hSextra.center_card_eq hSp
    let Z : Subgroup G := (Subgroup.center S).map S.subtype
    have hZcard : Nat.card Z = p := by
      dsimp [Z]
      rw [Subgroup.card_map_of_injective S.subtype_injective, hCenterCard]
    have hZrank : IsElementaryAbelianOfRank p 1 Z :=
      isElementaryAbelianOfRank_one_of_card_eq_prime hZcard
    have hZC : Z ≤ C := by
      dsimp [Z]
      rw [← hOmega]
      exact Subgroup.map_subtype_le (omegaOne p C)
    have hZS : Z ≤ S := Subgroup.map_subtype_le (Subgroup.center S)
    have hZcenterS : Z ≤ centerWithin S := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      intro s hs
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hz ⟨s, hs⟩)
    have hCcomm : IsMulCommutative C := by
      letI : IsCyclic C := hCcyc
      infer_instance
    have hSCcomm : ∀ s ∈ S, ∀ c ∈ C, Commute s c := by
      intro s hs c hc
      exact Subgroup.mem_centralizer_iff.mp (hCcent hc) s hs
    have hZcenterQ : Z ≤ centerWithin (Q : Subgroup G) := by
      intro z hz
      refine ⟨hZS.trans hSQ hz, ?_⟩
      intro q hq
      have hnorm : S ≤ Subgroup.normalizer (C : Set G) := by
        intro s hs
        apply Subgroup.centralizer_le_normalizer (C : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        exact (hSCcomm s hs c hc).eq.symm
      have hqProd : q ∈ (S : Set G) * (C : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right S C hnorm]
        rw [hSCsup]
        exact hq
      rcases hqProd with ⟨s, hs, c, hc, hqeq⟩
      have hzs : Commute z s := ((hZcenterS hz).2 s hs).symm
      have hzc : Commute z c := hSCcomm z (hZS hz) c hc
      rw [← hqeq]
      exact (hzs.mul_right hzc).symm
    have hZA : Z ≤ A := by
      have hTorsion :
          pTorsionCentralizerWithin p (Q : Subgroup G) A = (A : Set G) :=
        isPMaxElem_iff_pTorsionCentralizerWithin.mp hAmax
      intro z hz
      have hzp : z ^ p = 1 :=
        congrArg Subtype.val (hZrank.pow_eq_one ⟨z, hz⟩)
      have hzT : z ∈ pTorsionCentralizerWithin p (Q : Subgroup G) A :=
        ⟨(hZcenterQ hz).1, by
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          exact (hZcenterQ hz).2 a (hAQ ha), hzp⟩
      rw [hTorsion] at hzT
      exact hzT
    have hAS : A ≤ S := by
      intro a ha
      have haQ : a ∈ (Q : Subgroup G) := hAQ ha
      have hnorm : S ≤ Subgroup.normalizer (C : Set G) := by
        intro s hs
        apply Subgroup.centralizer_le_normalizer (C : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        exact (hSCcomm s hs c hc).eq.symm
      have haProd : a ∈ (S : Set G) * (C : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right S C hnorm]
        rw [hSCsup]
        exact haQ
      rcases haProd with ⟨s, hs, c, hc, haeq⟩
      have hsp : s ^ p = 1 := by
        exact congrArg Subtype.val
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hSexp ⟨s, hs⟩)
      have hap : a ^ p = 1 :=
        congrArg Subtype.val (hA.pow_eq_one ⟨a, ha⟩)
      have hcp : c ^ p = 1 := by
        have hsc := hSCcomm s hs c hc
        rw [← haeq, hsc.mul_pow, hsp, one_mul] at hap
        exact hap
      have hcOmega : (⟨c, hc⟩ : C) ∈ omegaOne p C :=
        mem_omegaOne_of_pow_eq_one p (Subtype.ext hcp)
      have hcZ : c ∈ Z := by
        change c ∈ (Subgroup.center S).map S.subtype
        rw [← hOmega]
        exact ⟨⟨c, hc⟩, hcOmega, rfl⟩
      rw [← haeq]
      exact S.mul_mem hs (hZS hcZ)
    let D : Subgroup G := centralizerWithin S A
    have hAD : A ≤ D := by
      intro a ha
      refine ⟨hAS ha, ?_⟩
      intro b hb
      letI : IsMulCommutative A := hA.commutative
      exact congrArg Subtype.val
        (mul_comm (⟨b, hb⟩ : A) ⟨a, ha⟩)
    have hDS : D ≤ S := centralizerWithin_le_left S A
    have hDp : IsPGroup p D := hSp.to_le hDS
    obtain ⟨n, hDcard⟩ := IsPGroup.iff_card.mp hDp
    have hnTwo : 2 ≤ n := by
      apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
      rw [← hA.card_eq, ← hDcard]
      exact Subgroup.card_le_of_le hAD
    have hnThree : n ≤ 3 := by
      apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
      rw [← hDcard, ← hScard]
      exact Subgroup.card_le_of_le hDS
    have hnNeThree : n ≠ 3 := by
      intro hn
      have hDS_eq : D = S := by
        apply Subgroup.eq_of_le_of_card_ge hDS
        rw [hDcard, hn, hScard]
      have hACenter : A ≤ Z := by
        intro a ha
        refine ⟨⟨a, hAS ha⟩, ?_, rfl⟩
        change (⟨a, hAS ha⟩ : S) ∈ Subgroup.center S
        rw [Subgroup.mem_center_iff]
        intro s
        have hsD : (s : G) ∈ D := by rw [hDS_eq]; exact s.2
        apply Subtype.ext
        change (s : G) * a = a * s
        exact (hsD.2 a ha).symm
      have hpows : p ^ 2 ≤ p := by
        rw [← hA.card_eq, ← hZcard]
        exact Subgroup.card_le_of_le hACenter
      have hpows' : p ^ 2 ≤ p ^ 1 := by simpa using hpows
      have : (2 : ℕ) ≤ 1 := by
        exact (Nat.pow_le_pow_iff_right
          (Fact.out : p.Prime).one_lt).mp hpows'
      omega
    have hn : n = 2 := by omega
    have hDA : D = A := by
      symm
      apply Subgroup.eq_of_le_of_card_ge hAD
      rw [hDcard, hn, hA.card_eq]
    have hSCinf : S ⊓ C = Z := by
      apply le_antisymm
      · intro x hx
        have hxCenter : (⟨x, hx.1⟩ : S) ∈ Subgroup.center S := by
          rw [Subgroup.mem_center_iff]
          intro s
          apply Subtype.ext
          change (s : G) * x = x * s
          exact hSCcomm s s.2 x hx.2
        exact ⟨⟨x, hx.1⟩, hxCenter, rfl⟩
      · exact le_inf hZS hZC
    have hACinf : A ⊓ C = Z := by
      apply le_antisymm
      · exact le_trans (inf_le_inf hAS le_rfl) (le_of_eq hSCinf)
      · exact le_inf hZA hZC
    have hACsup : A ⊔ C = centralizerWithin (Q : Subgroup G) A := by
      apply le_antisymm
      · apply sup_le
        · intro a ha
          refine ⟨hAQ ha, ?_⟩
          intro b hb
          letI : IsMulCommutative A := hA.commutative
          exact congrArg Subtype.val
            (mul_comm (⟨b, hb⟩ : A) ⟨a, ha⟩)
        · intro c hc
          refine ⟨hCQ hc, ?_⟩
          intro a ha
          exact hSCcomm a (hAS ha) c hc
      · intro x hx
        have hnorm : S ≤ Subgroup.normalizer (C : Set G) := by
          intro s hs
          apply Subgroup.centralizer_le_normalizer (C : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro c hc
          exact (hSCcomm s hs c hc).eq.symm
        have hxProd : x ∈ (S : Set G) * (C : Set G) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right S C hnorm]
          rw [hSCsup]
          exact hx.1
        rcases hxProd with ⟨s, hs, c, hc, hxeq⟩
        have hsD : s ∈ D := by
          refine ⟨hs, ?_⟩
          intro a ha
          have hxa : Commute x a := (hx.2 a ha).symm
          have hca : Commute c a := (hSCcomm a (hAS ha) c hc).symm
          have hEq : s = x * c⁻¹ := by rw [← hxeq]; group
          rw [hEq]
          exact (hxa.mul_left hca.inv_left).symm
        have hsA : s ∈ A := by rw [← hDA]; exact hsD
        rw [← hxeq]
        exact (A ⊔ C).mul_mem
          ((le_sup_left : A ≤ A ⊔ C) hsA)
          ((le_sup_right : C ≤ A ⊔ C) hc)
    exact ⟨Z, C, ⟨hZA, hZrank⟩, hZcenterQ, hCcyc, hZC,
      hACinf, (by
        intro a ha c hc
        exact hSCcomm a (hAS ha) c hc), hACsup⟩

/-! ### Bender--Glauberman Lemma 10.13 -/

set_option maxHeartbeats 1000000 in
/-- `BGsection10.v: basic_p2maxElem_structure`, Lemma 10.13.

The last component is the pairwise form of transitivity on the rank-one
subgroups of `A` other than `Ω₁(Z(P))`. -/
theorem basic_p2maxElem_structure
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] {A P : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hAmax : IsPMaxElem p (⊤ : Subgroup G) A)
    (hPp : IsPGroup p P) (hAP : A ≤ P)
    (hPnoncomm : ¬ IsMulCommutative P) :
    let Z₀ := omegaOneCenterAmbient p P
    IsElementaryAbelianOfRank p 1 Z₀ ∧
      (∃ Y : Subgroup G, IsCyclic Y ∧ Z₀ ≤ Y ∧
        ∀ A₀, RankOneLineIn p A A₀ → A₀ ≠ Z₀ →
          Disjoint A₀ Y ∧
          (∀ a ∈ A₀, ∀ y ∈ Y, Commute a y) ∧
          A₀ ⊔ Y = centralizerWithin P A) ∧
      (∀ A₁ A₂,
        RankOneLineIn p A A₁ → A₁ ≠ Z₀ →
        RankOneLineIn p A A₂ → A₂ ≠ Z₀ →
        ∃ x : G, x ∈ P ⊓ Subgroup.normalizer (A : Set G) ∧
          A₂ = A₁.map (MulAut.conj x⁻¹).toMonoidHom) := by
  classical
  let Z₀ : Subgroup G := omegaOneCenterAmbient p P
  have hAmaxP : IsPMaxElem p P A := hAmax.of_le le_top hAP
  obtain ⟨Q, hPQ⟩ := hPp.exists_le_sylow
  have hAQ : A ≤ (Q : Subgroup G) := hAP.trans hPQ
  have hAmaxQ : IsPMaxElem p (Q : Subgroup G) A :=
    hAmax.of_le le_top hAQ
  have hQnoncomm : ¬ IsMulCommutative Q := by
    intro hQcomm
    apply hPnoncomm
    letI : IsMulCommutative Q := hQcomm
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    exact congrArg (fun q : Q ↦ (q : G))
      (mul_comm (⟨(x : G), hPQ x.2⟩ : Q) ⟨(y : G), hPQ y.2⟩)
  obtain ⟨Z, YQ, hZline, hZcenterQ, hYQcyc, hZYQ,
      hAYQinf, hAYQcomm, hAYQsup⟩ :=
    basic_p2_decomposition Q hA hAQ hAmaxQ hQnoncomm
  have hZcenterP : Z ≤ centerWithin P := by
    intro z hz
    refine ⟨hZline.1.trans hAP hz, ?_⟩
    intro x hx
    exact (hZcenterQ hz).2 x (hPQ hx)
  have hZZ₀ : Z ≤ Z₀ := by
    intro z hz
    let zP : Subgroup.center P :=
      ⟨⟨z, (hZcenterP hz).1⟩, by
        rw [Subgroup.mem_center_iff]
        intro x
        apply Subtype.ext
        change (x : G) * z = z * x
        exact (hZcenterP hz).2 x x.2⟩
    have hzp : zP ^ p = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : Z ↦ (t : G))
        (hZline.2.pow_eq_one ⟨z, hz⟩)
    have hzOmega : (zP : P) ∈ omegaOneCenter p P :=
      ⟨zP, mem_omegaOne_of_pow_eq_one p hzp, rfl⟩
    exact ⟨(zP : P), hzOmega, rfl⟩
  have hZ₀P : Z₀ ≤ P := by
    intro z hz
    exact (omegaOneCenterAmbient_le_centerWithin p P hz).1
  have hZ₀centerP : Z₀ ≤ centerWithin P :=
    omegaOneCenterAmbient_le_centerWithin p P
  have hZ₀A : Z₀ ≤ A := by
    let AP : Subgroup P := A.subgroupOf P
    have hAPmax : IsPMaxElem p (⊤ : Subgroup P) AP :=
      hAmaxP.subgroupOf_top
    have hOmegaAP : omegaOneCenter p P ≤ AP :=
      omegaOneCenter_le_of_pmaxElem hAPmax
    intro z hz
    rcases hz with ⟨zP, hzP, rfl⟩
    exact hOmegaAP hzP
  have hCQcomm : IsMulCommutative (centralizerWithin (Q : Subgroup G) A) := by
    rw [← hAYQsup]
    have hAcomm : IsMulCommutative A := hA.commutative
    have hYcomm : IsMulCommutative YQ := by
      letI : IsCyclic YQ := hYQcyc
      infer_instance
    exact isMulCommutative_sup_of_commute hAcomm hYcomm hAYQcomm
  have hZ₀neA : Z₀ ≠ A := by
    intro hEq
    apply hPnoncomm
    have hPCQ : P ≤ centralizerWithin (Q : Subgroup G) A := by
      intro x hx
      refine ⟨hPQ hx, ?_⟩
      intro a ha
      have haZ : a ∈ Z₀ := by rw [hEq]; exact ha
      exact ((hZ₀centerP haZ).2 x hx).symm
    letI : IsMulCommutative (centralizerWithin (Q : Subgroup G) A) := hCQcomm
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    exact congrArg
      (fun q : centralizerWithin (Q : Subgroup G) A ↦ (q : G))
      (mul_comm
        (⟨(x : G), hPCQ x.2⟩ : centralizerWithin (Q : Subgroup G) A)
        ⟨(y : G), hPCQ y.2⟩)
  have hZ₀proper : Z₀ < A := lt_of_le_of_ne hZ₀A hZ₀neA
  have hZ₀p : IsPGroup p Z₀ := hPp.to_le hZ₀P
  obtain ⟨n, hZ₀cardPow⟩ := IsPGroup.iff_card.mp hZ₀p
  have hnPos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have hcardOne : Nat.card Z₀ = 1 := by rw [hZ₀cardPow, hn0, pow_zero]
    have hZ₀bot : Z₀ = ⊥ := Subgroup.eq_bot_of_card_eq Z₀ hcardOne
    have hZbot : Z = ⊥ := by
      apply le_bot_iff.mp
      rw [← hZ₀bot]
      exact hZZ₀
    exact hZline.2.ne_bot hZbot
  have hnLe : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    rw [← hZ₀cardPow, ← hA.card_eq]
    exact Subgroup.card_le_of_le hZ₀A
  have hnNeTwo : n ≠ 2 := by
    intro hn
    apply hZ₀neA
    apply Subgroup.eq_of_le_of_card_ge hZ₀A
    rw [hZ₀cardPow, hn, hA.card_eq]
  have hn : n = 1 := by omega
  have hZ₀card : Nat.card Z₀ = p := by
    rw [hZ₀cardPow, hn, pow_one]
  have hZ₀rank : IsElementaryAbelianOfRank p 1 Z₀ := by
    refine
      { isPGroup := hZ₀p
        commutative := ?_
        pow_eq_one := ?_
        card_eq := by simpa using hZ₀card }
    · apply isMulCommutative_iff.mpr
      intro x y
      apply Subtype.ext
      exact ((hZ₀centerP x.2).2 y (hZ₀P y.2)).symm
    · intro z
      rcases z.2 with ⟨zP, hzP, hz⟩
      apply Subtype.ext
      change (z : G) ^ p = 1
      rw [← hz]
      have hpP : zP ^ p = 1 := congrArg Subtype.val
        (omegaOneCenter_pow_eq_one p ⟨zP, hzP⟩)
      exact congrArg P.subtype hpP
  have hZZ₀eq : Z = Z₀ := by
    apply Subgroup.eq_of_le_of_card_ge hZZ₀
    rw [hZline.2.card_eq, hZ₀rank.card_eq]
  have hZ₀YQ : Z₀ ≤ YQ := by rw [← hZZ₀eq]; exact hZYQ
  have hAYQinf₀ : A ⊓ YQ = Z₀ := hAYQinf.trans hZZ₀eq
  let Y : Subgroup G := P ⊓ YQ
  have hYcyc : IsCyclic Y := by
    letI : IsCyclic YQ := hYQcyc
    let Y' : Subgroup YQ := Y.subgroupOf YQ
    have hY'cyc : IsCyclic Y' := inferInstance
    exact (Subgroup.subgroupOfEquivOfLe
      (show Y ≤ YQ from inf_le_right)).isCyclic.mp hY'cyc
  have hZ₀Y : Z₀ ≤ Y := le_inf hZ₀P hZ₀YQ
  have hCentPQ :
      centralizerWithin P A =
        P ⊓ centralizerWithin (Q : Subgroup G) A := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hPQ hx.1, hx.2⟩
    · intro hx
      exact ⟨hx.1, hx.2.2⟩
  have hProduct :
      ∀ A₀, RankOneLineIn p A A₀ → A₀ ≠ Z₀ →
        Disjoint A₀ Y ∧
        (∀ a ∈ A₀, ∀ y ∈ Y, Commute a y) ∧
        A₀ ⊔ Y = centralizerWithin P A := by
    intro A₀ hA₀ hA₀ne
    obtain ⟨hA₀Zdis, hA₀Zsup⟩ :=
      rankTwo_distinct_lines hA hA₀ ⟨hZ₀A, hZ₀rank⟩ hA₀ne
    have hA₀Ydis : Disjoint A₀ Y := by
      rw [disjoint_iff]
      apply le_antisymm
      · intro x hx
        have hxZ : x ∈ Z₀ := by
          rw [← hAYQinf₀]
          exact ⟨hA₀.1 hx.1, hx.2.2⟩
        have hxBot : x ∈ (A₀ ⊓ Z₀ : Subgroup G) := ⟨hx.1, hxZ⟩
        rw [disjoint_iff.mp hA₀Zdis] at hxBot
        exact hxBot
      · exact bot_le
    have hA₀Ycomm : ∀ a ∈ A₀, ∀ y ∈ Y, Commute a y := by
      intro a ha y hy
      exact hAYQcomm a (hA₀.1 ha) y hy.2
    have hAQsupYQ₀ : A ⊔ YQ = A₀ ⊔ YQ := by
      calc
        A ⊔ YQ = (A₀ ⊔ Z₀) ⊔ YQ := by rw [hA₀Zsup]
        _ = A₀ ⊔ YQ := by
          rw [sup_assoc, sup_eq_right.mpr hZ₀YQ]
    have hA₀normYQ : A₀ ≤ Subgroup.normalizer (YQ : Set G) := by
      intro a ha
      apply Subgroup.centralizer_le_normalizer (YQ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hAYQcomm a (hA₀.1 ha) y hy).eq.symm
    have hA₀Ysup : A₀ ⊔ Y = centralizerWithin P A := by
      rw [hCentPQ, ← hAYQsup, hAQsupYQ₀]
      symm
      apply le_antisymm
      · intro x hx
        have hxProd : x ∈ (A₀ : Set G) * (YQ : Set G) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right A₀ YQ hA₀normYQ]
          exact hx.2
        rcases hxProd with ⟨a, ha, y, hy, hxy⟩
        have haP : a ∈ P := hA₀.1.trans hAP ha
        have hyP : y ∈ P := by
          have hax : a⁻¹ * x ∈ P := P.mul_mem (P.inv_mem haP) hx.1
          have hay : a⁻¹ * x = y := by rw [← hxy]; group
          rwa [hay] at hax
        rw [← hxy]
        exact Subgroup.mul_mem_sup ha ⟨hyP, hy⟩
      · apply sup_le
        · intro a ha
          exact ⟨hA₀.1.trans hAP ha,
            (le_sup_left : A₀ ≤ A₀ ⊔ YQ) ha⟩
        · intro y hy
          exact ⟨hy.1, (le_sup_right : YQ ≤ A₀ ⊔ YQ) hy.2⟩
    exact ⟨hA₀Ydis, hA₀Ycomm, hA₀Ysup⟩
  have hTrans :
      ∀ A₁ A₂,
        RankOneLineIn p A A₁ → A₁ ≠ Z₀ →
        RankOneLineIn p A A₂ → A₂ ≠ Z₀ →
        ∃ x : G, x ∈ P ⊓ Subgroup.normalizer (A : Set G) ∧
          A₂ = A₁.map (MulAut.conj x⁻¹).toMonoidHom := by
    intro A₁ A₂ hA₁ hA₁ne hA₂ hA₂ne
    let N : Subgroup G := P ⊓ Subgroup.normalizer (A : Set G)
    let CP : Subgroup G := centralizerWithin P A
    have hCPN : CP ≤ N := by
      intro x hx
      exact ⟨hx.1, Subgroup.centralizer_le_normalizer (A : Set G) hx.2⟩
    let CPN : Subgroup N := CP.subgroupOf N
    let A₁o : OtherRankOneLines p A Z₀ := ⟨⟨A₁, hA₁⟩, hA₁ne⟩
    let A₂o : OtherRankOneLines p A Z₀ := ⟨⟨A₂, hA₂⟩, hA₂ne⟩
    letI : MulAction N (OtherRankOneLines p A Z₀) :=
      otherRankOneLinesConjAction P A Z₀ ⟨hZ₀A, hZ₀rank⟩ hZ₀centerP
    have hstab : MulAction.stabilizer N A₁o = CPN := by
      ext n
      constructor
      · intro hn
        have hmapA₁ :
            A₁.map (MulAut.conj (n : G)).toMonoidHom = A₁ := by
          have heq := congrArg
            (fun X : OtherRankOneLines p A Z₀ ↦ X.1.1) hn
          exact heq
        have hnNormA₁ : (n : G) ∈ Subgroup.normalizer (A₁ : Set G) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapA₁
        have hnCentA₁ : (n : G) ∈ centralizerWithin P A₁ :=
          normalizerWithin_le_centralizerWithin_of_card_eq_prime
            hPp (hA₁.1.trans hAP) (by simpa using hA₁.2.card_eq)
            ⟨n.2.1, hnNormA₁⟩
        obtain ⟨hA₁Zdis, hA₁Zsup⟩ :=
          rankTwo_distinct_lines hA hA₁ ⟨hZ₀A, hZ₀rank⟩ hA₁ne
        change (n : G) ∈ CP
        refine ⟨n.2.1, ?_⟩
        intro a ha
        have hnorm : A₁ ≤ Subgroup.normalizer (Z₀ : Set G) := by
          intro x hx
          apply Subgroup.centralizer_le_normalizer (Z₀ : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          letI : IsMulCommutative A := hA.commutative
          exact congrArg Subtype.val
            (mul_comm (⟨z, hZ₀A hz⟩ : A) ⟨x, hA₁.1 hx⟩)
        have haProd : a ∈ (A₁ : Set G) * (Z₀ : Set G) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right A₁ Z₀ hnorm]
          rw [hA₁Zsup]
          exact ha
        rcases haProd with ⟨a₁, ha₁, z, hz, haeq⟩
        have hna₁ : Commute (n : G) a₁ :=
          (hnCentA₁.2 a₁ ha₁).symm
        have hnz : Commute (n : G) z :=
          (hZ₀centerP hz).2 (n : G) n.2.1
        rw [← haeq]
        exact (hna₁.mul_right hnz).symm
      · intro hn
        have hnCP : (n : G) ∈ CP := hn
        have hnCentA₁ : (n : G) ∈ Subgroup.centralizer (A₁ : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          exact hnCP.2 a (hA₁.1 ha)
        have hnMap :
            A₁.map (MulAut.conj (n : G)).toMonoidHom = A₁ :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp
            (Subgroup.centralizer_le_normalizer (A₁ : Set G) hnCentA₁)
        apply Subtype.ext
        apply Subtype.ext
        exact hnMap
    have hCPcomm : IsMulCommutative CP := by
      have hCPQ : CP ≤ centralizerWithin (Q : Subgroup G) A := by
        intro x hx
        exact ⟨hPQ hx.1, hx.2⟩
      letI : IsMulCommutative (centralizerWithin (Q : Subgroup G) A) := hCQcomm
      apply isMulCommutative_iff.mpr
      intro x y
      apply Subtype.ext
      exact congrArg
        (fun q : centralizerWithin (Q : Subgroup G) A ↦ (q : G))
        (mul_comm
          (⟨(x : G), hCPQ x.2⟩ : centralizerWithin (Q : Subgroup G) A)
          ⟨(y : G), hCPQ y.2⟩)
    have hCPproper : CP < P := by
      refine lt_of_le_of_ne (centralizerWithin_le_left P A) ?_
      intro hEq
      apply hPnoncomm
      letI : IsMulCommutative CP := hCPcomm
      apply isMulCommutative_iff.mpr
      intro x y
      apply Subtype.ext
      exact congrArg (fun c : CP ↦ (c : G))
        (mul_comm
          (⟨(x : G), by rw [hEq]; exact x.2⟩ : CP)
          ⟨(y : G), by rw [hEq]; exact y.2⟩)
    have hNormCPN :
        P ⊓ Subgroup.normalizer (CP : Set G) ≤ N := by
      have hTorsion :
          pTorsionCentralizerWithin p P A = (A : Set G) :=
        isPMaxElem_iff_pTorsionCentralizerWithin.mp hAmaxP
      intro x hx
      refine ⟨hx.1, ?_⟩
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      have hCPmap : CP.map (MulAut.conj x).toMonoidHom = CP :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hx.2
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨a, ha, rfl⟩
        have haCP : a ∈ CP := ⟨hAP ha, by
          intro b hb
          letI : IsMulCommutative A := hA.commutative
          exact congrArg Subtype.val
            (mul_comm (⟨b, hb⟩ : A) ⟨a, ha⟩)⟩
        have haxCP : (MulAut.conj x) a ∈ CP := by
          rw [← hCPmap]
          exact Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom haCP
        have haxp : (MulAut.conj x a) ^ p = 1 := by
          simpa using congrArg (MulAut.conj x)
            (congrArg Subtype.val (hA.pow_eq_one ⟨a, ha⟩))
        have haxT : MulAut.conj x a ∈ pTorsionCentralizerWithin p P A :=
          ⟨haxCP.1, haxCP.2, haxp⟩
        rw [hTorsion] at haxT
        exact haxT
      · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    have hCPNproper : CP < N := by
      exact lt_of_lt_of_le
        (lt_inf_normalizer_of_isPGroup hPp hCPproper) hNormCPN
    have hstabProper : MulAction.stabilizer N A₁o < ⊤ := by
      rw [hstab]
      refine lt_of_le_of_ne le_top ?_
      intro htop
      have hNCP : N ≤ CP := by
        intro x hx
        have hxCPN : (⟨x, hx⟩ : N) ∈ CPN := by rw [htop]; trivial
        exact hxCPN
      exact (not_le_of_gt hCPNproper) hNCP
    have hNp : IsPGroup p N := hPp.to_le inf_le_left
    obtain ⟨k, hindexPow⟩ :=
      hNp.index (MulAction.stabilizer N A₁o)
    have hkPos : 0 < k := by
      by_contra hk
      have hk0 : k = 0 := by omega
      have hindexOne : (MulAction.stabilizer N A₁o).index = 1 := by
        rw [hindexPow, hk0, pow_zero]
      have htop : MulAction.stabilizer N A₁o = ⊤ :=
        Subgroup.index_eq_one.mp hindexOne
      exact hstabProper.ne htop
    have hOtherCard : Nat.card (OtherRankOneLines p A Z₀) = p :=
      natCard_otherRankOneLines hA ⟨hZ₀A, hZ₀rank⟩
    have hindexLe : (MulAction.stabilizer N A₁o).index ≤ p := by
      calc
        (MulAction.stabilizer N A₁o).index =
            (MulAction.orbit N A₁o).ncard :=
          MulAction.index_stabilizer N A₁o
        _ ≤ Nat.card (OtherRankOneLines p A Z₀) := Set.ncard_le_card _
        _ = p := hOtherCard
    have hpLeIndex : p ≤ (MulAction.stabilizer N A₁o).index := by
      rw [hindexPow]
      exact Nat.le_pow hkPos
    have hindex : (MulAction.stabilizer N A₁o).index = p :=
      le_antisymm hindexLe hpLeIndex
    have hOrbitCard : (MulAction.orbit N A₁o).ncard =
        Nat.card (OtherRankOneLines p A Z₀) := by
      rw [← MulAction.index_stabilizer N A₁o, hindex, hOtherCard]
    have hOrbitUniv : MulAction.orbit N A₁o = Set.univ :=
      (Set.eq_univ_iff_ncard (MulAction.orbit N A₁o)).mpr hOrbitCard
    have hA₂orbit : A₂o ∈ MulAction.orbit N A₁o := by
      rw [hOrbitUniv]
      trivial
    obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.mp hA₂orbit
    let x : G := (n : G)⁻¹
    refine ⟨x, ?_, ?_⟩
    · exact N.inv_mem n.2
    · have hmap := congrArg
          (fun X : OtherRankOneLines p A Z₀ ↦ X.1.1) hn
      change A₁.map (MulAut.conj (n : G)).toMonoidHom = A₂ at hmap
      simpa [x] using hmap.symm
  change IsElementaryAbelianOfRank p 1 Z₀ ∧
    (∃ Y : Subgroup G, IsCyclic Y ∧ Z₀ ≤ Y ∧
      ∀ A₀, RankOneLineIn p A A₀ → A₀ ≠ Z₀ →
        Disjoint A₀ Y ∧
        (∀ a ∈ A₀, ∀ y ∈ Y, Commute a y) ∧
        A₀ ⊔ Y = centralizerWithin P A) ∧ _
  exact ⟨hZ₀rank, ⟨Y, hYcyc, hZ₀Y, hProduct⟩, hTrans⟩

/-! ### Bender--Glauberman Proposition 10.14 -/

/-- `BGsection10.v: beta_not_narrow`, Proposition 10.14(a).

At an ambient beta prime there is no rank-two maximal elementary-abelian
subgroup, either in the full group or intrinsically in a Sylow subgroup. -/
theorem beta_not_narrow
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : p ∈ betaPrimes (⊤ : Subgroup G)) :
    (¬ ∃ A : Subgroup G,
        IsElementaryAbelianOfRank p 2 A ∧
          IsPMaxElem p (⊤ : Subgroup G) A) ∧
      ∀ P : Sylow p G,
        ¬ ∃ A : Subgroup P,
          IsElementaryAbelianOfRank p 2 A ∧
            IsPMaxElem p (⊤ : Subgroup P) A := by
  letI : Fact p.Prime := ⟨hp.1⟩
  constructor
  · rintro ⟨A, hA, hAmax⟩
    obtain ⟨P, hAP⟩ := hA.isPGroup.exists_le_sylow
    have hAmaxP : IsPMaxElem p (P : Subgroup G) A :=
      hAmax.of_le le_top hAP
    have hPnarrow : IsNarrow p (P : Subgroup G) := by
      intro _
      exact ⟨A, hA, hAmaxP⟩
    exact not_isNarrow_sylow_of_mem_beta_top hp P hPnarrow
  · intro P
    rintro ⟨A, hA, hAmax⟩
    have hPtop : IsNarrow p (⊤ : Subgroup P) := by
      intro _
      exact ⟨A, hA, hAmax⟩
    have hPambient : IsNarrow p (P : Subgroup G) :=
      (isNarrow_subgroup_iff_top (P : Subgroup G)).mpr hPtop
    exact not_isNarrow_sylow_of_mem_beta_top hp P hPambient

/-- `BGsection10.v: beta_noncyclic_uniq`, Proposition 10.14(b).

The source numerical hypothesis `'r(R) > 1` is represented by an exhibited
elementary-abelian rank-two subgroup of `R`. -/
theorem beta_noncyclic_uniq
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} (hp : p ∈ betaPrimes (⊤ : Subgroup G))
    {R : Subgroup G} (hRp : IsPGroup p R)
    (hRank : HasElementaryAbelianRankAtLeast p 2 R) :
    R ∈ minSimple_uniq_max_groups (G := G) := by
  letI : Fact p.Prime := ⟨hp.1⟩
  rcases hRank with ⟨A, hAR, hA⟩
  have hAnotmax : ¬ IsPMaxElem p (⊤ : Subgroup G) A := by
    intro hAmax
    exact (beta_not_narrow hp).1 ⟨A, hA, hAmax⟩
  have hAuniq : A ∈ minSimple_uniq_max_groups (G := G) :=
    nonmaxElem2_Uniqueness hA hAnotmax
  exact uniq_mmaxS hAR (mFT_pgroup_proper R hRp) hAuniq

/-- `BGsection10.v: beta_subnorm_uniq`, Proposition 10.14(c).

For a beta prime, the normalizer inside an ambient Sylow subgroup of every
subgroup has a unique maximal overgroup. -/
theorem beta_subnorm_uniq
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} (hp : p ∈ betaPrimes (⊤ : Subgroup G))
    (P : Sylow p G) {X : Subgroup G} (hXP : X ≤ (P : Subgroup G)) :
    ((P : Subgroup G) ⊓ Subgroup.normalizer (X : Set G)) ∈
      minSimple_uniq_max_groups (G := G) := by
  letI : Fact p.Prime := ⟨hp.1⟩
  let Q : Subgroup G :=
    (P : Subgroup G) ⊓ Subgroup.normalizer (X : Set G)
  have hQp : IsPGroup p Q := P.isPGroup'.to_le inf_le_left
  by_cases hRankQ : HasElementaryAbelianRankAtLeast p 2 Q
  · exact beta_noncyclic_uniq hp hQp hRankQ
  · have hNoRankQ :
        ¬ ∃ E : Subgroup Q, IsElementaryAbelianOfRank p 2 E := by
      rintro ⟨E, hE⟩
      let EG : Subgroup G := E.map Q.subtype
      have hEGQ : EG ≤ Q := Subgroup.map_subtype_le E
      have hEG : IsElementaryAbelianOfRank p 2 EG := by
        dsimp only [EG]
        exact hE.map_of_injective Q.subtype Q.subtype_injective
      exact hRankQ ⟨EG, hEGQ, hEG⟩
    have hQcyclic : IsCyclic Q :=
      (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
        hQp (mFT_odd Q)).mpr hNoRankQ
    letI : IsCyclic Q := hQcyclic
    have hXQ : X ≤ Q := by
      exact le_inf hXP Subgroup.le_normalizer
    let R : Subgroup Q := X.subgroupOf Q
    letI : R.Characteristic := subgroup_characteristic_of_isCyclic R
    have hNormQNormX :
        Subgroup.normalizer (Q : Set G) ≤
          Subgroup.normalizer (X : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro g hg x hx
      have hxR : x ∈ R.map Q.subtype := by
        simpa [R, Subgroup.map_subgroupOf_eq_of_le hXQ] using hx
      have hconj :=
        characteristic_map_subtype_invariant_under_normalizer
          Q (Subgroup.normalizer (Q : Set G)) R le_rfl
            g hg x hxR
      simpa [R, Subgroup.map_subgroupOf_eq_of_le hXQ] using hconj
    have hQP : Q ≤ (P : Subgroup G) := inf_le_left
    have hPQ : (P : Subgroup G) ≤ Q := by
      by_contra hnot
      have hQPproper : Q < (P : Subgroup G) :=
        lt_of_le_of_ne hQP (fun h ↦ hnot h.symm.le)
      have hgrowth :
          Q < (P : Subgroup G) ⊓
            Subgroup.normalizer (Q : Set G) :=
        lt_inf_normalizer_of_isPGroup P.isPGroup' hQPproper
      have hle :
          (P : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G) ≤ Q := by
        intro g hg
        exact ⟨hg.1, hNormQNormX hg.2⟩
      exact (not_le_of_gt hgrowth) hle
    have hPQeq : (P : Subgroup G) = Q := le_antisymm hPQ hQP
    have hRankThreeP :
        ∃ E : Subgroup G,
          E ≤ (P : Subgroup G) ∧
            IsElementaryAbelianOfRank p 3 E := by
      by_contra hnoRank
      apply not_isNarrow_sylow_of_mem_beta_top hp P
      intro hRank
      exact (hnoRank hRank).elim
    rcases hRankThreeP with ⟨E, hEP, hE⟩
    obtain ⟨A, hAE, hA⟩ := exists_rankTwo_le_of_rankThree hE
    exact (hRankQ ⟨A, hAE.trans (hEP.trans_eq hPQeq), hA⟩).elim

/-- `BGsection10.v: beta_norm_sub_mmax`, Proposition 10.14(d).

A nontrivial beta-subgroup of a maximal subgroup has its ambient normalizer
inside that maximal subgroup. -/
theorem beta_norm_sub_mmax
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M Y : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hYM : Y ≤ M)
    (hYbeta : IsPiNumber (betaPrimes M) (Nat.card Y))
    (hYne : Y ≠ ⊥) :
    Subgroup.normalizer (Y : Set G) ≤ M := by
  classical
  let F : Subgroup G := fittingWithin Y
  have hYproper : Y < ⊤ := lt_of_le_of_lt hYM (mmax_proper hM)
  have hYsol : IsSolvable Y := mFT_sol hYproper
  have hFne : F ≠ ⊥ := by
    intro hFbot
    apply hYne
    exact eq_bot_of_fittingWithin_eq_bot_of_isSolvable
      Y hYsol (by simpa [F] using hFbot)
  have hFcard : Nat.card F ≠ 1 :=
    (F.one_lt_card_iff_ne_bot.mpr hFne).ne'
  obtain ⟨q, hq, hqF⟩ := Nat.exists_prime_and_dvd hFcard
  letI : Fact q.Prime := ⟨hq⟩
  have hqY : q ∣ Nat.card Y :=
    hqF.trans (Subgroup.card_dvd_of_le (fittingWithin_le Y))
  have hqBetaM : q ∈ betaPrimes M := hYbeta hq hqY
  have hqPair :
      q ∈ sigmaPrimes M ∩ betaPrimes (⊤ : Subgroup G) := by
    rw [inter_sigma_beta_eq_beta hM]
    exact hqBetaM
  have hqBetaG : q ∈ betaPrimes (⊤ : Subgroup G) := hqPair.2
  let R : Subgroup Y := pCore q Y
  let X : Subgroup G := R.map Y.subtype
  have hqFcore : q ∣ Nat.card (fittingCore Y) := by
    have hcardF : Nat.card F = Nat.card (fittingCore Y) := by
      dsimp [F, fittingWithin]
      exact Subgroup.card_map_of_injective Y.subtype_injective
    rw [hcardF] at hqF
    exact hqF
  have hRne : R ≠ ⊥ := by
    let RF : Subgroup (fittingCore Y) := pCore q (fittingCore Y)
    have hRFne : RF ≠ ⊥ :=
      (pCore_ne_bot_iff_dvd_card_of_isNilpotent
        (G := fittingCore Y) q).2 hqFcore
    intro hRbot
    have hmapBot : RF.map (fittingCore Y).subtype = ⊥ := by
      rw [map_pCore_fittingCore_eq_pCore Y q]
      exact hRbot
    exact hRFne ((Subgroup.map_eq_bot_iff_of_injective
      RF (fittingCore Y).subtype_injective).mp hmapBot)
  have hXne : X ≠ ⊥ := by
    intro hXbot
    exact hRne ((Subgroup.map_eq_bot_iff_of_injective
      R Y.subtype_injective).mp hXbot)
  have hXY : X ≤ Y := Subgroup.map_subtype_le R
  have hXM : X ≤ M := hXY.trans hYM
  have hXp : IsPGroup q X := pCore_isPGroup.map Y.subtype
  let XM : Subgroup M := X.subgroupOf M
  have hXMp : IsPGroup q XM :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXM).symm
  obtain ⟨P, hXMP⟩ := hXMp.exists_le_sylow
  let PG : Subgroup G := ambientSylow M P
  have hXPG : X ≤ PG := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXM]
    exact Subgroup.map_mono hXMP
  have hqSigmaM : q ∈ sigmaPrimes M := beta_sub_sigma hM hqBetaM
  obtain ⟨Q, hQPG⟩ := sigma_Sylow_G hM hqSigmaM P
  have hXQ : X ≤ (Q : Subgroup G) := by
    rwa [hQPG]
  let NQ : Subgroup G :=
    (Q : Subgroup G) ⊓ Subgroup.normalizer (X : Set G)
  have hNQuniq : NQ ∈ minSimple_uniq_max_groups (G := G) := by
    simpa [NQ] using beta_subnorm_uniq hqBetaG Q hXQ
  have hQleM : (Q : Subgroup G) ≤ M := by
    rw [hQPG]
    exact Subgroup.map_subtype_le (P : Subgroup M)
  have hNQM : NQ ≤ M := inf_le_left.trans hQleM
  have hNQfamily :
      minSimple_max_groups_of (G := G) (NQ : Set G) = {M} :=
    def_uniq_mmax hNQuniq hM hNQM
  have hNormYNormX :
      Subgroup.normalizer (Y : Set G) ≤
        Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg x hx
    have hxR : x ∈ R.map Y.subtype := by simpa [X] using hx
    have hconj :=
      characteristic_map_subtype_invariant_under_normalizer
        Y (Subgroup.normalizer (Y : Set G)) R le_rfl
          g hg x hxR
    simpa [X] using hconj
  have hNormXproper : Subgroup.normalizer (X : Set G) < ⊤ :=
    mFT_norm_proper X hXne (mFT_pgroup_proper X hXp)
  have hNormXM : Subgroup.normalizer (X : Set G) ≤ M :=
    sub_uniq_mmax hNQfamily inf_le_right hNormXproper
  exact hNormYNormX.trans hNormXM

end

end Submission.OddOrder.BG.Section10
