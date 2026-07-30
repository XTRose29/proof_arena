import Submission.OddOrder.BG.Section01.CriticalOdd
import Submission.OddOrder.BG.Section04.OddPGroupRankOne
import Submission.OddOrder.BG.Section04.RankTwoDerivedComplement
import Submission.OddOrder.BG.Section04.RankTwoPrimeDivisors
import Submission.OddOrder.BG.Section05.NarrowCentralizerCharacterization
import Submission.OddOrder.BG.Section05.NormalRankTwoSCNRankThree
import Submission.OddOrder.MathlibSupport.CoprimeCentralFixedPoint
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRankSylowTransport
import Submission.OddOrder.MathlibSupport.NilpotentNormalCommutator
import Submission.OddOrder.MathlibSupport.PCoreSelfQuotient
import Submission.OddOrder.MathlibSupport.PGroupCenter
import Submission.OddOrder.MathlibSupport.PGroupMapKernel
import Submission.OddOrder.MathlibSupport.PGroupPrimeOrderCriterion
import Submission.OddOrder.MathlibSupport.PLengthOne
import Submission.OddOrder.MathlibSupport.PPrimeCoreDerivedHall
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient

/-!
# Narrow p-groups: automorphisms and the derived complement

This file ports Bender--Glauberman Theorems 5.5(a,b) and 5.6(a,c).
The numerical rank conditions in the source are expressed, as elsewhere in
this port, by the existence or nonexistence of an elementary-abelian subgroup
of rank three.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative commutatorElement Pointwise

noncomputable section

universe u

private theorem mulAut_isMulCommutative_of_isCyclic
    {X : Type*} [Group X] [IsCyclic X] :
    IsMulCommutative (MulAut X) := by
  apply isMulCommutative_iff.mpr
  intro a b
  obtain ⟨m, hm⟩ := a.toMonoidHom.map_cyclic
  obtain ⟨n, hn⟩ := b.toMonoidHom.map_cyclic
  apply MulEquiv.ext
  intro x
  change a (b x) = b (a x)
  calc
    a (b x) = (b x) ^ m := hm (b x)
    _ = (x ^ n) ^ m := by
      exact congrArg (fun z : X ↦ z ^ m) (by simpa using hn x)
    _ = x ^ (n * m) := (zpow_mul x n m).symm
    _ = x ^ (m * n) := by rw [mul_comm]
    _ = (x ^ m) ^ n := zpow_mul x m n
    _ = b (a x) := by
      simpa [show a x = x ^ m by simpa using hm x] using
        (hn (a x)).symm

private theorem quotient_pCore_properties_of_commutator_isPGroup
    {A : Type*} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime]
    (hderived : IsPGroup p (_root_.commutator A)) :
    IsPPrimeSubgroup p
        (⊤ : Subgroup (A ⧸ pCore p A)) ∧
      IsMulCommutative (A ⧸ pCore p A) := by
  have hderivedCore : _root_.commutator A ≤ pCore p A :=
    le_pCore hderived (by infer_instance)
  have hcomm : IsMulCommutative (A ⧸ pCore p A) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      hderivedCore
  letI : IsMulCommutative (A ⧸ pCore p A) := hcomm
  letI : Group.IsNilpotent (A ⧸ pCore p A) := by infer_instance
  have hnot : ¬ p ∣ Nat.card (A ⧸ pCore p A) :=
    not_dvd_natCard_of_pCore_eq_bot_of_isNilpotent
      (pCore_quotient_pCore_eq_bot (G := A) (p := p))
  refine ⟨?_, hcomm⟩
  rw [IsPPrimeSubgroup, Subgroup.card_top]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnot

private theorem isNarrow_subgroup_iff_top
    {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime]
    (A : Subgroup G) :
    IsNarrow p A ↔ IsNarrow p (⊤ : Subgroup A) := by
  have hiff := isNarrow_map_iff_of_injective
    (p := p) A.subtype A.subtype_injective (⊤ : Subgroup A)
  have hmapTop :
      (⊤ : Subgroup A).map A.subtype = A := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hmapTop] at hiff
  exact hiff

private theorem exists_elementaryAbelian_rank_three_in_sylow
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p G)
    (hRank3 : ∃ E : Subgroup G,
      IsElementaryAbelianOfRank p 3 E) :
    ∃ E : Subgroup S, IsElementaryAbelianOfRank p 3 E := by
  obtain ⟨E, hE⟩ := hRank3
  obtain ⟨P, hEP⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  let c : G →* G := (MulAut.conj g).toMonoidHom
  let F : Subgroup G := E.map c
  have hmapP : (P : Subgroup G).map c = (S : Subgroup G) := by
    change MulAut.conj g • (P : Subgroup G) = (S : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hg]
  have hFS : F ≤ (S : Subgroup G) := by
    exact (Subgroup.map_mono hEP).trans_eq hmapP
  have hF : IsElementaryAbelianOfRank p 3 F := by
    dsimp only [F, c]
    exact hE.map_of_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
  exact ⟨F.subgroupOf (S : Subgroup G), hF.subgroupOf hFS⟩

/-- The critical subgroup used in the high-rank branch meets the narrow
prime subgroup trivially, and its centralizer there has order `p`. -/
private theorem critical_centralizer_card_eq_prime
    {R : Type u} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) (hoddR : Odd (Nat.card R))
    (hRank3 : ∃ E : Subgroup R,
      IsElementaryAbelianOfRank p 3 E)
    (hNarrow : IsNarrow p (⊤ : Subgroup R))
    {H S : Subgroup R}
    (hHchar : H.Characteristic)
    (hHcomm : ⁅H, (⊤ : Subgroup R)⁆ ≤ centerWithin H)
    (hHexp : Monoid.exponent H = p)
    (hScard : Nat.card S = p)
    (hCentRank : ¬ ∃ F : Subgroup R,
      F ≤ centralizerWithin (⊤ : Subgroup R) S ∧
        IsElementaryAbelianOfRank p 3 F) :
    Disjoint S H ∧ Nat.card (centralizerWithin H S) = p := by
  classical
  letI : H.Characteristic := hHchar
  letI : H.Normal := by infer_instance
  letI : IsCyclic S := isCyclic_of_prime_card hScard
  letI : IsMulCommutative S := inferInstance

  have hHne : H ≠ ⊥ := by
    intro hHbot
    haveI : Subsingleton H :=
      ⟨fun x y ↦ by
        apply Subtype.ext
        have hx : (x : R) = 1 := by
          apply Subgroup.mem_bot.mp
          rw [← hHbot]
          exact x.property
        have hy : (y : R) = 1 := by
          apply Subgroup.mem_bot.mp
          rw [← hHbot]
          exact y.property
        exact hx.trans hy.symm⟩
    have hExpOne : Monoid.exponent H = 1 :=
      Monoid.exp_eq_one_of_subsingleton
    exact (Fact.out : p.Prime).ne_one (hHexp.symm.trans hExpOne)

  have hSHdis : Disjoint S H := by
    rw [disjoint_iff]
    by_contra hInfNe
    have hcardInfDvd : Nat.card (S ⊓ H : Subgroup R) ∣ p := by
      rw [← hScard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hcardInfDvd with
      hcardOne | hcardP
    · apply hInfNe
      exact Subgroup.eq_bot_of_card_eq (S ⊓ H : Subgroup R) hcardOne
    · have hInfEq : S ⊓ H = S := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_left
        rw [hcardP, hScard]
      have hSH : S ≤ H := by
        intro s hs
        have hsInf : s ∈ S ⊓ H := by rw [hInfEq]; exact hs
        exact hsInf.2
      let Z : Subgroup R := centerWithin H
      let U : Subgroup R := S ⊔ Z
      have hUH : U ≤ H := sup_le hSH
        (centralizerWithin_le_left H H)
      have hUclosure :
          U = Subgroup.closure ((S : Set R) ∪ (Z : Set R)) := by
        apply le_antisymm
        · apply sup_le
          · exact fun x hx ↦ Subgroup.subset_closure (Or.inl hx)
          · exact fun x hx ↦ Subgroup.subset_closure (Or.inr hx)
        · rw [Subgroup.closure_le]
          rintro x (hx | hx)
          · exact (show S ≤ U from le_sup_left) hx
          · exact (show Z ≤ U from le_sup_right) hx
      have hUcomm : IsMulCommutative U := by
        rw [hUclosure]
        apply Subgroup.isMulCommutative_closure
        intro x hx y hy
        rcases hx with hxS | hxZ <;> rcases hy with hyS | hyZ
        · exact congrArg Subtype.val
            (mul_comm (⟨x, hxS⟩ : S) ⟨y, hyS⟩)
        · exact (mem_centerWithin.mp hyZ).2 x (hSH hxS)
        · exact ((mem_centerWithin.mp hxZ).2 y (hSH hyS)).symm
        · letI : IsMulCommutative Z := by dsimp [Z]; infer_instance
          exact congrArg Subtype.val
            (mul_comm (⟨x, hxZ⟩ : Z) ⟨y, hyZ⟩)
      have hUpow : ∀ x : U, x ^ p = 1 := by
        intro x
        let xH : H := ⟨(x : R), hUH x.property⟩
        apply Subtype.ext
        exact congrArg (fun z : H ↦ (z : R)) (by
          simpa [hHexp] using Monoid.pow_exponent_eq_one xH)
      have hUelem : IsElementaryAbelianGroup p U :=
        { isPGroup := hR.to_subgroup U
          commutative := hUcomm
          pow_eq_one := hUpow }
      have hUnormal : U.Normal := by
        apply Subgroup.normalizer_eq_top_iff.mp
        apply top_unique
        rw [Subgroup.le_normalizer_iff_commutator_le_right,
          Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono hUH le_rfl).trans
          (hHcomm.trans le_sup_right)
      letI : U.Normal := hUnormal
      have hUcent : U ≤ centralizerWithin (⊤ : Subgroup R) S := by
        intro u hu
        refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
        intro s hs
        exact congrArg Subtype.val
          (mul_comm (⟨s, (show S ≤ U from le_sup_left) hs⟩ : U)
            ⟨u, hu⟩)
      obtain ⟨n, hUcard⟩ := hUelem.isPGroup.exists_card_eq
      have hnPos : 1 ≤ n := by
        have hpLe : p ≤ p ^ n := by
          calc
            p = Nat.card S := hScard.symm
            _ ≤ Nat.card U := Subgroup.card_le_of_le le_sup_left
            _ = p ^ n := hUcard
        by_contra hn
        have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        rw [hn0, pow_zero] at hpLe
        have hpOneLt := (Fact.out : p.Prime).one_lt
        omega
      have hnLe : n ≤ 2 := by
        by_contra hn
        have hthree : 3 ≤ n := by omega
        obtain ⟨F, hFU, _hFnormal, hFcard⟩ :=
          exists_normal_subgroup_card_pow_le hR U hUcard hthree
        have hFcomm : IsMulCommutative F := by
          apply isMulCommutative_iff.mpr
          intro x y
          apply Subtype.ext
          exact congrArg (fun z : U ↦ (z : R))
            (mul_comm (⟨x, hFU x.property⟩ : U)
              ⟨y, hFU y.property⟩)
        have hFpow : ∀ x : F, x ^ p = 1 := by
          intro x
          apply Subtype.ext
          exact congrArg (fun z : U ↦ (z : R))
            (hUpow ⟨x, hFU x.property⟩)
        apply hCentRank
        exact ⟨F, hFU.trans hUcent,
          { isPGroup := hR.to_subgroup F
            commutative := hFcomm
            pow_eq_one := hFpow
            card_eq := hFcard }⟩
      have hn : n = 1 ∨ n = 2 := by omega
      rcases hn with hn | hn
      · have hUcardP : Nat.card U = p := by simpa [hn] using hUcard
        have hSU : S = U := by
          apply Subgroup.eq_of_le_of_card_ge le_sup_left
          rw [hScard, hUcardP]
        have hSnormal : S.Normal := by rw [hSU]; infer_instance
        letI : S.Normal := hSnormal
        have hScenter : S ≤ Subgroup.center R :=
          normal_le_center_of_card_eq_prime
            (Fact.out : p.Prime) hR S hScard
        obtain ⟨E, hE⟩ := hRank3
        apply hCentRank
        refine ⟨E, ?_, hE⟩
        intro e he
        refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
        intro s hs
        exact (Subgroup.mem_center_iff.mp (hScenter hs) e).symm
      · have hUrank : IsElementaryAbelianOfRank p 2 U :=
          { toIsElementaryAbelianGroup := hUelem
            card_eq := by simpa [hn] using hUcard }
        obtain ⟨C, hC, hUC⟩ :=
          normal_p2Elem_SCN3 hR hoddR hRank3 hUrank hUnormal
        rcases hC with ⟨hCscn, F, hFC, hF⟩
        apply hCentRank
        refine ⟨F, ?_, hF⟩
        intro f hf
        refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
        intro s hs
        have hsC : s ∈ C := hUC
          ((show S ≤ U from le_sup_left) hs)
        letI : IsMulCommutative C := hCscn.commutative
        exact congrArg Subtype.val
          (mul_comm (⟨s, hsC⟩ : C) ⟨f, hFC hf⟩)

  let X : Subgroup R := centralizerWithin H S
  have hXne : X ≠ ⊥ := by
    have hInfNe := normal_inf_center_ne_bot hR H hHne
    intro hXbot
    apply hInfNe
    apply le_bot_iff.mp
    rw [← hXbot]
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro s _hs
    exact Subgroup.mem_center_iff.mp hx.2 s
  have hXp : IsPGroup p X := hR.to_subgroup X
  have hXodd : Odd (Nat.card X) := odd_natCard_subgroup X hoddR
  have hXcyclic : IsCyclic X := by
    apply (Submission.OddOrder.BG.Section04.odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
      hXp hXodd).mpr
    rintro ⟨E, hE⟩
    let ER : Subgroup R := E.map X.subtype
    have hER : IsElementaryAbelianOfRank p 2 ER := by
      dsimp only [ER]
      exact hE.map_of_injective X.subtype X.subtype_injective
    have hERH : ER ≤ H := by
      exact (Subgroup.map_subtype_le E).trans (centralizerWithin_le_left H S)
    have hSERdis : Disjoint S ER := hSHdis.mono_right hERH
    have hSERcomm : ∀ s ∈ S, ∀ e ∈ ER, Commute s e := by
      intro s hs e he
      have heX : e ∈ X := Subgroup.map_subtype_le E he
      exact (mem_centralizerWithin.mp heX).2 s hs
    have hSrank : IsElementaryAbelianOfRank p 1 S :=
      isElementaryAbelianOfRank_one_of_card_eq_prime hScard
    have hSup : IsElementaryAbelianOfRank p 3 (S ⊔ ER) := by
      simpa using isElementaryAbelianOfRank_sup_of_disjoint_of_commute
        hR hSrank hER hSERdis hSERcomm
    apply hCentRank
    refine ⟨S ⊔ ER, ?_, hSup⟩
    apply sup_le
    · intro s hs
      refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
      intro t ht
      exact congrArg Subtype.val
        (mul_comm (⟨t, ht⟩ : S) ⟨s, hs⟩)
    · intro e he
      have heX : e ∈ X := Subgroup.map_subtype_le E he
      exact ⟨trivial, (mem_centralizerWithin.mp heX).2⟩
  letI : IsCyclic X := hXcyclic
  letI : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hXne
  have hXpow : ∀ x : X, x ^ p = 1 := by
    intro x
    let xH : H := ⟨(x : R), (centralizerWithin_le_left H S) x.property⟩
    apply Subtype.ext
    exact congrArg (fun z : H ↦ (z : R)) (by
      simpa [hHexp] using Monoid.pow_exponent_eq_one xH)
  have hXexp : Monoid.exponent X = p :=
    (Monoid.exponent_eq_prime_iff (Fact.out : p.Prime)).mpr
      (fun x hx ↦ orderOf_eq_prime (hXpow x) hx)
  refine ⟨hSHdis, ?_⟩
  change Nat.card X = p
  calc
    Nat.card X = Monoid.exponent X := IsCyclic.exponent_eq_card.symm
    _ = p := hXexp

/-- If `L` is a nontrivial characteristic subgroup of the critical subgroup,
then `L / [L,R]` has order `p`.  The orbit of a generator of `S` bounds the
centralizer index by the size of `[L,R]`. -/
private theorem characteristic_commutator_factor_card_eq_prime
    {R : Type u} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R)
    {H S L : Subgroup R}
    (hSHdis : Disjoint S H)
    (hScard : Nat.card S = p)
    (hCentCard : Nat.card (centralizerWithin H S) = p)
    (hLchar : L.Characteristic) (hLH : L ≤ H) (hLne : L ≠ ⊥) :
    let K₀ : Subgroup R := ⁅L, (⊤ : Subgroup R)⁆
    let K : Subgroup L := K₀.subgroupOf L
    Nat.card (L ⧸ K) = p := by
  classical
  letI : Group.IsNilpotent R := hR.isNilpotent
  letI : L.Characteristic := hLchar
  letI : L.Normal := by infer_instance
  letI : IsCyclic S := isCyclic_of_prime_card hScard
  letI : IsMulCommutative S := inferInstance
  letI : Nontrivial S := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hScard]
    exact (Fact.out : p.Prime).one_lt
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  let sR : R := (s : R)
  let K₀ : Subgroup R := ⁅L, (⊤ : Subgroup R)⁆
  have hK₀char : K₀.Characteristic := by
    dsimp only [K₀]
    infer_instance
  letI : K₀.Characteristic := hK₀char
  letI : K₀.Normal := by infer_instance
  have hK₀L : K₀ ≤ L := Subgroup.commutator_le_left L ⊤
  let K : Subgroup L := K₀.subgroupOf L
  letI : K.Normal := (inferInstance : K₀.Normal).subgroupOf L
  let CL₀ : Subgroup R := centralizerWithin L S
  let CL : Subgroup L := CL₀.subgroupOf L
  let act : L →* MulAut R := MulAut.conj.comp L.subtype
  letI : MulAction L R := MulAction.compHom R act
  have hsmul (l : L) (x : R) :
      l • x = (l : R) * x * (l : R)⁻¹ := by
    calc
      l • x = (act l) • x :=
        MulAction.compHom_smul_def act l x
      _ = (act l) x := MulAut.smul_def (act l) x
      _ = (l : R) * x * (l : R)⁻¹ := rfl
  have hstab : MulAction.stabilizer L sR = CL := by
    ext l
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hl
      change (l : R) ∈ CL₀
      refine mem_centralizerWithin.mpr ⟨l.property, ?_⟩
      intro y hy
      have hconj : (l : R) * sR * (l : R)⁻¹ = sR := by
        rw [hsmul] at hl
        exact hl
      have hcomm : Commute (l : R) sR := by
        change (l : R) * sR = sR * (l : R)
        calc
          (l : R) * sR = ((l : R) * sR * (l : R)⁻¹) * (l : R) := by
            group
          _ = sR * (l : R) := by rw [hconj]
      let yS : S := ⟨y, hy⟩
      have hygen : yS ∈ Subgroup.zpowers s :=
        mem_zpowers_of_prime_card hScard hs
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hygen
      change Commute y (l : R)
      have hz := (hcomm.zpow_right n).symm
      have hnR : sR ^ n = y :=
        congrArg (fun z : S ↦ (z : R)) hn
      rw [hnR] at hz
      exact hz
    · intro hl
      change (l : R) ∈ CL₀ at hl
      have hcomm : Commute (l : R) sR :=
        ((mem_centralizerWithin.mp hl).2 sR s.property).symm
      change l • sR = sR
      rw [hsmul]
      exact hcomm.mul_inv_cancel
  let O : Set R := MulAction.orbit L sR
  let f : O → K₀ := fun y ↦
    ⟨(y : R) * sR⁻¹, by
      obtain ⟨l, hl⟩ := MulAction.mem_orbit_iff.mp y.property
      have hlR : (l : R) * sR * (l : R)⁻¹ = (y : R) := by
        rw [hsmul] at hl
        exact hl
      rw [← hlR]
      simpa [K₀, commutatorElement_def] using
        (Subgroup.commutator_mem_commutator l.property
          (show sR ∈ (⊤ : Subgroup R) by trivial))⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxyR := congrArg (fun z : K₀ ↦ (z : R)) hxy
    change (x : R) * sR⁻¹ = (y : R) * sR⁻¹ at hxyR
    exact mul_right_cancel hxyR
  have hOrbitCard : O.ncard ≤ Nat.card K₀ := by
    simpa [Nat.card_coe_set_eq] using
      (Nat.card_le_card_of_injective f hfinj)
  have hCLindex : CL.index ≤ Nat.card K₀ := by
    rw [← hstab]
    exact (MulAction.index_stabilizer L sR).trans_le hOrbitCard
  have hCL₀X : CL₀ ≤ centralizerWithin H S := by
    intro x hx
    exact ⟨hLH hx.1, hx.2⟩
  have hCLcard : Nat.card CL ≤ p := by
    calc
      Nat.card CL = Nat.card CL₀ :=
        natCard_subgroupOf_eq (centralizerWithin_le_left L S)
      _ ≤ Nat.card (centralizerWithin H S) :=
        Subgroup.card_le_of_le hCL₀X
      _ = p := hCentCard
  have hKcard : Nat.card K = Nat.card K₀ :=
    natCard_subgroupOf_eq hK₀L
  have hKindexCL : K.index ≤ Nat.card CL := by
    have hmul : Nat.card K * K.index ≤ Nat.card K * Nat.card CL := by
      calc
        Nat.card K * K.index = Nat.card L := K.card_mul_index
        _ = Nat.card CL * CL.index := CL.card_mul_index.symm
        _ ≤ Nat.card CL * Nat.card K₀ :=
          Nat.mul_le_mul_left (Nat.card CL) hCLindex
        _ = Nat.card K * Nat.card CL := by
          rw [hKcard, Nat.mul_comm]
    exact Nat.le_of_mul_le_mul_left hmul Nat.card_pos
  have hKlt : K₀ < L :=
    commutator_top_lt_of_normal_ne_bot hLne
  have hKneTop : K ≠ ⊤ := by
    intro hKtop
    apply hKlt.ne
    apply le_antisymm hK₀L
    intro x hx
    have hxK : (⟨x, hx⟩ : L) ∈ K := by rw [hKtop]; trivial
    exact hxK
  letI : Nontrivial (L ⧸ K) :=
    QuotientGroup.nontrivial_iff.mpr hKneTop
  have hQp : IsPGroup p (L ⧸ K) :=
    (hR.to_subgroup L).to_quotient K
  have hQcardLe : Nat.card (L ⧸ K) ≤ p := by
    rw [← K.index_eq_card]
    exact hKindexCL.trans hCLcard
  have hQcardNe : Nat.card (L ⧸ K) ≠ 1 :=
    (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne'
  have hpQ : p ∣ Nat.card (L ⧸ K) :=
    hQp.card_eq_or_dvd.resolve_left hQcardNe
  exact Nat.le_antisymm hQcardLe
    (Nat.le_of_dvd Nat.card_pos hpQ)

/-- `BGsection5.v: Aut_narrow` (Bender--Glauberman Theorem 5.5(a,b)). -/
theorem Aut_narrow
    {R : Type u} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) (hoddR : Odd (Nat.card R))
    (A : Subgroup (MulAut R))
    (hNarrow : IsNarrow p (⊤ : Subgroup R))
    (hsolA : IsSolvable A) (hoddA : Odd (Nat.card A)) :
    IsPPrimeSubgroup p
        (⊤ : Subgroup (A ⧸ pCore p A)) ∧
      IsMulCommutative (A ⧸ pCore p A) ∧
      ((∃ E : Subgroup R, IsElementaryAbelianOfRank p 3 E) →
        ∀ a : A, Nat.Coprime p (orderOf a) →
          orderOf a ∣ p - 1) := by
  classical
  by_cases hRank3 : ∃ E : Subgroup R,
      IsElementaryAbelianOfRank p 3 E
  · obtain ⟨H, hHchar, hHcomm, _hHclass, hHexp, hHfix⟩ :=
      Submission.OddOrder.BG.Section01.critical_odd hR hoddR (by
        intro hcard
        haveI : Subsingleton R := (Nat.card_eq_one_iff_unique.mp hcard).1
        obtain ⟨E, _hE⟩ := hRank3
        have hEcard : Nat.card E = 1 := Nat.card_unique
        rw [_hE.card_eq] at hEcard
        have hpgt : 1 < p ^ 3 := one_lt_pow₀
          (Fact.out : p.Prime).one_lt (by decide)
        omega)
    letI : H.Characteristic := hHchar
    obtain ⟨S, hScard, hCentRank⟩ :=
      (narrow_centP hR hoddR hRank3).mp hNarrow
    obtain ⟨hSHdis, hCentCard⟩ :=
      critical_centralizer_card_eq_prime hR hoddR hRank3 hNarrow
        hHchar hHcomm hHexp hScard hCentRank
    let Pows : Set A := (fun a : A ↦ a ^ (p - 1)) '' Set.univ
    let APow : Subgroup A := Subgroup.closure Pows
    let B : Subgroup A := _root_.commutator A ⊔ APow

    have hBcoprime_one : ∀ b : A, b ∈ B →
        Nat.Coprime p (orderOf b) → b = 1 := by
      intro b hbB hbCop
      have hfixAll : ∀ n : ℕ, ∀ L : Subgroup R,
          Nat.card L = n → L.Characteristic → L ≤ H →
          ∀ x : L, (b : MulAut R) (x : R) = x := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
          intro L hLcard hLchar hLH x
          letI : L.Characteristic := hLchar
          letI : L.Normal := by infer_instance
          by_cases hLbot : L = ⊥
          · have hxOne : (x : R) = 1 := by
              apply Subgroup.mem_bot.mp
              rw [← hLbot]
              exact x.property
            simpa [hxOne]
          · let K₀ : Subgroup R := ⁅L, (⊤ : Subgroup R)⁆
            have hK₀char : K₀.Characteristic := by
              dsimp only [K₀]
              infer_instance
            letI : K₀.Characteristic := hK₀char
            letI : K₀.Normal := by infer_instance
            have hK₀L : K₀ ≤ L := Subgroup.commutator_le_left L ⊤
            have hK₀H : K₀ ≤ H := hK₀L.trans hLH
            have hK₀lt : K₀ < L := by
              letI : Group.IsNilpotent R := hR.isNilpotent
              exact commutator_top_lt_of_normal_ne_bot hLbot
            have hKcardLt : Nat.card K₀ < n := by
              rw [← hLcard]
              exact natCard_subgroup_lt_of_lt hK₀lt
            have hfixK₀ : ∀ k : K₀,
                (b : MulAut R) (k : R) = k :=
              ih (Nat.card K₀) hKcardLt K₀ rfl hK₀char hK₀H
            let K : Subgroup L := K₀.subgroupOf L
            letI : K.Normal := (inferInstance : K₀.Normal).subgroupOf L
            have hQcard : Nat.card (L ⧸ K) = p :=
              characteristic_commutator_factor_card_eq_prime
                hR hSHdis hScard hCentCard hLchar hLH hLbot
            letI : IsCyclic (L ⧸ K) := isCyclic_of_prime_card hQcard
            let rL : A →* MulAut L :=
              (characteristicRestrictMulAutHom L).comp A.subtype
            letI : MulDistribMulAction A L :=
              MulDistribMulAction.compHom L rL
            have hsmulL (a : A) (y : L) : a • y = rL a y :=
              MulAction.compHom_smul_def rL a y
            have hKinv : ∀ a : A,
                K.map (rL a).toMonoidHom = K := by
              intro a
              apply Subgroup.eq_of_le_of_card_ge
              · rintro y ⟨k, hk, rfl⟩
                change ((rL a k : L) : R) ∈ K₀
                have hfixed := hK₀char.fixed (a : MulAut R)
                have hmem : (k : R) ∈
                    K₀.comap (a : MulAut R).toMonoidHom := by
                  rw [hfixed]
                  exact hk
                simpa [rL] using hmem
              · exact (Subgroup.card_map_of_injective (rL a).injective).ge
            letI : MulAction.QuotientAction A K := by
              refine ⟨?_⟩
              intro a y z hyz
              change y⁻¹ * z ∈ K at hyz
              change (a • y)⁻¹ * a • z ∈ K
              rw [← smul_inv', ← smul_mul']
              have hmem : rL a (y⁻¹ * z) ∈
                  K.map (rL a).toMonoidHom :=
                ⟨y⁻¹ * z, hyz, rfl⟩
              rwa [hKinv a] at hmem
            letI : MulDistribMulAction A (L ⧸ K) :=
              (QuotientGroup.mk'_surjective K).mulDistribMulAction
                (QuotientGroup.mk' K) (fun _ _ ↦ rfl)
            let rhoQ : A →* MulAut (L ⧸ K) :=
              MulDistribMulAction.toMulAut A (L ⧸ K)
            letI : IsMulCommutative (MulAut (L ⧸ K)) :=
              mulAut_isMulCommutative_of_isCyclic
            have hDerKer : _root_.commutator A ≤ rhoQ.ker :=
              Abelianization.commutator_subset_ker rhoQ
            have hPowKer : APow ≤ rhoQ.ker := by
              dsimp only [APow]
              rw [Subgroup.closure_le]
              rintro y ⟨a, _ha, rfl⟩
              change a ^ (p - 1) ∈ rhoQ.ker
              rw [MonoidHom.mem_ker, map_pow]
              have hAutCard : Nat.card (MulAut (L ⧸ K)) = p - 1 := by
                rw [IsCyclic.card_mulAut, hQcard,
                  Nat.totient_prime (Fact.out : p.Prime)]
              have hpw := pow_card_eq_one' (x := rhoQ a)
              rwa [hAutCard] at hpw
            have hBker : B ≤ rhoQ.ker :=
              sup_le hDerKer hPowKer
            have hbKer : rhoQ b = 1 :=
              MonoidHom.mem_ker.mp (hBker hbB)
            have hfixK : ∀ k : K, b • (k : L) = k := by
              intro k
              apply Subtype.ext
              exact hfixK₀ ⟨(k : R), k.property⟩
            have hKp : IsPGroup p K :=
              (hR.to_subgroup K₀).of_equiv
                (Subgroup.subgroupOfEquivOfLe hK₀L).symm
            obtain ⟨m, hKcard⟩ := hKp.exists_card_eq
            have hKcop : Nat.Coprime (Nat.card K) (orderOf b) := by
              rw [hKcard]
              exact hbCop.pow_left m
            have hqeq : QuotientGroup.mk' K (rL b x) =
                QuotientGroup.mk' K x := by
              have happ := congrArg
                (fun e : MulAut (L ⧸ K) ↦
                  e (QuotientGroup.mk' K x)) hbKer
              simpa [rhoQ, hsmulL] using happ
            have herr : (rL b x)⁻¹ * x ∈ K :=
              QuotientGroup.eq.mp hqeq
            have hfixed :=
              fixed_of_coprime_order_of_fixed_subgroup
                K b x hKcop hfixK herr
            simpa [hsmulL, rL] using
              congrArg Subtype.val hfixed
      have hfixH : ∀ h : H, (b : MulAut R) (h : R) = h :=
        hfixAll (Nat.card H) H rfl hHchar le_rfl
      let bFix : fixingSubgroup (MulAut R) (H : Set R) :=
        ⟨(b : MulAut R), by
          rw [mem_fixingSubgroup_iff]
          intro h hh
          exact hfixH ⟨h, hh⟩⟩
      by_contra hbNe
      have hbFixNe : bFix ≠ 1 := by
        intro hbOne
        apply hbNe
        apply Subtype.ext
        exact congrArg
          (fun z : fixingSubgroup (MulAut R) (H : Set R) ↦
            (z : MulAut R)) hbOne
      have hpOrderFix : p ∣ orderOf bFix := hHfix.dvd_orderOf hbFixNe
      have horder : orderOf bFix = orderOf b :=
        (Subgroup.orderOf_coe bFix).symm.trans
          (Subgroup.orderOf_coe b)
      have hpOrder : p ∣ orderOf b := by rwa [← horder]
      exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hbCop hpOrder

    have hderived : IsPGroup p (_root_.commutator A) := by
      apply isPGroup_of_prime_order_elements
      intro q hq hqp a haOrder
      have hcop : Nat.Coprime p (orderOf (a : A)) := by
        rw [Subgroup.orderOf_coe a, haOrder]
        exact (Nat.coprime_primes (Fact.out : p.Prime) hq).mpr
          (Ne.symm hqp)
      have haB : (a : A) ∈ B :=
        (show _root_.commutator A ≤ B from le_sup_left) a.property
      apply Subtype.ext
      exact hBcoprime_one (a : A) haB hcop
    obtain ⟨hprime, hcomm⟩ :=
      quotient_pCore_properties_of_commutator_isPGroup hderived
    refine ⟨hprime, hcomm, ?_⟩
    intro _hRank a haCop
    apply orderOf_dvd_iff_pow_eq_one.mpr
    have haPowB : a ^ (p - 1) ∈ B := by
      apply (show APow ≤ B from le_sup_right)
      apply Subgroup.subset_closure
      exact ⟨a, Set.mem_univ a, rfl⟩
    have haPowCop : Nat.Coprime p (orderOf (a ^ (p - 1))) :=
      haCop.coprime_dvd_right (orderOf_pow_dvd (x := a) (p - 1))
    exact hBcoprime_one (a ^ (p - 1)) haPowB haPowCop
  · have hderived :=
      Submission.OddOrder.BG.Section04.der1_Aut_rank2_pgroup
        hR hoddR hRank3 A hsolA hoddA
    obtain ⟨hprime, hcomm⟩ :=
      quotient_pCore_properties_of_commutator_isPGroup hderived
    exact ⟨hprime, hcomm, fun h ↦ (hRank3 h).elim⟩

/-- `BGsection5.v: narrow_der1_complement_max_pdiv`
(Bender--Glauberman Theorem 5.6(a,c)). -/
theorem narrow_der1_complement_max_pdiv
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hodd : Odd (Nat.card G)) (hsol : IsSolvable G)
    (S : Sylow p G)
    (hNarrow : IsNarrow p (⊤ : Subgroup S))
    (hpl : (∃ E : Subgroup G,
      IsElementaryAbelianOfRank p 3 E) → IsPLengthOne p G) :
    IsPrimeComplement p (pPrimeCore p (_root_.commutator G)) ∧
      ∀ {q : ℕ}, q.Prime →
        q ∣ Nat.card (G ⧸ pPrimeCore p G) → q ≤ p := by
  classical
  by_cases hRank3 : ∃ E : Subgroup G,
      IsElementaryAbelianOfRank p 3 E
  · let O : Subgroup G := pPrimeCore p G
    let Q := G ⧸ O
    letI : IsSolvable G := hsol
    letI : IsSolvable Q := isSolvable_quotient_of_isSolvable O
    have hQodd : Odd (Nat.card Q) := odd_natCard_quotient O hodd
    have hQcore : pPrimeCore p Q = ⊥ := by
      simpa [Q, O] using
        (pPrimeCore_quotient_self_eq_bot (G := G) (p := p))
    let R : Subgroup Q := pCore p Q
    have hRp : IsPGroup p R := pCore_isPGroup
    have hRodd : Odd (Nat.card R) := odd_natCard_subgroup R hQodd
    let quotientMap : G →* Q := QuotientGroup.mk' O
    obtain ⟨P, hPcore⟩ := hpl hRank3
    let SQ : Sylow p Q :=
      S.mapSurjective (QuotientGroup.mk'_surjective O)
    letI : P.Normal := by
      rw [hPcore]
      infer_instance
    letI : Unique (Sylow p Q) :=
      Sylow.unique_of_normal P inferInstance
    have hSQP : SQ = P := Subsingleton.elim SQ P
    have hSmap : (S : Subgroup G).map quotientMap = R := by
      change (SQ : Subgroup Q) = R
      rw [hSQP, hPcore]
    have hdisSO : Disjoint (S : Subgroup G) O := by
      dsimp only [O]
      exact disjoint_pPrimeCore_of_isPGroup S.isPGroup'
    let quotientMapS : S →* Q :=
      quotientMap.comp (S : Subgroup G).subtype
    have hquotientMapSInj : Function.Injective quotientMapS := by
      intro x y hxy
      apply Subtype.ext
      change quotientMap (x : G) = quotientMap (y : G) at hxy
      have hxyO : (x : G) * (y : G)⁻¹ ∈ O := by
        apply (QuotientGroup.eq_one_iff ((x : G) * (y : G)⁻¹)).mp
        change quotientMap ((x : G) * (y : G)⁻¹) = 1
        rw [map_mul, map_inv, hxy, mul_inv_cancel]
      have hxyS : (x : G) * (y : G)⁻¹ ∈ (S : Subgroup G) :=
        S.mul_mem x.property (S.inv_mem y.property)
      have hxyOne : (x : G) * (y : G)⁻¹ = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← disjoint_iff.mp hdisSO]
        exact ⟨hxyS, hxyO⟩
      exact mul_inv_eq_one.mp hxyOne
    have hquotientMapSRange : quotientMapS.range = R := by
      calc
        quotientMapS.range = (S : Subgroup G).map quotientMap := by
          dsimp only [quotientMapS]
          rw [MonoidHom.range_comp, Subgroup.range_subtype]
        _ = R := hSmap
    have hRnarrowSubgroup : IsNarrow p R := by
      have hmapNarrow :=
        (isNarrow_map_iff_of_injective quotientMapS
          hquotientMapSInj (⊤ : Subgroup S)).mpr hNarrow
      rw [← MonoidHom.range_eq_map, hquotientMapSRange] at hmapNarrow
      exact hmapNarrow
    have hRnarrow : IsNarrow p (⊤ : Subgroup R) :=
      (isNarrow_subgroup_iff_top R).mp hRnarrowSubgroup
    have hRrank3 : ∃ E : Subgroup R,
        IsElementaryAbelianOfRank p 3 E := by
      obtain ⟨E, hE⟩ :=
        exists_elementaryAbelian_rank_three_in_sylow S hRank3
      let F : Subgroup Q := E.map quotientMapS
      have hF : IsElementaryAbelianOfRank p 3 F := by
        dsimp only [F]
        exact hE.map_of_injective quotientMapS hquotientMapSInj
      have hFR : F ≤ R := by
        rw [← hquotientMapSRange]
        exact Subgroup.map_le_range (f := quotientMapS) E
      exact ⟨F.subgroupOf R, hF.subgroupOf hFR⟩
    let i : Q →* Subgroup.normalizer (R : Set Q) :=
      { toFun := fun x ↦ ⟨x, by
          rw [R.normalizer_eq_top]
          trivial⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }
    let rho : Q →* MulAut R := R.normalizerMonoidHom.comp i
    let A : Subgroup (MulAut R) := rho.range
    have hAsol : IsSolvable A :=
      solvable_of_surjective rho.rangeRestrict_surjective
    have hAodd : Odd (Nat.card A) :=
      hQodd.of_dvd_nat (Subgroup.card_range_dvd rho)
    obtain ⟨_hAprime, hAcomm, hAorder⟩ :=
      Aut_narrow hRp hRodd A hRnarrow hAsol hAodd
    have hAderivedLe :
        _root_.commutator A ≤ pCore p A :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hAcomm
    have hAderived : IsPGroup p (_root_.commutator A) :=
      pCore_isPGroup.to_le hAderivedLe
    let C : Subgroup Q := Subgroup.centralizer (R : Set Q)
    have hrhoKer : rho.ker = C := by
      ext x
      change i x ∈ R.normalizerMonoidHom.ker ↔
        x ∈ Subgroup.centralizer (R : Set Q)
      rw [Subgroup.normalizerMonoidHom_ker]
      rfl
    have hCp : IsPGroup p C := by
      dsimp only [C, R]
      exact centralizer_pCore_isPGroup_of_pPrimeCore_eq_bot hQcore
    have hrhoKerP : IsPGroup p rho.ker := by
      rw [hrhoKer]
      exact hCp
    let DQ : Subgroup Q := _root_.commutator Q
    have hmapDQ : DQ.map rho =
        (_root_.commutator A).map A.subtype := by
      calc
        DQ.map rho = ⁅rho.range, rho.range⁆ := map_commutator_eq Q rho
        _ = (_root_.commutator A).map A.subtype := by
          simpa [A] using (Subgroup.map_subtype_commutator A).symm
    have hmapDQP : IsPGroup p (DQ.map rho) := by
      rw [hmapDQ]
      exact hAderived.of_equiv
        ((_root_.commutator A).equivMapOfInjective
          A.subtype A.subtype_injective)
    have hrestrictKerP : IsPGroup p (rho.restrict DQ).ker := by
      let j : (rho.restrict DQ).ker →* rho.ker :=
        { toFun := fun x ↦ ⟨((x : DQ) : Q), x.property⟩
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl }
      exact hrhoKerP.of_injective j (by
        intro x y hxy
        have hxyQ : ((x : DQ) : Q) = ((y : DQ) : Q) :=
          congrArg (fun z : rho.ker ↦ (z : Q)) hxy
        apply Subtype.ext
        apply Subtype.ext
        exact hxyQ)
    have hDQp : IsPGroup p (_root_.commutator Q) := by
      change IsPGroup p DQ
      exact isPGroup_of_map_and_restrict_ker
        DQ rho hmapDQP hrestrictKerP
    have hHall : IsPrimeComplement p
        (pPrimeCore p (_root_.commutator G)) := by
      apply pPrimeCore_commutator_isPrimeComplement_of_quotient
        (N := O)
      · exact pPrimeCore_isNormalPPrime.1
      · simpa [Q, O] using hDQp
    refine ⟨hHall, ?_⟩
    intro q hq hqdvd
    by_cases hqp : q = p
    · exact Nat.le_of_eq hqp
    letI : Fact q.Prime := ⟨hq⟩
    have hqCcop : (Nat.card C).Coprime q := by
      obtain ⟨n, hCcard⟩ := hCp.exists_card_eq
      rw [hCcard]
      exact ((Nat.coprime_primes (Fact.out : p.Prime) hq).mpr
        (Ne.symm hqp)).pow_left n
    have hqC : ¬ q ∣ Nat.card C :=
      hq.coprime_iff_not_dvd.mp hqCcop.symm
    have hqdvdQ : q ∣ Nat.card Q := by
      simpa [Q, O] using hqdvd
    have hqindex : q ∣ C.index := by
      rw [← C.card_mul_index] at hqdvdQ
      exact (hq.dvd_mul.mp hqdvdQ).resolve_left hqC
    have hqA : q ∣ Nat.card A := by
      dsimp only [A]
      rw [← Subgroup.index_ker rho, hrhoKer]
      exact hqindex
    obtain ⟨a, haOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := A) q hqA
    have haCop : Nat.Coprime p (orderOf a) := by
      rw [haOrder]
      exact (Nat.coprime_primes (Fact.out : p.Prime) hq).mpr
        (Ne.symm hqp)
    have hqdiv : q ∣ p - 1 := by
      have hdiv := hAorder hRrank3 a haCop
      rwa [haOrder] at hdiv
    exact (Nat.le_of_dvd
      (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt) hqdiv).trans
        (Nat.sub_le p 1)
  · refine ⟨
      (Submission.OddOrder.BG.Section04.rank2_der1_complement
        hsol hodd hRank3).1, ?_⟩
    intro q hq hqdvd
    exact Submission.OddOrder.BG.Section04.rank2_max_pdiv
      hsol hodd hRank3 hq hqdvd

end

end Submission.OddOrder.BG.Section05
