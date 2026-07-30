import Submission.OddOrder.BG.Section04.OddNormalRankTwoExists
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation
import Submission.OddOrder.MathlibSupport.OmegaOneCentralizerMaxNormal
import Submission.OddOrder.MathlibSupport.PSubgroupGeneralLinearTwo
import Submission.OddOrder.MathlibSupport.SCNExistence
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
Bender--Glauberman Lemma 4.7.

MathComp states the result using numerical group rank and the finite set
`'SCN_3(R)`.  As elsewhere in this port, rank at least `n` is expanded into
the existence of an elementary-abelian subgroup of cardinal rank `n`.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A subgroup has `p`-rank at least `n`, in the cardinal-rank language used
by this port. -/
def HasElementaryAbelianRankAtLeast
    (p n : ℕ) (A : Subgroup G) : Prop :=
  ∃ E : Subgroup G, E ≤ A ∧ IsElementaryAbelianOfRank p n E

/-- The predicate corresponding to membership in MathComp's `'SCN_n(G)`.
-/
def IsSCNAtLeastRank
    (p n : ℕ) (A : Subgroup G) : Prop :=
  IsSCN (⊤ : Subgroup G) A ∧ HasElementaryAbelianRankAtLeast p n A

private theorem not_isCyclic_of_elementaryAbelian_rank_three
    {E : Subgroup G} (hE : IsElementaryAbelianOfRank p 3 E) :
    ¬ IsCyclic E := by
  intro hcyclic
  letI : IsCyclic E := hcyclic
  letI := Fintype.ofFinite E
  classical
  have hle : Nat.card E ≤ p := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hE.pow_eq_one, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := E) (Fact.out : p.Prime).pos)
  have hlt : p < p ^ 3 := by
    simpa using
      (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega : 1 < 3))
  exact (not_lt_of_ge (hE.card_eq ▸ hle)) hlt

/-- A proper elementary-abelian overgroup of a rank-two subgroup contains an
elementary-abelian subgroup of rank three. -/
private theorem exists_rank_three_of_rank_two_lt_elementary
    (hG : IsPGroup p G) {Z E : Subgroup G} [E.Normal]
    (hZ : IsElementaryAbelianOfRank p 2 Z)
    (hE : IsElementaryAbelianGroup p E) (hZE : Z < E) :
    ∃ F : Subgroup G, F ≤ E ∧ F.Normal ∧
      IsElementaryAbelianOfRank p 3 F := by
  obtain ⟨n, hEcard⟩ := hE.isPGroup.exists_card_eq
  have hcardlt : p ^ 2 < p ^ n := by
    simpa only [hZ.card_eq, hEcard] using natCard_subgroup_lt_of_lt hZE
  have hn : 3 ≤ n := by
    by_contra hnot
    have hnle : n ≤ 2 := by omega
    have hpows : p ^ n ≤ p ^ 2 :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos hnle
    exact (not_lt_of_ge hpows) hcardlt
  obtain ⟨F, hFE, hFnormal, hFcard⟩ :=
    exists_normal_subgroup_card_pow_le hG E hEcard hn
  have hFcomm : IsMulCommutative F := by
    letI : IsMulCommutative E := hE.commutative
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg Subtype.val
      (mul_comm (⟨x, hFE x.2⟩ : E) (⟨y, hFE y.2⟩ : E))
  have hFpow : ∀ x : F, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    change (x : G) ^ p = 1
    exact congrArg Subtype.val (hE.pow_eq_one (⟨x, hFE x.2⟩ : E))
  exact ⟨F, hFE, hFnormal,
    { isPGroup := hG.to_subgroup F
      commutative := hFcomm
      pow_eq_one := hFpow
      card_eq := hFcard }⟩

/-- Under the negation of `'SCN_3(G)`, a normal elementary-abelian subgroup
of rank two is maximal among the normal elementary-abelian subgroups. -/
private theorem maximal_normal_elementary_of_no_scn_rank_three
    (hG : IsPGroup p G) {Z : Subgroup G} [Z.Normal]
    (hZ : IsElementaryAbelianOfRank p 2 Z)
    (hNoSCN : ¬ ∃ A : Subgroup G, IsSCNAtLeastRank p 3 A) :
    ∀ {E : Subgroup G}, E.Normal → IsElementaryAbelianGroup p E →
      Z ≤ E → E ≤ Z := by
  intro E hEnormal hE hZE
  by_contra hnot
  have hZElt : Z < E := lt_of_le_of_ne hZE (fun hEq ↦ hnot hEq.ge)
  letI : E.Normal := hEnormal
  obtain ⟨F, hFE, _hFnormal, hF⟩ :=
    exists_rank_three_of_rank_two_lt_elementary hG hZ hE hZElt
  have hEnormalAbelian : IsNormalAbelian E :=
    ⟨hEnormal, hE.commutative⟩
  obtain ⟨A, hEA, hA⟩ :=
    exists_isSCN_top_containing hG E hEnormalAbelian
  apply hNoSCN
  exact ⟨A, hA, F, hFE.trans hEA, hF⟩

/-- An elementary-abelian rank-three subgroup has a rank-at-least-two
centralizer on every normal elementary-abelian rank-two subgroup.  This is
the cardinal form of MathComp's `logn_quotient_cent_abelem` step. -/
theorem prime_sq_le_natCard_centralizerWithin
    {A Z : Subgroup G} [Z.Normal]
    (hA : IsElementaryAbelianOfRank p 3 A)
    (hZ : IsElementaryAbelianOfRank p 2 Z) :
    p ^ 2 ≤ Nat.card (centralizerWithin A Z) := by
  letI : IsMulCommutative Z := hZ.commutative
  letI : AddCommGroup (Additive Z) := inferInstance
  letI : Module (ZMod p) (Additive Z) :=
    elementaryAbelianZModModule Z p hZ.pow_eq_one
  let normalizerHom : G →* Subgroup.normalizer (Z : Set G) :=
    (MonoidHom.id G).codRestrict (Subgroup.normalizer (Z : Set G)) fun g ↦ by
      rw [Subgroup.normalizer_eq_top_iff.mpr (show Z.Normal from inferInstance)]
      trivial
  let f : A →* Subgroup.normalizer (Z : Set G) :=
    normalizerHom.comp A.subtype
  let rhoAut : A →* MulAut Z := Z.normalizerMonoidHom.comp f
  let linearize :
      MulAut Z →* LinearMap.GeneralLinearGroup (ZMod p) (Additive Z) :=
    (mulAutRepresentation Z p).asGroupHom
  let rhoGL :
      A →* LinearMap.GeneralLinearGroup (ZMod p) (Additive Z) :=
    linearize.comp rhoAut
  let H : Subgroup A := (centralizerWithin A Z).subgroupOf A
  have hkerAut : rhoAut.ker = H := by
    ext a
    change rhoAut a = 1 ↔ (a : G) ∈ centralizerWithin A Z
    change rhoAut a = 1 ↔
      (a : G) ∈ A ∧ (a : G) ∈ Subgroup.centralizer (Z : Set G)
    simp only [a.property, true_and]
    change f a ∈ Z.normalizerMonoidHom.ker ↔ _
    rw [Subgroup.normalizerMonoidHom_ker]
    rfl
  have hker : rhoGL.ker = H := by
    calc
      rhoGL.ker = rhoAut.ker :=
        MonoidHom.ker_comp_of_injective rhoAut linearize
          (mulAutRepresentation_asGroupHom_injective Z p)
      _ = H := hkerAut
  have hRangeP : IsPGroup p rhoGL.range := by
    rw [rhoGL.range_eq_map]
    exact (hA.isPGroup.to_subgroup (⊤ : Subgroup A)).map rhoGL
  letI : Finite rhoGL.range :=
    Finite.of_surjective rhoGL.rangeRestrict rhoGL.rangeRestrict_surjective
  have hZcard : Nat.card (Additive Z) = p ^ 2 := by
    exact (Nat.card_congr Additive.ofMul).trans hZ.card_eq
  have hRangeCard : Nat.card rhoGL.range ≤ p :=
    natCard_le_prime_of_isPGroup_subgroup_linearGL_card_le_sq
      rhoGL.range hRangeP (by rw [hZcard])
  obtain ⟨r, hrange⟩ := hRangeP.exists_card_eq
  obtain ⟨k, hkernel⟩ :=
    (hA.isPGroup.to_subgroup rhoGL.ker).exists_card_eq
  have hrle : r ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    rw [hrange] at hRangeCard
    simpa using hRangeCard
  have hsum : r + k = 3 := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    calc
      p ^ (r + k) = p ^ r * p ^ k := by rw [pow_add]
      _ = Nat.card rhoGL.range * Nat.card rhoGL.ker := by
        rw [hrange, hkernel]
      _ = Nat.card (A ⧸ rhoGL.ker) * Nat.card rhoGL.ker := by
        rw [Nat.card_congr
          (QuotientGroup.quotientKerEquivRange rhoGL).toEquiv]
      _ = Nat.card A :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup rhoGL.ker).symm
      _ = p ^ 3 := hA.card_eq
  have hk : 2 ≤ k := by omega
  have hHcard : Nat.card H = p ^ k := by rw [← hker, hkernel]
  calc
    p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hk
    _ = Nat.card H := hHcard.symm
    _ = Nat.card (centralizerWithin A Z) :=
      natCard_subgroupOf_eq (centralizerWithin_le_left A Z)

private theorem no_rank_three_of_no_scn_rank_three
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hNoSCN : ¬ ∃ A : Subgroup G, IsSCNAtLeastRank p 3 A) :
    ¬ ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A := by
  rintro ⟨A, hA⟩
  have hncyclic : ¬ IsCyclic G := by
    intro hcyclic
    have htop : IsCyclic (⊤ : Subgroup G) :=
      Subgroup.topEquiv.isCyclic.mpr hcyclic
    letI : IsCyclic (⊤ : Subgroup G) := htop
    exact not_isCyclic_of_elementaryAbelian_rank_three hA
      (Subgroup.isCyclic_of_le le_top)
  letI : Nontrivial G := Nontrivial.of_not_isCyclic hncyclic
  have hpodd : Odd p := hodd.of_dvd_nat
    (hG.card_eq_or_dvd.resolve_left
      (ne_of_gt (Finite.one_lt_card (α := G))))
  obtain ⟨Z, hZnormal, hZ⟩ := ex_odd_normal_p2Elem hG hodd hncyclic
  letI : Z.Normal := hZnormal
  have hmax : ∀ {E : Subgroup G}, E.Normal →
      IsElementaryAbelianGroup p E → Z ≤ E → E ≤ Z :=
    maximal_normal_elementary_of_no_scn_rank_three hG hZ hNoSCN
  have homegaZ :
      (omegaOne p (centralizerWithin (⊤ : Subgroup G) Z)).map
          (centralizerWithin (⊤ : Subgroup G) Z).subtype = Z :=
    map_omegaOne_centralizerWithin_eq_of_maximal_normal_elementaryAbelian
      hG hpodd Z hZ.toIsElementaryAbelianGroup hmax
  let H : Subgroup G := centralizerWithin A Z
  have hHcard : p ^ 2 ≤ Nat.card H :=
    prime_sq_le_natCard_centralizerWithin hA hZ
  have hHZ : H ≤ Z := by
    intro x hx
    have hxC : x ∈ centralizerWithin (⊤ : Subgroup G) Z :=
      ⟨trivial, hx.2⟩
    let xC : centralizerWithin (⊤ : Subgroup G) Z := ⟨x, hxC⟩
    have hxpow : xC ^ p = 1 := by
      apply Subtype.ext
      change x ^ p = 1
      exact congrArg Subtype.val (hA.pow_eq_one (⟨x, hx.1⟩ : A))
    have hxOmega : xC ∈ omegaOne p (centralizerWithin (⊤ : Subgroup G) Z) :=
      mem_omegaOne_of_pow_eq_one p hxpow
    have hxMap : x ∈
        (omegaOne p (centralizerWithin (⊤ : Subgroup G) Z)).map
          (centralizerWithin (⊤ : Subgroup G) Z).subtype :=
      ⟨xC, hxOmega, rfl⟩
    exact homegaZ ▸ hxMap
  have hHZeq : H = Z := by
    apply Subgroup.eq_of_le_of_card_ge hHZ
    simpa only [hZ.card_eq] using hHcard
  have hZA : Z ≤ A := by
    rw [← hHZeq]
    exact centralizerWithin_le_left A Z
  have hAH : A ≤ H := by
    intro a ha
    refine ⟨ha, ?_⟩
    change ∀ z : G, z ∈ Z → z * a = a * z
    intro z hz
    letI : IsMulCommutative A := hA.commutative
    exact congrArg Subtype.val
      (mul_comm (⟨z, hZA hz⟩ : A) (⟨a, ha⟩ : A))
  have hAHeq : A = H := le_antisymm hAH (centralizerWithin_le_left A Z)
  have hAZ : A = Z := hAHeq.trans hHZeq
  have hpows : p ^ 3 = p ^ 2 := by
    rw [← hA.card_eq, hAZ, hZ.card_eq]
  have : (3 : ℕ) = 2 :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le hpows
  omega

/-- `BGsection4.v: rank2_SCN3_empty` (Bender--Glauberman Lemma 4.7). -/
theorem rank2_SCN3_empty
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G)) :
    (¬ ∃ E : Subgroup G, IsElementaryAbelianOfRank p 3 E) ↔
      ¬ ∃ A : Subgroup G, IsSCNAtLeastRank p 3 A := by
  constructor
  · intro hNoRank
    rintro ⟨A, hA, E, _hEA, hE⟩
    exact hNoRank ⟨E, hE⟩
  · intro hNoSCN
    exact no_rank_three_of_no_scn_rank_three hG hodd hNoSCN

end Submission.OddOrder.BG.Section04
