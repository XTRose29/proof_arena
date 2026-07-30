import Submission.OddOrder.BG.Section05.NarrowCentralizerDirectProduct
import Mathlib.GroupTheory.Sylow

/-!
Bender--Glauberman Corollary 5.4.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- `BGsection5.v:narrow_centP` (Bender--Glauberman Corollary 5.4).

The numerical condition `r_p(C_G(S)) ≤ 2` is represented by the absence
of an elementary-abelian rank-three subgroup of `C_G(S)`.  Since `G`
itself represents MathComp's ambient subgroup `R`, the tautological source
condition `S ≤ R` is omitted. -/
theorem narrow_centP
    (hG : IsPGroup p G) (_hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A) :
    IsNarrow p (⊤ : Subgroup G) ↔
      ∃ S : Subgroup G,
        Nat.card S = p ∧
          ¬ ∃ F : Subgroup G,
            F ≤ centralizerWithin (⊤ : Subgroup G) S ∧
              IsElementaryAbelianOfRank p 3 F := by
  constructor
  · intro hNarrow
    have hRankTop : ∃ A : Subgroup G,
        A ≤ (⊤ : Subgroup G) ∧ IsElementaryAbelianOfRank p 3 A := by
      obtain ⟨A, hA⟩ := hRank3
      exact ⟨A, le_top, hA⟩
    obtain ⟨E, hE, hmaxE⟩ := narrow_pmaxElem hNarrow hRankTop
    let Z : Subgroup G := omegaOneCenter p G
    have hZcard : Nat.card Z = p :=
      omegaOneCenter_card_eq_prime_of_rank_three_pmaxElem
        hG hRank3 hE hmaxE
    have hZE : Z ≤ E := omegaOneCenter_le_of_pmaxElem hmaxE
    have hZneE : Z ≠ E := by
      intro hZEeq
      have hcardEq := congrArg (fun H : Subgroup G ↦ Nat.card H) hZEeq
      rw [hZcard, hE.card_eq] at hcardEq
      have hpLt : p < p ^ 2 := by
        rw [pow_two]
        exact lt_mul_of_one_lt_right
          (Fact.out : p.Prime).pos (Fact.out : p.Prime).one_lt
      omega
    have hZltE : Z < E := lt_of_le_of_ne hZE hZneE
    obtain ⟨x, hxE, hxZ⟩ := SetLike.exists_of_lt hZltE
    let S : Subgroup G := Subgroup.zpowers x
    have hxne : x ≠ 1 := by
      intro hxone
      apply hxZ
      rw [hxone]
      exact Z.one_mem
    have hxpow : x ^ p = 1 :=
      congrArg Subtype.val (hE.pow_eq_one ⟨x, hxE⟩)
    have hxorder : orderOf x = p :=
      ((Nat.dvd_prime (Fact.out : p.Prime)).mp
        (orderOf_dvd_of_pow_eq_one hxpow)).resolve_left (by
          rw [orderOf_eq_one_iff]
          exact hxne)
    have hScard : Nat.card S = p := by
      dsimp [S]
      rw [Nat.card_zpowers, hxorder]
    have hSE : S ≤ E := by
      dsimp [S]
      exact Subgroup.zpowers_le.mpr hxE
    have hSnotZ : ¬ S ≤ Z := by
      intro hSZ
      exact hxZ (hSZ (Subgroup.mem_zpowers x))
    have hSZdis : Disjoint S Z := by
      rw [disjoint_iff]
      by_contra hInfNe
      have hdiv : Nat.card (S ⊓ Z : Subgroup G) ∣ p := by
        rw [← hScard]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv with
        hcardOne | hcardP
      · apply hInfNe
        exact Subgroup.eq_bot_of_card_eq (S ⊓ Z : Subgroup G) hcardOne
      · have hInfS : S ⊓ Z = S := by
          apply Subgroup.eq_of_le_of_card_ge inf_le_left
          rw [hcardP, hScard]
        apply hSnotZ
        intro s hs
        have hsInf : s ∈ S ⊓ Z := by rw [hInfS]; exact hs
        exact hsInf.2
    have hSZcomm : ∀ s ∈ S, ∀ z ∈ Z, Commute s z := by
      intro s _ z hz
      exact Subgroup.mem_center_iff.mp (omegaOneCenter_le_center p hz) s
    have hSupE : S ⊔ Z = E := by
      apply Subgroup.eq_of_le_of_card_ge (sup_le hSE hZE)
      rw [natCard_sup_eq_mul_of_disjoint_of_commute hSZdis hSZcomm,
        hScard, hZcard, hE.card_eq, pow_two]
    refine ⟨S, hScard, ?_⟩
    rintro ⟨F, hFCent, hF⟩
    have hTorsion :
        pTorsionCentralizerWithin p (⊤ : Subgroup G) E = (E : Set G) :=
      isPMaxElem_iff_pTorsionCentralizerWithin.mp hmaxE
    have hFE : F ≤ E := by
      intro f hf
      have hScentf : S ≤ Subgroup.centralizer ({f} : Set G) := by
        intro s hs
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (mem_centralizerWithin.mp (hFCent hf)).2 s hs
      have hZcentf : Z ≤ Subgroup.centralizer ({f} : Set G) := by
        intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.mp
          (omegaOneCenter_le_center p hz) f).symm
      have hfCentE : f ∈ Subgroup.centralizer (E : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        have heSup : e ∈ S ⊔ Z := by rw [hSupE]; exact he
        have heCentf := (sup_le hScentf hZcentf) heSup
        exact Subgroup.mem_centralizer_singleton_iff.mp heCentf
      have hfPow : f ^ p = 1 :=
        congrArg Subtype.val (hF.pow_eq_one ⟨f, hf⟩)
      have hfTorsion :
          f ∈ pTorsionCentralizerWithin p (⊤ : Subgroup G) E :=
        ⟨trivial, hfCentE, hfPow⟩
      rw [hTorsion] at hfTorsion
      exact hfTorsion
    have hpows : p ^ 3 ≤ p ^ 2 := by
      rw [← hF.card_eq, ← hE.card_eq]
      exact Subgroup.card_le_of_le hFE
    have : (3 : ℕ) ≤ 2 :=
      (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hpows
    omega
  · rintro ⟨S, hScard, hCentRank⟩
    intro _hRankTop
    let Z : Subgroup G := omegaOneCenter p G
    let SZ : Subgroup G := S ⊔ Z
    have hS : IsElementaryAbelianOfRank p 1 S :=
      isElementaryAbelianOfRank_one_of_card_eq_prime hScard
    have hSnotZ : ¬ S ≤ Z := by
      intro hSZ
      have hCentTop : centralizerWithin (⊤ : Subgroup G) S = ⊤ := by
        apply top_unique
        intro g _
        refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
        intro s hs
        exact (Subgroup.mem_center_iff.mp
          (omegaOneCenter_le_center p (hSZ hs)) g).symm
      apply hCentRank
      obtain ⟨A, hA⟩ := hRank3
      refine ⟨A, ?_, hA⟩
      rw [hCentTop]
      exact le_top
    have hSZdis : Disjoint S Z := by
      rw [disjoint_iff]
      by_contra hInfNe
      have hdiv : Nat.card (S ⊓ Z : Subgroup G) ∣ p := by
        rw [← hScard]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv with
        hcardOne | hcardP
      · apply hInfNe
        exact Subgroup.eq_bot_of_card_eq (S ⊓ Z : Subgroup G) hcardOne
      · have hInfS : S ⊓ Z = S := by
          apply Subgroup.eq_of_le_of_card_ge inf_le_left
          rw [hcardP, hScard]
        apply hSnotZ
        intro s hs
        have hsInf : s ∈ S ⊓ Z := by rw [hInfS]; exact hs
        exact hsInf.2
    have hZgroup : IsElementaryAbelianGroup p Z := by
      refine
        { isPGroup := hG.to_subgroup Z
          commutative := ?_
          pow_eq_one := ?_ }
      · apply isMulCommutative_iff.mpr
        intro z w
        apply Subtype.ext
        exact (Subgroup.mem_center_iff.mp
          (omegaOneCenter_le_center p z.2) w).symm
      · intro z
        exact omegaOneCenter_pow_eq_one p z
    obtain ⟨n, hZcard⟩ := hZgroup.isPGroup.exists_card_eq
    have hGone : 1 < Nat.card G := by
      obtain ⟨A, hA⟩ := hRank3
      have hAone : 1 < Nat.card A := by
        rw [hA.card_eq]
        exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
      exact hAone.trans_le A.card_le_card_group
    letI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hGone
    letI : Nontrivial (Subgroup.center G) := hG.center_nontrivial
    have hCenterP : IsPGroup p (Subgroup.center G) :=
      hG.to_subgroup (Subgroup.center G)
    obtain ⟨m, hm, hCenterCard⟩ :=
      hCenterP.nontrivial_iff_card.mp inferInstance
    have hpCenter : p ∣ Nat.card (Subgroup.center G) := by
      rw [hCenterCard]
      exact dvd_pow_self p hm.ne'
    obtain ⟨z, hzOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := Subgroup.center G) p hpCenter
    let zG : G := z
    have hzOrderG : orderOf zG = p :=
      (Subgroup.orderOf_coe z).trans hzOrder
    have hzPowG : zG ^ p = 1 :=
      (congrArg (fun k : ℕ ↦ zG ^ k) hzOrderG).symm.trans
        (pow_orderOf_eq_one zG)
    have hzOmega : z ∈ omegaOne p (Subgroup.center G) := by
      apply mem_omegaOne_of_pow_eq_one
      apply Subtype.ext
      exact hzPowG
    have hzZ : zG ∈ Z := ⟨z, hzOmega, rfl⟩
    have hzGne : zG ≠ 1 := by
      intro hz
      apply (Fact.out : p.Prime).ne_one
      rw [← hzOrderG, hz, orderOf_one]
    have hZone : 1 < Nat.card Z := by
      apply Z.one_lt_card_iff_ne_bot.mpr
      intro hZbot
      have : zG = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← hZbot]
        exact hzZ
      exact hzGne this
    have hnpos : 1 ≤ n := by
      by_contra hn
      have hnzero : n = 0 := by omega
      rw [hZcard, hnzero, pow_zero] at hZone
      omega
    have hZ : IsElementaryAbelianOfRank p n Z :=
      { hZgroup with card_eq := hZcard }
    have hSZcomm : ∀ s ∈ S, ∀ z ∈ Z, Commute s z := by
      intro s _ z hz
      exact Subgroup.mem_center_iff.mp (omegaOneCenter_le_center p hz) s
    have hSZrank : IsElementaryAbelianOfRank p (1 + n) SZ := by
      simpa [SZ] using
        (isElementaryAbelianOfRank_sup_of_disjoint_of_commute
          hG hS hZ hSZdis hSZcomm)
    have hSZCent : SZ ≤ centralizerWithin (⊤ : Subgroup G) S := by
      apply sup_le
      · intro s hs
        refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
        intro x hx
        letI : IsMulCommutative S := hS.commutative
        exact congrArg Subtype.val
          (mul_comm (⟨x, hx⟩ : S) ⟨s, hs⟩)
      · intro z hz
        refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
        intro s _
        exact Subgroup.mem_center_iff.mp
          (omegaOneCenter_le_center p hz) s
    have hnle : n ≤ 1 := by
      by_contra hn
      have hntwo : 2 ≤ n := by omega
      have hpThreeLe : p ^ 3 ≤ Nat.card SZ := by
        rw [hSZrank.card_eq]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
      obtain ⟨F, hFSZ, hFcard⟩ :=
        Sylow.exists_subgroup_le_card_pow_prime_of_le_card
          (Fact.out : p.Prime) hG hpThreeLe
      have hFcomm : IsMulCommutative F := by
        letI : IsMulCommutative SZ := hSZrank.commutative
        apply isMulCommutative_iff.mpr
        intro x y
        apply Subtype.ext
        exact congrArg (fun z : SZ ↦ (z : G))
          (mul_comm (⟨x, hFSZ x.2⟩ : SZ) ⟨y, hFSZ y.2⟩)
      have hFpow : ∀ x : F, x ^ p = 1 := by
        intro x
        apply Subtype.ext
        exact congrArg (fun z : SZ ↦ (z : G))
          (hSZrank.pow_eq_one ⟨x, hFSZ x.2⟩)
      apply hCentRank
      exact ⟨F, hFSZ.trans hSZCent,
        { isPGroup := hG.to_subgroup F
          commutative := hFcomm
          pow_eq_one := hFpow
          card_eq := hFcard }⟩
    have hn : n = 1 := by omega
    have hSZelem : IsElementaryAbelianOfRank p 2 SZ := by
      simpa [hn] using hSZrank
    have hSZmax : IsPMaxElem p (⊤ : Subgroup G) SZ := by
      refine ⟨⟨le_top, hSZelem.toIsElementaryAbelianGroup⟩, ?_⟩
      intro H hH hSZH
      letI : IsMulCommutative H := hH.2.commutative
      have hSH : S ≤ H := (show S ≤ SZ from le_sup_left).trans hSZH
      have hHCent : H ≤ centralizerWithin (⊤ : Subgroup G) S := by
        intro x hx
        refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
        intro s hs
        exact congrArg Subtype.val
          (mul_comm (⟨s, hSH hs⟩ : H) ⟨x, hx⟩)
      obtain ⟨k, hHcard⟩ := hH.2.isPGroup.exists_card_eq
      have hkle : k ≤ 2 := by
        by_contra hk
        have hkthree : 3 ≤ k := by omega
        have hpThreeLe : p ^ 3 ≤ Nat.card H := by
          rw [hHcard]
          exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hkthree
        obtain ⟨F, hFH, hFcard⟩ :=
          Sylow.exists_subgroup_le_card_pow_prime_of_le_card
            (Fact.out : p.Prime) hG hpThreeLe
        have hFcomm : IsMulCommutative F := by
          apply isMulCommutative_iff.mpr
          intro x y
          apply Subtype.ext
          exact congrArg (fun z : H ↦ (z : G))
            (mul_comm (⟨x, hFH x.2⟩ : H) ⟨y, hFH y.2⟩)
        have hFpow : ∀ x : F, x ^ p = 1 := by
          intro x
          apply Subtype.ext
          exact congrArg (fun z : H ↦ (z : G))
            (hH.2.pow_eq_one ⟨x, hFH x.2⟩)
        apply hCentRank
        exact ⟨F, hFH.trans hHCent,
          { isPGroup := hG.to_subgroup F
            commutative := hFcomm
            pow_eq_one := hFpow
            card_eq := hFcard }⟩
      have hHcardLe : Nat.card H ≤ p ^ 2 := by
        rw [hHcard]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hkle
      have hSZHcard : Nat.card H ≤ Nat.card SZ := by
        rw [hSZelem.card_eq]
        exact hHcardLe
      exact (Subgroup.eq_of_le_of_card_ge hSZH hSZHcard).symm
    exact ⟨SZ, hSZelem, hSZmax⟩

end Submission.OddOrder.BG.Section05
