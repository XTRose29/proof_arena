import Mathlib.GroupTheory.SemidirectProduct
import Submission.OddOrder.BG.Section04.MetacyclicComplementFactors
import Submission.OddOrder.BG.Section12.AbelianTau2
import Submission.OddOrder.MathlibSupport.AbelianPGroupRankThree
import Submission.OddOrder.MathlibSupport.CoprimeAbelianCocyclicCentralizerGeneration
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial
import Submission.OddOrder.PF.Section03.InternalDirectProduct

/-!
# The coprime cyclic split in Bender--Glauberman Theorem 12.12

This file isolates the finite-group argument used in the noncentral branch
of `BGsection12.v: FTtypeF_complement`.  An abelian Sylow subgroup of
cardinal rank two splits as its mixed commutator with a coprime actor and
the actor-fixed subgroup.  When both factors are nontrivial they are cyclic;
the larger factor has the exponent of the original Sylow subgroup.

The final witness deliberately contains no Section 12 regularity assertion.
It records only the characteristic omega subgroup normalized by the Sylow
normalizer.  The maximal-group argument in `Tau2NormalizerFTType` turns that
normalizer statement into the required sigma-core regularity.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped IsMulCommutative

noncomputable section

universe u

private theorem isMulCommutative_of_le_split_12_12
    {G : Type u} [Group G] {B C : Subgroup G}
    (hB : IsMulCommutative B) (hCB : C ≤ B) :
    IsMulCommutative C := by
  letI : IsMulCommutative B := hB
  apply isMulCommutative_iff.mpr
  intro x y
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  exact congrArg Subtype.val
    (mul_comm (⟨x, hCB x.2⟩ : B) (⟨y, hCB y.2⟩ : B))

/-! ## Coprime commutator/fixed-point decomposition -/

/-- The fixed-point subgroup inside the mixed commutator of a coprime
abelian action is trivial.  This is the reusable form of the local lemma
appearing in the proofs of `tau1_act_tau2` and `FTtypeF_complement`. -/
theorem centralizerWithin_commutator_eq_bot_of_coprime_abelian_12_12
    {G : Type u} [Group G] [Finite G] {K X : Subgroup G}
    (hXnormK : X ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card X))
    (hKab : IsMulCommutative K) :
    centralizerWithin ⁅K, X⁆ X = ⊥ := by
  classical
  let T : Subgroup G := ⁅K, X⁆
  have hTK : T ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hXnormK
  have hXnormT : X ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.normalizer_commutator_ge_right K X
  have hTcop : Nat.Coprime (Nat.card T) (Nat.card X) :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hTK)
  letI : IsMulCommutative K := hKab
  letI : IsSolvable K :=
    Submission.OddOrder.MathlibSupport.isSolvable_of_comm
      (fun a b : K => mul_comm a b)
  have hidem : ⁅X, ⁅X, K⁆⁆ = ⁅X, K⁆ :=
    commutator_commutator_eq_of_coprime
      (K := K) (R := X) hXnormK hcop
  have hperfect : ⁅X, T⁆ = T := by
    dsimp [T]
    rw [Subgroup.commutator_comm K X]
    exact hidem
  letI : IsMulCommutative T :=
    isMulCommutative_of_le_split_12_12 hKab hTK
  apply le_antisymm _ bot_le
  intro t ht
  let tt : T := ⟨t, ht.1⟩
  have hfix : ∀ x : X,
      (x : G) * (tt : G) * (x : G)⁻¹ = (tt : G) := by
    intro x
    calc
      (x : G) * (tt : G) * (x : G)⁻¹ =
          (tt : G) * (x : G) * (x : G)⁻¹ := by
            rw [ht.2 (x : G) x.property]
      _ = (tt : G) := by simp
  have htt : tt = 1 :=
    Submission.OddOrder.BG.Section06.fixed_eq_one_of_abelian_perfect_coprime_conjugation
      hXnormT hTcop hperfect tt hfix
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val htt)

/-- The commutator and fixed-point factors of a coprime abelian action form
an internal direct product of the acted-on group. -/
theorem coprime_abelian_commutator_centralizer_directProduct_12_12
    {G : Type u} [Group G] [Finite G] {K X : Subgroup G}
    (hXnormK : X ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card X))
    (hKab : IsMulCommutative K) :
    IsInternalDirectProductIn ⁅K, X⁆ (centralizerWithin K X) K := by
  classical
  let T : Subgroup G := ⁅K, X⁆
  let C : Subgroup G := centralizerWithin K X
  have hTK : T ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hXnormK
  have hCK : C ≤ K := centralizerWithin_le_left K X
  have hfixed : centralizerWithin T X = ⊥ := by
    simpa only [T] using
      centralizerWithin_commutator_eq_bot_of_coprime_abelian_12_12
        hXnormK hcop hKab
  have hdis : Disjoint (T.subgroupOf K) (C.subgroupOf K) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hzFixed : ((z : K) : G) ∈ centralizerWithin T X :=
      ⟨hz.1, hz.2.2⟩
    have hzBot : ((z : K) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hfixed]
      exact hzFixed
    exact Subgroup.mem_bot.mp hzBot
  letI : IsMulCommutative K := hKab
  letI : IsSolvable K :=
    Submission.OddOrder.MathlibSupport.isSolvable_of_comm
      (fun a b : K => mul_comm a b)
  have hgen : K ≤ ⁅X, K⁆ ⊔ C :=
    le_commutator_sup_centralizerWithin_of_coprime hXnormK hcop
  have hsup : T ⊔ C = K := by
    apply le_antisymm (sup_le hTK hCK)
    simpa only [T, Subgroup.commutator_comm X K] using hgen
  have hsupK : T.subgroupOf K ⊔ C.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hTK hCK, hsup]
    exact Subgroup.subgroupOf_self K
  have hcomp :
      (T.subgroupOf K).IsComplement' (C.subgroupOf K) := by
    letI : (T.subgroupOf K).Normal := by infer_instance
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
    rw [← Subgroup.normal_mul (T.subgroupOf K) (C.subgroupOf K), hsupK]
    rfl
  refine
    { left_le := hTK
      right_le := hCK
      complement := hcomp
      commute := ?_ }
  intro t c
  exact congrArg Subtype.val
    (mul_comm (⟨(t : G), hTK t.property⟩ : K)
      (⟨(c : G), hCK c.property⟩ : K))

/-! ## The regular odd `q`-group quotient step -/

/-- A solvable nontrivial group cannot have a semiregular coprime action
by a noncyclic odd `q`-group.  Equivalently, an odd `q`-group acting
semiregularly is cyclic.

This is the subgroup-form replacement for the source invocation of
`odd_regular_pgroup_cyclic` on `Q / C_Q(S)`.  The proof extracts a rank-two
elementary-abelian subgroup from a hypothetical noncyclic actor and applies
coprime cocyclic-centralizer generation to the acted-on group. -/
theorem quotient_regular_qgroup_isCyclic_12_12
    {G : Type u} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime] {Y A : Subgroup G}
    (hAq : IsPGroup q A)
    (hAodd : Odd (Nat.card A))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYsol : IsSolvable Y)
    (hYne : Y ≠ ⊥)
    (hreg : IsSemiregularConjugation Y A) :
    IsCyclic A := by
  classical
  by_contra hAncyclic
  have hRankTwo :
      ∃ E : Subgroup A, IsElementaryAbelianOfRank q 2 E := by
    by_contra hno
    exact hAncyclic
      ((odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
        hAq hAodd).mpr hno)
  obtain ⟨E, hE⟩ := hRankTwo
  let B : Subgroup G := E.map A.subtype
  have hBA : B ≤ A := Subgroup.map_subtype_le E
  have hB : IsElementaryAbelianOfRank q 2 B :=
    hE.map_of_injective A.subtype A.subtype_injective
  have hBcomm : IsMulCommutative B := hB.commutative
  have hBncyclic : ¬ IsCyclic B := hB.not_isCyclic Fact.out
  have hBY : B ≤ Subgroup.normalizer (Y : Set G) := hBA.trans hAY
  have hcopYA : Nat.Coprime (Nat.card Y) (Nat.card A) :=
    hreg.natCard_coprime hAY
  have hcopYB : Nat.Coprime (Nat.card Y) (Nat.card B) :=
    hcopYA.coprime_dvd_right (Subgroup.card_dvd_of_le hBA)
  have hcent : ∀ C : Subgroup G, C ≤ B →
      (C.subgroupOf B).Normal →
      IsCyclic (B ⧸ C.subgroupOf B) →
      centralizerWithin Y C ≤ (⊥ : Subgroup G) := by
    intro C hCB hCnormal hquotCyclic
    letI : (C.subgroupOf B).Normal := hCnormal
    have hCne : C ≠ ⊥ := by
      intro hCbot
      subst C
      have hsubBot :
          (⊥ : Subgroup G).subgroupOf B = (⊥ : Subgroup B) := by
        ext b
        simp
      have hquotBot : IsCyclic (B ⧸ (⊥ : Subgroup B)) :=
        (QuotientGroup.quotientMulEquivOfEq hsubBot).isCyclic.mp
          hquotCyclic
      exact hBncyclic (QuotientGroup.quotientBot.isCyclic.mp hquotBot)
    obtain ⟨cC, hcne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
    let c : G := cC
    have hcC : c ∈ C := cC.property
    have hcneG : c ≠ 1 := by
      intro hc
      apply hcne
      apply Subtype.ext
      exact hc
    intro y hy
    let cA : A := ⟨c, hBA (hCB hcC)⟩
    let yY : Y := ⟨y, hy.1⟩
    have hcAne : cA ≠ 1 := by
      intro hc
      apply hcneG
      simpa only [cA, c, Subgroup.coe_one] using
        congrArg (fun z : A ↦ (z : G)) hc
    have hcomm : Commute (c : G) y :=
      hy.2 c hcC
    have hconj :
        (cA : G) * (yY : G) * (cA : G)⁻¹ = (yY : G) := by
      change c * y * c⁻¹ = y
      rw [hcomm.eq]
      simp
    have hyOne : yY = 1 := hreg cA hcAne yY hconj
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hyOne)
  have hYbot : Y ≤ (⊥ : Subgroup G) :=
    le_of_centralizerWithin_cocyclic_le_of_coprime_abelian_solvable
      hBcomm hBncyclic hBY hcopYB hYsol hcent
  exact hYne (le_bot_iff.mp hYbot)

/-- Action-form wrapper around
`quotient_regular_qgroup_isCyclic_12_12`.  Passing to the external
semidirect product lets the subgroup theorem be applied to a quotient
action without choosing representatives in an ambient group. -/
private theorem isCyclic_of_semiregular_action_12_12
    {Y A : Type u} [Group Y] [Finite Y] [Group A] [Finite A]
    [MulDistribMulAction A Y] {q : ℕ} [Fact q.Prime]
    (hAq : IsPGroup q A) (hAodd : Odd (Nat.card A))
    (hYsol : IsSolvable Y) (hYcard : Nat.card Y ≠ 1)
    (hreg : ∀ a : A, a ≠ 1 → ∀ y : Y, a • y = y → y = 1) :
    IsCyclic A := by
  classical
  let phi : A →* MulAut Y := MulDistribMulAction.toMulAut A Y
  let X := Y ⋊[phi] A
  let YX : Subgroup X := (SemidirectProduct.inl : Y →* X).range
  let AX : Subgroup X := (SemidirectProduct.inr : A →* X).range
  let eY : Y ≃* YX := MonoidHom.ofInjective
    (SemidirectProduct.inl_injective (N := Y) (G := A) (φ := phi))
  let eA : A ≃* AX := MonoidHom.ofInjective
    (SemidirectProduct.inr_injective (N := Y) (G := A) (φ := phi))
  letI : Finite X := by
    dsimp [X]
    exact Finite.of_equiv (Y × A)
      (SemidirectProduct.equivProd (N := Y) (G := A) (φ := phi)).symm
  letI : YX.Normal := by
    dsimp [YX]
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hAXq : IsPGroup q AX := hAq.of_equiv eA
  have hAXodd : Odd (Nat.card AX) := by
    rw [show Nat.card AX = Nat.card A from
      Nat.card_congr eA.toEquiv.symm]
    exact hAodd
  have hAXnorm : AX ≤ Subgroup.normalizer (YX : Set X) :=
    Subgroup.le_normalizer_of_normal
  have hYXsol : IsSolvable YX :=
    solvable_of_solvable_injective
      (f := eY.symm.toMonoidHom) eY.symm.injective
  have hYXne : YX ≠ ⊥ := by
    intro hbot
    apply hYcard
    have hcardYX : Nat.card YX = 1 := by
      rw [hbot]
      exact Nat.card_unique
    rw [show Nat.card YX = Nat.card Y from
      Nat.card_congr eY.toEquiv.symm] at hcardYX
    exact hcardYX
  have hregX : IsSemiregularConjugation YX AX := by
    intro a ha y hconj
    let a₀ : A := eA.symm a
    let y₀ : Y := eY.symm y
    have haEq : (a : X) = SemidirectProduct.inr a₀ := by
      exact (congrArg Subtype.val (eA.apply_symm_apply a)).symm
    have hyEq : (y : X) = SemidirectProduct.inl y₀ := by
      exact (congrArg Subtype.val (eY.apply_symm_apply y)).symm
    have ha₀ne : a₀ ≠ 1 := by
      intro ha₀
      apply ha
      apply eA.symm.injective
      simpa [a₀, ha₀]
    have hleft := congrArg SemidirectProduct.left hconj
    rw [haEq, hyEq] at hleft
    have hfix : a₀ • y₀ = y₀ := by
      simpa [X, phi] using hleft
    have hy₀ : y₀ = 1 := hreg a₀ ha₀ne y₀ hfix
    apply eY.symm.injective
    simpa [y₀, hy₀]
  have hAXcyclic : IsCyclic AX :=
    quotient_regular_qgroup_isCyclic_12_12
      hAXq hAXodd hAXnorm hYXsol hYXne hregX
  exact eA.isCyclic.mpr hAXcyclic

/-- Coq `BGsection12.v`, lines 209--212.  If a rank-two odd `q`-group
normalizes a nontrivial solvable group, and its action kernel is properly
contained in a cyclic subgroup, then some subgroup has both nontrivial
fixed points and nontrivial mixed commutator. -/
theorem exists_mixed_subgroup_of_rank_two_coprime_kernel_12_12
    {G : Type u} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime] {S Q Q₀ Q₁ : Subgroup G}
    (hSsol : IsSolvable S) (hSne : S ≠ ⊥)
    (hQnormS : Q ≤ Subgroup.normalizer (S : Set G))
    (hQq : IsPGroup q Q) (hQodd : Odd (Nat.card Q))
    (hQ₀ : Q₀ = centralizerWithin Q S)
    (hQ₀Q₁ : Q₀ ≤ Q₁) (hQ₁Q : Q₁ ≤ Q)
    (hQ₁cyclic : IsCyclic Q₁) (hQ₀ltQ₁ : Q₀ < Q₁)
    (hQrank : HasElementaryAbelianRankAtLeast q 2 Q) :
    ∃ X : Subgroup G,
      X ≤ Q ∧ centralizerWithin S X ≠ ⊥ ∧ ⁅S, X⁆ ≠ ⊥ := by
  classical
  by_contra hnone
  let i : Q →* Subgroup.normalizer (S : Set G) :=
    Subgroup.inclusion hQnormS
  let rho : Q →* MulAut S := S.normalizerMonoidHom.comp i
  let Q₀Q : Subgroup Q := Q₀.subgroupOf Q
  have hker : rho.ker = Q₀Q := by
    ext x
    change i x ∈ S.normalizerMonoidHom.ker ↔ (x : G) ∈ Q₀
    rw [Subgroup.normalizerMonoidHom_ker, hQ₀]
    simp only [centralizerWithin, Subgroup.mem_inf,
      Subgroup.mem_subgroupOf, x.property, true_and]
    rfl
  have hQ₀Qnormal : Q₀Q.Normal := by
    rw [← hker]
    infer_instance
  letI : Q₀Q.Normal := hQ₀Qnormal
  let pi : Q →* Q ⧸ Q₀Q := QuotientGroup.mk' Q₀Q
  let phi : (Q ⧸ Q₀Q) →* MulAut S :=
    QuotientGroup.lift Q₀Q rho hker.symm.le
  letI : MulDistribMulAction (Q ⧸ Q₀Q) S :=
    MulDistribMulAction.compHom S phi
  have hreg : ∀ a : Q ⧸ Q₀Q, a ≠ 1 → ∀ s : S,
      a • s = s → s = 1 := by
    intro a ha s hs
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q₀Q a
    have hxQ₀ : x ∉ Q₀Q := by
      intro hx
      exact ha ((QuotientGroup.eq_one_iff x).mpr hx)
    let X : Subgroup G := Subgroup.zpowers (x : G)
    have hXQ : X ≤ Q :=
      Subgroup.zpowers_le.mpr x.property
    have hcommNe : ⁅S, X⁆ ≠ ⊥ := by
      intro hcomm
      have hSCX : S ≤ Subgroup.centralizer (X : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hxCent : (x : G) ∈ Subgroup.centralizer (S : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.mp (hSCX hz)
          (x : G) (Subgroup.mem_zpowers (x : G))).symm
      apply hxQ₀
      change (x : G) ∈ Q₀
      rw [hQ₀]
      exact ⟨x.property, hxCent⟩
    have hcentBot : centralizerWithin S X = ⊥ := by
      by_contra hcent
      exact hnone ⟨X, hXQ, hcent, hcommNe⟩
    have hfixRho : rho x s = s := by
      change phi (QuotientGroup.mk' Q₀Q x) s = s at hs
      exact hs
    have hconj :
        (x : G) * (s : G) * (x : G)⁻¹ = (s : G) := by
      simpa [rho, i, Subgroup.normalizerMonoidHom, HSMul.hSMul] using
        congrArg Subtype.val hfixRho
    have hxs : Commute (x : G) (s : G) := by
      rw [commute_iff_eq]
      calc
        (x : G) * (s : G) =
            ((x : G) * (s : G) * (x : G)⁻¹) * (x : G) := by group
        _ = (s : G) * (x : G) := by rw [hconj]
    have hsCent : (s : G) ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (hxs.zpow_left n).eq
    have hsBot : (s : G) ∈ (⊥ : Subgroup G) := by
      rw [← hcentBot]
      exact ⟨s.property, hsCent⟩
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hsBot
  have hQbarq : IsPGroup q (Q ⧸ Q₀Q) := hQq.to_quotient Q₀Q
  have hQbarOdd : Odd (Nat.card (Q ⧸ Q₀Q)) :=
    hQodd.of_dvd_nat Q₀Q.card_quotient_dvd_card
  have hScard : Nat.card S ≠ 1 := by
    intro hcard
    exact hSne (Subgroup.card_eq_one.mp hcard)
  have hQbarCyclic : IsCyclic (Q ⧸ Q₀Q) :=
    isCyclic_of_semiregular_action_12_12
      hQbarq hQbarOdd hSsol hScard hreg
  let Q₁Q : Subgroup Q := Q₁.subgroupOf Q
  have hQ₀QleQ₁Q : Q₀Q ≤ Q₁Q := by
    intro x hx
    exact hQ₀Q₁ hx
  let Q₁bar : Subgroup (Q ⧸ Q₀Q) := Q₁Q.map pi
  have hQ₁barNe : Q₁bar ≠ ⊥ := by
    intro hbot
    have hQ₁QleQ₀Q : Q₁Q ≤ Q₀Q := by
      rw [← QuotientGroup.ker_mk' Q₀Q]
      exact (Subgroup.map_eq_bot_iff Q₁Q).mp hbot
    have hQ₁Q₀ : Q₁ ≤ Q₀ := by
      intro x hx
      let xQ : Q := ⟨x, hQ₁Q hx⟩
      exact hQ₁QleQ₀Q (show xQ ∈ Q₁Q from hx)
    exact hQ₀ltQ₁.2 hQ₁Q₀
  letI : IsCyclic (Q ⧸ Q₀Q) := hQbarCyclic
  have hQbarNe : Nat.card (Q ⧸ Q₀Q) ≠ 1 := by
    intro hcard
    letI : Subsingleton (Q ⧸ Q₀Q) :=
      (Nat.card_eq_one_iff_unique.mp hcard).1
    exact hQ₁barNe (Subgroup.eq_bot_of_subsingleton Q₁bar)
  have hOmegaBarCard : Nat.card (omegaOne q (Q ⧸ Q₀Q)) = q :=
    card_omegaOne_of_isCyclic_isPGroup Fact.out hQbarq hQbarNe
  have hQ₁barq : IsPGroup q Q₁bar := hQbarq.to_subgroup Q₁bar
  have hQ₁barCyclic : IsCyclic Q₁bar :=
    Subgroup.isCyclic_of_le le_top
  letI : IsCyclic Q₁bar := hQ₁barCyclic
  have hQ₁barCard : Nat.card Q₁bar ≠ 1 := by
    intro hcard
    exact hQ₁barNe (Subgroup.card_eq_one.mp hcard)
  have hOmegaQ₁barCard : Nat.card (omegaOne q Q₁bar) = q :=
    card_omegaOne_of_isCyclic_isPGroup
      Fact.out hQ₁barq hQ₁barCard
  let O₁ : Subgroup (Q ⧸ Q₀Q) :=
    (omegaOne q Q₁bar).map Q₁bar.subtype
  have hO₁le : O₁ ≤ omegaOne q (Q ⧸ Q₀Q) :=
    map_omegaOne_le q Q₁bar.subtype
  have hO₁card : Nat.card O₁ = q := by
    dsimp [O₁]
    rw [Subgroup.card_map_of_injective Q₁bar.subtype_injective,
      hOmegaQ₁barCard]
  have hO₁eq : O₁ = omegaOne q (Q ⧸ Q₀Q) :=
    Subgroup.eq_of_le_of_card_ge hO₁le (by
      rw [hOmegaBarCard, hO₁card])
  have hOmegaBarLeQ₁bar : omegaOne q (Q ⧸ Q₀Q) ≤ Q₁bar := by
    rw [← hO₁eq]
    exact Subgroup.map_subtype_le (omegaOne q Q₁bar)
  have hmapOmegaLe :
      (omegaOne q Q).map pi ≤ Q₁Q.map pi :=
    (map_omegaOne_le q pi).trans hOmegaBarLeQ₁bar
  have hOmegaQleQ₁Q : omegaOne q Q ≤ Q₁Q := by
    have hle := Subgroup.map_le_map_iff.mp hmapOmegaLe
    rw [QuotientGroup.ker_mk', sup_eq_left.mpr hQ₀QleQ₁Q] at hle
    exact hle
  obtain ⟨E, hEQ, hE⟩ := hQrank
  let EQ : Subgroup Q := E.subgroupOf Q
  have hEQOmega : EQ ≤ omegaOne q Q := by
    intro x hx
    apply mem_omegaOne_of_pow_eq_one q
    apply Subtype.ext
    exact congrArg (fun z : E ↦ (z : G))
      (hE.pow_eq_one ⟨(x : G), hx⟩)
  have hEQ₁ : E ≤ Q₁ := by
    intro x hx
    let xQ : Q := ⟨x, hEQ hx⟩
    exact hOmegaQleQ₁Q (hEQOmega (show xQ ∈ EQ from hx))
  let E₁ : Subgroup Q₁ := E.subgroupOf Q₁
  letI : IsCyclic Q₁ := hQ₁cyclic
  have hE₁cyclic : IsCyclic E₁ := Subgroup.isCyclic_of_le le_top
  have hEcyclic : IsCyclic E :=
    (Subgroup.subgroupOfEquivOfLe hEQ₁).isCyclic.mp hE₁cyclic
  exact hE.not_isCyclic Fact.out hEcyclic

/-! ## Cyclic factors in rank two -/

/-- A commutative finite group of generator rank at most two is
metacyclic.  Kept local because the existing converse file uses this only
inside its rank-three contradiction. -/
private theorem isMetacyclic_of_isMulCommutative_rank_le_two_12_12
    {K : Type u} [Group K] [Finite K]
    (hKcomm : IsMulCommutative K) (hRank : Group.rank K ≤ 2) :
    IsMetacyclic K := by
  classical
  letI : IsMulCommutative K := hKcomm
  obtain ⟨S, hScard, hSgen⟩ := Group.rank_spec K
  have hCard : S.card ≤ 2 := by omega
  interval_cases h : S.card
  · have hRankZero : Group.rank K = 0 := by omega
    haveI : Subsingleton K := Group.rank_eq_zero_iff.mp hRankZero
    exact isMetacyclic_of_isCyclic K isCyclic_of_subsingleton
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h
    have hx : Subgroup.zpowers x = (⊤ : Subgroup K) := by
      rw [Subgroup.zpowers_eq_closure]
      simpa only [Finset.coe_singleton] using hSgen
    exact isMetacyclic_of_isMulCommutative_of_two_generators x 1 (by
      simp only [hx, Subgroup.zpowers_one_eq_bot, sup_bot_eq])
  · obtain ⟨x, y, _hxy, rfl⟩ := Finset.card_eq_two.mp h
    apply isMetacyclic_of_isMulCommutative_of_two_generators x y
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    simpa only [Finset.coe_insert, Finset.coe_singleton,
      Set.singleton_union] using hSgen

/-- In an abelian `p`-group of exact cardinal rank two, the nontrivial
commutator and fixed-point factors of a coprime action are both cyclic.
The direct-product decomposition is returned with them so downstream code
does not have to reconstruct its coercions. -/
theorem cyclic_factors_of_rank_two_coprime_decomposition_12_12
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {S X : Subgroup G}
    (hSp : IsPGroup p S)
    (hSodd : Odd (Nat.card S))
    (hScomm : IsMulCommutative S)
    (hRankTwo : HasElementaryAbelianRankAtLeast p 2 S)
    (hNoRankThree : ¬ HasElementaryAbelianRankAtLeast p 3 S)
    (hXnormS : X ≤ Subgroup.normalizer (S : Set G))
    (hcop : Nat.Coprime (Nat.card S) (Nat.card X))
    (hcommNe : ⁅S, X⁆ ≠ ⊥)
    (hcentNe : centralizerWithin S X ≠ ⊥) :
    IsCyclic (⁅S, X⁆ : Subgroup G) ∧
      IsCyclic (centralizerWithin S X) ∧
      IsInternalDirectProductIn ⁅S, X⁆
        (centralizerWithin S X) S := by
  classical
  have hdir :
      IsInternalDirectProductIn ⁅S, X⁆
        (centralizerWithin S X) S :=
    coprime_abelian_commutator_centralizer_directProduct_12_12
      hXnormS hcop hScomm
  have hRankLe : Group.rank S ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ Group.rank S := by omega
    obtain ⟨E, hES, hE⟩ :=
      exists_elementaryAbelian_rank_three_le_of_group_rank
        S hSp hScomm hthree
    exact hNoRankThree ⟨E, hES, hE⟩
  have hSmeta : IsMetacyclic S :=
    isMetacyclic_of_isMulCommutative_rank_le_two_12_12 hScomm hRankLe
  have hSncyclic : ¬ IsCyclic S := by
    intro hScyclic
    obtain ⟨E, hES, hE⟩ := hRankTwo
    let ES : Subgroup S := E.subgroupOf S
    letI : IsCyclic S := hScyclic
    have hEScyclic : IsCyclic ES := Subgroup.isCyclic_of_le le_top
    have hEcyclic : IsCyclic E :=
      (Subgroup.subgroupOfEquivOfLe hES).isCyclic.mp hEScyclic
    exact hE.not_isCyclic Fact.out hEcyclic
  let T : Subgroup G := ⁅S, X⁆
  let C : Subgroup G := centralizerWithin S X
  let TS : Subgroup S := T.subgroupOf S
  let CS : Subgroup S := C.subgroupOf S
  have hTSne : TS ≠ ⊥ := by
    intro hbot
    apply hcommNe
    rw [← Subgroup.map_subgroupOf_eq_of_le hdir.left_le,
      show T.subgroupOf S = TS from rfl, hbot, Subgroup.map_bot]
  have hCSne : CS ≠ ⊥ := by
    intro hbot
    apply hcentNe
    rw [← Subgroup.map_subgroupOf_eq_of_le hdir.right_le,
      show C.subgroupOf S = CS from rfl, hbot, Subgroup.map_bot]
  have hcyclicPair : IsCyclic TS ∧ IsCyclic CS :=
    isCyclic_pair_of_disjoint_of_isMetacyclic
      hSp hSodd hSmeta hSncyclic TS CS hdir.complement.disjoint
        hTSne hCSne
  have hTcyclic : IsCyclic T :=
    (Subgroup.subgroupOfEquivOfLe hdir.left_le).isCyclic.mp
      hcyclicPair.1
  have hCcyclic : IsCyclic C :=
    (Subgroup.subgroupOfEquivOfLe hdir.right_le).isCyclic.mp
      hcyclicPair.2
  exact ⟨by simpa only [T] using hTcyclic,
    by simpa only [C] using hCcyclic, hdir⟩

/-! ## Exponent and the larger cyclic factor -/

/-- For a direct product of two cyclic subgroups of a finite `p`-group,
the exponent is the larger of the two factor orders. -/
theorem exponent_eq_max_card_of_cyclic_pgroup_direct_product_12_12
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {S T C : Subgroup G}
    (hSp : IsPGroup p S)
    (hTcyclic : IsCyclic T)
    (hCcyclic : IsCyclic C)
    (hdir : IsInternalDirectProductIn T C S) :
    Monoid.exponent S = max (Nat.card T) (Nat.card C) := by
  classical
  letI : IsCyclic T := hTcyclic
  letI : IsCyclic C := hCcyclic
  have hTp : IsPGroup p T := hSp.to_le hdir.left_le
  have hCp : IsPGroup p C := hSp.to_le hdir.right_le
  obtain ⟨m, hTm⟩ := hTp.exists_card_eq
  obtain ⟨n, hCn⟩ := hCp.exists_card_eq
  have hExp : Monoid.exponent S =
      Nat.lcm (Nat.card T) (Nat.card C) := by
    calc
      Monoid.exponent S = Monoid.exponent (T × C) :=
        (Monoid.exponent_eq_of_mulEquiv hdir.mulEquiv).symm
      _ = Nat.lcm (Monoid.exponent T) (Monoid.exponent C) :=
        Monoid.exponent_prod
      _ = Nat.lcm (Nat.card T) (Nat.card C) := by
        rw [IsCyclic.exponent_eq_card, IsCyclic.exponent_eq_card]
  rw [hExp, hTm, hCn]
  rcases le_total m n with hmn | hnm
  · rw [Nat.lcm_eq_right_iff_dvd.mpr (pow_dvd_pow p hmn),
      Nat.max_eq_right
        (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hmn)]
  · rw [Nat.lcm_eq_left_iff_dvd.mpr (pow_dvd_pow p hnm),
      Nat.max_eq_left
        (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hnm)]

/-- Raw output of the noncentral rank-two split.  The selected factor is
normal in `U`, cyclic, exponent-preserving, and has characteristic omega
subgroup normalized by the whole normalizer of `S`. -/
structure CoprimeSplitWitness12_12
    {G : Type u} [Group G]
    (U S : Subgroup G) (p : ℕ) where
  Z : Subgroup G
  Z_ne_bot : Z ≠ ⊥
  Z_le_S : Z ≤ S
  Z_normal_U : (Z.subgroupOf U).Normal
  Z_cyclic : IsCyclic Z
  exponent_eq : Monoid.exponent Z = Monoid.exponent S
  normalizer_le_normalizer_omega :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer
        (((omegaOne p Z).map Z.subtype : Subgroup G) : Set G)

/-- The ambient image of a characteristic subgroup is normalized by the
ambient normalizer. -/
private theorem characteristic_map_subtype_le_normalizer_12_12
    {G : Type u} [Group G] (H : Subgroup G)
    (R : Subgroup H) [R.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (R.map H.subtype : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact characteristic_map_subtype_invariant_under_normalizer
      H (Subgroup.normalizer (H : Set G)) R le_rfl g hg r hr
  · intro hr
    have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).inv_mem hg
    have hback := characteristic_map_subtype_invariant_under_normalizer
      H (Subgroup.normalizer (H : Set G)) R le_rfl
      g⁻¹ hginv (g * r * g⁻¹) hr
    have hcancel : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by
      group
    simpa only [hcancel] using hback

/-- Choose the larger cyclic factor in the noncentral coprime split.

The two normalizer hypotheses are the direct output of
`abelian_tau2_norm_Sylow`; all remaining conclusions are finite abelian
`p`-group calculations. -/
noncomputable def exists_coprime_split_witness_12_12
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {U S X : Subgroup G}
    (hSU : S ≤ U)
    (hUnormS : U ≤ Subgroup.normalizer (S : Set G))
    (hSp : IsPGroup p S)
    (hSodd : Odd (Nat.card S))
    (hScomm : IsMulCommutative S)
    (hRankTwo : HasElementaryAbelianRankAtLeast p 2 S)
    (hNoRankThree : ¬ HasElementaryAbelianRankAtLeast p 3 S)
    (hXnormS : X ≤ Subgroup.normalizer (S : Set G))
    (hcop : Nat.Coprime (Nat.card S) (Nat.card X))
    (hcommNe : ⁅S, X⁆ ≠ ⊥)
    (hcentNe : centralizerWithin S X ≠ ⊥)
    (hNormComm :
      Subgroup.normalizer (S : Set G) ≤
        Subgroup.normalizer ((⁅S, X⁆ : Subgroup G) : Set G))
    (hNormCent :
      Subgroup.normalizer (S : Set G) ≤
        Subgroup.normalizer (centralizerWithin S X : Set G)) :
    CoprimeSplitWitness12_12 U S p := by
  classical
  let T : Subgroup G := ⁅S, X⁆
  let C : Subgroup G := centralizerWithin S X
  obtain ⟨hTcyclic, hCcyclic, hdir⟩ :=
    cyclic_factors_of_rank_two_coprime_decomposition_12_12
      hSp hSodd hScomm hRankTwo hNoRankThree hXnormS hcop
        hcommNe hcentNe
  have hExpMax : Monoid.exponent S =
      max (Nat.card T) (Nat.card C) :=
    exponent_eq_max_card_of_cyclic_pgroup_direct_product_12_12
      hSp hTcyclic hCcyclic hdir
  by_cases hcard : Nat.card T < Nat.card C
  · have hCU : C ≤ U := hdir.right_le.trans hSU
    have hCnormalU : (C.subgroupOf U).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCU).mpr
        (hUnormS.trans hNormCent)
    have hExpC : Monoid.exponent C = Monoid.exponent S := by
      letI : IsCyclic C := hCcyclic
      calc
        Monoid.exponent C = Nat.card C := IsCyclic.exponent_eq_card
        _ = max (Nat.card T) (Nat.card C) :=
          (Nat.max_eq_right hcard.le).symm
        _ = Monoid.exponent S := hExpMax.symm
    refine
      { Z := C
        Z_ne_bot := by simpa only [C] using hcentNe
        Z_le_S := hdir.right_le
        Z_normal_U := hCnormalU
        Z_cyclic := hCcyclic
        exponent_eq := hExpC
        normalizer_le_normalizer_omega := ?_ }
    exact hNormCent.trans
      (characteristic_map_subtype_le_normalizer_12_12
        C (omegaOne p C))
  · have hCT : Nat.card C ≤ Nat.card T := Nat.le_of_not_gt hcard
    have hTU : T ≤ U := hdir.left_le.trans hSU
    have hTnormalU : (T.subgroupOf U).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTU).mpr
        (hUnormS.trans hNormComm)
    have hExpT : Monoid.exponent T = Monoid.exponent S := by
      letI : IsCyclic T := hTcyclic
      calc
        Monoid.exponent T = Nat.card T := IsCyclic.exponent_eq_card
        _ = max (Nat.card T) (Nat.card C) :=
          (Nat.max_eq_left hCT).symm
        _ = Monoid.exponent S := hExpMax.symm
    refine
      { Z := T
        Z_ne_bot := by simpa only [T] using hcommNe
        Z_le_S := hdir.left_le
        Z_normal_U := hTnormalU
        Z_cyclic := hTcyclic
        exponent_eq := hExpT
        normalizer_le_normalizer_omega := ?_ }
    exact hNormComm.trans
      (characteristic_map_subtype_le_normalizer_12_12
        T (omegaOne p T))

end

end Submission.OddOrder.BG.Section12
