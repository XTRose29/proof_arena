import Submission.OddOrder.BG.Section07.SCNRankTwoSubgroup
import Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGenerationSolvable
import Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientExponent
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Centralizer generation for an extraspecial coprime actor

This is the quotient-action step in `BGsection12.v`, lines 2111--2143.
The center quotient of the extraspecial actor is noncyclic abelian.  Its
nonidentity cyclic subgroups lift to elementary-abelian rank-two subgroups,
so the solvable abelian centralizer-generation theorem applies.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

private theorem isMulCommutative_of_mulEquiv_source
    {H K : Type u} [Group H] [Group K]
    (hH : IsMulCommutative H) (e : H ≃* K) :
    IsMulCommutative K := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply e.symm.injective
  simpa only [map_mul] using
    (isMulCommutative_iff.mp hH (e.symm x) (e.symm y))

/-- A noncentral element together with the center of an extraspecial
`p`-group of exponent dividing `p` generates an elementary-abelian subgroup
of rank two. -/
private theorem rankTwo_zpowers_sup_center_of_extraspecial
    {Q : Type u} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (hQextra : IsExtraspecial Q) (hQp : IsPGroup p Q)
    (hQexp : Monoid.exponent Q ∣ p) {q : Q}
    (hq : q ∉ Subgroup.center Q) :
    IsElementaryAbelianOfRank p 2
      (Subgroup.zpowers q ⊔ Subgroup.center Q) := by
  classical
  have hZcard : Nat.card (Subgroup.center Q) = p :=
    hQextra.center_card_eq hQp
  have hZrank :
      IsElementaryAbelianOfRank p 1 (Subgroup.center Q) :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hZcard
  have hqne : q ≠ 1 := fun hqOne ↦ hq (hqOne ▸ (Subgroup.center Q).one_mem)
  have hqpow : q ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hQexp q
  have hqorder : orderOf q = p :=
    ((Nat.dvd_prime (Fact.out : p.Prime)).mp
      (orderOf_dvd_of_pow_eq_one hqpow)).resolve_left
        (by simpa [orderOf_eq_one_iff] using hqne)
  let X : Subgroup Q := Subgroup.zpowers q
  have hXcard : Nat.card X = p := by
    dsimp only [X]
    rw [Nat.card_zpowers, hqorder]
  have hXrank : IsElementaryAbelianOfRank p 1 X :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
  have hXZdis : Disjoint X (Subgroup.center Q) := by
    rw [disjoint_iff]
    by_contra hne
    have hcardNe :
        Nat.card (X ⊓ Subgroup.center Q : Subgroup Q) ≠ 1 :=
      fun hc ↦ hne (Subgroup.card_eq_one.mp hc)
    have hcardDvd :
        Nat.card (X ⊓ Subgroup.center Q : Subgroup Q) ∣ p := by
      simpa [hZcard] using Subgroup.card_dvd_of_le
        (inf_le_right : X ⊓ Subgroup.center Q ≤ Subgroup.center Q)
    have hcard : Nat.card (X ⊓ Subgroup.center Q : Subgroup Q) = p :=
      ((Nat.dvd_prime (Fact.out : p.Prime)).mp hcardDvd).resolve_left
        hcardNe
    have hinf : X ⊓ Subgroup.center Q = X :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hXcard])
    have hqCenter : q ∈ Subgroup.center Q := by
      have hqInf : q ∈ X ⊓ Subgroup.center Q := by
        rw [hinf]
        exact Subgroup.mem_zpowers q
      exact hqInf.2
    exact hq hqCenter
  have hXZcomm :
      ∀ x ∈ X, ∀ z ∈ Subgroup.center Q, Commute x z := by
    intro x _hx z hz
    rw [commute_iff_eq]
    exact Subgroup.mem_center_iff.mp hz x
  simpa [X] using
    isElementaryAbelianOfRank_sup_of_disjoint_of_commute
      hQp hXrank hZrank hXZdis hXZcomm

/-- The center quotient of an extraspecial component generates the
centralizer of the ambient omega-one center from the fixed points of its
rank-two subgroups.

The rank-three exclusion is retained in the interface used by Section 12;
the quotient-action argument itself only needs the displayed central-product
and exponent hypotheses. -/
theorem le_of_rankTwo_centralizers_of_coprime_extraspecial_action
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {Q C Y K : Subgroup G}
    (hQextra : IsExtraspecial Q)
    (hQexp : Monoid.exponent Q ∣ p)
    (_hNoRank : ¬ ∃ E : Subgroup P,
      IsElementaryAbelianOfRank p 3 E)
    (hQP : Q ≤ (P : Subgroup G))
    (hCQ : C ≤ Subgroup.centralizer (Q : Set G))
    (hQC : Q ⊔ C = (P : Subgroup G))
    (hQnormY : Q ≤ Subgroup.normalizer (Y : Set G))
    (hcop : (Nat.card Y).Coprime (Nat.card Q))
    (hsol : IsSolvable (centralizerWithin Y
      (Submission.OddOrder.BG.Section07.omegaOneCenterAmbient
        p (P : Subgroup G))))
    (hfixed : ∀ A : Subgroup G, A ≤ Q →
      IsElementaryAbelianOfRank p 2 A →
      centralizerWithin Y A ≤ K) :
    centralizerWithin Y
      (Submission.OddOrder.BG.Section07.omegaOneCenterAmbient
        p (P : Subgroup G)) ≤ K := by
  classical
  let P0 : Subgroup G := (P : Subgroup G)
  let Z : Subgroup G :=
    Submission.OddOrder.BG.Section07.omegaOneCenterAmbient p P0
  let D : Subgroup G := centralizerWithin Y Z
  let ZQ : Subgroup G := (Subgroup.center Q).map Q.subtype
  change D ≤ K
  have hQp : IsPGroup p Q := P.isPGroup'.to_le hQP
  have hZQleP : ZQ ≤ P0 := by
    exact (Subgroup.map_subtype_le (Subgroup.center Q)).trans hQP
  have hZQcenterP : ZQ ≤ centerWithin P0 := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hQP z.property, ?_⟩
    have hzCentQ : (z : G) ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hz ⟨q, hq⟩)
    have hzCentC : (z : G) ∈ Subgroup.centralizer (C : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_iff.mp (hCQ hc)
        (z : G) z.property).symm
    have hzCentSup :
        (z : G) ∈ Subgroup.centralizer ((Q ⊔ C : Subgroup G) : Set G) := by
      rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_iff]
      intro x hx
      rcases hx with hx | hx
      · exact Subgroup.mem_centralizer_iff.mp hzCentQ x hx
      · exact Subgroup.mem_centralizer_iff.mp hzCentC x hx
    rw [hQC] at hzCentSup
    exact Subgroup.mem_centralizer_iff.mp hzCentSup
  have hZQleZ : ZQ ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩
    have hzCenterAmbient : (z : G) ∈ centerWithin P0 :=
      hZQcenterP ⟨z, hz, rfl⟩
    let zP : P0 := ⟨z, hzCenterAmbient.1⟩
    have hzCenterP : zP ∈ Subgroup.center P0 := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact hzCenterAmbient.2 x x.property
    let zCenter : Subgroup.center P0 := ⟨zP, hzCenterP⟩
    have hzpowQ : z ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hQexp z
    have hzpowG : (z : G) ^ p = 1 := by
      simpa using congrArg (fun x : Q ↦ (x : G)) hzpowQ
    have hzpowCenter : zCenter ^ p = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hzpowG
    dsimp only [Z,
      Submission.OddOrder.BG.Section07.omegaOneCenterAmbient]
    exact ⟨zP, ⟨zCenter,
      mem_omegaOne_of_pow_eq_one p hzpowCenter, rfl⟩, rfl⟩
  have hZcenterP : Z ≤ centerWithin P0 := by
    dsimp only [Z]
    exact
      Submission.OddOrder.BG.Section07.omegaOneCenterAmbient_le_centerWithin
        p P0
  have hQnormD : Q ≤ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq d hd
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hQnormY hq) d).mp hd.1, ?_⟩
    intro z hz
    have hqz : Commute q z := (hZcenterP hz).2 q (hQP hq)
    have hzd : z * d = d * z := hd.2 z hz
    have hzdComm : Commute z d := hzd
    have hzq : Commute z q := hqz.symm
    exact ((hzq.mul_right hzdComm).mul_right hzq.inv_right).eq
  letI := subgroupConjugationAction D Q hQnormD
  let rho : Q →* MulAut D := MulDistribMulAction.toMulAut Q D
  have hcenterKer : Subgroup.center Q ≤ rho.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    have hdcomm : (z : G) * (d : G) = (d : G) * z :=
      d.property.2 (z : G) (hZQleZ ⟨z, hz, rfl⟩)
    have hcoe := coe_subgroupConjugationAction_smul D Q hQnormD z d
    change ((rho z d : D) : G) = (d : G)
    rw [show ((rho z d : D) : G) =
        (z : G) * (d : G) * (z : G)⁻¹ by
      simpa [rho] using hcoe]
    calc
      (z : G) * (d : G) * (z : G)⁻¹ =
          (d : G) * (z : G) * (z : G)⁻¹ := by rw [hdcomm]
      _ = d := by simp
  let phi : (Q ⧸ Subgroup.center Q) →* MulAut D :=
    QuotientGroup.lift (Subgroup.center Q) rho hcenterKer
  let X := D ⋊[phi] (Q ⧸ Subgroup.center Q)
  let DY : Subgroup X :=
    (SemidirectProduct.inl : D →* X).range
  let A : Subgroup X :=
    (SemidirectProduct.inr : (Q ⧸ Subgroup.center Q) →* X).range
  let DK : Subgroup D := K.comap D.subtype
  let KX : Subgroup X :=
    DK.map (SemidirectProduct.inl : D →* X)
  let eD : D ≃* DY := MonoidHom.ofInjective
    (SemidirectProduct.inl_injective
      (N := D) (G := Q ⧸ Subgroup.center Q) (φ := phi))
  let eA : (Q ⧸ Subgroup.center Q) ≃* A := MonoidHom.ofInjective
    (SemidirectProduct.inr_injective
      (N := D) (G := Q ⧸ Subgroup.center Q) (φ := phi))
  letI : Finite X := by
    dsimp [X]
    exact Finite.of_equiv (D × (Q ⧸ Subgroup.center Q))
      (SemidirectProduct.equivProd
        (N := D) (G := Q ⧸ Subgroup.center Q) (φ := phi)).symm
  have hQbarComm : IsMulCommutative (Q ⧸ Subgroup.center Q) :=
    hQextra.quotient_center_isMulCommutative
  have hAcomm : IsMulCommutative A :=
    isMulCommutative_of_mulEquiv_source hQbarComm eA
  have hQbarNcyc : ¬ IsCyclic (Q ⧸ Subgroup.center Q) := by
    intro hcyc
    letI : IsCyclic (Q ⧸ Subgroup.center Q) := hcyc
    exact hQextra.not_isMulCommutative
      (isMulCommutative_of_isCyclic_quotient_center_self Q)
  have hAncyc : ¬ IsCyclic A := by
    intro hcyc
    exact hQbarNcyc (eA.isCyclic.mpr hcyc)
  letI : DY.Normal := by
    dsimp [DY]
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hAnormDY : A ≤ Subgroup.normalizer (DY : Set X) :=
    Subgroup.le_normalizer_of_normal
  have hcardDY : Nat.card DY = Nat.card D :=
    Nat.card_congr eD.toEquiv.symm
  have hcardA : Nat.card A = Nat.card (Q ⧸ Subgroup.center Q) :=
    Nat.card_congr eA.toEquiv.symm
  have hDdivY : Nat.card D ∣ Nat.card Y :=
    Subgroup.card_dvd_of_le (centralizerWithin_le_left Y Z)
  have hQbarDivQ : Nat.card (Q ⧸ Subgroup.center Q) ∣ Nat.card Q :=
    (Subgroup.center Q).card_quotient_dvd_card
  have hcopDA : (Nat.card DY).Coprime (Nat.card A) := by
    rw [hcardDY, hcardA]
    exact (hcop.coprime_dvd_left hDdivY).coprime_dvd_right hQbarDivQ
  letI : IsSolvable D := by
    simpa only [D, Z, P0] using hsol
  have hDYsol : IsSolvable DY :=
    solvable_of_solvable_injective
      (f := eD.symm.toMonoidHom) eD.symm.injective
  have hcent : ∀ a : X, a ∈ A → a ≠ 1 →
      centralizerWithin DY (Subgroup.zpowers a) ≤ KX := by
    intro a haA haOne x hx
    rcases haA with ⟨aq, rfl⟩
    have haqOne : aq ≠ 1 := by
      intro haq
      apply haOne
      rw [haq, map_one]
    obtain ⟨q, rfl⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center Q) aq
    have hqNotCenter : q ∉ Subgroup.center Q := by
      intro hq
      apply haqOne
      exact (QuotientGroup.eq_one_iff q).mpr hq
    let BQ : Subgroup Q := Subgroup.zpowers q ⊔ Subgroup.center Q
    let B : Subgroup G := BQ.map Q.subtype
    have hBQrank : IsElementaryAbelianOfRank p 2 BQ := by
      simpa [BQ] using rankTwo_zpowers_sup_center_of_extraspecial
        hQextra hQp hQexp hqNotCenter
    have hBrank : IsElementaryAbelianOfRank p 2 B := by
      exact hBQrank.map_of_injective Q.subtype Q.subtype_injective
    have hBQ : B ≤ Q := Subgroup.map_subtype_le BQ
    rcases hx.1 with ⟨d, rfl⟩
    have hmul := hx.2
      (SemidirectProduct.inr
        (QuotientGroup.mk' (Subgroup.center Q) q))
      (Subgroup.mem_zpowers
        (SemidirectProduct.inr
          (QuotientGroup.mk' (Subgroup.center Q) q)))
    have hleft := congrArg SemidirectProduct.left hmul
    dsimp [X] at hleft
    simp only [one_mul, map_one, mul_one] at hleft
    have hfixRho : rho q d = d := by
      simpa [phi] using hleft
    have hfixAction : ((q • d : D) : G) = (d : G) := by
      simpa [rho] using congrArg Subtype.val hfixRho
    rw [coe_subgroupConjugationAction_smul D Q hQnormD q d] at hfixAction
    have hqd : Commute (q : G) (d : G) := by
      rw [commute_iff_eq]
      calc
        (q : G) * (d : G) =
            ((q : G) * (d : G) * (q : G)⁻¹) * (q : G) := by group
        _ = (d : G) * (q : G) := by rw [hfixAction]
    have hdCentX :
        (d : G) ∈ Subgroup.centralizer
          (Subgroup.zpowers (q : G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hqd.zpow_left n).eq
    have hdCentZQ :
        (d : G) ∈ Subgroup.centralizer (ZQ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact d.property.2 z (hZQleZ hz)
    have hBeq : B = Subgroup.zpowers (q : G) ⊔ ZQ := by
      dsimp [B, BQ, ZQ]
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      have hqcoe : Q.subtype q = (q : G) := rfl
      rw [hqcoe]
    have hdCentB : (d : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [hBeq, Subgroup.sup_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hy with hy | hy
      · exact Subgroup.mem_centralizer_iff.mp hdCentX y hy
      · exact Subgroup.mem_centralizer_iff.mp hdCentZQ y hy
    have hdK : (d : G) ∈ K :=
      hfixed B hBQ hBrank ⟨d.property.1, hdCentB⟩
    exact ⟨d, hdK, rfl⟩
  have hDYKX : DY ≤ KX :=
    le_of_centralizerWithin_zpowers_le_of_coprime_abelian_solvable
      hAcomm hAncyc hAnormDY hcopDA hDYsol hcent
  intro d hd
  let dD : D := ⟨d, hd⟩
  have hdDY : (SemidirectProduct.inl dD : X) ∈ DY := ⟨dD, rfl⟩
  rcases hDYKX hdDY with ⟨k, hk, hkEq⟩
  have hkd : k = dD :=
    SemidirectProduct.inl_injective hkEq
  have hkK : (k : G) ∈ K := hk
  simpa [hkd, dD] using hkK

end Submission.OddOrder.MathlibSupport
