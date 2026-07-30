import Submission.OddOrder.BG.Section08.PrimeSetCoreIntersection
import Submission.OddOrder.MathlibSupport.AmbientFitting
import Submission.OddOrder.MathlibSupport.CoprimeSolvableCentralProduct
import Submission.OddOrder.MathlibSupport.NilpotentPrimeCores
import Submission.OddOrder.MathlibSupport.PMaxElem
import Submission.OddOrder.MathlibSupport.PPrimeCoreCentralizer

/-!
# Bender--Glauberman Theorem 8.1(a): the constrained centralizer

This file ports the setup of Theorem 8.1(a) through the proof that the
centralizer of a maximal elementary-abelian subgroup in the Fitting subgroup
is normed constrained.
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open scoped commutatorElement

universe u

/-- Restriction of an ambient `p'`-core to a subgroup is contained in that
subgroup's `p'`-core. -/
theorem inf_map_pPrimeCore_le_map_pPrimeCore
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) {H K : Subgroup G} (hHK : H ≤ K) :
    H ⊓ (pPrimeCore p K).map K.subtype ≤
      (pPrimeCore p H).map H.subtype := by
  let Q : Subgroup G := (pPrimeCore p K).map K.subtype
  let L : Subgroup G := H ⊓ Q
  have hQK : Q ≤ K := by
    dsimp [Q]
    exact Subgroup.map_subtype_le _
  have hQnormalK : (Q.subgroupOf K).Normal := by
    dsimp [Q]
    change (((pPrimeCore p K).map K.subtype).comap K.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    infer_instance
  have hLnormalH : (L.subgroupOf H).Normal := by
    letI : (Q.subgroupOf K).Normal := hQnormalK
    have hn := Subgroup.inf_subgroupOf_inf_normal_of_right H Q K
    change ((H ⊓ Q).subgroupOf H).Normal
    rw [inf_eq_left.mpr hHK] at hn
    exact hn
  have hLprime : IsPPrimeSubgroup p L := by
    rw [IsPPrimeSubgroup]
    have hQcard : Nat.card Q = Nat.card (pPrimeCore p K) := by
      dsimp [Q]
      exact Subgroup.card_map_of_injective K.subtype_injective
    have hQprime : Nat.Coprime p (Nat.card Q) := by
      rw [hQcard]
      exact pPrimeCore_coprime_card
    exact hQprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  have hLsubprime : IsPPrimeSubgroup p (L.subgroupOf H) := by
    rw [IsPPrimeSubgroup, natCard_subgroupOf_eq
      (show L ≤ H from inf_le_left)]
    exact hLprime
  have hLcore : L.subgroupOf H ≤ pPrimeCore p H :=
    le_pPrimeCore hLsubprime hLnormalH
  change L ≤ (pPrimeCore p H).map H.subtype
  rw [← Subgroup.map_subgroupOf_eq_of_le (show L ≤ H from inf_le_left)]
  exact Subgroup.map_mono hLcore

/-- The `p'`-core of the normalizer of a `p`-subgroup in a solvable group
is contained in the ambient `p'`-core. -/
theorem map_pPrimeCore_inf_normalizer_le_map_pPrimeCore
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] {X R : Subgroup G}
    (hRX : R ≤ X) (hRp : IsPGroup p R)
    (hXsol : IsSolvable X) :
    (pPrimeCore p ↥(X ⊓ Subgroup.normalizer (R : Set G))).map
        (X ⊓ Subgroup.normalizer (R : Set G)).subtype ≤
      (pPrimeCore p X).map X.subtype := by
  let N : Subgroup G := X ⊓ Subgroup.normalizer (R : Set G)
  let RN : Subgroup N := R.subgroupOf N
  let O : Subgroup N := pPrimeCore p N
  have hRN : R ≤ N := by
    exact le_inf hRX Subgroup.le_normalizer
  have hRNp : IsPGroup p RN := by
    exact hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm
  have hRNnormal : RN.Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    intro n hn
    exact hn.2
  have hdis : Disjoint O RN := by
    exact disjoint_pPrimeCore_of_isPGroup hRNp |>.symm
  have hcomm : O ≤ Subgroup.centralizer (RN : Set N) := by
    have hc := Subgroup.commute_of_normal_of_disjoint
      O RN (by infer_instance) hRNnormal hdis
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (hc o r ho hr).eq.symm
  have hmapCent : O.map N.subtype ≤ centralizerWithin X R := by
    rintro _ ⟨o, ho, rfl⟩
    refine ⟨o.property.1, ?_⟩
    intro r hr
    let rN : N := ⟨r, hRN hr⟩
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp (hcomm ho) rN hr)
  have hcentN : centralizerWithin X R ≤ N := by
    exact le_inf (centralizerWithin_le_left X R)
      (inf_le_right.trans
        (Subgroup.centralizer_le_normalizer (R : Set G)))
  have hmapCoreCent : O.map N.subtype ≤
      (pPrimeCore p (centralizerWithin X R)).map
        (centralizerWithin X R).subtype := by
    have hrestrict := inf_map_pPrimeCore_le_map_pPrimeCore
      p hcentN
    change centralizerWithin X R ⊓ O.map N.subtype ≤
      (pPrimeCore p (centralizerWithin X R)).map
        (centralizerWithin X R).subtype at hrestrict
    rw [inf_eq_right.mpr hmapCent] at hrestrict
    exact hrestrict
  have hcore := map_pPrimeCore_centralizerWithin_le_map_pPrimeCore
    (p := p) (X := X) (R := R) hRX hRp hXsol
  exact hmapCoreCent.trans hcore

private theorem nonPCoreFitting_basic_of_le
    {G : Type u} [Group G] [Finite G]
    (M A₀ : Subgroup G)
    (hA₀F : A₀ ≤ fittingWithin M) :
    let F := fittingWithin M
    let A := centralizerWithin F A₀
    centerWithin F ≤ A ∧ A ≤ F ∧
      primeSupport (Nat.card A) = primeSupport (Nat.card F) := by
  let F := fittingWithin M
  let A := centralizerWithin F A₀
  have hZA : centerWithin F ≤ A :=
    centerWithin_le_centralizerWithin hA₀F
  have hAF : A ≤ F := centralizerWithin_le_left F A₀
  have hsupportCenter :
      primeSupport (Nat.card (centerWithin F)) =
        primeSupport (Nat.card F) :=
    primeSupport_centerWithin_eq_of_isNilpotent F
  have hsupport :
      primeSupport (Nat.card A) = primeSupport (Nat.card F) := by
    apply Set.Subset.antisymm
    · intro q hq
      exact ⟨hq.1, hq.2.trans (Subgroup.card_dvd_of_le hAF)⟩
    · intro q hq
      have hqZ : q ∈ primeSupport (Nat.card (centerWithin F)) := by
        rw [hsupportCenter]
        exact hq
      exact ⟨hqZ.1, hqZ.2.trans (Subgroup.card_dvd_of_le hZA)⟩
  exact ⟨hZA, hAF, hsupport⟩

private theorem nonPCoreFitting_basic
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (M A₀ : Subgroup G)
    (hA₀ : IsPMaxElem p (fittingWithin M) A₀) :
    let F := fittingWithin M
    let A := centralizerWithin F A₀
    centerWithin F ≤ A ∧ A ≤ F ∧ A₀ ≤ A ∧
      primeSupport (Nat.card A) = primeSupport (Nat.card F) := by
  have hbase := nonPCoreFitting_basic_of_le M A₀ hA₀.le
  exact ⟨hbase.1, hbase.2.1,
    le_inf hA₀.le
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        hA₀.elementary.commutative),
    hbase.2.2⟩

/-- The centralizer in the Fitting subgroup has exactly the same prime
support as the Fitting subgroup. -/
theorem non_pcore_fitting_primeSupport_eq
    {G : Type u} [Group G] [Finite G]
    (M A₀ : Subgroup G)
    (hA₀F : A₀ ≤ fittingWithin M) :
    primeSupport
        (Nat.card (centralizerWithin (fittingWithin M) A₀)) =
      primeSupport (Nat.card (fittingWithin M)) := by
  exact (nonPCoreFitting_basic_of_le M A₀ hA₀F).2.2

/-- The defining prime belongs to the support of the constrained
centralizer. -/
theorem non_pcore_fitting_prime_mem
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (M A₀ : Subgroup G)
    (hA₀ : IsPMaxElem p (fittingWithin M) A₀)
    (hRank3 : ∃ E : Subgroup G,
      E ≤ A₀ ∧ IsElementaryAbelianOfRank p 3 E) :
    p ∈ primeSupport
      (Nat.card (centralizerWithin (fittingWithin M) A₀)) := by
  obtain ⟨E, hEA₀, hErank⟩ := hRank3
  have hEne : E ≠ ⊥ := hErank.ne_bot
  have hpE : p ∣ Nat.card E :=
    hErank.isPGroup.card_eq_or_dvd.resolve_left
      (fun hcard ↦ hEne (Subgroup.card_eq_one.mp hcard))
  have hA₀A : A₀ ≤ centralizerWithin (fittingWithin M) A₀ :=
    (nonPCoreFitting_basic M A₀ hA₀).2.2.1
  exact ⟨Fact.out, hpE.trans
    (Subgroup.card_dvd_of_le (hEA₀.trans hA₀A))⟩

private theorem nonPCoreFitting_normalizer_pCore
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (M A₀ : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hA₀F : A₀ ≤ fittingWithin M)
    (q : ℕ) [Fact q.Prime]
    (hq : q ∈ primeSupport
      (Nat.card (centralizerWithin (fittingWithin M) A₀))) :
    Subgroup.normalizer
        ((pCore q (centerWithin (fittingWithin M))).map
          (centerWithin (fittingWithin M)).subtype : Set G) = M := by
  let F := fittingWithin M
  let A := centralizerWithin F A₀
  let Z := centerWithin F
  let Q : Subgroup G := (pCore q Z).map Z.subtype
  have hbasic := nonPCoreFitting_basic_of_le M A₀ hA₀F
  change q ∈ primeSupport (Nat.card A) at hq
  have hZA : Z ≤ A := hbasic.1
  have hAF : A ≤ F := hbasic.2.1
  have hsupport :
      primeSupport (Nat.card A) = primeSupport (Nat.card F) :=
    hbasic.2.2
  have hqF : q ∈ primeSupport (Nat.card F) := by
    rw [← hsupport]
    exact hq
  have hsupportZ :
      primeSupport (Nat.card Z) = primeSupport (Nat.card F) :=
    primeSupport_centerWithin_eq_of_isNilpotent F
  have hqZ : q ∣ Nat.card Z := by
    have : q ∈ primeSupport (Nat.card Z) := by
      rw [hsupportZ]
      exact hqF
    exact this.2
  letI : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  letI : Group.IsNilpotent Z :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (hZA.trans hAF))
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    have hcoreBot : pCore q Z = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (pCore q Z) Z.subtype_injective).mp hQbot
    exact (pCore_ne_bot_iff_dvd_card_of_isNilpotent
      (G := Z) q).2 hqZ hcoreBot
  have hQZ : Q ≤ Z := by
    dsimp [Q]
    exact Subgroup.map_subtype_le _
  have hFM : F ≤ M := fittingWithin_le M
  have hQM : Q ≤ M := hQZ.trans (hZA.trans (hAF.trans hFM))
  have hMnormF : M ≤ Subgroup.normalizer (F : Set G) :=
    fittingWithin_le_normalizer M
  have hMnormZ : M ≤ Subgroup.normalizer (Z : Set G) := by
    rw [show Z = (Subgroup.center F).map F.subtype from
      (map_center_eq_centerWithin F).symm,
      Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      F M (Subgroup.center F) hMnormF
  have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      Z M (pCore q Z) hMnormZ
  have hQnormalM : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).2 hMnormQ
  change Subgroup.normalizer (Q : Set G) = M
  exact mmax_normal hM hQM hQnormalM hQne

/-- For every prime in the support of the constrained centralizer, the
ambient centralizer of its mapped prime core lies in the chosen maximal
subgroup. -/
theorem non_pcore_fitting_centralizer_pCore_le
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (M A₀ : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hA₀F : A₀ ≤ fittingWithin M)
    (q : ℕ) [Fact q.Prime]
    (hq : q ∈ primeSupport
      (Nat.card (centralizerWithin (fittingWithin M) A₀))) :
    Subgroup.centralizer
        ((pCore q
          (centralizerWithin (fittingWithin M) A₀)).map
            (centralizerWithin (fittingWithin M) A₀).subtype : Set G) ≤
      M := by
  let F := fittingWithin M
  let A := centralizerWithin F A₀
  let Z := centerWithin F
  let QZ : Subgroup G := (pCore q Z).map Z.subtype
  let QA : Subgroup G := (pCore q A).map A.subtype
  have hbasic := nonPCoreFitting_basic_of_le M A₀ hA₀F
  have hZA : Z ≤ A := hbasic.1
  have hAF : A ≤ F := hbasic.2.1
  have hFM : F ≤ M := fittingWithin_le M
  have hQZZ : QZ ≤ Z := by
    dsimp [QZ]
    exact Subgroup.map_subtype_le _
  have hQZA : QZ ≤ A := hQZZ.trans hZA
  have hnormQZ := nonPCoreFitting_normalizer_pCore
    M A₀ hM hA₀F q hq
  change Subgroup.normalizer (QZ : Set G) = M at hnormQZ
  have hAnormQZ : A ≤ Subgroup.normalizer (QZ : Set G) := by
    rw [hnormQZ]
    exact hAF.trans hFM
  have hQZnormalA : (QZ.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQZA).2 hAnormQZ
  have hQZp : IsPGroup q QZ := by
    dsimp [QZ]
    exact pCore_isPGroup.map Z.subtype
  have hQZsubp : IsPGroup q (QZ.subgroupOf A) :=
    hQZp.of_equiv (Subgroup.subgroupOfEquivOfLe hQZA).symm
  have hQZcoreA : QZ.subgroupOf A ≤ pCore q A :=
    le_pCore hQZsubp hQZnormalA
  have hQZQA : QZ ≤ QA := by
    dsimp [QA]
    rw [← Subgroup.map_subgroupOf_eq_of_le hQZA]
    exact Subgroup.map_mono hQZcoreA
  change Subgroup.centralizer (QA : Set G) ≤ M
  exact (Subgroup.centralizer_le hQZQA).trans
    ((Subgroup.centralizer_le_normalizer (QZ : Set G)).trans_eq hnormQZ)

private theorem map_pCore_le_map_pCore_of_le_of_isNilpotent
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hHK : H ≤ K) [Group.IsNilpotent K] :
    (pCore p H).map H.subtype ≤ (pCore p K).map K.subtype := by
  let P : Subgroup G := (pCore p H).map H.subtype
  have hPK : P ≤ K := (Subgroup.map_subtype_le _).trans hHK
  have hPsubp : IsPGroup p (P.subgroupOf K) := by
    exact (pCore_isPGroup.map H.subtype).comap_subtype
  have hPcore : P.subgroupOf K ≤ pCore p K :=
    hPsubp.le_pCore_of_isNilpotent
  change P ≤ (pCore p K).map K.subtype
  rw [← Subgroup.map_subgroupOf_eq_of_le hPK]
  exact Subgroup.map_mono hPcore

/-- A different prime core of the constrained centralizer lies in the
`q'`-core of every proper overgroup. -/
theorem map_pCore_centralizerWithin_fittingWithin_le_map_pPrimeCore
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (M A₀ : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hA₀F : A₀ ≤ fittingWithin M)
    (q r : ℕ) [Fact q.Prime] [Fact r.Prime]
    (hq : q ∈ primeSupport
      (Nat.card (centralizerWithin (fittingWithin M) A₀)))
    (hqr : q ≠ r)
    {X : Subgroup G}
    (hAX : centralizerWithin (fittingWithin M) A₀ ≤ X)
    (hXproper : X < ⊤) :
    (pCore r (centralizerWithin (fittingWithin M) A₀)).map
        (centralizerWithin (fittingWithin M) A₀).subtype ≤
      (pPrimeCore q X).map X.subtype := by
  let F := fittingWithin M
  let A := centralizerWithin F A₀
  let Z := centerWithin F
  let R : Subgroup G := (pCore q Z).map Z.subtype
  let N : Subgroup G := X ⊓ Subgroup.normalizer (R : Set G)
  let P : Subgroup G := (pCore r F).map F.subtype
  let Ar : Subgroup G := (pCore r A).map A.subtype
  let L : Subgroup G := N ⊓ P
  have hbasic := nonPCoreFitting_basic_of_le M A₀ hA₀F
  have hZA : Z ≤ A := hbasic.1
  have hAF : A ≤ F := hbasic.2.1
  have hFM : F ≤ M := fittingWithin_le M
  have hRZ : R ≤ Z := by
    dsimp [R]
    exact Subgroup.map_subtype_le _
  have hRA : R ≤ A := hRZ.trans hZA
  have hRX : R ≤ X := hRA.trans hAX
  have hRp : IsPGroup q R := by
    dsimp [R]
    exact pCore_isPGroup.map Z.subtype
  have hnormR := nonPCoreFitting_normalizer_pCore
    M A₀ hM hA₀F q hq
  change Subgroup.normalizer (R : Set G) = M at hnormR
  have hAM : A ≤ M := hAF.trans hFM
  have hAN : A ≤ N := by
    exact le_inf hAX (by simpa [hnormR] using hAM)
  have hNM : N ≤ M := by
    exact inf_le_right.trans_eq hnormR
  letI : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  have hArP : Ar ≤ P := by
    exact map_pCore_le_map_pCore_of_le_of_isNilpotent hAF
  have hArA : Ar ≤ A := by
    dsimp [Ar]
    exact Subgroup.map_subtype_le _
  have hArN : Ar ≤ N := hArA.trans hAN
  have hArL : Ar ≤ L := le_inf hArN hArP
  have hPM : P ≤ M := by
    dsimp [P]
    exact (Subgroup.map_subtype_le _).trans hFM
  have hMnormF : M ≤ Subgroup.normalizer (F : Set G) :=
    fittingWithin_le_normalizer M
  have hMnormP : M ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      F M (pCore r F) hMnormF
  have hPnormalM : (P.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).2 hMnormP
  have hLnormalN : (L.subgroupOf N).Normal := by
    letI : (P.subgroupOf M).Normal := hPnormalM
    have hn := Subgroup.inf_subgroupOf_inf_normal_of_right N P M
    change ((N ⊓ P).subgroupOf N).Normal
    rw [inf_eq_left.mpr hNM] at hn
    exact hn
  have hPr : IsPGroup r P := by
    dsimp [P]
    exact pCore_isPGroup.map F.subtype
  have hLr : IsPGroup r L := hPr.to_le inf_le_right
  have hLprime : IsPPrimeSubgroup q L := by
    rw [IsPPrimeSubgroup]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hLr
    rw [hn]
    exact ((Nat.coprime_primes Fact.out Fact.out).2 hqr).pow_right n
  have hLsubprime : IsPPrimeSubgroup q (L.subgroupOf N) := by
    rw [IsPPrimeSubgroup, natCard_subgroupOf_eq
      (show L ≤ N from inf_le_left)]
    exact hLprime
  have hLcore : L.subgroupOf N ≤ pPrimeCore q N :=
    le_pPrimeCore hLsubprime hLnormalN
  have hArCoreN : Ar ≤ (pPrimeCore q N).map N.subtype := by
    apply hArL.trans
    rw [← Subgroup.map_subgroupOf_eq_of_le
      (show L ≤ N from inf_le_left)]
    exact Subgroup.map_mono hLcore
  have hbridge := map_pPrimeCore_inf_normalizer_le_map_pPrimeCore
    q hRX hRp (mFT_sol hXproper)
  change (pPrimeCore q N).map N.subtype ≤
    (pPrimeCore q X).map X.subtype at hbridge
  exact hArCoreN.trans hbridge

/-- The ambient centralizer of the constrained subgroup has no prime
divisors outside the subgroup's own prime support. -/
theorem non_pcore_fitting_centralizer_isPiNumber
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (M A₀ : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hA₀F : A₀ ≤ fittingWithin M)
    (hA₀A : A₀ ≤
      centralizerWithin (fittingWithin M) A₀)
    (s : ℕ) [Fact s.Prime]
    (hs : s ∈ primeSupport
      (Nat.card (centralizerWithin (fittingWithin M) A₀))) :
    IsPiNumber
      (primeSupport
        (Nat.card (centralizerWithin (fittingWithin M) A₀)))
      (Nat.card
        (Subgroup.centralizer
          (centralizerWithin (fittingWithin M) A₀ : Set G))) := by
  let F := fittingWithin M
  let A := centralizerWithin F A₀
  let CA : Subgroup G := Subgroup.centralizer (A : Set G)
  have hbasic := nonPCoreFitting_basic_of_le M A₀ hA₀F
  have hAF : A ≤ F := hbasic.2.1
  have hsupport :
      primeSupport (Nat.card A) = primeSupport (Nat.card F) :=
    hbasic.2.2
  have hcoreCent := non_pcore_fitting_centralizer_pCore_le
    M A₀ hM hA₀F s hs
  have hpsA :
      (pCore s A).map A.subtype ≤ A :=
    Subgroup.map_subtype_le _
  have hCAM : CA ≤ M := by
    apply (Subgroup.centralizer_le hpsA).trans
    simpa [A] using hcoreCent
  intro q hqPrime hqCA
  by_contra hqA
  letI : Fact q.Prime := ⟨hqPrime⟩
  obtain ⟨x, hxOrder⟩ := exists_prime_orderOf_dvd_card'
    (G := CA) q hqCA
  let xG : G := x
  have hxOrderG : orderOf xG = q :=
    (Subgroup.orderOf_coe x).trans hxOrder
  have hxCA : xG ∈ CA := x.property
  have hxM : xG ∈ M := hCAM hxCA
  let U : Subgroup G := Subgroup.zpowers xG
  let C : Subgroup G := centralizerWithin F U
  have hAC : A ≤ C := by
    apply le_inf hAF
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
    exact hxCA
  have hself : centralizerWithin F C ≤ C := by
    exact (centralizerWithin_antitone_right hAC).trans
      ((centralizerWithin_antitone_right hA₀A).trans hAC)
  have hUnormF : U ≤ Subgroup.normalizer (F : Set G) := by
    exact (Subgroup.zpowers_le.mpr hxM).trans
      (fittingWithin_le_normalizer M)
  have hqNotF : ¬ q ∣ Nat.card F := by
    intro hqF
    apply hqA
    rw [hsupport]
    exact ⟨hqPrime, hqF⟩
  have hcop : Nat.Coprime (Nat.card F) (Nat.card U) := by
    have hqcopF : Nat.Coprime q (Nat.card F) :=
      hqPrime.coprime_iff_not_dvd.mpr hqNotF
    rw [show Nat.card U = q by
      dsimp [U]
      rw [Nat.card_zpowers, hxOrderG]]
    exact hqcopF.symm
  letI : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  have hUcentF : U ≤ Subgroup.centralizer (F : Set G) :=
    coprime_nilpotent_centralizes_of_selfCentralizing_fixedPoints
      hUnormF hcop hself
  have hxCentF : xG ∈ Subgroup.centralizer (F : Set G) :=
    hUcentF (Subgroup.mem_zpowers xG)
  letI : IsSolvable M := mmax_sol hM
  let xM : M := ⟨xG, hxM⟩
  have hxCentFitM :
      xM ∈ Subgroup.centralizer (fittingCore M : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hyF : (y : G) ∈ F := by
      dsimp [F, fittingWithin]
      exact ⟨y, hy, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hxCentF (y : G) hyF
  have hxFitM : xM ∈ fittingCore M :=
    centralizer_fittingCore_le hxCentFitM
  have hxF : xG ∈ F := by
    dsimp [F, fittingWithin]
    exact ⟨xM, hxFitM, rfl⟩
  apply hqA
  rw [hsupport]
  exact ⟨hqPrime, by
    simpa [hxOrderG] using F.orderOf_dvd_natCard hxF⟩

private theorem exists_prime_ne_dvd_card_of_not_isPGroup
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : ¬ IsPGroup p G) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ Nat.card G := by
  by_contra hnone
  apply hG
  rw [IsPGroup.iff_card]
  have hcard : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hall : ∀ q ∈ (Nat.card G).primeFactorsList, q = p := by
    intro q hq
    obtain ⟨hqprime, hqdvd⟩ := (Nat.mem_primeFactorsList hcard).mp hq
    by_contra hqp
    exact hnone ⟨q, hqprime, hqp, hqdvd⟩
  use (Nat.card G).primeFactorsList.length
  rw [← List.prod_replicate, ← List.eq_replicate_of_mem hall,
    Nat.prod_primeFactorsList hcard]

/-- Failure of the Fitting subgroup to be a `p`-group supplies, against any
chosen prime, a different prime in the constrained centralizer's support. -/
theorem non_pcore_fitting_exists_prime_ne
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (M A₀ : Subgroup G)
    (hA₀F : A₀ ≤ fittingWithin M)
    (hFp : ¬ IsPGroup p (fittingWithin M))
    (hp : p ∈ primeSupport
      (Nat.card (centralizerWithin (fittingWithin M) A₀)))
    (q : ℕ) :
    ∃ r : ℕ,
      r ∈ primeSupport
        (Nat.card (centralizerWithin (fittingWithin M) A₀)) ∧
      r ≠ q := by
  by_cases hqp : q = p
  · subst q
    obtain ⟨r, hrPrime, hrp, hrF⟩ :=
      exists_prime_ne_dvd_card_of_not_isPGroup hFp
    refine ⟨r, ?_, hrp⟩
    rw [non_pcore_fitting_primeSupport_eq M A₀ hA₀F]
    exact ⟨hrPrime, hrF⟩
  · exact ⟨p, hp, fun hpq ↦ hqp hpq.symm⟩

/-- The constrained-centralizer step `cstrA` in Bender--Glauberman
Theorem 8.1(a). -/
theorem non_pcore_fitting_normedConstrained
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M A₀ : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFp : ¬ IsPGroup p (fittingWithin M))
    (hA₀ : IsPMaxElem p (fittingWithin M) A₀)
    (hRank3 : ∃ E : Subgroup G,
      E ≤ A₀ ∧ IsElementaryAbelianOfRank p 3 E) :
    NormedConstrained
      (centralizerWithin (fittingWithin M) A₀) := by
  let F := fittingWithin M
  let A := centralizerWithin F A₀
  let pi := primeSupport (Nat.card A)
  have hA₀F : A₀ ≤ F := hA₀.le
  have hbasic := nonPCoreFitting_basic M A₀ hA₀
  have hAF : A ≤ F := hbasic.2.1
  have hA₀A : A₀ ≤ A := hbasic.2.2.1
  have hsupport : pi = primeSupport (Nat.card F) :=
    hbasic.2.2.2
  have hp : p ∈ pi :=
    non_pcore_fitting_prime_mem p M A₀ hA₀ hRank3
  have hCApi :
      IsPiNumber pi
        (Nat.card (Subgroup.centralizer (A : Set G))) :=
    non_pcore_fitting_centralizer_isPiNumber
      M A₀ hM hA₀F hA₀A p hp
  have hAne : A ≠ ⊥ := by
    intro hAbot
    have hpdiv : p ∣ Nat.card A := hp.2
    rw [hAbot] at hpdiv
    exact (Fact.out : p.Prime).not_dvd_one (by simpa using hpdiv)
  have hAproper : A < ⊤ :=
    lt_of_le_of_lt (hAF.trans (fittingWithin_le M)) (mmax_proper hM)
  refine
    { nontrivial := hAne
      proper := hAproper
      constrained := ?_ }
  intro X Y hAX hXproper hY
  rcases hY with ⟨hYX, hYpi, hAnormY⟩
  apply le_primeSetCore_compl_of_le_map_pPrimeCore hYX
  intro q hq
  letI : Fact q.Prime := ⟨hq.1⟩
  obtain ⟨r, hr, hrq⟩ :=
    non_pcore_fitting_exists_prime_ne
      p M A₀ hA₀F hFp hp q
  letI : Fact r.Prime := ⟨hr.1⟩
  let Ar : Subgroup G := (pCore r A).map A.subtype
  let K : Subgroup G := (pPrimeCore q X).map X.subtype
  let C : Subgroup G := centralizerWithin Y Ar
  have hArA : Ar ≤ A := by
    dsimp [Ar]
    exact Subgroup.map_subtype_le _
  have hArK : Ar ≤ K := by
    exact map_pCore_centralizerWithin_fittingWithin_le_map_pPrimeCore
      M A₀ hM hA₀F q r hq hrq.symm hAX hXproper
  have hcoreCent := non_pcore_fitting_centralizer_pCore_le
    M A₀ hM hA₀F r hr
  have hCM : C ≤ M := by
    apply inf_le_right.trans
    simpa [Ar, A] using hcoreCent
  have hCY : C ≤ Y := centralizerWithin_le_left Y Ar
  have hCnormF : C ≤ Subgroup.normalizer (F : Set G) :=
    hCM.trans (fittingWithin_le_normalizer M)
  have hcommF : ⁅C, A⁆ ≤ F := by
    exact (Subgroup.commutator_mono le_rfl hAF).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hCnormF)
  have hcommY : ⁅C, A⁆ ≤ Y := by
    exact (Subgroup.commutator_mono hCY le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hAnormY)
  have hcopYF : Nat.Coprime (Nat.card Y) (Nat.card F) := by
    apply Nat.coprime_of_dvd
    intro t htPrime htY htF
    have htCompl : t ∈ piᶜ := hYpi htPrime htY
    apply htCompl
    rw [hsupport]
    exact ⟨htPrime, htF⟩
  have hdisYF : Disjoint Y F :=
    Subgroup.disjoint_of_coprime_natCard hcopYF
  have hcommBot : ⁅C, A⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf hcommY hcommF).trans (disjoint_iff.mp hdisYF).le
  have hCCA : C ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
  have hcopYCA : Nat.Coprime (Nat.card Y)
      (Nat.card (Subgroup.centralizer (A : Set G))) := by
    apply Nat.coprime_of_dvd
    intro t htPrime htY htCA
    exact (hYpi htPrime htY) (hCApi htPrime htCA)
  have hdisYCA : Disjoint Y (Subgroup.centralizer (A : Set G)) :=
    Subgroup.disjoint_of_coprime_natCard hcopYCA
  have hCbot : C = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf hCY hCCA).trans (disjoint_iff.mp hdisYCA).le
  have hcopYAr : Nat.Coprime (Nat.card Y) (Nat.card Ar) := by
    apply Nat.coprime_of_dvd
    intro t htPrime htY htAr
    apply hYpi htPrime htY
    exact ⟨htPrime, htAr.trans (Subgroup.card_dvd_of_le hArA)⟩
  have hArNormY : Ar ≤ Subgroup.normalizer (Y : Set G) :=
    hArA.trans hAnormY
  letI : IsSolvable Y := mFT_sol (lt_of_le_of_lt hYX hXproper)
  have hdecomp : Y ≤ ⁅Ar, Y⁆ ⊔ centralizerWithin Y Ar :=
    le_commutator_sup_centralizerWithin_of_coprime hArNormY hcopYAr
  have hYcomm : Y ≤ ⁅Ar, Y⁆ := by
    simpa [C, hCbot] using hdecomp
  have hKX : K ≤ X := by
    dsimp [K]
    exact Subgroup.map_subtype_le _
  have hKnormalX : (K.subgroupOf X).Normal := by
    dsimp [K]
    change (((pPrimeCore q X).map X.subtype).comap X.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    infer_instance
  have hXnormK : X ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).1 hKnormalX
  have hcommK : ⁅K, Y⁆ ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hYX.trans hXnormK)
  exact hYcomm.trans
    ((Subgroup.commutator_mono hArK le_rfl).trans hcommK)

end Submission.OddOrder.BG.Section08
