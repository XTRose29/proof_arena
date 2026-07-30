import Submission.OddOrder.BG.Section08.NonPCoreFittingConstrained
import Submission.OddOrder.BG.Section08.PrimeSetCoreFitting
import Submission.OddOrder.MathlibSupport.CoprimeFittingCentralizer

/-!
# Bender--Glauberman Theorem 8.1(a): maximal overgroups

This file ports the final maximal-overgroup argument in Theorem 8.1(a),
assuming the preceding singleton result for maximal normalized subgroups.
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07

universe u

/-- A finite solvable group with trivial Fitting subgroup is trivial. -/
theorem eq_bot_of_fittingWithin_eq_bot_of_isSolvable
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hsol : IsSolvable H)
    (hfit : fittingWithin H = ⊥) :
    H = ⊥ := by
  letI : IsSolvable H := hsol
  have hcore : fittingCore H = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective
      (fittingCore H) H.subtype_injective).mp
    simpa [fittingWithin] using hfit
  apply le_bot_iff.mp
  intro x hx
  let xH : H := ⟨x, hx⟩
  have hxCent : xH ∈ Subgroup.centralizer (fittingCore H : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hcore] at hy
    have hyOne : y = 1 := Subgroup.mem_bot.mp hy
    subst y
    simp
  have hxCore : xH ∈ fittingCore H :=
    centralizer_fittingCore_le hxCent
  rw [hcore] at hxCore
  apply Subgroup.mem_bot.mpr
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxCore)

/-- A normal subgroup's mapped `p`-core lies in the mapped `p`-core of the
ambient subgroup. -/
theorem map_pCore_le_map_pCore_of_normal
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] {K H : Subgroup G}
    (hKH : K ≤ H) (hKnormal : (K.subgroupOf H).Normal) :
    (pCore p K).map K.subtype ≤
      (pCore p H).map H.subtype := by
  let P : Subgroup G := (pCore p K).map K.subtype
  have hPH : P ≤ H := (Subgroup.map_subtype_le _).trans hKH
  have hHnormK : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKnormal
  have hHnormP : H ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      K H (pCore p K) hHnormK
  have hPnormal : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr hHnormP
  have hPp : IsPGroup p (P.subgroupOf H) :=
    (pCore_isPGroup.map K.subtype).of_equiv
      (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hPcore : P.subgroupOf H ≤ pCore p H :=
    le_pCore hPp hPnormal
  change P ≤ (pCore p H).map H.subtype
  rw [← Subgroup.map_subgroupOf_eq_of_le hPH]
  exact Subgroup.map_mono hPcore

private theorem primeSetCore_compl_primeSupport_eq_bot
    {G : Type u} [Group G] [Finite G] (X : Subgroup G) :
    primeSetCore (primeSupport (Nat.card X))ᶜ X = ⊥ := by
  let K : Subgroup G := primeSetCore (primeSupport (Nat.card X))ᶜ X
  have hKpi : IsPiNumber (primeSupport (Nat.card X))ᶜ (Nat.card K) := by
    simpa [K] using
      (primeSetCore_isPiNumber (primeSupport (Nat.card X))ᶜ X)
  have hKX : K ≤ X := by
    simpa [K] using (primeSetCore_le (primeSupport (Nat.card X))ᶜ X)
  apply Subgroup.card_eq_one.mp
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro q hq hqK
  exact (hKpi hq hqK) ⟨hq, hqK.trans (Subgroup.card_dvd_of_le hKX)⟩

private theorem map_pCore_le_centralizer_map_pPrimeCore
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    (pCore p H).map H.subtype ≤
      Subgroup.centralizer ((pPrimeCore p H).map H.subtype : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases hx with ⟨xH, hxH, rfl⟩
  rcases hy with ⟨yH, hyH, rfl⟩
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp
      (pCore_le_centralizer_pPrimeCore p hxH) yH hyH)

private theorem isPiNumber_singleton_of_isPGroup
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) :
    IsPiNumber ({p} : Set ℕ) (Nat.card P) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn]
  intro q hq hqdiv
  have hqp : q = p :=
    Nat.prime_eq_prime_of_dvd_pow hq Fact.out hqdiv
  simp [hqp]

/-- Every maximal overgroup of the constrained centralizer is the original
maximal subgroup, assuming the singleton maximal-normalized-family step. -/
theorem non_pcore_fitting_maximal_overgroup
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M A₀ H : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFp : ¬ IsPGroup p (fittingWithin M))
    (hA₀ : IsPMaxElem p (fittingWithin M) A₀)
    (hRank3 : ∃ E : Subgroup G,
      E ≤ A₀ ∧ IsElementaryAbelianOfRank p 3 E)
    (hmaxNorm : ∀ q,
      q ∉ primeSupport
          (Nat.card (centralizerWithin (fittingWithin M) A₀)) →
      max_normed_pgroups
          (centralizerWithin (fittingWithin M) A₀ : Set G)
          ({q} : Set ℕ) = {⊥})
    (hH : H ∈ minSimple_max_groups (G := G))
    (hAH : centralizerWithin (fittingWithin M) A₀ ≤ H) :
    H = M := by
  classical
  let F : Subgroup G := fittingWithin M
  let A : Subgroup G := centralizerWithin F A₀
  let D : Subgroup G := fittingWithin H
  let pi : Set ℕ := primeSupport (Nat.card A)
  let sigma : Set ℕ := primeSupport (Nat.card D)
  have hA₀F : A₀ ≤ F := hA₀.le
  have hAF : A ≤ F := centralizerWithin_le_left F A₀
  have hFM : F ≤ M := fittingWithin_le M
  have hDH : D ≤ H := fittingWithin_le H
  have hHproper : H < ⊤ := mmax_proper hH
  have hMproper : M < ⊤ := mmax_proper hM
  have hHsol : IsSolvable H := mmax_sol hH
  have hMsol : IsSolvable M := mmax_sol hM
  have hp : p ∈ pi := by
    simpa [pi, A, F] using
      (non_pcore_fitting_prime_mem p M A₀ hA₀ hRank3)
  have hpiAlt (q : ℕ) : ∃ r : ℕ, r ∈ pi ∧ r ≠ q := by
    simpa [pi, A, F] using
      (non_pcore_fitting_exists_prime_ne
        p M A₀ hA₀F hFp hp q)
  have hsigmaPi : sigma ⊆ pi := by
    intro q hqSigma
    by_contra hqPi
    letI : Fact q.Prime := ⟨hqSigma.1⟩
    let Dq : Subgroup G := (pCore q D).map D.subtype
    have hcoreNe : pCore q D ≠ ⊥ := by
      exact (pCore_ne_bot_iff_dvd_card_of_isNilpotent
        (G := D) q).2 hqSigma.2
    have hDqNe : Dq ≠ ⊥ := by
      intro hbot
      apply hcoreNe
      exact (Subgroup.map_eq_bot_iff_of_injective
        (pCore q D) D.subtype_injective).mp hbot
    have hHnormD : H ≤ Subgroup.normalizer (D : Set G) := by
      simpa [D] using (fittingWithin_le_normalizer H)
    have hHnormDq : H ≤ Subgroup.normalizer (Dq : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      exact characteristic_map_subtype_invariant_under_normalizer
        D H (pCore q D) hHnormD
    have hDqPi : IsPiNumber ({q} : Set ℕ) (Nat.card Dq) :=
      isPiNumber_singleton_of_isPGroup
        (by simpa [Dq] using (pCore_isPGroup.map D.subtype))
    obtain ⟨Q, hQmax, hDqQ⟩ :=
      max_normed_exists (A : Set G) ({q} : Set ℕ) Dq
        hDqPi (hAH.trans hHnormDq)
    have hfamily :
        max_normed_pgroups (A : Set G) ({q} : Set ℕ) = {⊥} := by
      simpa [A, F, pi] using hmaxNorm q hqPi
    have hQbot : Q = ⊥ := by
      rw [hfamily] at hQmax
      exact Set.mem_singleton_iff.mp hQmax
    exact hDqNe (le_bot_iff.mp (hDqQ.trans_eq hQbot))
  have hsupport : sigma = pi := by
    apply Set.Subset.antisymm hsigmaPi
    intro q hqPi
    by_contra hqSigma
    letI : Fact q.Prime := ⟨hqPi.1⟩
    let Aq : Subgroup G := (pCore q A).map A.subtype
    have hAqA : Aq ≤ A := by
      dsimp [Aq]
      exact Subgroup.map_subtype_le _
    have hAqH : Aq ≤ H := hAqA.trans hAH
    have hAqCore :
        Aq ≤ primeSetCore sigmaᶜ H := by
      apply le_primeSetCore_compl_of_le_map_pPrimeCore hAqH
      intro r hrSigma
      letI : Fact r.Prime := ⟨hrSigma.1⟩
      have hrPi : r ∈ pi := hsigmaPi hrSigma
      have hrq : r ≠ q := by
        intro hrq
        apply hqSigma
        simpa [hrq] using hrSigma
      simpa [Aq, A, F] using
        (map_pCore_centralizerWithin_fittingWithin_le_map_pPrimeCore
          M A₀ hM hA₀F r q hrPi hrq hAH hHproper)
    have hSigmaCoreH : primeSetCore sigmaᶜ H = ⊥ := by
      let K : Subgroup G := primeSetCore sigmaᶜ H
      have hKH : K ≤ H := by
        simpa [K] using (primeSetCore_le sigmaᶜ H)
      have hKproper : K < ⊤ := lt_of_le_of_lt hKH hHproper
      apply eq_bot_of_fittingWithin_eq_bot_of_isSolvable
        K (mFT_sol hKproper)
      calc
        fittingWithin K = primeSetCore sigmaᶜ D := by
          simpa [K, D] using
            (fittingWithin_primeSetCore_eq_primeSetCore_fittingWithin
              sigmaᶜ H)
        _ = ⊥ := by
          simpa [sigma] using
            (primeSetCore_compl_primeSupport_eq_bot D)
    have hAqBot : Aq = ⊥ := by
      apply le_bot_iff.mp
      exact hAqCore.trans_eq hSigmaCoreH
    letI : Group.IsNilpotent F := by
      dsimp [F]
      infer_instance
    letI : Group.IsNilpotent A :=
      Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hAF)
    have hcoreNe : pCore q A ≠ ⊥ :=
      (pCore_ne_bot_iff_dvd_card_of_isNilpotent
        (G := A) q).2 hqPi.2
    apply hcoreNe
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pCore q A) A.subtype_injective).mp hAqBot
  have hcross (q r : ℕ) [Fact q.Prime] [Fact r.Prime]
      (hqr : q ≠ r) :
      (pCore q D).map D.subtype ≤
        Subgroup.centralizer ((pCore r A).map A.subtype : Set G) := by
    let Dq : Subgroup G := (pCore q D).map D.subtype
    by_cases hDq : Dq = ⊥
    · simp [Dq, hDq]
    · have hcoreNe : pCore q D ≠ ⊥ := by
        intro hbot
        apply hDq
        simp [Dq, hbot]
      have hqSigma : q ∈ sigma := by
        refine ⟨Fact.out, ?_⟩
        exact (pCore_ne_bot_iff_dvd_card_of_isNilpotent
          (G := D) q).1 hcoreNe
      have hqPi : q ∈ pi := hsigmaPi hqSigma
      have hArPrime :
          (pCore r A).map A.subtype ≤
            (pPrimeCore q H).map H.subtype := by
        simpa [A, F] using
          (map_pCore_centralizerWithin_fittingWithin_le_map_pPrimeCore
            M A₀ hM hA₀F q r hqPi hqr hAH hHproper)
      have hcent := map_pCore_le_centralizer_map_pPrimeCore q H
      rw [← map_pCore_fittingWithin_eq_map_pCore H q] at hcent
      simpa [Dq, D] using
        hcent.trans (Subgroup.centralizer_le hArPrime)
  have hDM : D ≤ M := by
    change (fittingCore H).map H.subtype ≤ M
    rw [fittingCore, Subgroup.map_iSup]
    apply iSup_le
    intro q
    letI : Fact (q : ℕ).Prime := ⟨q.property⟩
    obtain ⟨r, hrPi, hrq⟩ := hpiAlt (q : ℕ)
    letI : Fact r.Prime := ⟨hrPi.1⟩
    have hqCent :
        (pCore (q : ℕ) D).map D.subtype ≤
          Subgroup.centralizer ((pCore r A).map A.subtype : Set G) :=
      hcross (q : ℕ) r (fun hqr ↦ hrq hqr.symm)
    have hcentM := non_pcore_fitting_centralizer_pCore_le
      M A₀ hM hA₀F r hrPi
    rw [map_pCore_fittingWithin_eq_map_pCore H (q : ℕ)] at hqCent
    exact hqCent.trans (by simpa [A, F] using hcentM)
  let Ap : Subgroup G := (pCore p A).map A.subtype
  let Hp : Subgroup G := (pPrimeCore p H).map H.subtype
  let Mp : Subgroup G := (pPrimeCore p M).map M.subtype
  have hApA : Ap ≤ A := by
    dsimp [Ap]
    exact Subgroup.map_subtype_le _
  have hApH : Ap ≤ H := hApA.trans hAH
  have hHpH : Hp ≤ H := by
    dsimp [Hp]
    exact Subgroup.map_subtype_le _
  have hMpM : Mp ≤ M := by
    dsimp [Mp]
    exact Subgroup.map_subtype_le _
  have hHpNormal : (Hp.subgroupOf H).Normal := by
    dsimp [Hp]
    change (((pPrimeCore p H).map H.subtype).comap H.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  have hMpNormal : (Mp.subgroupOf M).Normal := by
    dsimp [Mp]
    change (((pPrimeCore p M).map M.subtype).comap M.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have hApCentFitHp :
      Ap ≤ Subgroup.centralizer (fittingWithin Hp : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    change (fittingCore Hp).map Hp.subtype ≤
      Subgroup.centralizer (Ap : Set G)
    rw [fittingCore, Subgroup.map_iSup]
    apply iSup_le
    intro q
    letI : Fact (q : ℕ).Prime := ⟨q.property⟩
    by_cases hqp : (q : ℕ) = p
    · rw [hqp]
      have hHpCard : Nat.card Hp = Nat.card (pPrimeCore p H) := by
        dsimp [Hp]
        exact Subgroup.card_map_of_injective H.subtype_injective
      have hpcop : Nat.Coprime p (Nat.card Hp) := by
        rw [hHpCard]
        exact pPrimeCore_coprime_card
      have hbot : pCore p Hp = ⊥ :=
        pCore_eq_bot_of_not_dvd_card
          ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hpcop)
      simp [hbot]
    · have hcomponent :
          (pCore (q : ℕ) Hp).map Hp.subtype ≤
            (pCore (q : ℕ) H).map H.subtype :=
        map_pCore_le_map_pCore_of_normal
          (q : ℕ) hHpH hHpNormal
      have hDqCent :
          (pCore (q : ℕ) D).map D.subtype ≤
            Subgroup.centralizer (Ap : Set G) := by
        simpa [Ap] using hcross (q : ℕ) p hqp
      rw [map_pCore_fittingWithin_eq_map_pCore H (q : ℕ)] at hDqCent
      exact hcomponent.trans hDqCent
  have hApNormHp : Ap ≤ Subgroup.normalizer (Hp : Set G) := by
    exact hApH.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHpH).mp hHpNormal)
  have hHpApCop : Nat.Coprime (Nat.card Hp) (Nat.card Ap) := by
    have hApp : IsPGroup p Ap := by
      simpa [Ap] using
        ((pCore_isPGroup (G := A) (p := p)).map A.subtype)
    obtain ⟨n, hn⟩ :=
      IsPGroup.iff_card.mp hApp
    have hHpCard : Nat.card Hp = Nat.card (pPrimeCore p H) := by
      dsimp [Hp]
      exact Subgroup.card_map_of_injective H.subtype_injective
    rw [hn, hHpCard]
    exact (pPrimeCore_coprime_card (G := H) (p := p)).symm.pow_right n
  have hApCentHp : Ap ≤ Subgroup.centralizer (Hp : Set G) := by
    have hApWithin : Ap ≤ centralizerWithin Ap (fittingWithin Hp) :=
      le_inf le_rfl hApCentFitHp
    exact hApWithin.trans
      (coprime_cent_fitting hApNormHp hHpApCop
        (mFT_sol (lt_of_le_of_lt hHpH hHproper)))
  have hHpM : Hp ≤ M := by
    have hCentApM := non_pcore_fitting_centralizer_pCore_le
      M A₀ hM hA₀F p hp
    exact (Subgroup.le_centralizer_iff.mp hApCentHp).trans
      (by simpa [Ap, A, F] using hCentApM)
  let Dp : Subgroup G := (pCore p D).map D.subtype
  have hpSigma : p ∈ sigma := by
    rw [hsupport]
    exact hp
  have hDpNe : Dp ≠ ⊥ := by
    have hcoreNe : pCore p D ≠ ⊥ :=
      (pCore_ne_bot_iff_dvd_card_of_isNilpotent
        (G := D) p).2 hpSigma.2
    intro hbot
    apply hcoreNe
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pCore p D) D.subtype_injective).mp hbot
  have hDpH : Dp ≤ H := by
    exact (Subgroup.map_subtype_le _).trans hDH
  have hDpM : Dp ≤ M :=
    (Subgroup.map_subtype_le _).trans hDM
  have hDpEq :
      Dp = (pCore p H).map H.subtype := by
    simpa [Dp, D] using
      (map_pCore_fittingWithin_eq_map_pCore H p)
  have hDpNormal : (Dp.subgroupOf H).Normal := by
    rw [hDpEq]
    change (((pCore p H).map H.subtype).comap H.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  have hDpP : IsPGroup p Dp := by
    simpa [Dp] using ((pCore_isPGroup (G := D) (p := p)).map D.subtype)
  have hNormDp : Subgroup.normalizer (Dp : Set G) = H :=
    mmax_normal hH hDpH hDpNormal hDpNe
  let N : Subgroup G := M ⊓ Subgroup.normalizer (Dp : Set G)
  have hNH : N ≤ H := by
    exact inf_le_right.trans_eq hNormDp
  have hHpN : Hp ≤ N := by
    exact le_inf hHpM (by simpa [hNormDp] using hHpH)
  have hHpCoreN : Hp ≤ (pPrimeCore p N).map N.subtype := by
    have hrestrict := inf_map_pPrimeCore_le_map_pPrimeCore p hNH
    change N ⊓ Hp ≤ (pPrimeCore p N).map N.subtype at hrestrict
    rw [inf_eq_right.mpr hHpN] at hrestrict
    exact hrestrict
  have hCoreNM : (pPrimeCore p N).map N.subtype ≤ Mp := by
    have hbridge := map_pPrimeCore_inf_normalizer_le_map_pPrimeCore
      p hDpM hDpP hMsol
    simpa [N, Mp] using hbridge
  have hHpMp : Hp ≤ Mp := hHpCoreN.trans hCoreNM
  letI : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  have hMqAq (q : ℕ) [Fact q.Prime] (hqp : q ≠ p) :
      (pCore q M).map M.subtype ≤
        (pCore q A).map A.subtype := by
    let Fq : Subgroup G := (pCore q F).map F.subtype
    let Fp : Subgroup G := (pCore p F).map F.subtype
    have hFqF : Fq ≤ F := by
      dsimp [Fq]
      exact Subgroup.map_subtype_le _
    have hA₀Fp : A₀ ≤ Fp := by
      have hA₀subp : IsPGroup p (A₀.subgroupOf F) :=
        hA₀.elementary.isPGroup.of_equiv
          (Subgroup.subgroupOfEquivOfLe hA₀F).symm
      have hA₀core : A₀.subgroupOf F ≤ pCore p F :=
        hA₀subp.le_pCore_of_isNilpotent
      dsimp [Fp]
      rw [← Subgroup.map_subgroupOf_eq_of_le hA₀F]
      exact Subgroup.map_mono hA₀core
    have hFpPrime : Fp ≤ (pPrimeCore q F).map F.subtype := by
      dsimp [Fp]
      exact Subgroup.map_mono
        (pCore_le_pPrimeCore_of_ne (G := F) (p := q) (q := p) hqp)
    have hFqCentA₀ : Fq ≤ Subgroup.centralizer (A₀ : Set G) := by
      have hcent := map_pCore_le_centralizer_map_pPrimeCore q F
      exact hcent.trans
        ((Subgroup.centralizer_le hFpPrime).trans
          (Subgroup.centralizer_le hA₀Fp))
    have hFqA : Fq ≤ A := le_inf hFqF hFqCentA₀
    have hAnormF : A ≤ Subgroup.normalizer (F : Set G) :=
      hAF.trans Subgroup.le_normalizer
    have hAnormFq : A ≤ Subgroup.normalizer (Fq : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      exact characteristic_map_subtype_invariant_under_normalizer
        F A (pCore q F) hAnormF
    have hFqNormal : (Fq.subgroupOf A).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFqA).mpr hAnormFq
    have hFqP : IsPGroup q (Fq.subgroupOf A) :=
      (pCore_isPGroup.map F.subtype).of_equiv
        (Subgroup.subgroupOfEquivOfLe hFqA).symm
    have hFqCore : Fq.subgroupOf A ≤ pCore q A :=
      le_pCore hFqP hFqNormal
    have hFqAq : Fq ≤ (pCore q A).map A.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hFqA]
      exact Subgroup.map_mono hFqCore
    rw [← map_pCore_fittingWithin_eq_map_pCore M q]
    simpa [Fq, F] using hFqAq
  have hDpCentFitMp :
      Dp ≤ Subgroup.centralizer (fittingWithin Mp : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    change (fittingCore Mp).map Mp.subtype ≤
      Subgroup.centralizer (Dp : Set G)
    rw [fittingCore, Subgroup.map_iSup]
    apply iSup_le
    intro q
    letI : Fact (q : ℕ).Prime := ⟨q.property⟩
    by_cases hqp : (q : ℕ) = p
    · rw [hqp]
      have hMpCard : Nat.card Mp = Nat.card (pPrimeCore p M) := by
        dsimp [Mp]
        exact Subgroup.card_map_of_injective M.subtype_injective
      have hpcop : Nat.Coprime p (Nat.card Mp) := by
        rw [hMpCard]
        exact pPrimeCore_coprime_card
      have hbot : pCore p Mp = ⊥ :=
        pCore_eq_bot_of_not_dvd_card
          ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hpcop)
      simp [hbot]
    · have hcomponent :
          (pCore (q : ℕ) Mp).map Mp.subtype ≤
            (pCore (q : ℕ) M).map M.subtype :=
        map_pCore_le_map_pCore_of_normal
          (q : ℕ) hMpM hMpNormal
      have hMqAq' := hMqAq (q : ℕ) hqp
      have hAqCentDp :
          (pCore (q : ℕ) A).map A.subtype ≤
            Subgroup.centralizer (Dp : Set G) := by
        apply Subgroup.le_centralizer_iff.mp
        simpa [Dp] using
          hcross p (q : ℕ) (fun hpq ↦ hqp hpq.symm)
      exact hcomponent.trans (hMqAq'.trans hAqCentDp)
  have hDpNormMp : Dp ≤ Subgroup.normalizer (Mp : Set G) := by
    exact hDpM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hMpM).mp hMpNormal)
  have hMpDpCop : Nat.Coprime (Nat.card Mp) (Nat.card Dp) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hDpP
    have hMpCard : Nat.card Mp = Nat.card (pPrimeCore p M) := by
      dsimp [Mp]
      exact Subgroup.card_map_of_injective M.subtype_injective
    rw [hn, hMpCard]
    exact (pPrimeCore_coprime_card (G := M) (p := p)).symm.pow_right n
  have hDpCentMp : Dp ≤ Subgroup.centralizer (Mp : Set G) := by
    have hDpWithin : Dp ≤ centralizerWithin Dp (fittingWithin Mp) :=
      le_inf le_rfl hDpCentFitMp
    exact hDpWithin.trans
      (coprime_cent_fitting hDpNormMp hMpDpCop
        (mFT_sol (lt_of_le_of_lt hMpM hMproper)))
  have hMpH : Mp ≤ H := by
    exact (Subgroup.le_centralizer_iff.mp hDpCentMp).trans
      ((Subgroup.centralizer_le_normalizer (Dp : Set G)).trans_eq hNormDp)
  let Z : Subgroup G := centerWithin F
  let R : Subgroup G := (pCore p Z).map Z.subtype
  have hZA : Z ≤ A := by
    simpa [Z, A] using centerWithin_le_centralizerWithin hA₀F
  have hRZ : R ≤ Z := by
    dsimp [R]
    exact Subgroup.map_subtype_le _
  have hRH : R ≤ H := hRZ.trans (hZA.trans hAH)
  have hZF : Z ≤ F := hZA.trans hAF
  have hRM : R ≤ M := hRZ.trans (hZF.trans hFM)
  have hpF : p ∈ primeSupport (Nat.card F) := by
    have hsupportAF := non_pcore_fitting_primeSupport_eq M A₀ hA₀F
    simpa [pi, A, F] using (hsupportAF ▸ hp)
  have hpZ : p ∈ primeSupport (Nat.card Z) := by
    have hsupportZF := primeSupport_centerWithin_eq_of_isNilpotent F
    simpa [Z] using (hsupportZF.symm ▸ hpF)
  letI : Group.IsNilpotent Z :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hZF)
  have hRNe : R ≠ ⊥ := by
    have hcoreNe : pCore p Z ≠ ⊥ :=
      (pCore_ne_bot_iff_dvd_card_of_isNilpotent
        (G := Z) p).2 hpZ.2
    intro hbot
    apply hcoreNe
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pCore p Z) Z.subtype_injective).mp hbot
  have hMnormF : M ≤ Subgroup.normalizer (F : Set G) := by
    simpa [F] using fittingWithin_le_normalizer M
  have hMnormZ : M ≤ Subgroup.normalizer (Z : Set G) := by
    rw [show Z = (Subgroup.center F).map F.subtype from
      (map_center_eq_centerWithin F).symm,
      Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      F M (Subgroup.center F) hMnormF
  have hMnormR : M ≤ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      Z M (pCore p Z) hMnormZ
  have hRNormalM : (R.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRM).mpr hMnormR
  have hNormR : Subgroup.normalizer (R : Set G) = M :=
    mmax_normal hM hRM hRNormalM hRNe
  have hRP : IsPGroup p R := by
    simpa [R] using ((pCore_isPGroup (G := Z) (p := p)).map Z.subtype)
  let L : Subgroup G := H ⊓ Subgroup.normalizer (R : Set G)
  have hLM : L ≤ M := inf_le_right.trans_eq hNormR
  have hMpL : Mp ≤ L :=
    le_inf hMpH (by simpa [hNormR] using hMpM)
  have hMpCoreL : Mp ≤ (pPrimeCore p L).map L.subtype := by
    have hrestrict := inf_map_pPrimeCore_le_map_pPrimeCore p hLM
    change L ⊓ Mp ≤ (pPrimeCore p L).map L.subtype at hrestrict
    rw [inf_eq_right.mpr hMpL] at hrestrict
    exact hrestrict
  have hCoreLHp : (pPrimeCore p L).map L.subtype ≤ Hp := by
    have hbridge := map_pPrimeCore_inf_normalizer_le_map_pPrimeCore
      p hRH hRP hHsol
    simpa [L, Hp] using hbridge
  have hMpHp : Mp ≤ Hp := hMpCoreL.trans hCoreLHp
  have hEqPrime : Hp = Mp := le_antisymm hHpMp hMpHp
  obtain ⟨q, hqPi, hqp⟩ := hpiAlt p
  letI : Fact q.Prime := ⟨hqPi.1⟩
  let Dq : Subgroup G := (pCore q D).map D.subtype
  have hqSigma : q ∈ sigma := by
    rw [hsupport]
    exact hqPi
  have hDqNe : Dq ≠ ⊥ := by
    have hcoreNe : pCore q D ≠ ⊥ :=
      (pCore_ne_bot_iff_dvd_card_of_isNilpotent
        (G := D) q).2 hqSigma.2
    intro hbot
    apply hcoreNe
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pCore q D) D.subtype_injective).mp hbot
  have hDqHp : Dq ≤ Hp := by
    have hcore : pCore q H ≤ pPrimeCore p H :=
      pCore_le_pPrimeCore_of_ne (G := H) (p := p) (q := q)
        (fun hpq ↦ hqp hpq.symm)
    have hmap := Subgroup.map_mono (f := H.subtype) hcore
    rw [← map_pCore_fittingWithin_eq_map_pCore H q] at hmap
    simpa [Dq, D, Hp] using hmap
  have hHpNe : Hp ≠ ⊥ := by
    intro hbot
    exact hDqNe (le_bot_iff.mp (hDqHp.trans_eq hbot))
  have hHpNormalM : (Hp.subgroupOf M).Normal := by
    rw [hEqPrime]
    exact hMpNormal
  have hNormHpH : Subgroup.normalizer (Hp : Set G) = H :=
    mmax_normal hH hHpH hHpNormal hHpNe
  have hNormHpM : Subgroup.normalizer (Hp : Set G) = M :=
    mmax_normal hM hHpM hHpNormalM hHpNe
  exact hNormHpH.symm.trans hNormHpM

end Submission.OddOrder.BG.Section08
