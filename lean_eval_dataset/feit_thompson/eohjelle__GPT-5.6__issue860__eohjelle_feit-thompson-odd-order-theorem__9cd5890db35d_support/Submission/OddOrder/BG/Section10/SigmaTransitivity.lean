import Submission.OddOrder.BG.Section04.RankTwoDerivedComplement
import Submission.OddOrder.BG.Section06.PLengthOneProduct
import Submission.OddOrder.BG.Section09.RankThreeUniqueness
import Submission.OddOrder.BG.Section10.CorePredicates
import Submission.OddOrder.BG.Section10.MaximalCoreFacts
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRankSylowTransport
import Submission.OddOrder.MathlibSupport.PGroupNormalizer
import Submission.OddOrder.MathlibSupport.PPrimePCoreThirdIsomorphism
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# Bender--Glauberman Theorem 10.1: sigma transitivity

This file ports the two transitivity theorems immediately following the
definition of the `sigma`-core.  The main argument is the induction in
`BGsection10.v`, Theorem 10.1(a--c); part (d) is the preceding Sylow
transporter lemma.
-/

namespace Submission.OddOrder.BG.Section10

open Submission.OddOrder
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section06
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

private theorem map_conj_map_conj (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_one (H : Subgroup G) :
    H.map (MulAut.conj 1).toMonoidHom = H := by
  convert H.map_id using 1
  ext x
  simp

private theorem map_conj_inv_map_conj (H : Subgroup G) (a : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj a⁻¹).toMonoidHom = H := by
  rw [map_conj_map_conj]
  simpa only [inv_mul_cancel] using map_conj_one H

private theorem map_conj_eq_self_of_mem (H : Subgroup G) {a : G}
    (ha : a ∈ H) :
    H.map (MulAut.conj a).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.le_normalizer ha)

private theorem map_conj_inv_le_of_le_map_conj
    {A B : Subgroup G} {g : G}
    (h : A ≤ B.map (MulAut.conj g).toMonoidHom) :
    A.map (MulAut.conj g⁻¹).toMonoidHom ≤ B := by
  have hmapped := Subgroup.map_mono h
    (f := (MulAut.conj g⁻¹).toMonoidHom)
  rwa [map_conj_inv_map_conj] at hmapped

private theorem le_map_conj_inv_of_map_conj_le
    {A B : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom ≤ B) :
    A ≤ B.map (MulAut.conj g⁻¹).toMonoidHom := by
  have hmapped := Subgroup.map_mono h
    (f := (MulAut.conj g⁻¹).toMonoidHom)
  rwa [map_conj_inv_map_conj] at hmapped

/-- The conjugates of `M` which contain `X`, used only inside the proof of
Theorem 10.1. -/
private def conjugateOvergroups (M X : Subgroup G) : Set (Subgroup G) :=
  {H | (∃ g : G, H = M.map (MulAut.conj g).toMonoidHom) ∧ X ≤ H}

/-- Two overgroups lie in the same orbit under the centralizer of `X`. -/
private def centralizerConjugate
    (X H K : Subgroup G) : Prop :=
  ∃ c : G, c ∈ Subgroup.centralizer (X : Set G) ∧
    K = H.map (MulAut.conj c).toMonoidHom

private theorem centralizerConjugate_refl (X H : Subgroup G) :
    centralizerConjugate X H H := by
  refine ⟨1, by simp, ?_⟩
  exact (map_conj_one H).symm

private theorem centralizerConjugate_symm
    {X H K : Subgroup G} :
    centralizerConjugate X H K → centralizerConjugate X K H := by
  rintro ⟨c, hc, rfl⟩
  refine ⟨c⁻¹, (Subgroup.centralizer (X : Set G)).inv_mem hc, ?_⟩
  exact (map_conj_inv_map_conj H c).symm

private theorem centralizerConjugate_trans
    {X H K L : Subgroup G}
    (hHK : centralizerConjugate X H K)
    (hKL : centralizerConjugate X K L) :
    centralizerConjugate X H L := by
  rcases hHK with ⟨c, hc, rfl⟩
  rcases hKL with ⟨d, hd, rfl⟩
  refine ⟨d * c,
    (Subgroup.centralizer (X : Set G)).mul_mem hd hc, ?_⟩
  exact map_conj_map_conj H c d

private theorem centralizerConjugate_mono
    {X Y H K : Subgroup G} (hXY : X ≤ Y)
    (hHK : centralizerConjugate Y H K) :
    centralizerConjugate X H K := by
  rcases hHK with ⟨c, hc, hK⟩
  exact ⟨c, (Subgroup.centralizer_le hXY) hc, hK⟩

private def centralizerTransitiveOnConjugateOvergroups
    (M X : Subgroup G) : Prop :=
  ∀ ⦃H K : Subgroup G⦄,
    H ∈ conjugateOvergroups M X →
    K ∈ conjugateOvergroups M X →
    centralizerConjugate X H K

private theorem conjugateOvergroup_isMaximal
    [IsMinSimpleOddGroup G] {M X H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ conjugateOvergroups M X) :
    H ∈ minSimple_max_groups (G := G) := by
  rcases hH.1 with ⟨g, rfl⟩
  exact (mmaxJ M (MulAut.conj g)).mpr hM

private theorem conjugateOvergroup_map_of_mem_normalizer
    {M X H : Subgroup G} {g : G}
    (hH : H ∈ conjugateOvergroups M X)
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    H.map (MulAut.conj g).toMonoidHom ∈
      conjugateOvergroups M X := by
  rcases hH.1 with ⟨a, ha⟩
  refine ⟨?_, ?_⟩
  · refine ⟨g * a, ?_⟩
    rw [ha, map_conj_map_conj]
  · have hXmap : X.map (MulAut.conj g).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    rw [← hXmap]
    exact Subgroup.map_mono hH.2

private theorem centralizer_mul_relativeNormalizer_eq_normalizer
    [IsMinSimpleOddGroup G]
    {M X H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (htrans : centralizerTransitiveOnConjugateOvergroups M X)
    (hH : H ∈ conjugateOvergroups M X) :
    (Subgroup.centralizer (X : Set G) : Set G) *
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) =
      (Subgroup.normalizer (X : Set G) : Set G) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨c, hc, m, hm, rfl⟩
    exact (Subgroup.normalizer (X : Set G)).mul_mem
      (Subgroup.centralizer_le_normalizer (X : Set G) hc) hm.2
  · intro g hg
    have hHg := conjugateOvergroup_map_of_mem_normalizer hH hg
    obtain ⟨c, hc, hconj⟩ := htrans hH hHg
    let m : G := c⁻¹ * g
    have hmNormH : m ∈ Subgroup.normalizer (H : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      calc
        H.map (MulAut.conj m).toMonoidHom =
            (H.map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj c⁻¹).toMonoidHom := by
          simpa [m] using (map_conj_map_conj H g c⁻¹).symm
        _ = (H.map (MulAut.conj c).toMonoidHom).map
              (MulAut.conj c⁻¹).toMonoidHom := by rw [hconj]
        _ = H := map_conj_inv_map_conj H c
    have hHmax := conjugateOvergroup_isMaximal hM hH
    have hmH : m ∈ H := by
      rw [← norm_mmax hHmax]
      exact hmNormH
    have hcNorm : c ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.centralizer_le_normalizer (X : Set G) hc
    have hmNormX : m ∈ Subgroup.normalizer (X : Set G) := by
      exact (Subgroup.normalizer (X : Set G)).mul_mem
        ((Subgroup.normalizer (X : Set G)).inv_mem hcNorm) hg
    refine ⟨c, hc, m, ⟨hmH, hmNormX⟩, ?_⟩
    simp [m]

private theorem isPLengthOne_of_no_rank_three
    {H : Type u} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime]
    (hsol : IsSolvable H) (hodd : Odd (Nat.card H))
    (hRank : ¬ ∃ E : Subgroup H,
      IsElementaryAbelianOfRank p 3 E) :
    IsPLengthOne p H := by
  classical
  have hquotPrime : IsPPrimeSubgroup p
      (⊤ : Subgroup (H ⧸ pPrimePCore p H)) :=
    (rank2_der1_complement hsol hodd hRank).2.2
  have hnotFinal : ¬ p ∣ Nat.card (H ⧸ pPrimePCore p H) := by
    rw [IsPPrimeSubgroup, Subgroup.card_top] at hquotPrime
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hquotPrime
  have hnotTwoStep :
      ¬ p ∣ Nat.card ((H ⧸ pPrimeCore p H) ⧸
        pCore p (H ⧸ pPrimeCore p H)) := by
    rw [Nat.card_congr (pPrimePCoreQuotientEquiv p H).toEquiv]
    exact hnotFinal
  have hnotIndex :
      ¬ p ∣ (pCore p (H ⧸ pPrimeCore p H)).index := by
    rw [Subgroup.index_eq_card]
    exact hnotTwoStep
  let P : Sylow p (H ⧸ pPrimeCore p H) :=
    pCore_isPGroup.toSylow hnotIndex
  exact ⟨P, rfl⟩

/-! ### Bender--Glauberman Theorem 10.1(d) -/

/-- `BGsection10.v: sigma_Sylow_trans`, Theorem 10.1(d).

If a conjugate of a `sigma`-Sylow subgroup is still contained in the same
subgroup, then the conjugating element already belongs to that subgroup.
-/
theorem sigma_Sylow_trans
    {M : Subgroup G} {p : ℕ}
    (hp : p ∈ sigmaPrimes M) (P : Sylow p M) {g : G}
    (hconj : (ambientSylow M P).map
      (MulAut.conj g⁻¹).toMonoidHom ≤ M) :
    g ∈ M := by
  classical
  letI : Fact p.Prime := ⟨hp.1⟩
  let PG : Subgroup G := ambientSylow M P
  let Pg : Subgroup G :=
    PG.map (MulAut.conj g⁻¹).toMonoidHom
  let PgM : Subgroup M := Pg.subgroupOf M
  have hPgMp : IsPGroup p PgM := by
    exact ((P.isPGroup'.map M.subtype).map
      (MulAut.conj g⁻¹).toMonoidHom).comap_subtype
  let ePG : P ≃* PG :=
    (P : Subgroup M).equivMapOfInjective
      M.subtype M.subtype_injective
  let ePg : PG ≃* Pg :=
    (MulAut.conj g⁻¹).subgroupMap PG
  let ePgM : PgM ≃* Pg :=
    Subgroup.subgroupOfEquivOfLe hconj
  have hcardPgM : Nat.card PgM = Nat.card P := by
    calc
      Nat.card PgM = Nat.card Pg := Nat.card_congr ePgM.toEquiv
      _ = Nat.card PG := (Nat.card_congr ePg.toEquiv).symm
      _ = Nat.card P := (Nat.card_congr ePG.toEquiv).symm
  let PgSyl : Sylow p M :=
    { toSubgroup := PgM
      isPGroup' := hPgMp
      is_maximal' := by
        intro R hRp hPgMR
        obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
        exact (Subgroup.eq_of_le_of_card_ge hPgMR (by
          calc
            Nat.card R ≤ Nat.card S := Subgroup.card_le_of_le hRS
            _ = Nat.card P := Nat.card_congr (Sylow.equiv S P).toEquiv
            _ = Nat.card PgM := hcardPgM.symm)).symm }
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M P PgSyl
  have hmaps :
      PG.map (MulAut.conj g⁻¹).toMonoidHom =
        PG.map (MulAut.conj (m : G)).toMonoidHom := by
    calc
      PG.map (MulAut.conj g⁻¹).toMonoidHom =
          PgM.map M.subtype := by
        exact (Subgroup.map_subgroupOf_eq_of_le hconj).symm
      _ = ((m • P : Sylow p M) : Subgroup M).map M.subtype := by
        rw [hm]
      _ = PG.map (MulAut.conj (m : G)).toMonoidHom := by
        change ((P : Subgroup M).map
          (MulAut.conj m).toMonoidHom).map M.subtype =
            ((P : Subgroup M).map M.subtype).map
              (MulAut.conj (m : G)).toMonoidHom
        rw [Subgroup.map_map, Subgroup.map_map]
        apply congrArg (fun f : M →* G ↦ (P : Subgroup M).map f)
        ext x
        rfl
  let n : G := g * (m : G)
  have hnNorm : n ∈ Subgroup.normalizer (PG : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc
      PG.map (MulAut.conj n).toMonoidHom =
          (PG.map (MulAut.conj (m : G)).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by
        simpa only [n] using
          (map_conj_map_conj PG (m : G) g).symm
      _ = (PG.map (MulAut.conj g⁻¹).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by
        exact congrArg
          (fun H : Subgroup G ↦ H.map (MulAut.conj g).toMonoidHom)
          hmaps.symm
      _ = PG := by
        simpa only [inv_inv] using map_conj_inv_map_conj PG g⁻¹
  have hnM : n ∈ M := norm_sigma_Sylow hp P hnNorm
  have hmM : (m : G)⁻¹ ∈ M := M.inv_mem m.property
  have hgnm : g = n * (m : G)⁻¹ := by simp [n]
  rw [hgnm]
  exact M.mul_mem hnM hmM

/-! ### Bender--Glauberman Theorem 10.1(a--c) -/

/-- `BGsection10.v: sigma_group_trans`, Theorem 10.1(a--c).

The middle conjunct is the explicit Lean form of transitivity of the
centralizer on the conjugates of `M` which contain `X`.
-/
theorem sigma_group_trans
    [IsMinSimpleOddGroup G]
    {M X : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hp : p ∈ sigmaPrimes M) (hXp : IsPGroup p X) :
    (∀ g : G, X ≤ M →
      X.map (MulAut.conj g⁻¹).toMonoidHom ≤ M →
      ∃ c : G, c ∈ Subgroup.centralizer (X : Set G) ∧
        ∃ m : G, m ∈ M ∧ g = c * m) ∧
    (∀ ⦃H K : Subgroup G⦄,
      ((∃ a : G, H = M.map (MulAut.conj a).toMonoidHom) ∧ X ≤ H) →
      ((∃ b : G, K = M.map (MulAut.conj b).toMonoidHom) ∧ X ≤ K) →
      ∃ c : G, c ∈ Subgroup.centralizer (X : Set G) ∧
        K = H.map (MulAut.conj c).toMonoidHom) ∧
    (X ≤ M →
      (Subgroup.centralizer (X : Set G) : Set G) *
          ((M ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) =
        (Subgroup.normalizer (X : Set G) : Set G)) := by
  classical
  letI : Fact p.Prime := ⟨hp.1⟩

  have nonempty_overgroups (Y : Subgroup G) (hYp : IsPGroup p Y) :
      ∃ H : Subgroup G, H ∈ conjugateOvergroups M Y := by
    let S : Sylow p M := Classical.choice (inferInstance : Nonempty (Sylow p M))
    obtain ⟨Q, hQS⟩ := sigma_Sylow_G hM hp S
    obtain ⟨R, hYR⟩ := hYp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q R
    let H : Subgroup G := M.map (MulAut.conj g).toMonoidHom
    refine ⟨H, ⟨⟨g, rfl⟩, ?_⟩⟩
    have hQM : (Q : Subgroup G) ≤ M := by
      rw [hQS]
      exact Subgroup.map_subtype_le _
    have hRmap : (R : Subgroup G) =
        (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rw [← hg]
      rfl
    exact hYR.trans (hRmap.le.trans (Subgroup.map_mono hQM))

  let Claim : ℕ → Prop := fun n ↦
    ∀ Y : Subgroup G,
      Nat.card G - Nat.card Y < n → IsPGroup p Y →
      centralizerTransitiveOnConjugateOvergroups M Y

  have hClaim : ∀ n, Claim n := by
    intro n
    induction n with
    | zero =>
        intro Y hmeasure
        omega
    | succ n ih =>
        intro Y hmeasure hYp

        have ihY {Z : Subgroup G} (hYZ : Y < Z)
            (hZp : IsPGroup p Z) :
            centralizerTransitiveOnConjugateOvergroups M Z := by
          apply ih Z
          have hcardYZ : Nat.card Y < Nat.card Z :=
            natCard_subgroup_lt_of_lt hYZ
          have hcardZG : Nat.card Z ≤ Nat.card G :=
            by simpa only [Subgroup.card_top] using
              (Subgroup.card_le_of_le (H := Z) le_top)
          omega
          exact hZp

        by_cases hYbot : Y = ⊥
        · subst Y
          intro H K hH hK
          rcases hH.1 with ⟨a, rfl⟩
          rcases hK.1 with ⟨b, rfl⟩
          refine ⟨b * a⁻¹, ?_, ?_⟩
          · rw [Subgroup.mem_centralizer_iff]
            intro y hy
            have hy1 : y = 1 := by simpa using hy
            subst y
            simp
          · simpa using (map_conj_map_conj M a (b * a⁻¹)).symm

        let L : Subgroup G := Subgroup.normalizer (Y : Set G)
        have hYproper : Y < ⊤ := mFT_pgroup_proper Y hYp
        have hLproper : L < ⊤ := by
          dsimp only [L]
          exact mFT_norm_proper Y hYbot hYproper

        have separated_overgroups
            {B B' : Subgroup G}
            (hB : B ∈ conjugateOvergroups M Y)
            (hB' : B' ∈ conjugateOvergroups M Y)
            (hne : B ≠ B') :
            ∃ T : Sylow p (B ⊓ L : Subgroup G),
              Y < ambientSylow (B ⊓ L : Subgroup G) T := by
          let YB : Subgroup B := Y.subgroupOf B
          have hYBp : IsPGroup p YB := hYp.comap_subtype
          obtain ⟨S, hYBS⟩ := hYBp.exists_le_sylow
          let SG : Subgroup G := ambientSylow B S
          have hYSG : Y ≤ SG := by
            rw [← Subgroup.map_subgroupOf_eq_of_le hB.2]
            exact Subgroup.map_mono hYBS
          have hSGp : IsPGroup p SG := S.isPGroup'.map B.subtype
          rcases eq_or_lt_of_le hYSG with hEq | hlt
          · have hpB : p ∈ sigmaPrimes B := by
              rcases hB.1 with ⟨a, rfl⟩
              rw [sigmaPrimes_conj]
              exact hp
            rcases hB.1 with ⟨a, ha⟩
            rcases hB'.1 with ⟨b, hb⟩
            let k : G := b * a⁻¹
            have hB'conj : B' = B.map (MulAut.conj k).toMonoidHom := by
              rw [ha, hb]
              simpa [k] using (map_conj_map_conj M a k).symm
            have hback : Y.map (MulAut.conj k⁻¹).toMonoidHom ≤ B :=
              map_conj_inv_le_of_le_map_conj (hB'conj ▸ hB'.2)
            have hkB : k ∈ B := by
              apply sigma_Sylow_trans hpB S
              simpa [SG, hEq] using hback
            exfalso
            apply hne
            rw [hB'conj, map_conj_eq_self_of_mem B hkB]
          · have hYSL : Y < SG ⊓ L := by
              dsimp only [L]
              exact lt_inf_normalizer_of_isPGroup hSGp hlt
            have hSLle : SG ⊓ L ≤ B ⊓ L := by
              exact inf_le_inf (Subgroup.map_subtype_le _) le_rfl
            let SL : Subgroup ↑(B ⊓ L) := (SG ⊓ L).subgroupOf (B ⊓ L)
            have hSLp : IsPGroup p SL :=
              (hSGp.to_le inf_le_left).comap_subtype
            obtain ⟨T, hSLT⟩ := hSLp.exists_le_sylow
            refine ⟨T, lt_of_lt_of_le hYSL ?_⟩
            rw [← Subgroup.map_subgroupOf_eq_of_le hSLle]
            exact Subgroup.map_mono hSLT

        obtain ⟨M1, hM1⟩ := nonempty_overgroups Y hYp

        have hbase : ∀ ⦃M2 : Subgroup G⦄,
            M2 ∈ conjugateOvergroups M Y →
            centralizerConjugate Y M1 M2 := by
          intro M2 hM2
          by_cases hM12 : M1 = M2
          · subst M2
            exact centralizerConjugate_refl Y M1

          obtain ⟨T2, hYT2⟩ :=
            separated_overgroups hM2 hM1 (Ne.symm hM12)
          obtain ⟨T1, hYT1⟩ :=
            separated_overgroups hM1 hM2 hM12
          let X2 : Subgroup G := ambientSylow (M2 ⊓ L) T2
          let X1 : Subgroup G := ambientSylow (M1 ⊓ L) T1
          have hX1p : IsPGroup p X1 := T1.isPGroup'.map (M1 ⊓ L).subtype
          have hX2p : IsPGroup p X2 := T2.isPGroup'.map (M2 ⊓ L).subtype
          have hX1L : X1 ≤ L :=
            (Subgroup.map_subtype_le _).trans inf_le_right
          have hX2L : X2 ≤ L :=
            (Subgroup.map_subtype_le _).trans inf_le_right
          have hX1M1 : X1 ≤ M1 :=
            (Subgroup.map_subtype_le _).trans inf_le_left
          have hX2M2 : X2 ≤ M2 :=
            (Subgroup.map_subtype_le _).trans inf_le_left

          let X1L : Subgroup L := X1.subgroupOf L
          have hX1Lp : IsPGroup p X1L := hX1p.comap_subtype
          obtain ⟨P, hX1P⟩ := hX1Lp.exists_le_sylow
          let PG : Subgroup G := ambientSylow L P
          have hPGp : IsPGroup p PG := P.isPGroup'.map L.subtype
          have hX1PG : X1 ≤ PG := by
            rw [← Subgroup.map_subgroupOf_eq_of_le hX1L]
            exact Subgroup.map_mono hX1P
          have hYPG : Y < PG := lt_of_lt_of_le hYT1 hX1PG
          obtain ⟨M0, hM0⟩ := nonempty_overgroups PG hPGp
          have hPGM0 : PG ≤ M0 := hM0.2

          let X2L : Subgroup L := X2.subgroupOf L
          have hX2Lp : IsPGroup p X2L := hX2p.comap_subtype
          obtain ⟨Q, hX2Q⟩ := hX2Lp.exists_le_sylow
          obtain ⟨t, ht⟩ := MulAction.exists_smul_eq L Q P
          have hX2tPG :
              X2.map (MulAut.conj (t : G)).toMonoidHom ≤ PG := by
            rintro _ ⟨x, hx, rfl⟩
            let xL : L := ⟨x, hX2L hx⟩
            have hxQ : xL ∈ Q := hX2Q hx
            have htxP : (MulAut.conj t).toMonoidHom xL ∈ P := by
              rw [← ht]
              exact Subgroup.mem_map_of_mem
                (MulAut.conj t).toMonoidHom hxQ
            exact ⟨(MulAut.conj t).toMonoidHom xL, htxP, rfl⟩

          let M0t : Subgroup G :=
            M0.map (MulAut.conj (t : G)⁻¹).toMonoidHom
          have hX2M0t : X2 ≤ M0t :=
            le_map_conj_inv_of_map_conj_le (hX2tPG.trans hPGM0)
          have hM0t : M0t ∈ conjugateOvergroups M X2 := by
            rcases hM0.1 with ⟨a, ha⟩
            refine ⟨⟨(t : G)⁻¹ * a, ?_⟩, hX2M0t⟩
            dsimp only [M0t]
            rw [ha, map_conj_map_conj]

          have htrX1 := ihY hYT1 hX1p
          have htrX2 := ihY hYT2 hX2p
          have hM0X1 : M0 ∈ conjugateOvergroups M X1 :=
            ⟨hM0.1, hX1PG.trans hPGM0⟩
          have hM1X1 : M1 ∈ conjugateOvergroups M X1 :=
            ⟨hM1.1, hX1M1⟩
          have hM2X2 : M2 ∈ conjugateOvergroups M X2 :=
            ⟨hM2.1, hX2M2⟩
          have hrel01 : centralizerConjugate Y M0 M1 :=
            centralizerConjugate_mono hYT1.le
              (htrX1 hM0X1 hM1X1)
          have hrel02 : centralizerConjugate Y M0t M2 :=
            centralizerConjugate_mono hYT2.le
              (htrX2 hM0t hM2X2)

          have hbridge : centralizerConjugate Y M0 M0t := by
            by_cases hRankPG :
                HasElementaryAbelianRankAtLeast p 3 PG
            · have hPGuniq :
                  PG ∈ minSimple_uniq_max_groups (G := G) :=
                rank3_Uniqueness (mFT_pgroup_proper PG hPGp)
                  ⟨p, Fact.out, hRankPG⟩
              have hM0max := conjugateOvergroup_isMaximal hM hM0
              have hPGfamily :
                  minSimple_max_groups_of (G := G) (PG : Set G) = {M0} :=
                def_uniq_mmax hPGuniq hM0max hPGM0
              have hPGL : PG ≤ L := Subgroup.map_subtype_le _
              have hLM0 : L ≤ M0 :=
                sub_uniq_mmax hPGfamily hPGL hLproper
              have htM0 : (t : G) ∈ M0 := hLM0 t.property
              have hM0tEq : M0t = M0 := by
                dsimp only [M0t]
                exact map_conj_eq_self_of_mem M0 (M0.inv_mem htM0)
              rw [hM0tEq]
              exact centralizerConjugate_refl Y M0
            · have hNoPG : ¬ ∃ E : Subgroup PG,
                  IsElementaryAbelianOfRank p 3 E := by
                rintro ⟨E, hE⟩
                apply hRankPG
                exact ⟨E.map PG.subtype, Subgroup.map_subtype_le E,
                  hE.map_of_injective PG.subtype PG.subtype_injective⟩
              have hNoL : ¬ ∃ E : Subgroup L,
                  IsElementaryAbelianOfRank p 3 E :=
                no_elementaryAbelian_rank_three_of_sylow_map_le
                  P le_rfl hNoPG
              letI : IsSolvable L := mFT_sol hLproper
              have hoddL : Odd (Nat.card L) := mFT_odd L
              have hpl : IsPLengthOne p L :=
                isPLengthOne_of_no_rank_three (by infer_instance) hoddL hNoL
              let YL : Subgroup L := Y.subgroupOf L
              have hYLPG : YL ≤ (P : Subgroup L) := by
                intro y hy
                exact hX1P (hYT1.le hy)
              have htNYL : t ∈ Subgroup.normalizer (YL : Set L) := by
                rw [← Subgroup.subgroupOf_normalizer_eq Subgroup.le_normalizer]
                exact t.property
              have hYtP : ∀ y ∈ (YL : Set L),
                  (MulAut.conj ((t⁻¹ : L)⁻¹)).toMonoidHom y ∈ P := by
                intro y hy
                simp only [inv_inv]
                apply hYLPG
                have hmapYL :
                    YL.map (MulAut.conj t).toMonoidHom = YL :=
                  Subgroup.mem_normalizer_iff_map_conj_eq.mp htNYL
                rw [← hmapYL]
                exact Subgroup.mem_map_of_mem
                  (MulAut.conj t).toMonoidHom hy
              obtain ⟨c, hc, u, hu, htu⟩ :=
                plength1_Sylow_trans P hpl (YL : Set L) hYLPG
                  t⁻¹ hYtP
              have hcG : (c : G) ∈
                  Subgroup.centralizer (Y : Set G) := by
                rw [Subgroup.mem_centralizer_iff]
                intro y hy
                let yL : L := ⟨y, Subgroup.le_normalizer hy⟩
                exact congrArg Subtype.val
                  ((Subgroup.mem_centralizer_iff.mp hc) yL hy)
              have huG : (u : G) ∈
                  Subgroup.normalizer (PG : Set G) := by
                apply Subgroup.le_normalizer_map L.subtype
                exact ⟨u, hu, rfl⟩
              have htrPG := ihY hYPG hPGp
              have hfactor :=
                centralizer_mul_relativeNormalizer_eq_normalizer
                  hM htrPG hM0
              have huProd : (u : G) ∈
                  (Subgroup.centralizer (PG : Set G) : Set G) *
                    ((M0 ⊓ Subgroup.normalizer (PG : Set G) :
                      Subgroup G) : Set G) := by
                rw [hfactor]
                exact huG
              rcases huProd with ⟨d, hd, m, hm, hdu⟩
              have hdY : d ∈ Subgroup.centralizer (Y : Set G) :=
                (Subgroup.centralizer_le hYPG.le) hd
              let z : G := (c : G) * d
              have hz : z ∈ Subgroup.centralizer (Y : Set G) :=
                (Subgroup.centralizer (Y : Set G)).mul_mem hcG hdY
              refine ⟨z, hz, ?_⟩
              have htuG : ((t⁻¹ : L) : G) = (c : G) * (u : G) :=
                congrArg Subtype.val htu
              have htFactor : (t : G)⁻¹ = z * m := by
                rw [show (t : G)⁻¹ = ((t⁻¹ : L) : G) by rfl,
                  htuG, ← hdu]
                simp [z, mul_assoc]
              dsimp only [M0t]
              rw [htFactor]
              calc
                M0.map (MulAut.conj (z * m)).toMonoidHom =
                    (M0.map (MulAut.conj m).toMonoidHom).map
                      (MulAut.conj z).toMonoidHom :=
                  (map_conj_map_conj M0 m z).symm
                _ = M0.map (MulAut.conj z).toMonoidHom := by
                  rw [map_conj_eq_self_of_mem M0 hm.1]

          exact centralizerConjugate_trans
            (centralizerConjugate_symm hrel01)
            (centralizerConjugate_trans hbridge hrel02)

        intro H K hH hK
        exact centralizerConjugate_trans
          (centralizerConjugate_symm (hbase hH)) (hbase hK)

  have htrans : centralizerTransitiveOnConjugateOvergroups M X :=
    hClaim (Nat.card G - Nat.card X + 1) X (by omega) hXp

  have hMover (hXM : X ≤ M) : M ∈ conjugateOvergroups M X := by
    exact ⟨⟨1, (map_conj_one M).symm⟩, hXM⟩

  have part_a : ∀ g : G, X ≤ M →
      X.map (MulAut.conj g⁻¹).toMonoidHom ≤ M →
      ∃ c : G, c ∈ Subgroup.centralizer (X : Set G) ∧
        ∃ m : G, m ∈ M ∧ g = c * m := by
    intro g hXM hXgM
    have hXMg : X ≤ M.map (MulAut.conj g).toMonoidHom :=
      by simpa only [inv_inv] using
        (le_map_conj_inv_of_map_conj_le hXgM)
    have hMg : M.map (MulAut.conj g).toMonoidHom ∈
        conjugateOvergroups M X := ⟨⟨g, rfl⟩, hXMg⟩
    obtain ⟨c, hc, hconj⟩ := htrans (hMover hXM) hMg
    let m : G := c⁻¹ * g
    have hmNorm : m ∈ Subgroup.normalizer (M : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      calc
        M.map (MulAut.conj m).toMonoidHom =
            (M.map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj c⁻¹).toMonoidHom := by
          simpa [m] using (map_conj_map_conj M g c⁻¹).symm
        _ = (M.map (MulAut.conj c).toMonoidHom).map
              (MulAut.conj c⁻¹).toMonoidHom := by rw [hconj]
        _ = M := map_conj_inv_map_conj M c
    have hmM : m ∈ M := by
      rw [← norm_mmax hM]
      exact hmNorm
    exact ⟨c, hc, m, hmM, by simp [m]⟩

  refine ⟨part_a, ?_, ?_⟩
  · simpa [centralizerTransitiveOnConjugateOvergroups,
      conjugateOvergroups, centralizerConjugate] using htrans
  · intro hXM
    exact centralizer_mul_relativeNormalizer_eq_normalizer
      hM htrans (hMover hXM)

end Submission.OddOrder.BG.Section10
