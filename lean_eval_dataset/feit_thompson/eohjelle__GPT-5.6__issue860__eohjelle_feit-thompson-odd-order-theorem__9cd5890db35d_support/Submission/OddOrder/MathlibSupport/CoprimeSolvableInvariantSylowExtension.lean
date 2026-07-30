import Mathlib.GroupTheory.SchurZassenhaus
import Submission.OddOrder.MathlibSupport.Hall
import Submission.OddOrder.MathlibSupport.PGroupNormalizer
import Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow
import Submission.OddOrder.MathlibSupport.SolvableComplementConjugacy
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# Invariant Sylow extension under a coprime solvable action

This file supplies the `p`-local form of MathComp's
`coprime_Hall_subset` needed in Bender--Glauberman Section 7.  If `A`
normalizes a finite solvable group `L` coprimely, every `A`-normalized
`p`-subgroup of `L` is contained in an `A`-normalized Sylow subgroup of
`L`.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- A nontrivial subgroup whose prime divisors all lie in the singleton
`{p}` forces `p` to be prime. -/
theorem prime_of_isPiNumber_singleton_of_ne_bot {p : ℕ} {P : Subgroup G}
    (hPpi : IsPiNumber ({p} : Set ℕ) (Nat.card P)) (hPne : P ≠ ⊥) :
    p.Prime := by
  have hcardNe : Nat.card P ≠ 1 :=
    ne_of_gt (P.one_lt_card_iff_ne_bot.mpr hPne)
  obtain ⟨q, hq, hqdiv⟩ := Nat.exists_prime_and_dvd hcardNe
  have hqp : q = p := Set.mem_singleton_iff.mp (hPpi hq hqdiv)
  simpa [← hqp] using hq

/-- Singleton prime support is the cardinality form of `IsPGroup`. -/
theorem isPGroup_of_isPiNumber_singleton {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hPpi : IsPiNumber ({p} : Set ℕ) (Nat.card P)) :
    IsPGroup p P := by
  apply IsPGroup.iff_card.mpr
  refine ⟨(Nat.card P).primeFactorsList.length, ?_⟩
  apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
  intro q hq hqdiv
  exact Set.mem_singleton_iff.mp (hPpi hq hqdiv)

/-- A coprime subgroup of automorphisms of a finite solvable subgroup fixes
some Sylow subgroup.  This is the existence input for the extension form of
`coprime_Hall_subset`.

The proof applies the Frattini argument in `A ⊔ L`, constructs a complement
inside the normalizer of an arbitrary Sylow subgroup, and conjugates that
complement back to `A` by the solvable Schur--Zassenhaus theorem. -/
theorem exists_sylow_normalized_of_coprime_of_isSolvable
    {p : ℕ} [Fact p.Prime] {A L : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hcop : (Nat.card L).Coprime (Nat.card A))
    (hsol : IsSolvable L) :
    ∃ P : Sylow p L,
      A ≤ Subgroup.normalizer
        (((P : Subgroup L).map L.subtype : Subgroup G) : Set G) := by
  classical
  let J : Subgroup G := A ⊔ L
  let AJ : Subgroup J := A.subgroupOf J
  let LJ : Subgroup J := L.subgroupOf J
  have hAJJ : A ≤ J := le_sup_left
  have hLJJ : L ≤ J := le_sup_right
  letI : LJ.Normal := by
    dsimp [LJ, J]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hAL
  have hcardAJ : Nat.card AJ = Nat.card A :=
    natCard_subgroupOf_eq hAJJ
  have hcardLJ : Nat.card LJ = Nat.card L :=
    natCard_subgroupOf_eq hLJJ
  have hcopLJAJ : (Nat.card LJ).Coprime (Nat.card AJ) := by
    simpa [hcardLJ, hcardAJ] using hcop
  have hdisjoint : Disjoint LJ AJ :=
    Subgroup.disjoint_of_coprime_natCard hcopLJAJ
  have hsup : LJ ⊔ AJ = ⊤ := by
    rw [sup_comm, ← Subgroup.subgroupOf_sup hAJJ hLJJ]
    exact Subgroup.subgroupOf_self J
  have hcompAJ : LJ.IsComplement' AJ := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjoint
    rw [← Subgroup.normal_mul LJ AJ, hsup]
    rfl
  letI : IsSolvable L := hsol
  let eJL : LJ ≃* L := Subgroup.subgroupOfEquivOfLe hLJJ
  letI : IsSolvable LJ :=
    solvable_of_solvable_injective (f := eJL.toMonoidHom) eJL.injective
  have hcopLJindex : (Nat.card LJ).Coprime LJ.index := by
    rw [hcompAJ.symm.index_eq_card]
    exact hcopLJAJ
  let P₀ : Sylow p LJ := default
  let PJ : Subgroup J := (P₀ : Subgroup LJ).map LJ.subtype
  have hfrattini : Subgroup.normalizer (PJ : Set J) ⊔ LJ = ⊤ := by
    simpa [PJ] using P₀.normalizer_sup_eq_top
  let N : Subgroup J := Subgroup.normalizer (PJ : Set J)
  let LN : Subgroup N := LJ.comap N.subtype
  letI : LN.Normal := by
    dsimp [LN]
    infer_instance
  have hindexLN : LN.index = LJ.index := by
    dsimp [LN]
    rw [← LJ.relIndex_top_right, ← hfrattini]
    exact (Subgroup.relIndex_sup_right N LJ).symm
  have hcardLNdvd : Nat.card LN ∣ Nat.card LJ :=
    Subgroup.card_comap_dvd_of_injective LJ N.subtype
      N.subtype_injective
  have hcopLN : (Nat.card LN).Coprime LN.index := by
    rw [hindexLN]
    exact hcopLJindex.coprime_dvd_left hcardLNdvd
  obtain ⟨C, hC⟩ := LN.exists_right_complement'_of_coprime hcopLN
  let B : Subgroup J := C.map N.subtype
  have hcardC : Nat.card C = Nat.card AJ := by
    rw [← hC.symm.index_eq_card, hindexLN,
      hcompAJ.symm.index_eq_card]
  have hcardB : Nat.card B = Nat.card AJ := by
    rw [Subgroup.card_map_of_injective (K := C) N.subtype_injective]
    exact hcardC
  have hBcomp : LJ.IsComplement' B := by
    apply Subgroup.isComplement'_of_coprime
    · rw [hcardB]
      exact hcompAJ.card_mul
    · rw [hcardB]
      exact hcopLJAJ
  have hBnormPJ : B ≤ Subgroup.normalizer (PJ : Set J) := by
    dsimp [B, N]
    exact Subgroup.map_subtype_le C
  obtain ⟨x, hBx⟩ :=
    Subgroup.solvable_complement_conjugacy hcopLJindex hcompAJ hBcomp
  let xi : LJ := x⁻¹
  let S : Subgroup J := PJ.map (MulAut.conj (xi : J)).toMonoidHom
  have hAJnormS : AJ ≤ Subgroup.normalizer (S : Set J) := by
    intro a ha
    let b : J := (x : J) * a * (x : J)⁻¹
    have hbB : b ∈ B := by
      rw [hBx]
      exact ⟨a, ha, rfl⟩
    have hbNorm : b ∈ Subgroup.normalizer (PJ : Set J) :=
      hBnormPJ hbB
    have hbMap : (MulAut.conj (xi : J)) b ∈
        (Subgroup.normalizer (PJ : Set J)).map
          (MulAut.conj (xi : J)).toMonoidHom :=
      ⟨b, hbNorm, rfl⟩
    rw [Subgroup.map_equiv_normalizer_eq PJ (MulAut.conj (xi : J))]
      at hbMap
    have hba : (MulAut.conj (xi : J)) b = a := by
      dsimp [b, xi]
      group
    rwa [hba] at hbMap
  have hPJLJ : PJ ≤ LJ := by
    dsimp [PJ]
    exact Subgroup.map_subtype_le (P₀ : Subgroup LJ)
  have hSLJ : S ≤ LJ := by
    rintro s ⟨y, hy, rfl⟩
    exact LJ.mul_mem (LJ.mul_mem x⁻¹.property (hPJLJ hy))
      (LJ.inv_mem x⁻¹.property)
  let T : Subgroup LJ :=
    (P₀ : Subgroup LJ).map (MulAut.conj xi).toMonoidHom
  have hTindex : T.index = (P₀ : Subgroup LJ).index := by
    dsimp [T]
    exact Subgroup.index_map_equiv (P₀ : Subgroup LJ) (MulAut.conj xi)
  have hTp : IsPGroup p T := by
    dsimp [T]
    exact P₀.isPGroup'.map (MulAut.conj xi).toMonoidHom
  let P₁ : Sylow p LJ := hTp.toSylow (by
    rw [hTindex]
    exact P₀.not_dvd_index)
  have hP₁map : (P₁ : Subgroup LJ).map LJ.subtype = S := by
    change T.map LJ.subtype = S
    dsimp [T, S, PJ]
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  let TL : Subgroup L :=
    (P₁ : Subgroup LJ).map eJL.toMonoidHom
  have hTLindex : TL.index = (P₁ : Subgroup LJ).index := by
    dsimp [TL]
    exact Subgroup.index_map_equiv (P₁ : Subgroup LJ) eJL
  have hTLp : IsPGroup p TL := by
    dsimp [TL]
    exact P₁.isPGroup'.map eJL.toMonoidHom
  let P : Sylow p L := hTLp.toSylow (by
    rw [hTLindex]
    exact P₁.not_dvd_index)
  let SG : Subgroup G := S.map J.subtype
  have hAnormSG : A ≤ Subgroup.normalizer (SG : Set G) := by
    have hmapped : AJ.map J.subtype ≤
        (Subgroup.normalizer (S : Set J)).map J.subtype :=
      Subgroup.map_mono hAJnormS
    rw [Subgroup.map_subgroupOf_eq_of_le hAJJ] at hmapped
    exact hmapped.trans (Subgroup.le_normalizer_map J.subtype)
  have hPmap : (P : Subgroup L).map L.subtype = SG := by
    change TL.map L.subtype = S.map J.subtype
    dsimp [TL]
    rw [Subgroup.map_map, ← hP₁map, Subgroup.map_map]
    rfl
  refine ⟨P, ?_⟩
  simpa [hPmap] using hAnormSG

/-- `p`-local form of MathComp's `coprime_Hall_subset`: every normalized
`p`-subgroup extends to a normalized Sylow subgroup under a coprime action on
a finite solvable subgroup. -/
theorem exists_normalized_sylow_ge_of_coprime_of_isSolvable
    {p : ℕ} [Fact p.Prime] {A L X : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hcop : (Nat.card L).Coprime (Nat.card A))
    (hsol : IsSolvable L)
    (hXL : X ≤ L) (hXp : IsPGroup p X)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    ∃ P : Sylow p L,
      A ≤ Subgroup.normalizer
          (((P : Subgroup L).map L.subtype : Subgroup G) : Set G) ∧
        X ≤ (P : Subgroup L).map L.subtype := by
  classical
  let Good : Subgroup G → Prop := fun Y =>
    X ≤ Y ∧ Y ≤ L ∧ IsPGroup p Y ∧
      A ≤ Subgroup.normalizer (Y : Set G)
  have hXgood : Good X := ⟨le_rfl, hXL, hXp, hAX⟩
  obtain ⟨Y, hXY, hY, hYmax⟩ :=
    Finite.exists_le_maximal (p := Good) hXgood
  have hYL : Y ≤ L := hY.2.1
  let YL : Subgroup L := Y.subgroupOf L
  have hYLp : IsPGroup p YL :=
    hY.2.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hYL).symm
  have hpIndex : ¬p ∣ YL.index := by
    intro hpIndex
    let N : Subgroup G := L ⊓ Subgroup.normalizer (Y : Set G)
    have hYN : Y ≤ N :=
      le_inf hYL Subgroup.le_normalizer
    have hAN : A ≤ Subgroup.normalizer (N : Set G) := by
      exact (le_inf hAL (hY.2.2.2.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hNL : N ≤ L := inf_le_left
    have hcopN : (Nat.card N).Coprime (Nat.card A) :=
      hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hNL)
    let toL : N →* L := Subgroup.inclusion hNL
    letI : IsSolvable L := hsol
    have hsolN : IsSolvable N :=
      solvable_of_solvable_injective (f := toL) (by
        intro a b hab
        exact Subtype.ext (congrArg (fun z : L => (z : G)) hab))
    obtain ⟨PN, hAPN⟩ :=
      exists_sylow_normalized_of_coprime_of_isSolvable
        (p := p) hAN hcopN hsolN
    let R : Subgroup G := (PN : Subgroup N).map N.subtype
    let YN : Subgroup N := Y.subgroupOf N
    letI : YN.Normal := by
      dsimp [YN]
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYN]
      exact inf_le_right
    have hYNp : IsPGroup p YN :=
      hY.2.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hYN).symm
    have hYNPN : YN ≤ (PN : Subgroup N) :=
      hYNp.le_sylow_of_normal PN
    have hYltR : Y < R := by
      have hYNltPN : YN < (PN : Subgroup N) := by
        refine lt_of_le_of_ne hYNPN ?_
        intro hPNeq
        have hYLS : ∃ S : Sylow p L, YL ≤ (S : Subgroup L) :=
          hYLp.exists_le_sylow
        obtain ⟨SL, hYLSL⟩ := hYLS
        have hYLltSL : YL < (SL : Subgroup L) := by
          refine lt_of_le_of_ne hYLSL ?_
          intro hEq
          exact SL.not_dvd_index (by simpa [hEq] using hpIndex)
        let TL : Subgroup L :=
          (SL : Subgroup L) ⊓ Subgroup.normalizer (YL : Set L)
        have hYLltTL : YL < TL := by
          exact lt_inf_normalizer_of_isPGroup SL.isPGroup' hYLltSL
        let TG : Subgroup G := TL.map L.subtype
        have hTGN : TG ≤ N := by
          apply le_inf
          · exact Subgroup.map_subtype_le TL
          · have hmapped :
                (Subgroup.normalizer (YL : Set L)).map L.subtype ≤
                  Subgroup.normalizer
                    ((YL.map L.subtype : Subgroup G) : Set G) := by
              exact Subgroup.le_normalizer_map L.subtype
            rw [Subgroup.map_subgroupOf_eq_of_le hYL] at hmapped
            exact (Subgroup.map_mono inf_le_right).trans hmapped
        let TN : Subgroup N := TG.subgroupOf N
        have hTLp : IsPGroup p TL :=
          SL.isPGroup'.to_le inf_le_left
        have hTGp : IsPGroup p TG := hTLp.map L.subtype
        have hTNp : IsPGroup p TN :=
          hTGp.of_equiv (Subgroup.subgroupOfEquivOfLe hTGN).symm
        have hYltTG : Y < TG := by
          calc
            Y = YL.map L.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hYL).symm
            _ < TL.map L.subtype :=
              Subgroup.map_subtype_lt_map_subtype.mpr hYLltTL
            _ = TG := rfl
        have hYNltTN : YN < TN := by
          apply Subgroup.map_subtype_lt_map_subtype.mp
          calc
            YN.map N.subtype = Y :=
              Subgroup.map_subgroupOf_eq_of_le hYN
            _ < TG := hYltTG
            _ = TN.map N.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hTGN).symm
        have hPNleTN : (PN : Subgroup N) ≤ TN := by
          rw [← hPNeq]
          exact hYNltTN.le
        have hTNeqPN : TN = (PN : Subgroup N) :=
          PN.is_maximal' hTNp hPNleTN
        exact hYNltTN.ne (hPNeq.trans hTNeqPN.symm)
      calc
        Y = YN.map N.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hYN).symm
        _ < (PN : Subgroup N).map N.subtype :=
          Subgroup.map_subtype_lt_map_subtype.mpr hYNltPN
        _ = R := rfl
    have hRgood : Good R := by
      refine ⟨hY.1.trans hYltR.le, ?_, ?_, hAPN⟩
      · exact (Subgroup.map_subtype_le PN).trans hNL
      · exact PN.isPGroup'.map N.subtype
    exact hYltR.2 (hYmax hRgood hYltR.le)
  let P : Sylow p L := hYLp.toSylow hpIndex
  refine ⟨P, ?_, ?_⟩
  · change A ≤ Subgroup.normalizer
      (((YL : Subgroup L).map L.subtype : Subgroup G) : Set G)
    rw [Subgroup.map_subgroupOf_eq_of_le hYL]
    exact hY.2.2.2
  · change X ≤ (YL : Subgroup L).map L.subtype
    rw [Subgroup.map_subgroupOf_eq_of_le hYL]
    exact hY.1

/-- Prime-set/cardinality wrapper matching the normalized subgroup predicate
used in Bender--Glauberman Section 7.  Nontriviality recovers primality of
`p`, after which the `IsPGroup` extension theorem applies. -/
theorem exists_normalized_sylow_ge_of_coprime_of_isSolvable_of_isPiNumber
    {p : ℕ} {A L X : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hcop : (Nat.card L).Coprime (Nat.card A))
    (hsol : IsSolvable L)
    (hXL : X ≤ L)
    (hXpi : IsPiNumber ({p} : Set ℕ) (Nat.card X))
    (hXne : X ≠ ⊥)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    ∃ P : Sylow p L,
      A ≤ Subgroup.normalizer
          (((P : Subgroup L).map L.subtype : Subgroup G) : Set G) ∧
        X ≤ (P : Subgroup L).map L.subtype := by
  letI : Fact p.Prime :=
    ⟨prime_of_isPiNumber_singleton_of_ne_bot hXpi hXne⟩
  exact exists_normalized_sylow_ge_of_coprime_of_isSolvable
    hAL hcop hsol hXL (isPGroup_of_isPiNumber_singleton hXpi) hAX

end Submission.OddOrder.MathlibSupport
