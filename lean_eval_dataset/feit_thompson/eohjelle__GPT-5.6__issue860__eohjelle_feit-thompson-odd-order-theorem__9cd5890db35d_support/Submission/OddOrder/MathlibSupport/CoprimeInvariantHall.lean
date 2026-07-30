import Submission.OddOrder.MathlibSupport.MinimalNormalUnderElementaryAbelian
import Submission.OddOrder.MathlibSupport.MinimalNormalUnderExistence
import Submission.OddOrder.MathlibSupport.SolvableComplementConjugacy
import Submission.OddOrder.MathlibSupport.SolvablePrimeComplement
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# Prime-complement Hall subgroups invariant under a coprime action

This is the prime-complement specialization of MathComp's
`coprime_Hall_exists` (Bender--Glauberman, Proposition 1.5(a)).  If a finite
solvable subgroup is normalized by a subgroup of coprime order, it has a
Hall `p'`-subgroup normalized by that actor.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

private theorem exists_prime_isPGroup_of_minimalNormalUnder
    {G : Type u} [Group G] [Finite G]
    {E A : Subgroup G} [IsSolvable E]
    (hE : IsMinimalNormalUnder E A) :
    ∃ r : ℕ, r.Prime ∧ IsPGroup r E := by
  classical
  letI : IsMulCommutative E := hE.isMulCommutative_of_isSolvable
  have hcard : 1 < Nat.card E :=
    E.one_lt_card_iff_ne_bot.mpr hE.ne_bot
  obtain ⟨r, hr, hrdiv⟩ := Nat.exists_prime_and_dvd (ne_of_gt hcard)
  letI : Fact r.Prime := ⟨hr⟩
  let S : Sylow r E := default
  have hSne : (S : Subgroup E) ≠ ⊥ := S.ne_bot_of_dvd_card hrdiv
  have hScore : (S : Subgroup E) ≤ pCore r E :=
    le_pCore S.isPGroup' (by infer_instance)
  have hcoreNe : pCore r E ≠ ⊥ := by
    intro hcore
    apply hSne
    rw [hcore] at hScore
    exact le_bot_iff.mp hScore
  let D : Subgroup G := (pCore r E).map E.subtype
  have hDE : D ≤ E := by
    dsimp [D]
    exact Subgroup.map_subtype_le _
  have hDne : D ≠ ⊥ := by
    dsimp [D]
    intro hD
    apply hcoreNe
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pCore r E) E.subtype_injective).mp hD
  have hDinv : ∀ a : G, a ∈ A → ∀ d : G, d ∈ D →
      a * d * a⁻¹ ∈ D := by
    dsimp [D]
    exact characteristic_map_subtype_invariant_under_normalizer
      E A (pCore r E) hE.le_normalizer
  have hED : E ≤ D := hE.2.2 D hDE hDne hDinv
  have hDEq : D = E := le_antisymm hDE hED
  refine ⟨r, hr, ?_⟩
  rw [← hDEq]
  exact pCore_isPGroup.map E.subtype

/-- A relative complement containing a prescribed coprime subgroup.  Only
the normal factor, rather than the whole ambient group, needs to be
solvable. -/
private theorem exists_right_complement_ge_of_coprime
    {G : Type u} [Group G] [Finite G]
    {N A : Subgroup G} [N.Normal] [IsSolvable N]
    (hNcop : (Nat.card N).Coprime N.index)
    (hNAcop : (Nat.card N).Coprime (Nat.card A)) :
    ∃ C : Subgroup G, N.IsComplement' C ∧ A ≤ C := by
  classical
  obtain ⟨C, hC⟩ := N.exists_right_complement'_of_coprime hNcop
  let D : Subgroup G := N ⊔ A
  let ND : Subgroup D := N.subgroupOf D
  let AD : Subgroup D := A.subgroupOf D
  let CD : Subgroup D := (C ⊓ D).subgroupOf D
  letI : ND.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : N.Normal) D
  let eND : ND ≃* N :=
    Subgroup.subgroupOfEquivOfLe (show N ≤ D from le_sup_left)
  letI : IsSolvable ND :=
    solvable_of_solvable_injective (f := eND.toMonoidHom) eND.injective

  have hNDA : ND.IsComplement' AD := by
    have hdis : Disjoint ND AD := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro z hz
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      have hzbot : ((z : D) : G) ∈ (⊥ : Subgroup G) := by
        rw [← disjoint_iff.mp
          (Subgroup.disjoint_of_coprime_natCard hNAcop)]
        exact hz
      exact Subgroup.mem_bot.mp hzbot
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
    rw [← Subgroup.normal_mul ND AD]
    have hsup : ND ⊔ AD = ⊤ := by
      change N.subgroupOf D ⊔ A.subgroupOf D = ⊤
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      exact Subgroup.subgroupOf_self D
    rw [hsup]
    rfl

  have hNDC : ND.IsComplement' CD := by
    have hdis : Disjoint ND CD := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro z hz
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      have hzbot : ((z : D) : G) ∈ (⊥ : Subgroup G) := by
        rw [← disjoint_iff.mp hC.disjoint]
        exact ⟨hz.1, hz.2.1⟩
      exact Subgroup.mem_bot.mp hzbot
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
    rw [← Subgroup.normal_mul ND CD]
    have hsup : ND ⊔ CD = ⊤ := by
      apply top_unique
      intro z _
      obtain ⟨nc, hnc, -⟩ := hC.existsUnique (z : G)
      have hcD : (nc.2 : G) ∈ D := by
        have hcEq : (nc.2 : G) = (nc.1 : G)⁻¹ * (z : G) := by
          rw [← hnc]
          simp
        rw [hcEq]
        exact D.mul_mem
          (D.inv_mem ((show N ≤ D from le_sup_left) nc.1.property))
          z.property
      let nD : ND :=
        ⟨⟨(nc.1 : G), (show N ≤ D from le_sup_left) nc.1.property⟩,
          nc.1.property⟩
      let cD : CD :=
        ⟨⟨(nc.2 : G), hcD⟩, ⟨nc.2.property, hcD⟩⟩
      have hmul : (nD : D) * (cD : D) ∈ ND ⊔ CD :=
        Subgroup.mul_mem_sup nD.property cD.property
      have hmulEq : (nD : D) * (cD : D) = z :=
        Subtype.ext hnc
      rwa [← hmulEq]
    rw [hsup]
    rfl

  have hNDcop : (Nat.card ND).Coprime ND.index := by
    rw [hNDA.symm.index_eq_card,
      natCard_subgroupOf_eq (show N ≤ D from le_sup_left),
      natCard_subgroupOf_eq (show A ≤ D from le_sup_right)]
    exact hNAcop
  obtain ⟨n, hn⟩ :=
    Subgroup.solvable_complement_conjugacy hNDcop hNDC hNDA
  let nG : G := ((n : ND) : D)
  let C' : Subgroup G := C.map (MulAut.conj nG).toMonoidHom
  have hC'comp : N.IsComplement' C' := by
    have hcardC' : Nat.card C' = Nat.card C :=
      Subgroup.card_map_of_injective (MulAut.conj nG).injective
    have hcard : Nat.card N * Nat.card C' = Nat.card G := by
      rw [hcardC']
      exact hC.card_mul
    have hNmap :
        N.map (MulAut.conj nG).toMonoidHom = N :=
      Subgroup.Normal.map_conj_eq N nG
    have hdisMap : Disjoint
        (N.map (MulAut.conj nG).toMonoidHom) C' :=
      Subgroup.disjoint_map (MulAut.conj nG).injective hC.disjoint
    rw [hNmap] at hdisMap
    exact Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdisMap
  refine ⟨C', hC'comp, ?_⟩
  intro a ha
  let aD : D := ⟨a, (show A ≤ D from le_sup_right) ha⟩
  have haAD : aD ∈ AD := ha
  rw [hn] at haAD
  obtain ⟨c, hc, hca⟩ := haAD
  refine ⟨((c : D) : G), hc.1, ?_⟩
  exact congrArg (fun x : D ↦ (x : G)) hca

/-- The complement-selection step used in the `p`-minimal-normal branch.
It records the two relative-index identities needed by the Hall induction. -/
private theorem exists_normalized_complement_of_coprime_action
    {G : Type u} [Group G] [Finite G]
    {A N L : Subgroup G} [N.Normal] [IsSolvable N]
    (hNL : N ≤ L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hcopLA : (Nat.card L).Coprime (Nat.card A))
    (hNcop : (Nat.card N).Coprime (N.relIndex L)) :
    ∃ H : Subgroup G,
      H ≤ L ∧
      Nat.card H = N.relIndex L ∧
      H.relIndex L = Nat.card N ∧
      A ≤ Subgroup.normalizer (H : Set G) := by
  classical
  let J : Subgroup G := A ⊔ L
  have hAJ : A ≤ J := le_sup_left
  have hLJ : L ≤ J := le_sup_right
  have hNJ : N ≤ J := hNL.trans hLJ
  let AJ : Subgroup J := A.subgroupOf J
  let LJ : Subgroup J := L.subgroupOf J
  let NJ : Subgroup J := N.subgroupOf J
  letI : LJ.Normal := by
    dsimp [LJ, J]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hAL
  letI : NJ.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : N.Normal) J
  let eNJ : NJ ≃* N := Subgroup.subgroupOfEquivOfLe hNJ
  letI : IsSolvable NJ :=
    solvable_of_solvable_injective (f := eNJ.toMonoidHom) eNJ.injective
  have hcardAJ : Nat.card AJ = Nat.card A := natCard_subgroupOf_eq hAJ
  have hcardLJ : Nat.card LJ = Nat.card L := natCard_subgroupOf_eq hLJ
  have hcardNJ : Nat.card NJ = Nat.card N := natCard_subgroupOf_eq hNJ
  have hcopLJAJ : (Nat.card LJ).Coprime (Nat.card AJ) := by
    simpa [hcardLJ, hcardAJ] using hcopLA
  have hdis : Disjoint LJ AJ :=
    Subgroup.disjoint_of_coprime_natCard hcopLJAJ
  have hsup : LJ ⊔ AJ = ⊤ := by
    change L.subgroupOf J ⊔ A.subgroupOf J = ⊤
    rw [← Subgroup.subgroupOf_sup hLJ hAJ]
    simp [J, sup_comm]
  have hcompLA : LJ.IsComplement' AJ := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
    rw [← Subgroup.normal_mul LJ AJ, hsup]
    rfl
  have hNJLJ : NJ ≤ LJ := by
    intro n hn
    exact hNL hn
  have hrelNJ : NJ.relIndex LJ = N.relIndex L := by
    exact Subgroup.relIndex_subgroupOf hLJ
  have hindexLJ : LJ.index = Nat.card AJ :=
    hcompLA.symm.index_eq_card
  have hindexNJ : NJ.index = N.relIndex L * Nat.card AJ := by
    rw [← NJ.relIndex_mul_index hNJLJ, hrelNJ, hindexLJ]
  have hNcopA : (Nat.card N).Coprime (Nat.card A) :=
    hcopLA.coprime_dvd_left (Subgroup.card_dvd_of_le hNL)
  have hNJcopA : (Nat.card NJ).Coprime (Nat.card AJ) := by
    simpa [hcardNJ, hcardAJ] using hNcopA
  have hNJcopIndex : (Nat.card NJ).Coprime NJ.index := by
    rw [hindexNJ, hcardNJ, hcardAJ]
    exact hNcop.mul_right hNcopA
  obtain ⟨D, hDcomp, hAJD⟩ :=
    exists_right_complement_ge_of_coprime
      (N := NJ) (A := AJ) hNJcopIndex hNJcopA
  let HJ : Subgroup J := D ⊓ LJ
  let NL : Subgroup LJ := NJ.subgroupOf LJ
  let HL : Subgroup LJ := HJ.subgroupOf LJ
  letI : NL.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : NJ.Normal) LJ
  have hlocalComp : NL.IsComplement' HL := by
    have hlocalDis : Disjoint NL HL := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro z hz
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      have hzbot : ((z : LJ) : J) ∈ (⊥ : Subgroup J) := by
        rw [← disjoint_iff.mp hDcomp.disjoint]
        exact ⟨hz.1, hz.2.1⟩
      exact Subgroup.mem_bot.mp hzbot
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hlocalDis
    rw [← Subgroup.normal_mul NL HL]
    have hlocalSup : NL ⊔ HL = ⊤ := by
      apply top_unique
      intro z _
      obtain ⟨nd, hnd, -⟩ := hDcomp.existsUnique ((z : LJ) : J)
      have hdLJ : (nd.2 : J) ∈ LJ := by
        have hdEq : (nd.2 : J) = (nd.1 : J)⁻¹ * (z : J) := by
          rw [← hnd]
          simp
        rw [hdEq]
        exact LJ.mul_mem (LJ.inv_mem (hNJLJ nd.1.property)) z.property
      let nL : NL :=
        ⟨⟨(nd.1 : J), hNJLJ nd.1.property⟩, nd.1.property⟩
      let hL : HL :=
        ⟨⟨(nd.2 : J), hdLJ⟩, ⟨nd.2.property, hdLJ⟩⟩
      have hmul : (nL : LJ) * (hL : LJ) ∈ NL ⊔ HL :=
        Subgroup.mul_mem_sup nL.property hL.property
      have hmulEq : (nL : LJ) * (hL : LJ) = z :=
        Subtype.ext hnd
      rwa [← hmulEq]
    rw [hlocalSup]
    rfl
  let H : Subgroup G := HJ.map J.subtype
  have hHL : H ≤ L := by
    calc
      H ≤ LJ.map J.subtype := Subgroup.map_mono inf_le_right
      _ = L := Subgroup.map_subgroupOf_eq_of_le hLJ
  have hcardHJ : Nat.card HJ = Nat.card H := by
    exact (Subgroup.card_map_of_injective J.subtype_injective).symm
  have hcardHL : Nat.card HL = Nat.card HJ :=
    natCard_subgroupOf_eq inf_le_right
  have hcardNL : Nat.card NL = Nat.card NJ :=
    natCard_subgroupOf_eq hNJLJ
  have hcardH : Nat.card H = N.relIndex L := by
    calc
      Nat.card H = Nat.card HJ := hcardHJ.symm
      _ = Nat.card HL := hcardHL.symm
      _ = NL.index := hlocalComp.symm.index_eq_card.symm
      _ = NJ.relIndex LJ := rfl
      _ = N.relIndex L := hrelNJ
  have hrelHL : H.relIndex L = HJ.relIndex LJ := by
    rw [show H = HJ.map J.subtype from rfl,
      ← Subgroup.map_subgroupOf_eq_of_le hLJ]
    exact Subgroup.relIndex_map_map_of_injective HJ LJ
      J.subtype_injective
  have hrelH : H.relIndex L = Nat.card N := by
    calc
      H.relIndex L = HJ.relIndex LJ := hrelHL
      _ = HL.index := rfl
      _ = Nat.card NL := hlocalComp.index_eq_card
      _ = Nat.card NJ := hcardNL
      _ = Nat.card N := hcardNJ
  have hAJnormHJ : AJ ≤ Subgroup.normalizer (HJ : Set J) := by
    apply (le_inf (hAJD.trans Subgroup.le_normalizer)
      (Subgroup.le_normalizer_of_normal :
        AJ ≤ Subgroup.normalizer (LJ : Set J))).trans
    exact Subgroup.inf_normalizer_le_normalizer_inf
  have hAnormH : A ≤ Subgroup.normalizer (H : Set G) := by
    have hmapped : AJ.map J.subtype ≤
        (Subgroup.normalizer (HJ : Set J)).map J.subtype :=
      Subgroup.map_mono hAJnormHJ
    rw [Subgroup.map_subgroupOf_eq_of_le hAJ] at hmapped
    exact hmapped.trans (Subgroup.le_normalizer_map J.subtype)
  exact ⟨H, hHL, hcardH, hrelH, hAnormH⟩

private theorem natCard_map_quotient_lt_of_ne_bot_of_le
    {G : Type u} [Group G] [Finite G]
    {N K : Subgroup G} [N.Normal]
    (hNK : N ≤ K) (hN : N ≠ ⊥) :
    Nat.card (K.map (QuotientGroup.mk' N)) < Nat.card K := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let f : K →* K.map q := q.subgroupMap K
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (K.map q) := Fintype.ofFinite (K.map q)
  have hsurj : Function.Surjective f := q.subgroupMap_surjective K
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    obtain ⟨n, hn⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN
    have hfn : f ⟨n, hNK n.property⟩ = f 1 := by
      apply Subtype.ext
      change q (n : G) = q 1
      rw [map_one]
      exact QuotientGroup.eq_one_iff (n : G) |>.mpr n.property
    have hnOne : (⟨n, hNK n.property⟩ : K) = 1 := hinj hfn
    apply hn
    apply Subtype.ext
    exact congrArg (fun z : K ↦ (z : G)) hnOne
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_surjective_not_injective f hsurj hnotinj

set_option maxHeartbeats 1000000 in
/-- Normal-kernel form of the invariant prime-complement theorem. -/
private theorem exists_primeComplement_normalized_of_coprime_of_isSolvable_normal
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A K : Subgroup G} [K.Normal]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hsol : IsSolvable K) :
    ∃ H : Subgroup G,
      H ≤ K ∧
      IsPrimeComplement p (H.subgroupOf K) ∧
      A ≤ Subgroup.normalizer (H : Set G) := by
  classical
  let motive : ℕ → Prop := fun n ↦
    ∀ {X : Type u} [Group X] [Finite X]
      {B L : Subgroup X} [L.Normal],
      Nat.card L = n →
      Nat.Coprime (Nat.card L) (Nat.card B) →
      IsSolvable L →
      ∃ H : Subgroup X,
        H ≤ L ∧
        IsPrimeComplement p (H.subgroupOf L) ∧
        B ≤ Subgroup.normalizer (H : Set X)
  suffices hmain : motive (Nat.card K) from hmain rfl hcop hsol
  exact Nat.strong_induction_on (p := motive) (Nat.card K) fun n ih ↦ by
    intro X _ _ B L _ hcard hcop' hsol'
    letI : IsSolvable L := hsol'
    have hp := (Fact.out : p.Prime)
    by_cases hpdiv : p ∣ Nat.card L
    · have hLne : L ≠ ⊥ := by
        intro hbot
        subst L
        exact hp.not_dvd_one (by simpa using hpdiv)
      obtain ⟨M, hML, hMmin⟩ :=
        exists_minimalNormalUnder_le hLne
          (show (⊤ : Subgroup X) ≤ Subgroup.normalizer (L : Set X) from
            Subgroup.le_normalizer_of_normal)
      have hMnormal : M.Normal := by
        rw [← Subgroup.normalizer_eq_top_iff]
        exact top_unique hMmin.le_normalizer
      letI : M.Normal := hMnormal
      let toL : M →* L := Subgroup.inclusion hML
      letI : IsSolvable M :=
        solvable_of_solvable_injective (f := toL) (by
          intro x y hxy
          apply Subtype.ext
          exact congrArg (fun z : L ↦ (z : X)) hxy)
      obtain ⟨r, hr, hMr⟩ :=
        exists_prime_isPGroup_of_minimalNormalUnder hMmin
      letI : Fact r.Prime := ⟨hr⟩
      let q : X →* X ⧸ M := QuotientGroup.mk' M
      let Bq : Subgroup (X ⧸ M) := B.map q
      let Lq : Subgroup (X ⧸ M) := L.map q
      letI : Lq.Normal :=
        Subgroup.Normal.map (inferInstance : L.Normal) q
          (QuotientGroup.mk'_surjective M)
      have hLqlt : Nat.card Lq < Nat.card L :=
        natCard_map_quotient_lt_of_ne_bot_of_le hML hMmin.ne_bot
      have hLqdiv : Nat.card Lq ∣ Nat.card L :=
        Subgroup.card_map_dvd L q
      have hBqdiv : Nat.card Bq ∣ Nat.card B :=
        Subgroup.card_map_dvd B q
      have hcopq : Nat.Coprime (Nat.card Lq) (Nat.card Bq) :=
        (hcop'.coprime_dvd_left hLqdiv).coprime_dvd_right hBqdiv
      have hsolq : IsSolvable Lq :=
        solvable_of_surjective (f := q.subgroupMap L)
          (q.subgroupMap_surjective L)
      obtain ⟨Q, hQLq, hQHall, hBqnormQ⟩ :=
        ih (Nat.card Lq) (by simpa [hcard] using hLqlt)
          (X := X ⧸ M) (B := Bq) (L := Lq) rfl hcopq hsolq
      let T : Subgroup X := Q.comap q
      have hMT : M ≤ T := by
        intro m hm
        change q m ∈ Q
        have hqm : q m = 1 :=
          (QuotientGroup.eq_one_iff (N := M) m).mpr hm
        rw [hqm]
        exact Q.one_mem
      have hTL : T ≤ L := by
        calc
          Q.comap q ≤ Lq.comap q := Subgroup.comap_mono hQLq
          _ = L := by
            dsimp [Lq]
            exact Subgroup.comap_map_eq_self (by
              simpa [q, QuotientGroup.ker_mk'] using hML)
      have hBnormT : B ≤ Subgroup.normalizer (T : Set X) := by
        calc
          B ≤ Bq.comap q := Subgroup.le_comap_map q B
          _ ≤ (Subgroup.normalizer (Q : Set (X ⧸ M))).comap q :=
            Subgroup.comap_mono hBqnormQ
          _ ≤ Subgroup.normalizer (Q.comap q : Set X) :=
            Subgroup.le_normalizer_comap q
      have hTmap : T.map q = Q := by
        dsimp [T]
        exact Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective M) Q
      have hMrelT : M.relIndex T = Nat.card Q := by
        have hrel := Subgroup.relIndex_ker T q
        rw [show q.ker = M by
          exact QuotientGroup.ker_mk' M, hTmap] at hrel
        exact hrel
      have hTcard : Nat.card T = Nat.card M * Nat.card Q := by
        calc
          Nat.card T = (M.subgroupOf T).index *
              Nat.card (M.subgroupOf T) :=
            (M.subgroupOf T).index_mul_card.symm
          _ = M.relIndex T * Nat.card M := by
            change M.relIndex T * Nat.card (M.subgroupOf T) =
              M.relIndex T * Nat.card M
            rw [natCard_subgroupOf_eq hMT]
          _ = Nat.card Q * Nat.card M := by rw [hMrelT]
          _ = Nat.card M * Nat.card Q := Nat.mul_comm _ _
      have hTrelL : T.relIndex L = Q.relIndex Lq := by
        exact Subgroup.relIndex_comap Q q L
      have hQcard : Nat.Coprime (Nat.card Q) p := by
        simpa [natCard_subgroupOf_eq hQLq] using hQHall.card_coprime
      obtain ⟨b, hQindex⟩ := hQHall.exists_index_eq_pow
      have hQrel : Q.relIndex Lq = p ^ b := hQindex
      obtain ⟨a, hMcard⟩ := hMr.exists_card_eq
      by_cases hrp : r = p
      · subst r
        have hMcopQ : Nat.Coprime (Nat.card M) (Nat.card Q) := by
          rw [hMcard]
          exact hQcard.symm.pow_left a
        have hMcopT : Nat.Coprime (Nat.card M) (M.relIndex T) := by
          rw [hMrelT]
          exact hMcopQ
        have hcopTB : Nat.Coprime (Nat.card T) (Nat.card B) :=
          hcop'.coprime_dvd_left (Subgroup.card_dvd_of_le hTL)
        obtain ⟨H, hHT, hHcard, hHrelT, hBnormH⟩ :=
          exists_normalized_complement_of_coprime_action
            hMT hBnormT hcopTB hMcopT
        have hHL : H ≤ L := hHT.trans hTL
        have hHcardQ : Nat.card H = Nat.card Q := by
          rw [hHcard, hMrelT]
        have hHrelL : H.relIndex L = p ^ (a + b) := by
          calc
            H.relIndex L = H.relIndex T * T.relIndex L :=
              (H.relIndex_mul_relIndex T L hHT hTL).symm
            _ = Nat.card M * T.relIndex L := by rw [hHrelT]
            _ = p ^ a * p ^ b := by rw [hMcard, hTrelL, hQrel]
            _ = p ^ (a + b) := (pow_add p a b).symm
        refine ⟨H, hHL, ?_, hBnormH⟩
        constructor
        · rw [natCard_subgroupOf_eq hHL, hHcardQ]
          exact hQcard
        · exact ⟨a + b, hHrelL⟩
      · have hMcopP : Nat.Coprime (Nat.card M) p := by
          rw [hMcard]
          exact ((Nat.coprime_primes hr hp).mpr hrp).pow_left a
        have hTcopP : Nat.Coprime (Nat.card T) p := by
          rw [hTcard]
          exact hMcopP.mul_left hQcard
        refine ⟨T, hTL, ?_, hBnormT⟩
        constructor
        · rw [natCard_subgroupOf_eq hTL]
          exact hTcopP
        · exact ⟨b, hTrelL.trans hQrel⟩
    · refine ⟨L, le_rfl, ?_, Subgroup.le_normalizer_of_normal⟩
      constructor
      · rw [natCard_subgroupOf_eq le_rfl]
        exact (hp.coprime_iff_not_dvd.mpr hpdiv).symm
      · refine ⟨0, ?_⟩
        rw [Subgroup.subgroupOf_self, Subgroup.index_top]
        simp

/-- Prime-complement specialization of MathComp's `coprime_Hall_exists`:
a coprime actor on a finite solvable subgroup fixes a Hall `p'`-subgroup. -/
theorem exists_primeComplement_normalized_of_coprime_of_isSolvable
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A K : Subgroup G}
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hsol : IsSolvable K) :
    ∃ H : Subgroup G,
      H ≤ K ∧
      IsPrimeComplement p (H.subgroupOf K) ∧
      A ≤ Subgroup.normalizer (H : Set G) := by
  classical
  let J : Subgroup G := A ⊔ K
  have hAJ : A ≤ J := le_sup_left
  have hKJ : K ≤ J := le_sup_right
  let AJ : Subgroup J := A.subgroupOf J
  let KJ : Subgroup J := K.subgroupOf J
  letI : KJ.Normal := by
    dsimp [KJ, J]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hAK
  have hcardAJ : Nat.card AJ = Nat.card A := natCard_subgroupOf_eq hAJ
  have hcardKJ : Nat.card KJ = Nat.card K := natCard_subgroupOf_eq hKJ
  have hcopJ : Nat.Coprime (Nat.card KJ) (Nat.card AJ) := by
    simpa [hcardKJ, hcardAJ] using hcop
  let eKJ : KJ ≃* K := Subgroup.subgroupOfEquivOfLe hKJ
  have hsolKJ : IsSolvable KJ := by
    letI : IsSolvable K := hsol
    exact solvable_of_solvable_injective
      (f := eKJ.toMonoidHom) eKJ.injective
  obtain ⟨HJ, hHJKJ, hHJHall, hAJnormHJ⟩ :=
    exists_primeComplement_normalized_of_coprime_of_isSolvable_normal
      (p := p) (A := AJ) (K := KJ) hcopJ hsolKJ
  let H : Subgroup G := HJ.map J.subtype
  have hHK : H ≤ K := by
    calc
      H ≤ KJ.map J.subtype := Subgroup.map_mono hHJKJ
      _ = K := Subgroup.map_subgroupOf_eq_of_le hKJ
  have hcardH : Nat.card H = Nat.card HJ :=
    Subgroup.card_map_of_injective J.subtype_injective
  have hcardSubHJ : Nat.card (HJ.subgroupOf KJ) = Nat.card HJ :=
    natCard_subgroupOf_eq hHJKJ
  have hcardSubH : Nat.card (H.subgroupOf K) = Nat.card H :=
    natCard_subgroupOf_eq hHK
  have hrelMap : H.relIndex K = HJ.relIndex KJ := by
    rw [show H = HJ.map J.subtype from rfl,
      ← Subgroup.map_subgroupOf_eq_of_le hKJ]
    exact Subgroup.relIndex_map_map_of_injective HJ KJ
      J.subtype_injective
  have hHHall : IsPrimeComplement p (H.subgroupOf K) := by
    constructor
    · rw [hcardSubH, hcardH, ← hcardSubHJ]
      exact hHJHall.card_coprime
    · obtain ⟨n, hn⟩ := hHJHall.exists_index_eq_pow
      exact ⟨n, hrelMap.trans hn⟩
  have hAnormH : A ≤ Subgroup.normalizer (H : Set G) := by
    have hmapped : AJ.map J.subtype ≤
        (Subgroup.normalizer (HJ : Set J)).map J.subtype :=
      Subgroup.map_mono hAJnormHJ
    rw [Subgroup.map_subgroupOf_eq_of_le hAJ] at hmapped
    exact hmapped.trans (Subgroup.le_normalizer_map J.subtype)
  exact ⟨H, hHK, hHHall, hAnormH⟩

end Submission.OddOrder.MathlibSupport
