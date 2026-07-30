import Submission.OddOrder.MathlibSupport.AmbientFitting
import Submission.OddOrder.MathlibSupport.SolvableHallContainment

/-!
# Conjugacy and ambient transport for Hall subgroups

This file supplies the Hall-conjugacy step used in `BGsection13.v`,
lines 621--628.  Hall subgroups of a finite solvable group are conjugate by
an explicit inner automorphism.  The ambient form then replaces a represented
Hall subgroup by a conjugate containing a prescribed `pi`-subgroup, while
recording the containments and Fitting-cardinality facts which survive the
replacement.
-/

namespace Submission.OddOrder.MathlibSupport

noncomputable section

universe u v

private theorem isHall_map_of_surjective
    {G : Type u} {K : Type v} [Group G] [Group K]
    [Finite G] [Finite K] {pi : Set ℕ} {H : Subgroup G}
    (f : G →* K) (hf : Function.Surjective f) (hH : IsHall pi H) :
    IsHall pi (H.map f) := by
  constructor
  · exact hH.isPiNumber_card.of_dvd (Subgroup.card_map_dvd H f)
  · apply hH.isPiNumber_index.of_dvd
    rw [← (H.map f).index_comap_of_surjective hf]
    exact Subgroup.index_dvd_of_le (Subgroup.le_comap_map f H)

private theorem isHall_map_mulEquiv
    {G : Type u} {K : Type v} [Group G] [Group K]
    [Finite G] [Finite K] {pi : Set ℕ} {H : Subgroup G}
    (e : G ≃* K) (hH : IsHall pi H) :
    IsHall pi (H.map e.toMonoidHom) := by
  constructor
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hH.isPiNumber_card
  · have hindex : (H.map e.toMonoidHom).index = H.index :=
      Subgroup.index_map_equiv H e
    exact hindex.symm ▸ hH.isPiNumber_index

private theorem map_conj_map_conj
    {G : Type u} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_one
    {G : Type u} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj 1).toMonoidHom = H := by
  convert H.map_id using 1
  ext x
  simp

private theorem map_conj_then_map
    {G : Type u} {K : Type v} [Group G] [Group K]
    (H : Subgroup G) (f : G →* K) (x : G) :
    (H.map (MulAut.conj x).toMonoidHom).map f =
      (H.map f).map (MulAut.conj (f x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

/-! ### Hall conjugacy in a finite solvable group -/

/-- Any two `pi`-Hall subgroups of a finite solvable group are conjugate.
The witness is an element of the group, so the resulting equivalence is an
explicit inner automorphism. -/
theorem exists_map_conj_eq_of_isHall_of_isSolvable
    {G : Type u} [Group G] [Finite G] {pi : Set ℕ}
    {H J : Subgroup G} (hsol : IsSolvable G)
    (hH : IsHall pi H) (hJ : IsHall pi J) :
    ∃ x : G, J = H.map (MulAut.conj x).toMonoidHom := by
  classical
  letI : IsSolvable G := hsol
  let motive : ℕ → Prop := fun n ↦
    ∀ {K : Type u} [Group K] [Finite K] [IsSolvable K],
      Nat.card K = n → ∀ {A B : Subgroup K},
        IsHall pi A → IsHall pi B →
          ∃ x : K, B = A.map (MulAut.conj x).toMonoidHom
  suffices hmain : motive (Nat.card G) from hmain rfl hH hJ
  exact Nat.strong_induction_on (p := motive) (Nat.card G) fun n ih ↦ by
    intro K _ _ _ hcard A B hA hB
    by_cases hcardOne : Nat.card K = 1
    · letI : Subsingleton K :=
        (Nat.card_eq_one_iff_unique.mp hcardOne).1
      have hBA : B = A := by
        ext x
        constructor
        · intro _
          simpa only [Subsingleton.elim x 1] using A.one_mem
        · intro _
          simpa only [Subsingleton.elim x 1] using B.one_mem
      refine ⟨1, ?_⟩
      rw [map_conj_one]
      exact hBA
    have hcardGt : 1 < Nat.card K :=
      (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne').lt_of_ne
        (Ne.symm hcardOne)
    letI : Nontrivial K :=
      Finite.one_lt_card_iff_nontrivial.mp hcardGt
    obtain ⟨N, hNmin, -⟩ :=
      exists_minimalNormal_le (K := (⊤ : Subgroup K))
        (by infer_instance) top_ne_bot
    letI : N.Normal := hNmin.normal
    obtain ⟨r, hr, hNr⟩ := hNmin.exists_prime_isPGroup
    letI : Fact r.Prime := ⟨hr⟩
    have hquotlt : Nat.card (K ⧸ N) < Nat.card K :=
      natCard_quotient_lt_of_ne_bot N hNmin.ne_bot
    let q : K →* K ⧸ N := QuotientGroup.mk' N
    have hAbar : IsHall pi (A.map q) :=
      isHall_map_of_surjective q (QuotientGroup.mk'_surjective N) hA
    have hBbar : IsHall pi (B.map q) :=
      isHall_map_of_surjective q (QuotientGroup.mk'_surjective N) hB
    obtain ⟨xbar, hxbar⟩ :=
      ih (Nat.card (K ⧸ N)) (by simpa [hcard] using hquotlt)
        (K := K ⧸ N) rfl hAbar hBbar
    obtain ⟨x, hx⟩ := (QuotientGroup.mk'_surjective N) xbar
    have hxq : q x = xbar := hx
    let Ax : Subgroup K :=
      A.map (MulAut.conj x).toMonoidHom
    have hAxHall : IsHall pi Ax :=
      isHall_map_mulEquiv (MulAut.conj x) hA
    have hAxmap : Ax.map q = B.map q := by
      dsimp only [Ax]
      rw [map_conj_then_map, hxq]
      exact hxbar.symm
    let L : Subgroup K := N ⊔ Ax
    have hNL : N ≤ L := le_sup_left
    have hAxL : Ax ≤ L := le_sup_right
    have hBL : B ≤ L := by
      intro b hb
      have hbcomap : b ∈ (B.map q).comap q :=
        (Subgroup.le_comap_map q B) hb
      rw [← hAxmap] at hbcomap
      dsimp only [q] at hbcomap
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hbcomap
      simpa only [L, sup_comm] using hbcomap
    suffices hconjAx :
        ∃ y : K, B = Ax.map (MulAut.conj y).toMonoidHom by
      obtain ⟨y, hy⟩ := hconjAx
      refine ⟨y * x, ?_⟩
      calc
        B = Ax.map (MulAut.conj y).toMonoidHom := hy
        _ = (A.map (MulAut.conj x).toMonoidHom).map
              (MulAut.conj y).toMonoidHom := by rfl
        _ = A.map (MulAut.conj (y * x)).toMonoidHom :=
          map_conj_map_conj A x y
    by_cases hrPi : r ∈ pi
    · have hNpi : IsPiNumber pi (Nat.card N) :=
        IsPGroup.isPiNumber_natCard hNr hrPi
      have hNAx : N ≤ Ax :=
        normal_isPiNumber_le_isHall hNmin.normal hNpi hAxHall
      have hNB : N ≤ B :=
        normal_isPiNumber_le_isHall hNmin.normal hNpi hB
      have hAxB : Ax = B := by
        calc
          Ax = (Ax.map q).comap q := by
            rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk',
              sup_eq_left.mpr hNAx]
          _ = (B.map q).comap q := by rw [hAxmap]
          _ = B := by
            rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk',
              sup_eq_left.mpr hNB]
      refine ⟨1, ?_⟩
      rw [map_conj_one]
      exact hAxB.symm
    · have hNcompl : IsPiNumber piᶜ (Nat.card N) :=
        IsPGroup.isPiNumber_natCard hNr
          (show r ∈ piᶜ from hrPi)
      have hNcopAx : (Nat.card N).Coprime (Nat.card Ax) :=
        (hAxHall.isPiNumber_card.coprime_compl hNcompl).symm
      have hNcopB : (Nat.card N).Coprime (Nat.card B) :=
        (hB.isPiNumber_card.coprime_compl hNcompl).symm
      let NL : Subgroup L := N.subgroupOf L
      let AxL : Subgroup L := Ax.subgroupOf L
      let BL : Subgroup L := B.subgroupOf L
      letI : NL.Normal := hNmin.normal.subgroupOf L
      have hdisAx : Disjoint NL AxL := by
        apply Subgroup.disjoint_of_coprime_natCard
        rw [natCard_subgroupOf_eq hNL,
          natCard_subgroupOf_eq hAxL]
        exact hNcopAx
      have hdisB : Disjoint NL BL := by
        apply Subgroup.disjoint_of_coprime_natCard
        rw [natCard_subgroupOf_eq hNL,
          natCard_subgroupOf_eq hBL]
        exact hNcopB
      have hsupAx : NL ⊔ AxL = ⊤ := by
        change N.subgroupOf L ⊔ Ax.subgroupOf L = ⊤
        rw [← Subgroup.subgroupOf_sup hNL hAxL]
        exact Subgroup.subgroupOf_self L
      have hNB : N ⊔ B = L := by
        calc
          N ⊔ B = B ⊔ N := sup_comm N B
          _ = (B.map q).comap q := by
            rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
          _ = (Ax.map q).comap q := by rw [hAxmap]
          _ = Ax ⊔ N := by
            rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
          _ = N ⊔ Ax := sup_comm Ax N
          _ = L := by rfl
      have hsupB : NL ⊔ BL = ⊤ := by
        change N.subgroupOf L ⊔ B.subgroupOf L = ⊤
        rw [← Subgroup.subgroupOf_sup hNL hBL, hNB]
        exact Subgroup.subgroupOf_self L
      have hcompAx : NL.IsComplement' AxL := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisAx
        rw [← Subgroup.normal_mul NL AxL, hsupAx]
        rfl
      have hcompB : NL.IsComplement' BL := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisB
        rw [← Subgroup.normal_mul NL BL, hsupB]
        rfl
      letI : IsSolvable L := inferInstance
      letI : IsSolvable NL := inferInstance
      have hNLcop : (Nat.card NL).Coprime NL.index := by
        rw [hcompAx.symm.index_eq_card,
          natCard_subgroupOf_eq hNL,
          natCard_subgroupOf_eq hAxL]
        exact hNcopAx
      obtain ⟨y, hy⟩ :=
        Subgroup.solvable_complement_conjugacy
          hNLcop hcompAx hcompB
      let yK : K := ((y : NL) : L)
      refine ⟨yK, ?_⟩
      calc
        B = BL.map L.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hBL).symm
        _ = (AxL.map (MulAut.conj (y : L)).toMonoidHom).map
              L.subtype := by rw [hy]
        _ = AxL.map
              (L.subtype.comp (MulAut.conj (y : L)).toMonoidHom) :=
          Subgroup.map_map AxL L.subtype
            (MulAut.conj (y : L)).toMonoidHom
        _ = AxL.map
              ((MulAut.conj yK).toMonoidHom.comp L.subtype) := by rfl
        _ = (AxL.map L.subtype).map
              (MulAut.conj yK).toMonoidHom := by
          rw [Subgroup.map_map]
        _ = Ax.map (MulAut.conj yK).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le hAxL]

/-! ### Fitting-cardinality transport -/

private theorem map_pCore_mulEquiv
    {G : Type u} {K : Type v} [Group G] [Group K]
    (p : ℕ) [Fact p.Prime] (e : G ≃* K) :
    (pCore p G).map e.toMonoidHom = pCore p K := by
  have hker : IsPGroup p e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    exact IsPGroup.of_bot
  exact map_pCore_eq_of_surjective_of_ker_isPGroup
    e.toMonoidHom e.surjective hker

private theorem map_fittingCore_mulEquiv
    {G : Type u} {K : Type v} [Group G] [Group K]
    (e : G ≃* K) :
    (fittingCore G).map e.toMonoidHom = fittingCore K := by
  rw [fittingCore, fittingCore, Subgroup.map_iSup]
  apply iSup_congr
  intro p
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  exact map_pCore_mulEquiv (p : ℕ) e

/-- The ambient Fitting subgroup has the same cardinality after transporting
the ambient subgroup across a multiplicative equivalence. -/
theorem natCard_fittingWithin_map_mulEquiv
    {G : Type u} {K : Type v} [Group G] [Group K]
    [Finite G] [Finite K] (H : Subgroup G) (e : G ≃* K) :
    Nat.card (fittingWithin (H.map e.toMonoidHom)) =
      Nat.card (fittingWithin H) := by
  let H' : Subgroup K := H.map e.toMonoidHom
  let eH : H ≃* H' := e.subgroupMap H
  have hfit :
      (fittingCore H).map eH.toMonoidHom = fittingCore H' :=
    map_fittingCore_mulEquiv eH
  change Nat.card ((fittingCore H').map H'.subtype) =
    Nat.card ((fittingCore H).map H.subtype)
  rw [Subgroup.card_map_of_injective H'.subtype_injective,
    Subgroup.card_map_of_injective H.subtype_injective,
    ← hfit, Subgroup.card_map_of_injective eH.injective]

/-- Inner conjugation preserves the cardinality of the ambient Fitting
subgroup. -/
theorem natCard_fittingWithin_map_conj
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) (x : G) :
    Nat.card
        (fittingWithin (H.map (MulAut.conj x).toMonoidHom)) =
      Nat.card (fittingWithin H) :=
  natCard_fittingWithin_map_mulEquiv H (MulAut.conj x)

/-- Divisibility by any natural number is unchanged when the ambient Fitting
subgroup is conjugated. -/
theorem dvd_natCard_fittingWithin_map_conj_iff
    {G : Type u} [Group G] [Finite G]
    (n : ℕ) (H : Subgroup G) (x : G) :
    n ∣ Nat.card
        (fittingWithin (H.map (MulAut.conj x).toMonoidHom)) ↔
      n ∣ Nat.card (fittingWithin H) := by
  rw [natCard_fittingWithin_map_conj]

/-! ### Ambient Hall replacement -/

/-- Replace an ambiently represented Hall subgroup of a finite solvable
subgroup by a conjugate containing a prescribed `pi`-subgroup.

The conjugator belongs to `K`.  Consequently the new subgroup remains in
`K`; its intrinsic subgroup is still Hall.  The result also records generic
containment transport and both equality and divisibility invariance for the
ambient Fitting subgroup. -/
theorem exists_ambient_isHall_map_conj_ge_of_isSolvable
    {G : Type u} [Group G] [Finite G]
    {K A H : Subgroup G} {pi : Set ℕ}
    (hAK : A ≤ K) (hHK : H ≤ K) (hsol : IsSolvable K)
    (hApi : IsPiNumber pi (Nat.card A))
    (hH : IsHall pi (H.subgroupOf K)) :
    ∃ x : K,
      let H' : Subgroup G :=
        H.map (MulAut.conj (x : G)).toMonoidHom
      A ≤ H' ∧ H' ≤ K ∧
        IsHall pi (H'.subgroupOf K) ∧
        Nat.card (fittingWithin H') =
          Nat.card (fittingWithin H) ∧
        (∀ n : ℕ,
          n ∣ Nat.card (fittingWithin H') ↔
            n ∣ Nat.card (fittingWithin H)) ∧
        ∀ X : Subgroup G, X ≤ H →
          X.map (MulAut.conj (x : G)).toMonoidHom ≤ H' := by
  have hApiK : IsPiNumber pi (Nat.card (A.subgroupOf K)) := by
    rw [natCard_subgroupOf_eq hAK]
    exact hApi
  obtain ⟨J, hAJ, hJ⟩ :=
    exists_isHall_ge_of_isSolvable hsol pi hApiK
  obtain ⟨x, hx⟩ :=
    exists_map_conj_eq_of_isHall_of_isSolvable hsol hH hJ
  let H' : Subgroup G :=
    H.map (MulAut.conj (x : G)).toMonoidHom
  have hJmap : J.map K.subtype = H' := by
    calc
      J.map K.subtype =
          ((H.subgroupOf K).map
            (MulAut.conj x).toMonoidHom).map K.subtype := by
        rw [hx]
      _ = (H.subgroupOf K).map
          (K.subtype.comp (MulAut.conj x).toMonoidHom) :=
        Subgroup.map_map (H.subgroupOf K) K.subtype
          (MulAut.conj x).toMonoidHom
      _ = (H.subgroupOf K).map
          ((MulAut.conj (x : G)).toMonoidHom.comp K.subtype) := by
        rfl
      _ = ((H.subgroupOf K).map K.subtype).map
          (MulAut.conj (x : G)).toMonoidHom := by
        rw [Subgroup.map_map]
      _ = H' := by
        rw [Subgroup.map_subgroupOf_eq_of_le hHK]
  have hAH' : A ≤ H' := by
    intro a ha
    let aK : K := ⟨a, hAK ha⟩
    have haSub : aK ∈ A.subgroupOf K := ha
    have haJ : aK ∈ J := hAJ haSub
    have haMap : a ∈ J.map K.subtype :=
      Subgroup.mem_map_of_mem K.subtype haJ
    rw [hJmap] at haMap
    exact haMap
  have hH'K : H' ≤ K := by
    rw [← hJmap]
    exact Subgroup.map_subtype_le J
  have hH'sub : H'.subgroupOf K = J := by
    change H'.comap K.subtype = J
    rw [← hJmap]
    exact Subgroup.comap_map_eq_self_of_injective
      K.subtype_injective J
  have hH'Hall : IsHall pi (H'.subgroupOf K) := by
    rw [hH'sub]
    exact hJ
  have hfit : Nat.card (fittingWithin H') =
      Nat.card (fittingWithin H) :=
    natCard_fittingWithin_map_conj H (x : G)
  refine ⟨x, hAH', hH'K, hH'Hall, hfit, ?_, ?_⟩
  · intro n
    rw [hfit]
  · intro X hXH
    exact Subgroup.map_mono hXH

end

end Submission.OddOrder.MathlibSupport
