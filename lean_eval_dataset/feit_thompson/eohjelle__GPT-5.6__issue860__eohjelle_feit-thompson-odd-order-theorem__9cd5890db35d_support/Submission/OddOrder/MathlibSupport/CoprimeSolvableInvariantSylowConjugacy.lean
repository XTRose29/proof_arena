import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension

/-!
# Conjugacy of invariant Sylow subgroups under a coprime solvable action

This file supplies the `p`-local form of MathComp's `coprime_Hall_trans`.
If `A` acts coprimely on a finite solvable subgroup `L`, any two Sylow
`p`-subgroups of `L` normalized by `A` are conjugate by an element of
`L ∩ C_G(A)`.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G]

/-- In a coprime normalized product, an element of the normal factor which
normalizes the complement actually centralizes it.  This is the internal
subgroup form of MathComp's `coprime_norm_cent`. -/
theorem mem_centralizer_of_mem_of_mem_normalizer_of_coprime
    {A L : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hcop : (Nat.card L).Coprime (Nat.card A))
    {x : G} (hxL : x ∈ L)
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) :
    x ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hcommA : ⁅a, x⁆ ∈ A := by
    rw [commutatorElement_def]
    rw [show a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) by group]
    exact A.mul_mem ha
      ((Subgroup.mem_normalizer_iff.mp hxA a⁻¹).mp (A.inv_mem ha))
  have hcommL : ⁅a, x⁆ ∈ L := by
    rw [commutatorElement_def]
    exact L.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hAL ha) x).mp hxL)
      (L.inv_mem hxL)
  have hdisjoint : Disjoint L A :=
    Subgroup.disjoint_of_coprime_natCard hcop
  have hcommOne : ⁅a, x⁆ = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp hdisjoint]
    exact ⟨hcommL, hcommA⟩
  exact commutatorElement_eq_one_iff_mul_comm.mp hcommOne

/-- Internal `MulAut.conj`-oriented form of the invariant Sylow conjugacy
argument.  The source-shaped inverse-conjugation interface is exposed below. -/
theorem exists_mem_inf_centralizer_mulAutConj_sylow_of_coprime_of_isSolvable
    {p : ℕ} [Fact p.Prime] {A L : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hcop : (Nat.card L).Coprime (Nat.card A))
    (hsol : IsSolvable L)
    (P₁ P₂ : Sylow p L)
    (hAP₁ : A ≤ Subgroup.normalizer
      (((P₁ : Subgroup L).map L.subtype : Subgroup G) : Set G))
    (hAP₂ : A ≤ Subgroup.normalizer
      (((P₂ : Subgroup L).map L.subtype : Subgroup G) : Set G)) :
    ∃ x : G,
      x ∈ L ⊓ Subgroup.centralizer (A : Set G) ∧
        (P₁ : Subgroup L).map L.subtype =
          ((P₂ : Subgroup L).map L.subtype).map
            (MulAut.conj x).toMonoidHom := by
  classical
  open scoped Pointwise in
    let J : Subgroup G := A ⊔ L
    let AJ : Subgroup J := A.subgroupOf J
    let LJ : Subgroup J := L.subgroupOf J
    let Q₁ : Subgroup G := (P₁ : Subgroup L).map L.subtype
    let Q₂ : Subgroup G := (P₂ : Subgroup L).map L.subtype
    have hAJJ : A ≤ J := le_sup_left
    have hLJJ : L ≤ J := le_sup_right
    have hQ₁L : Q₁ ≤ L := by
      dsimp [Q₁]
      exact Subgroup.map_subtype_le (P₁ : Subgroup L)
    have hQ₂L : Q₂ ≤ L := by
      dsimp [Q₂]
      exact Subgroup.map_subtype_le (P₂ : Subgroup L)
    have hQ₁J : Q₁ ≤ J := hQ₁L.trans hLJJ
    have hQ₂J : Q₂ ≤ J := hQ₂L.trans hLJJ
    let H₁ : Subgroup J := Q₁.subgroupOf J
    let H₂ : Subgroup J := Q₂.subgroupOf J
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
    have hAJnormH₁ : AJ ≤ Subgroup.normalizer (H₁ : Set J) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hQ₁J]
      intro a ha
      exact hAP₁ ha
    have hAJnormH₂ : AJ ≤ Subgroup.normalizer (H₂ : Set J) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hQ₂J]
      intro a ha
      exact hAP₂ ha
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq L P₂ P₁
    let xJ : J := ⟨(x : G), hLJJ x.property⟩
    have hxJL : xJ ∈ LJ := x.property
    have hxSub : (P₁ : Subgroup L) =
        (P₂ : Subgroup L).map (MulAut.conj x).toMonoidHom := by
      rw [← hx]
      rfl
    have hQconj : Q₁ =
        Q₂.map (MulAut.conj (x : G)).toMonoidHom := by
      calc
        Q₁ = ((P₂ : Subgroup L).map
            (MulAut.conj x).toMonoidHom).map L.subtype := by
          rw [← hxSub]
        _ = Q₂.map (MulAut.conj (x : G)).toMonoidHom := by
          dsimp [Q₂]
          rw [Subgroup.map_map, Subgroup.map_map]
          rfl
    have hHconj : H₁ =
        H₂.map (MulAut.conj xJ).toMonoidHom := by
      apply Subgroup.map_injective J.subtype_injective
      calc
        H₁.map J.subtype = Q₁ :=
          Subgroup.map_subgroupOf_eq_of_le hQ₁J
        _ = Q₂.map (MulAut.conj (x : G)).toMonoidHom := hQconj
        _ = (H₂.map J.subtype).map
            (MulAut.conj (x : G)).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le hQ₂J]
        _ = (H₂.map (MulAut.conj xJ).toMonoidHom).map
            J.subtype := by
          rw [Subgroup.map_map, Subgroup.map_map]
          rfl
    let T₁ : Subgroup LJ :=
      (P₁ : Subgroup L).map eJL.symm.toMonoidHom
    have hT₁index : T₁.index = (P₁ : Subgroup L).index := by
      dsimp [T₁]
      exact Subgroup.index_map_equiv (P₁ : Subgroup L) eJL.symm
    have hT₁p : IsPGroup p T₁ := by
      dsimp [T₁]
      exact P₁.isPGroup'.map eJL.symm.toMonoidHom
    let P₁J : Sylow p LJ := hT₁p.toSylow (by
      rw [hT₁index]
      exact P₁.not_dvd_index)
    have hP₁Jmap : (P₁J : Subgroup LJ).map LJ.subtype = H₁ := by
      apply Subgroup.map_injective J.subtype_injective
      calc
        ((P₁J : Subgroup LJ).map LJ.subtype).map J.subtype =
            T₁.map (J.subtype.comp LJ.subtype) := by
          change (T₁.map LJ.subtype).map J.subtype = _
          rw [Subgroup.map_map]
        _ = (P₁ : Subgroup L).map L.subtype := by
          dsimp [T₁, eJL]
          rw [Subgroup.map_map]
          rfl
        _ = Q₁ := rfl
        _ = H₁.map J.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hQ₁J).symm
    have hfrattini : Subgroup.normalizer (H₁ : Set J) ⊔ LJ = ⊤ := by
      rw [← hP₁Jmap]
      exact P₁J.normalizer_sup_eq_top
    let N : Subgroup J := Subgroup.normalizer (H₁ : Set J)
    let D : Subgroup N := LJ.comap N.subtype
    letI : D.Normal := by
      dsimp [D]
      infer_instance
    have hcopLJindex : (Nat.card LJ).Coprime LJ.index := by
      rw [hcompAJ.symm.index_eq_card]
      exact hcopLJAJ
    have hindexD : D.index = LJ.index := by
      dsimp [D, N]
      rw [← LJ.relIndex_top_right, ← hfrattini]
      exact (Subgroup.relIndex_sup_right
        (Subgroup.normalizer (H₁ : Set J)) LJ).symm
    have hcardDdvd : Nat.card D ∣ Nat.card LJ :=
      Subgroup.card_comap_dvd_of_injective LJ N.subtype
        N.subtype_injective
    have hcopDindex : (Nat.card D).Coprime D.index := by
      rw [hindexD]
      exact hcopLJindex.coprime_dvd_left hcardDdvd
    have hAJN : AJ ≤ N := by
      dsimp [N]
      exact hAJnormH₁
    let B : Subgroup J :=
      AJ.map (MulAut.conj xJ).toMonoidHom
    have hBN : B ≤ N := by
      have hmapped : AJ.map (MulAut.conj xJ).toMonoidHom ≤
          (Subgroup.normalizer (H₂ : Set J)).map
            (MulAut.conj xJ).toMonoidHom :=
        Subgroup.map_mono hAJnormH₂
      rw [Subgroup.map_equiv_normalizer_eq H₂ (MulAut.conj xJ),
        ← hHconj] at hmapped
      simpa [B, N] using hmapped
    let AJN : Subgroup N := AJ.subgroupOf N
    let BN : Subgroup N := B.subgroupOf N
    have hcardAJN : Nat.card AJN = Nat.card AJ :=
      natCard_subgroupOf_eq hAJN
    have hcardB : Nat.card B = Nat.card AJ := by
      dsimp [B]
      exact Subgroup.card_map_of_injective (MulAut.conj xJ).injective
    have hcardBN : Nat.card BN = Nat.card AJ := by
      rw [natCard_subgroupOf_eq hBN]
      exact hcardB
    have hindexDAJ : D.index = Nat.card AJ :=
      hindexD.trans hcompAJ.symm.index_eq_card
    have hcompAJN : D.IsComplement' AJN := by
      apply Subgroup.isComplement'_of_coprime
      · rw [hcardAJN, ← hindexDAJ]
        exact D.card_mul_index
      · rw [hcardAJN, ← hindexDAJ]
        exact hcopDindex
    have hcompBN : D.IsComplement' BN := by
      apply Subgroup.isComplement'_of_coprime
      · rw [hcardBN, ← hindexDAJ]
        exact D.card_mul_index
      · rw [hcardBN, ← hindexDAJ]
        exact hcopDindex
    let toLJ : D →* LJ :=
      { toFun := fun d ↦ ⟨((d : N) : J), d.property⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }
    letI : IsSolvable D :=
      solvable_of_solvable_injective (f := toLJ) (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : LJ ↦ (z : J)) hab)
    obtain ⟨y, hy⟩ :=
      Subgroup.solvable_complement_conjugacy
        hcopDindex hcompAJN hcompBN
    let yJ : J := (y : N)
    have hyLJ : yJ ∈ LJ := y.property
    have hyN : yJ ∈ N := (y : N).property
    have hBy : B = AJ.map (MulAut.conj yJ).toMonoidHom := by
      calc
        B = BN.map N.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hBN).symm
        _ = (AJN.map (MulAut.conj (y : N)).toMonoidHom).map
            N.subtype := by rw [hy]
        _ = AJN.map
            (N.subtype.comp (MulAut.conj (y : N)).toMonoidHom) :=
          Subgroup.map_map AJN N.subtype
            (MulAut.conj (y : N)).toMonoidHom
        _ = AJN.map
            ((MulAut.conj yJ).toMonoidHom.comp N.subtype) := rfl
        _ = (AJN.map N.subtype).map
            (MulAut.conj yJ).toMonoidHom := by
          rw [Subgroup.map_map]
        _ = AJ.map (MulAut.conj yJ).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le hAJN]
    let cJ : J := yJ⁻¹ * xJ
    have hcLJ : cJ ∈ LJ := LJ.mul_mem (LJ.inv_mem hyLJ) hxJL
    have hmapC : AJ.map (MulAut.conj cJ).toMonoidHom ≤ AJ := by
      rintro z ⟨a, ha, rfl⟩
      have hxa : (MulAut.conj xJ).toMonoidHom a ∈ B := by
        exact Subgroup.mem_map_of_mem
          (MulAut.conj xJ).toMonoidHom ha
      rw [hBy] at hxa
      rcases hxa with ⟨a', ha', heq⟩
      have heq' : yJ⁻¹ * (xJ * a * xJ⁻¹) * yJ = a' := by
        change yJ * a' * yJ⁻¹ = xJ * a * xJ⁻¹ at heq
        rw [← heq]
        group
      change cJ * a * cJ⁻¹ ∈ AJ
      rw [show cJ * a * cJ⁻¹ = a' by
        simpa [cJ, mul_assoc] using heq']
      exact ha'
    have hcNormAJ : cJ ∈ Subgroup.normalizer (AJ : Set J) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply Subgroup.eq_of_le_of_card_ge hmapC
      exact (Subgroup.card_map_of_injective
        (MulAut.conj cJ).injective).ge
    have hAJnormLJ : AJ ≤ Subgroup.normalizer (LJ : Set J) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : LJ.Normal)]
      exact le_top
    have hcCentAJ : cJ ∈ Subgroup.centralizer (AJ : Set J) :=
      mem_centralizer_of_mem_of_mem_normalizer_of_coprime
        hAJnormLJ hcopLJAJ hcLJ hcNormAJ
    have hyNormH₁ : yJ ∈ Subgroup.normalizer (H₁ : Set J) := by
      simpa [N] using hyN
    have hyInvNormH₁ : yJ⁻¹ ∈
        Subgroup.normalizer (H₁ : Set J) :=
      (Subgroup.normalizer (H₁ : Set J)).inv_mem hyNormH₁
    have hcompConj : (MulAut.conj cJ).toMonoidHom =
        (MulAut.conj yJ⁻¹).toMonoidHom.comp
          (MulAut.conj xJ).toMonoidHom := by
      apply MonoidHom.ext
      intro z
      apply Subtype.ext
      dsimp [cJ]
      group
    have hHc : H₁ = H₂.map (MulAut.conj cJ).toMonoidHom := by
      symm
      calc
        H₂.map (MulAut.conj cJ).toMonoidHom =
            H₂.map ((MulAut.conj yJ⁻¹).toMonoidHom.comp
              (MulAut.conj xJ).toMonoidHom) := by rw [hcompConj]
        _ = (H₂.map (MulAut.conj xJ).toMonoidHom).map
            (MulAut.conj yJ⁻¹).toMonoidHom := by
          rw [Subgroup.map_map]
        _ = H₁.map (MulAut.conj yJ⁻¹).toMonoidHom := by
          rw [← hHconj]
        _ = H₁ :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp hyInvNormH₁
    let cG : G := (cJ : J)
    have hcL : cG ∈ L := hcLJ
    have hcCentA : cG ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      let aJ : J := ⟨a, hAJJ ha⟩
      have haAJ : aJ ∈ AJ := ha
      have hcomm :=
        Subgroup.mem_centralizer_iff.mp hcCentAJ aJ haAJ
      exact congrArg (fun z : J ↦ (z : G)) hcomm
    refine ⟨cG, ⟨hcL, hcCentA⟩, ?_⟩
    change Q₁ = Q₂.map (MulAut.conj cG).toMonoidHom
    calc
      Q₁ = H₁.map J.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQ₁J).symm
      _ = (H₂.map (MulAut.conj cJ).toMonoidHom).map
          J.subtype := by rw [hHc]
      _ = (H₂.map J.subtype).map
          (MulAut.conj cG).toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      _ = Q₂.map (MulAut.conj cG).toMonoidHom := by
        rw [Subgroup.map_subgroupOf_eq_of_le hQ₂J]

/-- `p`-local form of MathComp's `coprime_Hall_trans`: two invariant Sylow
subgroups for a coprime action on a solvable subgroup are conjugate by an
element of the acted-on subgroup which centralizes the acting subgroup.

MathComp's `H :^ x` is conjugation by `x⁻¹`, hence the inverse in the
conclusion. -/
theorem exists_mem_inf_centralizer_conj_sylow_of_coprime_of_isSolvable
    {p : ℕ} [Fact p.Prime] {A L : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hcop : (Nat.card L).Coprime (Nat.card A))
    (hsol : IsSolvable L)
    (P₁ P₂ : Sylow p L)
    (hAP₁ : A ≤ Subgroup.normalizer
      (((P₁ : Subgroup L).map L.subtype : Subgroup G) : Set G))
    (hAP₂ : A ≤ Subgroup.normalizer
      (((P₂ : Subgroup L).map L.subtype : Subgroup G) : Set G)) :
    ∃ x : G,
      x ∈ L ⊓ Subgroup.centralizer (A : Set G) ∧
        (P₁ : Subgroup L).map L.subtype =
          ((P₂ : Subgroup L).map L.subtype).map
            (MulAut.conj x⁻¹).toMonoidHom := by
  obtain ⟨y, hy, hconj⟩ :=
    exists_mem_inf_centralizer_mulAutConj_sylow_of_coprime_of_isSolvable
      hAL hcop hsol P₁ P₂ hAP₁ hAP₂
  refine ⟨y⁻¹, ⟨L.inv_mem hy.1,
    (Subgroup.centralizer (A : Set G)).inv_mem hy.2⟩, ?_⟩
  simpa using hconj

end Submission.OddOrder.MathlibSupport
