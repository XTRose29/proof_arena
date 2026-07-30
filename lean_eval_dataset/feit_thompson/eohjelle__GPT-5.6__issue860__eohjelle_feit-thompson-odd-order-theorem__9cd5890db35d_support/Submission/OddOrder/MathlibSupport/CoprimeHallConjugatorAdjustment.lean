import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.Hall
import Submission.OddOrder.MathlibSupport.SolvableComplementConjugacy
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
Adjusting a conjugator by coprime Hall-complement conjugacy.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped Pointwise commutatorElement

universe u

/-- If two `P`-invariant subgroups are conjugate by an element of the
coprime normal factor `K`, then the conjugator can be chosen in `C_K(P)`,
provided the relevant join-normalizer intersection is solvable. -/
theorem exists_centralizerWithin_conjugator_of_coprime_join
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {K P Q₀ Q₂ : Subgroup G}
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hKpi' : IsPiNumber piᶜ (Nat.card K))
    (hPpi : IsPiNumber pi (Nat.card P))
    (hPQ₀ : P ≤ Subgroup.normalizer (Q₀ : Set G))
    (hPQ₂ : P ≤ Subgroup.normalizer (Q₂ : Set G))
    (hsol : IsSolvable
      (((K ⊔ P) ⊓ Subgroup.normalizer (Q₂ : Set G) : Subgroup G)))
    {k : G} (hk : k ∈ K)
    (hQ₂ : Q₂ = Q₀.map (MulAut.conj k⁻¹).toMonoidHom) :
    ∃ x : G, x ∈ centralizerWithin K P ∧
      Q₂ = Q₀.map (MulAut.conj x⁻¹).toMonoidHom := by
  classical
  have hcopKP : (Nat.card K).Coprime (Nat.card P) := by
    apply Nat.coprime_of_dvd
    intro q hq hqK hqP
    exact (hKpi' hq hqK) (hPpi hq hqP)

  let Pk : Subgroup G :=
    P.map (MulAut.conj k⁻¹).toMonoidHom
  have hPkJoin : Pk ≤ K ⊔ P := by
    rintro z ⟨p, hp, rfl⟩
    exact (K ⊔ P).mul_mem
      ((K ⊔ P).mul_mem
        ((K ⊔ P).inv_mem ((show K ≤ K ⊔ P from le_sup_left) hk))
        ((show P ≤ K ⊔ P from le_sup_right) hp))
      (by simpa using ((show K ≤ K ⊔ P from le_sup_left) hk))
  have hPkNorm : Pk ≤ Subgroup.normalizer (Q₂ : Set G) := by
    have hmapped :
        P.map (MulAut.conj k⁻¹).toMonoidHom ≤
          (Subgroup.normalizer (Q₀ : Set G)).map
            (MulAut.conj k⁻¹).toMonoidHom :=
      Subgroup.map_mono hPQ₀
    rw [Subgroup.map_equiv_normalizer_eq Q₀ (MulAut.conj k⁻¹),
      ← hQ₂] at hmapped
    exact hmapped

  let L : Subgroup G :=
    (K ⊔ P) ⊓ Subgroup.normalizer (Q₂ : Set G)
  have hPL : P ≤ L := fun _ hp ↦
    ⟨(show P ≤ K ⊔ P from le_sup_right) hp, hPQ₂ hp⟩
  have hPkL : Pk ≤ L := fun _ hp ↦ ⟨hPkJoin hp, hPkNorm hp⟩
  have hLnormK : L ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    exact (sup_le Subgroup.le_normalizer hPK) hx.1

  let KL : Subgroup L := K.subgroupOf L
  let PL : Subgroup L := P.subgroupOf L
  let PkL : Subgroup L := Pk.subgroupOf L
  letI : KL.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLnormK
  letI : IsSolvable L := hsol

  have hKPdis : Disjoint K P :=
    Subgroup.disjoint_of_coprime_natCard hcopKP
  have hKLPLdis : Disjoint KL PL := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hzbot : ((z : L) : G) ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hKPdis]
      exact ⟨hz.1, hz.2⟩
    exact Subgroup.mem_bot.mp hzbot
  have hKLPLsup : KL ⊔ PL = ⊤ := by
    apply top_unique
    intro z _
    have hzprod : ((z : L) : G) ∈ (K : Set G) * (P : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K P hPK]
      exact z.property.1
    rcases hzprod with ⟨k', hk', p', hp', hkp⟩
    have hk'Norm : k' ∈ Subgroup.normalizer (Q₂ : Set G) := by
      have hk'eq : k' = ((z : L) : G) * p'⁻¹ := by
        rw [← hkp]
        simp
      rw [hk'eq]
      exact (Subgroup.normalizer (Q₂ : Set G)).mul_mem z.property.2
        ((Subgroup.normalizer (Q₂ : Set G)).inv_mem (hPQ₂ hp'))
    have hk'L : k' ∈ L :=
      ⟨(show K ≤ K ⊔ P from le_sup_left) hk', hk'Norm⟩
    have hp'L : p' ∈ L :=
      ⟨(show P ≤ K ⊔ P from le_sup_right) hp', hPQ₂ hp'⟩
    let kl : KL := ⟨⟨k', hk'L⟩, hk'⟩
    let pl : PL := ⟨⟨p', hp'L⟩, hp'⟩
    have hmul : (kl : L) * (pl : L) ∈ KL ⊔ PL :=
      Subgroup.mul_mem_sup kl.property pl.property
    have heqL : (kl : L) * (pl : L) = z :=
      Subtype.ext hkp
    rw [← heqL]
    exact hmul
  have hKLPL : KL.IsComplement' PL := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKLPLdis
    rw [← Subgroup.normal_mul KL PL, hKLPLsup]
    rfl

  have hcardPL : Nat.card PL = Nat.card P :=
    natCard_subgroupOf_eq hPL
  have hcardPkL : Nat.card PkL = Nat.card P := by
    calc
      Nat.card PkL = Nat.card Pk := natCard_subgroupOf_eq hPkL
      _ = Nat.card P := by
        dsimp [Pk]
        exact Subgroup.card_map_of_injective
          (MulAut.conj k⁻¹).injective
  have hKLmap : KL.map L.subtype ≤ K := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz
  have hcardKLdvd : Nat.card KL ∣ Nat.card K := by
    have hcardMap : Nat.card (KL.map L.subtype) = Nat.card KL :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [← hcardMap]
    exact Subgroup.card_dvd_of_le hKLmap
  have hKLPkL : KL.IsComplement' PkL := by
    apply Subgroup.isComplement'_of_coprime
    · rw [hcardPkL, ← hcardPL]
      exact hKLPL.card_mul
    · rw [hcardPkL]
      exact hcopKP.coprime_dvd_left hcardKLdvd
  have hcopKL : (Nat.card KL).Coprime KL.index := by
    rw [hKLPL.symm.index_eq_card, hcardPL]
    exact hcopKP.coprime_dvd_left hcardKLdvd

  obtain ⟨w, hw⟩ :=
    Subgroup.solvable_complement_conjugacy hcopKL hKLPL hKLPkL
  let wG : G := ((w : KL) : L)
  have hwK : wG ∈ K := w.property
  have hwNorm : wG ∈ Subgroup.normalizer (Q₂ : Set G) :=
    ((w : KL) : L).property.2
  have hPkEq :
      Pk = P.map (MulAut.conj wG).toMonoidHom := by
    calc
      Pk = PkL.map L.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hPkL).symm
      _ = (PL.map (MulAut.conj (w : L)).toMonoidHom).map
            L.subtype := by rw [hw]
      _ = PL.map
            (L.subtype.comp (MulAut.conj (w : L)).toMonoidHom) :=
        Subgroup.map_map PL L.subtype
          (MulAut.conj (w : L)).toMonoidHom
      _ = PL.map
            ((MulAut.conj wG).toMonoidHom.comp L.subtype) := rfl
      _ = (PL.map L.subtype).map
            (MulAut.conj wG).toMonoidHom := by
        rw [Subgroup.map_map]
      _ = P.map (MulAut.conj wG).toMonoidHom := by
        rw [Subgroup.map_subgroupOf_eq_of_le hPL]

  let x : G := k * wG
  have hxMapLe : P.map (MulAut.conj x).toMonoidHom ≤ P := by
    rintro z ⟨p, hp, rfl⟩
    have hwp : (MulAut.conj wG).toMonoidHom p ∈
        P.map (MulAut.conj wG).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj wG).toMonoidHom hp
    rw [← hPkEq] at hwp
    rcases hwp with ⟨p', hp', heq⟩
    have heq' : (MulAut.conj x).toMonoidHom p = p' := by
      have hconj := congrArg (fun z : G ↦ k * z * k⁻¹) heq
      simpa [Pk, x, MulAut.conj_apply, mul_assoc] using hconj.symm
    rw [heq']
    exact hp'
  have hxK : x ∈ K := K.mul_mem hk hwK
  have hxCent : x ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
    intro p hp
    have hcommK : ⁅x, p⁆ ∈ K :=
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hPK)
        (Subgroup.commutator_mem_commutator hxK hp)
    have hconjP : (MulAut.conj x).toMonoidHom p ∈ P :=
      hxMapLe (Subgroup.mem_map_of_mem
        (MulAut.conj x).toMonoidHom hp)
    have hcommP : ⁅x, p⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem hconjP (P.inv_mem hp)
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp hKPdis]
    exact ⟨hcommK, hcommP⟩

  have hwMap :
      Q₂.map (MulAut.conj wG⁻¹).toMonoidHom = Q₂ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (Q₂ : Set G)).inv_mem hwNorm)
  have hmapComp :
      Q₀.map (MulAut.conj x⁻¹).toMonoidHom =
        (Q₀.map (MulAut.conj k⁻¹).toMonoidHom).map
          (MulAut.conj wG⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext q
    simp [x, mul_assoc]
  refine ⟨x, ⟨hxK, hxCent⟩, ?_⟩
  calc
    Q₂ = Q₂.map (MulAut.conj wG⁻¹).toMonoidHom := hwMap.symm
    _ = (Q₀.map (MulAut.conj k⁻¹).toMonoidHom).map
          (MulAut.conj wG⁻¹).toMonoidHom := by rw [hQ₂]
    _ = Q₀.map (MulAut.conj x⁻¹).toMonoidHom := hmapComp.symm

end Submission.OddOrder.MathlibSupport
