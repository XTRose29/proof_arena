import Submission.OddOrder.BG.Section06.PLengthOneProduct
import Submission.OddOrder.MathlibSupport.FittingPCore
import Submission.OddOrder.MathlibSupport.OddPGroupElementaryCentralizer
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient

/-!
Bender--Glauberman Theorem 6.7.

A `p'`-subgroup normalized by a maximal elementary-abelian `p`-subgroup of
a solvable group of `p`-length one lies in the `p'`-core.
-/

namespace Submission.OddOrder.BG.Section06

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
/-- Images of elementary-abelian subgroups remain elementary abelian. -/
private theorem elementary_map {H : Type*} [Group H]
    {E : Subgroup G} (hE : IsElementaryAbelianGroup p E)
    (f : G →* H) : IsElementaryAbelianGroup p (E.map f) := by
  letI : IsMulCommutative E := hE.commutative
  refine
    { isPGroup := hE.isPGroup.map f
      commutative := Subgroup.map_isMulCommutative E f
      pow_eq_one := ?_ }
  intro x
  rcases x.property with ⟨e, he, hxe⟩
  apply Subtype.ext
  change (x : H) ^ p = 1
  rw [← hxe]
  rw [← map_pow]
  have hep : e ^ p = 1 :=
    congrArg Subtype.val (hE.pow_eq_one ⟨e, he⟩)
  rw [hep, map_one]

/-- The reduced-core form of Theorem 6.7.  The displayed Sylow subgroup is
the normal `p`-core; this is exactly what `p`-length one supplies after
quotienting by the `p'`-core. -/
theorem norm_pmaxElem_eq_bot_of_pPrimeCore_eq_bot
    [IsSolvable G] {E L : Subgroup G}
    (hmax : IsPMaxElem p (⊤ : Subgroup G) E)
    (hpodd : Odd p)
    (S : Sylow p G) (hScore : (S : Subgroup G) = pCore p G)
    (hprimeCore : pPrimeCore p G = ⊥)
    (hnormL : E ≤ Subgroup.normalizer (L : Set G))
    (hLp : IsPPrimeSubgroup p L) :
    L = ⊥ := by
  have hES : E ≤ (S : Subgroup G) := by
    obtain ⟨T, hET⟩ := hmax.elementary.isPGroup.exists_le_sylow
    have hSnormal : (S : Subgroup G).Normal := by
      rw [hScore]
      infer_instance
    letI : Unique (Sylow p G) := Sylow.unique_of_normal S hSnormal
    simpa [show T = S from Subsingleton.elim T S] using hET
  have hcopSL : (Nat.card S).Coprime (Nat.card L) := by
    rw [S.card_eq_multiplicity]
    exact hLp.pow_left _
  have hdisSL : Disjoint (S : Subgroup G) L :=
    Subgroup.disjoint_of_coprime_natCard hcopSL
  have hnormS : L ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    rw [hScore, (pCore p G).normalizer_eq_top]
    exact le_top
  have hcentralE : L ≤ Subgroup.centralizer (E : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    apply le_bot_iff.mp
    have hle : ⁅L, E⁆ ≤ (S : Subgroup G) ⊓ L := by
      apply le_inf
      · exact (Subgroup.commutator_mono le_rfl hES).trans
          (Subgroup.le_normalizer_iff_commutator_le_right.mp hnormS)
      · rw [Subgroup.commutator_comm]
        exact Subgroup.le_normalizer_iff_commutator_le_right.mp hnormL
    simpa [disjoint_iff.mp hdisSL] using hle
  have hmaxS : IsPMaxElem p (S : Subgroup G) E :=
    hmax.of_le le_top hES
  have hTorsion : pTorsionCentralizerWithin p (S : Subgroup G) E =
      (E : Set G) :=
    isPMaxElem_iff_pTorsionCentralizerWithin.mp hmaxS
  have hoddS : Odd (Nat.card S) := by
    rw [S.card_eq_multiplicity]
    exact hpodd.pow
  have hcentralS : L ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    apply coprime_odd_faithful_centralizes_of_pTorsionCentralizer
      hmaxS.isPElementaryIn S.isPGroup' hnormS hcopSL hoddS
    simpa [hTorsion] using hcentralE
  have hcentLeS : Subgroup.centralizer ((S : Subgroup G) : Set G) ≤
      (S : Subgroup G) := by
    rw [hScore]
    exact centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hprimeCore
  apply le_antisymm ?_ bot_le
  intro l hl
  apply Subgroup.mem_bot.mpr
  have hlS : l ∈ (S : Subgroup G) := hcentLeS (hcentralS hl)
  have hlInf : l ∈ (S : Subgroup G) ⊓ L := ⟨hlS, hl⟩
  rw [disjoint_iff.mp hdisSL] at hlInf
  exact Subgroup.mem_bot.mp hlInf

/-- `BGsection6.plength1_norm_pmaxElem`, Bender--Glauberman Theorem 6.7. -/
theorem plength1_norm_pmaxElem [IsSolvable G]
    {E L : Subgroup G}
    (hmax : IsPMaxElem p (⊤ : Subgroup G) E)
    (hpodd : Odd p)
    (hpl : IsPLengthOne p G)
    (hnormL : E ≤ Subgroup.normalizer (L : Set G))
    (hLp : IsPPrimeSubgroup p L) :
    L ≤ pPrimeCore p G := by
  classical
  let K : Subgroup G := pPrimeCore p G
  letI : K.Normal := by
    dsimp [K]
    infer_instance
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let Eq : Subgroup (G ⧸ K) := E.map q
  let Lq : Subgroup (G ⧸ K) := L.map q
  obtain ⟨P, hPcore⟩ := hpl
  letI : P.Normal := by
    rw [hPcore]
    infer_instance
  letI : Unique (Sylow p (G ⧸ K)) :=
    Sylow.unique_of_normal P inferInstance
  obtain ⟨S, hES⟩ := hmax.elementary.isPGroup.exists_le_sylow
  let Sq : Sylow p (G ⧸ K) :=
    S.mapSurjective (QuotientGroup.mk'_surjective K)
  have hSqP : Sq = P := Subsingleton.elim Sq P
  have hSqCore : (Sq : Subgroup (G ⧸ K)) = pCore p (G ⧸ K) := by
    rw [hSqP]
    exact hPcore
  have hdisSK : Disjoint (S : Subgroup G) K := by
    dsimp [K]
    exact disjoint_pPrimeCore_of_isPGroup S.isPGroup'
  have hqInjS : ∀ {x y : G}, x ∈ (S : Subgroup G) →
      y ∈ (S : Subgroup G) → q x = q y → x = y := by
    intro x y hx hy hxy
    have hxyK : x * y⁻¹ ∈ K := by
      apply (QuotientGroup.eq_one_iff (x * y⁻¹)).mp
      change q (x * y⁻¹) = 1
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hxyS : x * y⁻¹ ∈ (S : Subgroup G) :=
      S.mul_mem hx (S.inv_mem hy)
    have hxyOne : x * y⁻¹ = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hdisSK]
      exact ⟨hxyS, hxyK⟩
    exact mul_inv_eq_one.mp hxyOne
  have hEqElem : IsElementaryAbelianGroup p Eq := by
    dsimp [Eq]
    exact elementary_map hmax.elementary q
  have hmaxEq : IsPMaxElem p (⊤ : Subgroup (G ⧸ K)) Eq := by
    refine ⟨⟨le_top, hEqElem⟩, ?_⟩
    intro Fq hFq hEqFq
    obtain ⟨Tq, hFqTq⟩ := hFq.2.isPGroup.exists_le_sylow
    have hTqSq : Tq = Sq := Subsingleton.elim Tq Sq
    have hFqSq : Fq ≤ (Sq : Subgroup (G ⧸ K)) := by
      simpa [hTqSq] using hFqTq
    let F : Subgroup G := Fq.comap q ⊓ (S : Subgroup G)
    letI : IsMulCommutative Fq := hFq.2.commutative
    have hFpow : ∀ x : F, x ^ p = 1 := by
      intro x
      let xq : Fq := ⟨q (x : G), x.property.1⟩
      have hxqpow : xq ^ p = 1 := hFq.2.pow_eq_one xq
      apply Subtype.ext
      apply hqInjS
      · exact S.pow_mem x.property.2 p
      · exact S.one_mem
      · change q ((x : G) ^ p) = q 1
        rw [map_pow, map_one]
        exact congrArg Subtype.val hxqpow
    letI : IsMulCommutative F := by
      refine ⟨⟨fun x y ↦ ?_⟩⟩
      let xq : Fq := ⟨q (x : G), x.property.1⟩
      let yq : Fq := ⟨q (y : G), y.property.1⟩
      apply Subtype.ext
      apply hqInjS
      · exact S.mul_mem x.property.2 y.property.2
      · exact S.mul_mem y.property.2 x.property.2
      · change q ((x : G) * y) = q ((y : G) * x)
        simpa [map_mul] using congrArg Subtype.val (mul_comm xq yq)
    have hFElem : IsElementaryAbelianGroup p F :=
      { isPGroup := by
          intro x
          refine ⟨1, ?_⟩
          simpa using hFpow x
        commutative := inferInstance
        pow_eq_one := hFpow }
    have hEF : E ≤ F := by
      intro e he
      refine ⟨?_, hES he⟩
      exact hEqFq ⟨e, he, rfl⟩
    have hFmap : F.map q = Fq := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hx.1
      · intro z hz
        have hzSq : z ∈ (Sq : Subgroup (G ⧸ K)) := hFqSq hz
        rcases hzSq with ⟨x, hxS, hxz⟩
        refine ⟨x, ⟨?_, hxS⟩, hxz⟩
        change q x ∈ Fq
        rw [hxz]
        exact hz
    have hFE : F = E := hmax.2 F ⟨le_top, hFElem⟩ hEF
    calc
      Fq = F.map q := hFmap.symm
      _ = E.map q := congrArg (fun H : Subgroup G ↦ H.map q) hFE
      _ = Eq := rfl
  have hnormLq : Eq ≤ Subgroup.normalizer (Lq : Set (G ⧸ K)) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨e * l * e⁻¹, (Subgroup.mem_normalizer_iff.mp
        (hnormL he) l).mp hl, by simp⟩
    · rintro ⟨l, hl, hql⟩
      refine ⟨e⁻¹ * l * e, (Subgroup.mem_normalizer_iff''.mp
        (hnormL he) l).mp hl, ?_⟩
      rw [map_mul, map_mul, map_inv, hql]
      group
  have hLqPrime : IsPPrimeSubgroup p Lq := by
    dsimp [Lq, IsPPrimeSubgroup]
    exact hLp.coprime_dvd_right (Subgroup.card_map_dvd L q)
  letI : IsSolvable (G ⧸ K) :=
    solvable_of_surjective (f := q) (QuotientGroup.mk'_surjective K)
  have hLqBot : Lq = ⊥ :=
    norm_pmaxElem_eq_bot_of_pPrimeCore_eq_bot hmaxEq hpodd Sq hSqCore
      (by
        dsimp [K]
        exact pPrimeCore_quotient_self_eq_bot)
      hnormLq hLqPrime
  have hLK : L ≤ q.ker := (Subgroup.map_eq_bot_iff L).mp hLqBot
  simpa [q, QuotientGroup.ker_mk', K] using hLK

end Submission.OddOrder.BG.Section06
