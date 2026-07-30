import Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect
import Submission.OddOrder.MathlibSupport.Fitting
import Submission.OddOrder.MathlibSupport.FrattiniPGroup
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient

/-!
Bender--Glauberman Lemma 6.3(b).

Although this result is not used later in the MathComp development, it is the
second half of the source lemma and naturally follows the semidirect-product
result in `CoprimeDerivedSemidirect`.
-/

namespace Submission.OddOrder.BG.Section06

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G]

/-- In a finite nilpotent group, quotienting by the `p'`-core leaves a
`p`-group. -/
theorem quotient_pPrimeCore_isPGroup_of_isNilpotent
    {p : ℕ} [Fact p.Prime] [Group.IsNilpotent G] :
    IsPGroup p (G ⧸ pPrimeCore p G) := by
  let Q := G ⧸ pPrimeCore p G
  letI : Group.IsNilpotent Q := by infer_instance
  have hfitTop : fittingCore Q = ⊤ := by
    apply top_unique
    exact nilpotent_normal_le_fittingCore
      (H := (⊤ : Subgroup Q)) (by infer_instance) (by infer_instance)
  have hcoreTop : pCore p Q = ⊤ := by
    calc
      pCore p Q = fittingCore Q :=
        (fittingCore_eq_pCore_of_pPrimeCore_eq_bot p
          (pPrimeCore_quotient_self_eq_bot (G := G) (p := p))).symm
      _ = ⊤ := hfitTop
  have hpTop : IsPGroup p (⊤ : Subgroup Q) := by
    rw [← hcoreTop]
    exact pCore_isPGroup
  exact hpTop.of_equiv Subgroup.topEquiv

/-- A finite `p`-group with cyclic abelianization is cyclic. -/
theorem isCyclic_of_isPGroup_of_isCyclic_abelianization
    {p : ℕ} [Fact p.Prime]
    (hpG : IsPGroup p G)
    [IsCyclic (G ⧸ _root_.commutator G)] :
    IsCyclic G := by
  let D : Subgroup G := _root_.commutator G
  let F : Subgroup G := frattini G
  letI : F.Normal := by
    dsimp [F]
    infer_instance
  have hDF : D ≤ F := by
    dsimp [D, F]
    exact IsPGroup.commutator_le_frattini hpG
  let φ : (G ⧸ D) →* (G ⧸ F) :=
    QuotientGroup.map D F (MonoidHom.id G) hDF
  have hφ : Function.Surjective φ := by
    apply QuotientGroup.map_surjective_of_surjective
    · exact QuotientGroup.mk'_surjective F
  letI : IsCyclic (G ⧸ F) := isCyclic_of_surjective φ hφ
  obtain ⟨x, hx⟩ :=
    isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic (G ⧸ F))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective F x
  have hmap : (Subgroup.zpowers g).map (QuotientGroup.mk' F) = ⊤ := by
    rw [MonoidHom.map_zpowers, hx]
  have hsup : Subgroup.zpowers g ⊔ F = ⊤ := by
    calc
      Subgroup.zpowers g ⊔ F =
          ((Subgroup.zpowers g).map (QuotientGroup.mk' F)).comap
            (QuotientGroup.mk' F) := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      _ = ⊤ := by rw [hmap, Subgroup.comap_top]
  exact isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨g, frattini_nongenerating hsup⟩

/-- `BGsection6.prime_nil_der1_factor`, Bender--Glauberman Lemma 6.3(b).

The source Hall assertion is represented by coprimality of the derived
subgroup's cardinality and index. -/
theorem prime_nil_der1_factor
    (hnil : Group.IsNilpotent (_root_.commutator G))
    (hprime : (Nat.card (G ⧸ _root_.commutator G)).Prime) :
    (Nat.card (_root_.commutator G)).Coprime
        (_root_.commutator G).index ∧
      ∀ H : Subgroup G, (_root_.commutator G).IsComplement' H →
        _root_.commutator G = ⁅(⊤ : Subgroup G), H⁆ := by
  classical
  let D : Subgroup G := _root_.commutator G
  letI : Group.IsNilpotent D := by
    simpa [D] using hnil
  let p : ℕ := Nat.card (G ⧸ D)
  have hp : p.Prime := by
    simpa [p, D] using hprime
  letI : Fact p.Prime := ⟨hp⟩
  let N : Subgroup D := pPrimeCore p D
  letI : N.Characteristic := by
    dsimp [N]
    infer_instance
  let Na : Subgroup G := N.map D.subtype
  letI : Na.Normal := by
    dsimp [Na]
    infer_instance
  have hNaD : Na ≤ D := by
    dsimp [Na]
    exact Subgroup.map_subtype_le N
  let q : G →* G ⧸ Na := QuotientGroup.mk' Na
  let Q := G ⧸ Na
  let Dq : Subgroup Q := D.map q
  let f : D →* Q := q.comp D.subtype
  have hfker : f.ker = N := by
    ext x
    change QuotientGroup.mk' Na (x : G) = 1 ↔ x ∈ N
    constructor
    · intro hx
      change ((x : G) : G ⧸ Na) = 1 at hx
      have hxNa : (x : G) ∈ Na :=
        (QuotientGroup.eq_one_iff (x : G)).mp hx
      change (x : G) ∈ N.map D.subtype at hxNa
      rcases hxNa with ⟨n, hn, hnx⟩
      have hnxeq : n = x := Subtype.ext hnx
      simpa [hnxeq] using hn
    · intro hx
      change ((x : G) : G ⧸ Na) = 1
      apply (QuotientGroup.eq_one_iff (x : G)).mpr
      change (x : G) ∈ N.map D.subtype
      exact ⟨x, hx, rfl⟩
  have hfrange : f.range = Dq := by
    dsimp [f, Dq]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hDqP : IsPGroup p Dq := by
    have hDNp : IsPGroup p (D ⧸ N) :=
      quotient_pPrimeCore_isPGroup_of_isNilpotent (G := D) (p := p)
    obtain ⟨n, hn⟩ := hDNp.exists_card_eq
    apply IsPGroup.of_card (n := n)
    calc
      Nat.card Dq = Nat.card f.range :=
        congrArg (fun L : Subgroup Q ↦ Nat.card L) hfrange.symm
      _ = f.ker.index := (Subgroup.index_ker f).symm
      _ = N.index := congrArg Subgroup.index hfker
      _ = Nat.card (D ⧸ N) := N.index_eq_card
      _ = p ^ n := hn
  have hindexDq : Dq.index = D.index := by
    dsimp [Dq]
    have hker : q.ker ≤ D := by
      rw [show q.ker = Na by
        dsimp [q]
        exact QuotientGroup.ker_mk' Na]
      exact hNaD
    exact D.index_map_eq (QuotientGroup.mk'_surjective Na) hker
  have hindexD : D.index = p := by
    exact D.index_eq_card
  have hQP : IsPGroup p Q := by
    obtain ⟨n, hn⟩ := hDqP.exists_card_eq
    apply IsPGroup.of_card (n := n + 1)
    calc
      Nat.card Q = Dq.index * Nat.card Dq := Dq.index_mul_card.symm
      _ = p * p ^ n := by rw [hindexDq, hindexD, hn]
      _ = p ^ (n + 1) := (pow_succ' p n).symm
  have hcommQ : _root_.commutator Q = Dq := by
    symm
    dsimp [Dq, D]
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Na)]
    rfl
  let e : (Q ⧸ Dq) ≃* (G ⧸ D) := by
    simpa [Q, Dq, q] using
      (QuotientGroup.quotientQuotientEquivQuotient Na D hNaD)
  letI : IsCyclic (G ⧸ D) := isCyclic_of_prime_card (p := p) rfl
  letI : IsCyclic (Q ⧸ Dq) :=
    isCyclic_of_injective e.toMonoidHom e.injective
  have hcycAb : IsCyclic (Q ⧸ _root_.commutator Q) := by
    let eAb : (Q ⧸ _root_.commutator Q) ≃* (Q ⧸ Dq) :=
      QuotientGroup.quotientMulEquivOfEq hcommQ
    exact isCyclic_of_injective eAb.toMonoidHom eAb.injective
  letI : IsCyclic (Q ⧸ _root_.commutator Q) := hcycAb
  letI : IsCyclic Q :=
    isCyclic_of_isPGroup_of_isCyclic_abelianization hQP
  have hQcommBot : _root_.commutator Q = ⊥ := by
    letI : IsMulCommutative Q := IsCyclic.isMulCommutative
    exact commutator_eq_bot Q
  have hDmapBot : D.map q = ⊥ := by
    change Dq = ⊥
    rw [← hcommQ, hQcommBot]
  have hDNa : D ≤ Na := by
    have hle := (Subgroup.map_eq_bot_iff D).mp hDmapBot
    simpa [q, QuotientGroup.ker_mk'] using hle
  have hNaEq : Na = D := le_antisymm hNaD hDNa
  have hNtop : N = ⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    calc
      N.map D.subtype = Na := rfl
      _ = D := hNaEq
      _ = D.subtype.range := D.range_subtype.symm
      _ = (⊤ : Subgroup D).map D.subtype := MonoidHom.range_eq_map D.subtype
  have hpD : p.Coprime (Nat.card D) := by
    have hcore := pPrimeCore_coprime_card (G := D) (p := p)
    rw [← show N = pPrimeCore p D from rfl, hNtop] at hcore
    simpa using hcore
  have hHall : (Nat.card D).Coprime D.index := by
    rw [hindexD]
    exact hpD.symm
  refine ⟨by simpa [D] using hHall, ?_⟩
  intro H hcomp
  have hnorm : H ≤ Subgroup.normalizer (D : Set G) := by
    rw [D.normalizer_eq_top]
    exact le_top
  have hcopDH : (Nat.card D).Coprime (Nat.card H) := by
    rw [← hcomp.symm.index_eq_card]
    exact hHall
  have hmixed : ⁅D, H⁆ = D :=
    (coprime_der1_sdprod (K := D) (H := H) hcomp hnorm hcopDH
      (by change D ≤ _root_.commutator G; exact le_rfl)).1
  change D = ⁅(⊤ : Subgroup G), H⁆
  apply le_antisymm
  · rw [← hmixed]
    exact Subgroup.commutator_mono le_top le_rfl
  · dsimp [D]
    exact Subgroup.commutator_mono le_rfl le_top

end Submission.OddOrder.BG.Section06
