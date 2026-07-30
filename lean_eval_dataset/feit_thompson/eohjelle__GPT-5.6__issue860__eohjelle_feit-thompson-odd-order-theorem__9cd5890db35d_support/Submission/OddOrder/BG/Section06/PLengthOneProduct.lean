import Submission.OddOrder.BG.Section06.PProdCoprime
import Submission.OddOrder.MathlibSupport.PLengthOne
import Submission.OddOrder.MathlibSupport.PPrimePCore

/-!
Bender--Glauberman Lemma 6.6 for groups of `p`-length one.
-/

namespace Submission.OddOrder.BG.Section06

open Submission.OddOrder.MathlibSupport
open scoped commutatorElement
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- `BGsection6.plength1_Sylow_prod`, Lemma 6.6(a1).

The source product `O_{p'}(G) * S` is a join here because the first factor is
normal. -/
theorem plength1_Sylow_prod (S : Sylow p G)
    (hpl : IsPLengthOne p G) :
    pPrimeCore p G ⊔ (S : Subgroup G) = pPrimePCore p G := by
  classical
  let K : Subgroup G := pPrimeCore p G
  letI : K.Normal := by
    dsimp [K]
    infer_instance
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  obtain ⟨P, hP⟩ := hpl
  let Sq : Sylow p (G ⧸ K) :=
    S.mapSurjective (QuotientGroup.mk'_surjective K)
  letI : P.Normal := by
    rw [hP]
    infer_instance
  letI : Unique (Sylow p (G ⧸ K)) :=
    Sylow.unique_of_normal P inferInstance
  have hSqP : Sq = P := Subsingleton.elim Sq P
  have hSmap : (S : Subgroup G).map q =
      pCore p (G ⧸ K) := by
    change (Sq : Subgroup (G ⧸ K)) = pCore p (G ⧸ K)
    rw [hSqP]
    simpa [K] using hP
  have hmap : (K ⊔ (S : Subgroup G)).map q =
      pCore p (G ⧸ K) := by
    rw [Subgroup.map_sup]
    have hKbot : K.map q = ⊥ := by
      exact (Subgroup.map_eq_bot_iff K).mpr (by
        rw [QuotientGroup.ker_mk'])
    rw [hKbot, hSmap]
    simp
  calc
    K ⊔ (S : Subgroup G) =
        ((K ⊔ (S : Subgroup G)).map q).comap q := by
      symm
      apply Subgroup.comap_map_eq_self
      rw [QuotientGroup.ker_mk']
      exact le_sup_left
    _ = (pCore p (G ⧸ K)).comap q := by rw [hmap]
    _ = pPrimePCore p G := by rfl

/-- `BGsection6.plength1_Frattini`, Lemma 6.6(a2). -/
theorem plength1_Frattini (S : Sylow p G)
    (hpl : IsPLengthOne p G) :
    pPrimeCore p G ⊔ Subgroup.normalizer (S : Set G) = ⊤ := by
  let K : Subgroup G := pPrimeCore p G
  let N : Subgroup G := pPrimePCore p G
  have hprod : K ⊔ (S : Subgroup G) = N := by
    simpa [K, N] using plength1_Sylow_prod S hpl
  have hSN : (S : Subgroup G) ≤ N := by
    rw [← hprod]
    exact le_sup_right
  have hfrat : Subgroup.normalizer (S : Set G) ⊔ N = ⊤ :=
    Sylow.normalizer_sup_eq_top' S hSN
  have hNle : N ≤ K ⊔ Subgroup.normalizer (S : Set G) := by
    rw [← hprod]
    exact sup_le le_sup_left
      (Subgroup.le_normalizer.trans le_sup_right)
  apply top_unique
  rw [← hfrat]
  exact sup_le le_sup_right hNle

/-- The `p'`-core has order coprime to every Sylow `p`-subgroup. -/
private theorem pPrimeCore_coprime_sylow (S : Sylow p G) :
    (Nat.card (pPrimeCore p G)).Coprime (Nat.card S) := by
  rw [S.card_eq_multiplicity]
  exact (pPrimeCore_coprime_card (G := G) (p := p)).symm.pow_right _

/-- `BGsection6.plength1_Sylow_sub_der1`, Lemma 6.6(b). -/
theorem plength1_Sylow_sub_der1 (S : Sylow p G)
    (hpl : IsPLengthOne p G)
    (hSder : (S : Subgroup G) ≤ _root_.commutator G) :
    (S : Subgroup G) ≤
      ⁅Subgroup.normalizer (S : Set G),
        Subgroup.normalizer (S : Set G)⁆ := by
  let K : Subgroup G := pPrimeCore p G
  let U : Subgroup G := Subgroup.normalizer (S : Set G)
  have hKU : K ⊔ U = ⊤ := by
    simpa [K, U] using plength1_Frattini S hpl
  have hSU : (S : Subgroup G) ≤ U := by
    dsimp [U]
    exact Subgroup.le_normalizer
  have hcop : (Nat.card K).Coprime (Nat.card S) := by
    simpa [K] using pPrimeCore_coprime_sylow S
  have hfocal := pprod_focal_coprime
    (K := K) (U := U) (H := (S : Subgroup G)) hKU hSU hcop
  intro x hx
  have hxleft : x ∈ (S : Subgroup G) ⊓ _root_.commutator G :=
    ⟨hx, hSder hx⟩
  rw [hfocal] at hxleft
  exact hxleft.2

/-- `BGsection6.plength1_Sylow_trans`, Lemma 6.6(c).

The source allows an arbitrary set `Y`; its generated subgroup is used in
the application of Lemma 6.5(c). -/
theorem plength1_Sylow_trans [IsSolvable G]
    (S : Sylow p G) (hpl : IsPLengthOne p G)
    (Y : Set G) (hYS : Y ⊆ (S : Set G))
    (g : G)
    (hYgS : ∀ y ∈ Y, (MulAut.conj g⁻¹).toMonoidHom y ∈ S) :
    ∃ c : G, c ∈ Subgroup.centralizer Y ∧
      ∃ u : G, u ∈ Subgroup.normalizer (S : Set G) ∧ g = c * u := by
  let K : Subgroup G := pPrimeCore p G
  let U : Subgroup G := Subgroup.normalizer (S : Set G)
  let H : Subgroup G := Subgroup.closure Y
  have hKU : K ⊔ U = ⊤ := by
    simpa [K, U] using plength1_Frattini S hpl
  have hHS : H ≤ (S : Subgroup G) := by
    dsimp [H]
    exact (Subgroup.closure_le (S : Subgroup G)).mpr hYS
  have hHU : H ≤ U :=
    hHS.trans (by
      dsimp [U]
      exact Subgroup.le_normalizer)
  have hHgS : H.map (MulAut.conj g⁻¹).toMonoidHom ≤
      (S : Subgroup G) := by
    rw [Subgroup.map_le_iff_le_comap]
    dsimp [H]
    apply (Subgroup.closure_le
      ((S : Subgroup G).comap
        (MulAut.conj g⁻¹).toMonoidHom)).mpr
    intro y hy
    exact hYgS y hy
  have hHgU : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ U :=
    hHgS.trans (by
      dsimp [U]
      exact Subgroup.le_normalizer)
  have hcopKS : (Nat.card K).Coprime (Nat.card S) := by
    simpa [K] using pPrimeCore_coprime_sylow S
  have hcardHdvd : Nat.card H ∣ Nat.card S :=
    Subgroup.card_dvd_of_le hHS
  have hcopKH : (Nat.card K).Coprime (Nat.card H) :=
    hcopKS.coprime_dvd_right hcardHdvd
  obtain ⟨c, hc, u, hu, hcu⟩ :=
    pprod_trans_coprime hKU hHU hcopKH g hHgU
  refine ⟨c, ?_, u, hu, hcu⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp hc.2)
    y (Subgroup.subset_closure hy)

/-- `BGsection6.plength1_Sylow_Jsub`, Lemma 6.6(d).

Every `p`-subgroup can be conjugated into `S` by an element centralizing its
intersection with `S`.  As elsewhere, the source conjugate `Q :^ x` is the
image under `MulAut.conj x⁻¹`. -/
theorem plength1_Sylow_Jsub (S : Sylow p G)
    (hpl : IsPLengthOne p G)
    (Q : Subgroup G) (hQp : IsPGroup p Q) :
    ∃ x : G, x ∈ Subgroup.centralizer ((Q ⊓ (S : Subgroup G) : Subgroup G) : Set G) ∧
      Q.map (MulAut.conj x⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
  classical
  let K : Subgroup G := pPrimeCore p G
  let N : Subgroup G := pPrimePCore p G
  letI : K.Normal := by
    dsimp [K]
    infer_instance
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  obtain ⟨P, hP⟩ := hpl
  letI : P.Normal := by
    rw [hP]
    infer_instance
  letI : Unique (Sylow p (G ⧸ K)) :=
    Sylow.unique_of_normal P inferInstance
  have hQN : Q ≤ N := by
    change Q ≤ (pCore p (G ⧸ K)).comap q
    rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨T, hQT⟩ := (hQp.map q).exists_le_sylow
    calc
      Q.map q ≤ (T : Subgroup (G ⧸ K)) := hQT
      _ = (P : Subgroup (G ⧸ K)) :=
        congrArg (fun R : Sylow p (G ⧸ K) ↦ (R : Subgroup (G ⧸ K)))
          (Subsingleton.elim T P)
      _ = pCore p (G ⧸ K) := by simpa [K] using hP
  have hprod : K ⊔ (S : Subgroup G) = N := by
    simpa [K, N] using
      plength1_Sylow_prod S (show IsPLengthOne p G from ⟨P, hP⟩)
  have hSN : (S : Subgroup G) ≤ N := by
    rw [← hprod]
    exact le_sup_right
  let SN : Sylow p N := S.subtype hSN
  let QN : Subgroup N := Q.subgroupOf N
  have hQNp : IsPGroup p QN := by
    dsimp [QN]
    exact hQp.comap_subtype
  obtain ⟨T, hQNT⟩ := hQNp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N T SN
  let xy : G := ((n⁻¹ : N) : G)
  have hxyN : xy ∈ N := by
    exact (n⁻¹ : N).property
  have hQxyS : Q.map (MulAut.conj xy⁻¹).toMonoidHom ≤
      (S : Subgroup G) := by
    rintro z ⟨a, ha, rfl⟩
    let aN : N := ⟨a, hQN ha⟩
    have haQN : aN ∈ QN := by
      exact ha
    have haT : aN ∈ T := hQNT haQN
    have hnaSN : (MulAut.conj n).toMonoidHom aN ∈ SN := by
      rw [← hn]
      change (MulAut.conj n).toMonoidHom aN ∈
        (T : Subgroup N).map (MulAut.conj n).toMonoidHom
      exact Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom haT
    change ((n : G) * a * (n : G)⁻¹) ∈ (S : Subgroup G) at hnaSN
    simpa [xy, MulAut.conj_apply] using hnaSN
  have hxyProd : xy ∈ (K : Set G) * ((S : Subgroup G) : Set G) := by
    rw [← Subgroup.normal_mul K (S : Subgroup G), hprod]
    exact hxyN
  rcases hxyProd with ⟨x, hxK, y, hyS, hxy⟩
  have hQxS : Q.map (MulAut.conj x⁻¹).toMonoidHom ≤
      (S : Subgroup G) := by
    rintro z ⟨a, ha, rfl⟩
    have haxyS : (MulAut.conj xy⁻¹).toMonoidHom a ∈ S :=
      hQxyS (Subgroup.mem_map_of_mem
        (MulAut.conj xy⁻¹).toMonoidHom ha)
    rw [← hxy] at haxyS
    have hback : y * (MulAut.conj (x * y)⁻¹).toMonoidHom a * y⁻¹ ∈
        (S : Subgroup G) :=
      S.mul_mem (S.mul_mem hyS haxyS) (S.inv_mem hyS)
    simpa [MulAut.conj_apply, mul_assoc] using hback
  refine ⟨x, ?_, hQxS⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzQ : z ∈ Q := hz.1
  have hzS : z ∈ (S : Subgroup G) := hz.2
  have hxzS : (MulAut.conj x⁻¹).toMonoidHom z ∈ S :=
    hQxS (Subgroup.mem_map_of_mem
      (MulAut.conj x⁻¹).toMonoidHom hzQ)
  have hcommK : ⁅x⁻¹, z⁆ ∈ K :=
    (Subgroup.commutator_le_left K (Q ⊓ (S : Subgroup G)))
      (Subgroup.commutator_mem_commutator (K.inv_mem hxK) hz)
  have hcommS : ⁅x⁻¹, z⁆ ∈ (S : Subgroup G) := by
    rw [commutatorElement_def]
    exact S.mul_mem hxzS (S.inv_mem hzS)
  have hdis : Disjoint K (S : Subgroup G) :=
    Subgroup.disjoint_of_coprime_natCard
      (by simpa [K] using pPrimeCore_coprime_sylow S)
  have hcommOne : ⁅x⁻¹, z⁆ = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp hdis]
    exact ⟨hcommK, hcommS⟩
  exact (Commute.inv_left_iff.mp
    (commutatorElement_eq_one_iff_commute.mp hcommOne)).symm

end Submission.OddOrder.BG.Section06
