import Submission.OddOrder.BG.Section06.PrimeNilDerivedFactor
import Submission.OddOrder.MathlibSupport.SolvableComplementConjugacy

/-!
Bender--Glauberman Lemma 6.5 for a coprime product.

The ambient group is the source subgroup `G`; thus the source equality
`K * U = G` is represented by `K ⊔ U = ⊤`.
-/

namespace Submission.OddOrder.BG.Section06

open Submission.OddOrder.MathlibSupport
open scoped commutatorElement
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K U H : Subgroup G}

omit [Finite G] in
/-- `BGsection6.pprod_focal_coprime`, Bender--Glauberman Lemma 6.5(a).
No solvability hypothesis is needed. -/
theorem pprod_focal_coprime [K.Normal]
    (hKU : K ⊔ U = ⊤)
    (hHU : H ≤ U)
    (hcop : (Nat.card K).Coprime (Nat.card H)) :
    H ⊓ _root_.commutator G = H ⊓ ⁅U, U⁆ := by
  classical
  let qK : G →* G ⧸ K := QuotientGroup.mk' K
  have hUtop : U.map qK = ⊤ := by
    have hKbot : K.map qK = ⊥ := by
      exact (Subgroup.map_eq_bot_iff K).mpr (by
        rw [QuotientGroup.ker_mk'])
    calc
      U.map qK = K.map qK ⊔ U.map qK := by rw [hKbot]; simp
      _ = (K ⊔ U).map qK := (Subgroup.map_sup K U qK).symm
      _ = ⊤ := by
        rw [hKU, Subgroup.map_top_of_surjective qK
          (QuotientGroup.mk'_surjective K)]
  have hmapDer : (_root_.commutator G).map qK = ⁅U, U⁆.map qK := by
    calc
      (_root_.commutator G).map qK = ⁅qK.range, qK.range⁆ :=
        map_commutator_eq G qK
      _ = ⁅(⊤ : Subgroup (G ⧸ K)), ⊤⁆ := by
        rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective K)]
      _ = ⁅U.map qK, U.map qK⁆ := by rw [hUtop]
      _ = ⁅U, U⁆.map qK := (Subgroup.map_commutator U U qK).symm
  let A : Subgroup G := ⁅U, U⁆
  have hAU : A ≤ U := by
    dsimp [A]
    exact Subgroup.commutator_le_self U
  let AU : Subgroup U := A.subgroupOf U
  letI : AU.Normal := by
    dsimp [AU, A]
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      (Subgroup.normalizer_commutator_ge_left U U)
  let qU : U →* U ⧸ AU := QuotientGroup.mk' AU
  let HU : Subgroup U := H.subgroupOf U
  let J : Subgroup G := U ⊓ K
  let JU : Subgroup U := J.subgroupOf U
  have hcardHU : Nat.card HU = Nat.card H := by
    dsimp [HU]
    exact natCard_subgroupOf_eq hHU
  have hcardJU : Nat.card JU = Nat.card J := by
    dsimp [JU, J]
    exact natCard_subgroupOf_eq inf_le_left
  have hHUdiv : Nat.card (HU.map qU) ∣ Nat.card H := by
    rw [← hcardHU]
    exact Subgroup.card_map_dvd HU qU
  have hJUdiv : Nat.card (JU.map qU) ∣ Nat.card K := by
    apply (Subgroup.card_map_dvd JU qU).trans
    rw [hcardJU]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hdis : Disjoint (HU.map qU) (JU.map qU) :=
    Subgroup.disjoint_of_coprime_natCard
      ((hcop.coprime_dvd_left hJUdiv).symm.coprime_dvd_left hHUdiv)
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hxU : x ∈ U := hHU hx.1
    let xu : U := ⟨x, hxU⟩
    have hxMap : qK x ∈ (_root_.commutator G).map qK :=
      Subgroup.mem_map_of_mem qK hx.2
    rw [hmapDer] at hxMap
    rcases hxMap with ⟨y, hyA, hyx⟩
    have hyU : y ∈ U := hAU hyA
    let yu : U := ⟨y, hyU⟩
    let j : G := y⁻¹ * x
    have hjK : j ∈ K := by
      dsimp [j]
      exact QuotientGroup.eq.mp hyx
    have hjU : j ∈ U := by
      dsimp [j]
      exact U.mul_mem (U.inv_mem hyU) hxU
    let ju : U := ⟨j, hjU⟩
    have hqyu : qU yu = 1 := by
      apply (QuotientGroup.eq_one_iff yu).mpr
      exact hyA
    have hqxj : qU xu = qU ju := by
      change qU xu = qU (yu⁻¹ * xu)
      rw [map_mul, map_inv, hqyu, inv_one, one_mul]
    have hqxHU : qU xu ∈ HU.map qU := by
      exact ⟨xu, hx.1, rfl⟩
    have hqxJU : qU xu ∈ JU.map qU := by
      refine ⟨ju, ⟨hjU, hjK⟩, ?_⟩
      exact hqxj.symm
    have hqxBot : qU xu ∈ (⊥ : Subgroup (U ⧸ AU)) := by
      rw [← disjoint_iff.mp hdis]
      exact ⟨hqxHU, hqxJU⟩
    have hqxOne : qU xu = 1 := Subgroup.mem_bot.mp hqxBot
    exact (QuotientGroup.eq_one_iff xu).mp hqxOne
  · intro x hx
    exact ⟨hx.1, (Subgroup.commutator_mono le_top le_top) hx.2⟩

/-- `BGsection6.pprod_trans_coprime`, Bender--Glauberman Lemma 6.5(c).

The source conjugate `H :^ g` is represented by the image under
`MulAut.conj g⁻¹`.  Membership of `g` in the source ambient subgroup is
automatic here because that subgroup is the Lean ambient type. -/
theorem pprod_trans_coprime [K.Normal] [IsSolvable G]
    (hKU : K ⊔ U = ⊤)
    (hHU : H ≤ U)
    (hcop : (Nat.card K).Coprime (Nat.card H))
    (g : G)
    (hgU : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ U) :
    ∃ c : G, c ∈ K ⊓ Subgroup.centralizer (H : Set G) ∧
      ∃ u : G, u ∈ U ∧ g = c * u := by
  classical
  have hgprod : g ∈ (K : Set G) * (U : Set G) := by
    rw [← Subgroup.normal_mul K U, hKU]
    exact Set.mem_univ g
  rcases hgprod with ⟨k, hk, u, hu, rfl⟩
  let Hk : Subgroup G :=
    H.map (MulAut.conj k⁻¹).toMonoidHom
  have hHkU : Hk ≤ U := by
    rintro z ⟨h, hh, rfl⟩
    have hgu :
        (MulAut.conj (k * u)⁻¹).toMonoidHom h ∈ U :=
      hgU (Subgroup.mem_map_of_mem
        (MulAut.conj (k * u)⁻¹).toMonoidHom hh)
    have hback :
        u * (MulAut.conj (k * u)⁻¹).toMonoidHom h * u⁻¹ ∈ U :=
      U.mul_mem (U.mul_mem hu hgu) (U.inv_mem hu)
    simpa [MulAut.conj_apply, mul_assoc] using hback
  have hHkKH : Hk ≤ K ⊔ H := by
    rintro z ⟨h, hh, rfl⟩
    exact (K ⊔ H).mul_mem
      ((K ⊔ H).mul_mem
        ((K ⊔ H).inv_mem ((show K ≤ K ⊔ H from le_sup_left) hk))
        ((show H ≤ K ⊔ H from le_sup_right) hh))
      (by simpa using ((show K ≤ K ⊔ H from le_sup_left) hk))
  let L : Subgroup G := (K ⊔ H) ⊓ U
  have hHL : H ≤ L := fun _ hh ↦
    ⟨(show H ≤ K ⊔ H from le_sup_right) hh, hHU hh⟩
  have hHkL : Hk ≤ L := fun _ hz ↦ ⟨hHkKH hz, hHkU hz⟩
  let KL : Subgroup L := K.comap L.subtype
  let HL : Subgroup L := H.subgroupOf L
  let HkL : Subgroup L := Hk.subgroupOf L
  letI : KL.Normal := by
    dsimp [KL]
    exact Subgroup.Normal.comap (inferInstance : K.Normal) L.subtype
  have hKHdis : Disjoint K H :=
    Subgroup.disjoint_of_coprime_natCard hcop
  have hKLHLdis : Disjoint KL HL := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hKHdis]
      exact ⟨hz.1, hz.2⟩
    exact Subgroup.mem_bot.mp hzbot
  have hKLHLsup : KL ⊔ HL = ⊤ := by
    apply top_unique
    intro z _
    have hzprod : (z : G) ∈ (K : Set G) * (H : Set G) := by
      rw [← Subgroup.normal_mul K H]
      exact z.property.1
    rcases hzprod with ⟨k', hk', h', hh', hkh⟩
    have hk'U : k' ∈ U := by
      have hkeq : k' = (z : G) * h'⁻¹ := by
        rw [← hkh]
        simp
      rw [hkeq]
      exact U.mul_mem z.property.2 (U.inv_mem (hHU hh'))
    have hk'L : k' ∈ L :=
      ⟨(show K ≤ K ⊔ H from le_sup_left) hk', hk'U⟩
    have hh'L : h' ∈ L :=
      ⟨(show H ≤ K ⊔ H from le_sup_right) hh', hHU hh'⟩
    let kl : KL := ⟨⟨k', hk'L⟩, hk'⟩
    let hl : HL := ⟨⟨h', hh'L⟩, hh'⟩
    have hmul : (kl : L) * (hl : L) ∈ KL ⊔ HL :=
      Subgroup.mul_mem_sup kl.property hl.property
    have heqL : (kl : L) * (hl : L) = z :=
      Subtype.ext hkh
    rw [← heqL]
    exact hmul
  have hKLHL : KL.IsComplement' HL := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKLHLdis
    rw [← Subgroup.normal_mul KL HL, hKLHLsup]
    rfl
  have hcardHL : Nat.card HL = Nat.card H :=
    natCard_subgroupOf_eq hHL
  have hcardHkL : Nat.card HkL = Nat.card H := by
    calc
      Nat.card HkL = Nat.card Hk := natCard_subgroupOf_eq hHkL
      _ = Nat.card H := by
        dsimp [Hk]
        exact Subgroup.card_map_of_injective
          (MulAut.conj k⁻¹).injective
  have hKLmap : KL.map L.subtype ≤ K := by
    rintro x ⟨z, hz, rfl⟩
    exact hz
  have hcardKLdvd : Nat.card KL ∣ Nat.card K := by
    have hc : Nat.card (KL.map L.subtype) = Nat.card KL :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [← hc]
    exact Subgroup.card_dvd_of_le hKLmap
  have hKLHkL : KL.IsComplement' HkL := by
    apply Subgroup.isComplement'_of_coprime
    · rw [hcardHkL, ← hcardHL]
      exact hKLHL.card_mul
    · rw [hcardHkL]
      exact hcop.coprime_dvd_left hcardKLdvd
  have hcopKL : (Nat.card KL).Coprime KL.index := by
    rw [hKLHL.symm.index_eq_card, hcardHL]
    exact hcop.coprime_dvd_left hcardKLdvd
  obtain ⟨w, hw⟩ :=
    Subgroup.solvable_complement_conjugacy hcopKL hKLHL hKLHkL
  let wG : G := ((w : KL) : L)
  have hwK : wG ∈ K := w.property
  have hwU : wG ∈ U := ((w : KL) : L).property.2
  have hHkEq : Hk = H.map (MulAut.conj wG).toMonoidHom := by
    calc
      Hk = HkL.map L.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hHkL).symm
      _ = (HL.map (MulAut.conj (w : L)).toMonoidHom).map
            L.subtype := by rw [hw]
      _ = HL.map
            (L.subtype.comp (MulAut.conj (w : L)).toMonoidHom) :=
        Subgroup.map_map HL L.subtype
          (MulAut.conj (w : L)).toMonoidHom
      _ = HL.map
            ((MulAut.conj wG).toMonoidHom.comp L.subtype) := rfl
      _ = (HL.map L.subtype).map
            (MulAut.conj wG).toMonoidHom := by
        rw [Subgroup.map_map]
      _ = H.map (MulAut.conj wG).toMonoidHom := by
        rw [Subgroup.map_subgroupOf_eq_of_le hHL]
  let c : G := k * wG
  have hcMapLe : H.map (MulAut.conj c).toMonoidHom ≤ H := by
    rintro z ⟨h, hh, rfl⟩
    have hwh : (MulAut.conj wG).toMonoidHom h ∈
        H.map (MulAut.conj wG).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj wG).toMonoidHom hh
    rw [← hHkEq] at hwh
    rcases hwh with ⟨h', hh', heq⟩
    have heq' : (MulAut.conj c).toMonoidHom h = h' := by
      have hmul := congrArg (fun z : G ↦ k * z * k⁻¹) heq
      simpa [Hk, c, MulAut.conj_apply, mul_assoc] using hmul.symm
    rw [heq']
    exact hh'
  have hcMap : H.map (MulAut.conj c).toMonoidHom = H := by
    apply Subgroup.eq_of_le_of_card_ge hcMapLe
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hcK : c ∈ K := K.mul_mem hk hwK
  have hcCent : c ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
    intro h hh
    have hcommK : ⁅c, h⁆ ∈ K :=
      (Subgroup.commutator_le_left K H)
        (Subgroup.commutator_mem_commutator hcK hh)
    have hconjH : (MulAut.conj c).toMonoidHom h ∈ H :=
      hcMapLe (Subgroup.mem_map_of_mem
        (MulAut.conj c).toMonoidHom hh)
    have hcommH : ⁅c, h⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem hconjH (H.inv_mem hh)
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp hKHdis]
    exact ⟨hcommK, hcommH⟩
  let v : G := wG⁻¹ * u
  refine ⟨c, ⟨hcK, hcCent⟩, v, ?_, ?_⟩
  · exact U.mul_mem (U.inv_mem hwU) hu
  · simp [c, v, mul_assoc]

/-- `BGsection6.pprod_norm_coprime_prod`, Bender--Glauberman Lemma 6.5(b).
The product is stated as an equality of underlying sets, matching the source
group-product notation. -/
theorem pprod_norm_coprime_prod [K.Normal] [IsSolvable G]
    (hKU : K ⊔ U = ⊤)
    (hHU : H ≤ U)
    (hcop : (Nat.card K).Coprime (Nat.card H)) :
    ((K ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) *
        ((U ⊓ Subgroup.normalizer (H : Set G) : Subgroup G) : Set G) =
      (Subgroup.normalizer (H : Set G) : Set G) := by
  apply Set.Subset.antisymm
  · rintro g ⟨c, hc, u, hu, rfl⟩
    exact (Subgroup.normalizer (H : Set G)).mul_mem
      (Subgroup.centralizer_le_normalizer (H : Set G) hc.2) hu.2
  · intro g hg
    have hgU : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ U := by
      have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
        (Subgroup.normalizer (H : Set G)).inv_mem hg
      have hmap : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hginv
      rw [hmap]
      exact hHU
    obtain ⟨c, hc, u, hu, hcu⟩ :=
      pprod_trans_coprime hKU hHU hcop g hgU
    have hcNorm : c ∈ Subgroup.normalizer (H : Set G) :=
      Subgroup.centralizer_le_normalizer (H : Set G) hc.2
    have huNorm : u ∈ Subgroup.normalizer (H : Set G) := by
      have hueq : u = c⁻¹ * g := by
        rw [hcu]
        simp
      rw [hueq]
      exact (Subgroup.normalizer (H : Set G)).mul_mem
        ((Subgroup.normalizer (H : Set G)).inv_mem hcNorm) hg
    exact ⟨c, hc, u, ⟨hu, huNorm⟩, hcu.symm⟩

end Submission.OddOrder.BG.Section06
