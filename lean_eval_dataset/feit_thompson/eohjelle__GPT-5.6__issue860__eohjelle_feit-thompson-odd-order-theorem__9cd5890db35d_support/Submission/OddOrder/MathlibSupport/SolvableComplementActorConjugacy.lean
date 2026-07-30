import Mathlib.GroupTheory.SchurZassenhaus
import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.ComplementQuotient
import Submission.OddOrder.MathlibSupport.MinimalNormalExistence
import Submission.OddOrder.MathlibSupport.MinimalNormal
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# Schur--Zassenhaus conjugacy with solvable complement

`SolvableComplementConjugacy` supplies the conjugacy half of
Schur--Zassenhaus when the normal Hall factor is solvable.  The other branch,
needed by Peterfalvi's quotient argument, assumes instead that the complement
(equivalently, the quotient) is solvable.

The proof inducts on the complement.  A minimal normal `p`-subgroup of the
complement is first aligned in the two complements by Sylow conjugacy.  Both
complements then lie in its normalizer; factoring out the aligned subgroup
strictly lowers the complement order and gives the induction step.
-/

namespace Subgroup

open Submission.OddOrder.MathlibSupport
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]
variable {N B C : Subgroup G} [N.Normal]

private theorem IsComplement'.quotientMap_surjective_on_right
    (h : N.IsComplement' B) :
    Function.Surjective
      ((QuotientGroup.mk' N).comp B.subtype) := by
  intro z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
  obtain ⟨nb, hnb, _⟩ := h.existsUnique g
  refine ⟨nb.2, ?_⟩
  change QuotientGroup.mk' N (nb.2 : G) = QuotientGroup.mk' N g
  rw [← hnb, map_mul]
  have hn : QuotientGroup.mk' N (nb.1 : G) = 1 :=
    QuotientGroup.eq_one_iff (nb.1 : G) |>.mpr nb.1.property
  rw [hn, one_mul]

/-- A complement maps isomorphically to the quotient by the normal factor. -/
private noncomputable def IsComplement'.rightQuotientMulEquiv
    (h : N.IsComplement' B) : B ≃* (G ⧸ N) :=
  MulEquiv.ofBijective ((QuotientGroup.mk' N).comp B.subtype)
    ⟨h.quotientMap_injective_on_right le_rfl,
      h.quotientMap_surjective_on_right⟩

@[simp]
private theorem IsComplement'.rightQuotientMulEquiv_apply
    (h : N.IsComplement' B) (b : B) :
    h.rightQuotientMulEquiv b = QuotientGroup.mk' N (b : G) :=
  by
    change ((QuotientGroup.mk' N).comp B.subtype) b = _
    rfl

private theorem map_conj_map_conj (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Conjugating the right complement by an element of the normal factor
again gives a right complement. -/
private theorem IsComplement'.conj_right_of_mem_left
    (h : N.IsComplement' B) (n : N) :
    N.IsComplement'
      (B.map (MulAut.conj (n : G)).toMonoidHom) := by
  let Bn : Subgroup G := B.map (MulAut.conj (n : G)).toMonoidHom
  have hcardBn : Nat.card Bn = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective
  have hcard : Nat.card N * Nat.card Bn = Nat.card G := by
    rw [hcardBn]
    exact h.card_mul
  have hNmap :
      N.map (MulAut.conj (n : G)).toMonoidHom = N :=
    Subgroup.Normal.map_conj_eq N (n : G)
  have hdis : Disjoint N Bn := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    rcases hz.2 with ⟨b, hb, hbz⟩
    have hzNmap : z ∈ N.map (MulAut.conj (n : G)).toMonoidHom := by
      rw [hNmap]
      exact hz.1
    rcases hzNmap with ⟨a, ha, haz⟩
    have hab : a = b :=
      (MulAut.conj (n : G)).injective (haz.trans hbz.symm)
    have hbN : b ∈ N := hab ▸ ha
    have hbBot : b ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp h.disjoint]
      exact ⟨hbN, hb⟩
    apply Subgroup.mem_bot.mpr
    rw [← hbz, Subgroup.mem_bot.mp hbBot, map_one]
  exact Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdis

/-- Restricting a complement decomposition to a subgroup that contains the
right factor preserves the decomposition. -/
private theorem IsComplement'.subgroupOf_of_right_le
    (h : N.IsComplement' B) {S : Subgroup G} (hBS : B ≤ S) :
    (N.subgroupOf S).IsComplement' (B.subgroupOf S) := by
  let NS : Subgroup S := N.subgroupOf S
  let BS : Subgroup S := B.subgroupOf S
  letI : NS.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : N.Normal) S
  have hdis : Disjoint NS BS := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp h.disjoint]
    exact hz
  have hsup : NS ⊔ BS = ⊤ := by
    apply top_unique
    intro s _
    obtain ⟨nb, hnb, _⟩ := h.existsUnique (s : G)
    have hbS : (nb.2 : G) ∈ S := hBS nb.2.property
    have hnS : (nb.1 : G) ∈ S := by
      have hnEq : (nb.1 : G) = (s : G) * (nb.2 : G)⁻¹ := by
        rw [← hnb]
        group
      rw [hnEq]
      exact S.mul_mem s.property (S.inv_mem hbS)
    let nS : NS := ⟨⟨(nb.1 : G), hnS⟩, nb.1.property⟩
    let bS : BS := ⟨⟨(nb.2 : G), hbS⟩, nb.2.property⟩
    have hmul : (nS : S) * (bS : S) ∈ NS ⊔ BS :=
      Subgroup.mul_mem_sup nS.property bS.property
    have hmulEq : (nS : S) * (bS : S) = s :=
      Subtype.ext hnb
    rwa [← hmulEq]
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  rw [← Subgroup.normal_mul NS BS, hsup]
  rfl

/-- Quotienting by a normal subgroup of the right complement preserves the
two complementary images. -/
private theorem IsComplement'.quotient_isComplement_right
    (h : N.IsComplement' B) {P : Subgroup G} [P.Normal]
    (hPB : P ≤ B) :
    (N.map (QuotientGroup.mk' P)).IsComplement'
      (B.map (QuotientGroup.mk' P)) := by
  let q : G →* G ⧸ P := QuotientGroup.mk' P
  let Nq : Subgroup (G ⧸ P) := N.map q
  let Bq : Subgroup (G ⧸ P) := B.map q
  letI : Nq.Normal :=
    Subgroup.Normal.map (inferInstance : N.Normal) q
      (QuotientGroup.mk'_surjective P)
  have hsup : Nq ⊔ Bq = ⊤ := by
    dsimp [Nq, Bq]
    rw [← Subgroup.map_sup, h.sup_eq_top,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective P)]
  have hdis : Disjoint Nq Bq := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro z hz
    rcases hz.1 with ⟨n, hn, hnz⟩
    rcases hz.2 with ⟨b, hb, hbz⟩
    have hqeq : q n = q b := hnz.trans hbz.symm
    have hdiffP : n⁻¹ * b ∈ P := QuotientGroup.eq.mp hqeq
    have hdiffB : n⁻¹ * b ∈ B := hPB hdiffP
    have hnB : n ∈ B := by
      rw [show n = b * (n⁻¹ * b)⁻¹ by group]
      exact B.mul_mem hb (B.inv_mem hdiffB)
    have hnOne : n = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp h.disjoint]
      exact ⟨hn, hnB⟩
    apply Subgroup.mem_bot.mpr
    rw [← hnz, hnOne, map_one]
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  rw [← Subgroup.normal_mul Nq Bq, hsup]
  rfl

private theorem natCard_map_quotient_lt_of_ne_bot_of_le
    {P H : Subgroup G} [P.Normal] (hPH : P ≤ H) (hP : P ≠ ⊥) :
    Nat.card (H.map (QuotientGroup.mk' P)) < Nat.card H := by
  let q : G →* G ⧸ P := QuotientGroup.mk' P
  let f : H →* H.map q := q.subgroupMap H
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (H.map q) := Fintype.ofFinite (H.map q)
  have hsurj : Function.Surjective f := q.subgroupMap_surjective H
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    obtain ⟨p, hp⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP
    have hfp : f ⟨p, hPH p.property⟩ = f 1 := by
      apply Subtype.ext
      change q (p : G) = q 1
      rw [map_one]
      exact QuotientGroup.eq_one_iff (p : G) |>.mpr p.property
    have hpOne : (⟨p, hPH p.property⟩ : H) = 1 := hinj hfp
    apply hp
    apply Subtype.ext
    exact congrArg (fun x : H ↦ (x : G)) hpOne
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_surjective_not_injective f hsurj hnotinj

/-- Complements to a normal Hall subgroup are conjugate by an element of the
normal factor when the complement is solvable. -/
theorem solvable_right_complement_conjugacy [IsSolvable B]
    (hcop : (Nat.card N).Coprime N.index)
    (hB : N.IsComplement' B) (hC : N.IsComplement' C) :
    ∃ n : N, C = B.map (MulAut.conj (n : G)).toMonoidHom := by
  classical
  let motive : ℕ → Prop := fun n ↦
    ∀ (G' : Type u) [Group G'] [Finite G']
      (N' B' C' : Subgroup G') [N'.Normal] [IsSolvable B'],
      Nat.card B' = n →
      (Nat.card N').Coprime N'.index →
      N'.IsComplement' B' → N'.IsComplement' C' →
      ∃ x : N', C' = B'.map (MulAut.conj (x : G')).toMonoidHom
  have hmain : ∀ n, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp only [motive]
      intro G' _ _ N' B' C' _ _ hcard hcop' hB' hC'
      have hcopNB : (Nat.card N').Coprime (Nat.card B') := by
        rw [← hB'.symm.index_eq_card]
        exact hcop'
      by_cases hBbot : B' = ⊥
      · have hcardC : Nat.card C' = Nat.card B' := by
          have hmul : Nat.card N' * Nat.card C' =
              Nat.card N' * Nat.card B' :=
            hC'.card_mul.trans hB'.card_mul.symm
          exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := N')) hmul
        have hCbot : C' = ⊥ := by
          apply Subgroup.eq_bot_of_card_eq
          rw [hcardC, hBbot]
          exact Subgroup.card_bot
        refine ⟨1, ?_⟩
        simp [hBbot, hCbot]
      · letI : Nontrivial B' :=
          (Subgroup.nontrivial_iff_ne_bot B').mpr hBbot
        obtain ⟨P, hPmin, -⟩ :=
          exists_minimalNormal_le (G := B') (K := (⊤ : Subgroup B'))
            (by infer_instance) top_ne_bot
        letI : P.Normal := hPmin.normal
        obtain ⟨p, hp, hPp⟩ := hPmin.exists_prime_isPGroup
        letI : Fact p.Prime := ⟨hp⟩

        let qN : G' →* G' ⧸ N' := QuotientGroup.mk' N'
        let eB : B' ≃* (G' ⧸ N') := hB'.rightQuotientMulEquiv
        let eC : C' ≃* (G' ⧸ N') := hC'.rightQuotientMulEquiv
        let e : B' ≃* C' := eB.trans eC.symm
        have heqQ (b : B') : qN (e b : G') = qN (b : G') := by
          change eC (e b) = eB b
          simp [e]

        let PB : Subgroup G' := P.map B'.subtype
        let PC₀ : Subgroup C' := P.map e.toMonoidHom
        letI : PC₀.Normal :=
          Subgroup.Normal.map (inferInstance : P.Normal) e.toMonoidHom
            e.surjective
        let PC : Subgroup G' := PC₀.map C'.subtype
        have hPBB : PB ≤ B' := Subgroup.map_subtype_le P
        have hPCC : PC ≤ C' := Subgroup.map_subtype_le PC₀
        have hBnormPB : B' ≤ Subgroup.normalizer (PB : Set G') := by
          intro b hb
          apply Subgroup.le_normalizer_map B'.subtype
          refine ⟨⟨b, hb⟩, ?_, rfl⟩
          rw [Subgroup.normalizer_eq_top_iff.mpr
            (inferInstance : P.Normal)]
          exact Subgroup.mem_top _
        have hCnormPC : C' ≤ Subgroup.normalizer (PC : Set G') := by
          intro c hc
          apply Subgroup.le_normalizer_map C'.subtype
          refine ⟨⟨c, hc⟩, ?_, rfl⟩
          rw [Subgroup.normalizer_eq_top_iff.mpr
            (inferInstance : PC₀.Normal)]
          exact Subgroup.mem_top _
        have hcardPB : Nat.card PB = Nat.card P :=
          Subgroup.card_map_of_injective B'.subtype_injective
        have hcardPC₀ : Nat.card PC₀ = Nat.card P :=
          Subgroup.card_map_of_injective e.injective
        have hcardPC : Nat.card PC = Nat.card P := by
          rw [show Nat.card PC = Nat.card PC₀ from
            Subgroup.card_map_of_injective C'.subtype_injective,
            hcardPC₀]
        have hPBp : IsPGroup p PB := hPp.map B'.subtype
        have hPC₀p : IsPGroup p PC₀ := hPp.map e.toMonoidHom
        have hPCp : IsPGroup p PC := hPC₀p.map C'.subtype

        let H : Subgroup G' := N' ⊔ PB
        have hNH : N' ≤ H := le_sup_left
        have hPBH : PB ≤ H := le_sup_right
        have hPCH : PC ≤ H := by
          rintro c ⟨c₀, hc₀, rfl⟩
          rcases hc₀ with ⟨b, hb, rfl⟩
          have hqeq : qN ((e b : C') : G') = qN (b : G') := heqQ b
          have hdiff : (b : G')⁻¹ * ((e b : C') : G') ∈ N' :=
            QuotientGroup.eq.mp hqeq.symm
          change ((e b : C') : G') ∈ N' ⊔ PB
          rw [show ((e b : C') : G') =
              (b : G') * ((b : G')⁻¹ * ((e b : C') : G')) by group]
          exact (N' ⊔ PB).mul_mem
            ((show PB ≤ N' ⊔ PB from le_sup_right)
              (show (b : G') ∈ PB from ⟨b, hb, rfl⟩))
            ((show N' ≤ N' ⊔ PB from le_sup_left) hdiff)
        let NH : Subgroup H := N'.subgroupOf H
        let PBH : Subgroup H := PB.subgroupOf H
        let PCH : Subgroup H := PC.subgroupOf H
        letI : NH.Normal :=
          Subgroup.Normal.subgroupOf (inferInstance : N'.Normal) H
        have hNHPB : NH.IsComplement' PBH := by
          letI : NH.Normal := inferInstance
          have hdis : Disjoint NH PBH := by
            rw [disjoint_iff]
            apply le_antisymm _ bot_le
            intro z hz
            apply Subgroup.mem_bot.mpr
            apply Subtype.ext
            apply Subgroup.mem_bot.mp
            rw [← disjoint_iff.mp
              (Disjoint.mono le_rfl hPBB hB'.disjoint)]
            exact hz
          have hsup : NH ⊔ PBH = ⊤ := by
            rw [← Subgroup.subgroupOf_sup hNH hPBH]
            exact Subgroup.subgroupOf_self H
          apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
          rw [← Subgroup.normal_mul NH PBH, hsup]
          rfl
        have hcardNH : Nat.card NH = Nat.card N' :=
          natCard_subgroupOf_eq hNH
        have hcardPBH : Nat.card PBH = Nat.card P := by
          rw [natCard_subgroupOf_eq hPBH, hcardPB]
        have hcardPCH : Nat.card PCH = Nat.card P := by
          rw [natCard_subgroupOf_eq hPCH, hcardPC]
        have hcardPdvdB : Nat.card P ∣ Nat.card B' := by
          simpa using Subgroup.card_dvd_of_le
            (show P ≤ (⊤ : Subgroup B') from le_top)
        have hcopNP : (Nat.card N').Coprime (Nat.card P) :=
          hcopNB.coprime_dvd_right hcardPdvdB
        have hNPCHcop : (Nat.card NH).Coprime (Nat.card PCH) := by
          simpa only [hcardNH, hcardPCH] using hcopNP
        have hNHPc : NH.IsComplement' PCH := by
          apply Subgroup.isComplement'_of_coprime
          · rw [hcardPCH, ← hcardPBH]
            exact hNHPB.card_mul
          · exact hNPCHcop
        have hPBHp : IsPGroup p PBH :=
          hPBp.of_equiv (Subgroup.subgroupOfEquivOfLe hPBH).symm
        have hPCHp : IsPGroup p PCH :=
          hPCp.of_equiv (Subgroup.subgroupOfEquivOfLe hPCH).symm
        obtain ⟨a, hcardP⟩ := hPp.exists_card_eq
        have ha : a ≠ 0 := by
          intro ha0
          subst a
          have hPcardOne : Nat.card P = 1 := by simpa using hcardP
          exact hPmin.ne_bot (P.eq_bot_of_card_eq hPcardOne)
        have hpdvdP : p ∣ Nat.card P := by
          rw [hcardP]
          exact dvd_pow_self p ha
        have hpNotN : ¬ p ∣ Nat.card N' := by
          intro hpN
          exact (Nat.Prime.not_coprime_iff_dvd.mpr
            ⟨p, hp, hpN, hpdvdP⟩) hcopNP
        have hpNotPBHIndex : ¬ p ∣ PBH.index := by
          rw [hNHPB.index_eq_card, hcardNH]
          exact hpNotN
        have hpNotPCHIndex : ¬ p ∣ PCH.index := by
          rw [hNHPc.index_eq_card, hcardNH]
          exact hpNotN
        let SPB : Sylow p H := hPBHp.toSylow hpNotPBHIndex
        let SPC : Sylow p H := hPCHp.toSylow hpNotPCHIndex
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H SPB SPC
        have hPCHconj :
            PCH = PBH.map (MulAut.conj g).toMonoidHom := by
          change (SPC : Subgroup H) =
            (SPB : Subgroup H).map (MulAut.conj g).toMonoidHom
          rw [← hg]
          rfl
        obtain ⟨nb, hnb, _⟩ := hNHPB.existsUnique g
        have hPBmap :
            PBH.map (MulAut.conj (nb.2 : H)).toMonoidHom = PBH :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp
            (PBH.le_normalizer nb.2.property)
        have hPCHnH :
            PCH = PBH.map (MulAut.conj (nb.1 : H)).toMonoidHom := by
          calc
            PCH = PBH.map (MulAut.conj g).toMonoidHom := hPCHconj
            _ = PBH.map
                (MulAut.conj ((nb.1 : H) * (nb.2 : H))).toMonoidHom := by
                  rw [hnb]
            _ = (PBH.map (MulAut.conj (nb.2 : H)).toMonoidHom).map
                (MulAut.conj (nb.1 : H)).toMonoidHom := by
                  rw [map_conj_map_conj]
            _ = PBH.map (MulAut.conj (nb.1 : H)).toMonoidHom := by
              rw [hPBmap]
        let n₀ : N' := ⟨(((nb.1 : NH) : H) : G'), nb.1.property⟩
        have hPCn₀ :
            PC = PB.map (MulAut.conj (n₀ : G')).toMonoidHom := by
          calc
            PC = PCH.map H.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hPCH).symm
            _ = (PBH.map
                (MulAut.conj (nb.1 : H)).toMonoidHom).map H.subtype := by
                  rw [hPCHnH]
            _ = (PBH.map H.subtype).map
                (MulAut.conj (n₀ : G')).toMonoidHom := by
                  rw [Subgroup.map_map, Subgroup.map_map]
                  rfl
            _ = PB.map (MulAut.conj (n₀ : G')).toMonoidHom := by
              rw [Subgroup.map_subgroupOf_eq_of_le hPBH]

        let Cx : Subgroup G' :=
          C'.map (MulAut.conj (n₀ : G')⁻¹).toMonoidHom
        have hCxcomp : N'.IsComplement' Cx := by
          exact hC'.conj_right_of_mem_left ⟨(n₀ : G')⁻¹,
            N'.inv_mem n₀.property⟩
        have hPCx :
            PC.map (MulAut.conj (n₀ : G')⁻¹).toMonoidHom = PB := by
          rw [hPCn₀]
          change (MulAut.conj (n₀ : G')⁻¹) •
            ((MulAut.conj (n₀ : G')) • PB) = PB
          rw [← mul_smul]
          simp
        have hPBCx : PB ≤ Cx := by
          rw [← hPCx]
          exact Subgroup.map_mono hPCC
        have hCxnormPB : Cx ≤ Subgroup.normalizer (PB : Set G') := by
          have hmapped :
              C'.map (MulAut.conj (n₀ : G')⁻¹).toMonoidHom ≤
                (Subgroup.normalizer (PC : Set G')).map
                  (MulAut.conj (n₀ : G')⁻¹).toMonoidHom :=
            Subgroup.map_mono hCnormPC
          rw [Subgroup.map_equiv_normalizer_eq PC
            (MulAut.conj (n₀ : G')⁻¹), hPCx] at hmapped
          exact hmapped

        let S : Subgroup G' := Subgroup.normalizer (PB : Set G')
        have hBS : B' ≤ S := hBnormPB
        have hCxS : Cx ≤ S := hCxnormPB
        let NS : Subgroup S := N'.subgroupOf S
        let BS : Subgroup S := B'.subgroupOf S
        let CS : Subgroup S := Cx.subgroupOf S
        letI : NS.Normal :=
          Subgroup.Normal.subgroupOf (inferInstance : N'.Normal) S
        have hNSBS : NS.IsComplement' BS :=
          hB'.subgroupOf_of_right_le hBS
        have hNSCS : NS.IsComplement' CS :=
          hCxcomp.subgroupOf_of_right_le hCxS
        have hPBs : PB ≤ S := Subgroup.le_normalizer
        let PS : Subgroup S := PB.subgroupOf S
        have hPSnormal : PS.Normal := by
          apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPBs).mpr
          exact le_rfl
        letI : PS.Normal := hPSnormal
        have hPBne : PB ≠ ⊥ := by
          intro hPBbot
          apply hPmin.ne_bot
          exact (Subgroup.map_eq_bot_iff_of_injective
            P B'.subtype_injective).mp hPBbot
        have hPSne : PS ≠ ⊥ := by
          intro hPSbot
          apply hPBne
          have hmapped := congrArg (Subgroup.map S.subtype) hPSbot
          rw [Subgroup.map_bot,
            Subgroup.map_subgroupOf_eq_of_le hPBs] at hmapped
          exact hmapped
        have hPSBS : PS ≤ BS := by
          intro x hx
          exact hPBB hx
        have hPSCS : PS ≤ CS := by
          intro x hx
          exact hPBCx hx

        let qP : S →* S ⧸ PS := QuotientGroup.mk' PS
        let NSq : Subgroup (S ⧸ PS) := NS.map qP
        let BSq : Subgroup (S ⧸ PS) := BS.map qP
        let CSq : Subgroup (S ⧸ PS) := CS.map qP
        letI : NSq.Normal :=
          Subgroup.Normal.map (inferInstance : NS.Normal) qP
            (QuotientGroup.mk'_surjective PS)
        have hNSqBSq : NSq.IsComplement' BSq :=
          hNSBS.quotient_isComplement_right hPSBS
        have hNSqCSq : NSq.IsComplement' CSq :=
          hNSCS.quotient_isComplement_right hPSCS
        have hBSsolv : IsSolvable BS :=
          solvable_of_solvable_injective
            (f := (Subgroup.subgroupOfEquivOfLe hBS).toMonoidHom)
            (Subgroup.subgroupOfEquivOfLe hBS).injective
        letI : IsSolvable BS := hBSsolv
        letI : IsSolvable BSq :=
          solvable_of_surjective (f := qP.subgroupMap BS)
            (qP.subgroupMap_surjective BS)
        have hcardBS : Nat.card BS = Nat.card B' :=
          natCard_subgroupOf_eq hBS
        have hBSqLt : Nat.card BSq < n := by
          rw [← hcard, ← hcardBS]
          exact natCard_map_quotient_lt_of_ne_bot_of_le hPSBS hPSne
        have hNSdivN : Nat.card NS ∣ Nat.card N' := by
          have hmapCard : Nat.card (NS.map S.subtype) = Nat.card NS :=
            Subgroup.card_map_of_injective S.subtype_injective
          have hmapLe : NS.map S.subtype ≤ N' := by
            rintro _ ⟨x, hx, rfl⟩
            exact hx
          rw [← hmapCard]
          exact Subgroup.card_dvd_of_le hmapLe
        have hBSdivB : Nat.card BS ∣ Nat.card B' := by
          rw [hcardBS]
        have hNSqdivN : Nat.card NSq ∣ Nat.card N' :=
          (Subgroup.card_map_dvd NS qP).trans hNSdivN
        have hBSqdivB : Nat.card BSq ∣ Nat.card B' :=
          (Subgroup.card_map_dvd BS qP).trans hBSdivB
        have hcopqCards :
            (Nat.card NSq).Coprime (Nat.card BSq) :=
          (hcopNB.coprime_dvd_left hNSqdivN).coprime_dvd_right hBSqdivB
        have hcopq : (Nat.card NSq).Coprime NSq.index := by
          rw [hNSqBSq.symm.index_eq_card]
          exact hcopqCards
        obtain ⟨nq, hnq⟩ :=
          ih (Nat.card BSq) hBSqLt (S ⧸ PS) NSq BSq CSq rfl
            hcopq hNSqBSq hNSqCSq
        rcases nq.property with ⟨s, hsNS, hsmap⟩
        let ns : NS := ⟨s, hsNS⟩
        have hmapConj :
            (BS.map (MulAut.conj (s : S)).toMonoidHom).map qP =
              BSq.map (MulAut.conj (nq : S ⧸ PS)).toMonoidHom := by
          dsimp [BSq]
          rw [Subgroup.map_map, Subgroup.map_map]
          congr 1
          ext b
          simp [MulAut.conj_apply, hsmap]
        have hCSconj :
            CS = BS.map (MulAut.conj (s : S)).toMonoidHom := by
          apply Subgroup.map_injective_of_ker_le qP
          · rw [QuotientGroup.ker_mk']
            exact hPSCS
          · rw [QuotientGroup.ker_mk']
            have hPSmap :
                PS.map (MulAut.conj (s : S)).toMonoidHom = PS :=
              Subgroup.Normal.map_conj_eq PS (s : S)
            rw [← hPSmap]
            exact Subgroup.map_mono hPSBS
          · change CSq =
              (BS.map (MulAut.conj (s : S)).toMonoidHom).map qP
            exact hnq.trans hmapConj.symm
        let n₁ : N' := ⟨((s : S) : G'), hsNS⟩
        have hCxEq :
            Cx = B'.map (MulAut.conj (n₁ : G')).toMonoidHom := by
          calc
            Cx = CS.map S.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hCxS).symm
            _ = (BS.map (MulAut.conj (s : S)).toMonoidHom).map
                S.subtype := by rw [hCSconj]
            _ = (BS.map S.subtype).map
                (MulAut.conj (n₁ : G')).toMonoidHom := by
                  rw [Subgroup.map_map, Subgroup.map_map]
                  rfl
            _ = B'.map (MulAut.conj (n₁ : G')).toMonoidHom := by
              rw [Subgroup.map_subgroupOf_eq_of_le hBS]
        let out : N' := n₀ * n₁
        refine ⟨out, ?_⟩
        have hCxBack :
            Cx.map (MulAut.conj (n₀ : G')).toMonoidHom = C' := by
          change (MulAut.conj (n₀ : G')) •
            ((MulAut.conj (n₀ : G')⁻¹) • C') = C'
          rw [← mul_smul]
          simp
        calc
          C' = Cx.map (MulAut.conj (n₀ : G')).toMonoidHom :=
            hCxBack.symm
          _ = (B'.map (MulAut.conj (n₁ : G')).toMonoidHom).map
              (MulAut.conj (n₀ : G')).toMonoidHom := by rw [hCxEq]
          _ = B'.map (MulAut.conj (out : G')).toMonoidHom := by
            rw [map_conj_map_conj]
            rfl
  exact hmain (Nat.card B) G N B C rfl hcop hB hC

end Subgroup

namespace Submission.OddOrder.MathlibSupport

universe u

/-- In a finite group, quotienting by a normal subgroup coprime to a
solvable subgroup carries its centralizer onto the centralizer of its image.

This is the solvable-actor branch of MathComp's
`strongest_coprime_quotient_cent`. -/
theorem map_centralizer_quotient_eq_of_coprime_of_solvable_right
    {G : Type u} [Group G] [Finite G]
    {N R : Subgroup G} [N.Normal] [IsSolvable R]
    (hcop : Nat.Coprime (Nat.card N) (Nat.card R)) :
    (Subgroup.centralizer (R : Set G)).map (QuotientGroup.mk' N) =
      Subgroup.centralizer
        (R.map (QuotientGroup.mk' N) : Set (G ⧸ N)) := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨r, hr, rfl⟩
    exact congrArg q (Subgroup.mem_centralizer_iff.mp hc r hr)
  · intro z hz
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
    let Rg : Subgroup G := R.map (MulAut.conj g).toMonoidHom
    have hRgL : Rg ≤ N ⊔ R := by
      rintro _ ⟨r, hr, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp hz (q r)
        (Subgroup.mem_map_of_mem q hr)
      change q r * q g = q g * q r at hcomm
      have hqeq : q (g * r * g⁻¹) = q r := by
        change q g * q r * (q g)⁻¹ = q r
        rw [← hcomm]
        group
      have hker : (g * r * g⁻¹)⁻¹ * r ∈ N :=
        QuotientGroup.eq.mp hqeq
      change g * r * g⁻¹ ∈ N ⊔ R
      rw [show g * r * g⁻¹ =
          r * ((g * r * g⁻¹)⁻¹ * r)⁻¹ by group]
      exact (N ⊔ R).mul_mem
        ((show R ≤ N ⊔ R from le_sup_right) hr)
        ((show N ≤ N ⊔ R from le_sup_left) (N.inv_mem hker))
    let L : Subgroup G := N ⊔ R
    let NL : Subgroup L := N.subgroupOf L
    let RL : Subgroup L := R.subgroupOf L
    let RgL : Subgroup L := Rg.subgroupOf L
    letI : NL.Normal :=
      Subgroup.Normal.subgroupOf (inferInstance : N.Normal) L
    have hcardNL : Nat.card NL = Nat.card N :=
      natCard_subgroupOf_eq le_sup_left
    have hcardRL : Nat.card RL = Nat.card R :=
      natCard_subgroupOf_eq le_sup_right
    have hdisNR : Disjoint N R :=
      Subgroup.disjoint_of_coprime_natCard hcop
    have hdisNLRL : Disjoint NL RL := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro x hx
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hdisNR]
      exact hx
    have hsupNLRL : NL ⊔ RL = ⊤ := by
      change N.subgroupOf L ⊔ R.subgroupOf L = ⊤
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      exact Subgroup.subgroupOf_self L
    have hcompRL : NL.IsComplement' RL := by
      apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisNLRL
      rw [← Subgroup.normal_mul NL RL, hsupNLRL]
      rfl
    have hcardRg : Nat.card Rg = Nat.card R :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hcardRgL : Nat.card RgL = Nat.card RL := by
      rw [natCard_subgroupOf_eq hRgL, hcardRg,
        natCard_subgroupOf_eq le_sup_right]
    have hcompRgL : NL.IsComplement' RgL := by
      apply Subgroup.isComplement'_of_coprime
      · rw [hcardRgL]
        exact hcompRL.card_mul
      · rw [hcardNL, hcardRgL, hcardRL]
        exact hcop
    have hcopNLindex : Nat.Coprime (Nat.card NL) NL.index := by
      rw [hcompRL.symm.index_eq_card, hcardNL, hcardRL]
      exact hcop
    have hRLsolv : IsSolvable RL :=
      solvable_of_solvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe
          (show R ≤ L from le_sup_right)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe
          (show R ≤ L from le_sup_right)).injective
    letI : IsSolvable RL := hRLsolv
    obtain ⟨n, hn⟩ :=
      Subgroup.solvable_right_complement_conjugacy
        hcopNLindex hcompRL hcompRgL
    let nG : G := ((n : NL) : L)
    have hnN : nG ∈ N := n.property
    let c : G := nG⁻¹ * g
    have hconjR (r : G) (hr : r ∈ R) : c * r * c⁻¹ ∈ R := by
      have hxRg : g * r * g⁻¹ ∈ Rg := ⟨r, hr, rfl⟩
      let xL : L := ⟨g * r * g⁻¹, hRgL hxRg⟩
      have hxRgL : xL ∈ RgL := hxRg
      rw [hn] at hxRgL
      rcases hxRgL with ⟨s, hs, hns⟩
      have hnsG : nG * (s : G) * nG⁻¹ = g * r * g⁻¹ :=
        congrArg (fun y : L ↦ (y : G)) hns
      rw [show c * r * c⁻¹ = (s : G) by
        dsimp [c]
        calc
          nG⁻¹ * g * r * (nG⁻¹ * g)⁻¹ =
              nG⁻¹ * (g * r * g⁻¹) * nG := by group
          _ = nG⁻¹ * (nG * (s : G) * nG⁻¹) * nG := by rw [← hnsG]
          _ = (s : G) := by group]
      exact hs
    have hqn : q nG = 1 := QuotientGroup.eq_one_iff nG |>.mpr hnN
    have hqc : q c = q g := by simp [c, hqn]
    refine ⟨c, ?_, hqc⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro r hr
    have hcr : c * r * c⁻¹ ∈ R := hconjR r hr
    have hcomm := Subgroup.mem_centralizer_iff.mp hz (q r)
      (Subgroup.mem_map_of_mem q hr)
    change q r * q g = q g * q r at hcomm
    have hqeq : q (c * r * c⁻¹) = q r := by
      change q c * q r * (q c)⁻¹ = q r
      rw [hqc, ← hcomm]
      group
    have hdiffN : (c * r * c⁻¹)⁻¹ * r ∈ N :=
      QuotientGroup.eq.mp hqeq
    have hdiffR : (c * r * c⁻¹)⁻¹ * r ∈ R :=
      R.mul_mem (R.inv_mem hcr) hr
    have hdiffOne : (c * r * c⁻¹)⁻¹ * r = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hdisNR]
      exact ⟨hdiffN, hdiffR⟩
    have hconjEq : c * r * c⁻¹ = r :=
      inv_mul_eq_one.mp hdiffOne
    symm
    calc
      c * r = (c * r * c⁻¹) * c := by group
      _ = r * c := by rw [hconjEq]

/-- Internal-centralizer form of
`map_centralizer_quotient_eq_of_coprime_of_solvable_right`. -/
theorem map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
    {G : Type u} [Group G] [Finite G]
    {N Y R : Subgroup G} [N.Normal] [IsSolvable R]
    (hNY : N ≤ Y)
    (hcop : Nat.Coprime (Nat.card N) (Nat.card R)) :
    (centralizerWithin Y R).map (QuotientGroup.mk' N) =
      centralizerWithin (Y.map (QuotientGroup.mk' N))
        (R.map (QuotientGroup.mk' N)) := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hcent :=
    map_centralizer_quotient_eq_of_coprime_of_solvable_right hcop
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    refine ⟨⟨c, hc.1, rfl⟩, ?_⟩
    have hcmap : q c ∈
        (Subgroup.centralizer (R : Set G)).map q :=
      ⟨c, hc.2, rfl⟩
    rwa [hcent] at hcmap
  · intro z hz
    have hzCent : z ∈
        (Subgroup.centralizer (R : Set G)).map q := by
      rw [hcent]
      exact hz.2
    rcases hzCent with ⟨c, hcCent, hcz⟩
    rcases hz.1 with ⟨y, hy, hyz⟩
    have hqeq : q c = q y := hcz.trans hyz.symm
    have hdiff : c⁻¹ * y ∈ N := QuotientGroup.eq.mp hqeq
    have hcY : c ∈ Y := by
      rw [show c = y * (c⁻¹ * y)⁻¹ by group]
      exact Y.mul_mem hy (Y.inv_mem (hNY hdiff))
    exact ⟨c, ⟨hcY, hcCent⟩, hcz⟩

end Submission.OddOrder.MathlibSupport
