import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.GroupTheory.Solvable
import Submission.OddOrder.MathlibSupport.ComplementQuotient
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
Conjugacy of complements to solvable normal Hall subgroups.

Mathlib's Schur--Zassenhaus file currently supplies the existence half.  The
conjugacy half needed by Bender--Glauberman Lemma 6.5 is proved here.  The
abelian step uses the transversal action already constructed in mathlib; the
general result inducts through the commutator subgroup of the normal factor.
-/

namespace Subgroup

open MulOpposite MulAction leftTransversals
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]
variable {N B C : Subgroup G} [N.Normal]

/-- Complements to an abelian normal Hall subgroup are conjugate by an
element of the normal subgroup. -/
theorem abelian_complement_conjugacy [IsMulCommutative N]
    (hcop : (Nat.card N).Coprime N.index)
    (hB : N.IsComplement' B) (hC : N.IsComplement' C) :
    ∃ n : N, C = B.map (MulAut.conj (n : G)).toMonoidHom := by
  let αB : N.LeftTransversal := ⟨(B : Set G), hB.symm⟩
  let αC : N.LeftTransversal := ⟨(C : Set G), hC.symm⟩
  let aB : N.QuotientDiff := Quotient.mk'' αB
  let aC : N.QuotientDiff := Quotient.mk'' αC
  have hBfix (b : B) : (b : G) • aB = aB := by
    change Quotient.mk'' (op ((b : G)⁻¹) • αB) = Quotient.mk'' αB
    apply congrArg Quotient.mk''
    apply Subtype.ext
    have hop : op ((b : G)⁻¹) ∈
        MulAction.stabilizer Gᵐᵒᵖ (B : Set G) := by
      rw [stabilizer_op_subgroup]
      exact B.inv_mem b.property
    exact MulAction.mem_stabilizer_iff.mp hop
  have hCfix (c : C) : (c : G) • aC = aC := by
    change Quotient.mk'' (op ((c : G)⁻¹) • αC) = Quotient.mk'' αC
    apply congrArg Quotient.mk''
    apply Subtype.ext
    have hop : op ((c : G)⁻¹) ∈
        MulAction.stabilizer Gᵐᵒᵖ (C : Set G) := by
      rw [stabilizer_op_subgroup]
      exact C.inv_mem c.property
    exact MulAction.mem_stabilizer_iff.mp hop
  have hBcomp : N.IsComplement' (MulAction.stabilizer G aB) :=
    isComplement'_stabilizer_of_coprime hcop
  have hCcomp : N.IsComplement' (MulAction.stabilizer G aC) :=
    isComplement'_stabilizer_of_coprime hcop
  have hBle : B ≤ MulAction.stabilizer G aB := by
    intro b hb
    exact MulAction.mem_stabilizer_iff.mpr (hBfix ⟨b, hb⟩)
  have hCle : C ≤ MulAction.stabilizer G aC := by
    intro c hc
    exact MulAction.mem_stabilizer_iff.mpr (hCfix ⟨c, hc⟩)
  have hBeq : MulAction.stabilizer G aB = B := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hBle
    rw [← hB.symm.index_eq_card, ← hBcomp.symm.index_eq_card]
  have hCeq : MulAction.stabilizer G aC = C := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hCle
    rw [← hC.symm.index_eq_card, ← hCcomp.symm.index_eq_card]
  obtain ⟨n, hn⟩ := exists_smul_eq hcop aB aC
  refine ⟨n, ?_⟩
  calc
    C = MulAction.stabilizer G aC := hCeq.symm
    _ = MulAction.stabilizer G (n • aB) := by rw [hn]
    _ = (MulAction.stabilizer G aB).map
          (MulAut.conj (n : G)).toMonoidHom :=
      MulAction.stabilizer_smul_eq_stabilizer_map_conj (n : G) aB
    _ = B.map (MulAut.conj (n : G)).toMonoidHom := by rw [hBeq]

open Submission.OddOrder.MathlibSupport

/-- Complements to a solvable normal Hall subgroup are conjugate by an
element of that normal subgroup. -/
theorem solvable_complement_conjugacy [IsSolvable N]
    (hcop : (Nat.card N).Coprime N.index)
    (hB : N.IsComplement' B) (hC : N.IsComplement' C) :
    ∃ n : N, C = B.map (MulAut.conj (n : G)).toMonoidHom := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (G' : Type u) [Group G'] [Finite G']
      (N' B' C' : Subgroup G') [N'.Normal] [IsSolvable N'],
      Nat.card N' = n →
      (Nat.card N').Coprime N'.index →
      N'.IsComplement' B' → N'.IsComplement' C' →
      ∃ x : N', C' = B'.map (MulAut.conj (x : G')).toMonoidHom
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp only [P]
      intro G' _ _ N' B' C' _ _ hcard hcop' hB' hC'
      by_cases hab : ∀ a b : N', a * b = b * a
      · letI : IsMulCommutative N' := isMulCommutative_iff.mpr hab
        exact abelian_complement_conjugacy hcop' hB' hC'
      · have hNne : N' ≠ ⊥ := by
          intro hbot
          apply hab
          intro a b
          apply Subtype.ext
          have ha : (a : G') = 1 := by
            apply Subgroup.mem_bot.mp
            rw [← hbot]
            exact a.property
          have hb : (b : G') = 1 := by
            apply Subgroup.mem_bot.mp
            rw [← hbot]
            exact b.property
          simp [ha, hb]
        let D : Subgroup G' := ⁅N', N'⁆
        have hDN : D ≤ N' := by
          dsimp [D]
          exact Subgroup.commutator_le_left N' N'
        letI : D.Normal := by
          dsimp [D]
          infer_instance
        let q : G' →* G' ⧸ D := QuotientGroup.mk' D
        let Nq : Subgroup (G' ⧸ D) := N'.map q
        let Bq : Subgroup (G' ⧸ D) := B'.map q
        let Cq : Subgroup (G' ⧸ D) := C'.map q
        letI : Nq.Normal := by
          dsimp [Nq]
          exact Subgroup.Normal.map (inferInstance : N'.Normal) q
            (QuotientGroup.mk'_surjective D)
        have hBq : Nq.IsComplement' Bq := by
          dsimp [Nq, Bq]
          exact Subgroup.IsComplement'.quotient_isComplement hB' hDN
        have hCq : Nq.IsComplement' Cq := by
          dsimp [Nq, Cq]
          exact Subgroup.IsComplement'.quotient_isComplement hC' hDN
        have hNqcomm : _root_.commutator Nq = ⊥ := by
          apply (Subgroup.map_injective Nq.subtype_injective)
          rw [Subgroup.map_subtype_commutator, Subgroup.map_bot]
          change ⁅N'.map q, N'.map q⁆ = ⊥
          rw [← Subgroup.map_commutator, show ⁅N', N'⁆ = D by rfl]
          exact (Subgroup.map_eq_bot_iff D).mpr (by
            rw [QuotientGroup.ker_mk'])
        letI : IsMulCommutative Nq :=
          (_root_.commutator_eq_bot_iff Nq).mp hNqcomm
        have hNqindex : Nq.index = N'.index := by
          dsimp [Nq, q]
          apply Subgroup.index_map_eq N' (QuotientGroup.mk'_surjective D)
          rw [QuotientGroup.ker_mk']
          exact hDN
        have hNqdiv : Nat.card Nq ∣ Nat.card N' := by
          dsimp [Nq]
          exact Subgroup.card_map_dvd N' q
        have hcopq : (Nat.card Nq).Coprime Nq.index := by
          rw [hNqindex]
          exact hcop'.coprime_dvd_left hNqdiv
        obtain ⟨xq, hxq⟩ :=
          abelian_complement_conjugacy hcopq hBq hCq
        rcases xq.property with ⟨x, hxN, hxmap⟩
        let xn : N' := ⟨x, hxN⟩
        let Bx : Subgroup G' :=
          B'.map (MulAut.conj (xn : G')).toMonoidHom
        have hBxmap : Bx.map q = Cq := by
          rw [hxq]
          dsimp [Bx, Bq]
          rw [Subgroup.map_map, Subgroup.map_map]
          congr 1
          ext b
          simp only [MonoidHom.coe_comp, Function.comp_apply]
          rw [← hxmap]
          rfl
        have hmapN :
            N'.map (MulAut.conj (xn : G')).toMonoidHom = N' :=
          Subgroup.Normal.map_conj_eq N' (xn : G')
        have hBxcomp : N'.IsComplement' Bx := by
          rw [Subgroup.isComplement'_iff_card_mul_and_disjoint]
          constructor
          · dsimp [Bx]
            rw [Subgroup.card_map_of_injective
              (MulAut.conj (xn : G')).injective]
            exact hB'.card_mul
          · rw [disjoint_iff]
            apply le_antisymm _ bot_le
            intro z hz
            rcases hz.2 with ⟨b, hbB, hbz⟩
            have hzNmap : z ∈
                N'.map (MulAut.conj (xn : G')).toMonoidHom := by
              rw [hmapN]
              exact hz.1
            rcases hzNmap with ⟨a, haN, haz⟩
            have habEq : a = b :=
              (MulAut.conj (xn : G')).injective (haz.trans hbz.symm)
            have hbN : b ∈ N' := habEq ▸ haN
            have hbBot : b ∈ (⊥ : Subgroup G') := by
              rw [← disjoint_iff.mp hB'.disjoint]
              exact ⟨hbN, hbB⟩
            apply Subgroup.mem_bot.mpr
            rw [← hbz, Subgroup.mem_bot.mp hbBot, map_one]
        let L : Subgroup G' := D ⊔ C'
        have hCL : C' ≤ L := by
          dsimp [L]
          exact le_sup_right
        have hDL : D ≤ L := by
          dsimp [L]
          exact le_sup_left
        have hBxL : Bx ≤ L := by
          intro b hb
          have hbq : q b ∈ Cq := by
            rw [← hBxmap]
            exact Subgroup.mem_map_of_mem q hb
          have hbcomap : b ∈ Cq.comap q := hbq
          dsimp [Cq, q] at hbcomap
          rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hbcomap
          simpa [L, sup_comm] using hbcomap
        let DL : Subgroup L := D.subgroupOf L
        let BL : Subgroup L := Bx.subgroupOf L
        let CL : Subgroup L := C'.subgroupOf L
        letI : DL.Normal := by
          dsimp [DL]
          exact Subgroup.Normal.subgroupOf (inferInstance : D.Normal) L
        have hDLCL : DL.IsComplement' CL := by
          apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
          · rw [disjoint_iff]
            apply le_antisymm _ bot_le
            intro z hz
            apply Subgroup.mem_bot.mpr
            apply Subtype.ext
            have hzbot : (z : G') ∈ (⊥ : Subgroup G') := by
              rw [← disjoint_iff.mp
                (Disjoint.mono hDN le_rfl hC'.disjoint)]
              exact ⟨hz.1, hz.2⟩
            exact Subgroup.mem_bot.mp hzbot
          · rw [← Subgroup.normal_mul DL CL]
            have hsup : DL ⊔ CL = ⊤ := by
              change D.subgroupOf L ⊔ C'.subgroupOf L = ⊤
              rw [← Subgroup.subgroupOf_sup hDL hCL]
              simp [L]
            rw [hsup]
            rfl
        have hDLBL : DL.IsComplement' BL := by
          apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
          · rw [disjoint_iff]
            apply le_antisymm _ bot_le
            intro z hz
            apply Subgroup.mem_bot.mpr
            apply Subtype.ext
            have hzbot : (z : G') ∈ (⊥ : Subgroup G') := by
              rw [← disjoint_iff.mp
                (Disjoint.mono hDN le_rfl hBxcomp.disjoint)]
              exact ⟨hz.1, hz.2⟩
            exact Subgroup.mem_bot.mp hzbot
          · rw [← Subgroup.normal_mul DL BL]
            have hsupG : D ⊔ Bx = L := by
              calc
                D ⊔ Bx = Bx ⊔ D := sup_comm D Bx
                _ = (Bx.map q).comap q := by
                  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
                _ = Cq.comap q := by rw [hBxmap]
                _ = C' ⊔ D := by
                  dsimp [Cq, q]
                  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
                _ = D ⊔ C' := sup_comm C' D
                _ = L := rfl
            have hsup : DL ⊔ BL = ⊤ := by
              change D.subgroupOf L ⊔ Bx.subgroupOf L = ⊤
              rw [← Subgroup.subgroupOf_sup hDL hBxL, hsupG]
              exact Subgroup.subgroupOf_self L
            rw [hsup]
            rfl
        let toN : DL →* N' :=
          { toFun := fun d ↦ ⟨((d : L) : G'), hDN d.property⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl }
        letI : IsSolvable DL :=
          solvable_of_solvable_injective (f := toN) (by
            intro a b hab'
            have hG : (((a : DL) : L) : G') = (((b : DL) : L) : G') :=
              congrArg (fun z : N' ↦ (z : G')) hab'
            exact Subtype.ext (Subtype.ext hG))
        letI : Nontrivial N' :=
          (Subgroup.nontrivial_iff_ne_bot N').mpr hNne
        have hDsubLt : D < N' := by
          have hcommLt : _root_.commutator N' < ⊤ :=
            IsSolvable.commutator_lt_top_of_nontrivial N'
          have hmapLt :
              (_root_.commutator N').map N'.subtype <
                (⊤ : Subgroup N').map N'.subtype :=
            (Subgroup.map_subtype_lt_map_subtype).2 hcommLt
          calc
            D = (_root_.commutator N').map N'.subtype := by
              exact N'.map_subtype_commutator.symm
            _ < (⊤ : Subgroup N').map N'.subtype := hmapLt
            _ = N' := by
              rw [← MonoidHom.range_eq_map, N'.range_subtype]
        have hDlt : Nat.card D < Nat.card N' :=
          natCard_subgroup_lt_of_lt hDsubLt
        have hcardDL : Nat.card DL = Nat.card D := by
          have hc := Subgroup.card_map_of_injective
            (K := DL) L.subtype_injective
          rw [Subgroup.map_subgroupOf_eq_of_le hDL] at hc
          exact hc.symm
        have hDLlt : Nat.card DL < n := by
          rw [hcardDL, ← hcard]
          exact hDlt
        have hcardBL : Nat.card BL = N'.index := by
          calc
            Nat.card BL = Nat.card Bx := by
              have hc := Subgroup.card_map_of_injective
                (K := BL) L.subtype_injective
              rw [Subgroup.map_subgroupOf_eq_of_le hBxL] at hc
              exact hc.symm
            _ = Nat.card B' := by
              dsimp [Bx]
              exact Subgroup.card_map_of_injective
                (MulAut.conj (xn : G')).injective
            _ = N'.index := hB'.symm.index_eq_card.symm
        have hcardDLdvd : Nat.card DL ∣ Nat.card N' := by
          rw [hcardDL]
          exact Subgroup.card_dvd_of_le hDN
        have hcopDL : (Nat.card DL).Coprime DL.index := by
          rw [hDLBL.symm.index_eq_card, hcardBL]
          exact hcop'.coprime_dvd_left hcardDLdvd
        obtain ⟨d, hd⟩ :=
          ih (Nat.card DL) hDLlt L DL BL CL rfl hcopDL hDLBL hDLCL
        have hdG : C' = Bx.map
            (MulAut.conj (((d : DL) : L) : G')).toMonoidHom := by
          calc
            C' = CL.map L.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hCL).symm
            _ = (BL.map (MulAut.conj (d : L)).toMonoidHom).map
                  L.subtype := by rw [hd]
            _ = BL.map
                  (L.subtype.comp (MulAut.conj (d : L)).toMonoidHom) :=
              Subgroup.map_map BL L.subtype
                (MulAut.conj (d : L)).toMonoidHom
            _ = BL.map
                  ((MulAut.conj (((d : DL) : L) : G')).toMonoidHom.comp
                    L.subtype) := rfl
            _ = (BL.map L.subtype).map
                  (MulAut.conj (((d : DL) : L) : G')).toMonoidHom := by
              rw [Subgroup.map_map]
            _ = Bx.map
                  (MulAut.conj (((d : DL) : L) : G')).toMonoidHom := by
              rw [Subgroup.map_subgroupOf_eq_of_le hBxL]
        let y : N' :=
          ⟨(((d : DL) : L) : G') * (xn : G'),
            N'.mul_mem (hDN d.property) xn.property⟩
        refine ⟨y, ?_⟩
        rw [hdG]
        dsimp [Bx]
        rw [Subgroup.map_map]
        congr 1
        ext b
        simp [y, MulAut.conj_apply, mul_assoc]
  exact hP (Nat.card N) G N B C rfl hcop hB hC

end Subgroup
