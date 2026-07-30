import Mathlib.GroupTheory.Sylow
import Submission.OddOrder.MathlibSupport.PGroupCenter

/-!
Normal subgroups of prescribed prime-power order inside normal subgroups of
finite `p`-groups.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- If a normal subgroup of a finite `p`-group has order `p ^ n`, then it
contains an ambient-normal subgroup of order `p ^ k` for every `k ≤ n`.

This is the mathlib-facing form of the `normal_pgroup` step used in
`BGsection4.v`. -/
theorem exists_normal_subgroup_card_pow_le
    (hG : IsPGroup p G) (M : Subgroup G) [M.Normal]
    {n k : ℕ} (hMcard : Nat.card M = p ^ n) (hk : k ≤ n) :
    ∃ K : Subgroup G, K ≤ M ∧ K.Normal ∧ Nat.card K = p ^ k := by
  induction k with
  | zero =>
      exact ⟨⊥, bot_le, inferInstance, by simp⟩
  | succ k ih =>
      have hkn : k ≤ n := (Nat.le_succ k).trans hk
      obtain ⟨K, hKM, hKnormal, hKcard⟩ := ih hkn
      letI : K.Normal := hKnormal
      let Q := G ⧸ K
      let Mbar : Subgroup Q := M.map (QuotientGroup.mk' K)
      letI : Mbar.Normal :=
        Subgroup.Normal.map (show M.Normal from inferInstance)
          (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
      have hMbar_ne : Mbar ≠ ⊥ := by
        intro hMbar
        have hMK : M ≤ K := by
          change M.map (QuotientGroup.mk' K) = ⊥ at hMbar
          simpa [QuotientGroup.ker_mk'] using
            (Subgroup.map_eq_bot_iff M).mp hMbar
        have hKM' : K = M := le_antisymm hKM hMK
        have hpow_lt : p ^ k < p ^ n :=
          Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt
            (Nat.lt_of_succ_le hk)
        have hpows_eq : p ^ k = p ^ n := by
          calc
            p ^ k = Nat.card K := hKcard.symm
            _ = Nat.card M := by rw [hKM']
            _ = p ^ n := hMcard
        exact (ne_of_lt hpow_lt) hpows_eq
      have hQ : IsPGroup p Q := hG.to_quotient K
      let C : Subgroup Q := Mbar ⊓ Subgroup.center Q
      have hC_ne : C ≠ ⊥ :=
        normal_inf_center_ne_bot hQ Mbar hMbar_ne
      letI : Nontrivial C := C.nontrivial_iff_ne_bot.mpr hC_ne
      have hCp : IsPGroup p C := hQ.to_subgroup C
      obtain ⟨m, hm, hCcard⟩ := hCp.nontrivial_iff_card.mp inferInstance
      have hpC : p ∣ Nat.card C := by
        rw [hCcard]
        exact dvd_pow_self p hm.ne'
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := C) p hpC
      let zQ : Q := z
      have hzQ : orderOf zQ = p :=
        (Subgroup.orderOf_coe z).trans hz
      let E : Subgroup Q := Subgroup.zpowers zQ
      have hEcard : Nat.card E = p := by
        rw [Nat.card_zpowers, hzQ]
      have hEC : E ≤ C := by
        apply Subgroup.zpowers_le.mpr
        exact z.property
      have hEcenter : E ≤ Subgroup.center Q := hEC.trans inf_le_right
      letI : E.Normal := ⟨fun a ha b ↦ by
        simpa [Subgroup.mem_center_iff.mp (hEcenter ha) b] using ha⟩
      let L : Subgroup G := E.comap (QuotientGroup.mk' K)
      have hLM : L ≤ M := by
        have hEMbar : E ≤ Mbar := hEC.trans inf_le_left
        have hcomap : Mbar.comap (QuotientGroup.mk' K) = M := by
          dsimp [Mbar]
          rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hKM]
        exact hcomap ▸ Subgroup.comap_mono hEMbar
      have hLcard : Nat.card L = p ^ (k + 1) := by
        change Nat.card (QuotientGroup.mk ⁻¹' (E : Set Q)) = p ^ (k + 1)
        rw [QuotientGroup.card_preimage_mk, hKcard]
        change p ^ k * Nat.card E = p ^ (k + 1)
        rw [hEcard, pow_succ]
      exact ⟨L, hLM, inferInstance, by simpa [Nat.succ_eq_add_one] using hLcard⟩

end Submission.OddOrder.MathlibSupport
