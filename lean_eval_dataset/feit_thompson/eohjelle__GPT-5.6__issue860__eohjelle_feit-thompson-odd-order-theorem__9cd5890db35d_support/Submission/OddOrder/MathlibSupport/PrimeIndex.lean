import Submission.OddOrder.MathlibSupport.FrattiniPGroup

/-!
Subgroups of prime index.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

theorem isCoatom_of_index_eq_prime {H : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hindex : H.index = p) : IsCoatom H := by
  rw [isCoatom_iff_ge_of_le]
  constructor
  · intro htop
    have : H.index = 1 := by simp [htop]
    exact hp.ne_one (hindex.symm.trans this)
  · intro K hKtop hHK
    have hdiv : K.index ∣ p := by
      rw [← hindex]
      exact H.index_dvd_of_le hHK
    rcases (Nat.dvd_prime hp).mp hdiv with hKone | hKp
    · exact (hKtop (Subgroup.index_eq_one.mp hKone)).elim
    · have hmul := H.relIndex_mul_index hHK
      have hrel : H.relIndex K = 1 := by
        apply Nat.mul_right_cancel hp.pos
        simpa [hindex, hKp] using hmul
      exact Subgroup.relIndex_eq_one.mp hrel

theorem normal_of_index_eq_prime {H : Subgroup G} {p : ℕ}
    [Finite G] (hp : p.Prime) (hG : IsPGroup p G)
    (hindex : H.index = p) : H.Normal := by
  letI : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.isCoatom_normal hG
    (isCoatom_of_index_eq_prime hp hindex)

end Submission.OddOrder.MathlibSupport
