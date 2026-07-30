import Submission.OddOrder.MathlibSupport.AbelianPerfectPrimeAction
import Submission.OddOrder.MathlibSupport.ComplementQuotient

/-!
Fixed points of a perfect prime-order action lie in the derived subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R : Subgroup G}

/-- If a prime-order complement acts perfectly on `K`, its fixed subgroup in
`K` is contained in the derived subgroup of `K`. -/
theorem centralizerWithin_le_commutator_of_prime_perfect_action
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hRprime : (Nat.card R).Prime)
    (hperfect : ⁅R, K⁆ = K) :
    centralizerWithin K R ≤ ⁅K, K⁆ := by
  classical
  letI : K.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [← hKR.sup_eq_top]
    exact sup_le Subgroup.le_normalizer hnormK
  let N : Subgroup G := ⁅K, K⁆
  letI : N.Normal := by dsimp [N]; infer_instance
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Kq : Subgroup (G ⧸ N) := K.map q
  let Rq : Subgroup (G ⧸ N) := R.map q
  letI : Kq.Normal :=
    Subgroup.Normal.map (inferInstance : K.Normal) q
      (QuotientGroup.mk'_surjective N)
  have hNK : N ≤ K := by
    dsimp [N]
    exact Subgroup.commutator_le_left K K
  have hRqcard : Nat.card Rq = Nat.card R := by
    let f : R → Rq := q.subgroupMap R
    have hf : Function.Bijective f :=
      ⟨Subgroup.IsComplement'.quotientRight_subgroupMap_injective hKR hNK,
        q.subgroupMap_surjective R⟩
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  have hRqprime : (Nat.card Rq).Prime := by
    rw [hRqcard]
    exact hRprime
  have hcommKq : ⁅Kq, Kq⁆ = ⊥ := by
    dsimp [Kq]
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    simpa [q, QuotientGroup.ker_mk', N]
  letI : IsMulCommutative Kq := by
    have hcent : Kq ≤ Subgroup.centralizer (Kq : Set (G ⧸ N)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommKq
    refine ⟨⟨fun x y ↦ ?_⟩⟩
    apply Subtype.ext
    exact hcent y.property x x.property
  have hnormKq : Rq ≤ Subgroup.normalizer (Kq : Set (G ⧸ N)) := by
    rw [Kq.normalizer_eq_top]
    exact le_top
  have hperfectq : ⁅Rq, Kq⁆ = Kq := by
    dsimp [Rq, Kq]
    rw [← Subgroup.map_commutator, hperfect]
  have hRqne : Rq ≠ ⊥ := by
    intro hbot
    apply hRqprime.ne_one
    simp [hbot]
  letI : Nontrivial Rq :=
    (Subgroup.nontrivial_iff_ne_bot Rq).mpr hRqne
  obtain ⟨r, hr⟩ : ∃ r : Rq, r ≠ 1 := exists_ne 1
  intro c hc
  let cq : Kq := ⟨q c, ⟨c, hc.1, rfl⟩⟩
  have hfix : (r : G ⧸ N) * (cq : G ⧸ N) * (r : G ⧸ N)⁻¹ =
      (cq : G ⧸ N) := by
    rcases r.property with ⟨r0, hr0, hrq⟩
    have hcomm : r0 * c = c * r0 :=
      Subgroup.mem_centralizer_iff.mp hc.2 r0 hr0
    change (r : G ⧸ N) * q c * (r : G ⧸ N)⁻¹ = q c
    rw [← hrq]
    calc
      q r0 * q c * (q r0)⁻¹ = q (r0 * c * r0⁻¹) := by simp
      _ = q c := by rw [hcomm]; simp
  have hcq : cq = 1 :=
    fixed_eq_one_of_abelian_perfect_prime_action
      hnormKq hRqprime hperfectq r hr cq hfix
  apply (show c ∈ N from ?_)
  apply (QuotientGroup.eq_one_iff c).mp
  exact congrArg Subtype.val hcq

end Submission.OddOrder.MathlibSupport
