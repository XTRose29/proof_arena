import Submission.OddOrder.MathlibSupport.FixedPointFreeOrbitCount

/-!
Fixed points of center-quotient conjugation actions from centralizer equalities.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {A : Type u} [Group A]

/-- Under the `card_clPqH` centralizer hypotheses, every nonidentity element of
`H` fixes only the identity coset in `P / Z(P)`. -/
theorem centerQuotient_fixed_eq_one_of_centralizers
    (P H : Subgroup A) (hHP : H ≤ Subgroup.normalizer P)
    (hcop : (Nat.card P).Coprime (Nat.card H))
    (hcenter : H ≤ Subgroup.centralizer (centerWithin P : Set A))
    (hcentralizer : ∀ h : H, h ≠ 1 ->
      centralizerWithin P (Subgroup.zpowers (h : A)) = centerWithin P) :
    letI := subgroupConjugationAction P H hHP
    letI := subgroupConjugationCenterQuotientAction P H hHP
    ∀ h : H, h ≠ 1 -> ∀ q : P ⧸ Subgroup.center P, h • q = q -> q = 1 := by
  letI := subgroupConjugationAction P H hHP
  letI := subgroupConjugationCenterQuotientAction P H hHP
  intro h hh q hq
  have hcopCenterH :
      (Nat.card (Subgroup.center P)).Coprime (Nat.card H) :=
    hcop.coprime_dvd_left (Subgroup.center P).card_subgroup_dvd_card
  have hcopOrder :
      (Nat.card (Subgroup.center P)).Coprime (orderOf h) :=
    natCard_coprime_orderOf_of_natCard_coprime
      (Subgroup.center P) hcopCenterH h
  have hfixCenter : ∀ z : Subgroup.center P, h • (z : P) = z := by
    intro z
    apply Subtype.ext
    change (h : A) * (z : P) * (h : A)⁻¹ = z
    have hz : ((z : P) : A) ∈ centerWithin P := by
      rw [← map_center_eq_centerWithin P]
      exact ⟨(z : P), z.property, rfl⟩
    have hcomm :=
      (Subgroup.mem_centralizer_iff.mp (hcenter h.property) _ hz).symm
    calc
      (h : A) * (z : P) * (h : A)⁻¹ =
          (z : P) * (h : A) * (h : A)⁻¹ := by rw [hcomm]
      _ = z := by simp
  have hfixedP : ∀ p : P, h • p = p -> p ∈ Subgroup.center P := by
    intro p hp
    have hpAmbient : (h : A) * (p : A) * (h : A)⁻¹ = p :=
      congrArg Subtype.val hp
    have hcomm : Commute (h : A) (p : A) := by
      apply (mul_inv_eq_iff_eq_mul.mp ?_)
      simpa [mul_assoc] using hpAmbient
    have hpcentralizer : (p : A) ∈
        centralizerWithin P (Subgroup.zpowers (h : A)) := by
      refine ⟨p.property, ?_⟩
      change ∀ y ∈ Subgroup.zpowers (h : A), y * (p : A) = (p : A) * y
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hcomm.zpow_left k).eq
    have hpcenterWithin : (p : A) ∈ centerWithin P := by
      rw [← hcentralizer h hh]
      exact hpcentralizer
    have hpmap : (p : A) ∈ (Subgroup.center P).map P.subtype := by
      rw [map_center_eq_centerWithin P]
      exact hpcenterWithin
    obtain ⟨z, hz, hzp⟩ := hpmap
    have hpz : p = z := Subtype.ext hzp.symm
    simpa [hpz] using hz
  have hlift := fixed_rep_mem_of_coprime_order_of_fixed_subgroup
    (Subgroup.center P) h hcopOrder hfixCenter hfixedP
  have hfixedBy := quotient_fixedBy_eq_singleton_of_fixed_rep_mem
    (Subgroup.center P) h hh hlift
  have hqmem : q ∈ MulAction.fixedBy (P ⧸ Subgroup.center P) h := hq
  rw [hfixedBy] at hqmem
  simpa using hqmem

end Submission.OddOrder.MathlibSupport
