import Submission.SparseGrid

namespace Submission.Helpers

/-- Bad coarse-grid indices in the residue class `r` modulo `H`.  The
corresponding actual times are `r + H * j`. -/
noncomputable def phaseBadGridIndices
    (H L r : ℕ) (good : ℕ → Prop) : Finset ℕ :=
  badGridIndices H (L - r) fun t => good (r + t)

lemma mem_phaseBadGridIndices_iff
    {H L r : ℕ} (good : ℕ → Prop) {j : ℕ} :
    j ∈ phaseBadGridIndices H L r good ↔
      j < L - r ∧ H * j < L - r ∧ ¬good (r + H * j) := by
  simpa [phaseBadGridIndices] using
    (mem_badGridIndices_iff
      (H := H) (L := L - r) (good := fun t => good (r + t)) (j := j))

/-- The disjoint union of the bad grids over all residue classes. -/
noncomputable def phaseBadPairs
    (H L : ℕ) (good : ℕ → Prop) : Finset (Σ _r : Fin H, ℕ) :=
  Finset.univ.sigma fun r => phaseBadGridIndices H L r.val good

/-- A residue and its coarse-grid index determine their actual time. -/
def phaseBadTimeEmbedding (H : ℕ) (hH : 0 < H) :
    (Σ _r : Fin H, ℕ) ↪ ℕ where
  toFun p := p.1.val + H * p.2
  inj' := by
    rintro ⟨r, j⟩ ⟨s, k⟩ h
    have hrs_val : r.val = s.val := by
      have hmod := congrArg (fun z : ℕ => z % H) h
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt,
        Nat.mod_eq_of_lt s.isLt] using hmod
    have hrs : r = s := Fin.ext hrs_val
    subst s
    have hjk : j = k := by
      apply Nat.mul_left_cancel hH
      exact Nat.add_left_cancel h
    subst k
    rfl

@[simp] lemma phaseBadTimeEmbedding_apply
    (H : ℕ) (hH : 0 < H) (p : Σ _r : Fin H, ℕ) :
    phaseBadTimeEmbedding H hH p = p.1.val + H * p.2 := rfl

lemma card_phaseBadPairs
    {H : ℕ} (hH : 0 < H) (L : ℕ) (good : ℕ → Prop) :
    (phaseBadPairs H L good).card = finiteBadCountNat good L := by
  classical
  rw [← Finset.card_image_of_injective
    (phaseBadPairs H L good) (phaseBadTimeEmbedding H hH).injective]
  unfold finiteBadCountNat
  congr 1
  ext t
  constructor
  · intro ht
    obtain ⟨⟨r, j⟩, hp, ht⟩ := Finset.mem_image.mp ht
    have hp' := Finset.mem_sigma.mp hp
    have hj := (mem_phaseBadGridIndices_iff good).mp hp'.2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      rw [← ht]
      rw [phaseBadTimeEmbedding_apply]
      omega
    · rw [← ht]
      simpa only [phaseBadTimeEmbedding_apply] using hj.2.2
  · intro ht
    have ht' := Finset.mem_filter.mp ht
    let r : Fin H := ⟨t % H, Nat.mod_lt t hH⟩
    let j : ℕ := t / H
    have htime : r.val + H * j = t := by
      simpa [r, j] using Nat.mod_add_div t H
    have htL : t < L := Finset.mem_range.mp ht'.1
    have hsumlt : r.val + H * j < L := by
      simpa only [htime] using htL
    have hgap : H * j < L - r.val := by
      omega
    have hjlt : j < L - r.val := by
      exact (Nat.le_mul_of_pos_left j hH).trans_lt hgap
    have hj :
        j ∈ phaseBadGridIndices H L r.val good := by
      apply (mem_phaseBadGridIndices_iff good).mpr
      refine ⟨hjlt, hgap, ?_⟩
      simpa [htime] using ht'.2
    apply Finset.mem_image.mpr
    refine ⟨⟨r, j⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ r, hj⟩, ?_⟩
    exact htime

/-- Averaging over grid phases removes the coarse-spacing loss: every bad
time occurs in exactly one residue class. -/
lemma sum_card_phaseBadGridIndices
    {H : ℕ} (hH : 0 < H) (L : ℕ) (good : ℕ → Prop) :
    (∑ r : Fin H, (phaseBadGridIndices H L r.val good).card) =
      finiteBadCountNat good L := by
  classical
  simpa [phaseBadPairs] using card_phaseBadPairs hH L good

/-- At least one residue class has no more than its averaged share of the bad
times. -/
lemma exists_phase_mul_card_le_finiteBadCountNat
    {H : ℕ} (hH : 0 < H) (L : ℕ) (good : ℕ → Prop) :
    ∃ r : Fin H,
      H * (phaseBadGridIndices H L r.val good).card ≤
        finiteBadCountNat good L := by
  classical
  by_contra hnone
  push Not at hnone
  have hsum := Finset.sum_lt_sum_of_nonempty
    (s := (Finset.univ : Finset (Fin H)))
    ⟨⟨0, hH⟩, Finset.mem_univ _⟩ (fun r _hr => hnone r)
  have hirr :
      H * finiteBadCountNat good L <
        H * finiteBadCountNat good L := by
    calc
      H * finiteBadCountNat good L =
          ∑ _r : Fin H, finiteBadCountNat good L := by simp
      _ < ∑ r : Fin H,
          H * (phaseBadGridIndices H L r.val good).card := hsum
      _ = H *
          (∑ r : Fin H,
            (phaseBadGridIndices H L r.val good).card) := by
        rw [Finset.mul_sum]
      _ = H * finiteBadCountNat good L := by
        rw [sum_card_phaseBadGridIndices hH L good]
  exact (lt_irrefl _ hirr)

end Submission.Helpers
