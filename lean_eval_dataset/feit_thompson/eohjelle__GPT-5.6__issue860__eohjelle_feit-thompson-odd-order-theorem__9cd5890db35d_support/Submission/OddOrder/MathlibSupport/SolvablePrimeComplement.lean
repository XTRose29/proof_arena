import Submission.OddOrder.MathlibSupport.MinimalNormalExistence
import Submission.OddOrder.MathlibSupport.MinimalNormal
import Submission.OddOrder.MathlibSupport.PrimeComplement
import Submission.OddOrder.MathlibSupport.Solvability

/-!
Existence of Hall `q'`-subgroups in finite solvable groups.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- Every finite solvable group has a Hall `q'`-subgroup.  This is the
specialized existence half of Hall's theorem needed in B&G Theorem 3.4. -/
theorem exists_primeComplement_of_isSolvable
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {q : ℕ} (hq : q.Prime) :
    ∃ H : Subgroup G, IsPrimeComplement q H := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  let motive : ℕ → Prop := fun n =>
    ∀ {K : Type u} [Group K] [Finite K] [IsSolvable K],
      Nat.card K = n → ∃ H : Subgroup K, IsPrimeComplement q H
  suffices hmain : motive (Nat.card G) from hmain rfl
  exact Nat.strong_induction_on (p := motive) (Nat.card G) fun n ih => by
    intro K _ _ _ hcard
    by_cases hqdvd : q ∣ Nat.card K
    · have hKcard : 1 < Nat.card K :=
        hq.one_lt.trans_le (Nat.le_of_dvd Nat.card_pos hqdvd)
      letI : Nontrivial K :=
        Finite.one_lt_card_iff_nontrivial.mp hKcard
      obtain ⟨M, hMmin, -⟩ :=
        exists_minimalNormal_le (K := (⊤ : Subgroup K))
          (by infer_instance) top_ne_bot
      letI : M.Normal := hMmin.normal
      obtain ⟨r, hr, hMr⟩ := hMmin.exists_prime_isPGroup
      letI : Fact r.Prime := ⟨hr⟩
      have hquotlt : Nat.card (K ⧸ M) < Nat.card K :=
        natCard_quotient_lt_of_ne_bot M hMmin.ne_bot
      obtain ⟨Hbar, hHbar⟩ :=
        ih (Nat.card (K ⧸ M)) (by simpa [hcard] using hquotlt)
          (K := K ⧸ M) rfl
      let pi : K →* K ⧸ M := QuotientGroup.mk' M
      let L : Subgroup K := Hbar.comap pi
      have hML : M ≤ L := by
        intro x hx
        change pi x ∈ Hbar
        have hpix : pi x = 1 := by
          exact QuotientGroup.eq_one_iff x |>.mpr hx
        rw [hpix]
        exact Hbar.one_mem
      let ML : Subgroup L := M.subgroupOf L
      let f : L →* K ⧸ M := pi.comp L.subtype
      have hkerf : f.ker = ML := by
        ext x
        change pi (x : K) = 1 ↔ (x : K) ∈ M
        exact QuotientGroup.eq_one_iff (x : K)
      have hrangef : f.range = Hbar := by
        apply le_antisymm
        · rintro x ⟨y, rfl⟩
          exact y.2
        · intro x hx
          obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M x
          refine ⟨⟨g, ?_⟩, rfl⟩
          exact hx
      have hMLindex : ML.index = Nat.card Hbar := by
        calc
          ML.index = f.ker.index := congrArg Subgroup.index hkerf.symm
          _ = Nat.card f.range := Subgroup.index_ker f
          _ = Nat.card Hbar :=
            Nat.card_congr (MulEquiv.subgroupCongr hrangef).toEquiv
      have hMLcard : Nat.card ML = Nat.card M :=
        natCard_subgroupOf_eq hML
      have hLindex : L.index = Hbar.index := by
        simpa [L, pi] using
          Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective M)
      have hLcard : Nat.card L = Nat.card M * Nat.card Hbar := by
        rw [← ML.index_mul_card, hMLindex, hMLcard, mul_comm]
      by_cases hrq : r = q
      · subst r
        obtain ⟨a, ha⟩ := hMr.exists_card_eq
        letI : ML.Normal := hMmin.normal.subgroupOf L
        have hcopML : Nat.Coprime (Nat.card ML) ML.index := by
          rw [hMLcard, ha, hMLindex]
          exact hHbar.card_coprime.symm.pow_left a
        obtain ⟨H, hcomp⟩ := ML.exists_right_complement'_of_coprime hcopML
        let J : Subgroup K := H.map L.subtype
        have hcardJ : Nat.card J = Nat.card H :=
          Subgroup.card_map_of_injective L.subtype_injective
        have hcardH : Nat.card H = Nat.card Hbar := by
          rw [← hMLindex]
          exact hcomp.symm.index_eq_card.symm
        refine ⟨J, ?_⟩
        constructor
        · rw [hcardJ, hcardH]
          exact hHbar.card_coprime
        · obtain ⟨b, hb⟩ := hHbar.exists_index_eq_pow
          refine ⟨a + b, ?_⟩
          dsimp [J]
          rw [Subgroup.index_map_subtype, hcomp.index_eq_card,
            hMLcard, ha, hLindex, hb, pow_add]
      · obtain ⟨a, ha⟩ := hMr.exists_card_eq
        have hMq : Nat.Coprime (Nat.card M) q := by
          rw [ha]
          exact ((Nat.coprime_primes hr hq).mpr hrq).pow_left a
        refine ⟨L, ?_⟩
        constructor
        · rw [hLcard]
          exact hMq.mul_left hHbar.card_coprime
        · simpa [hLindex] using hHbar.exists_index_eq_pow
    · refine ⟨⊤, ?_⟩
      constructor
      · simpa using (hq.coprime_iff_not_dvd.mpr hqdvd).symm
      · exact ⟨0, by simp⟩

end Submission.OddOrder.MathlibSupport
