import Submission.OddOrder.MathlibSupport.SolvablePrimeComplement

/-!
Selecting a Hall `q'`-subgroup containing a prime-order complementary factor.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G] [IsSolvable G]
variable {K R : Subgroup G}

/-- In a coprime factorization with prime-order right factor, a Hall
`q'`-subgroup can be selected to contain that factor.  The proof only needs
ordinary Sylow conjugacy: the right factor and a Sylow subgroup inside an
arbitrary Hall `q'`-subgroup are Sylow for the same prime. -/
theorem exists_primeComplement_ge_prime_factor
    (hKR : K.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hRprime : (Nat.card R).Prime)
    {q : ℕ} (hq : q.Prime) (hqdvd : q ∣ Nat.card K) :
    ∃ J : Subgroup G, IsPrimeComplement q J ∧ R ≤ J := by
  classical
  let p := Nat.card R
  letI : Fact p.Prime := ⟨hRprime⟩
  letI : Fact q.Prime := ⟨hq⟩
  have hpK : Nat.Coprime p (Nat.card K) := by
    simpa [p] using hcop.symm
  have hpq : p ≠ q := by
    intro hpq
    apply hRprime.coprime_iff_not_dvd.mp hpK
    simpa [p, hpq] using hqdvd
  have hRp : IsPGroup p R := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by simp [p]⟩
  have hpRindex : ¬p ∣ R.index := by
    rw [hKR.index_eq_card]
    exact hRprime.coprime_iff_not_dvd.mp hpK
  let PR : Sylow p G := hRp.toSylow hpRindex
  obtain ⟨H, hH⟩ :=
    exists_primeComplement_of_isSolvable (G := G) hq
  let S : Sylow p H := Sylow.nonempty.some
  have hSmapP : IsPGroup p ((S : Subgroup H).map H.subtype) :=
    S.isPGroup'.map H.subtype
  have hpHindex : ¬p ∣ H.index := by
    obtain ⟨n, hn⟩ := hH.exists_index_eq_pow
    rw [hn]
    intro hpdvd
    exact hpq (Nat.prime_eq_prime_of_dvd_pow hRprime hq hpdvd)
  have hpSmapIndex : ¬p ∣ ((S : Subgroup H).map H.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact hRprime.not_dvd_mul S.not_dvd_index hpHindex
  let PH : Sylow p G := hSmapP.toSylow hpSmapIndex
  have hPHle : (PH : Subgroup G) ≤ H :=
    Subgroup.map_subtype_le (S : Subgroup H)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PH PR
  let J : Subgroup G := MulAut.conj g • H
  have hconj : MulAut.conj g • (PH : Subgroup G) = R := by
    rw [← Sylow.coe_subgroup_smul, hg]
    rfl
  have hRJ : R ≤ J := by
    calc
      R = MulAut.conj g • (PH : Subgroup G) := hconj.symm
      _ ≤ MulAut.conj g • H :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPHle
      _ = J := rfl
  exact ⟨J, hH.smul_mulAut (MulAut.conj g), hRJ⟩

end Submission.OddOrder.MathlibSupport
