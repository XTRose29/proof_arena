import Mathlib
import Submission.CharTheory

/-!
# Character-theoretic core of Burnside's p^a q^b theorem

The main result is that a finite group of order p^a · q^b with a, b ≥ 1
cannot be simple.
-/

namespace Submission.BurnsideCore

open scoped Classical
noncomputable section

open Fintype

/-!
## Part 1: 1/p is not an algebraic integer
-/

theorem not_isIntegral_inv_prime (p : ℕ) (hp : Nat.Prime p) :
    ¬ IsIntegral ℤ ((p : ℂ)⁻¹) := by
  intro h
  obtain ⟨q, hq⟩ := h
  have h_contra : (p : ℤ) ∣ 1 := by
    -- Multiply both sides of the equation by $p^{\deg(q)}$ to clear the denominators.
    have h_cleared : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (p : ℤ) ^ (q.natDegree - i) = 0 := by
      rw [ ← @Int.cast_inj ℂ ] ; simp_all +decide [ Polynomial.eval₂_eq_sum_range ];
      convert congr_arg ( fun x : ℂ => x * ( p : ℂ ) ^ q.natDegree ) hq.2 using 1 <;> norm_num [ Finset.sum_mul _ _ _ ];
      field_simp;
      exact Finset.sum_congr rfl fun x hx => by rw [ eq_div_iff ( pow_ne_zero _ ( Nat.cast_ne_zero.mpr hp.ne_zero ) ) ] ; rw [ mul_assoc, ← pow_add, Nat.sub_add_cancel ( Finset.mem_range_succ_iff.mp hx ) ] ;
    simp_all +decide [ Finset.sum_range_succ ];
    exact ⟨ - ( ∑ i ∈ Finset.range q.natDegree, q.coeff i * p ^ ( q.natDegree - i ) ) / p, by linarith [ Int.ediv_mul_cancel ( show ( p : ℤ ) ∣ - ( ∑ i ∈ Finset.range q.natDegree, q.coeff i * p ^ ( q.natDegree - i ) ) from dvd_neg.mpr <| Finset.dvd_sum fun i hi => dvd_mul_of_dvd_right ( dvd_pow_self _ <| Nat.sub_ne_zero_of_lt <| Finset.mem_range.mp hi ) _ ) ] ⟩
  exact absurd h_contra (by
  exact mod_cast hp.not_dvd_one)

/-!
## Part 2: Sylow-theoretic argument
-/

/-- The p-part of the factorization of p^a * q^b. -/
lemma factorization_prime_pow_mul {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    (p ^ a * q ^ b).factorization p = a := by
have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
(hp.coprime_iff_not_dvd.2 fun h => hpq (hq.eq_one_or_self_of_dvd p h |>.resolve_left hp.ne_one)).pow a b
rw [Nat.factorization_mul_of_coprime hcop]
simp [Nat.Prime.factorization_pow hp, Nat.Prime.factorization_pow hq, hpq.symm]

/-- The Sylow p-subgroup of a group of order p^a * q^b has order p^a. -/
lemma sylow_card_eq {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hcard : Fintype.card G = p ^ a * q ^ b) (P : Sylow p G) :
    Nat.card (P : Subgroup G) = p ^ a := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hcard,
      factorization_prime_pow_mul hp hq hpq]

/-
In a group of order p^a * q^b with a ≥ 1, there exists g ≠ 1
    such that p^a divides |C_G(g)|.
-/
theorem exists_element_centralizer_dvd {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : 0 < a) (_hb : 0 < b)
    (hcard : Fintype.card G = p ^ a * q ^ b) :
    ∃ g : G, g ≠ 1 ∧ p ^ a ∣ Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  -- By Sylow's theorem, there exists a Sylow p-subgroup $P$ of $G$.
  obtain ⟨P, hP⟩ : ∃ P : Sylow p G, True := by
    simp +zetaDelta at *;
  -- Since $P$ is a Sylow $p$-subgroup, its center $Z(P)$ is nontrivial.
  have h_center_nontrivial : Nontrivial (↥(Subgroup.center P)) := by
    haveI := Fact.mk hp;
    have h_center_nontrivial : IsPGroup p P := by
      exact P.2;
    convert h_center_nontrivial.center_nontrivial;
    have hP_card : Nat.card P = p ^ (Nat.factorization (Nat.card G) p) := by
      convert P.card_eq_multiplicity;
    have hP_card_pos : p ^ (Nat.factorization (Nat.card G) p) > 1 := by
      simp_all +decide [ Nat.factorization_mul, hp.ne_zero, hq.ne_zero ];
      exact one_lt_pow₀ hp.one_lt ( by positivity );
    exact Fintype.one_lt_card_iff_nontrivial.mp ( by rw [ ← Nat.card_eq_fintype_card ] ; exact hP_card.symm ▸ hP_card_pos );
  -- Since $Z(P)$ is nontrivial, there exists a non-identity element $g₀ \in Z(P)$.
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : P, g₀ ≠ 1 ∧ g₀ ∈ Subgroup.center P := by
    obtain ⟨ g₀, hg₀ ⟩ := exists_ne ( 1 : ↥ ( Subgroup.center P ) ) ; use g₀; aesop;
  -- Since $g₀ \in Z(P)$, we have $P \subseteq C_G(g₀)$.
  have hP_subset_centralizer : (P : Subgroup G) ≤ Subgroup.centralizer {g₀.val} := by
    intro x hx; simp_all +decide [ Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff ] ;
    exact congr_arg Subtype.val ( hg₀.2.comm ⟨ x, hx ⟩ );
  refine' ⟨ g₀, _, _ ⟩ <;> simp_all +decide;
  have := Subgroup.card_dvd_of_le hP_subset_centralizer; simp_all +decide ;
  haveI := Fact.mk hp; haveI := Fact.mk hq; have := P.card_eq_multiplicity; simp_all +decide [ Nat.Prime.pow_dvd_iff_le_factorization ] ;
  simp_all +decide [ Nat.factorization_mul, hp.ne_zero, hq.ne_zero ];
  exact le_trans ( Nat.le_add_right _ _ ) ‹_›

/-
The centralizer index divides q^b when p^a divides |C_G(g)|
    and |G| = p^a * q^b.
-/
theorem centralizer_index_dvd_prime_pow {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hcard : Fintype.card G = p ^ a * q ^ b)
    (g : G) (hdvd : p ^ a ∣ Nat.card (Subgroup.centralizer ({g} : Set G))) :
    ∃ k, k ≤ b ∧ (Subgroup.centralizer ({g} : Set G)).index = q ^ k := by
  -- By definition of index, we have that the index of the centralizer divides the order of the group.
  have h_index_divides_card : Subgroup.index (Subgroup.centralizer {g}) ∣ Fintype.card G := by
    convert Subgroup.index_dvd_card ( Subgroup.centralizer { g } );
    rw [ Nat.card_eq_fintype_card ];
  simp_all +decide;
  have h_index_divides_qb : (Subgroup.centralizer {g}).index ∣ q ^ b := by
    refine' Nat.Coprime.dvd_of_dvd_mul_left _ h_index_divides_card;
    refine' Nat.Coprime.pow_right _ _;
    refine' Nat.Coprime.symm ( hp.coprime_iff_not_dvd.mpr _ );
    have := Subgroup.index_mul_card ( Subgroup.centralizer { g } );
    obtain ⟨ k, hk ⟩ := hdvd; simp_all +decide ;
    -- Dividing both sides of the equation by $p^a$, we get $(Subgroup.centralizer {g}).index * k = q^b$.
    have h_div : (Subgroup.centralizer {g}).index * k = q ^ b := by
      nlinarith [ pow_pos hp.pos a ];
    intro h; have := Nat.Prime.dvd_of_dvd_pow hp ( h_div ▸ dvd_mul_of_dvd_left h _ ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
  rw [ Nat.dvd_prime_pow hq ] at h_index_divides_qb ; tauto

/-
If the centralizer index is 1, then g is in the center.
-/
theorem mem_center_of_centralizer_index_one {G : Type*} [Group G]
    (g : G) (h : (Subgroup.centralizer ({g} : Set G)).index = 1) :
    g ∈ Subgroup.center G := by
  simp_all +decide [ Subgroup.mem_center_iff ]

/-
A nontrivial group whose order is p^a*q^b and has nontrivial center is not simple.
-/
theorem not_simple_of_nontrivial_center {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (_hpq : p ≠ q)
    (ha : 0 < a) (hb : 0 < b)
    (hcard : Fintype.card G = p ^ a * q ^ b)
    (hcenter : ∃ g : G, g ≠ 1 ∧ g ∈ Subgroup.center G) :
    ¬ IsSimpleGroup G := by
  rintro ⟨ hG ⟩;
  -- Since the center is nontrivial and normal, it must be the entire group.
  have hcenter_normal : Subgroup.Normal (Subgroup.center G) := by
    infer_instance
  have hcenter_eq_top : Subgroup.center G = ⊤ := by
    cases hG _ hcenter_normal <;> simp_all +decide [ Subgroup.eq_bot_iff_forall ];
  -- Since $G$ is abelian, every subgroup is normal. Let $H$ be a subgroup of $G$ with order $p^a$.
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, Nat.card H = p ^ a := by
    convert Sylow.exists_subgroup_card_pow_prime _ _;
    · infer_instance;
    · exact ⟨ hp ⟩;
    · aesop;
  cases hG H ( by constructor; simp +decide [ Subgroup.mem_center_iff.mp ( hcenter_eq_top.symm ▸ Subgroup.mem_top _ ) ] ) <;> simp_all +decide;
  · exact absurd hH ( ne_of_lt ( one_lt_pow₀ hp.one_lt ha.ne' ) );
  · exact absurd hH ( ne_of_gt ( lt_mul_of_one_lt_right ( pow_pos hp.pos _ ) ( one_lt_pow₀ hq.one_lt hb.ne' ) ) )

/-!
## Part 3: Character-theoretic non-simplicity
-/

/-- If G has g ≠ 1 with [G:C_G(g)] = q^k (k ≥ 1), then G is not simple.
    This is the character-theoretic core of Burnside's theorem.
    
    Proof: Assume G is simple. Use column orthogonality to get
    ∑ d_i · χ_i(g) = 0. For i with gcd(d_i, q^k) = 1 and d_i > 1,
    χ_i(g) = 0 (by the vanishing lemma + simplicity). The trivial rep
    contributes 1. So 1 + ∑_{q | d_i} d_i · χ_i(g) = 0.
    Each d_i · χ_i(g) = q · (d_i/q · χ_i(g)) where d_i/q · χ_i(g) is
    an algebraic integer. So 1/q is an algebraic integer, contradiction. -/
theorem not_simple_of_prime_power_centralizer_index {G : Type} [Group G] [Fintype G]
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (ha : 0 < a) (_hb : 0 < b)
    (hcard : Fintype.card G = p ^ a * q ^ b)
    (g : G) (hg : g ≠ 1)
    (k : ℕ) (hk : 0 < k)
    (hindex : (Subgroup.centralizer ({g} : Set G)).index = q ^ k) :
    ¬ IsSimpleGroup G := by
  intro hsimple
  -- Use the character-theoretic core to derive that 1/q is an algebraic integer
  have h_one_div : IsIntegral ℤ ((q : ℂ)⁻¹) := by
    apply Submission.CharTheory.burnside_char_core hq hk g hg hindex hsimple
    refine ⟨p, hp, hpq, ?_⟩
    rw [hcard]
    exact (dvd_pow_self p ha.ne').trans (dvd_mul_right _ _)
  exact not_isIntegral_inv_prime q hq h_one_div

/-!
## Assembly
-/

/-- A group of order p^a * q^b with a, b ≥ 1 is not simple. -/
theorem not_isSimpleGroup_of_card {G : Type} [Group G] [Fintype G]
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (ha : 0 < a) (hb : 0 < b)
    (hcard : Fintype.card G = p ^ a * q ^ b) :
    ¬ IsSimpleGroup G := by
  obtain ⟨g, hg_ne, hdvd⟩ := exists_element_centralizer_dvd hp hq ha hb hcard
  obtain ⟨k, _, hindex⟩ := centralizer_index_dvd_prime_pow hp hq hpq hcard g hdvd
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · -- k = 0: index is 1, g is central
    have hindex1 : (Subgroup.centralizer ({g} : Set G)).index = 1 := by simpa using hindex
    exact not_simple_of_nontrivial_center hp hq hpq ha hb hcard
      ⟨g, hg_ne, mem_center_of_centralizer_index_one g hindex1⟩
  · -- k ≥ 1: character theory
    exact not_simple_of_prime_power_centralizer_index hp hq hpq ha hb hcard g hg_ne k hk_pos hindex

end
end Submission.BurnsideCore
