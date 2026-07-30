import Mathlib.GroupTheory.Sylow
import Submission.OddOrder.MathlibSupport.PrimeOrderFixedPoint
import Submission.OddOrder.MathlibSupport.SubgroupConjugationQuotientAction

/-!
Invariant Sylow subgroups under coprime prime-order actions.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped Pointwise

universe u v

variable {A : Type u} {X : Type v}
variable [Group A] [Finite A] [Group X] [Finite X]

/-- A coprime action by a group of prime order fixes a Sylow subgroup. -/
theorem exists_fixed_sylow_of_prime_natCard
    [MulDistribMulAction A X] {q : ℕ} (hq : q.Prime)
    (hprime : (Nat.card A).Prime)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card X)) :
    ∃ P : Sylow q X, P ∈ MulAction.fixedPoints A (Sylow q X) := by
  letI : Fact q.Prime := ⟨hq⟩
  let P₀ : Sylow q X := Sylow.nonempty.some
  have hcount : Nat.card (Sylow q X) ∣ Nat.card X :=
    P₀.card_dvd_index.trans P₀.index_dvd_card
  have hcountcop : Nat.Coprime (Nat.card A) (Nat.card (Sylow q X)) :=
    hcop.coprime_dvd_right hcount
  exact nonempty_fixedPoints_of_prime_natCard hprime hcountcop

variable {G : Type*} [Group G] [Finite G]
variable {K R : Subgroup G}

/-- An ambient subgroup is a Sylow `q`-subgroup of `K` when it is the image
of a mathlib `Sylow q K` under the subgroup inclusion. -/
def IsSylowSubgroupOf (q : ℕ) (Q K : Subgroup G) : Prop :=
  ∃ P : Sylow q K, Q = (P : Subgroup K).map K.subtype

omit [Finite G] in
theorem IsSylowSubgroupOf.isPGroup {q : ℕ} [Fact q.Prime]
    {Q K : Subgroup G} (hQ : IsSylowSubgroupOf q Q K) :
    IsPGroup q Q := by
  obtain ⟨P, rfl⟩ := hQ
  exact P.isPGroup'.map K.subtype

/-- Under internal conjugation, a coprime prime-order subgroup normalizing `K`
normalizes the ambient image of some Sylow subgroup of `K`. -/
theorem exists_sylow_normalized_by_prime_subgroup
    {q : ℕ} (hq : q.Prime)
    (hnorm : R ≤ Subgroup.normalizer (K : Set G))
    (hRprime : (Nat.card R).Prime)
    (hcop : Nat.Coprime (Nat.card R) (Nat.card K)) :
    ∃ P : Sylow q K,
      R ≤ Subgroup.normalizer
        (((P : Subgroup K).map K.subtype : Subgroup G) : Set G) := by
  letI : MulDistribMulAction R K :=
    subgroupConjugationAction K R hnorm
  obtain ⟨P, hP⟩ :=
    exists_fixed_sylow_of_prime_natCard hq hRprime hcop
  refine ⟨P, ?_⟩
  intro r hr
  let rr : R := ⟨r, hr⟩
  have hfixed : ∀ s : R, s • P = P :=
    MulAction.mem_fixedPoints.mp hP
  have hforward : ∀ (s : R) (x : G),
      x ∈ (P : Subgroup K).map K.subtype →
      (s : G) * x * (s : G)⁻¹ ∈ (P : Subgroup K).map K.subtype := by
    intro s x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨s • y, ?_, ?_⟩
    · have hmem : s • y ∈ s • (P : Subgroup K) :=
        Subgroup.smul_mem_pointwise_smul y s (P : Subgroup K) hy
      rw [← Sylow.pointwise_smul_def, hfixed s] at hmem
      exact hmem
    · exact coe_subgroupConjugationAction_smul K R hnorm s y
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward rr x
  · intro hx
    have hinv := hforward rr⁻¹
      ((rr : G) * x * (rr : G)⁻¹) hx
    simpa [rr, mul_assoc] using hinv

/-- If `K` is not a `q`-group, the invariant Sylow subgroup supplied above is
a proper ambient subgroup of `K`. -/
theorem exists_proper_isPGroup_normalized_by_prime_subgroup
    {q : ℕ} (hq : q.Prime)
    (hnorm : R ≤ Subgroup.normalizer (K : Set G))
    (hRprime : (Nat.card R).Prime)
    (hcop : Nat.Coprime (Nat.card R) (Nat.card K))
    (hKq : ¬IsPGroup q K) :
    ∃ Q : Subgroup G,
      Q < K ∧ IsSylowSubgroupOf q Q K ∧
        R ≤ Subgroup.normalizer (Q : Set G) := by
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hPnorm⟩ :=
    exists_sylow_normalized_by_prime_subgroup hq hnorm hRprime hcop
  let Q : Subgroup G := (P : Subgroup K).map K.subtype
  have hPlt : (P : Subgroup K) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hKq
    have htopP : IsPGroup q (⊤ : Subgroup K) :=
      P.isPGroup'.of_equiv (MulEquiv.subgroupCongr htop)
    exact htopP.of_equiv Subgroup.topEquiv
  have hQlt : Q < K := by
    rw [← K.range_subtype, MonoidHom.range_eq_map]
    exact Subgroup.map_subtype_lt_map_subtype.mpr hPlt
  exact ⟨Q, hQlt, ⟨P, rfl⟩, hPnorm⟩

end Submission.OddOrder.MathlibSupport
