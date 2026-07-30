import ChallengeDeps
import Submission.Kakutani

open LeanEval.GameTheory
open Set Function
open scoped BigOperators

namespace Submission

noncomputable section

variable {n : ℕ} {S : Fin n → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]

private abbrev ProfileSpace (S : Fin n → Type*) :=
  ∀ i, S i → ℝ

private abbrev EuclideanProfile (S : Fin n → Type*) :=
  EuclideanSpace ℝ (Σ i, S i)

private def toEuclidean (σ : ProfileSpace S) : EuclideanProfile S :=
  WithLp.toLp 2 fun x ↦ σ x.1 x.2

private def toProfile (σ : EuclideanProfile S) : ProfileSpace S :=
  fun i a ↦ σ ⟨i, a⟩

omit [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)] in
@[simp]
private theorem toProfile_toEuclidean (σ : ProfileSpace S) :
    toProfile (toEuclidean σ) = σ := rfl

omit [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)] in
@[simp]
private theorem toEuclidean_toProfile (σ : EuclideanProfile S) :
    toEuclidean (toProfile σ) = σ := by
  apply PiLp.ext
  rintro ⟨i, a⟩
  rfl

omit [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)] in
private theorem continuous_toEuclidean :
    Continuous (toEuclidean (S := S)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  fun_prop

private def strategySet : Set (EuclideanProfile S) :=
  {σ | ∀ i, toProfile σ i ∈ stdSimplex ℝ (S i)}

private noncomputable def pureStrategy {i : Fin n} (a : S i) : S i → ℝ := by
  classical
  exact Pi.single a 1

private def deviationPayoff
    (u : Fin n → StrategyProfile n S → ℝ) (i : Fin n)
    (σ : ProfileSpace S) (τ : S i → ℝ) : ℝ :=
  expectedPayoff (u i) (Function.update σ i τ)

omit [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)] in
private theorem prod_update_apply (σ : ProfileSpace S) (i : Fin n)
    (τ : S i → ℝ) (s : StrategyProfile n S) :
    (∏ j, (Function.update σ i τ) j (s j)) =
      τ (s i) * ∏ j ∈ Finset.univ.erase i, σ j (s j) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j ↦ (Function.update σ i τ) j (s j)) (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne]
  exact Finset.ne_of_mem_erase hj

omit [∀ i, Nonempty (S i)] in
private theorem deviationPayoff_eq_sum_pure
    (u : Fin n → StrategyProfile n S → ℝ) (i : Fin n)
    (σ : ProfileSpace S) (τ : S i → ℝ) :
    deviationPayoff u i σ τ =
      ∑ a, τ a * deviationPayoff u i σ (pureStrategy a) := by
  classical
  simp only [deviationPayoff, expectedPayoff, prod_update_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [pureStrategy, Pi.single_apply]
  rw [Finset.sum_eq_single (s i)]
  · simp
    ring
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

omit [∀ i, Nonempty (S i)] in
private theorem deviationPayoff_affine
    (u : Fin n → StrategyProfile n S → ℝ) (i : Fin n)
    (σ : ProfileSpace S) (τ ρ : S i → ℝ) (a b : ℝ) :
    deviationPayoff u i σ (fun x ↦ a * τ x + b * ρ x) =
      a * deviationPayoff u i σ τ + b * deviationPayoff u i σ ρ := by
  classical
  calc
    deviationPayoff u i σ (fun x ↦ a * τ x + b * ρ x) =
        ∑ x, (a * τ x + b * ρ x) *
          deviationPayoff u i σ (pureStrategy x) :=
      deviationPayoff_eq_sum_pure u i σ _
    _ = a * (∑ x, τ x * deviationPayoff u i σ (pureStrategy x)) +
        b * (∑ x, ρ x * deviationPayoff u i σ (pureStrategy x)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = a * deviationPayoff u i σ τ + b * deviationPayoff u i σ ρ := by
      rw [← deviationPayoff_eq_sum_pure u i σ τ,
        ← deviationPayoff_eq_sum_pure u i σ ρ]

omit [∀ i, Nonempty (S i)] in
private theorem pureStrategy_mem {i : Fin n} (a : S i) :
    pureStrategy a ∈ stdSimplex ℝ (S i) := by
  classical
  simpa only [pureStrategy] using single_mem_stdSimplex ℝ a

private theorem strategySet_nonempty :
    (strategySet : Set (EuclideanProfile S)).Nonempty := by
  classical
  let σ : ProfileSpace S :=
    fun i ↦ (stdSimplex.barycenter : stdSimplex ℝ (S i))
  exact ⟨toEuclidean σ,
    fun i ↦ (stdSimplex.barycenter : stdSimplex ℝ (S i)).property⟩

omit [∀ i, Nonempty (S i)] in
private theorem strategySet_compact :
    IsCompact (strategySet : Set (EuclideanProfile S)) := by
  classical
  let A : Set (ProfileSpace S) :=
    {σ | ∀ i, σ i ∈ stdSimplex ℝ (S i)}
  have hA : IsCompact A := by
    simpa only [A, Set.mem_setOf_eq] using
      (isCompact_pi_infinite (fun i ↦ isCompact_stdSimplex ℝ (S i)))
  have himage : toEuclidean '' A = (strategySet : Set (EuclideanProfile S)) := by
    ext σ
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact hτ
    · intro hσ
      exact ⟨toProfile σ, hσ, toEuclidean_toProfile σ⟩
  rw [← himage]
  exact hA.image continuous_toEuclidean

omit [∀ i, Nonempty (S i)] in
private theorem strategySet_convex :
    Convex ℝ (strategySet : Set (EuclideanProfile S)) := by
  rw [strategySet]
  intro σ hσ τ hτ a b ha hb hab i
  change (fun x ↦ a * toProfile σ i x + b * toProfile τ i x) ∈
    stdSimplex ℝ (S i)
  exact (convex_stdSimplex ℝ (S i)) (hσ i) (hτ i) ha hb hab

omit [∀ i, Nonempty (S i)] in
private theorem continuous_deviationPayoff_left
    (u : Fin n → StrategyProfile n S → ℝ) (i : Fin n) (τ : S i → ℝ) :
    Continuous (fun σ : EuclideanProfile S ↦
      deviationPayoff u i (toProfile σ) τ) := by
  classical
  unfold deviationPayoff expectedPayoff
  refine continuous_finsetSum Finset.univ fun s _ ↦
    (continuous_finsetProd Finset.univ fun j _ ↦ ?_).mul continuous_const
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
    exact continuous_const
  · simp only [Function.update_of_ne hji, toProfile]
    exact PiLp.continuous_apply 2 _ (⟨j, s j⟩ : Σ k, S k)

omit [∀ i, Nonempty (S i)] in
private theorem continuous_deviationPayoff_pair
    (u : Fin n → StrategyProfile n S → ℝ) (i : Fin n) :
    Continuous (fun q : EuclideanProfile S × EuclideanProfile S ↦
      deviationPayoff u i (toProfile q.1) (toProfile q.2 i)) := by
  classical
  unfold deviationPayoff expectedPayoff
  refine continuous_finsetSum Finset.univ fun s _ ↦
    (continuous_finsetProd Finset.univ fun j _ ↦ ?_).mul continuous_const
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, toProfile]
    exact (PiLp.continuous_apply 2 _ (⟨i, s i⟩ : Σ k, S k)).comp continuous_snd
  · simp only [Function.update_of_ne hji, toProfile]
    exact (PiLp.continuous_apply 2 _ (⟨j, s j⟩ : Σ k, S k)).comp continuous_fst

private noncomputable def bestPure
    (u : Fin n → StrategyProfile n S → ℝ) (i : Fin n)
    (σ : ProfileSpace S) : S i :=
  Classical.choose
    (Finset.exists_max_image Finset.univ
      (fun a ↦ deviationPayoff u i σ (pureStrategy a))
      Finset.univ_nonempty)

private theorem le_bestPure
    (u : Fin n → StrategyProfile n S → ℝ) (i : Fin n)
    (σ : ProfileSpace S) (a : S i) :
    deviationPayoff u i σ (pureStrategy a) ≤
      deviationPayoff u i σ (pureStrategy (bestPure u i σ)) := by
  classical
  exact
    (Classical.choose_spec
      (Finset.exists_max_image Finset.univ
        (fun b ↦ deviationPayoff u i σ (pureStrategy b))
      Finset.univ_nonempty)).2 a (Finset.mem_univ a)

private def bestResponse
    (u : Fin n → StrategyProfile n S → ℝ)
    (σ : EuclideanProfile S) : Set (EuclideanProfile S) :=
  {τ | τ ∈ strategySet ∧ ∀ i a,
    deviationPayoff u i (toProfile σ) (pureStrategy a) ≤
      deviationPayoff u i (toProfile σ) (toProfile τ i)}

private theorem bestResponse_nonempty
    (u : Fin n → StrategyProfile n S → ℝ) (σ : EuclideanProfile S) :
    (bestResponse u σ).Nonempty := by
  classical
  let τ : ProfileSpace S :=
    fun i ↦ pureStrategy (bestPure u i (toProfile σ))
  refine ⟨toEuclidean τ, ?_, ?_⟩
  · intro i
    change pureStrategy (bestPure u i (toProfile σ)) ∈ stdSimplex ℝ (S i)
    exact pureStrategy_mem (bestPure u i (toProfile σ))
  · intro i a
    change deviationPayoff u i (toProfile σ) (pureStrategy a) ≤
      deviationPayoff u i (toProfile σ)
        (pureStrategy (bestPure u i (toProfile σ)))
    exact le_bestPure u i (toProfile σ) a

omit [∀ i, Nonempty (S i)] in
private theorem bestResponse_convex
    (u : Fin n → StrategyProfile n S → ℝ) (σ : EuclideanProfile S) :
    Convex ℝ (bestResponse u σ) := by
  intro τ hτ ρ hρ a b ha hb hab
  constructor
  · exact strategySet_convex hτ.1 hρ.1 ha hb hab
  · intro i x
    have hpayoff :
        deviationPayoff u i (toProfile σ)
            (toProfile (a • τ + b • ρ) i) =
          a * deviationPayoff u i (toProfile σ) (toProfile τ i) +
          b * deviationPayoff u i (toProfile σ) (toProfile ρ i) := by
      change
        deviationPayoff u i (toProfile σ)
            (fun y ↦ a * toProfile τ i y + b * toProfile ρ i y) =
          a * deviationPayoff u i (toProfile σ) (toProfile τ i) +
          b * deviationPayoff u i (toProfile σ) (toProfile ρ i)
      exact deviationPayoff_affine u i (toProfile σ) _ _ a b
    calc
      deviationPayoff u i (toProfile σ) (pureStrategy x) =
          (a + b) * deviationPayoff u i (toProfile σ) (pureStrategy x) := by
            rw [hab, one_mul]
      _ = a * deviationPayoff u i (toProfile σ) (pureStrategy x) +
          b * deviationPayoff u i (toProfile σ) (pureStrategy x) := by ring
      _ ≤ a * deviationPayoff u i (toProfile σ) (toProfile τ i) +
          b * deviationPayoff u i (toProfile σ) (toProfile ρ i) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hτ.2 i x) ha)
          (mul_le_mul_of_nonneg_left (hρ.2 i x) hb)
      _ = deviationPayoff u i (toProfile σ)
          (toProfile (a • τ + b • ρ) i) := hpayoff.symm

omit [∀ i, Nonempty (S i)] in
private theorem bestResponse_graph_closed
    (u : Fin n → StrategyProfile n S → ℝ) :
    IsClosed {q : EuclideanProfile S × EuclideanProfile S |
      q.2 ∈ bestResponse u q.1} := by
  rw [show {q : EuclideanProfile S × EuclideanProfile S |
      q.2 ∈ bestResponse u q.1} =
      (Prod.snd ⁻¹' strategySet) ∩
        ⋂ i, ⋂ a, {q |
          deviationPayoff u i (toProfile q.1) (pureStrategy a) ≤
            deviationPayoff u i (toProfile q.1) (toProfile q.2 i)} by
    ext q
    simp only [bestResponse, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_iInter]]
  refine (strategySet_compact.isClosed.preimage continuous_snd).inter ?_
  refine isClosed_iInter fun i ↦ isClosed_iInter fun a ↦ ?_
  exact isClosed_le
    ((continuous_deviationPayoff_left u i (pureStrategy a)).comp continuous_fst)
    (continuous_deviationPayoff_pair u i)

omit [∀ i, Nonempty (S i)] in
private theorem bestResponse_closed
    (u : Fin n → StrategyProfile n S → ℝ) (σ : EuclideanProfile S) :
    IsClosed (bestResponse u σ) := by
  have hgraph := bestResponse_graph_closed u
  have hpair : Continuous (fun τ : EuclideanProfile S ↦ (σ, τ)) :=
    continuous_const.prodMk continuous_id
  change IsClosed {τ : EuclideanProfile S |
    (σ, τ).2 ∈ bestResponse u (σ, τ).1}
  exact hgraph.preimage hpair

theorem nash_equilibrium_exists_aux
    (u : Fin n → StrategyProfile n S → ℝ) :
    ∃ σ : ∀ i, S i → ℝ, IsNashEquilibrium u σ := by
  classical
  obtain ⟨σ, hσ, hbest⟩ := kakutani_fixed_point_aux
    (strategySet_compact (S := S))
    (strategySet_convex (S := S))
    (strategySet_nonempty (S := S))
    (bestResponse u)
    (bestResponse_graph_closed u)
    (fun x _ ↦ bestResponse_nonempty u x)
    (fun x _ ↦ bestResponse_convex u x)
    (fun x _ ↦ bestResponse_closed u x)
    (fun _ _ _ h ↦ h.1)
  refine ⟨toProfile σ, hσ, ?_⟩
  intro i τ hτ
  calc
    expectedPayoff (u i) (Function.update (toProfile σ) i τ) =
        deviationPayoff u i (toProfile σ) τ := rfl
    _ = ∑ a, τ a * deviationPayoff u i (toProfile σ) (pureStrategy a) :=
      deviationPayoff_eq_sum_pure u i (toProfile σ) τ
    _ ≤ ∑ a, τ a * deviationPayoff u i (toProfile σ) (toProfile σ i) := by
      exact Finset.sum_le_sum fun a _ ↦
        mul_le_mul_of_nonneg_left (hbest.2 i a) (hτ.1 a)
    _ = deviationPayoff u i (toProfile σ) (toProfile σ i) := by
      rw [← Finset.sum_mul, hτ.2, one_mul]
    _ = expectedPayoff (u i) (toProfile σ) := by
      unfold deviationPayoff
      rw [Function.update_eq_self]

end

end Submission
