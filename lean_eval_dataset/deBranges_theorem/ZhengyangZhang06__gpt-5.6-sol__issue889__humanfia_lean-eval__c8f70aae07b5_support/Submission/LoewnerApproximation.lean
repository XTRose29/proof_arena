import Submission.RadialLoewner

open Filter

namespace Submission

lemma tendsto_milinFunctional_of_logarithmicCoeff
    {L : ℂ → ℂ} {A : ℕ → ℂ → ℂ}
    (hcoeff : ∀ k : ℕ,
      Tendsto (fun j => logarithmicCoeff (A j) k) atTop
        (nhds (logarithmicCoeff L k))) (N : ℕ) :
    Tendsto (fun j => milinFunctional (A j) N) atTop
      (nhds (milinFunctional L N)) := by
  simp_rw [milinFunctional_eq_weighted]
  apply tendsto_finsetSum
  intro k hk
  exact (((hcoeff (k + 1)).norm.pow 2).const_mul (((k + 1 : ℕ) : ℝ))).sub
    tendsto_const_nhds |>.const_mul (((N - k : ℕ) : ℝ))

lemma tendsto_milinFunctional_of_logarithmicCoeff_up_to
    {L : ℂ → ℂ} {A : ℕ → ℂ → ℂ} (N : ℕ)
    (hcoeff : ∀ k ∈ Finset.range N,
      Tendsto (fun j => logarithmicCoeff (A j) (k + 1)) atTop
        (nhds (logarithmicCoeff L (k + 1)))) :
    Tendsto (fun j => milinFunctional (A j) N) atTop
      (nhds (milinFunctional L N)) := by
  simp_rw [milinFunctional_eq_weighted]
  apply tendsto_finsetSum
  intro k hk
  exact ((((hcoeff k hk).norm.pow 2).const_mul (((k + 1 : ℕ) : ℝ))).sub
    tendsto_const_nhds).const_mul (((N - k : ℕ) : ℝ))

lemma satisfiesMilin_of_logarithmicCoeff_tendsto
    {L : ℂ → ℂ} {A : ℕ → ℂ → ℂ}
    (hA : ∀ j, SatisfiesMilin (A j))
    (hcoeff : ∀ k : ℕ,
      Tendsto (fun j => logarithmicCoeff (A j) k) atTop
        (nhds (logarithmicCoeff L k))) :
    SatisfiesMilin L := by
  intro N
  apply le_of_tendsto (tendsto_milinFunctional_of_logarithmicCoeff hcoeff N)
  exact Eventually.of_forall fun j => hA j N

lemma satisfiesMilin_of_approximating_finiteConvexLoewnerRepresentations
    {L : ℂ → ℂ} {A : ℕ → ℂ → ℂ}
    (hrep : ∀ j N : ℕ,
      Nonempty (FiniteConvexLoewnerRepresentation (A j) N))
    (hcoeff : ∀ k : ℕ,
      Tendsto (fun j => logarithmicCoeff (A j) k) atTop
        (nhds (logarithmicCoeff L k))) :
    SatisfiesMilin L := by
  apply satisfiesMilin_of_logarithmicCoeff_tendsto
    (fun j => satisfiesMilin_of_finiteConvexLoewnerRepresentations (hrep j))
    hcoeff

lemma satisfiesMilin_of_orderwise_approximating_finiteConvexLoewnerRepresentations
    {L : ℂ → ℂ} {A : ℕ → ℕ → ℂ → ℂ}
    (hrep : ∀ N j : ℕ,
      Nonempty (FiniteConvexLoewnerRepresentation (A N j) N))
    (hcoeff : ∀ N k, k ∈ Finset.range N →
      Tendsto (fun j => logarithmicCoeff (A N j) (k + 1)) atTop
        (nhds (logarithmicCoeff L (k + 1)))) :
    SatisfiesMilin L := by
  intro N
  apply le_of_tendsto
    (tendsto_milinFunctional_of_logarithmicCoeff_up_to N
      (fun k hk => hcoeff N k hk))
  exact Eventually.of_forall fun j =>
    (hrep N j).some.certificate.milinFunctional_nonpos

lemma normalized_coeff_bound_of_orderwise_approximating_finiteConvexLoewnerRepresentations
    {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (Metric.ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ Metric.ball (0 : ℂ) R,
      Complex.exp (L z) = dslope f 0 z)
    {A : ℕ → ℕ → ℂ → ℂ}
    (hrep : ∀ N j : ℕ,
      Nonempty (FiniteConvexLoewnerRepresentation (A N j) N))
    (hcoeff : ∀ N k, k ∈ Finset.range N →
      Tendsto (fun j => logarithmicCoeff (A N j) (k + 1)) atTop
        (nhds (logarithmicCoeff L (k + 1)))) (n : ℕ) :
    ‖taylorCoeff f n‖ ≤ n := by
  exact normalized_coeff_bound_of_milin_only hR hf hL hL0 hexp
    (satisfiesMilin_of_orderwise_approximating_finiteConvexLoewnerRepresentations
      hrep hcoeff) n

end Submission
