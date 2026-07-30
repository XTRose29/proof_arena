import Submission.DeBrangesGasper
import Submission.DeBrangesSystem

open Filter

namespace Submission

structure FiniteDrivenLoewnerRepresentation (L : ℂ → ℂ) (N : ℕ) where
  c : ℕ → ℝ → ℂ
  cDot : ℕ → ℝ → ℂ
  omega : ℝ → ℂ
  c_initial : ∀ k ∈ Finset.range N, c (k + 1) 0 = logarithmicCoeff L (k + 1)
  hasDerivAt_c :
    ∀ k ∈ Finset.range N, ∀ t, 0 ≤ t → HasDerivAt (c (k + 1)) (cDot (k + 1) t) t
  norm_omega : ∀ t, 0 ≤ t → ‖omega t‖ = 1
  loewnerODE : ∀ t, 0 ≤ t →
    SatisfiesDrivenLoewnerLogarithmicODE N
      (fun k => c k t) (fun k => cDot k t) (omega t)
  c_tendsto_zero : ∀ k ∈ Finset.range N, Tendsto (c (k + 1)) atTop (nhds 0)

lemma FiniteDrivenLoewnerRepresentation.energy_tendsto_zero {L : ℂ → ℂ} {N : ℕ}
    (rep : FiniteDrivenLoewnerRepresentation L N) :
    Tendsto
      (fun t => deBrangesEnergy N
        (fun k => explicitDeBrangesTau N k t) (fun k => rep.c k t))
      atTop (nhds 0) := by
  unfold deBrangesEnergy
  convert tendsto_finsetSum (Finset.range N) (fun k hk => by
    have htau := tendsto_explicitDeBrangesTau N (k + 1) (by omega)
    have hc : Tendsto (fun t => ‖rep.c (k + 1) t‖ ^ 2) atTop (nhds 0) := by
      simpa using (rep.c_tendsto_zero k hk).norm.pow 2
    simpa only [mul_zero] using
      (htau.mul hc).const_mul (((k + 1 : ℕ) : ℝ))) using 1 <;>
    simp [mul_assoc]

lemma explicitDeBrangesWeight_tendsto_zero (N : ℕ) :
    Tendsto
      (fun t => deBrangesWeight N (fun k => explicitDeBrangesTau N k t))
      atTop (nhds 0) := by
  unfold deBrangesWeight
  convert tendsto_finsetSum (Finset.range N) (fun k hk =>
    (tendsto_explicitDeBrangesTau N (k + 1) (by omega)).div_const
      (((k + 1 : ℕ) : ℝ))) using 1;
    simp

lemma FiniteDrivenLoewnerRepresentation.gap_tendsto_zero {L : ℂ → ℂ} {N : ℕ}
    (rep : FiniteDrivenLoewnerRepresentation L N) :
    Tendsto
      (deBrangesGap N (fun k t => explicitDeBrangesTau N k t) rep.c)
      atTop (nhds 0) := by
  change Tendsto
    (fun t =>
      deBrangesEnergy N
          (fun k => explicitDeBrangesTau N k t) (fun k => rep.c k t) -
        deBrangesWeight N (fun k => explicitDeBrangesTau N k t))
    atTop (nhds 0)
  simpa only [sub_self] using
    rep.energy_tendsto_zero.sub (explicitDeBrangesWeight_tendsto_zero N)

noncomputable def FiniteDrivenLoewnerRepresentation.certificate
    {L : ℂ → ℂ} {N : ℕ} (rep : FiniteDrivenLoewnerRepresentation L N) :
    DeBrangesMilinCertificate L N where
  c := rep.c
  cDot := rep.cDot
  omega := rep.omega
  tau := fun k t => explicitDeBrangesTau N k t
  tauDot := fun k t => explicitDeBrangesTauDot N k t
  c_initial := rep.c_initial
  tau_initial := by
    intro k hk
    have hkN : k + 1 ≤ N := Finset.mem_range.mp hk
    rw [explicitDeBrangesTau_zero (by omega) hkN]
    congr 1
    omega
  hasDerivAt_c := rep.hasDerivAt_c
  hasDerivAt_tau := by
    intro k hk t ht
    exact hasDerivAt_explicitDeBrangesTau N (k + 1) t
  norm_omega := rep.norm_omega
  loewnerODE := rep.loewnerODE
  deBrangesSystem := fun t ht => explicitDeBranges_satisfies_system N t
  tauDot_nonpos := by
    intro t ht k hk
    exact explicitDeBrangesTauDot_nonpos_of_gasper satisfiesGasperIdentities
      (by omega) (Finset.mem_range.mp hk) ht
  gap_tendsto_zero := rep.gap_tendsto_zero

lemma satisfiesMilin_of_finiteDrivenLoewnerRepresentations {L : ℂ → ℂ}
    (hrep : ∀ N : ℕ, Nonempty (FiniteDrivenLoewnerRepresentation L N)) :
    SatisfiesMilin L := by
  apply satisfiesMilin_of_deBranges_certificates
  intro N
  exact ⟨(hrep N).some.certificate⟩

lemma normalized_coeff_bound_of_finiteDrivenLoewnerRepresentations
    {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) (hL : DifferentiableOn ℂ L (Metric.ball 0 R))
    (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ Metric.ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hrep : ∀ N : ℕ, Nonempty (FiniteDrivenLoewnerRepresentation L N))
    (n : ℕ) : ‖taylorCoeff f n‖ ≤ n := by
  exact normalized_coeff_bound_of_milin_only hR hf hL hL0 hexp
    (satisfiesMilin_of_finiteDrivenLoewnerRepresentations hrep) n

end Submission
