import Submission.ConvexLoewner

open Filter

namespace Submission

/-- The exact asymptotic interface used by the de Branges energy argument.
Unlike `FiniteConvexLoewnerRepresentation`, this structure does not require
the individual coefficient paths to converge.  It only records the weighted
energy decay which is actually used at infinity. -/
structure FiniteConvexLoewnerEnergyRepresentation (L : ℂ → ℂ) (N : ℕ) where
  c : ℕ → ℝ → ℂ
  cDot : ℕ → ℝ → ℂ
  c_initial : ∀ k ∈ Finset.range N,
    c (k + 1) 0 = logarithmicCoeff L (k + 1)
  hasDerivAt_c : ∀ k ∈ Finset.range N, ∀ t, 0 ≤ t →
    HasDerivAt (c (k + 1)) (cDot (k + 1) t) t
  loewnerData : ∀ t, 0 ≤ t →
    Nonempty (FiniteConvexLoewnerData N
      (fun k => c k t) (fun k => cDot k t))
  energy_tendsto_zero : Tendsto
    (fun t => deBrangesEnergy N
      (fun k => explicitDeBrangesTau N k t) (fun k => c k t))
    atTop (nhds 0)

lemma FiniteConvexLoewnerEnergyRepresentation.gap_tendsto_zero
    {L : ℂ → ℂ} {N : ℕ}
    (rep : FiniteConvexLoewnerEnergyRepresentation L N) :
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

noncomputable def FiniteConvexLoewnerEnergyRepresentation.certificate
    {L : ℂ → ℂ} {N : ℕ}
    (rep : FiniteConvexLoewnerEnergyRepresentation L N) :
    ConvexDeBrangesMilinCertificate L N where
  c := rep.c
  cDot := rep.cDot
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
  loewnerData := rep.loewnerData
  deBrangesSystem := fun t ht => explicitDeBranges_satisfies_system N t
  tauDot_nonpos := by
    intro t ht k hk
    exact explicitDeBrangesTauDot_nonpos_of_gasper satisfiesGasperIdentities
      (by omega) (Finset.mem_range.mp hk) ht
  gap_tendsto_zero := rep.gap_tendsto_zero

lemma satisfiesMilin_of_finiteConvexLoewnerEnergyRepresentations
    {L : ℂ → ℂ}
    (hrep : ∀ N : ℕ,
      Nonempty (FiniteConvexLoewnerEnergyRepresentation L N)) :
    SatisfiesMilin L := by
  intro N
  exact (hrep N).some.certificate.milinFunctional_nonpos

/-- A bounded-coefficient version of the finite convex representation.  This
is the natural output of a normalized univalent Loewner chain: compactness of
each finite coefficient body gives the boundedness, while no coefficientwise
limit of the chain has to be selected. -/
structure FiniteBoundedConvexLoewnerRepresentation (L : ℂ → ℂ) (N : ℕ) where
  c : ℕ → ℝ → ℂ
  cDot : ℕ → ℝ → ℂ
  c_initial : ∀ k ∈ Finset.range N,
    c (k + 1) 0 = logarithmicCoeff L (k + 1)
  hasDerivAt_c : ∀ k ∈ Finset.range N, ∀ t, 0 ≤ t →
    HasDerivAt (c (k + 1)) (cDot (k + 1) t) t
  loewnerData : ∀ t, 0 ≤ t →
    Nonempty (FiniteConvexLoewnerData N
      (fun k => c k t) (fun k => cDot k t))
  coeffSq_isBounded : ∀ k ∈ Finset.range N,
    IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun t => ‖c (k + 1) t‖ ^ 2)

noncomputable def FiniteBoundedConvexLoewnerRepresentation.toEnergyRepresentation
    {L : ℂ → ℂ} {N : ℕ}
    (rep : FiniteBoundedConvexLoewnerRepresentation L N) :
    FiniteConvexLoewnerEnergyRepresentation L N where
  c := rep.c
  cDot := rep.cDot
  c_initial := rep.c_initial
  hasDerivAt_c := rep.hasDerivAt_c
  loewnerData := rep.loewnerData
  energy_tendsto_zero := by
    unfold deBrangesEnergy
    convert tendsto_finsetSum (Finset.range N) (fun k hk => by
      have htau := tendsto_explicitDeBrangesTau N (k + 1) (by omega)
      have hprod : Tendsto
          (fun t => explicitDeBrangesTau N (k + 1) t *
            ‖rep.c (k + 1) t‖ ^ 2) atTop (nhds 0) :=
        htau.zero_mul_isBoundedUnder_le (rep.coeffSq_isBounded k hk)
      simpa only [mul_zero] using
        hprod.const_mul (((k + 1 : ℕ) : ℝ))) using 1 <;>
      simp [mul_assoc]

lemma satisfiesMilin_of_finiteBoundedConvexLoewnerRepresentations
    {L : ℂ → ℂ}
    (hrep : ∀ N : ℕ,
      Nonempty (FiniteBoundedConvexLoewnerRepresentation L N)) :
    SatisfiesMilin L := by
  apply satisfiesMilin_of_finiteConvexLoewnerEnergyRepresentations
  intro N
  exact ⟨(hrep N).some.toEnergyRepresentation⟩

/-- Every convergent finite convex representation supplies the weaker energy
interface.  This keeps all existing representation results usable. -/
noncomputable def FiniteConvexLoewnerRepresentation.toEnergyRepresentation
    {L : ℂ → ℂ} {N : ℕ} (rep : FiniteConvexLoewnerRepresentation L N) :
    FiniteConvexLoewnerEnergyRepresentation L N where
  c := rep.c
  cDot := rep.cDot
  c_initial := rep.c_initial
  hasDerivAt_c := rep.hasDerivAt_c
  loewnerData := rep.loewnerData
  energy_tendsto_zero := rep.energy_tendsto_zero

end Submission
