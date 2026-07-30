import Submission.DeBrangesRepresentation

open Filter

namespace Submission

lemma weighted_affine_sum {ι : Type*} [Fintype ι]
    (w b : ι → ℝ) (a q : ℝ) (hw : ∑ i, w i = 1) :
    a + q * ∑ i, w i * b i = ∑ i, w i * (a + q * b i) := by
  calc
    a + q * ∑ i, w i * b i =
        (∑ i, w i) * a + q * ∑ i, w i * b i := by rw [hw]; ring
    _ = ∑ i, (w i * a + q * (w i * b i)) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ i, w i * (a + q * b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Finite-dimensional Herglotz data: the coefficient velocity is a convex
combination of velocities produced by unit-circle boundary drivers. -/
structure FiniteConvexLoewnerData (N : ℕ) (c cDot : ℕ → ℂ) where
  m : ℕ
  weight : Fin m → ℝ
  direction : Fin m → ℕ → ℂ
  omega : Fin m → ℂ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  norm_omega : ∀ i, ‖omega i‖ = 1
  point_ode : ∀ i, SatisfiesDrivenLoewnerLogarithmicODE N c (direction i) (omega i)
  average : ∀ k ∈ Finset.range N,
    cDot (k + 1) = ∑ i, (weight i : ℂ) * direction i (k + 1)

lemma deBrangesEnergyRate_eq_convex_sum
    {N : ℕ} {tau tauDot : ℕ → ℝ} {c cDot : ℕ → ℂ}
    (data : FiniteConvexLoewnerData N c cDot) :
    deBrangesEnergyRate N tau tauDot c cDot =
      ∑ i, data.weight i *
        deBrangesEnergyRate N tau tauDot c (data.direction i) := by
  unfold deBrangesEnergyRate
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [data.average k hk]
  rw [Finset.sum_mul, Complex.re_sum]
  simp_rw [mul_assoc, Complex.re_ofReal_mul]
  let a := tauDot (k + 1) * ‖c (k + 1)‖ ^ 2
  let q := 2 * tau (k + 1)
  let b := fun i =>
    (data.direction i (k + 1) * starRingEnd ℂ (c (k + 1))).re
  have h := weighted_affine_sum data.weight b a q data.weight_sum
  calc
    _ = ((k + 1 : ℕ) : ℝ) * (a + q * ∑ i, data.weight i * b i) := by
      simp only [a, q, b]
      ring
    _ = ((k + 1 : ℕ) : ℝ) * ∑ i, data.weight i * (a + q * b i) := by rw [h]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [a, q, b]
      ring

lemma deBrangesEnergyRate_lower_bound_convex
    {N : ℕ} {tau tauDot : ℕ → ℝ} {c cDot : ℕ → ℂ}
    (hsystem : SatisfiesDeBrangesSystem N tau tauDot)
    (data : FiniteConvexLoewnerData N c cDot)
    (htauDot : ∀ k ∈ Finset.range N, tauDot (k + 1) ≤ 0) :
    (tauDot 1 - tau 1) / 2 ≤
      deBrangesEnergyRate N tau tauDot c cDot := by
  rw [deBrangesEnergyRate_eq_convex_sum data]
  calc
    (tauDot 1 - tau 1) / 2 =
        ∑ i, data.weight i * ((tauDot 1 - tau 1) / 2) := by
      rw [← Finset.sum_mul, data.weight_sum, one_mul]
    _ ≤ ∑ i, data.weight i *
        deBrangesEnergyRate N tau tauDot c (data.direction i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (deBrangesEnergyRate_lower_bound_driven hsystem
          (data.norm_omega i) (data.point_ode i) htauDot)
        (data.weight_nonneg i)

/-- A de Branges certificate whose Loewner velocity is allowed to be a finite
convex combination of boundary-driver velocities.  This is the finite-order
form needed for a general Herglotz function. -/
structure ConvexDeBrangesMilinCertificate (L : ℂ → ℂ) (N : ℕ) where
  c : ℕ → ℝ → ℂ
  cDot : ℕ → ℝ → ℂ
  tau : ℕ → ℝ → ℝ
  tauDot : ℕ → ℝ → ℝ
  c_initial : ∀ k ∈ Finset.range N, c (k + 1) 0 = logarithmicCoeff L (k + 1)
  tau_initial : ∀ k ∈ Finset.range N, tau (k + 1) 0 = ((N - k : ℕ) : ℝ)
  hasDerivAt_c : ∀ k ∈ Finset.range N, ∀ t, 0 ≤ t →
    HasDerivAt (c (k + 1)) (cDot (k + 1) t) t
  hasDerivAt_tau : ∀ k ∈ Finset.range N, ∀ t, 0 ≤ t →
    HasDerivAt (tau (k + 1)) (tauDot (k + 1) t) t
  loewnerData : ∀ t, 0 ≤ t →
    Nonempty (FiniteConvexLoewnerData N (fun k => c k t) (fun k => cDot k t))
  deBrangesSystem : ∀ t, 0 ≤ t →
    SatisfiesDeBrangesSystem N (fun k => tau k t) (fun k => tauDot k t)
  tauDot_nonpos : ∀ t, 0 ≤ t → ∀ k ∈ Finset.range N, tauDot (k + 1) t ≤ 0
  gap_tendsto_zero : Tendsto (deBrangesGap N tau c) atTop (nhds 0)

lemma ConvexDeBrangesMilinCertificate.hasDerivAt_gap
    {L : ℂ → ℂ} {N : ℕ} (cert : ConvexDeBrangesMilinCertificate L N)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (deBrangesGap N cert.tau cert.c)
      (deBrangesEnergyRate N (fun k => cert.tau k t) (fun k => cert.tauDot k t)
          (fun k => cert.c k t) (fun k => cert.cDot k t) -
        deBrangesWeightRate N (fun k => cert.tauDot k t)) t := by
  exact hasDerivAt_deBrangesGap
    (fun k hk => cert.hasDerivAt_tau k hk t ht)
    (fun k hk => cert.hasDerivAt_c k hk t ht)

lemma ConvexDeBrangesMilinCertificate.gap_mono
    {L : ℂ → ℂ} {N : ℕ} (cert : ConvexDeBrangesMilinCertificate L N) :
    MonotoneOn (deBrangesGap N cert.tau cert.c) (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro t ht
    exact (cert.hasDerivAt_gap ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := by
      have ht' : t ∈ Set.Ioi 0 := by simpa only [interior_Ici] using ht
      exact (Set.mem_Ioi.mp ht').le
    exact (cert.hasDerivAt_gap ht0).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := by
      have ht' : t ∈ Set.Ioi 0 := by simpa only [interior_Ici] using ht
      exact (Set.mem_Ioi.mp ht').le
    have hgap := cert.hasDerivAt_gap ht0
    rw [hgap.deriv]
    have hrate := deBrangesEnergyRate_lower_bound_convex
      (cert.deBrangesSystem t ht0) (cert.loewnerData t ht0).some
      (cert.tauDot_nonpos t ht0)
    have hweight := deBrangesSystem_boundary_eq_weightRate
      (cert.deBrangesSystem t ht0)
    linarith

lemma ConvexDeBrangesMilinCertificate.gap_zero_eq_milinFunctional
    {L : ℂ → ℂ} {N : ℕ} (cert : ConvexDeBrangesMilinCertificate L N) :
    deBrangesGap N cert.tau cert.c 0 = milinFunctional L N := by
  rw [milinFunctional_eq_weighted]
  unfold deBrangesGap deBrangesEnergy deBrangesWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  change
    ((k + 1 : ℕ) : ℝ) * cert.tau (k + 1) 0 * ‖cert.c (k + 1) 0‖ ^ 2 -
        cert.tau (k + 1) 0 / ((k + 1 : ℕ) : ℝ) =
      ((N - k : ℕ) : ℝ) *
        (((k + 1 : ℕ) : ℝ) * ‖logarithmicCoeff L (k + 1)‖ ^ 2 -
          1 / ((k + 1 : ℕ) : ℝ))
  rw [cert.c_initial k hk, cert.tau_initial k hk]
  ring

lemma ConvexDeBrangesMilinCertificate.milinFunctional_nonpos
    {L : ℂ → ℂ} {N : ℕ} (cert : ConvexDeBrangesMilinCertificate L N) :
    milinFunctional L N ≤ 0 := by
  have hle : deBrangesGap N cert.tau cert.c 0 ≤ 0 := by
    apply ge_of_tendsto cert.gap_tendsto_zero
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact cert.gap_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  rwa [cert.gap_zero_eq_milinFunctional] at hle

lemma satisfiesMilin_of_convex_deBranges_certificates {L : ℂ → ℂ}
    (hcert : ∀ N : ℕ, Nonempty (ConvexDeBrangesMilinCertificate L N)) :
    SatisfiesMilin L := by
  intro N
  exact (hcert N).some.milinFunctional_nonpos

/-- A finite-order representation by general Herglotz data.  Coefficients only
need to converge to finite limits: the explicit de Branges weights tend to
zero, so convergence to the identity is unnecessarily restrictive. -/
structure FiniteConvexLoewnerRepresentation (L : ℂ → ℂ) (N : ℕ) where
  c : ℕ → ℝ → ℂ
  cDot : ℕ → ℝ → ℂ
  cLimit : ℕ → ℂ
  c_initial : ∀ k ∈ Finset.range N, c (k + 1) 0 = logarithmicCoeff L (k + 1)
  hasDerivAt_c : ∀ k ∈ Finset.range N, ∀ t, 0 ≤ t →
    HasDerivAt (c (k + 1)) (cDot (k + 1) t) t
  loewnerData : ∀ t, 0 ≤ t →
    Nonempty (FiniteConvexLoewnerData N (fun k => c k t) (fun k => cDot k t))
  c_tendsto : ∀ k ∈ Finset.range N, Tendsto (c (k + 1)) atTop (nhds (cLimit (k + 1)))

lemma FiniteConvexLoewnerRepresentation.energy_tendsto_zero
    {L : ℂ → ℂ} {N : ℕ} (rep : FiniteConvexLoewnerRepresentation L N) :
    Tendsto
      (fun t => deBrangesEnergy N
        (fun k => explicitDeBrangesTau N k t) (fun k => rep.c k t))
      atTop (nhds 0) := by
  unfold deBrangesEnergy
  convert tendsto_finsetSum (Finset.range N) (fun k hk => by
    have htau := tendsto_explicitDeBrangesTau N (k + 1) (by omega)
    have hc : Tendsto (fun t => ‖rep.c (k + 1) t‖ ^ 2) atTop
        (nhds (‖rep.cLimit (k + 1)‖ ^ 2)) :=
      (rep.c_tendsto k hk).norm.pow 2
    simpa only [zero_mul] using
      (htau.mul hc).const_mul (((k + 1 : ℕ) : ℝ))) using 1 <;>
    simp [mul_assoc]

lemma FiniteConvexLoewnerRepresentation.gap_tendsto_zero
    {L : ℂ → ℂ} {N : ℕ} (rep : FiniteConvexLoewnerRepresentation L N) :
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

noncomputable def FiniteConvexLoewnerRepresentation.certificate
    {L : ℂ → ℂ} {N : ℕ} (rep : FiniteConvexLoewnerRepresentation L N) :
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

lemma satisfiesMilin_of_finiteConvexLoewnerRepresentations {L : ℂ → ℂ}
    (hrep : ∀ N : ℕ, Nonempty (FiniteConvexLoewnerRepresentation L N)) :
    SatisfiesMilin L := by
  apply satisfiesMilin_of_convex_deBranges_certificates
  intro N
  exact ⟨(hrep N).some.certificate⟩

end Submission
