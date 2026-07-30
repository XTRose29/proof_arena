import Submission.OddOrder.PF.Section02.DadeSetSignalizer
import Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset

/-!
# Orbits of nonempty subsets in the Dade expansion

The expansion of the Dade isometry is indexed by the nonempty subsets of the
Dade set, modulo conjugation by the complement `L`.  This file packages that
action and fixes one representative in every orbit.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u

variable {Γ : Type u} [Group Γ]

/-- A nonempty subset of the Dade set `A`. -/
abbrev DadeSubset (A : Set Γ) := {B : Set Γ // IsDadeSubset A B}

/-- Conjugating a Dade subset by an element of `L` again gives a Dade
subset.  The normalizer clause in `ddA` is precisely what preserves the
ambient set `A`. -/
@[reducible] private def dadeSubsetConjugationSMul
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) : SMul L (DadeSubset A) := by
  let conjugationAction := subgroupConjugationActionOnAmbient L
  letI : SMul L Γ := conjugationAction.toSMul
  letI : MulAction L Γ := conjugationAction.toMulAction
  letI : MulAction L (Set Γ) := Set.mulActionSet
  refine ⟨fun x B => ⟨x • (B : Set Γ), ?_⟩⟩
  constructor
  · intro y hy
    rcases Set.mem_smul_set.mp hy with ⟨b, hb, rfl⟩
    exact
      (Subgroup.mem_set_normalizer_iff.mp
        (ddA.1.2 x.property) b).mp (B.property.1 hb)
  · obtain ⟨b, hb⟩ := B.property.2
    exact ⟨x • b, Set.smul_mem_smul_set (a := x) hb⟩

/-- The conjugation action of `L` on the nonempty subsets of the Dade set
`A`.  This is kept as an explicit action value because it depends on the
proof `ddA` that `L` normalizes `A`. -/
@[reducible] def dadeSubsetConjugationAction
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) : MulAction L (DadeSubset A) := by
  let conjugationAction := subgroupConjugationActionOnAmbient L
  letI : SMul L Γ := conjugationAction.toSMul
  letI : MulAction L Γ := conjugationAction.toMulAction
  letI : MulAction L (Set Γ) := Set.mulActionSet
  letI : SMul L (DadeSubset A) := dadeSubsetConjugationSMul ddA
  exact Function.Injective.mulAction Subtype.val Subtype.coe_injective
    (fun _ _ => rfl)

/-- On underlying sets, the Dade-subset action is conjugation in the ambient
group. -/
@[simp] theorem coe_dadeSubset_smul
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : L) (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    ((x • B : DadeSubset A) : Set Γ) =
      MulAut.conj (x : Γ) '' (B : Set Γ) := by
  rfl

/-- The finite-orbit quotient of nonempty subsets of `A` by conjugation by
`L`. -/
abbrev DadeSubsetOrbit
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :=
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  MulAction.orbitRel.Quotient L (DadeSubset A)

/-- The representative of a Dade-subset orbit selected by `Quotient.out`.
This is the Lean counterpart of MathComp's `repr (B :^: L)`. -/
noncomputable def Dade_transversal
    {G L : Subgroup Γ} {A : Set Γ}
    {ddA : DadeHypothesis G L A}
    (omega : DadeSubsetOrbit ddA) : DadeSubset A := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  exact Quotient.out omega

/-- The selected representative maps back to its orbit label. -/
@[simp] theorem Dade_transversal_mk
    {G L : Subgroup Γ} {A : Set Γ}
    {ddA : DadeHypothesis G L A}
    (omega : DadeSubsetOrbit ddA) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    (Quotient.mk'' (Dade_transversal omega) : DadeSubsetOrbit ddA) = omega := by
  exact Quotient.out_eq' omega

/-- The selected representative is an element of the orbit that it
represents. -/
theorem Dade_transversal_mem_orbit
    {G L : Subgroup Γ} {A : Set Γ}
    {ddA : DadeHypothesis G L A}
    (omega : DadeSubsetOrbit ddA) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    Dade_transversal omega ∈
      MulAction.orbitRel.Quotient.orbit omega := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  rw [MulAction.orbitRel.Quotient.mem_orbit]
  exact Dade_transversal_mk omega

/-- An orbit is the conjugacy orbit of its selected representative. -/
theorem DadeSubsetOrbit.orbit_eq_transversal
    {G L : Subgroup Γ} {A : Set Γ}
    {ddA : DadeHypothesis G L A}
    (omega : DadeSubsetOrbit ddA) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    MulAction.orbitRel.Quotient.orbit omega =
      MulAction.orbit L (Dade_transversal omega) := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  exact MulAction.orbitRel.Quotient.orbit_eq_orbit_out
    omega Quotient.out_eq'

/-- Every Dade subset is conjugate under `L` to the representative of its
orbit.  This membership form is convenient for orbit reindexing. -/
theorem mem_orbit_Dade_transversal
    {G L : Subgroup Γ} {A : Set Γ}
    {ddA : DadeHypothesis G L A}
    (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    B ∈ MulAction.orbit L
      (Dade_transversal
        (Quotient.mk'' B : DadeSubsetOrbit ddA)) := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  let omega : DadeSubsetOrbit ddA := Quotient.mk'' B
  have hB : B ∈ MulAction.orbitRel.Quotient.orbit omega := by
    rw [MulAction.orbitRel.Quotient.mem_orbit]
  rw [DadeSubsetOrbit.orbit_eq_transversal] at hB
  exact hB

/-- Witness form of `mem_orbit_Dade_transversal`: a concrete element of `L`
conjugates the selected representative to the original subset. -/
theorem exists_smul_Dade_transversal_eq
    {G L : Subgroup Γ} {A : Set Γ}
    {ddA : DadeHypothesis G L A}
    (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    ∃ x : L,
      x • Dade_transversal
        (Quotient.mk'' B : DadeSubsetOrbit ddA) = B := by
  exact mem_orbit_Dade_transversal B

/-- Equivalently, the selected representative is a conjugate of the
original subset. -/
theorem exists_smul_eq_Dade_transversal
    {G L : Subgroup Γ} {A : Set Γ}
    {ddA : DadeHypothesis G L A}
    (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    ∃ x : L,
      x • B = Dade_transversal
        (Quotient.mk'' B : DadeSubsetOrbit ddA) := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  obtain ⟨x, hx⟩ := exists_smul_Dade_transversal_eq B
  refine ⟨x⁻¹, ?_⟩
  calc
    x⁻¹ • B = x⁻¹ •
        (x • Dade_transversal
          (Quotient.mk'' B : DadeSubsetOrbit ddA)) :=
      congrArg (fun C : DadeSubset A => x⁻¹ • C) hx.symm
    _ = Dade_transversal
        (Quotient.mk'' B : DadeSubsetOrbit ddA) := inv_smul_smul _ _

end

end Submission.OddOrder.PF
