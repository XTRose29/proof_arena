import Mathlib

namespace Submission.Helpers

open scoped BigOperators

/-! A small mod-two chain model used for barycentric subdivision.  Keeping coefficients in
`ZMod 2` makes orientations irrelevant, which is exactly what the parity proof of Sperner's
lemma needs. -/

noncomputable section

universe u v

/-- Finite simplicial chains with coefficients in `ZMod 2`. -/
abbrev ModTwoChain (V : Type*) := Finset V →₀ ZMod 2

/-- The chain consisting of one simplex. -/
def singletonChain {V : Type*} (s : Finset V) : ModTwoChain V :=
  Finsupp.single s 1

/-- The unoriented boundary of one simplex. -/
def simplexBoundary {V : Type*} [DecidableEq V] (s : Finset V) : ModTwoChain V :=
  ∑ v ∈ s, singletonChain (s.erase v)

/-- Extend the boundary operation linearly to finite chains. -/
def chainBoundary {V : Type*} [DecidableEq V] (c : ModTwoChain V) : ModTwoChain V :=
  c.sum fun s a ↦ a • simplexBoundary s

/-- Cone a chain from a new apex. Degenerate cones, where the apex is already present, vanish. -/
def chainCone {V : Type*} [DecidableEq V] (p : V) (c : ModTwoChain V) : ModTwoChain V :=
  c.sum fun s a ↦ if p ∈ s then 0 else a • singletonChain (insert p s)

@[simp] theorem chainBoundary_singletonChain {V : Type*} [DecidableEq V]
    (s : Finset V) : chainBoundary (singletonChain s) = simplexBoundary s := by
  classical
  ext t
  simp [chainBoundary, singletonChain]

@[simp] theorem chainBoundary_zero {V : Type*} [DecidableEq V] :
    chainBoundary (0 : ModTwoChain V) = 0 := by
  simp [chainBoundary]

theorem chainBoundary_add {V : Type*} [DecidableEq V] (a b : ModTwoChain V) :
    chainBoundary (a + b) = chainBoundary a + chainBoundary b := by
  classical
  unfold chainBoundary
  rw [Finsupp.sum_add_index'] <;> simp [add_smul]

theorem chainBoundary_smul {V : Type*} [DecidableEq V] (a : ZMod 2)
    (c : ModTwoChain V) : chainBoundary (a • c) = a • chainBoundary c := by
  classical
  unfold chainBoundary
  rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_smul]

@[simp] theorem chainCone_zero {V : Type*} [DecidableEq V] (p : V) :
    chainCone p (0 : ModTwoChain V) = 0 := by
  simp [chainCone]

theorem chainCone_add {V : Type*} [DecidableEq V] (p : V) (a b : ModTwoChain V) :
    chainCone p (a + b) = chainCone p a + chainCone p b := by
  classical
  unfold chainCone
  rw [Finsupp.sum_add_index']
  · intro s
    split <;> simp
  · intro s b₁ b₂
    split <;> simp [add_smul]

theorem chainCone_smul {V : Type*} [DecidableEq V] (p : V) (a : ZMod 2)
    (c : ModTwoChain V) : chainCone p (a • c) = a • chainCone p c := by
  classical
  unfold chainCone
  rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_smul]

@[simp] theorem chainCone_singletonChain {V : Type*} [DecidableEq V] (p : V)
    (s : Finset V) :
    chainCone p (singletonChain s) =
      if p ∈ s then 0 else singletonChain (insert p s) := by
  classical
  ext t
  simp [chainCone, singletonChain]

@[simp] theorem chainCone_finset_sum {V I : Type*} [DecidableEq V] (p : V)
    (s : Finset I) (f : I → ModTwoChain V) :
    chainCone p (∑ i ∈ s, f i) = ∑ i ∈ s, chainCone p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, chainCone_add]

@[simp] theorem modTwoChain_add_self {V : Type*} (c : ModTwoChain V) : c + c = 0 := by
  ext s
  exact CharTwo.add_self_eq_zero _

private theorem simplexBoundary_insert_of_not_mem {V : Type*} [DecidableEq V]
    (p : V) (s : Finset V) (hp : p ∉ s) :
    simplexBoundary (insert p s) =
      singletonChain s + chainCone p (simplexBoundary s) := by
  classical
  simp [simplexBoundary, hp]
  apply Finset.sum_congr rfl
  intro v hv
  have hvp : v ≠ p := by
    intro hvp
    subst v
    exact hp hv
  rw [Finset.erase_insert_of_ne hvp.symm]

private theorem chainCone_simplexBoundary_of_mem {V : Type*} [DecidableEq V]
    (p : V) (s : Finset V) (hp : p ∈ s) :
    chainCone p (simplexBoundary s) = singletonChain s := by
  classical
  rw [simplexBoundary, chainCone_finset_sum]
  rw [Finset.sum_eq_single p]
  · simp [hp]
  · intro b hb hbp
    have hmem : p ∈ s.erase b := Finset.mem_erase.mpr ⟨hbp.symm, hp⟩
    simp [hmem]
  · simp [hp]

private theorem chainBoundary_chainCone_singleton {V : Type*} [DecidableEq V]
    (p : V) (s : Finset V) :
    chainBoundary (chainCone p (singletonChain s)) +
        chainCone p (chainBoundary (singletonChain s)) = singletonChain s := by
  classical
  by_cases hp : p ∈ s
  · rw [chainCone_singletonChain, if_pos hp, chainBoundary_zero, zero_add,
      chainBoundary_singletonChain, chainCone_simplexBoundary_of_mem p s hp]
  · rw [chainCone_singletonChain, if_neg hp, chainBoundary_singletonChain,
      simplexBoundary_insert_of_not_mem p s hp, chainBoundary_singletonChain]
    calc
      singletonChain s + chainCone p (simplexBoundary s) +
          chainCone p (simplexBoundary s) =
          singletonChain s +
            (chainCone p (simplexBoundary s) + chainCone p (simplexBoundary s)) := by
              abel
      _ = singletonChain s := by rw [modTwoChain_add_self, add_zero]

theorem chainBoundary_chainCone {V : Type*} [DecidableEq V] (p : V)
    (c : ModTwoChain V) :
    chainBoundary (chainCone p c) + chainCone p (chainBoundary c) = c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add s a c _ _ ih =>
      have hsingle : Finsupp.single s a = a • singletonChain s := by
        ext t
        simp [singletonChain]
      have hscalar :
          chainBoundary (chainCone p (Finsupp.single s a)) +
              chainCone p (chainBoundary (Finsupp.single s a)) = Finsupp.single s a := by
        rw [hsingle, chainCone_smul, chainBoundary_smul, chainBoundary_smul,
          chainCone_smul, ← smul_add, chainBoundary_chainCone_singleton]
      rw [chainCone_add, chainBoundary_add, chainBoundary_add, chainCone_add]
      calc
        (chainBoundary (chainCone p (Finsupp.single s a)) +
              chainBoundary (chainCone p c)) +
            (chainCone p (chainBoundary (Finsupp.single s a)) +
              chainCone p (chainBoundary c)) =
            (chainBoundary (chainCone p (Finsupp.single s a)) +
                chainCone p (chainBoundary (Finsupp.single s a))) +
              (chainBoundary (chainCone p c) + chainCone p (chainBoundary c)) := by
                abel
        _ = Finsupp.single s a + c := by rw [hscalar, ih]

theorem chainBoundary_sq {V : Type*} [DecidableEq V] (c : ModTwoChain V) :
    chainBoundary (chainBoundary c) = 0 := by
  classical
  have hsingle : ∀ s : Finset V,
      chainBoundary (chainBoundary (singletonChain s)) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [simplexBoundary]
    | @insert p s hp ih =>
        have hcone : chainCone p (singletonChain s) = singletonChain (insert p s) := by
          simp [hp]
        rw [← hcone]
        have happly := congrArg chainBoundary
          (chainBoundary_chainCone p (singletonChain s))
        rw [chainBoundary_add] at happly
        have hconeBoundary := chainBoundary_chainCone p
          (chainBoundary (singletonChain s))
        rw [ih, chainCone_zero, add_zero] at hconeBoundary
        rw [hconeBoundary] at happly
        apply add_right_cancel (b := chainBoundary (singletonChain s))
        simpa using happly
  induction c using Finsupp.induction with
  | zero => simp
  | single_add s a c _ _ ih =>
      have hs : Finsupp.single s a = a • singletonChain s := by
        ext t
        simp [singletonChain]
      rw [chainBoundary_add, chainBoundary_add, ih, add_zero, hs,
        chainBoundary_smul, chainBoundary_smul, hsingle, smul_zero]

@[simp] theorem chainBoundary_finset_sum {V I : Type*} [DecidableEq V]
    (s : Finset I) (f : I → ModTwoChain V) :
    chainBoundary (∑ i ∈ s, f i) = ∑ i ∈ s, chainBoundary (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, chainBoundary_add]

/-- The top-dimensional chain in the barycentric subdivision of one simplex. -/
def subdivideSimplex {V : Type*} [DecidableEq V]
    (s : Finset V) : ModTwoChain (Finset V) :=
  if s = ∅ then singletonChain ∅
  else chainCone s (∑ v : s, subdivideSimplex (s.erase v))
termination_by s.card
decreasing_by
  simp_wf
  exact ⟨v, v.property⟩

/-- Barycentric subdivision, extended linearly to chains. -/
def subdivideChain {V : Type*} [DecidableEq V]
    (c : ModTwoChain V) : ModTwoChain (Finset V) :=
  c.sum fun s a ↦ a • subdivideSimplex s

@[simp] theorem subdivideChain_singletonChain {V : Type*} [DecidableEq V]
    (s : Finset V) : subdivideChain (singletonChain s) = subdivideSimplex s := by
  classical
  ext t
  simp [subdivideChain, singletonChain]

@[simp] theorem subdivideChain_zero {V : Type*} [DecidableEq V] :
    subdivideChain (0 : ModTwoChain V) = 0 := by
  simp [subdivideChain]

theorem subdivideChain_add {V : Type*} [DecidableEq V] (a b : ModTwoChain V) :
    subdivideChain (a + b) = subdivideChain a + subdivideChain b := by
  classical
  unfold subdivideChain
  rw [Finsupp.sum_add_index'] <;> simp [add_smul]

theorem subdivideChain_smul {V : Type*} [DecidableEq V] (a : ZMod 2)
    (c : ModTwoChain V) : subdivideChain (a • c) = a • subdivideChain c := by
  classical
  unfold subdivideChain
  rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_smul]

@[simp] theorem subdivideChain_finset_sum {V I : Type*} [DecidableEq V]
    (s : Finset I) (f : I → ModTwoChain V) :
    subdivideChain (∑ i ∈ s, f i) = ∑ i ∈ s, subdivideChain (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, subdivideChain_add]

/-- Barycentric subdivision commutes with the augmented boundary. -/
theorem chainBoundary_subdivideSimplex {V : Type*} [DecidableEq V]
    (s : Finset V) :
    chainBoundary (subdivideSimplex s) = subdivideChain (simplexBoundary s) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
      by_cases hs : s = ∅
      · subst s
        simp [subdivideSimplex, simplexBoundary]
      · rw [subdivideSimplex]
        simp only [hs, if_false]
        let c : ModTwoChain (Finset V) :=
          ∑ v : s, subdivideSimplex (s.erase v)
        have hc_eq : c = ∑ v ∈ s, subdivideSimplex (s.erase v) := by
          dsimp [c]
          simpa only [Finset.attach_eq_univ] using
            Finset.sum_attach s (fun v ↦ subdivideSimplex (s.erase v))
        change chainBoundary (chainCone s c) = subdivideChain (simplexBoundary s)
        have hc : chainBoundary c = 0 := by
          calc
            chainBoundary c =
                ∑ v ∈ s, chainBoundary (subdivideSimplex (s.erase v)) := by
                  rw [hc_eq, chainBoundary_finset_sum]
            _ = ∑ v ∈ s, subdivideChain (simplexBoundary (s.erase v)) := by
                  apply Finset.sum_congr rfl
                  intro v hv
                  exact ih (s.erase v) (Finset.erase_ssubset hv)
            _ = subdivideChain (∑ v ∈ s, simplexBoundary (s.erase v)) := by
                  symm
                  simp
            _ = subdivideChain (chainBoundary (simplexBoundary s)) := by
                  congr 1
                  rw [simplexBoundary, chainBoundary_finset_sum]
                  apply Finset.sum_congr rfl
                  intro v _
                  rw [chainBoundary_singletonChain]
            _ = 0 := by
                  rw [← chainBoundary_singletonChain s, chainBoundary_sq,
                    subdivideChain_zero]
        have hcone := chainBoundary_chainCone s c
        rw [hc, chainCone_zero, add_zero] at hcone
        rw [hcone]
        rw [hc_eq]
        simp [simplexBoundary]

/-- Barycentric subdivision is a chain map. -/
theorem chainBoundary_subdivideChain {V : Type*} [DecidableEq V]
    (c : ModTwoChain V) :
    chainBoundary (subdivideChain c) = subdivideChain (chainBoundary c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add s a c _ _ ih =>
      have hs : Finsupp.single s a = a • singletonChain s := by
        ext t
        simp [singletonChain]
      rw [subdivideChain_add, chainBoundary_add, chainBoundary_add,
        subdivideChain_add, ih, hs, subdivideChain_smul, chainBoundary_smul,
        chainBoundary_smul, subdivideChain_smul, subdivideChain_singletonChain,
        chainBoundary_singletonChain, chainBoundary_subdivideSimplex]

/-- Vertex types obtained by repeatedly replacing vertices with finite faces. -/
def SubdivisionVertex (V : Type u) : ℕ → Type u
  | 0 => V
  | k + 1 => Finset (SubdivisionVertex V k)

/-- Decidable equality propagates through every level of iterated subdivision. -/
instance {V : Type*} [DecidableEq V] (k : ℕ) :
    DecidableEq (SubdivisionVertex V k) := by
  induction k with
  | zero =>
      change DecidableEq V
      infer_instance
  | succ k ih =>
      change DecidableEq (Finset (SubdivisionVertex V k))
      letI : DecidableEq (SubdivisionVertex V k) := ih
      infer_instance

/-- Repeated barycentric subdivision of a single simplex. -/
def iteratedSubdivision {V : Type*} [DecidableEq V]
    (s : Finset V) : (k : ℕ) → ModTwoChain (SubdivisionVertex V k)
  | 0 => singletonChain s
  | k + 1 => by
      classical
      exact subdivideChain (iteratedSubdivision s k)

/-- The original vertices supporting a vertex of an iterated subdivision. -/
def vertexCarrier {V : Type*} [DecidableEq V] :
    (k : ℕ) → SubdivisionVertex V k → Finset V
  | 0, v => {v}
  | k + 1, s => by
      classical
      exact s.biUnion (vertexCarrier k)

/-- The average of a finite family, with the empty average defined to be zero. -/
def finsetAverage {V E : Type*} [DecidableEq V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : V → E) (s : Finset V) : E :=
  (s.card : ℝ)⁻¹ • ∑ v ∈ s, p v

/-- Geometric realization of vertices in an iterated barycentric subdivision. -/
def subdivisionPosition {V E : Type*} [DecidableEq V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : V → E) :
    (k : ℕ) → SubdivisionVertex V k → E
  | 0, v => p v
  | k + 1, s => by
      classical
      exact finsetAverage (subdivisionPosition p k) s

end

end Submission.Helpers
