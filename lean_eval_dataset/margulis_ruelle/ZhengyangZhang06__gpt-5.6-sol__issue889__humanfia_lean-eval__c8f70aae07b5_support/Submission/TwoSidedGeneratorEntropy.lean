import Submission.GeneratorEntropy

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

noncomputable def centeredIndexObservation
    {M : Type*} (T T_inv : M → M) (P : Finset (Set M)) (d : ↥P)
    (m n : ℕ) (x : M) : Fin (m + n) → Fin (Fintype.card ↥P) :=
  fun i => if _h : i.val < m then
    partitionIndexLabel P d (T_inv^[m - i.val] x)
  else partitionIndexLabel P d (T^[i.val - m] x)

lemma measurable_centeredIndexObservation
    {M : Type*} [MeasurableSpace M]
    (T T_inv : M → M) (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (d : ↥P)
    (m n : ℕ) :
    Measurable (centeredIndexObservation T T_inv P d m n) := by
  apply measurable_pi_lambda
  intro i
  unfold centeredIndexObservation
  split_ifs with hi
  · exact (measurable_partitionIndexLabel P hP d).comp
      (hT_inv.iterate (m - i.val))
  · exact (measurable_partitionIndexLabel P hP d).comp
      (hT.iterate (i.val - m))

lemma centeredIndexObservation_eq_observationBlock_comp
    {M : Type*}
    (T T_inv : M → M) (hT_right : Function.RightInverse T_inv T)
    (P : Finset (Set M)) (d : ↥P) (m n : ℕ) :
    centeredIndexObservation T T_inv P d m n =
      fun x => observationBlock T (partitionIndexLabel P d) (m + n)
        (T_inv^[m] x) := by
  funext x i
  unfold centeredIndexObservation observationBlock
  split_ifs with hi
  · rw [iterate_before_inverse_cancel hT_right hi.le]
  · have hmi : m ≤ i.val := le_of_not_gt hi
    have hsum : m + (i.val - m) = i.val := Nat.add_sub_of_le hmi
    rw [← hsum, iterate_after_inverse_cancel hT_right]
    congr 2
    omega

lemma observationEntropy_centeredIndexObservation
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) (d : ↥P)
    (m n : ℕ) :
    observationEntropy mu (centeredIndexObservation T T_inv P d m n) =
      partitionEntropy mu (iteratedJoin T P (m + n)) := by
  rw [centeredIndexObservation_eq_observationBlock_comp
    T T_inv hT_right P d m n]
  rw [observationEntropy_comp_measurePreserving mu (T_inv^[m])
    (hT_inv.iterate m)
    (observationBlock T (partitionIndexLabel P d) (m + n))
    (measurable_observationBlock T hT.measurable (partitionIndexLabel P d)
      (measurable_partitionIndexLabel P hP.measurable d) (m + n))]
  exact observationEntropy_observationBlock_partitionIndexLabel
    mu T hT P hP d (m + n)

lemma partitionSymbol_eq_of_unique_of_indexLabel_eq
    {M : Type*} (P : Finset (Set M)) (d : ↥P) {x y : M}
    (hx : ∃! A : Set M, A ∈ P ∧ x ∈ A)
    (hy : ∃! A : Set M, A ∈ P ∧ y ∈ A)
    (hlabel : partitionIndexLabel P d x = partitionIndexLabel P d y) :
    partitionSymbol P x = partitionSymbol P y := by
  classical
  obtain ⟨A, hAP, hxA⟩ := hx.exists
  obtain ⟨B, hBP, hyB⟩ := hy.exists
  have hxlabel := partitionLabel_eq_of_unique P d hx hAP hxA
  have hylabel := partitionLabel_eq_of_unique P d hy hBP hyB
  have hABsub : (⟨A, hAP⟩ : ↥P) = ⟨B, hBP⟩ := by
    apply (Fintype.equivFin ↥P).injective
    simpa [partitionIndexLabel, hxlabel, hylabel] using hlabel
  have hAB : A = B := congrArg Subtype.val hABsub
  funext C
  have hmem : x ∈ C.1 ↔ y ∈ C.1 := by
    constructor
    · intro hxC
      have hCA : C.1 = A := hx.unique ⟨C.2, hxC⟩ ⟨hAP, hxA⟩
      rw [hCA, hAB]
      exact hyB
    · intro hyC
      have hCB : C.1 = B := hy.unique ⟨C.2, hyC⟩ ⟨hBP, hyB⟩
      rw [hCB, ← hAB]
      exact hxA
  by_cases hxC : x ∈ C.1
  · have hyC := hmem.mp hxC
    simp [partitionSymbol, hxC, hyC]
  · have hyC : y ∉ C.1 := fun h => hxC (hmem.mpr h)
    simp [partitionSymbol, hxC, hyC]

noncomputable def partitionOrbitUniqueSet
    {M : Type*} (T T_inv : M → M) (P : Finset (Set M)) : Set M :=
  {x | ∀ z : ℤ, ∃! A : Set M, A ∈ P ∧ biIterate T T_inv z x ∈ A}

lemma partitionOrbitUniqueSet_compl_measure_zero
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T T_inv : M → M)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P) :
    mu (partitionOrbitUniqueSet T T_inv P)ᶜ = 0 := by
  apply mem_ae_iff.mp
  change ∀ᵐ x ∂mu, ∀ z : ℤ,
    ∃! A : Set M, A ∈ P ∧ biIterate T T_inv z x ∈ A
  rw [ae_all_iff]
  intro z
  cases z with
  | ofNat n =>
      exact ae_existsUnique_partition_atom_iterate mu T hT P hP n
  | negSucc n =>
      exact ae_existsUnique_partition_atom_iterate mu T_inv hT_inv P hP (n + 1)

lemma partitionIndexLabel_iterate_eq_of_centeredIndexObservation_eq
    {M : Type*} (T T_inv : M → M) (P : Finset (Set M)) (d : ↥P)
    {m n : ℕ} {x y : M}
    (hcenter : centeredIndexObservation T T_inv P d m n x =
      centeredIndexObservation T T_inv P d m n y)
    {a : ℕ} (ha : a < n) :
    partitionIndexLabel P d (T^[a] x) =
      partitionIndexLabel P d (T^[a] y) := by
  let i : Fin (m + n) := ⟨m + a, by omega⟩
  have hi := congrFun hcenter i
  simpa [centeredIndexObservation, i] using hi

lemma partitionIndexLabel_inverseIterate_eq_of_centeredIndexObservation_eq
    {M : Type*} (T T_inv : M → M) (P : Finset (Set M)) (d : ↥P)
    {m n : ℕ} {x y : M}
    (hcenter : centeredIndexObservation T T_inv P d m n x =
      centeredIndexObservation T T_inv P d m n y)
    {q : ℕ} (hq_pos : 0 < q) (hq : q ≤ m) :
    partitionIndexLabel P d (T_inv^[q] x) =
      partitionIndexLabel P d (T_inv^[q] y) := by
  let i : Fin (m + n) := ⟨m - q, by omega⟩
  have hi := congrFun hcenter i
  have heval (z : M) : centeredIndexObservation T T_inv P d m n z i =
      partitionIndexLabel P d (T_inv^[q] z) := by
    unfold centeredIndexObservation
    rw [dif_pos (by dsimp [i]; omega)]
    congr 2
    dsimp [i]
    omega
  rw [heval x, heval y] at hi
  exact hi

lemma observationEntropy_observationBlock_twoSidedObservation_le
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (d : ↥P) (r N : ℕ) :
    observationEntropy mu
        (observationBlock T (twoSidedObservation T T_inv P r) N) ≤
      partitionEntropy mu (iteratedJoin T P (N + 2 * (r + 1))) := by
  let m := r + 1
  let n := N + (r + 1)
  let X := observationBlock T (twoSidedObservation T T_inv P r) N
  let Z := centeredIndexObservation T T_inv P d m n
  let good := partitionOrbitUniqueSet T T_inv P
  have hZ : Measurable Z :=
    measurable_centeredIndexObservation T T_inv hT.measurable hT_inv.measurable
      P hP.measurable d m n
  have hfull : mu goodᶜ = 0 :=
    partitionOrbitUniqueSet_compl_measure_zero mu T T_inv hT hT_inv P hP
  have hdet : ∀ x ∈ good, ∀ y ∈ good, Z x = Z y → X x = X y := by
    intro x hx y hy hcenter
    change ∀ z : ℤ, ∃! A : Set M,
      A ∈ P ∧ biIterate T T_inv z x ∈ A at hx
    change ∀ z : ℤ, ∃! A : Set M,
      A ∈ P ∧ biIterate T T_inv z y ∈ A at hy
    funext j k
    have hk : k.1 ≤ r := k.2
    change partitionSymbol P
        (biIterate T T_inv (Equiv.intEquivNat.symm k.1) (T^[j.val] x)) =
      partitionSymbol P
        (biIterate T T_inv (Equiv.intEquivNat.symm k.1) (T^[j.val] y))
    have hcode := Equiv.apply_symm_apply Equiv.intEquivNat k.1
    cases hz : Equiv.intEquivNat.symm k.1 with
    | ofNat a =>
        have hka : 2 * a = k.1 := by
          rw [hz] at hcode
          exact hcode
        have ha : a ≤ r := by omega
        let u := j.val + a
        have hu : u < n := by
          dsimp [u, n]
          omega
        have hlabel :=
          partitionIndexLabel_iterate_eq_of_centeredIndexObservation_eq
            T T_inv P d hcenter hu
        have hsymbol := partitionSymbol_eq_of_unique_of_indexLabel_eq P d
          (hx (Int.ofNat u)) (hy (Int.ofNat u)) hlabel
        simpa [hz, biIterate, u, Function.iterate_add_apply, Nat.add_comm] using hsymbol
    | negSucc a =>
        have hka : 2 * a + 1 = k.1 := by
          rw [hz] at hcode
          exact hcode
        let q := a + 1
        have hq : q ≤ m := by
          dsimp [q, m]
          omega
        by_cases hqj : q ≤ j.val
        · let u := j.val - q
          have hu : u < n := by
            dsimp [u, n]
            omega
          have hlabel :=
            partitionIndexLabel_iterate_eq_of_centeredIndexObservation_eq
              T T_inv P d hcenter hu
          have hsymbol := partitionSymbol_eq_of_unique_of_indexLabel_eq P d
            (hx (Int.ofNat u)) (hy (Int.ofNat u)) hlabel
          have hcancel (z : M) : T_inv^[q] (T^[j.val] z) = T^[u] z := by
            simpa [u] using
              (iterate_before_inverse_cancel
                (T := T_inv) (T_inv := T) hT_left hqj z)
          simpa [hz, biIterate, q, hcancel] using hsymbol
        · have hjq : j.val < q := lt_of_not_ge hqj
          let v := q - j.val
          have hv_pos : 0 < v := Nat.sub_pos_of_lt hjq
          have hv : v ≤ m := by
            dsimp [v]
            omega
          have hlabel :=
            partitionIndexLabel_inverseIterate_eq_of_centeredIndexObservation_eq
              T T_inv P d hcenter hv_pos hv
          have hvpred : v - 1 + 1 = v := Nat.sub_add_cancel hv_pos
          have hlabel' : partitionIndexLabel P d
              (biIterate T T_inv (Int.negSucc (v - 1)) x) =
              partitionIndexLabel P d
                (biIterate T T_inv (Int.negSucc (v - 1)) y) := by
            simpa [biIterate, hvpred] using hlabel
          have hsymbol := partitionSymbol_eq_of_unique_of_indexLabel_eq P d
            (hx (Int.negSucc (v - 1))) (hy (Int.negSucc (v - 1))) hlabel'
          have hcancel (z : M) : T_inv^[q] (T^[j.val] z) = T_inv^[v] z := by
            have hsum : v + j.val = q := Nat.sub_add_cancel hjq.le
            rw [← hsum, Function.iterate_add_apply, (hT_left.iterate j.val) z]
          simpa [hz, biIterate, q, hvpred, hcancel] using hsymbol
  calc
    observationEntropy mu X ≤ observationEntropy mu Z :=
      observationEntropy_le_of_ae_determined mu X Z hZ good hfull hdet
    _ = partitionEntropy mu (iteratedJoin T P (m + n)) :=
      observationEntropy_centeredIndexObservation
        mu T T_inv hT_right hT hT_inv P hP d m n
    _ = partitionEntropy mu (iteratedJoin T P (N + 2 * (r + 1))) := by
      have hlen : m + n = N + 2 * (r + 1) := by
        dsimp [m, n]
        omega
      rw [hlen]

lemma entropyW_le_entropyW_of_twoSided_generator_of_shrinking
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (P Q : Finset (Set EucPlane))
    (hP : IsMeasurablePartition mu P)
    (hQ : IsMeasurablePartition mu Q)
    {s : Set EucPlane} (hs : MeasurableSet s) (hfull : mu sᶜ = 0)
    {lam1 lam2 R : ℝ} (hR : 0 < R)
    (good : ℕ → Set EucPlane)
    (hs_good : ∀ x ∈ s, ∀ᶠ L : ℕ in atTop, x ∈ good L)
    (hs_atom : ∀ x ∈ s, ∀ L,
      ∃ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L), x ∈ A)
    (hpair : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
        dist x y ≤ Real.exp (-R * L)) :
    entropyW mu T Q ≤ entropyW mu T P := by
  classical
  have hPne := measurable_partition_nonempty mu hP
  let d : ↥P := ⟨hPne.choose, hPne.choose_spec⟩
  have hconditional := tendsto_twoSidedConditionalPartitionEntropy_zero_of_shrinking
    mu T T_inv hT_right hT.measurable hT_inv.measurable P hP.measurable
      Q hQ.measurable hs hfull hR good hs_good hs_atom hpair
  have hineq (r : ℕ) : entropyW mu T Q ≤
      entropyW mu T P + twoSidedConditionalPartitionEntropy mu T T_inv P Q r := by
    have hrate := entropyW_le_of_observationBlock_entropy_le
      mu T T_inv hT_right hT P Q hP hQ
      (twoSidedObservation T T_inv P r)
      (measurable_twoSidedObservation T T_inv hT.measurable hT_inv.measurable
        P hP.measurable r)
      (2 * (r + 1))
      (observationEntropy_observationBlock_twoSidedObservation_le
        mu T T_inv hT_left hT_right hT hT_inv P hP d r)
    rw [twoSidedConditionalPartitionEntropy_eq]
    exact hrate
  have hrhs : Tendsto
      (fun r => entropyW mu T P +
        twoSidedConditionalPartitionEntropy mu T T_inv P Q r)
      atTop (nhds (entropyW mu T P)) := by
    simpa using tendsto_const_nhds.add hconditional
  exact ge_of_tendsto' hrhs hineq

lemma kolmogorovSinaiEntropy_eq_entropyW_of_twoSided_generator_of_shrinking
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    {s : Set EucPlane} (hs : MeasurableSet s) (hfull : mu sᶜ = 0)
    {lam1 lam2 R : ℝ} (hR : 0 < R)
    (good : ℕ → Set EucPlane)
    (hs_good : ∀ x ∈ s, ∀ᶠ L : ℕ in atTop, x ∈ good L)
    (hs_atom : ∀ x ∈ s, ∀ L,
      ∃ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L), x ∈ A)
    (hpair : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
        dist x y ≤ Real.exp (-R * L)) :
    kolmogorovSinaiEntropy mu T = entropyW mu T P := by
  let S : Set ℝ := {h | ∃ Q : Finset (Set EucPlane),
    IsMeasurablePartition mu Q ∧ entropyW mu T Q = h}
  have hPmem : entropyW mu T P ∈ S := ⟨P, hP, rfl⟩
  have hbound : ∀ h ∈ S, h ≤ entropyW mu T P := by
    intro h hh
    obtain ⟨Q, hQ, rfl⟩ := hh
    exact entropyW_le_entropyW_of_twoSided_generator_of_shrinking
      mu T T_inv hT_left hT_right hT hT_inv P Q hP hQ hs hfull hR
        good hs_good hs_atom hpair
  have hSbdd : BddAbove S := ⟨entropyW mu T P, hbound⟩
  unfold kolmogorovSinaiEntropy
  change sSup S = entropyW mu T P
  apply le_antisymm
  · exact csSup_le ⟨entropyW mu T P, hPmem⟩ hbound
  · exact le_csSup hSbdd hPmem

end Submission.Helpers
