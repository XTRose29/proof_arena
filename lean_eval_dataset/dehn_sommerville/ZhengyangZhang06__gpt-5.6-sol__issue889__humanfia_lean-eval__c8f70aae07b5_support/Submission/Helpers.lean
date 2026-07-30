import ChallengeDeps

namespace Submission.Helpers

open LeanEval.Combinatorics.DehnSommerville

namespace DehnSommerville

noncomputable section

/-- Faces of a fixed cardinality, as a local finite set. -/
def facesOfCard {d : ℕ} (X : FiniteSimplicialSphere d) (n : ℕ) :
    Set (Finset (EuclideanSpace ℝ (Fin d))) :=
  {s | s ∈ X.K.faces ∧ s.card = n}

lemma mem_facesOfCard {d n : ℕ} {X : FiniteSimplicialSphere d}
    {s : Finset (EuclideanSpace ℝ (Fin d))} :
    s ∈ facesOfCard X n ↔ s ∈ X.K.faces ∧ s.card = n :=
  Iff.rfl

lemma finite_facesOfCard {d n : ℕ} (X : FiniteSimplicialSphere d) :
    (facesOfCard X n).Finite :=
  X.finite_faces.subset fun _ hs => hs.1

lemma faceCount_eq_ncard_facesOfCard {d : ℕ} (X : FiniteSimplicialSphere d) (k : ℕ) :
    faceCount X k = (facesOfCard X (k + 1)).ncard :=
  rfl

@[simp]
lemma extendedFaceCount_zero {d : ℕ} (X : FiniteSimplicialSphere d) :
    extendedFaceCount X 0 = 1 := by
  simp [extendedFaceCount]

@[simp]
lemma extendedFaceCount_succ {d : ℕ} (X : FiniteSimplicialSphere d) (i : ℕ) :
    extendedFaceCount X (i + 1) = faceCount X i := by
  simp [extendedFaceCount]

lemma extendedFaceCount_of_ne_zero {d i : ℕ} (X : FiniteSimplicialSphere d)
    (hi : i ≠ 0) :
    extendedFaceCount X i = faceCount X (i - 1) := by
  simp [extendedFaceCount, hi]

/-- Faces together with the empty face, matching the extended f-vector indexing. -/
def augmentedFaces {d : ℕ} (X : FiniteSimplicialSphere d) :
    Set (Finset (EuclideanSpace ℝ (Fin d))) :=
  insert ∅ X.K.faces

lemma mem_augmentedFaces {d : ℕ} {X : FiniteSimplicialSphere d}
    {s : Finset (EuclideanSpace ℝ (Fin d))} :
    s ∈ augmentedFaces X ↔ s = ∅ ∨ s ∈ X.K.faces := by
  rfl

lemma finite_augmentedFaces {d : ℕ} (X : FiniteSimplicialSphere d) :
    (augmentedFaces X).Finite := by
  exact X.finite_faces.insert ∅

/-- Augmented faces of a fixed cardinality. -/
def augmentedFacesOfCard {d : ℕ} (X : FiniteSimplicialSphere d) (n : ℕ) :
    Set (Finset (EuclideanSpace ℝ (Fin d))) :=
  {s | s ∈ augmentedFaces X ∧ s.card = n}

lemma finite_augmentedFacesOfCard {d n : ℕ} (X : FiniteSimplicialSphere d) :
    (augmentedFacesOfCard X n).Finite :=
  (finite_augmentedFaces X).subset fun _ hs => hs.1

lemma augmentedFacesOfCard_zero {d : ℕ} (X : FiniteSimplicialSphere d) :
    augmentedFacesOfCard X 0 = {∅} := by
  ext s
  constructor
  · intro hs
    exact Finset.card_eq_zero.mp hs.2
  · intro hs
    rw [Set.mem_singleton_iff] at hs
    subst s
    simp [augmentedFacesOfCard, augmentedFaces]

lemma augmentedFacesOfCard_succ {d n : ℕ} (X : FiniteSimplicialSphere d) :
    augmentedFacesOfCard X (n + 1) = facesOfCard X (n + 1) := by
  ext s
  constructor
  · intro hs
    rcases (mem_augmentedFaces.mp hs.1) with rfl | hs_face
    · exfalso
      exact Nat.succ_ne_zero n (by simpa using hs.2.symm)
    · exact ⟨hs_face, hs.2⟩
  · intro hs
    exact ⟨mem_augmentedFaces.mpr (Or.inr hs.1), hs.2⟩

lemma extendedFaceCount_eq_augmentedFacesOfCard {d i : ℕ}
    (X : FiniteSimplicialSphere d) :
    extendedFaceCount X i = (augmentedFacesOfCard X i).ncard := by
  cases i with
  | zero =>
      simp [augmentedFacesOfCard_zero]
  | succ i =>
      simp [extendedFaceCount_succ, faceCount_eq_ncard_facesOfCard,
        augmentedFacesOfCard_succ]

lemma hVector_eq_sum_augmentedFacesOfCard {d : ℕ} (X : FiniteSimplicialSphere d)
    (j : ℕ) :
    hVector X j =
      ∑ i ∈ Finset.range (j + 1),
        (-1 : ℤ) ^ (j - i) * (Nat.choose (d - i) (j - i) : ℤ) *
          ((augmentedFacesOfCard X i).ncard : ℤ) := by
  simp [hVector, extendedFaceCount_eq_augmentedFacesOfCard]

@[simp]
lemma hVector_zero {d : ℕ} (X : FiniteSimplicialSphere d) :
    hVector X 0 = 1 := by
  simp [hVector]

/-- The combinatorial link of a face, represented with the empty face included. -/
def linkFaces {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Set (Finset (EuclideanSpace ℝ (Fin d))) :=
  {τ | τ ∈ augmentedFaces X ∧ Disjoint σ τ ∧ σ ∪ τ ∈ augmentedFaces X}

lemma mem_linkFaces {d : ℕ} {X : FiniteSimplicialSphere d}
    {σ τ : Finset (EuclideanSpace ℝ (Fin d))} :
    τ ∈ linkFaces X σ ↔
      τ ∈ augmentedFaces X ∧ Disjoint σ τ ∧ σ ∪ τ ∈ augmentedFaces X :=
  Iff.rfl

lemma finite_linkFaces {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    (linkFaces X σ).Finite :=
  (finite_augmentedFaces X).subset fun _ hτ => hτ.1

/-- Alternating Euler sum of the augmented link. -/
def linkEulerSum {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) : ℤ :=
  ∑ τ ∈ (finite_linkFaces X σ).toFinset, (-1 : ℤ) ^ τ.card

/-- The Euler-link relation needed to turn the local f-vector algebra into Dehn-Sommerville. -/
def HasEulerianLinks {d : ℕ} (X : FiniteSimplicialSphere d) : Prop :=
  ∀ σ ∈ augmentedFaces X, linkEulerSum X σ = (-1 : ℤ) ^ (d - σ.card)

lemma face_card_le_dim_succ {d : ℕ} (X : FiniteSimplicialSphere d)
    {s : Finset (EuclideanSpace ℝ (Fin d))} (hs : s ∈ X.K.faces) :
    s.card ≤ d + 1 := by
  classical
  have h_ind : AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin d)) :=
    X.K.indep hs
  have h_le : Fintype.card s ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) + 1 :=
    h_ind.card_le_finrank_succ.trans <|
      Nat.add_le_add_right (Submodule.finrank_le
        (vectorSpan ℝ (Set.range ((↑) : s → EuclideanSpace ℝ (Fin d))))) 1
  simpa [finrank_euclideanSpace, Fintype.card_fin] using h_le

/-! ### The finite polynomial reduction -/

open Polynomial

/-- The h-polynomial written in the face-number basis. -/
def hPolynomial {d : ℕ} (X : FiniteSimplicialSphere d) : ℤ[X] :=
  ∑ i ∈ Finset.range (d + 1),
    C (extendedFaceCount X i : ℤ) *
      (Polynomial.X ^ i * (1 - Polynomial.X) ^ (d - i))

/-- The polynomial obtained by reciprocating each h-polynomial summand. -/
def reciprocalPolynomial {d : ℕ} (X : FiniteSimplicialSphere d) : ℤ[X] :=
  ∑ i ∈ Finset.range (d + 1),
    C (extendedFaceCount X i : ℤ) * (Polynomial.X - 1) ^ (d - i)

/-- Generalized Euler relations in the sign convention used by `hPolynomial`. -/
def HasEulerRelations {d : ℕ} (X : FiniteSimplicialSphere d) : Prop :=
  ∀ k, k ≤ d →
    ∑ i ∈ Finset.Icc k d,
      (-1 : ℤ) ^ (d - i) * (Nat.choose i k : ℤ) * (extendedFaceCount X i : ℤ) =
        (extendedFaceCount X k : ℤ)

lemma coeff_one_sub_X_pow_int (n k : ℕ) :
    coeff ((1 - Polynomial.X : ℤ[X]) ^ n) k =
      (-1 : ℤ) ^ k * (Nat.choose n k : ℤ) := by
  have hbase : (1 - Polynomial.X : ℤ[X]) = -(Polynomial.X - 1) := by ring
  have hpoly : (1 - Polynomial.X : ℤ[X]) ^ n =
      C (-1) ^ n * (Polynomial.X - 1) ^ n := by
    rw [hbase, neg_eq_neg_one_mul, mul_pow]
    simp
  rw [hpoly, ← map_pow, coeff_C_mul]
  rw [show (Polynomial.X - 1 : ℤ[X]) = Polynomial.X + C (-1) by
    norm_num [sub_eq_add_neg]]
  rw [coeff_X_add_C_pow]
  rw [← mul_assoc, ← pow_add]
  by_cases hk : k ≤ n
  · have hmod : (n + (n - k)) % 2 = k % 2 := by omega
    rw [neg_one_pow_eq_pow_mod_two, hmod, ← neg_one_pow_eq_pow_mod_two]
  · rw [Nat.choose_eq_zero_of_lt (not_le.mp hk)]
    simp

lemma coeff_hTerm (d i j : ℕ) (hi : i ≤ j) (_hj : j ≤ d) :
    coeff ((Polynomial.X : ℤ[X]) ^ i * (1 - Polynomial.X) ^ (d - i)) j =
      (-1 : ℤ) ^ (j - i) * (Nat.choose (d - i) (j - i) : ℤ) := by
  rw [coeff_X_pow_mul']
  simp only [hi, ↓reduceIte]
  rw [coeff_one_sub_X_pow_int]

lemma coeff_X_sub_one_pow_int (n k : ℕ) :
    coeff (((Polynomial.X : ℤ[X]) - 1) ^ n) k =
      (-1 : ℤ) ^ (n - k) * (Nat.choose n k : ℤ) := by
  rw [show (Polynomial.X - 1 : ℤ[X]) = Polynomial.X + C (-1) by
    norm_num [sub_eq_add_neg]]
  rw [coeff_X_add_C_pow]

lemma coeff_taylor_hTerm (d i k : ℕ) (hki : k ≤ i) (hid : i ≤ d) :
    coeff (((Polynomial.X + 1 : ℤ[X]) ^ i) * (-Polynomial.X) ^ (d - i)) (d - k) =
      (-1 : ℤ) ^ (d - i) * (Nat.choose i k : ℤ) := by
  have hpow : (-Polynomial.X : ℤ[X]) ^ (d - i) =
      C ((-1 : ℤ) ^ (d - i)) * Polynomial.X ^ (d - i) := by
    rw [neg_pow]
    congr 1
    simp
  rw [hpow]
  rw [show (Polynomial.X + 1 : ℤ[X]) ^ i *
      (C ((-1 : ℤ) ^ (d - i)) * Polynomial.X ^ (d - i)) =
      C ((-1 : ℤ) ^ (d - i)) *
        ((Polynomial.X + 1) ^ i * Polynomial.X ^ (d - i)) by ring]
  rw [coeff_C_mul, coeff_mul_X_pow']
  have hle : d - i ≤ d - k := Nat.sub_le_sub_left hki d
  simp only [hle, ↓reduceIte]
  have hsub : d - k - (d - i) = i - k := by omega
  rw [hsub, coeff_X_add_one_pow]
  rw [Nat.choose_symm hki]

lemma coeff_taylor_hTerm_eq_zero (d i k : ℕ) (hik : i < k) (hkd : k ≤ d) :
    coeff (((Polynomial.X + 1 : ℤ[X]) ^ i) * (-Polynomial.X) ^ (d - i)) (d - k) =
      0 := by
  have hpow : (-Polynomial.X : ℤ[X]) ^ (d - i) =
      C ((-1 : ℤ) ^ (d - i)) * Polynomial.X ^ (d - i) := by
    rw [neg_pow]
    congr 1
    simp
  rw [hpow]
  rw [show (Polynomial.X + 1 : ℤ[X]) ^ i *
      (C ((-1 : ℤ) ^ (d - i)) * Polynomial.X ^ (d - i)) =
      C ((-1 : ℤ) ^ (d - i)) *
        ((Polynomial.X + 1) ^ i * Polynomial.X ^ (d - i)) by ring]
  rw [coeff_C_mul, coeff_mul_X_pow']
  have hlt : d - k < d - i := by omega
  simp [not_le_of_gt hlt]

lemma coeff_hPolynomial {d : ℕ} (X : FiniteSimplicialSphere d)
    (j : ℕ) (hj : j ≤ d) :
    coeff (hPolynomial X) j = hVector X j := by
  classical
  rw [hPolynomial]
  simp only [finsetSum_coeff, coeff_C_mul]
  calc
    ∑ i ∈ Finset.range (d + 1),
        (extendedFaceCount X i : ℤ) *
          coeff (Polynomial.X ^ i * (1 - Polynomial.X) ^ (d - i)) j =
        ∑ i ∈ Finset.range (j + 1),
          (extendedFaceCount X i : ℤ) *
            coeff (Polynomial.X ^ i * (1 - Polynomial.X) ^ (d - i)) j := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hj))
      intro i _ hi
      have hji : j < i := by
        have : ¬i < j + 1 := by simpa only [Finset.mem_range] using hi
        omega
      rw [coeff_X_pow_mul']
      simp [not_le_of_gt hji]
    _ = hVector X j := by
      rw [hVector]
      apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [coeff_hTerm d i j hij hj]
      ring

lemma coeff_reciprocalPolynomial {d : ℕ} (X : FiniteSimplicialSphere d)
    (j : ℕ) (hj : j ≤ d) :
    coeff (reciprocalPolynomial X) j = hVector X (d - j) := by
  classical
  rw [reciprocalPolynomial]
  simp only [finsetSum_coeff, coeff_C_mul]
  calc
    ∑ i ∈ Finset.range (d + 1),
        (extendedFaceCount X i : ℤ) * coeff ((Polynomial.X - 1) ^ (d - i)) j =
        ∑ i ∈ Finset.range (d - j + 1),
          (extendedFaceCount X i : ℤ) * coeff ((Polynomial.X - 1) ^ (d - i)) j := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.sub_le d j)))
      intro i hid hi
      have hdi : d - j < i := by
        have : ¬i < d - j + 1 := by simpa only [Finset.mem_range] using hi
        omega
      rw [coeff_X_sub_one_pow_int]
      rw [Nat.choose_eq_zero_of_lt]
      · simp
      · have hd : d - j + j = d := Nat.sub_add_cancel hj
        have hiD : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hid)
        omega
    _ = hVector X (d - j) := by
      rw [hVector]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ d - j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [coeff_X_sub_one_pow_int]
      have hj' : j ≤ d - i := by omega
      have hsub : d - i - j = d - j - i := by omega
      have hchoose : Nat.choose (d - i) j = Nat.choose (d - i) (d - j - i) := by
        rw [← hsub]
        exact (Nat.choose_symm hj').symm
      rw [hsub, hchoose]
      ring

lemma taylor_reciprocalPolynomial {d : ℕ} (X : FiniteSimplicialSphere d) :
    Polynomial.taylor 1 (reciprocalPolynomial X) =
      ∑ i ∈ Finset.range (d + 1),
        C (extendedFaceCount X i : ℤ) * Polynomial.X ^ (d - i) := by
  simp [reciprocalPolynomial, Polynomial.taylor_apply]

lemma taylor_hPolynomial {d : ℕ} (X : FiniteSimplicialSphere d) :
    Polynomial.taylor 1 (hPolynomial X) =
      ∑ i ∈ Finset.range (d + 1),
        C (extendedFaceCount X i : ℤ) *
          ((Polynomial.X + 1) ^ i * (-Polynomial.X) ^ (d - i)) := by
  simp only [hPolynomial, Polynomial.taylor_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma coeff_taylor_hPolynomial {d : ℕ} (X : FiniteSimplicialSphere d)
    (hX : HasEulerRelations X) (k : ℕ) (hkd : k ≤ d) :
    coeff (Polynomial.taylor 1 (hPolynomial X)) (d - k) =
      (extendedFaceCount X k : ℤ) := by
  rw [taylor_hPolynomial]
  simp only [finsetSum_coeff, coeff_C_mul]
  calc
    ∑ i ∈ Finset.range (d + 1),
        (extendedFaceCount X i : ℤ) *
          coeff ((Polynomial.X + 1) ^ i * (-Polynomial.X) ^ (d - i)) (d - k) =
        ∑ i ∈ Finset.Icc k d,
          (extendedFaceCount X i : ℤ) *
            coeff ((Polynomial.X + 1) ^ i * (-Polynomial.X) ^ (d - i)) (d - k) := by
      symm
      apply Finset.sum_subset
      · intro i hi
        simp only [Finset.mem_Icc] at hi
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hi.2)
      · intro i hi hiIcc
        have hid : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hik : i < k := by
          simp only [Finset.mem_Icc, not_and_or, not_le] at hiIcc
          rcases hiIcc with hiIcc | hiIcc
          · exact hiIcc
          · exact (not_lt_of_ge hid hiIcc).elim
        rw [coeff_taylor_hTerm_eq_zero d i k hik hkd]
        simp
    _ = extendedFaceCount X k := by
      rw [← hX k hkd]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      rw [coeff_taylor_hTerm d i k hi'.1 hi'.2]
      ring

lemma coeff_taylor_reciprocalPolynomial {d : ℕ} (X : FiniteSimplicialSphere d)
    (k : ℕ) (hkd : k ≤ d) :
    coeff (Polynomial.taylor 1 (reciprocalPolynomial X)) (d - k) =
      (extendedFaceCount X k : ℤ) := by
  rw [taylor_reciprocalPolynomial]
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  calc
    ∑ i ∈ Finset.range (d + 1),
        (extendedFaceCount X i : ℤ) * (if d - k = d - i then 1 else 0) =
        (extendedFaceCount X k : ℤ) * (if d - k = d - k then 1 else 0) := by
      apply Finset.sum_eq_single k
      · intro i hi hik
        have hid : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hne : d - k ≠ d - i := by
          intro h
          apply hik
          omega
        simp [hne]
      · intro hk
        exact (hk (Finset.mem_range.mpr (Nat.lt_succ_of_le hkd))).elim
    _ = extendedFaceCount X k := by simp

lemma natDegree_taylor_reciprocalPolynomial_le {d : ℕ}
    (X : FiniteSimplicialSphere d) :
    (Polynomial.taylor 1 (reciprocalPolynomial X)).natDegree ≤ d := by
  rw [taylor_reciprocalPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have hid : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  compute_degree
  omega

lemma natDegree_taylor_hPolynomial_le {d : ℕ} (X : FiniteSimplicialSphere d) :
    (Polynomial.taylor 1 (hPolynomial X)).natDegree ≤ d := by
  rw [taylor_hPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have hid : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  compute_degree
  omega

lemma hPolynomial_eq_reciprocalPolynomial_of_eulerRelations {d : ℕ}
    (X : FiniteSimplicialSphere d) (hX : HasEulerRelations X) :
    hPolynomial X = reciprocalPolynomial X := by
  apply Polynomial.taylor_injective 1
  apply (Polynomial.ext_iff_natDegree_le
    (natDegree_taylor_hPolynomial_le X)
    (natDegree_taylor_reciprocalPolynomial_le X)).2
  intro i hid
  have hk : d - i ≤ d := Nat.sub_le d i
  have hindex : d - (d - i) = i := Nat.sub_sub_self hid
  calc
    coeff (Polynomial.taylor 1 (hPolynomial X)) i =
        coeff (Polynomial.taylor 1 (hPolynomial X)) (d - (d - i)) := by rw [hindex]
    _ = (extendedFaceCount X (d - i) : ℤ) :=
      coeff_taylor_hPolynomial X hX (d - i) hk
    _ = coeff (Polynomial.taylor 1 (reciprocalPolynomial X)) (d - (d - i)) :=
      (coeff_taylor_reciprocalPolynomial X (d - i) hk).symm
    _ = coeff (Polynomial.taylor 1 (reciprocalPolynomial X)) i := by rw [hindex]

lemma dehn_sommerville_of_eulerRelations {d j : ℕ}
    (X : FiniteSimplicialSphere d) (hX : HasEulerRelations X) (hj : j ≤ d) :
    hVector X j = hVector X (d - j) := by
  calc
    hVector X j = coeff (hPolynomial X) j := (by
      symm
      exact coeff_hPolynomial X j hj)
    _ = coeff (reciprocalPolynomial X) j := by
      rw [hPolynomial_eq_reciprocalPolynomial_of_eulerRelations X hX]
    _ = hVector X (d - j) := coeff_reciprocalPolynomial X j hj

/-! ### From local link sums to the generalized Euler relations -/

def augmentedFaceFinset {d : ℕ} (X : FiniteSimplicialSphere d) :
    Finset (Finset (EuclideanSpace ℝ (Fin d))) :=
  (finite_augmentedFaces X).toFinset

@[simp]
lemma mem_augmentedFaceFinset {d : ℕ} {X : FiniteSimplicialSphere d}
    {s : Finset (EuclideanSpace ℝ (Fin d))} :
    s ∈ augmentedFaceFinset X ↔ s ∈ augmentedFaces X := by
  simp [augmentedFaceFinset]

lemma augmentedFaces_down_closed {d : ℕ} (X : FiniteSimplicialSphere d)
    {s t : Finset (EuclideanSpace ℝ (Fin d))}
    (hs : s ∈ augmentedFaces X) (hts : t ⊆ s) : t ∈ augmentedFaces X := by
  rcases mem_augmentedFaces.mp hs with rfl | hs
  · have : t = ∅ := Finset.subset_empty.mp hts
    subst t
    simp [augmentedFaces]
  · by_cases ht : t = ∅
    · subst t
      simp [augmentedFaces]
    · exact mem_augmentedFaces.mpr <| Or.inr <|
        X.K.down_closed hs hts (Finset.nonempty_iff_ne_empty.mpr ht)

def cofaces {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Finset (Finset (EuclideanSpace ℝ (Fin d))) :=
  (augmentedFaceFinset X).filter fun G => σ ⊆ G

@[simp]
lemma mem_cofaces {d : ℕ} {X : FiniteSimplicialSphere d}
    {σ G : Finset (EuclideanSpace ℝ (Fin d))} :
    G ∈ cofaces X σ ↔ G ∈ augmentedFaces X ∧ σ ⊆ G := by
  simp [cofaces]

def HasCofaceEulerRelations {d : ℕ} (X : FiniteSimplicialSphere d) : Prop :=
  ∀ σ ∈ augmentedFaces X,
    ∑ G ∈ cofaces X σ, (-1 : ℤ) ^ (d - G.card) = 1

def linkFaceFinset {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Finset (Finset (EuclideanSpace ℝ (Fin d))) :=
  (finite_linkFaces X σ).toFinset

@[simp]
lemma mem_linkFaceFinset {d : ℕ} {X : FiniteSimplicialSphere d}
    {σ τ : Finset (EuclideanSpace ℝ (Fin d))} :
    τ ∈ linkFaceFinset X σ ↔ τ ∈ linkFaces X σ := by
  simp [linkFaceFinset]

lemma linkEulerSum_eq_sum_cofaces_card_sub {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    linkEulerSum X σ =
      ∑ G ∈ cofaces X σ, (-1 : ℤ) ^ (G.card - σ.card) := by
  rw [linkEulerSum]
  change (∑ τ ∈ linkFaceFinset X σ, (-1 : ℤ) ^ τ.card) = _
  apply Finset.sum_bij (fun τ _ => σ ∪ τ)
  · intro τ hτ
    have hτ' := mem_linkFaceFinset.mp hτ
    exact mem_cofaces.mpr ⟨hτ'.2.2, Finset.subset_union_left⟩
  · intro τ hτ υ hυ hEq
    have hτ' := mem_linkFaceFinset.mp hτ
    have hυ' := mem_linkFaceFinset.mp hυ
    calc
      τ = (σ ∪ τ) \ σ := (Finset.union_sdiff_cancel_left hτ'.2.1).symm
      _ = (σ ∪ υ) \ σ := by rw [hEq]
      _ = υ := Finset.union_sdiff_cancel_left hυ'.2.1
  · intro G hG
    have hG' := mem_cofaces.mp hG
    refine ⟨G \ σ, ?_, ?_⟩
    · apply mem_linkFaceFinset.mpr
      refine ⟨augmentedFaces_down_closed X hG'.1 Finset.sdiff_subset,
        Finset.disjoint_sdiff, ?_⟩
      simpa [Finset.union_sdiff_of_subset hG'.2] using hG'.1
    · exact Finset.union_sdiff_of_subset hG'.2
  · intro τ hτ
    have hτ' := mem_linkFaceFinset.mp hτ
    rw [Finset.card_union_of_disjoint hτ'.2.1]
    simp

/-- A parity-stable form of the local Euler relation. Unlike natural-number
subtraction, this sign also detects a hypothetical face of cardinality `d + 1`. -/
def HasSignedEulerianLinks {d : ℕ} (X : FiniteSimplicialSphere d) : Prop :=
  ∀ σ ∈ augmentedFaces X,
    linkEulerSum X σ = (-1 : ℤ) ^ d * (-1 : ℤ) ^ σ.card

/-! ### A global Euler and punctured-deletion reduction -/

/-- Alternating cardinality sum over all faces, including the empty face. -/
def augmentedEulerSum {d : ℕ} (X : FiniteSimplicialSphere d) : ℤ :=
  ∑ G ∈ augmentedFaceFinset X, (-1 : ℤ) ^ G.card

/-- Augmented faces which do not contain `σ`. Geometrically, for nonempty `σ`,
this is the subcomplex left after deleting the relative interior point used to
puncture `σ`. -/
def deletionFaceFinset {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Finset (Finset (EuclideanSpace ℝ (Fin d))) :=
  (augmentedFaceFinset X).filter fun G => ¬σ ⊆ G

@[simp]
lemma mem_deletionFaceFinset {d : ℕ} {X : FiniteSimplicialSphere d}
    {σ G : Finset (EuclideanSpace ℝ (Fin d))} :
    G ∈ deletionFaceFinset X σ ↔ G ∈ augmentedFaces X ∧ ¬σ ⊆ G := by
  simp [deletionFaceFinset]

/-- Alternating cardinality sum of the augmented deletion. -/
def deletionEulerSum {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) : ℤ :=
  ∑ G ∈ deletionFaceFinset X σ, (-1 : ℤ) ^ G.card

lemma linkFaceFinset_empty {d : ℕ} (X : FiniteSimplicialSphere d) :
    linkFaceFinset X (∅ : Finset (EuclideanSpace ℝ (Fin d))) =
      augmentedFaceFinset X := by
  ext G
  simp [linkFaces, augmentedFaces]

lemma linkEulerSum_empty {d : ℕ} (X : FiniteSimplicialSphere d) :
    linkEulerSum X (∅ : Finset (EuclideanSpace ℝ (Fin d))) = augmentedEulerSum X := by
  rw [linkEulerSum]
  change (∑ G ∈ linkFaceFinset X ∅, (-1 : ℤ) ^ G.card) = _
  rw [linkFaceFinset_empty]
  rfl

lemma augmentedEulerSum_eq_deletionEulerSum_add_cofaces {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    augmentedEulerSum X = deletionEulerSum X σ +
      ∑ G ∈ cofaces X σ, (-1 : ℤ) ^ G.card := by
  classical
  rw [augmentedEulerSum, deletionEulerSum, deletionFaceFinset, cofaces]
  simpa [add_comm] using
    (Finset.sum_filter_add_sum_filter_not (augmentedFaceFinset X)
      (fun G => σ ⊆ G) (fun G => (-1 : ℤ) ^ G.card)).symm

lemma sum_cofaces_neg_one_pow_card {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    (∑ G ∈ cofaces X σ, (-1 : ℤ) ^ G.card) =
      (-1 : ℤ) ^ σ.card * linkEulerSum X σ := by
  rw [linkEulerSum_eq_sum_cofaces_card_sub]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  have hsub := (mem_cofaces.mp hG).2
  rw [← pow_add, Nat.add_sub_of_le (Finset.card_le_card hsub)]

/-- The two Euler inputs obtained from a sphere and its point complements:
the global augmented sum has the sphere sign, while every nonempty face
deletion has vanishing augmented sum. -/
def HasSphereDeletionEuler {d : ℕ} (X : FiniteSimplicialSphere d) : Prop :=
  augmentedEulerSum X = (-1 : ℤ) ^ d ∧
    ∀ σ ∈ augmentedFaces X, σ.Nonempty → deletionEulerSum X σ = 0

lemma neg_one_pow_mul_self (n : ℕ) :
    (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

lemma hasSignedEulerianLinks_of_hasSphereDeletionEuler {d : ℕ}
    (X : FiniteSimplicialSphere d) (hX : HasSphereDeletionEuler X) :
    HasSignedEulerianLinks X := by
  intro σ hσ
  by_cases hσempty : σ = ∅
  · subst σ
    simp [linkEulerSum_empty, hX.1]
  · have hσne : σ.Nonempty := Finset.nonempty_iff_ne_empty.mpr hσempty
    have hsplit := augmentedEulerSum_eq_deletionEulerSum_add_cofaces X σ
    rw [hX.1, hX.2 σ hσ hσne, zero_add, sum_cofaces_neg_one_pow_card] at hsplit
    calc
      linkEulerSum X σ =
          ((-1 : ℤ) ^ σ.card * (-1 : ℤ) ^ σ.card) * linkEulerSum X σ := by
        rw [neg_one_pow_mul_self, one_mul]
      _ = (-1 : ℤ) ^ σ.card *
          ((-1 : ℤ) ^ σ.card * linkEulerSum X σ) := by ring
      _ = (-1 : ℤ) ^ σ.card * (-1 : ℤ) ^ d := by rw [hsplit]
      _ = (-1 : ℤ) ^ d * (-1 : ℤ) ^ σ.card := by ring

lemma linkFaceFinset_eq_singleton_empty_of_card_eq_dim_succ {d : ℕ}
    (X : FiniteSimplicialSphere d)
    {G : Finset (EuclideanSpace ℝ (Fin d))}
    (hG : G ∈ augmentedFaces X) (hcard : G.card = d + 1) :
    linkFaceFinset X G = {∅} := by
  ext τ
  constructor
  · intro hτ
    have hτ' := mem_linkFaceFinset.mp hτ
    have hGne : G ≠ ∅ := by
      intro h
      subst G
      simp at hcard
    have hUnionNe : G ∪ τ ≠ ∅ := by
      intro h
      exact hGne (Finset.union_eq_empty.mp h).1
    have hUnionFace : G ∪ τ ∈ X.K.faces := by
      rcases mem_augmentedFaces.mp hτ'.2.2 with h | h
      · exact (hUnionNe h).elim
      · exact h
    have hle := face_card_le_dim_succ X hUnionFace
    have hUnionCard := Finset.card_union_of_disjoint hτ'.2.1
    have hτCard : τ.card = 0 := by omega
    simp [Finset.card_eq_zero.mp hτCard]
  · intro hτ
    rw [Finset.mem_singleton] at hτ
    subst τ
    apply mem_linkFaceFinset.mpr
    exact ⟨by simp [augmentedFaces], by simp, by simpa using hG⟩

lemma linkEulerSum_eq_one_of_card_eq_dim_succ {d : ℕ}
    (X : FiniteSimplicialSphere d)
    {G : Finset (EuclideanSpace ℝ (Fin d))}
    (hG : G ∈ augmentedFaces X) (hcard : G.card = d + 1) :
    linkEulerSum X G = 1 := by
  rw [linkEulerSum]
  change (∑ τ ∈ linkFaceFinset X G, (-1 : ℤ) ^ τ.card) = 1
  rw [linkFaceFinset_eq_singleton_empty_of_card_eq_dim_succ X hG hcard]
  simp

lemma neg_one_pow_mul_succ_self (d : ℕ) :
    (-1 : ℤ) ^ d * (-1 : ℤ) ^ (d + 1) = -1 := by
  rw [pow_succ]
  calc
    (-1 : ℤ) ^ d * ((-1 : ℤ) ^ d * -1) =
        ((-1 : ℤ) ^ d * (-1 : ℤ) ^ d) * -1 := by ring
    _ = -1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      norm_num

lemma card_le_dim_of_hasSignedEulerianLinks {d : ℕ}
    (X : FiniteSimplicialSphere d) (hX : HasSignedEulerianLinks X)
    {G : Finset (EuclideanSpace ℝ (Fin d))} (hG : G ∈ augmentedFaces X) :
    G.card ≤ d := by
  by_cases hEmpty : G = ∅
  · simp [hEmpty]
  have hFace : G ∈ X.K.faces :=
    (mem_augmentedFaces.mp hG).resolve_left hEmpty
  have hle := face_card_le_dim_succ X hFace
  by_contra hnot
  have hcard : G.card = d + 1 := by omega
  have hsigned := hX G hG
  rw [linkEulerSum_eq_one_of_card_eq_dim_succ X hG hcard, hcard,
    neg_one_pow_mul_succ_self] at hsigned
  norm_num at hsigned

lemma neg_one_pow_sub_eq_product {d s : ℕ} (hsd : s ≤ d) :
    (-1 : ℤ) ^ (d - s) = (-1 : ℤ) ^ d * (-1 : ℤ) ^ s := by
  symm
  calc
    (-1 : ℤ) ^ d * (-1 : ℤ) ^ s =
        ((-1 : ℤ) ^ (d - s) * (-1 : ℤ) ^ s) * (-1 : ℤ) ^ s := by
      rw [show (-1 : ℤ) ^ d =
        (-1 : ℤ) ^ (d - s) * (-1 : ℤ) ^ s by
          rw [← pow_add, Nat.sub_add_cancel hsd]]
    _ = (-1 : ℤ) ^ (d - s) *
        ((-1 : ℤ) ^ s * (-1 : ℤ) ^ s) := by ring
    _ = (-1 : ℤ) ^ (d - s) := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]

lemma hasEulerianLinks_of_hasSignedEulerianLinks {d : ℕ}
    (X : FiniteSimplicialSphere d) (hX : HasSignedEulerianLinks X) :
    HasEulerianLinks X := by
  intro σ hσ
  calc
    linkEulerSum X σ = (-1 : ℤ) ^ d * (-1 : ℤ) ^ σ.card := hX σ hσ
    _ = (-1 : ℤ) ^ (d - σ.card) :=
      (neg_one_pow_sub_eq_product
        (card_le_dim_of_hasSignedEulerianLinks X hX hσ)).symm

lemma neg_one_pow_coface_sign {d s g : ℕ} (hsg : s ≤ g) (hgd : g ≤ d) :
    (-1 : ℤ) ^ (d - s) * (-1 : ℤ) ^ (g - s) = (-1 : ℤ) ^ (d - g) := by
  have hsub : d - s = d - g + (g - s) := by omega
  rw [hsub, pow_add]
  calc
    (-1 : ℤ) ^ (d - g) * (-1 : ℤ) ^ (g - s) * (-1 : ℤ) ^ (g - s) =
        (-1 : ℤ) ^ (d - g) *
          ((-1 : ℤ) ^ (g - s) * (-1 : ℤ) ^ (g - s)) := by ring
    _ = (-1 : ℤ) ^ (d - g) := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]

lemma hasCofaceEulerRelations_of_hasEulerianLinks {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (hcard : ∀ G ∈ augmentedFaces X, G.card ≤ d)
    (hX : HasEulerianLinks X) : HasCofaceEulerRelations X := by
  intro σ hσ
  have hσd := hcard σ hσ
  have hlink := hX σ hσ
  rw [linkEulerSum_eq_sum_cofaces_card_sub] at hlink
  calc
    ∑ G ∈ cofaces X σ, (-1 : ℤ) ^ (d - G.card) =
        (-1 : ℤ) ^ (d - σ.card) *
          ∑ G ∈ cofaces X σ, (-1 : ℤ) ^ (G.card - σ.card) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro G hG
      have hG' := mem_cofaces.mp hG
      exact (neg_one_pow_coface_sign (Finset.card_le_card hG'.2) (hcard G hG'.1)).symm
    _ = (-1 : ℤ) ^ (d - σ.card) * (-1 : ℤ) ^ (d - σ.card) := by rw [hlink]
    _ = 1 := by
      rw [← pow_add, ← two_mul]
      rw [pow_mul, neg_one_sq, one_pow]

def augmentedFacesOfCardFinset {d : ℕ} (X : FiniteSimplicialSphere d) (k : ℕ) :
    Finset (Finset (EuclideanSpace ℝ (Fin d))) :=
  (finite_augmentedFacesOfCard (n := k) X).toFinset

@[simp]
lemma mem_augmentedFacesOfCardFinset {d k : ℕ} {X : FiniteSimplicialSphere d}
    {σ : Finset (EuclideanSpace ℝ (Fin d))} :
    σ ∈ augmentedFacesOfCardFinset X k ↔ σ ∈ augmentedFaces X ∧ σ.card = k := by
  simp [augmentedFacesOfCardFinset, augmentedFacesOfCard]

lemma card_augmentedFacesOfCardFinset {d k : ℕ} (X : FiniteSimplicialSphere d) :
    (augmentedFacesOfCardFinset X k).card = extendedFaceCount X k := by
  rw [extendedFaceCount_eq_augmentedFacesOfCard]
  exact (Set.ncard_eq_toFinset_card _ (finite_augmentedFacesOfCard (n := k) X)).symm

lemma fixedCard_filter_subset_eq_powersetCard {d k : ℕ}
    (X : FiniteSimplicialSphere d)
    {G : Finset (EuclideanSpace ℝ (Fin d))} (hG : G ∈ augmentedFaces X) :
    (augmentedFacesOfCardFinset X k).filter (fun σ => σ ⊆ G) = G.powersetCard k := by
  ext σ
  simp only [Finset.mem_filter, mem_augmentedFacesOfCardFinset,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hcard⟩, hsub⟩
    exact ⟨hsub, hcard⟩
  · rintro ⟨hsub, hcard⟩
    exact ⟨⟨augmentedFaces_down_closed X hG hsub, hcard⟩, hsub⟩

lemma sum_cofaces_over_fixedCard {d k : ℕ} (X : FiniteSimplicialSphere d) :
    (∑ σ ∈ augmentedFacesOfCardFinset X k,
      ∑ G ∈ cofaces X σ, (-1 : ℤ) ^ (d - G.card)) =
      ∑ G ∈ augmentedFaceFinset X,
        (-1 : ℤ) ^ (d - G.card) * (Nat.choose G.card k : ℤ) := by
  classical
  calc
    (∑ σ ∈ augmentedFacesOfCardFinset X k,
      ∑ G ∈ cofaces X σ, (-1 : ℤ) ^ (d - G.card)) =
        ∑ σ ∈ augmentedFacesOfCardFinset X k,
          ∑ G ∈ augmentedFaceFinset X,
            if σ ⊆ G then (-1 : ℤ) ^ (d - G.card) else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [cofaces, Finset.sum_filter]
    _ = ∑ G ∈ augmentedFaceFinset X,
          ∑ σ ∈ augmentedFacesOfCardFinset X k,
            if σ ⊆ G then (-1 : ℤ) ^ (d - G.card) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ G ∈ augmentedFaceFinset X,
        (-1 : ℤ) ^ (d - G.card) * (Nat.choose G.card k : ℤ) := by
      apply Finset.sum_congr rfl
      intro G hG
      rw [← Finset.sum_filter]
      rw [fixedCard_filter_subset_eq_powersetCard X (mem_augmentedFaceFinset.mp hG)]
      simp [Finset.card_powersetCard]
      ring

lemma augmentedFaceFinset_filter_card {d i : ℕ} (X : FiniteSimplicialSphere d) :
    (augmentedFaceFinset X).filter (fun G => G.card = i) =
      augmentedFacesOfCardFinset X i := by
  ext G
  simp [and_comm]

lemma sum_augmentedFaces_grouped_by_card {d k : ℕ}
    (X : FiniteSimplicialSphere d)
    (hcard : ∀ G ∈ augmentedFaces X, G.card ≤ d) :
    (∑ G ∈ augmentedFaceFinset X,
      (-1 : ℤ) ^ (d - G.card) * (Nat.choose G.card k : ℤ)) =
      ∑ i ∈ Finset.Icc k d,
        (-1 : ℤ) ^ (d - i) * (Nat.choose i k : ℤ) *
          (extendedFaceCount X i : ℤ) := by
  classical
  calc
    (∑ G ∈ augmentedFaceFinset X,
      (-1 : ℤ) ^ (d - G.card) * (Nat.choose G.card k : ℤ)) =
        ∑ i ∈ Finset.range (d + 1),
          ∑ G ∈ augmentedFaceFinset X with G.card = i,
            (-1 : ℤ) ^ (d - G.card) * (Nat.choose G.card k : ℤ) := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro G hG
      exact Finset.mem_range.mpr <| Nat.lt_succ_of_le <|
        hcard G (mem_augmentedFaceFinset.mp hG)
    _ = ∑ i ∈ Finset.range (d + 1),
        (-1 : ℤ) ^ (d - i) * (Nat.choose i k : ℤ) *
          (extendedFaceCount X i : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (augmentedFaceFinset X).filter (fun G => G.card = i) =
        augmentedFacesOfCardFinset X i by exact augmentedFaceFinset_filter_card X]
      calc
        (∑ G ∈ augmentedFacesOfCardFinset X i,
          (-1 : ℤ) ^ (d - G.card) * (Nat.choose G.card k : ℤ)) =
            ∑ _G ∈ augmentedFacesOfCardFinset X i,
              (-1 : ℤ) ^ (d - i) * (Nat.choose i k : ℤ) := by
          apply Finset.sum_congr rfl
          intro G hG
          rw [(mem_augmentedFacesOfCardFinset.mp hG).2]
        _ = (-1 : ℤ) ^ (d - i) * (Nat.choose i k : ℤ) *
            (extendedFaceCount X i : ℤ) := by
          rw [Finset.sum_const]
          rw [nsmul_eq_mul, card_augmentedFacesOfCardFinset]
          ring
    _ = ∑ i ∈ Finset.Icc k d,
        (-1 : ℤ) ^ (d - i) * (Nat.choose i k : ℤ) *
          (extendedFaceCount X i : ℤ) := by
      symm
      apply Finset.sum_subset
      · intro i hi
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hi).2)
      · intro i hi hiIcc
        have hid : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hik : i < k := by
          simp only [Finset.mem_Icc, not_and_or, not_le] at hiIcc
          rcases hiIcc with hiIcc | hiIcc
          · exact hiIcc
          · exact (not_lt_of_ge hid hiIcc).elim
        rw [Nat.choose_eq_zero_of_lt hik]
        simp

lemma hasEulerRelations_of_hasCofaceEulerRelations {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (hcard : ∀ G ∈ augmentedFaces X, G.card ≤ d)
    (hX : HasCofaceEulerRelations X) : HasEulerRelations X := by
  intro k hkd
  rw [← sum_augmentedFaces_grouped_by_card X hcard]
  rw [← sum_cofaces_over_fixedCard X]
  calc
    (∑ σ ∈ augmentedFacesOfCardFinset X k,
      ∑ G ∈ cofaces X σ, (-1 : ℤ) ^ (d - G.card)) =
        ∑ _σ ∈ augmentedFacesOfCardFinset X k, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact hX σ (mem_augmentedFacesOfCardFinset.mp hσ).1
    _ = extendedFaceCount X k := by
      simp [card_augmentedFacesOfCardFinset]

lemma hasEulerRelations_of_hasEulerianLinks {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (hcard : ∀ G ∈ augmentedFaces X, G.card ≤ d)
    (hX : HasEulerianLinks X) : HasEulerRelations X :=
  hasEulerRelations_of_hasCofaceEulerRelations X hcard
    (hasCofaceEulerRelations_of_hasEulerianLinks X hcard hX)

lemma hasEulerRelations_of_hasSignedEulerianLinks {d : ℕ}
    (X : FiniteSimplicialSphere d) (hX : HasSignedEulerianLinks X) :
    HasEulerRelations X :=
  hasEulerRelations_of_hasEulerianLinks X
    (fun _G hG => card_le_dim_of_hasSignedEulerianLinks X hX hG)
    (hasEulerianLinks_of_hasSignedEulerianLinks X hX)

lemma dehn_sommerville_of_hasSignedEulerianLinks {d j : ℕ}
    (X : FiniteSimplicialSphere d) (hX : HasSignedEulerianLinks X) (hj : j ≤ d) :
    hVector X j = hVector X (d - j) :=
  dehn_sommerville_of_eulerRelations X
    (hasEulerRelations_of_hasSignedEulerianLinks X hX) hj

end

end DehnSommerville

end Submission.Helpers
