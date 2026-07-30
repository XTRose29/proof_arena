import ChallengeDeps

namespace Submission.Helpers

open LeanEval.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open MvPolynomial

variable {K : Type*} [Field K]

lemma eval_smul_of_isHomogeneous {σ : Type*} {p : MvPolynomial σ K} {N : ℕ}
    (hp : p.IsHomogeneous N) (c : K) (x : σ → K) :
    eval (c • x) p = c ^ N * eval x p := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hp.degree_eq_sum_deg_support hs, ← Finset.prod_pow_eq_pow_sum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  ring

lemma eval₂_smul_of_isHomogeneous {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial σ R} {N : ℕ} (hp : p.IsHomogeneous N)
    (f : R →+* S) (c : S) (x : σ → S) :
    eval₂ f (c • x) p = c ^ N * eval₂ f x p := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hp.degree_eq_sum_deg_support hs, ← Finset.prod_pow_eq_pow_sum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  ring

lemma chartIndex_rep_ne_zero {n : ℕ} (p : ProjSpace K n) :
    Projectivization.rep p (chartIndex p) ≠ 0 :=
  Classical.choose_spec (Function.ne_iff.mp p.rep_nonzero)

lemma affineConeCoord_chartIndex {n : ℕ} (p : ProjSpace K n) :
    affineConeCoord p (chartIndex p) = 1 := by
  simp [affineConeCoord, chartIndex_rep_ne_zero p]

lemma affineConeCoord_eq_smul_rep {n : ℕ} (p : ProjSpace K n) :
    affineConeCoord p = (Projectivization.rep p (chartIndex p))⁻¹ • Projectivization.rep p := by
  funext j
  simp [affineConeCoord, div_eq_inv_mul]

lemma eval_affineConeCoord_eq {n N : ℕ} (p : ProjSpace K n)
    {g : MvPolynomial (Fin (n + 1)) K} (hg : g.IsHomogeneous N) :
    eval (affineConeCoord p) g =
      (Projectivization.rep p (chartIndex p))⁻¹ ^ N * eval (Projectivization.rep p) g := by
  rw [affineConeCoord_eq_smul_rep p, eval_smul_of_isHomogeneous hg]

lemma eval_affineConeCoord_eq_zero {n N : ℕ} (p : ProjSpace K n)
    {g : MvPolynomial (Fin (n + 1)) K} (hg : g.IsHomogeneous N)
    (hp : p ∈ vanishingSet g) :
    eval (affineConeCoord p) g = 0 := by
  rw [eval_affineConeCoord_eq p hg, hp]
  simp

lemma eval_slice_eq_zero {n : ℕ} (p : ProjSpace K n) :
    eval (affineConeCoord p) (X (chartIndex p) - C 1) = 0 := by
  simp [affineConeCoord_chartIndex p]

noncomputable def localEvalAt {n : ℕ} (q : Fin (n + 1) → K) :
    localRingAt q →+* K :=
  IsLocalization.lift (M := (maxIdealAt q).primeCompl) (S := localRingAt q)
    (g := evalAt q) fun y => by
    rw [isUnit_iff_ne_zero]
    simpa only [Ideal.mem_primeCompl_iff, maxIdealAt, RingHom.mem_ker] using y.2

@[simp]
lemma localEvalAt_algebraMap {n : ℕ} (q : Fin (n + 1) → K)
    (g : MvPolynomial (Fin (n + 1)) K) :
    localEvalAt q (algebraMap _ (localRingAt q) g) = eval q g := by
  exact IsLocalization.lift_eq (M := (maxIdealAt q).primeCompl)
    (S := localRingAt q) (g := evalAt q) _ g

noncomputable def localIntersectionIdeal {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (p : ProjSpace K n) :
    Ideal (localRingAt (affineConeCoord p)) :=
  let φ : MvPolynomial (Fin (n + 1)) K →+* localRingAt (affineConeCoord p) := algebraMap _ _
  Ideal.span ((Set.range fun k : Fin n => φ (f k)) ∪ {φ (X (chartIndex p) - C 1)})

lemma localIntersectionIdeal_le_ker {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k)) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k)) :
    localIntersectionIdeal f p ≤ RingHom.ker (localEvalAt (affineConeCoord p)) := by
  rw [localIntersectionIdeal, Ideal.span_le]
  rintro g (⟨k, rfl⟩ | rfl)
  · change localEvalAt (affineConeCoord p)
      (algebraMap _ (localRingAt (affineConeCoord p)) (f k)) = 0
    rw [localEvalAt_algebraMap]
    exact eval_affineConeCoord_eq_zero p (hd k) (Set.mem_iInter.mp hp k)
  · change localEvalAt (affineConeCoord p)
      (algebraMap _ (localRingAt (affineConeCoord p)) (X (chartIndex p) - C 1)) = 0
    rw [localEvalAt_algebraMap]
    exact eval_slice_eq_zero p

lemma localIntersectionIdeal_ne_top {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k)) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k)) :
    localIntersectionIdeal f p ≠ ⊤ := by
  intro htop
  apply RingHom.ker_ne_top (localEvalAt (affineConeCoord p))
  exact top_unique (htop ▸ localIntersectionIdeal_le_ker f d hd p hp)

lemma intersectionMultiplicity_pos {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k)) (p : ProjSpace K n)
    (hp : p ∈ ⋂ k, vanishingSet (f k)) :
    0 < intersectionMultiplicity f p := by
  rw [intersectionMultiplicity]
  change 0 < Module.length K
    (localRingAt (affineConeCoord p) ⧸ localIntersectionIdeal f p)
  rw [Module.length_pos_iff, Ideal.Quotient.nontrivial_iff]
  exact localIntersectionIdeal_ne_top f d hd p hp

noncomputable def pointHyperplane {n : ℕ} (p : ProjSpace K n) :
    Subspace K (Fin (n + 1) → K) :=
  LinearMap.ker ((dotProductBilin K K) (Projectivization.rep p))

lemma pointHyperplane_ne_top {n : ℕ} (p : ProjSpace K n) :
    pointHyperplane p ≠ ⊤ := by
  rw [pointHyperplane, ne_eq, LinearMap.ker_eq_top]
  intro hzero
  have h := LinearMap.congr_fun hzero (Pi.single (chartIndex p) 1)
  change dotProduct (Projectivization.rep p) (Pi.single (chartIndex p) 1) = 0 at h
  rw [dotProduct_single_one] at h
  exact chartIndex_rep_ne_zero p h

noncomputable def linearForm {n : ℕ} (a : Fin (n + 1) → K) :
    MvPolynomial (Fin (n + 1)) K :=
  ∑ i, C (a i) * X i

lemma linearForm_isHomogeneous {n : ℕ} (a : Fin (n + 1) → K) :
    (linearForm a).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X (a i) i

lemma eval_linearForm {n : ℕ} (a x : Fin (n + 1) → K) :
    eval x (linearForm a) = dotProduct a x := by
  simp [linearForm, dotProduct]

lemma exists_linearForm_nonzero_on_finite [IsAlgClosed K] {n : ℕ}
    (S : Set (ProjSpace K n)) (hS : S.Finite) :
    ∃ a : Fin (n + 1) → K, ∀ p ∈ S, eval (Projectivization.rep p) (linearForm a) ≠ 0 := by
  let T : Finset (Subspace K (Fin (n + 1) → K)) :=
    hS.toFinset.image fun p => pointHyperplane p
  have htop : (⊤ : Subspace K (Fin (n + 1) → K)) ∉ T := by
    intro hmem
    dsimp [T] at hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨p, _, hp⟩ := hmem
    exact pointHyperplane_ne_top p hp
  have hne := Subspace.biUnion_ne_univ_of_top_notMem htop
  obtain ⟨a, ha⟩ : ∃ a : Fin (n + 1) → K, a ∉ ⋃ U ∈ T, (U : Set (Fin (n + 1) → K)) := by
    by_contra! hall
    apply hne
    exact Set.eq_univ_of_forall hall
  refine ⟨a, fun p hp => ?_⟩
  rw [eval_linearForm, dotProduct_comm]
  intro hzero
  apply ha
  rw [Set.mem_iUnion₂]
  refine ⟨pointHyperplane p, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨p, hS.mem_toFinset.mpr hp, rfl⟩
  · change dotProduct (Projectivization.rep p) a = 0
    exact hzero

noncomputable def linearSliceCoord {n : ℕ} (a : Fin (n + 1) → K) (p : ProjSpace K n) :
    Fin (n + 1) → K :=
  fun j => Projectivization.rep p j / eval (Projectivization.rep p) (linearForm a)

lemma linearSliceCoord_eq_smul_rep {n : ℕ} (a : Fin (n + 1) → K) (p : ProjSpace K n) :
    linearSliceCoord a p =
      (eval (Projectivization.rep p) (linearForm a))⁻¹ • Projectivization.rep p := by
  funext j
  simp [linearSliceCoord, div_eq_inv_mul]

lemma eval_linearSliceCoord_eq {n N : ℕ} (a : Fin (n + 1) → K) (p : ProjSpace K n)
    {g : MvPolynomial (Fin (n + 1)) K} (hg : g.IsHomogeneous N) :
    eval (linearSliceCoord a p) g =
      (eval (Projectivization.rep p) (linearForm a))⁻¹ ^ N *
        eval (Projectivization.rep p) g := by
  rw [linearSliceCoord_eq_smul_rep, eval_smul_of_isHomogeneous hg]

lemma eval_linearForm_linearSliceCoord {n : ℕ} (a : Fin (n + 1) → K)
    (p : ProjSpace K n) (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    eval (linearSliceCoord a p) (linearForm a) = 1 := by
  rw [eval_linearSliceCoord_eq a p (linearForm_isHomogeneous a)]
  simpa using inv_mul_cancel₀ hne

lemma eval_linearSliceCoord_eq_zero {n N : ℕ} (a : Fin (n + 1) → K)
    (p : ProjSpace K n) {g : MvPolynomial (Fin (n + 1)) K}
    (hg : g.IsHomogeneous N) (hp : p ∈ vanishingSet g) :
    eval (linearSliceCoord a p) g = 0 := by
  rw [eval_linearSliceCoord_eq a p hg, hp]
  simp

noncomputable def linearSliceIdeal {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (a : Fin (n + 1) → K)
    (p : ProjSpace K n) : Ideal (localRingAt (linearSliceCoord a p)) :=
  let φ : MvPolynomial (Fin (n + 1)) K →+* localRingAt (linearSliceCoord a p) := algebraMap _ _
  Ideal.span ((Set.range fun k : Fin n => φ (f k)) ∪ {φ (linearForm a - C 1)})

lemma linearSliceIdeal_le_ker {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k)) (a : Fin (n + 1) → K)
    (p : ProjSpace K n) (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    linearSliceIdeal f a p ≤ RingHom.ker (localEvalAt (linearSliceCoord a p)) := by
  rw [linearSliceIdeal, Ideal.span_le]
  rintro g (⟨k, rfl⟩ | rfl)
  · change localEvalAt (linearSliceCoord a p)
      (algebraMap _ (localRingAt (linearSliceCoord a p)) (f k)) = 0
    rw [localEvalAt_algebraMap]
    exact eval_linearSliceCoord_eq_zero a p (hd k) (Set.mem_iInter.mp hp k)
  · change localEvalAt (linearSliceCoord a p)
      (algebraMap _ (localRingAt (linearSliceCoord a p)) (linearForm a - C 1)) = 0
    rw [localEvalAt_algebraMap]
    simp [eval_linearForm_linearSliceCoord a p hne]

lemma linearSliceIdeal_ne_top {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k)) (a : Fin (n + 1) → K)
    (p : ProjSpace K n) (hp : p ∈ ⋂ k, vanishingSet (f k))
    (hne : eval (Projectivization.rep p) (linearForm a) ≠ 0) :
    linearSliceIdeal f a p ≠ ⊤ := by
  intro htop
  apply RingHom.ker_ne_top (localEvalAt (linearSliceCoord a p))
  exact top_unique (htop ▸ linearSliceIdeal_le_ker f d hd a p hp hne)

lemma isUnit_algebraMap_localRingAt {n : ℕ} (q : Fin (n + 1) → K)
    (g : MvPolynomial (Fin (n + 1)) K) (hg : eval q g ≠ 0) :
    IsUnit (algebraMap _ (localRingAt q) g) := by
  exact IsLocalization.map_units (M := (maxIdealAt q).primeCompl) (localRingAt q)
    ⟨g, by
      simpa only [Ideal.mem_primeCompl_iff, maxIdealAt, RingHom.mem_ker, evalAt] using hg⟩

lemma isUnit_quotient_algebraMap_localRingAt {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (g : MvPolynomial (Fin (n + 1)) K)
    (hg : eval q g ≠ 0) :
    IsUnit (Ideal.Quotient.mk I (algebraMap _ (localRingAt q) g)) :=
  (isUnit_algebraMap_localRingAt q g hg).map (Ideal.Quotient.mk I)

noncomputable def quotientCoeffMap {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) : K →+* localRingAt q ⧸ I :=
  (Ideal.Quotient.mk I).comp (algebraMap K (localRingAt q))

noncomputable def quotientPolynomialMap {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) :
    MvPolynomial (Fin (n + 1)) K →+* localRingAt q ⧸ I :=
  (Ideal.Quotient.mk I).comp (algebraMap _ (localRingAt q))

lemma eval₂_quotientPolynomialMap {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (g : MvPolynomial (Fin (n + 1)) K) :
    eval₂ (quotientCoeffMap q I) (fun i => quotientPolynomialMap q I (X i)) g =
      quotientPolynomialMap q I g := by
  change (eval₂Hom (quotientCoeffMap q I) (fun i => quotientPolynomialMap q I (X i))) g = _
  have hhom : eval₂Hom (quotientCoeffMap q I) (fun i => quotientPolynomialMap q I (X i)) =
      quotientPolynomialMap q I := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [eval₂Hom_C]
      change Ideal.Quotient.mk I ((algebraMap K (localRingAt q)) r) =
        Ideal.Quotient.mk I
          ((algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q)) (C r))
      congr 1
    · intro i
      simp
  rw [hhom]

noncomputable def normalizationUnit {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (g : MvPolynomial (Fin (n + 1)) K)
    (hg : eval q g ≠ 0) : (localRingAt q ⧸ I)ˣ :=
  (isUnit_quotient_algebraMap_localRingAt q I g hg).unit

lemma normalizationUnit_spec {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (g : MvPolynomial (Fin (n + 1)) K)
    (hg : eval q g ≠ 0) :
    (↑(normalizationUnit q I g hg) : localRingAt q ⧸ I) = quotientPolynomialMap q I g := by
  exact (isUnit_quotient_algebraMap_localRingAt q I g hg).unit_spec

noncomputable def normalizeHom {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (g : MvPolynomial (Fin (n + 1)) K)
    (hg : eval q g ≠ 0) :
    MvPolynomial (Fin (n + 1)) K →+* localRingAt q ⧸ I :=
  eval₂Hom (quotientCoeffMap q I) fun i =>
    (↑(normalizationUnit q I g hg)⁻¹ : localRingAt q ⧸ I) * quotientPolynomialMap q I (X i)

lemma normalizeHom_of_isHomogeneous {n N : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (g h : MvPolynomial (Fin (n + 1)) K)
    (hg : eval q g ≠ 0) (hh : h.IsHomogeneous N) :
    normalizeHom q I g hg h =
      (↑(normalizationUnit q I g hg)⁻¹ : localRingAt q ⧸ I) ^ N *
        quotientPolynomialMap q I h := by
  rw [normalizeHom]
  change eval₂ (quotientCoeffMap q I)
      ((↑(normalizationUnit q I g hg)⁻¹ : localRingAt q ⧸ I) •
        fun i => quotientPolynomialMap q I (X i)) h = _
  rw [eval₂_smul_of_isHomogeneous hh, eval₂_quotientPolynomialMap]

lemma normalizeHom_degree_one {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (g : MvPolynomial (Fin (n + 1)) K)
    (hg : eval q g ≠ 0) (hhom : g.IsHomogeneous 1) :
    normalizeHom q I g hg g = 1 := by
  rw [normalizeHom_of_isHomogeneous q I g g hg hhom, pow_one,
    ← normalizationUnit_spec q I g hg]
  exact Units.inv_mul (normalizationUnit q I g hg)

noncomputable def quotientLocalEval {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (hI : I ≤ RingHom.ker (localEvalAt q)) :
    localRingAt q ⧸ I →+* K :=
  Ideal.Quotient.lift I (localEvalAt q) fun _x hx => RingHom.mem_ker.mp (hI hx)

@[simp]
lemma quotientLocalEval_mk {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (hI : I ≤ RingHom.ker (localEvalAt q))
    (x : localRingAt q) :
    quotientLocalEval q I hI (Ideal.Quotient.mk I x) = localEvalAt q x := by
  exact Ideal.Quotient.lift_mk I (localEvalAt q) _

lemma quotientLocalEval_surjective {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (hI : I ≤ RingHom.ker (localEvalAt q)) :
    Function.Surjective (quotientLocalEval q I hI) := by
  intro k
  refine ⟨Ideal.Quotient.mk I (algebraMap K (localRingAt q) k), ?_⟩
  rw [quotientLocalEval_mk]
  calc
    localEvalAt q (algebraMap K (localRingAt q) k) =
        localEvalAt q
          (algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q) (C k)) := by
      congr 1
    _ = eval q (C k) := localEvalAt_algebraMap q (C k)
    _ = k := by simp

lemma isUnit_of_quotientLocalEval_ne_zero {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (hI : I ≤ RingHom.ker (localEvalAt q))
    (x : localRingAt q ⧸ I) (hx : quotientLocalEval q I hI x ≠ 0) :
    IsUnit x := by
  have hIne : I ≠ ⊤ := by
    intro htop
    apply RingHom.ker_ne_top (localEvalAt q)
    exact top_unique (htop ▸ hI)
  letI : Nontrivial (localRingAt q ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  letI : IsLocalRing (localRingAt q ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  apply (IsLocalRing.notMem_maximalIdeal (R := localRingAt q ⧸ I) (x := x)).mp
  rw [← IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective (quotientLocalEval q I hI)
      (quotientLocalEval_surjective q I hI))]
  simpa only [RingHom.mem_ker] using hx

lemma quotientLocalEval_quotientPolynomialMap {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (hI : I ≤ RingHom.ker (localEvalAt q))
    (g : MvPolynomial (Fin (n + 1)) K) :
    quotientLocalEval q I hI (quotientPolynomialMap q I g) = eval q g := by
  rw [quotientPolynomialMap, RingHom.comp_apply, quotientLocalEval_mk,
    localEvalAt_algebraMap]

lemma quotientLocalEval_normalizationUnit {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (hI : I ≤ RingHom.ker (localEvalAt q))
    (g : MvPolynomial (Fin (n + 1)) K) (hg : eval q g ≠ 0) :
    quotientLocalEval q I hI (normalizationUnit q I g hg) = eval q g := by
  rw [normalizationUnit_spec, quotientLocalEval_quotientPolynomialMap]

lemma quotientLocalEval_normalizeHom {n : ℕ} (q : Fin (n + 1) → K)
    (I : Ideal (localRingAt q)) (hI : I ≤ RingHom.ker (localEvalAt q))
    (g : MvPolynomial (Fin (n + 1)) K) (hg : eval q g ≠ 0) :
    (quotientLocalEval q I hI).comp (normalizeHom q I g hg) =
      eval fun i => q i / eval q g := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, normalizeHom, eval₂Hom_C, eval_C]
    change quotientLocalEval q I hI ((quotientCoeffMap q I) r) = r
    rw [quotientCoeffMap, RingHom.comp_apply, quotientLocalEval_mk]
    calc
      localEvalAt q (algebraMap K (localRingAt q) r) =
          localEvalAt q
            (algebraMap (MvPolynomial (Fin (n + 1)) K) (localRingAt q) (C r)) := by
        congr 1
      _ = eval q (C r) := localEvalAt_algebraMap q (C r)
      _ = r := by simp
  · intro i
    rw [RingHom.comp_apply, normalizeHom, eval₂Hom_X', map_mul]
    simp [quotientLocalEval_normalizationUnit, quotientLocalEval_quotientPolynomialMap,
      eval_X, div_eq_mul_inv, mul_comm]

noncomputable def localNormalizeHom {n : ℕ}
    (q q' : Fin (n + 1) → K) (I : Ideal (localRingAt q))
    (hI : I ≤ RingHom.ker (localEvalAt q))
    (g : MvPolynomial (Fin (n + 1)) K) (hg : eval q g ≠ 0)
    (hcenter : q' = fun i => q i / eval q g) :
    localRingAt q' →+* localRingAt q ⧸ I :=
  IsLocalization.lift (M := (maxIdealAt q').primeCompl) (S := localRingAt q')
    (P := localRingAt q ⧸ I) (g := normalizeHom q I g hg) fun y => by
      apply isUnit_of_quotientLocalEval_ne_zero q I hI
      rw [← RingHom.comp_apply, quotientLocalEval_normalizeHom]
      have hy : eval q' (y : MvPolynomial (Fin (n + 1)) K) ≠ 0 := by
        simpa only [Ideal.mem_primeCompl_iff, maxIdealAt, RingHom.mem_ker, evalAt] using y.2
      simpa only [hcenter] using hy

end Submission.Helpers
