import Submission.HilbertProduct
import Mathlib.Algebra.Colimit.Module
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Regular.Flat

open MvPolynomial RingTheory.Sequence
open scoped Pointwise

variable {K : Type*} [Field K]

namespace Submission.Helpers

attribute [local instance] MvPolynomial.gradedAlgebra

lemma mem_of_mul_mem_idealOfList_of_isRegular_append
    {R : Type*} [CommRing R] (gs : List R) (r x : R)
    (hreg : IsRegular R (gs ++ [r]))
    (hx : r * x ∈ Ideal.ofList gs) :
    x ∈ Ideal.ofList gs := by
  have hlast := hreg.toIsWeaklyRegular.regular_mod_prev gs.length (by simp)
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at hlast
  have hsmul :
      Ideal.ofList ((gs ++ [r]).take gs.length) •
          (⊤ : Submodule R R) =
        (Ideal.ofList gs : Submodule R R) := by
    simp
  rw [hsmul] at hlast
  apply hlast x
  simpa [smul_eq_mul] using hx

set_option maxHeartbeats 800000 in
lemma regularModIdeal_head_of_regular_cons
    {σ : Type*} [Finite σ]
    (r : MvPolynomial σ K) (gs : List (MvPolynomial σ K))
    (hreg : IsRegular (MvPolynomial σ K) (r :: gs)) :
    RegularModIdeal (Ideal.ofList gs) r := by
  intro x hx
  apply Ideal.mem_of_localization_maximal
  intro P hP
  let S := Localization.AtPrime P
  let φ : MvPolynomial σ K →+* S := algebraMap _ _
  by_cases hIP : Ideal.ofList gs ≤ P
  · by_cases hrP : r ∈ P
    · have hall : ∀ q ∈ r :: gs, q ∈ P := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hrP
        · exact hIP (Ideal.subset_span hq)
      have hlocal : IsRegular S ((r :: gs).map φ) :=
        hreg.toIsWeaklyRegular.isRegular_of_isLocalization_of_mem S P hall
      have hperm :
          ((r :: gs).map φ).Perm ((gs.map φ) ++ [φ r]) := by
        simpa using
          (List.perm_append_comm :
            ([φ r] ++ gs.map φ).Perm (gs.map φ ++ [φ r]))
      have hlocal' : IsRegular S ((gs.map φ) ++ [φ r]) :=
        IsLocalRing.isRegular_of_perm hlocal hperm
      rw [Ideal.map_ofList]
      apply mem_of_mul_mem_idealOfList_of_isRegular_append
        (gs.map φ) (φ r) (φ x) hlocal'
      rw [← map_mul]
      rw [← Ideal.map_ofList]
      exact Ideal.mem_map_of_mem φ hx
    · have hunit : IsUnit (φ r) :=
        IsLocalization.map_units (M := P.primeCompl) S ⟨r, hrP⟩
      have hmul : φ r * φ x ∈ Ideal.map φ (Ideal.ofList gs) := by
        rw [← map_mul]
        exact Ideal.mem_map_of_mem φ hx
      apply ((Ideal.map φ (Ideal.ofList gs)).smul_mem_iff_of_isUnit hunit).mp
      simpa [smul_eq_mul] using hmul
  · rw [IsLocalization.AtPrime.map_eq_top_of_not_le S hIP]
    exact Submodule.mem_top

noncomputable def dehomogenizedSliceIdeal {σ : Type*}
    (I : Ideal (MvPolynomial σ K)) (L : MvPolynomial σ K) :
    Ideal (MvPolynomial σ K) :=
  I ⊔ Ideal.span {L - C 1}

noncomputable def homogeneousPowMulLinear {σ : Type*}
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (i j : ℕ) (hij : i ≤ j) :
    HomogeneousPiece (K := K) (σ := σ) i →ₗ[K]
      HomogeneousPiece (K := K) (σ := σ) j :=
  ((LinearMap.mulLeft K (L ^ (j - i))).domRestrict
    (homogeneousSubmodule σ K i)).codRestrict
      (homogeneousSubmodule σ K j) fun p => by
        change (L ^ (j - i) * p.1).IsHomogeneous j
        convert (hL.pow (j - i)).mul p.2 using 1
        omega

lemma homogeneousPowMulLinear_apply {σ : Type*}
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (i j : ℕ) (hij : i ≤ j)
    (p : HomogeneousPiece (K := K) (σ := σ) i) :
    (homogeneousPowMulLinear L hL i j hij p : MvPolynomial σ K) =
      L ^ (j - i) * p :=
  rfl

noncomputable def homogeneousPowMulQuotient {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (i j : ℕ) (hij : i ≤ j) :
    HomogeneousQuotientPiece I i →ₗ[K] HomogeneousQuotientPiece I j :=
  (homogeneousIdealPart I i).mapQ (homogeneousIdealPart I j)
    (homogeneousPowMulLinear L hL i j hij) fun p hp => by
      change L ^ (j - i) * p.1 ∈ I
      exact I.mul_mem_left _ hp

lemma homogeneousPowMulQuotient_apply {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (i j : ℕ) (hij : i ≤ j)
    (p : HomogeneousPiece (K := K) (σ := σ) i) :
    homogeneousPowMulQuotient I L hL i j hij (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (homogeneousPowMulLinear L hL i j hij p) :=
  rfl

lemma homogeneousPowMulQuotient_self {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (i : ℕ) (x : HomogeneousQuotientPiece I i) :
    homogeneousPowMulQuotient I L hL i i le_rfl x = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ p =>
      rw [homogeneousPowMulQuotient_apply]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      simp [homogeneousPowMulLinear_apply]

lemma homogeneousPowMulQuotient_comp {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k)
    (x : HomogeneousQuotientPiece I i) :
    homogeneousPowMulQuotient I L hL j k hjk
        (homogeneousPowMulQuotient I L hL i j hij x) =
      homogeneousPowMulQuotient I L hL i k (hij.trans hjk) x := by
  induction x using Submodule.Quotient.induction_on with
  | _ p =>
      rw [homogeneousPowMulQuotient_apply, homogeneousPowMulQuotient_apply,
        homogeneousPowMulQuotient_apply]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      simp only [homogeneousPowMulLinear_apply]
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

noncomputable instance homogeneousQuotientDirectedSystem {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1) :
    DirectedSystem (fun i ↦ HomogeneousQuotientPiece I i)
      (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij) where
  map_self := fun i x ↦ homogeneousPowMulQuotient_self I L hL i x
  map_map := fun k j i hij hjk x ↦
    homogeneousPowMulQuotient_comp I L hL i j k hij hjk x

set_option maxHeartbeats 800000 in
lemma exists_pow_mul_mem_of_homogeneous_mem_dehomogenized {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (p : MvPolynomial σ K) (i : ℕ) (hpHom : p.IsHomogeneous i)
    (hp : p ∈ dehomogenizedSliceIdeal I L) :
    ∃ k : ℕ, L ^ k * p ∈ I := by
  rw [dehomogenizedSliceIdeal] at hp
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  have hab' : a + q * L - q = p := by
    calc
      a + q * L - q = a + q * (L - C 1) := by
        rw [C_1]
        ring_nf
      _ = p := hab
  have hcomponent (m : ℕ) :
      homogeneousComponent m a + homogeneousComponent m (q * L) -
          homogeneousComponent m q =
        homogeneousComponent m p := by
    simpa [sub_eq_add_neg, add_assoc] using
      congrArg (homogeneousComponent m) hab'
  have hlow : ∀ m, m < i → homogeneousComponent m q ∈ I := by
    intro m
    induction m with
    | zero =>
        intro hzero
        have hc := hcomponent 0
        rw [homogeneousComponent_mul_right_of_not_le hL (by omega),
          homogeneousComponent_of_mem hpHom, if_neg (Nat.ne_of_lt hzero)] at hc
        have ha0 := homogeneousComponent_mem_of_isHomogeneousIdeal hI ha 0
        have heq : homogeneousComponent 0 q = homogeneousComponent 0 a := by
          exact (sub_eq_zero.mp (by simpa using hc)).symm
        rwa [heq]
    | succ m ih =>
        intro hsucc
        have hm : m < i := (Nat.lt_succ_self m).trans hsucc
        have hc := hcomponent (m + 1)
        rw [homogeneousComponent_mul_right_of_le hL (by omega),
          homogeneousComponent_of_mem hpHom, if_neg (by omega : m + 1 ≠ i)] at hc
        have hsub : m + 1 - 1 = m := by omega
        rw [hsub] at hc
        have ham := homogeneousComponent_mem_of_isHomogeneousIdeal hI ha (m + 1)
        have hmul : homogeneousComponent m q * L ∈ I := by
          simpa [mul_comm] using I.mul_mem_left L (ih hm)
        have heq : homogeneousComponent (m + 1) q =
            homogeneousComponent (m + 1) a + homogeneousComponent m q * L := by
          exact (sub_eq_zero.mp hc).symm
        rw [heq]
        exact I.add_mem ham hmul
  have hpq : p + homogeneousComponent i q ∈ I := by
    cases i with
    | zero =>
        have hc := hcomponent 0
        rw [homogeneousComponent_mul_right_of_not_le hL (by omega),
          homogeneousComponent_of_mem hpHom, if_pos rfl] at hc
        have ha0 := homogeneousComponent_mem_of_isHomogeneousIdeal hI ha 0
        have heq : p + homogeneousComponent 0 q = homogeneousComponent 0 a := by
          rw [← hc]
          abel
        rwa [heq]
    | succ i =>
        have hc := hcomponent (i + 1)
        rw [homogeneousComponent_mul_right_of_le hL (by omega),
          homogeneousComponent_of_mem hpHom, if_pos rfl] at hc
        have hsub : i + 1 - 1 = i := by omega
        rw [hsub] at hc
        have hai := homogeneousComponent_mem_of_isHomogeneousIdeal hI ha (i + 1)
        have hmul : homogeneousComponent i q * L ∈ I := by
          simpa [mul_comm] using I.mul_mem_left L (hlow i (by omega))
        have heq : p + homogeneousComponent (i + 1) q =
            homogeneousComponent (i + 1) a + homogeneousComponent i q * L := by
          rw [← hc]
          abel
        rw [heq]
        exact I.add_mem hai hmul
  have hhigh : ∀ k : ℕ,
      L ^ k * p + homogeneousComponent (i + k) q ∈ I := by
    intro k
    induction k with
    | zero => simpa using hpq
    | succ k ih =>
        have hc := hcomponent (i + k + 1)
        rw [homogeneousComponent_mul_right_of_le hL (by omega),
          homogeneousComponent_of_mem hpHom, if_neg (by omega : i + k + 1 ≠ i)] at hc
        have hsub : i + k + 1 - 1 = i + k := by omega
        rw [hsub] at hc
        have haik :=
          homogeneousComponent_mem_of_isHomogeneousIdeal hI ha (i + k + 1)
        have hrel : homogeneousComponent (i + k + 1) q -
            L * homogeneousComponent (i + k) q ∈ I := by
          have heq : homogeneousComponent (i + k + 1) q -
              L * homogeneousComponent (i + k) q =
                homogeneousComponent (i + k + 1) a := by
            rw [← sub_eq_zero.mp hc]
            ring_nf
          rwa [heq]
        have hmul := I.mul_mem_left L ih
        have hadd := I.add_mem hmul hrel
        have heq : L * (L ^ k * p + homogeneousComponent (i + k) q) +
              (homogeneousComponent (i + k + 1) q -
                L * homogeneousComponent (i + k) q) =
            L ^ (k + 1) * p + homogeneousComponent (i + (k + 1)) q := by
          rw [pow_succ]
          ring_nf
        rwa [heq] at hadd
  let k := q.totalDegree + 1
  refine ⟨k, ?_⟩
  have h := hhigh k
  rw [homogeneousComponent_eq_zero (i + k) q (by
    dsimp [k]
    omega), add_zero] at h
  exact h

noncomputable abbrev HomogeneousQuotientDirectLimit {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1) :=
  Module.DirectLimit (fun i ↦ HomogeneousQuotientPiece I i)
    (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij)

noncomputable def homogeneousPieceToDehomogenized {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (m : ℕ) :
    HomogeneousQuotientPiece I m →ₗ[K]
      MvPolynomial σ K ⧸ dehomogenizedSliceIdeal I L := by
  let J := dehomogenizedSliceIdeal I L
  let raw : HomogeneousPiece (K := K) (σ := σ) m →ₗ[K]
      MvPolynomial σ K ⧸ J :=
    (Ideal.Quotient.mkₐ K J).toLinearMap.comp
      (homogeneousSubmodule σ K m).subtype
  exact (homogeneousIdealPart I m).liftQ raw <| by
    intro p hp
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk J p.1 = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (show I ≤ J from le_sup_left) hp

@[simp]
lemma homogeneousPieceToDehomogenized_apply {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (m : ℕ)
    (p : HomogeneousPiece (K := K) (σ := σ) m) :
    homogeneousPieceToDehomogenized I L m (Submodule.Quotient.mk p) =
      Ideal.Quotient.mk (dehomogenizedSliceIdeal I L) p.1 :=
  rfl

lemma homogeneousPieceToDehomogenized_compatible {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (i j : ℕ) (hij : i ≤ j) (x : HomogeneousQuotientPiece I i) :
    homogeneousPieceToDehomogenized I L j
        (homogeneousPowMulQuotient I L hL i j hij x) =
      homogeneousPieceToDehomogenized I L i x := by
  induction x using Submodule.Quotient.induction_on with
  | _ p =>
      rw [homogeneousPowMulQuotient_apply,
        homogeneousPieceToDehomogenized_apply,
        homogeneousPieceToDehomogenized_apply]
      change Ideal.Quotient.mk (dehomogenizedSliceIdeal I L)
          (L ^ (j - i) * p.1) =
        Ideal.Quotient.mk (dehomogenizedSliceIdeal I L) p.1
      have hLone : Ideal.Quotient.mk (dehomogenizedSliceIdeal I L) L = 1 := by
        rw [Ideal.Quotient.mk_eq_one_iff_sub_mem]
        exact (show Ideal.span {L - C 1} ≤ dehomogenizedSliceIdeal I L
          from le_sup_right) (Ideal.subset_span (Set.mem_singleton (L - C 1)))
      rw [map_mul, map_pow, hLone, one_pow, one_mul]

noncomputable def homogeneousDirectLimitToDehomogenized {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1) :
    HomogeneousQuotientDirectLimit I L hL →ₗ[K]
      MvPolynomial σ K ⧸ dehomogenizedSliceIdeal I L :=
  Module.DirectLimit.lift K ℕ
    (fun i ↦ HomogeneousQuotientPiece I i)
    (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij)
    (homogeneousPieceToDehomogenized I L)
    (homogeneousPieceToDehomogenized_compatible I L hL)

@[simp]
lemma homogeneousDirectLimitToDehomogenized_of {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (i : ℕ) (x : HomogeneousQuotientPiece I i) :
    homogeneousDirectLimitToDehomogenized I L hL
        (Module.DirectLimit.of K ℕ
          (fun i ↦ HomogeneousQuotientPiece I i)
          (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij) i x) =
      homogeneousPieceToDehomogenized I L i x :=
  by
    apply Module.DirectLimit.lift_of

set_option maxHeartbeats 800000 in
lemma homogeneousDirectLimitToDehomogenized_surjective {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1) :
    Function.Surjective (homogeneousDirectLimitToDehomogenized I L hL) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ p =>
      induction p using MvPolynomial.decomposition.inductionOn with
      | zero => exact ⟨0, map_zero _⟩
      | homogeneous p =>
          refine ⟨Module.DirectLimit.of K ℕ
            (fun i ↦ HomogeneousQuotientPiece I i)
            (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij)
            _ (Submodule.Quotient.mk p), ?_⟩
          rw [homogeneousDirectLimitToDehomogenized_of,
            homogeneousPieceToDehomogenized_apply]
          rfl
      | add p q hp hq =>
          obtain ⟨x, hx⟩ := hp
          obtain ⟨y, hy⟩ := hq
          refine ⟨x + y, ?_⟩
          rw [map_add, hx, hy]
          rfl

set_option maxHeartbeats 800000 in
lemma homogeneousDirectLimitToDehomogenized_injective {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    Function.Injective (homogeneousDirectLimitToDehomogenized I L hL) := by
  intro z w hzw
  obtain ⟨i, x, y, rfl, rfl⟩ :=
    Module.DirectLimit.exists_of₂
      (R := K) (G := fun i ↦ HomogeneousQuotientPiece I i)
      (f := fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij) z w
  simp only [homogeneousDirectLimitToDehomogenized_of] at hzw
  induction x using Submodule.Quotient.induction_on with
  | _ p =>
    induction y using Submodule.Quotient.induction_on with
    | _ q =>
      rw [homogeneousPieceToDehomogenized_apply,
        homogeneousPieceToDehomogenized_apply,
        Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hzw
      obtain ⟨k, hk⟩ :=
        exists_pow_mul_mem_of_homogeneous_mem_dehomogenized
          I L hL hI (p.1 - q.1) i (p.2.sub q.2) hzw
      let j := i + k
      have hij : i ≤ j := Nat.le_add_right i k
      have hmap :
          homogeneousPowMulQuotient I L hL i j hij
              (Submodule.Quotient.mk p) =
            homogeneousPowMulQuotient I L hL i j hij
              (Submodule.Quotient.mk q) := by
        rw [homogeneousPowMulQuotient_apply,
          homogeneousPowMulQuotient_apply]
        apply (Submodule.Quotient.eq' (homogeneousIdealPart I j)).2
        change -(L ^ (j - i) * p.1) + L ^ (j - i) * q.1 ∈ I
        have hneg := I.neg_mem hk
        change -(L ^ k * (p.1 - q.1)) ∈ I at hneg
        have heq : -(L ^ k * (p.1 - q.1)) =
            -(L ^ k * p.1) + L ^ k * q.1 := by ring_nf
        rw [heq] at hneg
        have hji : j - i = k := by simp [j]
        rw [hji]
        exact hneg
      calc
        Module.DirectLimit.of K ℕ
            (fun i ↦ HomogeneousQuotientPiece I i)
            (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij)
            i (Submodule.Quotient.mk p) =
          Module.DirectLimit.of K ℕ
            (fun i ↦ HomogeneousQuotientPiece I i)
            (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij)
            j (homogeneousPowMulQuotient I L hL i j hij
              (Submodule.Quotient.mk p)) :=
            (Module.DirectLimit.of_f
              (R := K) (G := fun i ↦ HomogeneousQuotientPiece I i)
              (f := fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij)).symm
        _ = Module.DirectLimit.of K ℕ
            (fun i ↦ HomogeneousQuotientPiece I i)
            (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij)
            j (homogeneousPowMulQuotient I L hL i j hij
              (Submodule.Quotient.mk q)) := congrArg _ hmap
        _ = Module.DirectLimit.of K ℕ
            (fun i ↦ HomogeneousQuotientPiece I i)
            (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij)
            i (Submodule.Quotient.mk q) :=
            Module.DirectLimit.of_f
              (R := K) (G := fun i ↦ HomogeneousQuotientPiece I i)
              (f := fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij)

noncomputable def homogeneousDirectLimitDehomogenizedEquiv {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    HomogeneousQuotientDirectLimit I L hL ≃ₗ[K]
      MvPolynomial σ K ⧸ dehomogenizedSliceIdeal I L :=
  LinearEquiv.ofBijective (homogeneousDirectLimitToDehomogenized I L hL)
    ⟨homogeneousDirectLimitToDehomogenized_injective I L hL hI,
      homogeneousDirectLimitToDehomogenized_surjective I L hL⟩

end Submission.Helpers
