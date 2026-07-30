import Submission.AffineBridge

open MvPolynomial RingTheory.Sequence
open scoped Pointwise

variable {K : Type*} [Field K]

namespace Submission.Helpers

attribute [local instance] MvPolynomial.gradedAlgebra

lemma RegularModIdeal.pow {σ : Type*}
    {I : Ideal (MvPolynomial σ K)} {L : MvPolynomial σ K}
    (hreg : RegularModIdeal I L) (k : ℕ) :
    RegularModIdeal I (L ^ k) := by
  induction k with
  | zero =>
      intro p hp
      simpa using hp
  | succ k ih =>
      intro p hp
      apply ih p
      apply hreg (L ^ k * p)
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hp

set_option maxHeartbeats 800000 in
lemma homogeneousPowMulQuotient_injective {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (hreg : RegularModIdeal I L)
    (i j : ℕ) (hij : i ≤ j) :
    Function.Injective (homogeneousPowMulQuotient I L hL i j hij) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
        rw [LinearMap.mem_ker, homogeneousPowMulQuotient_apply,
          Submodule.Quotient.mk_eq_zero] at hx
        rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
        exact hreg.pow (j - i) p.1 hx
  · exact bot_le

set_option maxHeartbeats 800000 in
lemma range_homogeneousPowMulQuotient_succ_eq_ker_factor {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (i : ℕ) :
    LinearMap.range
        (homogeneousPowMulQuotient I L hL i (i + 1) (Nat.le_succ i)) =
      LinearMap.ker
        (homogeneousQuotientFactor
          (show I ≤ I ⊔ Ideal.span {L} from le_sup_left) (i + 1)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
        rw [LinearMap.mem_ker, homogeneousPowMulQuotient_apply,
          homogeneousQuotientFactor_apply, Submodule.Quotient.mk_eq_zero]
        change L ^ (i + 1 - i) * p.1 ∈ I ⊔ Ideal.span {L}
        simp only [Nat.add_sub_cancel_left, pow_one]
        apply (show Ideal.span {L} ≤ I ⊔ Ideal.span {L} from le_sup_right)
        simpa [mul_comm] using
          (Ideal.span {L}).mul_mem_left p.1
            (Ideal.mem_span_singleton_self L)
  · intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
        rw [LinearMap.mem_ker, homogeneousQuotientFactor_apply,
          Submodule.Quotient.mk_eq_zero] at hx
        change p.1 ∈ I ⊔ Ideal.span {L} at hx
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hb
        let qh : HomogeneousPiece (K := K) (σ := σ) i :=
          ⟨homogeneousComponent i q, homogeneousComponent_isHomogeneous _ _⟩
        refine ⟨Submodule.Quotient.mk qh, ?_⟩
        rw [homogeneousPowMulQuotient_apply]
        apply (Submodule.Quotient.eq' (homogeneousIdealPart I (i + 1))).2
        have hacomp : homogeneousComponent (i + 1) a ∈ I :=
          homogeneousComponent_mem_of_isHomogeneousIdeal hI ha (i + 1)
        have hpcomp : homogeneousComponent (i + 1) a +
            homogeneousComponent (i + 1) (q * L) = p.1 := by
          calc
            _ = homogeneousComponent (i + 1) p.1 := by
              rw [← map_add, hab]
            _ = p.1 := by
              rw [homogeneousComponent_of_mem p.2, if_pos rfl]
        have hqcomp : homogeneousComponent (i + 1) (q * L) =
            L * homogeneousComponent i q := by
          rw [homogeneousComponent_mul_right_of_le hL (by omega)]
          have hsub : i + 1 - 1 = i := by omega
          rw [hsub, mul_comm]
        change -(L ^ (i + 1 - i) * homogeneousComponent i q) + p.1 ∈ I
        rw [Nat.add_sub_cancel_left, pow_one, ← hpcomp, hqcomp]
        simpa [add_assoc] using hacomp

set_option maxHeartbeats 800000 in
lemma homogeneousPowMulQuotient_succ_surjective {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (i : ℕ)
    (hzero :
      Subsingleton (HomogeneousQuotientPiece (I ⊔ Ideal.span {L}) (i + 1))) :
    Function.Surjective
      (homogeneousPowMulQuotient I L hL i (i + 1) (Nat.le_succ i)) := by
  let mul := homogeneousPowMulQuotient I L hL i (i + 1) (Nat.le_succ i)
  let fac := homogeneousQuotientFactor
    (show I ≤ I ⊔ Ideal.span {L} from le_sup_left) (i + 1)
  have hrange : LinearMap.range mul = LinearMap.ker fac :=
    range_homogeneousPowMulQuotient_succ_eq_ker_factor I L hL hI i
  letI := hzero
  have hker : LinearMap.ker fac = ⊤ := by
    apply top_unique
    intro x _
    rw [LinearMap.mem_ker]
    exact Subsingleton.elim _ _
  exact LinearMap.range_eq_top.mp (hrange.trans hker)

set_option maxHeartbeats 800000 in
lemma homogeneousPowMulQuotient_surjective_of_vanishing {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (N : ℕ)
    (hzero : ∀ m, N < m →
      Subsingleton (HomogeneousQuotientPiece (I ⊔ Ideal.span {L}) m))
    {j : ℕ} (hNj : N ≤ j) :
    Function.Surjective (homogeneousPowMulQuotient I L hL N j hNj) := by
  induction hNj with
  | refl =>
      intro x
      exact ⟨x, homogeneousPowMulQuotient_self I L hL N x⟩
  | @step j hNj ih =>
      have hstep :=
        homogeneousPowMulQuotient_succ_surjective I L hL hI j
          (hzero (j + 1) (lt_of_le_of_lt hNj (Nat.lt_succ_self j)))
      intro x
      obtain ⟨y, hy⟩ := hstep x
      obtain ⟨z, hz⟩ := ih y
      refine ⟨z, ?_⟩
      rw [← homogeneousPowMulQuotient_comp I L hL N j (j + 1)
        hNj (Nat.le_succ j) z, hz, hy]

noncomputable def stablePieceToDirectLimit {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1) (N : ℕ) :
    HomogeneousQuotientPiece I N →ₗ[K]
      HomogeneousQuotientDirectLimit I L hL :=
  Module.DirectLimit.of K ℕ
    (fun i ↦ HomogeneousQuotientPiece I i)
    (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij) N

lemma stablePieceToDirectLimit_injective {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (hreg : RegularModIdeal I L) (N : ℕ) :
    Function.Injective (stablePieceToDirectLimit I L hL N) := by
  intro x y hxy
  obtain ⟨j, hNj, hmap⟩ :=
    Module.DirectLimit.exists_eq_of_of_eq
      (R := K) (G := fun i ↦ HomogeneousQuotientPiece I i)
      (f := fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij) hxy
  exact homogeneousPowMulQuotient_injective I L hL hreg N j hNj hmap

set_option maxHeartbeats 800000 in
lemma stablePieceToDirectLimit_surjective {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (N : ℕ)
    (hzero : ∀ m, N < m →
      Subsingleton (HomogeneousQuotientPiece (I ⊔ Ideal.span {L}) m)) :
    Function.Surjective (stablePieceToDirectLimit I L hL N) := by
  intro z
  obtain ⟨i, x, rfl⟩ :=
    Module.DirectLimit.exists_of
      (R := K) (G := fun i ↦ HomogeneousQuotientPiece I i)
      (f := fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij) z
  let j := max N i
  have hNj : N ≤ j := le_max_left N i
  have hij : i ≤ j := le_max_right N i
  let y := homogeneousPowMulQuotient I L hL i j hij x
  obtain ⟨w, hw⟩ :=
    homogeneousPowMulQuotient_surjective_of_vanishing
      I L hL hI N hzero hNj y
  refine ⟨w, ?_⟩
  calc
    Module.DirectLimit.of K ℕ
        (fun i ↦ HomogeneousQuotientPiece I i)
        (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij) N w =
      Module.DirectLimit.of K ℕ
        (fun i ↦ HomogeneousQuotientPiece I i)
        (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij) j
        (homogeneousPowMulQuotient I L hL N j hNj w) :=
          (Module.DirectLimit.of_f
            (R := K) (G := fun i ↦ HomogeneousQuotientPiece I i)
            (f := fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij)).symm
    _ = Module.DirectLimit.of K ℕ
        (fun i ↦ HomogeneousQuotientPiece I i)
        (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij) j y := by
          rw [hw]
    _ = Module.DirectLimit.of K ℕ
        (fun i ↦ HomogeneousQuotientPiece I i)
        (fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij) i x :=
          Module.DirectLimit.of_f
            (R := K) (G := fun i ↦ HomogeneousQuotientPiece I i)
            (f := fun i j hij ↦ homogeneousPowMulQuotient I L hL i j hij)

noncomputable def stablePieceDirectLimitEquiv {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (hreg : RegularModIdeal I L) (N : ℕ)
    (hzero : ∀ m, N < m →
      Subsingleton (HomogeneousQuotientPiece (I ⊔ Ideal.span {L}) m)) :
    HomogeneousQuotientPiece I N ≃ₗ[K]
      HomogeneousQuotientDirectLimit I L hL :=
  LinearEquiv.ofBijective (stablePieceToDirectLimit I L hL N)
    ⟨stablePieceToDirectLimit_injective I L hL hreg N,
      stablePieceToDirectLimit_surjective I L hL hI N hzero⟩

noncomputable def stablePieceDehomogenizedEquiv {σ : Type*}
    (I : Ideal (MvPolynomial σ K))
    (L : MvPolynomial σ K) (hL : L.IsHomogeneous 1)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (hreg : RegularModIdeal I L) (N : ℕ)
    (hzero : ∀ m, N < m →
      Subsingleton (HomogeneousQuotientPiece (I ⊔ Ideal.span {L}) m)) :
    HomogeneousQuotientPiece I N ≃ₗ[K]
      MvPolynomial σ K ⧸ dehomogenizedSliceIdeal I L :=
  stablePieceDirectLimitEquiv I L hL hI hreg N hzero ≪≫ₗ
    homogeneousDirectLimitDehomogenizedEquiv I L hL hI

end Submission.Helpers
