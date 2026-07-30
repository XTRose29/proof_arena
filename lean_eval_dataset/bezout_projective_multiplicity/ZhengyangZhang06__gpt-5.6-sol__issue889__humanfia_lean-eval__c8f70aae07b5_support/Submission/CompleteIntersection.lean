import Submission.HilbertSeries
import Submission.Rees
import Submission.QuotientPoints

open LeanEval.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization Pointwise
open MvPolynomial RingTheory.Sequence

variable {K : Type*} [Field K]

namespace Submission.Helpers

noncomputable def coordinateList (m : ℕ) :
    List (MvPolynomial (Fin m) K) :=
  List.ofFn fun i => X i

lemma coordinateList_length (m : ℕ) :
    (coordinateList (K := K) m).length = m := by
  simp [coordinateList]

lemma ideal_of_coordinate_take {m i : ℕ} (hi : i ≤ m) :
    Ideal.ofList ((coordinateList (K := K) m).take i) =
      Ideal.span (X '' {j : Fin m | j.1 < i}) := by
  apply congrArg Ideal.span
  ext p
  constructor
  · intro hp
    change p ∈ (coordinateList (K := K) m).take i at hp
    rw [List.mem_iff_getElem] at hp
    obtain ⟨j, hj, hp⟩ := hp
    have hji : j < i := hj.trans_le (List.length_take_le i _)
    have hjm : j < m := hji.trans_le hi
    refine ⟨⟨j, hjm⟩, hji, ?_⟩
    rw [List.getElem_take] at hp
    simpa [coordinateList] using hp
  · rintro ⟨j, hj, rfl⟩
    change X j ∈ (coordinateList (K := K) m).take i
    rw [List.mem_iff_getElem]
    refine ⟨j.1, ?_, ?_⟩
    · simp only [List.length_take, coordinateList_length, Nat.min_eq_left hi]
      exact hj
    · rw [List.getElem_take]
      simp [coordinateList]

lemma ideal_of_coordinateList (m : ℕ) :
    Ideal.ofList (coordinateList (K := K) m) = idealOfVars (Fin m) K := by
  have h := ideal_of_coordinate_take (K := K) (m := m) (i := m) le_rfl
  have ht : (coordinateList (K := K) m).take m =
      coordinateList (K := K) m := by
    simp [coordinateList]
  rw [ht] at h
  rw [h]
  congr 1
  ext p
  simp

lemma idealOfVars_ne_top (m : ℕ) : (idealOfVars (Fin m) K : Ideal _) ≠ ⊤ := by
  intro htop
  have hmem : C (1 : K) ∈ idealOfVars (Fin m) K := by
    rw [htop]
    trivial
  simpa using (C_mem_pow_idealOfVars_iff (σ := Fin m) 1 (1 : K)).mp
    (by simpa using hmem)

lemma coordinateList_isRegular (m : ℕ) :
    IsRegular (MvPolynomial (Fin m) K) (coordinateList (K := K) m) := by
  rw [isRegular_iff]
  constructor
  · rw [isWeaklyRegular_iff_Fin]
    intro i
    have him_lt : i.1 < m := by
      simpa [coordinateList] using i.2
    have him : i.1 ≤ m := him_lt.le
    have hi_eq :
        (coordinateList (K := K) m).get i = X (⟨i.1, him_lt⟩ : Fin m) := by
      simp [coordinateList]
    change IsSMulRegular
      (MvPolynomial (Fin m) K ⧸
        Ideal.ofList ((coordinateList (K := K) m).take i.1) • ⊤)
      ((coordinateList (K := K) m).get i)
    rw [hi_eq, isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro p hp
    have hsmul :
        Ideal.ofList ((coordinateList (K := K) m).take i.1) •
          (⊤ : Submodule (MvPolynomial (Fin m) K)
            (MvPolynomial (Fin m) K)) =
        (Ideal.ofList ((coordinateList (K := K) m).take i.1) :
          Submodule (MvPolynomial (Fin m) K) (MvPolynomial (Fin m) K)) := by
      simp
    rw [hsmul] at hp ⊢
    change X (⟨i.1, him_lt⟩ : Fin m) * p ∈
      Ideal.ofList ((coordinateList (K := K) m).take i.1) at hp
    change p ∈ Ideal.ofList ((coordinateList (K := K) m).take i.1)
    rw [ideal_of_coordinate_take him] at hp ⊢
    rw [mem_ideal_span_X_image] at hp ⊢
    intro e he
    let ii : Fin m := ⟨i.1, him_lt⟩
    have he' : Finsupp.single ii 1 + e ∈ (X ii * p).support := by
      rw [support_X_mul]
      exact Finset.mem_map.mpr ⟨e, he, rfl⟩
    obtain ⟨j, hj, hne⟩ := hp _ he'
    refine ⟨j, hj, ?_⟩
    have hji : j ≠ ii := by
      intro h
      subst j
      exact (Nat.lt_irrefl i.1) hj
    simpa [Finsupp.single_apply, hji] using hne
  · have hI := ideal_of_coordinateList (K := K) m
    change (⊤ : Submodule (MvPolynomial (Fin m) K)
      (MvPolynomial (Fin m) K)) ≠
      Ideal.ofList (coordinateList (K := K) m) • ⊤
    simpa [hI] using Ne.symm (idealOfVars_ne_top (K := K) m)

lemma vanishingIdeal_singleton_zero_eq_idealOfVars {σ : Type*} :
    MvPolynomial.vanishingIdeal K {(0 : σ → K)} = idealOfVars σ K := by
  ext p
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  constructor
  · intro hp e he
    change MvPolynomial.eval (0 : σ → K) p = 0 at hp
    rw [eval_zero] at hp
    rw [Nat.one_le_iff_ne_zero]
    intro he0
    have : e = 0 := (Finsupp.degree_eq_zero_iff e).mp he0
    subst e
    change p.coeff 0 = 0 at hp
    exact (mem_support_iff.mp he) hp
  · intro hp
    change MvPolynomial.eval (0 : σ → K) p = 0
    rw [eval_zero]
    by_contra hne
    change p.coeff 0 ≠ 0 at hne
    have hmem : (0 : σ →₀ ℕ) ∈ p.support := mem_support_iff.mpr hne
    have := hp 0 hmem
    simp at this

lemma maxIdealAt_zero_eq_idealOfVars {n : ℕ} :
    maxIdealAt (0 : Fin (n + 1) → K) = idealOfVars (Fin (n + 1)) K := by
  rw [maxIdealAt_eq_vanishingIdeal]
  exact vanishingIdeal_singleton_zero_eq_idealOfVars

noncomputable def supLeftPart {R : Type*} [CommRing R]
    (I J : Ideal R) (x : R) : R := by
  classical
  exact if hx : x ∈ I ⊔ J then Classical.choose (Submodule.mem_sup.mp hx) else 0

lemma supLeftPart_mem_left {R : Type*} [CommRing R]
    (I J : Ideal R) {x : R} (hx : x ∈ I ⊔ J) : supLeftPart I J x ∈ I := by
  rw [supLeftPart, dif_pos hx]
  exact (Classical.choose_spec (Submodule.mem_sup.mp hx)).1

lemma sub_supLeftPart_mem_right {R : Type*} [CommRing R]
    (I J : Ideal R) {x : R} (hx : x ∈ I ⊔ J) : x - supLeftPart I J x ∈ J := by
  simp only [supLeftPart, dif_pos hx]
  obtain ⟨hy, z, hz, hsum⟩ := Classical.choose_spec (Submodule.mem_sup.mp hx)
  have : x - Classical.choose (Submodule.mem_sup.mp hx) = z := by
    calc
      x - Classical.choose (Submodule.mem_sup.mp hx) =
          (Classical.choose (Submodule.mem_sup.mp hx) + z) -
            Classical.choose (Submodule.mem_sup.mp hx) :=
        congrArg (fun w => w - Classical.choose (Submodule.mem_sup.mp hx)) hsum.symm
      _ = z := by abel
  rwa [this]

lemma supLeftPart_smul_eq_on_quotSMulTop {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) {x r : R}
    (hx : x ∈ I ⊔ Ideal.span {r}) (m : QuotSMulTop r M) :
    x • m = supLeftPart I (Ideal.span {r}) x • m := by
  have hsub := sub_supLeftPart_mem_right I (Ideal.span {r}) hx
  have hspan : Ideal.span {r} ≤ Module.annihilator R (QuotSMulTop r M) := by
    rw [Ideal.span_le]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact QuotSMulTop.mem_annihilator M r
  have hzero : (x - supLeftPart I (Ideal.span {r}) x) • m = 0 :=
    Module.mem_annihilator.mp (hspan hsub) m
  simpa [sub_smul, sub_eq_zero] using hzero

noncomputable def removeSpanComponent {R : Type*} [CommRing R]
    (I : Ideal R) (r : R) (xs : List R) : List R :=
  xs.map (supLeftPart I (Ideal.span {r}))

lemma removeSpanComponent_length {R : Type*} [CommRing R]
    (I : Ideal R) (r : R) (xs : List R) :
    (removeSpanComponent I r xs).length = xs.length := by
  simp [removeSpanComponent]

lemma removeSpanComponent_mem {R : Type*} [CommRing R]
    (I : Ideal R) (r : R) (xs : List R)
    (hxs : ∀ x ∈ xs, x ∈ I ⊔ Ideal.span {r}) :
    ∀ x ∈ removeSpanComponent I r xs, x ∈ I := by
  intro x hx
  rw [removeSpanComponent, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact supLeftPart_mem_left I (Ideal.span {r}) (hxs y hy)

lemma removeSpanComponent_isRegular {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (r : R) (xs : List R)
    (hxs : ∀ x ∈ xs, x ∈ I ⊔ Ideal.span {r})
    (hreg : IsRegular (QuotSMulTop r M) xs) :
    IsRegular (QuotSMulTop r M) (removeSpanComponent I r xs) := by
  apply ((AddEquiv.refl (QuotSMulTop r M)).isRegular_congr ?_).mp hreg
  rw [removeSpanComponent, List.forall₂_map_right_iff]
  apply List.forall₂_same.mpr
  intro x hx m
  exact supLeftPart_smul_eq_on_quotSMulTop I (hxs x hx) m

noncomputable def homogeneousEquationIdeal {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  Ideal.span (Set.range f)

lemma homogeneousSlicePolynomialIdeal_eq_sup {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K)
    (a : Fin (n + 1) → K) :
    homogeneousSlicePolynomialIdeal f a =
      homogeneousEquationIdeal f ⊔ Ideal.span {linearForm a} := by
  rw [homogeneousSlicePolynomialIdeal, homogeneousEquationIdeal, Ideal.span_union]

lemma ideal_smul_top_lt_top_of_ne_top {R : Type*} [CommRing R]
    (I : Ideal R) (hI : I ≠ ⊤) :
    I • (⊤ : Submodule R R) < ⊤ := by
  rw [lt_top_iff_ne_top]
  simpa using hI

lemma exists_regular_equation_sequence_mod_linear [IsAlgClosed K] {n : ℕ}
    (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k)) (hdpos : ∀ k, 1 ≤ d k)
    (a : Fin (n + 1) → K)
    (hne : ∀ p ∈ ⋂ k, vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0)
    (hLne : linearForm a ≠ 0) :
    let R := MvPolynomial (Fin (n + 1)) K
    let L := linearForm a
    let I := homogeneousEquationIdeal f
    ∃ gs : List R, gs.length = n ∧ (∀ g ∈ gs, g ∈ I) ∧
      IsRegular (QuotSMulTop L R) gs := by
  let R := MvPolynomial (Fin (n + 1)) K
  let L := linearForm a
  let I := homogeneousEquationIdeal f
  let J := homogeneousSlicePolynomialIdeal f a
  let m := idealOfVars (Fin (n + 1)) K
  have hm_ne : m ≠ ⊤ := idealOfVars_ne_top (K := K) (n + 1)
  have hJrad : J.radical = m := by
    calc
      J.radical = maxIdealAt (0 : Fin (n + 1) → K) :=
        homogeneousSlicePolynomialIdeal_radical_eq_maxIdealAt_zero
          f d hd hdpos a hne
      _ = m := maxIdealAt_zero_eq_idealOfVars
  have hJ_ne : J ≠ ⊤ := by
    intro htop
    have : J.radical = ⊤ := by simp [htop]
    rw [hJrad] at this
    exact hm_ne this
  have hm_smul : m • (⊤ : Submodule R R) < ⊤ :=
    ideal_smul_top_lt_top_of_ne_top m hm_ne
  have hJ_smul : J • (⊤ : Submodule R R) < ⊤ :=
    ideal_smul_top_lt_top_of_ne_top J hJ_ne
  let coords := coordinateList (K := K) (n + 1)
  have hcoords_len : coords.length = n + 1 := coordinateList_length (K := K) _
  have hcoords_mem : ∀ x ∈ coords, x ∈ m := by
    intro x hx
    have hI := ideal_of_coordinateList (K := K) (n + 1)
    change x ∈ idealOfVars (Fin (n + 1)) K
    rw [← hI]
    change x ∈ Ideal.ofList coords
    exact Ideal.subset_span hx
  have hcoords_reg : IsRegular R coords := coordinateList_isRegular (K := K) _
  have hzero : PrimeSpectrum.zeroLocus (m : Set R) =
      PrimeSpectrum.zeroLocus (J : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_radical J, hJrad]
  obtain ⟨js, hjs_len, hjs_mem, hjs_reg⟩ :=
    Submission.Helpers.ModuleCat.exists_isRegular_of_zeroLocus_eq
      m J (n + 1) (ModuleCat.of R R) hm_smul hJ_smul hzero
      coords hcoords_len hcoords_mem hcoords_reg
  have hLmem : L ∈ J := by
    change linearForm a ∈ homogeneousSlicePolynomialIdeal f a
    rw [homogeneousSlicePolynomialIdeal]
    exact Ideal.subset_span (Set.mem_union_right _ (Set.mem_singleton _))
  have hLreg : IsSMulRegular R L := (IsRegular.of_ne_zero hLne).isSMulRegular
  obtain ⟨tail, htail_len, htail_mem, htail_reg⟩ :=
    Submission.Helpers.ModuleCat.exists_isRegular_tail_of_mem
      J n (ModuleCat.of R R) hJ_smul js hjs_len hjs_mem hjs_reg hLmem hLreg
  have hJ_eq : J = I ⊔ Ideal.span {L} :=
    homogeneousSlicePolynomialIdeal_eq_sup f a
  have htail_mem' : ∀ x ∈ tail, x ∈ I ⊔ Ideal.span {L} := by
    intro x hx
    rw [← hJ_eq]
    exact htail_mem x hx
  let gs := removeSpanComponent I L tail
  refine ⟨gs, ?_, ?_, ?_⟩
  · exact (removeSpanComponent_length I L tail).trans htail_len
  · exact removeSpanComponent_mem I L tail htail_mem'
  · exact removeSpanComponent_isRegular I L tail htail_mem' htail_reg

end Submission.Helpers
