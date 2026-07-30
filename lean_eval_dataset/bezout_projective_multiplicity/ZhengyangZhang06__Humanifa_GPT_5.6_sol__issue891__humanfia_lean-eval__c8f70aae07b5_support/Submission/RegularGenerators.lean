import Submission.CompleteIntersection
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open LeanEval.AlgebraicGeometry MvPolynomial RingTheory.Sequence
open scoped Pointwise

variable {K : Type*} [Field K]

universe v

namespace Submission.Helpers

noncomputable def familyIdeal {R ι : Type*} [CommRing R]
    (f : ι → R) (s : Finset ι) : Ideal R :=
  Ideal.span (f '' (s : Set ι))

lemma familyIdeal_generator {R ι : Type*} [CommRing R]
    (f : ι → R) (s : Finset ι) {i : ι} (hi : i ∈ s) :
    f i ∈ familyIdeal f s :=
  Ideal.subset_span ⟨i, hi, rfl⟩

lemma familyIdeal_mono {R ι : Type*} [CommRing R]
    (f : ι → R) {s t : Finset ι} (hst : s ⊆ t) :
    familyIdeal f s ≤ familyIdeal f t := by
  apply Ideal.span_mono
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, hst hi, rfl⟩

lemma homogeneous_mem_idealOfVars {σ : Type*}
    {p : MvPolynomial σ K} {e : ℕ} (hp : p.IsHomogeneous e) (he : 0 < e) :
    p ∈ idealOfVars σ K := by
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  intro a ha
  have hweight := hp (mem_support_iff.mp ha)
  rw [Finsupp.degree_eq_weight_one]
  change 1 ≤ Finsupp.weight (1 : σ → ℕ) a
  rw [hweight]
  exact he

lemma regular_not_mem_associatedPrime {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R]
    {r : R} (hr : IsSMulRegular M r) (P : associatedPrimes R M) :
    r ∉ P.1 := by
  intro hrP
  have hrUnion : r ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [Set.mem_iUnion]
    refine ⟨P.1, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨P.2, hrP⟩
  rw [biUnion_associatedPrimes_eq_compl_regular R M] at hrUnion
  exact hrUnion hr

lemma exists_homogeneous_regular_pivot [Infinite K]
    {σ ι M : Type*} [Finite σ] [Nonempty σ] [DecidableEq ι]
    [AddCommGroup M] [Module (MvPolynomial σ K) M]
    [Module.Finite (MvPolynomial σ K) M]
    (f : ι → MvPolynomial σ K) (d : ι → ℕ)
    (hd : ∀ i, (f i).IsHomogeneous (d i)) (hdpos : ∀ i, 0 < d i)
    (s : Finset ι) (hs : s.Nonempty) (t : ι) (ht : t ∈ s)
    (htmax : ∀ i ∈ s, d i ≤ d t)
    (rs : List (MvPolynomial σ K)) (hlen : rs.length = s.card)
    (hmem : ∀ r ∈ rs, r ∈ familyIdeal f s) (hreg : IsRegular M rs) :
    ∃ g : MvPolynomial σ K,
      g.IsHomogeneous (d t) ∧ g ∈ familyIdeal f s ∧ IsSMulRegular M g ∧
        familyIdeal f s = familyIdeal f (s.erase t) ⊔ Ideal.span {g} := by
  let R := MvPolynomial σ K
  have hrsne : rs ≠ [] := by
    intro hrs
    rw [hrs, List.length_nil] at hlen
    exact hs.ne_empty (Finset.card_eq_zero.mp hlen.symm)
  obtain ⟨r, rs', rfl⟩ := List.exists_cons_of_ne_nil hrsne
  have hrreg : IsSMulRegular M r :=
    (isRegular_cons_iff M r rs').mp hreg |>.1
  have hrmem : r ∈ familyIdeal f s := hmem r (by simp)
  have hJnotle (P : associatedPrimes R M) : ¬ familyIdeal f s ≤ P.1 := by
    intro hle
    exact regular_not_mem_associatedPrime hrreg P (hle hrmem)
  let W := homogeneousSubmodule σ K 1
  let badLinear (P : associatedPrimes R M) : Submodule K W :=
    (P.1.restrictScalars K).comap W.subtype
  have hbadLinear (P : associatedPrimes R M) : badLinear P ≠ ⊤ := by
    intro htop
    have hX (i : σ) : X i ∈ P.1 := by
      have hx : (⟨X i, isHomogeneous_X K i⟩ : W) ∈ badLinear P := by
        rw [htop]
        exact Submodule.mem_top
      exact hx
    have hmle : idealOfVars σ K ≤ P.1 := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hX i
    apply hJnotle P
    rw [familyIdeal, Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hmle (homogeneous_mem_idealOfVars (hd i) (hdpos i))
  letI : Fintype (associatedPrimes R M) :=
    (associatedPrimes.finite R M).fintype
  obtain ⟨ell, hell⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top badLinear hbadLinear
  have hellhom : (ell : R).IsHomogeneous 1 := ell.2
  have hellP (P : associatedPrimes R M) : (ell : R) ∉ P.1 := hell P
  let v : s → R := fun i ↦ (ell : R) ^ (d t - d i.1) * f i.1
  let comb : (s →₀ K) →ₗ[K] R := Finsupp.linearCombination K v
  have hcombProper (P : associatedPrimes R M) :
      (P.1.restrictScalars K).comap comb ≠ ⊤ := by
    obtain ⟨i, hi, hfi⟩ : ∃ i ∈ s, f i ∉ P.1 := by
      by_contra h
      push Not at h
      apply hJnotle P
      rw [familyIdeal, Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact h i hi
    let ii : s := ⟨i, hi⟩
    have hvnot : v ii ∉ P.1 := by
      intro hv
      rcases P.2.1.mul_mem_iff_mem_or_mem.mp hv with hp | hp
      · exact hellP P (P.2.1.mem_of_pow_mem _ hp)
      · exact hfi hp
    intro htop
    have hsingle : Finsupp.single ii (1 : K) ∈
        (P.1.restrictScalars K).comap comb := by
      rw [htop]
      exact Submodule.mem_top
    apply hvnot
    simpa [comb] using hsingle
  let tt : s := ⟨t, ht⟩
  let bad : Option (associatedPrimes R M) → Submodule K (s →₀ K)
    | none => LinearMap.ker (Finsupp.lapply tt)
    | some P => (P.1.restrictScalars K).comap comb
  have hbad (i : Option (associatedPrimes R M)) : bad i ≠ ⊤ := by
    cases i with
    | none =>
        intro htop
        have hsingle : Finsupp.single tt (1 : K) ∈ bad none := by
          rw [htop]
          exact Submodule.mem_top
        change (Finsupp.lapply tt : (s →₀ K) →ₗ[K] K)
          (Finsupp.single tt 1) = 0 at hsingle
        simp at hsingle
    | some P => exact hcombProper P
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  have hct : c tt ≠ 0 := by
    intro hzero
    apply hc none
    change (Finsupp.lapply tt : (s →₀ K) →ₗ[K] K) c = 0
    simp [hzero]
  let g : R := comb c
  have hghom : g.IsHomogeneous (d t) := by
    change (Finsupp.linearCombination K v c).IsHomogeneous (d t)
    rw [Finsupp.linearCombination_apply]
    apply IsHomogeneous.sum
    intro i hi
    change (c i) • v i |>.IsHomogeneous (d t)
    rw [smul_eq_C_mul]
    apply IsHomogeneous.C_mul
    convert (hellhom.pow (d t - d i.1)).mul (hd i.1) using 1
    simpa only [one_mul] using (Nat.sub_add_cancel (htmax i.1 i.2)).symm
  have hgmem : g ∈ familyIdeal f s := by
    change Finsupp.linearCombination K v c ∈ familyIdeal f s
    rw [Finsupp.linearCombination_apply]
    apply Submodule.sum_mem
    intro i hi
    change (c i) • v i ∈ familyIdeal f s
    rw [smul_eq_C_mul]
    exact Ideal.mul_mem_left _ _
      (Ideal.mul_mem_left _ _ (familyIdeal_generator f s i.2))
  have hgreg : IsSMulRegular M g := by
    by_contra hnreg
    have hgunion : g ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
      rw [biUnion_associatedPrimes_eq_compl_regular R M]
      exact hnreg
    rw [Set.mem_iUnion] at hgunion
    obtain ⟨P, hgunion⟩ := hgunion
    rw [Set.mem_iUnion] at hgunion
    obtain ⟨hP, hgP⟩ := hgunion
    let PP : associatedPrimes R M := ⟨P, hP⟩
    apply hc (some PP)
    exact hgP
  have hdiff : g - C (c tt) * f t ∈ familyIdeal f (s.erase t) := by
    let c' := c - Finsupp.single tt (c tt)
    have hc't : c' tt = 0 := by simp [c']
    have hc'mem : comb c' ∈ familyIdeal f (s.erase t) := by
      change Finsupp.linearCombination K v c' ∈ familyIdeal f (s.erase t)
      rw [Finsupp.linearCombination_apply]
      apply Submodule.sum_mem
      intro i hi
      have hit : i.1 ≠ t := by
        intro hit
        have : i = tt := Subtype.ext hit
        subst i
        exact (Finsupp.mem_support_iff.mp hi) hc't
      change (c' i) • v i ∈ familyIdeal f (s.erase t)
      rw [smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
        (familyIdeal_generator f (s.erase t) (Finset.mem_erase.mpr ⟨hit, i.2⟩)))
    have hcomb : comb c' = g - C (c tt) * f t := by
      dsimp [c', g, comb]
      rw [map_sub, Finsupp.linearCombination_single]
      change _ - (c tt) • ((ell : R) ^ (d t - d t) * f t) =
        _ - C (c tt) * f t
      rw [Nat.sub_self, pow_zero, one_mul, smul_eq_C_mul]
    rwa [hcomb] at hc'mem
  have hIdeal : familyIdeal f s = familyIdeal f (s.erase t) ⊔ Ideal.span {g} := by
    apply le_antisymm
    · rw [familyIdeal, Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      by_cases hit : i = t
      · subst i
        let H := familyIdeal f (s.erase t) ⊔ Ideal.span {g}
        have hgH : g ∈ H :=
          (show Ideal.span {g} ≤ H from le_sup_right)
            (Ideal.subset_span (Set.mem_singleton g))
        have hdiffH : g - C (c tt) * f t ∈ H :=
          (show familyIdeal f (s.erase t) ≤ H from le_sup_left) hdiff
        have hscaled : C (c tt) * f t ∈ H := by
          convert H.sub_mem hgH hdiffH using 1
          ring
        have hinv : C ((c tt)⁻¹) * (C (c tt) * f t) ∈ H :=
          H.mul_mem_left _ hscaled
        simpa [← C_mul, hct] using hinv
      · exact (show familyIdeal f (s.erase t) ≤
            familyIdeal f (s.erase t) ⊔ Ideal.span {g} from le_sup_left)
          (familyIdeal_generator f (s.erase t) (Finset.mem_erase.mpr ⟨hit, hi⟩))
    · apply sup_le
      · exact familyIdeal_mono f (Finset.erase_subset t s)
      · rw [Ideal.span_le]
        rintro _ (rfl : _ = g)
        exact hgmem
  exact ⟨g, hghom, hgmem, hgreg, hIdeal⟩

set_option maxHeartbeats 800000 in
lemma exists_homogeneous_regular_generators_list [Infinite K]
    {σ ι : Type*} {M : Type v} [Finite σ] [Nonempty σ] [DecidableEq ι]
    [AddCommGroup M] [Module (MvPolynomial σ K) M]
    [Module.Finite (MvPolynomial σ K) M]
    [Small.{v} (MvPolynomial σ K)]
    (f : ι → MvPolynomial σ K) (d : ι → ℕ)
    (hd : ∀ i, (f i).IsHomogeneous (d i)) (hdpos : ∀ i, 0 < d i)
    (is : List ι) (his : is.Nodup)
    (hsorted : is.Pairwise fun i j ↦ d j ≤ d i)
    (rs : List (MvPolynomial σ K)) (hlen : rs.length = is.length)
    (hmem : ∀ r ∈ rs, r ∈ familyIdeal f is.toFinset)
    (hreg : IsRegular M rs)
    (hproper : familyIdeal f is.toFinset •
      (⊤ : Submodule (MvPolynomial σ K) M) < ⊤) :
    ∃ gs : List (MvPolynomial σ K),
      List.Forall₂ (fun i g ↦ g.IsHomogeneous (d i)) is gs ∧
        Ideal.ofList gs = familyIdeal f is.toFinset ∧ IsRegular M gs := by
  induction is generalizing M rs with
  | nil =>
      have hrs : rs = [] := List.eq_nil_of_length_eq_zero hlen
      subst rs
      exact ⟨[], .nil, by simp [familyIdeal], hreg⟩
  | cons t ts ih =>
      have ht : t ∈ (t :: ts).toFinset := by simp
      have hsne : (t :: ts).toFinset.Nonempty := ⟨t, ht⟩
      have hmax : ∀ i ∈ (t :: ts).toFinset, d i ≤ d t := by
        intro i hi
        rw [List.mem_toFinset] at hi
        simp only [List.mem_cons] at hi
        rcases hi with hi | hi
        · subst i
          exact le_rfl
        · exact (List.pairwise_cons.mp hsorted).1 i hi
      obtain ⟨g, hghom, hgmem, hgreg, hIdeal⟩ :=
        exists_homogeneous_regular_pivot f d hd hdpos (t :: ts).toFinset hsne
          t ht hmax rs (hlen.trans (List.toFinset_card_of_nodup his).symm) hmem hreg
      have ht_not : t ∉ ts := (List.nodup_cons.mp his).1
      have herase : (t :: ts).toFinset.erase t = ts.toFinset := by
        simp [ht_not]
      rw [herase] at hIdeal
      obtain ⟨tail, htail_len, htail_mem, htail_reg⟩ :=
        Submission.Helpers.ModuleCat.exists_isRegular_tail_of_mem
          (familyIdeal f (t :: ts).toFinset) ts.length
          (ModuleCat.of (MvPolynomial σ K) M) hproper rs (by simpa using hlen)
          hmem hreg hgmem hgreg
      have htail_mem' : ∀ x ∈ tail,
          x ∈ familyIdeal f ts.toFinset ⊔ Ideal.span {g} := by
        intro x hx
        rw [← hIdeal]
        exact htail_mem x hx
      let tail' := removeSpanComponent (familyIdeal f ts.toFinset) g tail
      have htail'_len : tail'.length = ts.length :=
        (removeSpanComponent_length (familyIdeal f ts.toFinset) g tail).trans htail_len
      have htail'_mem : ∀ x ∈ tail', x ∈ familyIdeal f ts.toFinset :=
        removeSpanComponent_mem (familyIdeal f ts.toFinset) g tail htail_mem'
      have htail'_reg : IsRegular (QuotSMulTop g M) tail' :=
        removeSpanComponent_isRegular (familyIdeal f ts.toFinset) g tail
          htail_mem' htail_reg
      have hrest_le : familyIdeal f ts.toFinset ≤
          familyIdeal f (t :: ts).toFinset := by
        apply familyIdeal_mono
        intro i hi
        simpa using List.mem_cons_of_mem t (List.mem_toFinset.mp hi)
      have hfull_ne : familyIdeal f (t :: ts).toFinset •
          (⊤ : Submodule (MvPolynomial σ K) (QuotSMulTop g M)) ≠ ⊤ :=
        smul_top_quotSMulTop_ne_top_of_smul_top_ne_top hgmem hproper.ne
      have hrest_ne : familyIdeal f ts.toFinset •
          (⊤ : Submodule (MvPolynomial σ K) (QuotSMulTop g M)) ≠ ⊤ := by
        intro htop
        apply hfull_ne
        apply top_unique
        have hmono : familyIdeal f ts.toFinset •
            (⊤ : Submodule (MvPolynomial σ K) (QuotSMulTop g M)) ≤
            familyIdeal f (t :: ts).toFinset • ⊤ :=
          Submodule.smul_mono_left hrest_le
        rw [htop] at hmono
        exact hmono
      obtain ⟨gs, hgs_hom, hgs_ideal, hgs_reg⟩ :=
        ih (M := QuotSMulTop g M) (List.nodup_cons.mp his).2
          (List.pairwise_cons.mp hsorted).2 tail' htail'_len htail'_mem
          htail'_reg hrest_ne.lt_top
      have hgs_hom' : List.Forall₂ (fun i q ↦ q.IsHomogeneous (d i))
          (t :: ts) (g :: gs) := .cons hghom hgs_hom
      have hgs_reg' : IsRegular M (g :: gs) := IsRegular.cons hgreg hgs_reg
      refine ⟨g :: gs, hgs_hom', ?_, hgs_reg'⟩
      rw [Ideal.ofList_cons, hgs_ideal, sup_comm, ← hIdeal]

lemma exists_homogeneous_regular_generators [Infinite K]
    {σ ι : Type*} {M : Type v} [Finite σ] [Nonempty σ] [Fintype ι]
    [DecidableEq ι]
    [AddCommGroup M] [Module (MvPolynomial σ K) M]
    [Module.Finite (MvPolynomial σ K) M]
    [Small.{v} (MvPolynomial σ K)]
    (f : ι → MvPolynomial σ K) (d : ι → ℕ)
    (hd : ∀ i, (f i).IsHomogeneous (d i)) (hdpos : ∀ i, 0 < d i)
    (rs : List (MvPolynomial σ K)) (hlen : rs.length = Fintype.card ι)
    (hmem : ∀ r ∈ rs, r ∈ Ideal.span (Set.range f))
    (hreg : IsRegular M rs)
    (hproper : Ideal.span (Set.range f) •
      (⊤ : Submodule (MvPolynomial σ K) M) < ⊤) :
    ∃ order : List ι, ∃ gs : List (MvPolynomial σ K),
      order.Nodup ∧ order.toFinset = Finset.univ ∧
        List.Forall₂ (fun i g ↦ g.IsHomogeneous (d i)) order gs ∧
        Ideal.ofList gs = Ideal.span (Set.range f) ∧ IsRegular M gs := by
  classical
  let rel : ι → ι → Prop := fun i j ↦ d j ≤ d i
  let order := (Finset.univ : Finset ι).toList.insertionSort rel
  have hperm : order.Perm (Finset.univ : Finset ι).toList := by
    exact List.perm_insertionSort rel _
  have horder_nodup : order.Nodup :=
    hperm.nodup_iff.mpr (Finset.univ : Finset ι).nodup_toList
  have horder_finset : order.toFinset = Finset.univ := by
    calc
      order.toFinset = (Finset.univ : Finset ι).toList.toFinset :=
        List.toFinset_eq_of_perm _ _ hperm
      _ = Finset.univ := by simp
  have horder_sorted : order.Pairwise fun i j ↦ d j ≤ d i :=
    List.pairwise_insertionSort rel _
  have hfamily : familyIdeal f order.toFinset = Ideal.span (Set.range f) := by
    rw [horder_finset, familyIdeal]
    congr 1
    ext x
    simp
  have horder_len : order.length = Fintype.card ι := by
    simpa using hperm.length_eq
  obtain ⟨gs, hhom, hideal, hgsreg⟩ :=
    exists_homogeneous_regular_generators_list f d hd hdpos order horder_nodup
      horder_sorted rs (hlen.trans horder_len.symm) (by simpa [hfamily] using hmem)
      hreg (by simpa [hfamily] using hproper)
  exact ⟨order, gs, horder_nodup, horder_finset, hhom,
    by simpa [hfamily] using hideal, hgsreg⟩

lemma exists_homogeneous_regular_equation_generators_mod_linear [IsAlgClosed K]
    {n : ℕ} (f : Fin n → MvPolynomial (Fin (n + 1)) K) (d : Fin n → ℕ)
    (hd : ∀ k, (f k).IsHomogeneous (d k)) (hdpos : ∀ k, 0 < d k)
    (a : Fin (n + 1) → K)
    (hne : ∀ p ∈ ⋂ k, LeanEval.AlgebraicGeometry.vanishingSet (f k),
      eval (Projectivization.rep p) (linearForm a) ≠ 0)
    (hLne : linearForm a ≠ 0) :
    let R := MvPolynomial (Fin (n + 1)) K
    let L := linearForm a
    ∃ order : List (Fin n), ∃ gs : List R,
      order.Nodup ∧ order.toFinset = Finset.univ ∧
        List.Forall₂ (fun i g ↦ g.IsHomogeneous (d i)) order gs ∧
        Ideal.ofList gs = homogeneousEquationIdeal f ∧
        IsRegular (QuotSMulTop L R) gs := by
  let R := MvPolynomial (Fin (n + 1)) K
  let L := linearForm a
  let I := homogeneousEquationIdeal f
  let J := homogeneousSlicePolynomialIdeal f a
  obtain ⟨rs, hrs_len, hrs_mem, hrs_reg⟩ :=
    exists_regular_equation_sequence_mod_linear f d hd hdpos a hne hLne
  have hm_ne : (idealOfVars (Fin (n + 1)) K : Ideal R) ≠ ⊤ :=
    idealOfVars_ne_top (K := K) (n + 1)
  have hJrad : J.radical = idealOfVars (Fin (n + 1)) K := by
    calc
      J.radical = maxIdealAt (0 : Fin (n + 1) → K) :=
        homogeneousSlicePolynomialIdeal_radical_eq_maxIdealAt_zero
          f d hd hdpos a hne
      _ = idealOfVars (Fin (n + 1)) K := maxIdealAt_zero_eq_idealOfVars
  have hJ_ne : J ≠ ⊤ := by
    intro htop
    have : J.radical = ⊤ := by simp [htop]
    rw [hJrad] at this
    exact hm_ne this
  have hJproper : J • (⊤ : Submodule R R) < ⊤ :=
    ideal_smul_top_lt_top_of_ne_top J hJ_ne
  have hLmem : L ∈ J := by
    change linearForm a ∈ homogeneousSlicePolynomialIdeal f a
    rw [homogeneousSlicePolynomialIdeal]
    exact Ideal.subset_span (Set.mem_union_right _ (Set.mem_singleton _))
  have hJquot_ne : J • (⊤ : Submodule R (QuotSMulTop L R)) ≠ ⊤ :=
    smul_top_quotSMulTop_ne_top_of_smul_top_ne_top hLmem hJproper.ne
  have hIJ : I ≤ J := by
    change homogeneousEquationIdeal f ≤ homogeneousSlicePolynomialIdeal f a
    rw [homogeneousSlicePolynomialIdeal_eq_sup f a]
    exact le_sup_left
  have hIquot_ne : I • (⊤ : Submodule R (QuotSMulTop L R)) ≠ ⊤ := by
    intro htop
    apply hJquot_ne
    apply top_unique
    have hmono : I • (⊤ : Submodule R (QuotSMulTop L R)) ≤ J • ⊤ :=
      Submodule.smul_mono_left hIJ
    rw [htop] at hmono
    exact hmono
  have hrs_mem' : ∀ g ∈ rs, g ∈ Ideal.span (Set.range f) := by
    simpa only [homogeneousEquationIdeal] using hrs_mem
  have hIproper' : Ideal.span (Set.range f) •
      (⊤ : Submodule R (QuotSMulTop L R)) < ⊤ := by
    simpa only [I, homogeneousEquationIdeal] using hIquot_ne.lt_top
  obtain ⟨order, gs, hord, huniv, hhom, hideal, hgsreg⟩ :=
    exists_homogeneous_regular_generators
      (M := QuotSMulTop L R) f d hd hdpos rs (by simpa using hrs_len)
      hrs_mem' hrs_reg hIproper'
  exact ⟨order, gs, hord, huniv, hhom,
    by simpa only [homogeneousEquationIdeal] using hideal, hgsreg⟩

end Submission.Helpers
