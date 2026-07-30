import Submission.FirstOrder

namespace Submission.HigherOrder

open LeanEval.Analysis.SobolevMorreyProblem
open MeasureTheory
open ContinuousLinearMap Filter
open scoped ENNReal NNReal Topology

theorem contDiff_partialDeriv {n : ℕ} {φ : E n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (partialDeriv i φ) := by
  unfold partialDeriv
  exact (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_partialDeriv {n : ℕ} {φ : E n → ℝ}
    (hφ : HasCompactSupport φ) (i : Fin n) :
    HasCompactSupport (partialDeriv i φ) := by
  unfold partialDeriv
  exact hφ.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))

theorem contDiff_iterate_partialDeriv {n : ℕ} {φ : E n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin n) (a : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) ((partialDeriv i)^[a] φ) := by
  induction a with
  | zero => simpa
  | succ a ih =>
      rw [Function.iterate_succ_apply']
      exact contDiff_partialDeriv ih i

theorem hasCompactSupport_iterate_partialDeriv {n : ℕ} {φ : E n → ℝ}
    (hφ : HasCompactSupport φ) (i : Fin n) (a : ℕ) :
    HasCompactSupport ((partialDeriv i)^[a] φ) := by
  induction a with
  | zero => simpa
  | succ a ih =>
      rw [Function.iterate_succ_apply']
      exact hasCompactSupport_partialDeriv ih i

theorem partialDeriv_comm {n : ℕ} {φ : E n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i j : Fin n) :
    partialDeriv i (partialDeriv j φ) =
      partialDeriv j (partialDeriv i φ) := by
  funext x
  let ei : E n := EuclideanSpace.single i (1 : ℝ)
  let ej : E n := EuclideanSpace.single j (1 : ℝ)
  have hfd :
      DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := (1 : ℕ∞)) (by
      exact_mod_cast (show (1 : ℕ∞) + 1 ≤ ⊤ from le_top))).differentiable
      (by norm_num) x
  have hconst_i : DifferentiableAt ℝ (fun _ : E n ↦ ei) x :=
    differentiableAt_const ei
  have hconst_j : DifferentiableAt ℝ (fun _ : E n ↦ ej) x :=
    differentiableAt_const ej
  have hi :
      fderiv ℝ (fun y ↦ fderiv ℝ φ y ej) x ei =
        fderiv ℝ (fderiv ℝ φ) x ei ej := by
    rw [fderiv_clm_apply hfd hconst_j]
    simp
  have hj :
      fderiv ℝ (fun y ↦ fderiv ℝ φ y ei) x ej =
        fderiv ℝ (fderiv ℝ φ) x ej ei := by
    rw [fderiv_clm_apply hfd hconst_i]
    simp
  unfold partialDeriv
  rw [hi, hj]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)).eq ei ej

theorem iterate_partialDeriv_comm {n : ℕ} {φ : E n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i j : Fin n) (a : ℕ) :
    (partialDeriv j)^[a] (partialDeriv i φ) =
      partialDeriv i ((partialDeriv j)^[a] φ) := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact partialDeriv_comm (contDiff_iterate_partialDeriv hφ j a) j i

private theorem foldr_contDiff {n : ℕ} (m : Fin n → ℕ)
    (l : List (Fin n)) {φ : E n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (l.foldr (fun i ψ ↦ (partialDeriv i)^[m i] ψ) φ) := by
  induction l with
  | nil => simpa
  | cons a l ih =>
      rw [List.foldr_cons]
      exact contDiff_iterate_partialDeriv ih a (m a)

private theorem foldr_hasCompactSupport {n : ℕ} (m : Fin n → ℕ)
    (l : List (Fin n)) {φ : E n → ℝ}
    (hφ : HasCompactSupport φ) :
    HasCompactSupport
      (l.foldr (fun i ψ ↦ (partialDeriv i)^[m i] ψ) φ) := by
  induction l with
  | nil => simpa
  | cons a l ih =>
      rw [List.foldr_cons]
      exact hasCompactSupport_iterate_partialDeriv ih a (m a)

private theorem foldr_partialDeriv_comm {n : ℕ} (m : Fin n → ℕ)
    (i : Fin n) (l : List (Fin n)) (hi : i ∉ l)
    {φ : E n → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    l.foldr (fun j ψ ↦ (partialDeriv j)^[m j] ψ) (partialDeriv i φ) =
      partialDeriv i
        (l.foldr (fun j ψ ↦ (partialDeriv j)^[m j] ψ) φ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hil : i ∉ l := by
        intro h
        exact hi (by simp [h])
      rw [List.foldr_cons, List.foldr_cons, ih hil]
      exact iterate_partialDeriv_comm (foldr_contDiff m l hφ) i a (m a)

private theorem foldr_add_coordMulti {n : ℕ} (m : Fin n → ℕ)
    (i : Fin n) (l : List (Fin n)) (hl : l.Nodup)
    {φ : E n → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    l.foldr
        (fun j ψ ↦ (partialDeriv j)^[(m + Helpers.coordMulti i) j] ψ) φ =
      if i ∈ l then
        l.foldr (fun j ψ ↦ (partialDeriv j)^[m j] ψ) (partialDeriv i φ)
      else
        l.foldr (fun j ψ ↦ (partialDeriv j)^[m j] ψ) φ := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have htail := hl.tail
      rw [List.foldr_cons, ih htail, List.foldr_cons]
      by_cases hai : a = i
      · subst a
        have hil : i ∉ l := (List.nodup_cons.mp hl).1
        rw [if_neg hil]
        rw [foldr_partialDeriv_comm m i l hil hφ]
        simp only [Helpers.coordMulti, Pi.add_apply, if_pos]
        rw [Function.iterate_succ_apply]
        simp only [List.mem_cons, true_or, if_true]
      · have hia : i ≠ a := Ne.symm hai
        simp only [Helpers.coordMulti, Pi.add_apply, if_neg hai, add_zero]
        by_cases hil : i ∈ l
        · simp only [hil, if_true, List.mem_cons, hia, false_or]
        · simp only [hil, if_false, List.mem_cons, hia, false_or,
            List.foldr_cons]

theorem mixedDeriv_add_coordMulti {n : ℕ} (m : Fin n → ℕ)
    (i : Fin n) {φ : E n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    mixedDeriv (m + Helpers.coordMulti i) φ =
      mixedDeriv m (partialDeriv i φ) := by
  unfold mixedDeriv
  rw [foldr_add_coordMulti m i (List.finRange n) (List.nodup_finRange n) hφ]
  simp

theorem mixedDeriv_contDiff {n : ℕ} (m : Fin n → ℕ)
    {φ : E n → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (mixedDeriv m φ) := by
  exact foldr_contDiff m (List.finRange n) hφ

theorem mixedDeriv_hasCompactSupport {n : ℕ} (m : Fin n → ℕ)
    {φ : E n → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (mixedDeriv m φ) := by
  exact foldr_hasCompactSupport m (List.finRange n) hφ

theorem sum_add_coordMulti {n : ℕ} (m : Fin n → ℕ) (i : Fin n) :
    ∑ j, (m + Helpers.coordMulti i) j = (∑ j, m j) + 1 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, Helpers.sum_coordMulti]

theorem derivRep_isWeakDeriv_coord {n k : ℕ} {p : ℝ≥0∞}
    {f : E n → ℝ} (hf : MemSobolevWk k p f)
    (m : Fin n → ℕ) (i : Fin n)
    (hm : (∑ j, m j) + 1 ≤ k) :
    IsWeakDeriv
      (Helpers.MemSobolevWk.derivRep hf m (by omega))
      (Helpers.MemSobolevWk.derivRep hf (m + Helpers.coordMulti i)
        (by simpa only [sum_add_coordMulti] using hm))
      (Helpers.coordMulti i) := by
  let hm0 : (∑ j, m j) ≤ k :=
    by omega
  let hmi : (∑ j, (m + Helpers.coordMulti i) j) ≤ k := by
    simpa only [sum_add_coordMulti] using hm
  let u :=
    Helpers.MemSobolevWk.derivRep hf m hm0
  let ui :=
    Helpers.MemSobolevWk.derivRep hf (m + Helpers.coordMulti i) hmi
  have hweakm :
      IsWeakDeriv f u m :=
    Helpers.MemSobolevWk.isWeakDeriv_derivRep hf m hm0
  have hweakmi :
      IsWeakDeriv f ui (m + Helpers.coordMulti i) :=
    Helpers.MemSobolevWk.isWeakDeriv_derivRep hf
      (m + Helpers.coordMulti i) hmi
  change IsWeakDeriv u ui (Helpers.coordMulti i)
  intro φ hφ hφc
  have h1 :=
    hweakm (partialDeriv i φ)
      (contDiff_partialDeriv hφ i)
      (hasCompactSupport_partialDeriv hφc i)
  rw [← mixedDeriv_add_coordMulti m i hφ] at h1
  have h2 := hweakmi φ hφ hφc
  have heq :
      (-1 : ℝ) ^ (∑ j, m j) *
          ∫ x, u x * partialDeriv i φ x =
        (-1 : ℝ) ^ ((∑ j, m j) + 1) *
          ∫ x, ui x * φ x :=
    h1.symm.trans (by
      simpa only [sum_add_coordMulti] using h2)
  have hsign : (-1 : ℝ) ^ (∑ j, m j) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hcancel :
      (-1 : ℝ) ^ (∑ j, m j) *
          ∫ x, u x * partialDeriv i φ x =
        (-1 : ℝ) ^ (∑ j, m j) *
          (-∫ x, ui x * φ x) := by
    calc
      (-1 : ℝ) ^ (∑ j, m j) *
          ∫ x, u x * partialDeriv i φ x =
          (-1 : ℝ) ^ ((∑ j, m j) + 1) *
            ∫ x, ui x * φ x := heq
      _ = (-1 : ℝ) ^ (∑ j, m j) *
          (-∫ x, ui x * φ x) := by
        rw [pow_succ]
        ring
  have hresult :
      ∫ x, u x * partialDeriv i φ x =
        -∫ x, ui x * φ x :=
    mul_left_cancel₀ hsign hcancel
  simpa only [Helpers.mixedDeriv_coordMulti, Helpers.sum_coordMulti,
    pow_one, neg_one_mul] using hresult

noncomputable def rawDerivRep {n k : ℕ} {p : ℝ≥0∞}
    {f : E n → ℝ} (hf : MemSobolevWk k p f)
    (m : Fin n → ℕ) : E n → ℝ :=
  if hm : (∑ i, m i) ≤ k then
    Helpers.MemSobolevWk.derivRep hf m hm
  else
    0

theorem rawDerivRep_eq {n k : ℕ} {p : ℝ≥0∞}
    {f : E n → ℝ} (hf : MemSobolevWk k p f)
    (m : Fin n → ℕ) (hm : (∑ i, m i) ≤ k) :
    rawDerivRep hf m = Helpers.MemSobolevWk.derivRep hf m hm := by
  simp only [rawDerivRep, dif_pos hm]

theorem rawDerivRep_isWeakDeriv {n k : ℕ} {p : ℝ≥0∞}
    {f : E n → ℝ} (hf : MemSobolevWk k p f)
    (m : Fin n → ℕ) (hm : (∑ i, m i) ≤ k) :
    IsWeakDeriv f (rawDerivRep hf m) m := by
  rw [rawDerivRep_eq hf m hm]
  exact Helpers.MemSobolevWk.isWeakDeriv_derivRep hf m hm

theorem rawDerivRep_memLp {n k : ℕ} {p : ℝ≥0∞}
    {f : E n → ℝ} (hf : MemSobolevWk k p f)
    (m : Fin n → ℕ) (hm : (∑ i, m i) ≤ k) :
    MemLp (rawDerivRep hf m) p volume := by
  rw [rawDerivRep_eq hf m hm]
  exact Helpers.MemSobolevWk.memLp_derivRep hf m hm

theorem rawDerivRep_isWeakDeriv_coord {n k : ℕ} {p : ℝ≥0∞}
    {f : E n → ℝ} (hf : MemSobolevWk k p f)
    (m : Fin n → ℕ) (i : Fin n)
    (hm : (∑ j, m j) + 1 ≤ k) :
    IsWeakDeriv (rawDerivRep hf m)
      (rawDerivRep hf (m + Helpers.coordMulti i))
      (Helpers.coordMulti i) := by
  rw [rawDerivRep_eq hf m (by omega),
    rawDerivRep_eq hf (m + Helpers.coordMulti i)
      (by simpa only [sum_add_coordMulti] using hm)]
  exact derivRep_isWeakDeriv_coord hf m i hm

noncomputable def regularRep {n k : ℕ} {p : ℝ≥0∞}
    {f : E n → ℝ} (hf : MemSobolevWk k p f)
    (m : Fin n → ℕ) : E n → ℝ :=
  Submission.FirstOrder.PK.morreyRep n (rawDerivRep hf m)

theorem regularRep_ae_eq {n k : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (hm : (∑ j, m j) + 1 ≤ k) :
    rawDerivRep hf m =ᵐ[volume] regularRep hf m := by
  let u := rawDerivRep hf m
  let du : Fin n → E n → ℝ :=
    fun i ↦ rawDerivRep hf (m + Helpers.coordMulti i)
  have hpENN : 1 ≤ ENNReal.ofReal p :=
    Helpers.one_le_ofReal_of_dim_pos hn hp
  have huLp : MemLp u (ENNReal.ofReal p) volume :=
    rawDerivRep_memLp hf m (by omega)
  have hu : LocallyIntegrable u volume :=
    huLp.locallyIntegrable hpENN
  have hweak : ∀ i, IsWeakDeriv u (du i) (Helpers.coordMulti i) :=
    fun i ↦ rawDerivRep_isWeakDeriv_coord hf m i hm
  have hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) volume :=
    fun i ↦ rawDerivRep_memLp hf (m + Helpers.coordMulti i)
      (by simpa only [sum_add_coordMulti] using hm)
  exact Submission.FirstOrder.PK.ae_eq_morreyRep
    hn hp hu hweak hdu

theorem regularRep_continuous {n k : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (hm : (∑ j, m j) + 1 ≤ k) :
    Continuous (regularRep hf m) := by
  let u := rawDerivRep hf m
  let du : Fin n → E n → ℝ :=
    fun i ↦ rawDerivRep hf (m + Helpers.coordMulti i)
  have hpENN : 1 ≤ ENNReal.ofReal p :=
    Helpers.one_le_ofReal_of_dim_pos hn hp
  have huLp : MemLp u (ENNReal.ofReal p) volume :=
    rawDerivRep_memLp hf m (by omega)
  have hu : LocallyIntegrable u volume :=
    huLp.locallyIntegrable hpENN
  exact Submission.FirstOrder.PK.morreyRep_continuous hn hp hu
    (fun i ↦ rawDerivRep_isWeakDeriv_coord hf m i hm)
    (fun i ↦ rawDerivRep_memLp hf (m + Helpers.coordMulti i)
      (by simpa only [sum_add_coordMulti] using hm))

theorem regularRep_bounded {n k : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (hm : (∑ j, m j) + 1 ≤ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖regularRep hf m x‖ ≤ M := by
  let u := rawDerivRep hf m
  let du : Fin n → E n → ℝ :=
    fun i ↦ rawDerivRep hf (m + Helpers.coordMulti i)
  have hpENN : 1 ≤ ENNReal.ofReal p :=
    Helpers.one_le_ofReal_of_dim_pos hn hp
  have huLp : MemLp u (ENNReal.ofReal p) volume :=
    rawDerivRep_memLp hf m (by omega)
  have hu : LocallyIntegrable u volume :=
    huLp.locallyIntegrable hpENN
  exact Submission.FirstOrder.PK.exists_morreyRep_bound hn hp hu huLp
    (fun i ↦ rawDerivRep_isWeakDeriv_coord hf m i hm)
    (fun i ↦ rawDerivRep_memLp hf (m + Helpers.coordMulti i)
      (by simpa only [sum_add_coordMulti] using hm))

theorem regularRep_holder {n k : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (hm : (∑ j, m j) + 1 ≤ k) :
    ∃ C : NNReal,
      HolderWith C (Submission.Morrey.morreyExponent n p).toNNReal
        (regularRep hf m) := by
  let u := rawDerivRep hf m
  let du : Fin n → E n → ℝ :=
    fun i ↦ rawDerivRep hf (m + Helpers.coordMulti i)
  have hpENN : 1 ≤ ENNReal.ofReal p :=
    Helpers.one_le_ofReal_of_dim_pos hn hp
  have huLp : MemLp u (ENNReal.ofReal p) volume :=
    rawDerivRep_memLp hf m (by omega)
  have hu : LocallyIntegrable u volume :=
    huLp.locallyIntegrable hpENN
  exact Submission.FirstOrder.PK.morreyRep_holder hn hp hu huLp
    (fun i ↦ rawDerivRep_isWeakDeriv_coord hf m i hm)
    (fun i ↦ rawDerivRep_memLp hf (m + Helpers.coordMulti i)
      (by simpa only [sum_add_coordMulti] using hm))

noncomputable def coordDerivative {n k : ℕ} {p : ℝ}
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) : E n → E n →L[ℝ] ℝ :=
  fun x ↦ ∑ i : Fin n,
    regularRep hf (m + Helpers.coordMulti i) x • EuclideanSpace.proj i

theorem fderiv_regularize_eq_sum {n k : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (hm : (∑ i, m i) + 1 ≤ k)
    {t : ℝ} (ht : t ≠ 0) (x : E n) :
    fderiv ℝ
        (Submission.ProductKernel.regularize n t (rawDerivRep hf m)) x =
      ∑ i : Fin n,
        Submission.ProductKernel.regularize n t
            (rawDerivRep hf (m + Helpers.coordMulti i)) x •
          EuclideanSpace.proj i := by
  let u := rawDerivRep hf m
  have hpENN : 1 ≤ ENNReal.ofReal p :=
    Helpers.one_le_ofReal_of_dim_pos hn hp
  have huLp : MemLp u (ENNReal.ofReal p) volume :=
    rawDerivRep_memLp hf m (by omega)
  have hu : LocallyIntegrable u volume := huLp.locallyIntegrable hpENN
  ext z
  have hz :
      z = ∑ i : Fin n, z i • EuclideanSpace.single i (1 : ℝ) := by
    classical
    apply PiLp.ext
    intro j
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      EuclideanSpace.single, PiLp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  rw [hz, map_sum, map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  rw [← LeanEval.Analysis.SobolevMorreyProblem.partialDeriv,
    Submission.FirstOrder.PK.partialDeriv_regularize hu
      (rawDerivRep_isWeakDeriv_coord hf m i hm) ht x]
  rw [sum_apply]
  simp only [smul_apply, EuclideanSpace.coe_proj]
  change
    Submission.ProductKernel.regularize n t
        (rawDerivRep hf (m + Helpers.coordMulti i)) x =
      ∑ j : Fin n,
        Submission.ProductKernel.regularize n t
            (rawDerivRep hf (m + Helpers.coordMulti j)) x *
          (EuclideanSpace.single i (1 : ℝ)) j
  symm
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [EuclideanSpace.single, hj]
  · simp

private theorem tendstoUniformly_sum {ι : Type*} [Fintype ι]
    {X Y : Type*} [NormedAddCommGroup Y]
    {l : Filter ℕ} {F : ι → ℕ → X → Y} {g : ι → X → Y}
    (h : ∀ i, TendstoUniformly (F i) (g i) l) :
    TendstoUniformly
      (fun j x ↦ ∑ i, F i j x)
      (fun x ↦ ∑ i, g i x) l := by
  classical
  have hs (s : Finset ι) :
      TendstoUniformly
        (fun j x ↦ ∑ i ∈ s, F i j x)
        (fun x ↦ ∑ i ∈ s, g i x) l := by
    induction s using Finset.induction_on with
    | empty =>
        rw [Metric.tendstoUniformly_iff]
        intro ε hε
        exact Filter.Eventually.of_forall fun _j _x ↦ by simpa using hε
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        change TendstoUniformly
          (F a + fun j x ↦ ∑ i ∈ s, F i j x)
          (g a + fun x ↦ ∑ i ∈ s, g i x) l
        exact (h a).add ih
  simpa using hs Finset.univ

theorem tendstoUniformly_fderiv_regularize {n k : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (hm : (∑ i, m i) + 2 ≤ k) :
    TendstoUniformly
      (fun j x ↦
        fderiv ℝ
          (Submission.ProductKernel.regularize n
            (Submission.Morrey.scale j) (rawDerivRep hf m)) x)
      (coordDerivative hf m) atTop := by
  let embed (i : Fin n) : ℝ →L[ℝ] E n →L[ℝ] ℝ :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.proj i)
  have hcomponent (i : Fin n) :
      TendstoUniformly
        (fun j x ↦
          embed i (Submission.ProductKernel.regularize n
              (Submission.Morrey.scale j)
              (rawDerivRep hf (m + Helpers.coordMulti i)) x))
        (fun x ↦
          embed i (regularRep hf (m + Helpers.coordMulti i) x)) atTop := by
    let mi := m + Helpers.coordMulti i
    let ui := rawDerivRep hf mi
    let dui : Fin n → E n → ℝ :=
      fun j ↦ rawDerivRep hf (mi + Helpers.coordMulti j)
    have huiLp : MemLp ui (ENNReal.ofReal p) volume :=
      rawDerivRep_memLp hf mi (by
        rw [show mi = m + Helpers.coordMulti i by rfl,
          sum_add_coordMulti]
        omega)
    have hui : LocallyIntegrable ui volume :=
      huiLp.locallyIntegrable (Helpers.one_le_ofReal_of_dim_pos hn hp)
    have hweak :
        ∀ j, IsWeakDeriv ui (dui j) (Helpers.coordMulti j) := by
      intro j
      exact rawDerivRep_isWeakDeriv_coord hf mi j (by
        rw [show mi = m + Helpers.coordMulti i by rfl,
          sum_add_coordMulti]
        omega)
    have hdu : ∀ j, MemLp (dui j) (ENNReal.ofReal p) volume := by
      intro j
      exact rawDerivRep_memLp hf (mi + Helpers.coordMulti j) (by
        rw [sum_add_coordMulti,
          show mi = m + Helpers.coordMulti i by rfl,
          sum_add_coordMulti]
        omega)
    have hscalar :=
      Submission.FirstOrder.PK.tendstoUniformly_regularize_morreyRep
        hn hp hui hweak hdu
    have hembed :
        UniformContinuous (embed i) := (embed i).lipschitz.uniformContinuous
    have hcomp := hembed.comp_tendstoUniformly hscalar
    change TendstoUniformly
      (fun j x ↦ embed i
        (Submission.ProductKernel.regularize n
          (Submission.Morrey.scale j)
          (rawDerivRep hf (m + Helpers.coordMulti i)) x))
      (fun x ↦ embed i
        (regularRep hf (m + Helpers.coordMulti i) x)) atTop at hcomp
    exact hcomp
  have hsum :=
    tendstoUniformly_sum
      (F := fun i j x ↦
        embed i (Submission.ProductKernel.regularize n
            (Submission.Morrey.scale j)
            (rawDerivRep hf (m + Helpers.coordMulti i)) x))
      (g := fun i x ↦
        embed i (regularRep hf (m + Helpers.coordMulti i) x))
      hcomponent
  rw [tendstoUniformly_congr
    (Filter.Eventually.of_forall fun j ↦ by
      funext x
      exact fderiv_regularize_eq_sum hn hp hf m (by omega)
        (Submission.Morrey.scale_pos j).ne' x)]
  change TendstoUniformly
    (fun j x ↦ ∑ i : Fin n,
      Submission.ProductKernel.regularize n (Submission.Morrey.scale j)
          (rawDerivRep hf (m + Helpers.coordMulti i)) x •
        EuclideanSpace.proj i)
    (fun x ↦ ∑ i : Fin n,
      regularRep hf (m + Helpers.coordMulti i) x •
        EuclideanSpace.proj i) atTop
  simpa only [embed, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply] using hsum

theorem regularRep_hasFDerivAt {n k : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (hm : (∑ i, m i) + 2 ≤ k) (x : E n) :
    HasFDerivAt (regularRep hf m) (coordDerivative hf m x) x := by
  let u := rawDerivRep hf m
  have huLp : MemLp u (ENNReal.ofReal p) volume :=
    rawDerivRep_memLp hf m (by omega)
  have hu : LocallyIntegrable u volume :=
    huLp.locallyIntegrable (Helpers.one_le_ofReal_of_dim_pos hn hp)
  have hweak :
      ∀ i, IsWeakDeriv u
        (rawDerivRep hf (m + Helpers.coordMulti i))
        (Helpers.coordMulti i) :=
    fun i ↦ rawDerivRep_isWeakDeriv_coord hf m i (by omega)
  have hdu :
      ∀ i, MemLp (rawDerivRep hf (m + Helpers.coordMulti i))
        (ENNReal.ofReal p) volume :=
    fun i ↦ rawDerivRep_memLp hf (m + Helpers.coordMulti i) (by
      rw [sum_add_coordMulti]
      omega)
  apply hasFDerivAt_of_tendstoUniformly
    (tendstoUniformly_fderiv_regularize hn hp hf m hm)
    (fun j y ↦ ?_)
    (fun y ↦ Submission.FirstOrder.PK.tendsto_regularize_morreyRep
      hn hp hu hweak hdu y)
    x
  have hsmooth :=
    (Submission.ProductKernel.regularize_contDiff n
      (Submission.Morrey.scale_pos j).ne' hu).differentiable (by norm_num)
  exact (hsmooth y).hasFDerivAt

theorem regularRep_fderiv {n k : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (hm : (∑ i, m i) + 2 ≤ k) :
    fderiv ℝ (regularRep hf m) = coordDerivative hf m := by
  funext x
  exact (regularRep_hasFDerivAt hn hp hf m hm x).fderiv

theorem regularRep_contDiff {n k : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (s : ℕ)
    (hm : (∑ i, m i) + s + 1 ≤ k) :
    ContDiff ℝ s (regularRep hf m) := by
  induction s generalizing m with
  | zero =>
      exact contDiff_zero.mpr
        (regularRep_continuous hn hp hf m (by omega))
  | succ s ih =>
      change ContDiff ℝ ((s : WithTop ℕ∞) + 1) (regularRep hf m)
      rw [contDiff_succ_iff_hasFDerivAt]
      refine ⟨coordDerivative hf m, ?_, fun x ↦
        regularRep_hasFDerivAt hn hp hf m (by omega) x⟩
      change ContDiff ℝ s (fun x ↦ ∑ i : Fin n,
        regularRep hf (m + Helpers.coordMulti i) x •
          EuclideanSpace.proj i)
      exact ContDiff.sum fun i _hi ↦
        (ih (m + Helpers.coordMulti i) (by
          rw [sum_add_coordMulti]
          omega)).smul_const (EuclideanSpace.proj i)

noncomputable def coordEmbed {n : ℕ} (i : Fin n) :
    ℝ →L[ℝ] E n →L[ℝ] ℝ :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.proj i)

theorem iteratedFDeriv_coordDerivative {n k s : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (hm : (∑ i, m i) + s + 2 ≤ k) (x : E n) :
    iteratedFDeriv ℝ s (coordDerivative hf m) x =
      ∑ i : Fin n,
        (coordEmbed i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ s
            (regularRep hf (m + Helpers.coordMulti i)) x) := by
  rw [show coordDerivative hf m =
    fun y ↦ ∑ i : Fin n,
      regularRep hf (m + Helpers.coordMulti i) y •
        EuclideanSpace.proj i by rfl]
  rw [iteratedFDeriv_fun_sum_apply]
  · apply Finset.sum_congr rfl
    intro i _hi
    simpa only [coordEmbed] using
      (iteratedFDeriv_smul_const_apply
        ((regularRep_contDiff hn hp hf
          (m + Helpers.coordMulti i) s (by
            rw [sum_add_coordMulti]
            omega)).contDiffAt :
          ContDiffAt ℝ s
            (regularRep hf (m + Helpers.coordMulti i)) x))
  · intro i _hi
    exact ((regularRep_contDiff hn hp hf
      (m + Helpers.coordMulti i) s (by
        rw [sum_add_coordMulti]
        omega)).smul_const (EuclideanSpace.proj i)).contDiffAt

set_option maxHeartbeats 800000 in
theorem exists_iteratedFDeriv_regularRep_bound {n k s : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (hm : (∑ i, m i) + s + 1 ≤ k) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x, ‖iteratedFDeriv ℝ s (regularRep hf m) x‖ ≤ M := by
  induction s generalizing m with
  | zero =>
      obtain ⟨M, hM, hbound⟩ :=
        regularRep_bounded hn hp hf m (by omega)
      exact ⟨M, hM, fun x ↦ by
        simpa only [norm_iteratedFDeriv_zero] using hbound x⟩
  | succ s ih =>
      choose M hM hbound using fun i : Fin n ↦
        ih (m + Helpers.coordMulti i) (by
          rw [sum_add_coordMulti]
          omega)
      let B : ℝ := ∑ i : Fin n, ‖coordEmbed i‖ * M i
      refine ⟨B, Finset.sum_nonneg fun i _hi ↦
        mul_nonneg (norm_nonneg (coordEmbed i)) (hM i), fun x ↦ ?_⟩
      calc
        ‖iteratedFDeriv ℝ (s + 1) (regularRep hf m) x‖ =
            ‖iteratedFDeriv ℝ s
              (fderiv ℝ (regularRep hf m)) x‖ :=
          norm_iteratedFDeriv_fderiv.symm
        _ = ‖iteratedFDeriv ℝ s (coordDerivative hf m) x‖ := by
          rw [regularRep_fderiv hn hp hf m (by omega)]
        _ = ‖∑ i : Fin n,
              (coordEmbed i).compContinuousMultilinearMap
                (iteratedFDeriv ℝ s
                  (regularRep hf (m + Helpers.coordMulti i)) x)‖ := by
          rw [iteratedFDeriv_coordDerivative hn hp hf m (by omega) x]
        _ ≤ ∑ i : Fin n,
              ‖(coordEmbed i).compContinuousMultilinearMap
                (iteratedFDeriv ℝ s
                  (regularRep hf (m + Helpers.coordMulti i)) x)‖ :=
          by
            simpa using
              (norm_sum_le (Finset.univ : Finset (Fin n))
                (fun i ↦
                  (coordEmbed i).compContinuousMultilinearMap
                    (iteratedFDeriv ℝ s
                      (regularRep hf (m + Helpers.coordMulti i)) x)))
        _ ≤ ∑ i : Fin n, ‖coordEmbed i‖ * M i := by
          apply Finset.sum_le_sum
          intro i _hi
          exact ((coordEmbed i).norm_compContinuousMultilinearMap_le
            (iteratedFDeriv ℝ s
              (regularRep hf (m + Helpers.coordMulti i)) x)).trans
                (mul_le_mul_of_nonneg_left (hbound i x) (norm_nonneg _))
        _ = B := rfl

private theorem holderWith_sum {ι X Y : Type*} [Fintype ι]
    [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    {a : NNReal} {C : ι → NNReal} {F : ι → X → Y}
    (hF : ∀ i, HolderWith (C i) a (F i)) :
    HolderWith (∑ i, C i) a (fun x ↦ ∑ i, F i x) := by
  classical
  have hs (s : Finset ι) :
      HolderWith (∑ i ∈ s, C i) a
        (fun x ↦ ∑ i ∈ s, F i x) := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        change HolderWith 0 a (0 : X → Y)
        exact HolderWith.zero
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        change HolderWith (C i + ∑ j ∈ s, C j) a
          (F i + fun x ↦ ∑ j ∈ s, F j x)
        exact (hF i).add ih
  simpa using hs Finset.univ

private theorem holderWith_compContinuousMultilinearMap
    {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)]
    {G G' : Type*} [SeminormedAddCommGroup G] [NormedSpace ℝ G]
    [SeminormedAddCommGroup G'] [NormedSpace ℝ G']
    (g : G →L[ℝ] G') {C a : NNReal}
    {F : X → ContinuousMultilinearMap ℝ E G}
    (hF : HolderWith C a F) :
    HolderWith ((‖g‖).toNNReal * C) a
      (fun x ↦ g.compContinuousMultilinearMap (F x)) := by
  intro x y
  rw [edist_nndist, edist_nndist,
    ← ENNReal.coe_rpow_of_nonneg _ NNReal.zero_le_coe,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  change
    dist (g.compContinuousMultilinearMap (F x))
        (g.compContinuousMultilinearMap (F y)) ≤
      (((‖g‖).toNNReal * C : NNReal) : ℝ) *
        dist x y ^ (a : ℝ)
  have hsub :
      g.compContinuousMultilinearMap (F x - F y) =
        g.compContinuousMultilinearMap (F x) -
          g.compContinuousMultilinearMap (F y) := by
    ext v
    simp
  calc
    dist (g.compContinuousMultilinearMap (F x))
        (g.compContinuousMultilinearMap (F y)) =
        ‖g.compContinuousMultilinearMap (F x - F y)‖ := by
          rw [dist_eq_norm, hsub]
    _ ≤ ‖g‖ * ‖F x - F y‖ :=
      g.norm_compContinuousMultilinearMap_le (F x - F y)
    _ = ‖g‖ * dist (F x) (F y) := by rw [dist_eq_norm]
    _ ≤ ‖g‖ * ((C : ℝ) * dist x y ^ (a : ℝ)) :=
      mul_le_mul_of_nonneg_left (hF.dist_le x y) g.opNorm_nonneg
    _ = (((‖g‖).toNNReal * C : NNReal) : ℝ) *
        dist x y ^ (a : ℝ) := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ g.opNorm_nonneg]
      ring

theorem exists_holder_iteratedFDeriv_regularRep {n k s : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (hm : (∑ i, m i) + s + 1 ≤ k) :
    ∃ C : NNReal,
      HolderWith C (Submission.Morrey.morreyExponent n p).toNNReal
        (iteratedFDeriv ℝ s (regularRep hf m)) := by
  induction s generalizing m with
  | zero =>
      obtain ⟨C, hC⟩ := regularRep_holder hn hp hf m (by omega)
      refine ⟨C, ?_⟩
      rw [iteratedFDeriv_zero_eq_comp]
      have hiso :
          HolderWith 1 1
            (continuousMultilinearCurryFin0 ℝ (E n) ℝ).symm :=
        (continuousMultilinearCurryFin0 ℝ (E n) ℝ).symm.isometry.lipschitz.holderWith
      simpa only [one_mul, NNReal.coe_one, NNReal.rpow_one] using hiso.comp hC
  | succ s ih =>
      choose C hC using fun i : Fin n ↦
        ih (m + Helpers.coordMulti i) (by
          rw [sum_add_coordMulti]
          omega)
      have hcomponent (i : Fin n) :
          HolderWith ((‖coordEmbed i‖).toNNReal * C i)
            (Submission.Morrey.morreyExponent n p).toNNReal
            (fun x ↦
              (coordEmbed i).compContinuousMultilinearMap
                (iteratedFDeriv ℝ s
                  (regularRep hf (m + Helpers.coordMulti i)) x)) := by
        exact holderWith_compContinuousMultilinearMap
          (coordEmbed i) (hC i)
      have hsum :
          HolderWith (∑ i : Fin n, (‖coordEmbed i‖).toNNReal * C i)
            (Submission.Morrey.morreyExponent n p).toNNReal
            (fun x ↦ ∑ i : Fin n,
              (coordEmbed i).compContinuousMultilinearMap
                (iteratedFDeriv ℝ s
                  (regularRep hf (m + Helpers.coordMulti i)) x)) :=
        holderWith_sum hcomponent
      let I :=
        (continuousMultilinearCurryRightEquiv' ℝ s (E n) ℝ).symm
      have hI : HolderWith 1 1 I :=
        I.isometry.lipschitz.holderWith
      have hcomposed :
          HolderWith (∑ i : Fin n, (‖coordEmbed i‖).toNNReal * C i)
            (Submission.Morrey.morreyExponent n p).toNNReal
            (I ∘ fun x ↦ ∑ i : Fin n,
              (coordEmbed i).compContinuousMultilinearMap
                (iteratedFDeriv ℝ s
                  (regularRep hf (m + Helpers.coordMulti i)) x)) := by
        simpa only [one_mul, NNReal.coe_one, NNReal.rpow_one] using hI.comp hsum
      refine ⟨∑ i : Fin n, (‖coordEmbed i‖).toNNReal * C i, ?_⟩
      have heq :
          iteratedFDeriv ℝ (s + 1) (regularRep hf m) =
            I ∘ fun x ↦ ∑ i : Fin n,
              (coordEmbed i).compContinuousMultilinearMap
                (iteratedFDeriv ℝ s
                  (regularRep hf (m + Helpers.coordMulti i)) x) := by
        funext x
        rw [iteratedFDeriv_succ_eq_comp_right,
          regularRep_fderiv hn hp hf m (by omega)]
        change I (iteratedFDeriv ℝ s (coordDerivative hf m) x) = _
        rw [iteratedFDeriv_coordDerivative hn hp hf m (by omega) x]
        rfl
      rwa [heq]

theorem exists_lipschitz_iteratedFDeriv_regularRep {n k s : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (m : Fin n → ℕ) (hm : (∑ i, m i) + s + 2 ≤ k) :
    ∃ C : NNReal,
      LipschitzWith C (iteratedFDeriv ℝ s (regularRep hf m)) := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_iteratedFDeriv_regularRep_bound hn hp hf m (s := s + 1)
      (by omega)
  have hcont :=
    regularRep_contDiff hn hp hf m (s + 1) (by omega)
  have hdiff :
      Differentiable ℝ (iteratedFDeriv ℝ s (regularRep hf m)) :=
    hcont.differentiable_iteratedFDeriv (by
      exact_mod_cast Nat.lt_succ_self s)
  refine ⟨M.toNNReal, lipschitzWith_of_nnnorm_fderiv_le hdiff fun x ↦ ?_⟩
  change
    ‖fderiv ℝ (iteratedFDeriv ℝ s (regularRep hf m)) x‖ ≤
      (M.toNNReal : ℝ)
  rw [norm_fderiv_iteratedFDeriv, Real.coe_toNNReal _ hM]
  exact hbound x

private theorem holderWith_zero_of_norm_bound
    {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    {F : X → Y} {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, ‖F x‖ ≤ M) :
    HolderWith (2 * M.toNNReal) 0 F := by
  intro x y
  simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one, edist_nndist]
  rw [ENNReal.coe_le_coe]
  change dist (F x) (F y) ≤ 2 * M.toNNReal
  rw [Real.coe_toNNReal _ hM]
  calc
    dist (F x) (F y) ≤ ‖F x‖ + ‖F y‖ := dist_le_norm_add_norm _ _
    _ ≤ M + M := add_le_add (hbound x) (hbound y)
    _ = 2 * M := by ring

private theorem exists_holderWith_of_bound_of_holderWith
    {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    {F : X → Y} {M a b : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x, ‖F x‖ ≤ M) (hab : a ≤ b)
    {C : NNReal} (hC : HolderWith C b.toNNReal F) :
    ∃ C' : NNReal, HolderWith C' a.toNNReal F := by
  let C₀ : NNReal := 2 * M.toNNReal
  have hzero : HolderWith C₀ 0 F := by
    exact holderWith_zero_of_norm_bound hM hbound
  refine ⟨max C₀ C, ?_⟩
  exact hzero.of_le_of_le hC bot_le (Real.toNNReal_le_toNNReal hab)

theorem regularRep_memHolder {n k r : ℕ} {α p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hgap : (r : ℝ) + α < (k : ℝ) - n / p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f) :
    MemHolder r α (regularRep hf (fun _ ↦ 0)) := by
  have hrk : r + 1 ≤ k :=
    Helpers.succ_le_of_morrey_gap hp hα hgap
  have hcont :
      ContDiff ℝ r (regularRep hf (fun _ ↦ 0)) :=
    regularRep_contDiff hn hp hf (fun _ ↦ 0) r (by
      simpa using hrk)
  have hbounded :
      ∀ j ≤ r, ∃ M : ℝ,
        ∀ x, ‖iteratedFDeriv ℝ j
          (regularRep hf (fun _ ↦ 0)) x‖ ≤ M := by
    intro j hj
    obtain ⟨M, _hM, hM⟩ :=
      exists_iteratedFDeriv_regularRep_bound hn hp hf
        (fun _ ↦ 0) (s := j) (by
          simpa using (Nat.add_le_add_right hj 1 |>.trans hrk))
    exact ⟨M, hM⟩
  obtain ⟨Mr, hMr, hboundr⟩ :=
    exists_iteratedFDeriv_regularRep_bound hn hp hf
      (fun _ ↦ 0) (s := r) (by simpa using hrk)
  have hholder :
      ∃ C : NNReal,
        HolderWith C α.toNNReal
          (iteratedFDeriv ℝ r (regularRep hf (fun _ ↦ 0))) := by
    by_cases hextra : r + 2 ≤ k
    · obtain ⟨C, hC⟩ :=
        exists_lipschitz_iteratedFDeriv_regularRep hn hp hf
          (fun _ ↦ 0) (s := r) (by simpa using hextra)
      have hC' :
          HolderWith C (1 : ℝ).toNNReal
            (iteratedFDeriv ℝ r (regularRep hf (fun _ ↦ 0))) := by
        simpa using hC.holderWith
      exact exists_holderWith_of_bound_of_holderWith
        hMr hboundr hα1 hC'
    · have hk : k = r + 1 := by omega
      let β := Submission.Morrey.morreyExponent n p
      have hαβ : α ≤ β := by
        dsimp [β, Submission.Morrey.morreyExponent]
        rw [hk] at hgap
        push_cast at hgap
        linarith
      obtain ⟨C, hC⟩ :=
        exists_holder_iteratedFDeriv_regularRep hn hp hf
          (fun _ ↦ 0) (s := r) (by simpa using hrk)
      exact exists_holderWith_of_bound_of_holderWith
        hMr hboundr hαβ hC
  exact ⟨hcont, hholder, hbounded⟩

theorem ae_eq_regularRep_zero {n k : ℕ} {p : ℝ}
    (hn : 0 < n) (hp : (n : ℝ) < p)
    {f : E n → ℝ} (hf : MemSobolevWk k (ENNReal.ofReal p) f)
    (hk : 1 ≤ k) :
    f =ᵐ[volume] regularRep hf (fun _ ↦ 0) := by
  let z : Fin n → ℕ := fun _ ↦ 0
  have hzsum : ∑ i, z i = 0 := by simp [z]
  have hraw : IsWeakDeriv f (rawDerivRep hf z) z :=
    rawDerivRep_isWeakDeriv hf z (by rw [hzsum]; omega)
  have hself : IsWeakDeriv f f z := by
    intro φ _hφ _hφc
    simp only [z, Helpers.mixedDeriv_zero, Finset.sum_const_zero,
      pow_zero, one_mul]
  have hrawLp : MemLp (rawDerivRep hf z) (ENNReal.ofReal p) volume :=
    rawDerivRep_memLp hf z (by rw [hzsum]; omega)
  have hrawLoc : LocallyIntegrable (rawDerivRep hf z) volume :=
    hrawLp.locallyIntegrable (Helpers.one_le_ofReal_of_dim_pos hn hp)
  have hfirst : f =ᵐ[volume] rawDerivRep hf z :=
    Submission.Helpers.IsWeakDeriv.ae_eq hself hraw hf.1 hrawLoc
  exact hfirst.trans (regularRep_ae_eq hn hp hf z (by
    rw [hzsum]
    simpa using hk))

end Submission.HigherOrder
