import Submission.Helpers

open MeasureTheory Module Set
open scoped ContDiff Topology

namespace Submission

noncomputable section

private lemma infty_add_nat (k : ℕ) : (∞ : ℕ∞ω) + k = ∞ := by
  induction k with
  | zero => simp only [Nat.cast_zero, add_zero]
  | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc, ih, ENat.coe_top_add_one]

set_option maxHeartbeats 4000000 in
private theorem scalarSardAux (d : ℕ)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (hd : finrank ℝ V ≤ d)
    (f : V → ℝ) (s : Set V)
    (hf : ∀ x ∈ s, ContDiffAt ℝ ∞ f x)
    (hcrit : ∀ x ∈ s, fderiv ℝ f x = 0) :
    volume (f '' s) = 0 := by
  classical
  induction d generalizing V with
  | zero =>
      haveI : Subsingleton V :=
        Module.finrank_zero_iff.mp (Nat.eq_zero_of_le_zero hd)
      apply Set.Subsingleton.measure_zero
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [Subsingleton.elim x y]
  | succ d ih =>
      let flat : Set V :=
        {x | x ∈ s ∧ ∀ i, 1 ≤ i → i ≤ finrank ℝ V + 1 →
          iteratedFDeriv ℝ i f x = 0}
      let layer : ℕ → Set V := fun i =>
        {x | x ∈ s ∧ 2 ≤ i ∧
          iteratedFDeriv ℝ (i - 1) f x = 0 ∧
          iteratedFDeriv ℝ i f x ≠ 0}
      have hflat : volume (f '' flat) = 0 := by
        apply Helpers.volume_image_eq_zero_of_flat_on
            (k := finrank ℝ V + 1) (by omega)
        · rw [finrank_self]
          apply (ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp))).2
          norm_cast
          omega
        · intro x hx
          exact hf x hx.1
        · intro x hx
          exact hx.2
      have hlayer : ∀ i, volume (f '' layer i) = 0 := by
        intro i
        apply Helpers.volume_image_eq_zero_of_locally_null
        intro x hx
        change x ∈ s ∧ 2 ≤ i ∧
          iteratedFDeriv ℝ (i - 1) f x = 0 ∧
          iteratedFDeriv ℝ i f x ≠ 0 at hx
        let k := i - 1
        let M := V [×k]→L[ℝ] ℝ
        let Dk : V → M := iteratedFDeriv ℝ k f
        let A : V →L[ℝ] M := fderiv ℝ Dk x
        have hA : A ≠ 0 := by
          intro hAzero
          apply hx.2.2.2
          have hki : k + 1 = i := by
            dsimp only [k]
            omega
          apply norm_eq_zero.mp
          rw [← hki]
          rw [← norm_fderiv_iteratedFDeriv]
          change ‖A‖ = 0
          rw [hAzero]
          exact norm_zero (E := V →L[ℝ] M)
        obtain ⟨v, hv⟩ : ∃ v, A v ≠ 0 := by
          by_contra! hall
          apply hA
          apply ContinuousLinearMap.ext
          exact hall
        obtain ⟨ell, _, hell⟩ :=
          exists_dual_vector ℝ (A v) (norm_ne_zero_iff.mpr hv)
        let g : V → ℝ := ell ∘ Dk
        let A₀ : V →L[ℝ] ℝ := ell.comp A
        have hA₀v : A₀ v ≠ 0 := by
          change ell (A v) ≠ 0
          rw [hell]
          exact norm_ne_zero_iff.mpr hv
        have hsurj : Function.Surjective A₀ := by
          intro y
          refine ⟨(y / A₀ v) • v, ?_⟩
          simp [hA₀v]
        have hsplit : A₀.HasRightInverse :=
          ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hsurj
        let R : ℝ →L[ℝ] V := hsplit.rightInverse
        have hR : Function.RightInverse R A₀ :=
          hsplit.rightInverse_rightInverse
        let Q : V →L[ℝ] V :=
          ContinuousLinearMap.id ℝ V - R.comp A₀
        have hQ_mem : ∀ y, Q y ∈ A₀.ker := by
          intro y
          change A₀ (Q y) = 0
          simp [Q, hR (A₀ y)]
        let P : V →L[ℝ] A₀.ker :=
          Q.codRestrict A₀.ker hQ_mem
        let L : V →L[ℝ] ℝ × A₀.ker := A₀.prod P
        have hL_injective : Function.Injective L := by
          intro y z hyz
          have hfirst : A₀ y = A₀ z :=
            congrArg Prod.fst hyz
          have hsecond : P y = P z :=
            congrArg Prod.snd hyz
          have hQ : Q y = Q z :=
            congrArg Subtype.val hsecond
          calc
            y = R (A₀ y) + Q y := by simp [Q]
            _ = R (A₀ z) + Q z := by rw [hfirst, hQ]
            _ = z := by simp [Q]
        have hL_surjective : Function.Surjective L := by
          rintro ⟨a, z⟩
          refine ⟨R a + z, ?_⟩
          apply Prod.ext
          · change A₀ (R a + (z : V)) = a
            simp [hR a]
          · apply Subtype.ext
            change Q (R a + (z : V)) = z
            simp [Q, hR a]
        let e : V ≃L[ℝ] ℝ × A₀.ker :=
          ContinuousLinearEquiv.ofBijective L
            (LinearMap.ker_eq_bot.mpr hL_injective)
            (LinearMap.range_eq_top.mpr hL_surjective)
        let phi : V → ℝ × A₀.ker := fun y => (g y, P y)
        have hDk : ContDiffAt ℝ ∞ Dk x := by
          exact (hf x hx.1).iteratedFDeriv_right
            (infty_add_nat k).le
        have hDk' : DifferentiableAt ℝ Dk x := by
          exact (hf x hx.1).differentiableAt_iteratedFDeriv
            (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)
        have hg : ContDiffAt ℝ ∞ g x := by
          exact hDk.continuousLinearMap_comp ell
        have hg' : HasFDerivAt g A₀ x := by
          exact ell.hasFDerivAt.comp x hDk'.hasFDerivAt
        have heq : A₀.prod P = (e : V →L[ℝ] ℝ × A₀.ker) := by
          rfl
        have hphi : ContDiffAt ℝ ∞ phi x := by
          exact hg.prodMk P.contDiff.contDiffAt
        have hphi' : HasFDerivAt phi (e : V →L[ℝ] ℝ × A₀.ker) x := by
          convert hg'.prodMk P.hasFDerivAt using 1
          exact heq
        let chart : OpenPartialHomeomorph V (ℝ × A₀.ker) :=
          hphi.toOpenPartialHomeomorph phi hphi' (by simp)
        have hxsource : x ∈ chart.source := by
          exact hphi.mem_toOpenPartialHomeomorph_source hphi' (by simp)
        have hinv : ContDiffAt ℝ ∞ chart.symm (phi x) := by
          change ContDiffAt ℝ ∞
            (hphi.localInverse hphi' (by simp)) (phi x)
          exact hphi.to_localInverse hphi' (by simp)
        let q : Set (ℝ × A₀.ker) :=
          {z | ContDiffAt ℝ 1 chart.symm z}
        have hq : q ∈ 𝓝 (phi x) :=
          (hinv.of_le (by simp)).eventually (by simp)
        have hpre : phi ⁻¹' q ∈ 𝓝 x :=
          hphi.continuousAt hq
        let t : Set V := layer i ∩ (chart.source ∩ phi ⁻¹' q)
        have ht : t ∈ 𝓝[layer i] x := by
          apply inter_mem_nhdsWithin
          exact Filter.inter_mem
            (chart.open_source.mem_nhds hxsource) hpre
        refine ⟨t, ht, ?_⟩
        let zset : Set A₀.ker :=
          {z | (0, z) ∈ chart.target ∧ (0, z) ∈ q ∧
            chart.symm (0, z) ∈ t}
        let h : A₀.ker → ℝ := fun z => f (chart.symm (0, z))
        have hsmooth : ∀ z ∈ zset, ContDiffAt ℝ ∞ h z := by
          intro z hz
          have hphi_z : ContDiffAt ℝ ∞ phi (chart.symm (0, z)) := by
            have hDk_z : ContDiffAt ℝ ∞ Dk (chart.symm (0, z)) :=
              (hf _ hz.2.2.1.1).iteratedFDeriv_right
                (infty_add_nat k).le
            exact (hDk_z.continuousLinearMap_comp ell).prodMk
              P.contDiff.contDiffAt
          have hinv_z : ContDiffAt ℝ ∞ chart.symm (0, z) :=
            Helpers.OpenPartialHomeomorph.contDiffAt_symm_infty_of_one
              chart hz.1 (by simpa [chart] using hphi_z) hz.2.1
          have hinr : ContDiffAt ℝ ∞
              (Prod.mk (0 : ℝ) : A₀.ker → ℝ × A₀.ker) z :=
            (contDiffAt_const (c := (0 : ℝ))).prodMk contDiffAt_id
          have hpsi : ContDiffAt ℝ ∞
              (fun w : A₀.ker => chart.symm (0, w)) z :=
            hinv_z.comp z hinr
          exact (hf _ hz.2.2.1.1).comp z hpsi
        have hcritical : ∀ z ∈ zset, fderiv ℝ h z = 0 := by
          intro z hz
          have hphi_z : ContDiffAt ℝ ∞ phi (chart.symm (0, z)) := by
            have hDk_z : ContDiffAt ℝ ∞ Dk (chart.symm (0, z)) :=
              (hf _ hz.2.2.1.1).iteratedFDeriv_right
                (infty_add_nat k).le
            exact (hDk_z.continuousLinearMap_comp ell).prodMk
              P.contDiff.contDiffAt
          have hinv_z : ContDiffAt ℝ ∞ chart.symm (0, z) :=
            Helpers.OpenPartialHomeomorph.contDiffAt_symm_infty_of_one
              chart hz.1 (by simpa [chart] using hphi_z) hz.2.1
          have hinr : ContDiffAt ℝ ∞
              (Prod.mk (0 : ℝ) : A₀.ker → ℝ × A₀.ker) z :=
            (contDiffAt_const (c := (0 : ℝ))).prodMk contDiffAt_id
          have hpsi : ContDiffAt ℝ ∞
              (fun w : A₀.ker => chart.symm (0, w)) z :=
            hinv_z.comp z hinr
          have hfzero : HasFDerivAt f (0 : V →L[ℝ] ℝ) (chart.symm (0, z)) := by
            simpa [hcrit _ hz.2.2.1.1] using
              (hf _ hz.2.2.1.1).differentiableAt (by simp) |>.hasFDerivAt
          simpa [h, Function.comp_def] using
            (hfzero.comp z ((hpsi.differentiableAt (by simp)).hasFDerivAt)).fderiv
        have hdimker : finrank ℝ A₀.ker ≤ d := by
          have hrank :=
            A₀.toLinearMap.finrank_range_add_finrank_ker
          have hrange : LinearMap.range A₀.toLinearMap = ⊤ :=
            A₀.toLinearMap.range_eq_top.mpr hsurj
          rw [hrange, finrank_top, finrank_self] at hrank
          omega
        have hznull : volume (h '' zset) = 0 :=
          ih hdimker h zset hsmooth hcritical
        apply measure_mono_null _ hznull
        intro y hy
        rcases hy with ⟨u, hu, rfl⟩
        have hulayer : u ∈ layer i := hu.1
        change u ∈ s ∧ 2 ≤ i ∧
          iteratedFDeriv ℝ (i - 1) f u = 0 ∧
          iteratedFDeriv ℝ i f u ≠ 0 at hulayer
        have hgzero : g u = 0 := by
          simp [g, Dk, k, hulayer.2.2.1]
        let z : A₀.ker := (phi u).2
        have hpair : (0, z) = phi u := by
          apply Prod.ext
          · simpa [phi] using hgzero.symm
          · rfl
        have hutarget : phi u ∈ chart.target :=
          chart.map_source hu.2.1
        have huinv : chart.symm (phi u) = u :=
          chart.left_inv hu.2.1
        refine ⟨z, ?_, ?_⟩
        · refine ⟨hpair.symm ▸ hutarget, hpair.symm ▸ hu.2.2, ?_⟩
          simpa [hpair, huinv] using hu
        · simp [h, hpair, huinv]
      have hcover : s ⊆ flat ∪ ⋃ i, layer i := by
        intro x hx
        by_cases hflatx : ∀ i, 1 ≤ i → i ≤ finrank ℝ V + 1 →
            iteratedFDeriv ℝ i f x = 0
        · exact Or.inl ⟨hx, hflatx⟩
        · right
          push Not at hflatx
          obtain ⟨j, hj1, hjbound, hjne⟩ := hflatx
          let p : ℕ → Prop := fun i =>
            1 ≤ i ∧ i ≤ finrank ℝ V + 1 ∧
              iteratedFDeriv ℝ i f x ≠ 0
          have hp : ∃ i, p i := ⟨j, hj1, hjbound, hjne⟩
          let i := Nat.find hp
          have hi := Nat.find_spec hp
          have hone : iteratedFDeriv ℝ 1 f x = 0 := by
            apply norm_eq_zero.mp
            rw [norm_iteratedFDeriv_one, hcrit x hx, norm_zero]
          have hi2 : 2 ≤ i := by
            by_contra hnot
            have hieq : i = 1 := by omega
            apply hi.2.2
            change iteratedFDeriv ℝ i f x = 0
            rw [hieq]
            exact hone
          have hprev : iteratedFDeriv ℝ (i - 1) f x = 0 := by
            by_contra hne
            have hlt : i - 1 < i := by omega
            exact (Nat.find_min hp hlt) ⟨by omega, by omega, hne⟩
          exact mem_iUnion.2 ⟨i, hx, hi2, hprev, hi.2.2⟩
      refine measure_mono_null (image_mono hcover) ?_
      rw [image_union, image_iUnion]
      exact measure_union_null hflat (measure_iUnion_null hlayer)

theorem scalarSardOn
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (f : V → ℝ) (s : Set V)
    (hf : ∀ x ∈ s, ContDiffAt ℝ ∞ f x)
    (hcrit : ∀ x ∈ s, fderiv ℝ f x = 0) :
    volume (f '' s) = 0 :=
  scalarSardAux (finrank ℝ V) le_rfl f s hf hcrit

end

end Submission
