import Submission.Scalar

open LeanEval.Geometry.SardTheoremProblem
open MeasureTheory Module Set
open scoped ContDiff Topology

namespace Submission

noncomputable section

private def splitLinear (n : ℕ) : E (n + 1) ≃L[ℝ] ℝ × E n :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).trans <|
    ((LinearEquiv.piCongrLeft ℝ (fun _ : Option (Fin n) => ℝ) (finSuccEquiv n) ≪≫ₗ
      LinearEquiv.piOptionEquivProd ℝ).toContinuousLinearEquiv).trans <|
        (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
          (EuclideanSpace.equiv (Fin n) ℝ).symm

@[simp]
private theorem splitLinear_fst (n : ℕ) (y : E (n + 1)) :
    (splitLinear n y).1 = y 0 := by
  rfl

@[simp]
private theorem splitLinear_snd (n : ℕ) (y : E (n + 1)) (j : Fin n) :
    (splitLinear n y).2 j = y j.succ := by
  rfl

private theorem splitLinear_measurePreserving (n : ℕ) :
    MeasurePreserving (splitLinear n) := by
  have h₁ : MeasurePreserving
      (WithLp.ofLp : E (n + 1) → (Fin (n + 1) → ℝ)) :=
    PiLp.volume_preserving_ofLp (Fin (n + 1))
  have h₂ : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0) :=
    volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0
  have h₃ : MeasurePreserving
      (Prod.map id (WithLp.toLp 2) :
        (ℝ × (Fin n → ℝ)) → (ℝ × E n)) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (PiLp.volume_preserving_toLp (Fin n))
  have h := h₃.comp (h₂.comp h₁)
  convert h using 1
  ext y
  · rfl
  · rw [splitLinear_snd]
    rfl

private theorem volume_eq_zero_of_split_image {n : ℕ} {s : Set (E (n + 1))}
    (hs : volume (splitLinear n '' s) = 0) :
    volume s = 0 := by
  have hpre :=
    (splitLinear_measurePreserving n).quasiMeasurePreserving.preimage_null hs
  simpa only [preimage_image_eq _ (splitLinear n).injective] using hpre

set_option maxHeartbeats 8000000 in
private theorem sardOnAux (n : ℕ)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (f : V → E n) (u : Set V) (hu : IsOpen u)
    (hf : ContDiffOn ℝ ∞ f u) :
    volume (f '' {x | x ∈ u ∧ ¬Function.Surjective (fderiv ℝ f x)}) = 0 := by
  induction n generalizing V with
  | zero =>
      have hempty :
          {x | x ∈ u ∧ ¬Function.Surjective (fderiv ℝ f x)} = ∅ := by
        apply Set.Subset.antisymm
        · intro x hx
          exfalso
          apply hx.2
          intro y
          exact ⟨0, Subsingleton.elim _ y⟩
        · exact Set.empty_subset _
      rw [hempty, image_empty, measure_empty]
  | succ n ih =>
      let e : E (n + 1) ≃L[ℝ] ℝ × E n := splitLinear n
      let head : E (n + 1) →L[ℝ] ℝ :=
        (ContinuousLinearMap.fst ℝ ℝ (E n)).comp e.toContinuousLinearMap
      let tail : E (n + 1) →L[ℝ] E n :=
        (ContinuousLinearMap.snd ℝ ℝ (E n)).comp e.toContinuousLinearMap
      let g : V → ℝ := head ∘ f
      let crit : Set V :=
        {x | x ∈ u ∧ ¬Function.Surjective (fderiv ℝ f x)}
      let s₀ : Set V := {x | x ∈ crit ∧ fderiv ℝ g x = 0}
      let s₁ : Set V := {x | x ∈ crit ∧ fderiv ℝ g x ≠ 0}
      have hcrit : crit ⊆ s₀ ∪ s₁ := by
        intro x hx
        by_cases hzero : fderiv ℝ g x = 0
        · exact Or.inl ⟨hx, hzero⟩
        · exact Or.inr ⟨hx, hzero⟩
      have hzero_scalar : volume (g '' s₀) = 0 := by
        apply scalarSardOn
        · intro x hx
          exact ((hf x hx.1.1).contDiffAt
            (hu.mem_nhds hx.1.1)).continuousLinearMap_comp head
        · intro x hx
          exact hx.2
      have hzero_split : volume (e '' (f '' s₀)) = 0 := by
        apply measure_mono_null
            (show e '' (f '' s₀) ⊆ (g '' s₀) ×ˢ (univ : Set (E n)) by
              rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
              exact ⟨⟨x, hx, rfl⟩, mem_univ _⟩)
        rw [Measure.volume_eq_prod, Measure.prod_prod, hzero_scalar, zero_mul]
      have hzero : volume (f '' s₀) = 0 :=
        volume_eq_zero_of_split_image hzero_split
      have hone : volume (f '' s₁) = 0 := by
        apply Helpers.volume_image_eq_zero_of_locally_null
        intro x hx
        change x ∈ crit ∧ fderiv ℝ g x ≠ 0 at hx
        let A : V →L[ℝ] ℝ := fderiv ℝ g x
        have hsurj : Function.Surjective A := by
          obtain ⟨v, hv⟩ : ∃ v, A v ≠ 0 := by
            by_contra! hall
            apply hx.2
            ext v
            simpa using hall v
          intro y
          refine ⟨(y / A v) • v, ?_⟩
          simp [hv]
        have hsplit : A.HasRightInverse :=
          ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hsurj
        let R : ℝ →L[ℝ] V := hsplit.rightInverse
        have hR : Function.RightInverse R A :=
          hsplit.rightInverse_rightInverse
        let Q : V →L[ℝ] V :=
          ContinuousLinearMap.id ℝ V - R.comp A
        have hQ_mem : ∀ y, Q y ∈ A.ker := by
          intro y
          change A (Q y) = 0
          simp [Q, hR (A y)]
        let P : V →L[ℝ] A.ker :=
          Q.codRestrict A.ker hQ_mem
        let L : V →L[ℝ] ℝ × A.ker := A.prod P
        have hL_injective : Function.Injective L := by
          intro y z hyz
          have hfirst : A y = A z :=
            congrArg Prod.fst hyz
          have hsecond : P y = P z :=
            congrArg Prod.snd hyz
          have hQ : Q y = Q z :=
            congrArg Subtype.val hsecond
          calc
            y = R (A y) + Q y := by simp [Q]
            _ = R (A z) + Q z := by rw [hfirst, hQ]
            _ = z := by simp [Q]
        have hL_surjective : Function.Surjective L := by
          rintro ⟨a, z⟩
          refine ⟨R a + z, ?_⟩
          apply Prod.ext
          · change A (R a + (z : V)) = a
            simp [hR a]
          · apply Subtype.ext
            change Q (R a + (z : V)) = z
            simp [Q, hR a]
        let edom : V ≃L[ℝ] ℝ × A.ker :=
          ContinuousLinearEquiv.ofBijective L
            (LinearMap.ker_eq_bot.mpr hL_injective)
            (LinearMap.range_eq_top.mpr hL_surjective)
        let phi : V → ℝ × A.ker := fun y => (g y, P y)
        have hg : ContDiffAt ℝ ∞ g x :=
          ((hf x hx.1.1).contDiffAt
            (hu.mem_nhds hx.1.1)).continuousLinearMap_comp head
        have hg' : HasFDerivAt g A x := by
          exact hg.differentiableAt (by simp) |>.hasFDerivAt
        have heq : A.prod P = (edom : V →L[ℝ] ℝ × A.ker) := by
          rfl
        have hphi : ContDiffAt ℝ ∞ phi x :=
          hg.prodMk P.contDiff.contDiffAt
        have hphi' : HasFDerivAt phi (edom : V →L[ℝ] ℝ × A.ker) x := by
          convert hg'.prodMk P.hasFDerivAt using 1
          exact heq
        let chart : OpenPartialHomeomorph V (ℝ × A.ker) :=
          hphi.toOpenPartialHomeomorph phi hphi' (by simp)
        have hxsource : x ∈ chart.source :=
          hphi.mem_toOpenPartialHomeomorph_source hphi' (by simp)
        have hinv : ContDiffAt ℝ ∞ chart.symm (phi x) := by
          change ContDiffAt ℝ ∞
            (hphi.localInverse hphi' (by simp)) (phi x)
          exact hphi.to_localInverse hphi' (by simp)
        have hx_u : x ∈ u := hx.1.1
        have hgood_mem :
            {p | p ∈ chart.target ∧ ContDiffAt ℝ 1 chart.symm p ∧
              chart.symm p ∈ u} ∈ 𝓝 (phi x) := by
          have htarget : chart.target ∈ 𝓝 (phi x) :=
            chart.open_target.mem_nhds (chart.map_source hxsource)
          have hsmooth :
              {p | ContDiffAt ℝ 1 chart.symm p} ∈ 𝓝 (phi x) :=
            (hinv.of_le (by simp)).eventually (by simp)
          have himage : chart.symm ⁻¹' u ∈ 𝓝 (phi x) := by
            apply hinv.continuousAt
            change u ∈ 𝓝 (chart.symm (chart x))
            rw [chart.left_inv hxsource]
            exact hu.mem_nhds hx_u
          exact Filter.inter_mem htarget (Filter.inter_mem hsmooth himage)
        obtain ⟨q, hqsub, hqopen, hphixq⟩ :=
          mem_nhds_iff.mp hgood_mem
        have hsource_mem :
            u ∩ (chart.source ∩ phi ⁻¹' q) ∈ 𝓝 x := by
          exact Filter.inter_mem (hu.mem_nhds hx_u) <|
            Filter.inter_mem (chart.open_source.mem_nhds hxsource)
              (hphi.continuousAt (hqopen.mem_nhds hphixq))
        obtain ⟨ε, hε, hball⟩ :=
          Metric.mem_nhds_iff.mp hsource_mem
        let r : ℝ := ε / 2
        have hr : 0 < r := by positivity
        let K : Set V := Metric.closedBall x r
        have hKsubset : K ⊆ u ∩ (chart.source ∩ phi ⁻¹' q) := by
          intro y hy
          apply hball
          rw [Metric.mem_ball]
          exact hy.trans_lt (by dsimp [r]; linarith)
        let c : Set V :=
          {y | y ∈ K ∧ ¬Function.Surjective (fderiv ℝ f y)}
        have hKcompact : IsCompact K :=
          isCompact_closedBall x r
        have hdfcont : ContinuousOn (fderiv ℝ f) K := by
          intro y hy
          have hyu : y ∈ u := (hKsubset hy).1
          exact ((hf y hyu).contDiffAt (hu.mem_nhds hyu)).fderiv_right (m := 1)
            (by
              change (2 : ℕ∞ω) ≤ ∞
              exact
                (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le) |>.continuousAt.continuousWithinAt
        have hccompact : IsCompact c := by
          exact Helpers.isCompact_not_surjective hKcompact hdfcont
        have hfcont : ContinuousOn f c := by
          exact hf.continuousOn.mono fun y hy => (hKsubset hy.1).1
        have himagecompact : IsCompact (e '' (f '' c)) := by
          exact (hccompact.image_of_continuousOn hfcont).image e.continuous
        have himagemeas : MeasurableSet (e '' (f '' c)) :=
          himagecompact.measurableSet
        have hcnull_split : volume (e '' (f '' c)) = 0 := by
          rw [Measure.volume_eq_prod]
          apply Measure.measure_prod_null_of_ae_null himagemeas
          apply Filter.Eventually.of_forall
          intro a
          let ua : Set A.ker := {z | (a, z) ∈ q}
          have hua : IsOpen ua := by
            exact hqopen.preimage
              (continuous_const.prodMk continuous_id)
          let ha : A.ker → E n :=
            fun z => tail (f (chart.symm (a, z)))
          have hha : ContDiffOn ℝ ∞ ha ua := by
            intro z hz
            have hqgood := hqsub hz
            have hinr : ContDiffAt ℝ ∞
                (fun w : A.ker => (a, w)) z :=
              contDiffAt_const.prodMk contDiffAt_id
            have hphi_z :
                ContDiffAt ℝ ∞ phi (chart.symm (a, z)) := by
              have hg_z : ContDiffAt ℝ ∞ g (chart.symm (a, z)) :=
                ((hf _ hqgood.2.2).contDiffAt
                  (hu.mem_nhds hqgood.2.2)).continuousLinearMap_comp head
              exact hg_z.prodMk P.contDiff.contDiffAt
            have hinv_z : ContDiffAt ℝ ∞ chart.symm (a, z) :=
              Helpers.OpenPartialHomeomorph.contDiffAt_symm_infty_of_one
                chart hqgood.1 (by simpa [chart] using hphi_z) hqgood.2.1
            have hpsi : ContDiffAt ℝ ∞
                (fun w : A.ker => chart.symm (a, w)) z :=
              hinv_z.comp z hinr
            exact ((((hf _ hqgood.2.2).contDiffAt
              (hu.mem_nhds hqgood.2.2)).comp z hpsi).continuousLinearMap_comp
                tail).contDiffWithinAt
          have hhnull :=
            ih ha ua hua hha
          apply measure_mono_null _ hhnull
          intro w hw
          change w ∈ Prod.mk a ⁻¹' (e '' (f '' c)) at hw
          rcases hw with ⟨yout, ⟨y, hyc, rfl⟩, heout⟩
          have hyK : y ∈ K := hyc.1
          have hyN := hKsubset hyK
          have hysource : y ∈ chart.source := hyN.2.1
          have hphiyq : phi y ∈ q := hyN.2.2
          let z : A.ker := (phi y).2
          have hfirst : g y = a := by
            have := congrArg Prod.fst heout
            simpa [g, head, e] using this
          have hpair : (a, z) = phi y := by
            apply Prod.ext
            · simpa [phi] using hfirst.symm
            · rfl
          have hzua : z ∈ ua := by
            change (a, z) ∈ q
            rwa [hpair]
          have hinvy : chart.symm (a, z) = y := by
            rw [hpair]
            exact chart.left_inv hysource
          refine ⟨z, ⟨hzua, ?_⟩, ?_⟩
          · intro hsurjha
            have hqgood := hqsub hzua
            let H : ℝ × A.ker → ℝ × E n :=
              fun p => e (f (chart.symm p))
            have hH : DifferentiableAt ℝ H (a, z) := by
              exact e.differentiableAt.comp (a, z) <|
                ((hf _ hqgood.2.2).contDiffAt
                  (hu.mem_nhds hqgood.2.2)).differentiableAt (by simp) |>.comp (a, z)
                  (hqgood.2.1.differentiableAt (by simp))
            let fstL : (ℝ × E n) →L[ℝ] ℝ :=
              ContinuousLinearMap.fst ℝ ℝ (E n)
            let sndL : (ℝ × E n) →L[ℝ] E n :=
              ContinuousLinearMap.snd ℝ ℝ (E n)
            let inrL : A.ker →L[ℝ] ℝ × A.ker :=
              (0 : A.ker →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ A.ker)
            let DH : (ℝ × A.ker) →L[ℝ] ℝ × E n :=
              fderiv ℝ H (a, z)
            have hlocal_first :
                (fstL ∘ H) =ᶠ[𝓝 (a, z)] Prod.fst := by
              filter_upwards [hqopen.mem_nhds hzua] with p hp
              have hp_good := hqsub hp
              have hright : phi (chart.symm p) = p :=
                chart.right_inv hp_good.1
              have := congrArg Prod.fst hright
              simpa [H, phi, g, head, e, fstL, Function.comp_def] using this
            have hDHfst : fstL.comp DH =
                ContinuousLinearMap.fst ℝ ℝ A.ker := by
              have hder :=
                (fstL.hasFDerivAt.comp (a, z) hH.hasFDerivAt).fderiv
              rw [hlocal_first.fderiv_eq] at hder
              rw [fderiv_fst] at hder
              simpa [fstL, DH] using hder.symm
            have hDHtail :
                fderiv ℝ ha z = sndL.comp (DH.comp inrL) := by
              have hinr_deriv :
                  HasFDerivAt (fun w : A.ker => (a, w)) inrL z := by
                simpa [inrL] using
                  (hasFDerivAt_const (x := z) (c := a)).prodMk
                    (hasFDerivAt_id z)
              have hder :=
                (sndL.hasFDerivAt.comp z
                  (hH.hasFDerivAt.comp z hinr_deriv)).fderiv
              simpa [ha, H, tail, sndL, DH, Function.comp_def] using hder
            have hDHsurj : Function.Surjective DH := by
              intro out
              obtain ⟨v, hv⟩ := hsurjha
                (out.2 - (DH (out.1, 0)).2)
              refine ⟨(out.1, v), ?_⟩
              apply Prod.ext
              · have hfstv := DFunLike.congr_fun hDHfst (out.1, v)
                simpa [fstL] using hfstv
              · have htailv := congrArg (fun L => L v) hDHtail
                rw [hv] at htailv
                have hsum : (out.1, v) =
                    (out.1, (0 : A.ker)) + (0, v) := by
                  ext <;> simp
                have htailv' :
                    (DH (0, v)).2 =
                      out.2 - (DH (out.1, 0)).2 := by
                  rw [htailv]
                  rfl
                rw [hsum, map_add]
                change (DH (out.1, 0)).2 + (DH (0, v)).2 = out.2
                rw [htailv']
                abel
            have hfactor :
                DH = (e : E (n + 1) →L[ℝ] ℝ × E n).comp
                  ((fderiv ℝ f y).comp
                    (fderiv ℝ chart.symm (a, z))) := by
              have hder :=
                (e.hasFDerivAt.comp (a, z) <|
                  (((hf _ hqgood.2.2).contDiffAt
                    (hu.mem_nhds hqgood.2.2)).differentiableAt
                      (by simp) |>.hasFDerivAt.comp
                    (a, z) (hqgood.2.1.differentiableAt (by simp) |>.hasFDerivAt))).fderiv
              simpa [DH, H, hinvy, Function.comp_def] using hder
            apply hyc.2
            intro out
            obtain ⟨v, hv⟩ := hDHsurj (e out)
            refine ⟨fderiv ℝ chart.symm (a, z) v, ?_⟩
            rw [hfactor] at hv
            exact e.injective hv
          · have := congrArg Prod.snd heout
            simpa [ha, tail, e, hinvy] using this
        have hcnull : volume (f '' c) = 0 :=
          volume_eq_zero_of_split_image hcnull_split
        let t : Set V := s₁ ∩ K
        refine ⟨t, ?_, ?_⟩
        · apply inter_mem_nhdsWithin
          exact Metric.closedBall_mem_nhds x hr
        · apply measure_mono_null _ hcnull
          apply image_mono
          intro y hy
          exact ⟨hy.2, hy.1.1.2⟩
      refine measure_mono_null (image_mono hcrit) ?_
      rw [image_union]
      exact measure_union_null hzero hone

theorem sardOn
    {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (f : V → E n) (u : Set V) (hu : IsOpen u)
    (hf : ContDiffOn ℝ ∞ f u) :
    volume (f '' {x | x ∈ u ∧ ¬Function.Surjective (fderiv ℝ f x)}) = 0 :=
  sardOnAux n f u hu hf

theorem sardCritical {m n : ℕ} (f : E m → E n) (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | ¬Function.Surjective (fderiv ℝ f x)}) = 0 := by
  simpa only [mem_univ, true_and] using
    sardOn f univ isOpen_univ hf.contDiffOn

end

end Submission
