import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis.WienerOneOverF
open Set
open scoped ComplexConjugate Real

variable {T : ℝ} [Fact (0 < T)]

namespace Submission

/-ResultProofDefinitionsBegin-/

/-- The change of variables `(n,k) ↦ (k,n-k)` on `ℤ × ℤ`.  Keeping the
change of variables explicit is useful when a product of two absolutely
summable series is regrouped by its Fourier index. -/
private def wienerSubEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by
    rcases p with ⟨n,k⟩
    simp
  right_inv p := by
    rcases p with ⟨k,l⟩
    simp

/-- The convolution of two absolutely summable bilateral complex series is
again absolutely summable.  This is the elementary ``ℓ¹ * ℓ¹ ⊂ ℓ¹``
calculation. We record the absolute statement, since this is the part of
Wiener's algebra which doesn't require any Fourier uniqueness.

The proof uses the non-negative Fubini theorem for series twice. The product
series on `ℤ × ℤ` is summable; the equivalence `(n,k) ↦ (k,n-k)` expresses
its fibres as the convolution coefficients. -/
private lemma wiener_summable_convolution
    (a b : ℤ → ℂ) (ha : Summable a) (hb : Summable b) :
    Summable (fun n : ℤ => ∑' k : ℤ, a k * b (n-k)) := by
  have ha' : Summable (fun n : ℤ => ‖a n‖) := ha.norm
  have hb' : Summable (fun n : ℤ => ‖b n‖) := hb.norm
  -- The absolute product series is summable on the product.
  have hp : Summable (fun p : ℤ × ℤ => ‖a p.1 * b p.2‖) :=
    ha'.mul_norm hb'
  -- Change variables so that the first coordinate is the sum of the
  -- original two coordinates.
  have hnk : Summable (fun p : ℤ × ℤ => ‖a p.2 * b (p.1 - p.2)‖) := by
    -- `summable_iff` makes this just reindexing an unconditional series.
    have h := (wienerSubEquiv.summable_iff
      (f := fun p : ℤ × ℤ => ‖a p.1 * b p.2‖)).2 hp
    simpa [wienerSubEquiv, Function.comp_def] using h
  -- Fubini for a nonnegative real series gives summability of the fibre
  -- sums themselves, as well as absolute summability on each fibre.
  have hnknonneg : 0 ≤ (fun p : ℤ × ℤ => ‖a p.2 * b (p.1 - p.2)‖) :=
    fun _ => norm_nonneg _
  obtain ⟨hfib, hout⟩ :=
    (summable_prod_of_nonneg hnknonneg).1 hnk
  -- On a fibre, the norm-sum dominates the norm of the sum.  This makes
  -- the series of convolution coefficients absolutely summable.
  have hnorm : Summable
      (fun n : ℤ => ‖∑' k : ℤ, a k * b (n-k)‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hout
    intro n
    -- triangle inequality for an absolutely summable series
    have hf : Summable (fun k : ℤ => ‖a k * b (n-k)‖) := by
      simpa using (hfib n)
    exact norm_tsum_le_tsum_norm hf
  exact hnorm.of_norm

private noncomputable def wienerCoeffCLM (n : ℤ) : C(AddCircle T, ℂ) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
    ((fourierBasis (T:=T)).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousMap.toLp 2 (AddCircle.haarAddCircle) ℂ))
lemma wienerCoeffCLM_apply (n:ℤ) (f:C(AddCircle T,ℂ)) :
 wienerCoeffCLM n f = fourierCoeff f n := by
  change (fourierBasis.repr ((ContinuousMap.toLp 2 (AddCircle.haarAddCircle) ℂ) f)) n = _
  rw [fourierBasis_repr, fourierCoeff_toLp]
lemma wiener_terms_summable {a : ℤ → ℂ} (ha: Summable a) : Summable (fun n => a n • (fourier (T:=T) n)) := by
  apply Summable.of_norm
  simpa [norm_smul, fourier_norm] using ha.norm

private noncomputable def wienerSeries (a: ℤ→ℂ) : C(AddCircle T,ℂ) := ∑' n, a n • (fourier n)
lemma wienerSeries_coeff {a:ℤ→ℂ} (ha:Summable a) (m:ℤ) :
    fourierCoeff (wienerSeries (T:=T) a) m = a m := by
  have hs := (wienerCoeffCLM (T:=T) m).hasSum (wiener_terms_summable (T:=T) ha).hasSum
  -- mapped terms
  have term : ∀ n : ℤ,
      wienerCoeffCLM (T:=T) m (a n • fourier n) =
        (a n) * (Pi.single (M:=fun _ : ℤ => ℂ) n (1:ℂ) m) := by
    intro n
    rw [wienerCoeffCLM_apply]
    -- compute coeff of smul
    have hsm := fourierCoeff.const_smul (T:=T)
      (fun x => fourier (T:=T) n x) (a n) m
    have hn : fourierCoeff (fun x => (fourier (T:=T) n x)) m =
        Pi.single (M:=fun _ : ℤ => ℂ) n (1:ℂ) m :=
      congrFun (fourierCoeff_fourier (T:=T) n) m
    change fourierCoeff ((a n) • (fun x => fourier (T:=T) n x)) m =
      _ at hsm
    rw [hn] at hsm
    exact hsm

  have hs' : HasSum
      (fun n : ℤ => a n * Pi.single (M:=fun _ : ℤ => ℂ) n (1:ℂ) m)
      (wienerCoeffCLM (T:=T) m (wienerSeries (T:=T) a)) := by
    simpa [wienerSeries, term] using hs
  have hz : ∀ n : ℤ, n ≠ m ->
      a n * Pi.single (M:=fun _ : ℤ => ℂ) n (1:ℂ) m = 0 := by
    intro n h
    have h' : m ≠ n := Ne.symm h
    simp [Pi.single_eq_of_ne h']
  have ht : (∑' n : ℤ,
      a n * Pi.single (M:=fun _ : ℤ => ℂ) n (1:ℂ) m) = a m := by
    rw [tsum_eq_single m hz]
    simp
  have main : wienerCoeffCLM (T:=T) m (wienerSeries (T:=T) a) = a m :=
    hs'.tsum_eq.symm.trans ht
  simpa [wienerCoeffCLM_apply] using main

lemma wienerSeries_fourierCoeff {T : ℝ} [Fact (0 < T)]
    (f:C(AddCircle T,ℂ)) (hf:Summable (fourierCoeff f)) :
   wienerSeries (T:=T) (fourierCoeff f) = f := by
  unfold wienerSeries
  exact (hasSum_fourier_series_of_summable hf).tsum_eq

lemma wiener_summable_coeff_iff {T : ℝ} [Fact (0 < T)]
    (f:C(AddCircle T,ℂ)) :
 Summable (fourierCoeff f) ↔ ∃ a : ℤ→ℂ, Summable a ∧ wienerSeries (T:=T) a = f := by
 constructor
 · intro hf
   exact ⟨fourierCoeff f, hf, wienerSeries_fourierCoeff f hf⟩
 · rintro ⟨a,ha,rfl⟩
   have hc : fourierCoeff (wienerSeries (T:=T) a) = a := by
     funext m; exact wienerSeries_coeff ha m
   rw [hc]
   exact ha

lemma wienerSeries_mul {a b:ℤ→ℂ} (ha:Summable a) (hb:Summable b) :
 wienerSeries (T:=T) a * wienerSeries (T:=T) b =
   wienerSeries (T:=T) (fun n : ℤ => ∑' k : ℤ, a k * b (n-k)) := by
  -- summability of reshuffled continuous-map series
  have hp0 : Summable (fun p : ℤ × ℤ => ‖a p.1 * b p.2‖) := ha.norm.mul_norm hb.norm
  have hp : Summable (fun p : ℤ × ℤ => ‖a p.2 * b (p.1-p.2)‖) := by
    have h := (wienerSubEquiv.summable_iff
      (f := fun p : ℤ × ℤ => ‖a p.1 * b p.2‖)).2 hp0
    simpa [wienerSubEquiv, Function.comp_def] using h
  have hfib : ∀ n : ℤ, Summable (fun k : ℤ => ‖a k * b (n-k)‖) := by
    have := (summable_prod_of_nonneg (f:=fun p : ℤ × ℤ => ‖a p.2 * b (p.1-p.2)‖)
      (fun _ => norm_nonneg _)).1 hp
    simpa using this.1
  -- work pointwise with scalar series
  ext x
  change (wienerSeries (T:=T) a) x * (wienerSeries (T:=T) b) x = _
  -- evaluate each outer series
  have evalser (c:ℤ→ℂ) (hc:Summable c) :
      (wienerSeries (T:=T) c) x = ∑' n : ℤ, c n * fourier (T:=T) n x := by
    unfold wienerSeries
    -- evaluation CLM
    have ev := (ContinuousMap.evalCLM ℂ x).map_tsum (wiener_terms_summable (T:=T) hc)
    simpa [smul_eq_mul] using ev
  rw [evalser a ha, evalser b hb,
      evalser _ (wiener_summable_convolution a b ha hb)]
  have hnormterm (c:ℤ→ℂ) (hc:Summable c) :
      Summable (fun n : ℤ => ‖c n * fourier (T:=T) n x‖) := by
    simpa [norm_mul, fourier_apply, Circle.norm_coe] using hc.norm
  rw [tsum_mul_tsum_of_summable_norm (hnormterm a ha) (hnormterm b hb)]
  -- reindex product to (sum,index)
  have htr (k l : ℤ) :
      (a k * fourier (T:=T) k x) * (b l * fourier (T:=T) l x) =
        (a k * b l) * fourier (T:=T) (k+l) x := by
    rw [fourier_add]
    ring
  simp_rw [htr]
  -- summable on the changed variables (the character has norm one)
  have hpC : Summable (fun p : ℤ × ℤ =>
       (a p.2 * b (p.1-p.2)) * fourier (T:=T) p.1 x) := by
    apply Summable.of_norm
    simpa [norm_mul, fourier_apply, Circle.norm_coe] using hp
  -- change variables in the product sum
  rw [← (wienerSubEquiv.tsum_eq
       (fun p : ℤ × ℤ => (a p.1 * b p.2) * fourier (T:=T) (p.1+p.2) x))]
  change (∑' p : ℤ × ℤ,
       (a p.2 * b (p.1-p.2)) * fourier (T:=T)
          (p.2 + (p.1-p.2)) x) = _
  have heq (q : ℤ × ℤ) : q.2 + (q.1 - q.2) = q.1 := by omega
  simp_rw [heq]
  rw [hpC.tsum_prod]
  congr 1
  funext n
  rw [Summable.tsum_mul_right (fourier (T:=T) n x)
       ((hfib n).of_norm)]



lemma wiener_mul_closed {T : ℝ} [Fact (0 < T)] (f g : C(AddCircle T,ℂ))
    (hf : Summable (fourierCoeff f)) (hg : Summable (fourierCoeff g)) :
    Summable (fourierCoeff (f*g)) := by
  let a : ℤ → ℂ := fourierCoeff f
  let b : ℤ → ℂ := fourierCoeff g
  have ha : Summable a := hf
  have hb : Summable b := hg
  let c : ℤ → ℂ := fun n : ℤ => ∑' k : ℤ, a k * b (n-k)
  have hc : Summable c := wiener_summable_convolution a b ha hb
  have eqn : f * g = wienerSeries (T:=T) c := by
    rw [← wienerSeries_fourierCoeff f hf, ← wienerSeries_fourierCoeff g hg]
    exact wienerSeries_mul ha hb
  rw [eqn]
  have he : fourierCoeff (wienerSeries (T:=T) c) = c := by
    funext n
    exact wienerSeries_coeff hc n
  rw [he]
  exact hc

lemma wienerSeries_single_zero {T : ℝ} [Fact (0 < T)] :
    wienerSeries (T:=T) (Pi.single 0 (1:ℂ)) = 1 := by
  unfold wienerSeries
  rw [tsum_eq_single 0]
  · ext x
    simp [fourier_apply]
  intro n hn
  simp [Pi.single_eq_of_ne hn]



-- The Banach algebra `ℓ¹(ℤ)` with convolution.
private noncomputable abbrev WS := lp (fun _ : ℤ => ℂ) 1
private lemma ws_summable (u : WS) : Summable (fun n : ℤ => u n) :=
  Memℓp.summable_of_one u.2
private noncomputable def wsOf (u : ℤ → ℂ) (hu : Summable u) : WS :=
  ⟨u, by
    apply memℓp_gen
    simpa using hu.norm⟩
@[simp] private lemma wsOf_apply (u : ℤ → ℂ) (hu) (n:ℤ) : wsOf u hu n = u n := rfl

private noncomputable def wsMul (u v : WS) : WS :=
  wsOf (fun n : ℤ => ∑' k : ℤ, u k * v (n-k))
    (wiener_summable_convolution _ _ (ws_summable u) (ws_summable v))
private noncomputable instance : Mul WS := ⟨wsMul⟩
private noncomputable instance : One WS := ⟨lp.single 1 0 (1:ℂ)⟩
@[simp] private lemma ws_mul_apply (u v:WS) (n:ℤ) :
    (u*v) n = ∑' k : ℤ, u k * v (n-k) := rfl
private lemma ws_one_apply (n:ℤ) : (1:WS) n = Pi.single (M:=fun _ : ℤ => ℂ) 0 (1:ℂ) n := rfl

private noncomputable def wsSeries (u : WS) : C(AddCircle (1:ℝ),ℂ) :=
  wienerSeries (T:=(1:ℝ)) (fun n : ℤ => u n)
private lemma wsSeries_inj : Function.Injective wsSeries := by
  intro u v h
  apply lp.ext
  funext n
  have hn := congrArg (fun q : C(AddCircle (1:ℝ),ℂ) => fourierCoeff q n) h
  simpa [wsSeries, wienerSeries_coeff (ws_summable u),
    wienerSeries_coeff (ws_summable v)] using hn
private lemma wsSeries_add (u v:WS) : wsSeries (u+v) = wsSeries u + wsSeries v := by
  unfold wsSeries wienerSeries
  rw [← Summable.tsum_add (wiener_terms_summable (T:=(1:ℝ)) (ws_summable u))
      (wiener_terms_summable (T:=(1:ℝ)) (ws_summable v))]
  congr 1; funext n
  exact add_smul (u n) (v n) (fourier n)
private lemma wsSeries_zero : wsSeries (0:WS) = 0 := by
  have h := wsSeries_add (0:WS) 0
  simpa using h
private lemma wsSeries_neg (u:WS) : wsSeries (-u) = - wsSeries u := by
  apply add_left_cancel (a:=wsSeries u)
  rw [← wsSeries_add]
  simp [wsSeries_zero]
private lemma wsSeries_sub (u v:WS) : wsSeries (u-v) = wsSeries u - wsSeries v := by
  simpa [sub_eq_add_neg, wsSeries_neg] using wsSeries_add u (-v)
private lemma wsSeries_mul (u v:WS) : wsSeries (u*v) = wsSeries u * wsSeries v := by
  symm
  exact wienerSeries_mul (T:=(1:ℝ)) (ws_summable u) (ws_summable v)
private lemma wsSeries_one : wsSeries (1:WS) = 1 :=
  wienerSeries_single_zero (T:=(1:ℝ))

-- Put the transported ring structure on `WS`.
private noncomputable instance : NatCast WS := ⟨fun n => n • (1:WS)⟩
private noncomputable instance : IntCast WS := ⟨fun n => n • (1:WS)⟩
private noncomputable instance : Pow WS ℕ := ⟨fun u n => npowRec n u⟩
private lemma wsSeries_nsmul (n:ℕ) (u:WS) : wsSeries (n • u) = n • wsSeries u := by
  induction n with
  | zero => simp [wsSeries_zero]
  | succ n ih =>
      rw [succ_nsmul, succ_nsmul, wsSeries_add, ih]
private lemma wsSeries_zsmul (n:ℤ) (u:WS) : wsSeries (n • u) = n • wsSeries u := by
  cases n with
  | ofNat n => simpa using wsSeries_nsmul n u
  | negSucc n =>
      rw [negSucc_zsmul, negSucc_zsmul, wsSeries_neg, wsSeries_nsmul]
private lemma wsSeries_npow (u:WS) (n:ℕ) : wsSeries (u^n) = wsSeries u ^ n := by
  induction n with
  | zero => change wsSeries 1 = 1; exact wsSeries_one
  | succ n ih => change wsSeries (u^n * u) = _; rw [wsSeries_mul, ih, pow_succ]

private noncomputable instance wsCommRing : CommRing WS :=
  Function.Injective.commRing wsSeries wsSeries_inj
    wsSeries_zero wsSeries_one wsSeries_add wsSeries_mul wsSeries_neg wsSeries_sub
    wsSeries_nsmul wsSeries_zsmul wsSeries_npow
    (fun n => (wsSeries_nsmul n (1:WS)).trans (by rw [wsSeries_one]; simp [nsmul_eq_mul]))
    (fun n => (wsSeries_zsmul n (1:WS)).trans (by rw [wsSeries_one]; simp [zsmul_eq_mul]))

private lemma ws_norm (u:WS) : ‖u‖ = ∑' n : ℤ, ‖u n‖ := by
  simp [lp.norm_eq_tsum_rpow]
private lemma ws_norm_mul_le (u v:WS) : ‖u*v‖ ≤ ‖u‖ * ‖v‖ := by
  have hu := (ws_summable u).norm
  have hv := (ws_summable v).norm
  have hp0 : Summable (fun p : ℤ × ℤ => ‖u p.1 * v p.2‖) := hu.mul_norm hv
  have hp : Summable (fun p : ℤ × ℤ => ‖u p.2 * v (p.1-p.2)‖) := by
    have h := (wienerSubEquiv.summable_iff
      (f:=fun p : ℤ × ℤ => ‖u p.1 * v p.2‖)).2 hp0
    simpa [wienerSubEquiv, Function.comp_def] using h
  obtain ⟨hfib, hout⟩ :=
    (summable_prod_of_nonneg
      (f:=fun p : ℤ × ℤ => ‖u p.2 * v (p.1-p.2)‖)
      (fun _ => norm_nonneg _)).1 hp
  rw [ws_norm, ws_norm, ws_norm]
  calc
    (∑' n : ℤ, ‖(u*v) n‖) ≤
        ∑' n : ℤ, (∑' k : ℤ, ‖u k * v (n-k)‖) := by
      apply Summable.tsum_le_tsum
      · intro n; rw [ws_mul_apply]; exact norm_tsum_le_tsum_norm (by simpa using (hfib n))
      · exact (ws_summable (u*v)).norm
      · simpa using hout
    _ = ∑' p : ℤ × ℤ, ‖u p.2 * v (p.1-p.2)‖ := by rw [hp.tsum_prod]
    _ = ∑' p : ℤ × ℤ, ‖u p.1 * v p.2‖ := by
      exact (wienerSubEquiv.tsum_eq (fun p : ℤ × ℤ => ‖u p.1 * v p.2‖))
    _ = _ := by
      rw [hp0.tsum_prod]
      simp_rw [norm_mul]
      have hm : Summable (fun p : ℤ × ℤ => ‖u p.1‖ * ‖v p.2‖) := by simpa [norm_mul] using hp0
      rw [← hm.tsum_prod, ← Summable.tsum_mul_tsum hu hv hm]
private noncomputable instance wsNormedCommRing : NormedCommRing WS :=
  { wsCommRing with
    toMetricSpace := inferInstance
    dist_eq := fun x y => by rw [dist_eq_norm]; change ‖x - y‖ = ‖-x + y‖; rw [norm_sub_rev]; congr 1 <;> abel
    norm_mul_le := ws_norm_mul_le }

private lemma wsSeries_smul (c:ℂ) (u:WS) : wsSeries (c • u) = c • wsSeries u := by
  unfold wsSeries wienerSeries
  rw [← Summable.tsum_const_smul c (wiener_terms_summable (T:=(1:ℝ)) (ws_summable u))]
  congr 1; funext n
  simp [lp.coeFn_smul, mul_smul]

private noncomputable instance wsAlgebra : Algebra ℂ WS :=
  Algebra.ofModule
    (fun c u v => wsSeries_inj <| by
      rw [wsSeries_mul, wsSeries_smul, wsSeries_smul, wsSeries_mul]
      ext x; change _; simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm])
    (fun c u v => wsSeries_inj <| by
      rw [wsSeries_mul, wsSeries_smul, wsSeries_smul, wsSeries_mul]
      ext x; change _; simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm])
private noncomputable instance wsNormedAlgebra : NormedAlgebra ℂ WS where
  norm_smul_le := norm_smul_le

private noncomputable def wsDelta (n:ℤ) : WS := lp.single 1 n (1:ℂ)
@[simp] private lemma wsDelta_apply (n j:ℤ) : wsDelta n j = Pi.single (M:=fun _ : ℤ => ℂ) n (1:ℂ) j := rfl
private lemma wsDelta_norm (n:ℤ) : ‖wsDelta n‖ = 1 := by
  simpa [wsDelta] using (lp.norm_single (p:=(1:ENNReal)) (by norm_num) n (1:ℂ))
private lemma wsSeries_delta (n:ℤ) : wsSeries (wsDelta n) = fourier (T:=(1:ℝ)) n := by
  unfold wsSeries wienerSeries wsDelta
  rw [tsum_eq_single n]
  · simp
  intro j hj
  change (Pi.single (M:=fun _ : ℤ => ℂ) n (1:ℂ) j) • (fourier (T:=(1:ℝ)) j) = 0
  have h0 : Pi.single (M:=fun _ : ℤ => ℂ) n (1:ℂ) j = 0 := by
    classical
    simp [hj]
  rw [h0]
  ext x
  simp
private lemma wsDelta_add (m n:ℤ) : wsDelta m * wsDelta n = wsDelta (m+n) := by
  apply wsSeries_inj
  rw [wsSeries_mul, wsSeries_delta, wsSeries_delta, wsSeries_delta]
  ext x
  exact (fourier_add (m:=m) (n:=n) (x:=x)).symm
private lemma wsDelta_zero : wsDelta 0 = (1:WS) := rfl

/-- The point masses form the usual absolutely convergent expansion of an `ℓ¹` vector. -/
private lemma ws_summable_delta (u : WS) :
    Summable (fun n : ℤ => (u n) • wsDelta n) := by
  apply Summable.of_norm
  simpa [norm_smul, wsDelta_norm] using (ws_summable u).norm

private lemma ws_hasSum_delta (u : WS) :
    HasSum (fun n : ℤ => (u n) • wsDelta n) u := by
  have hs := ws_summable_delta u
  have heq : (∑' n : ℤ, (u n) • wsDelta n) = u := by
    apply lp.ext
    funext j
    have hm := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 j).map_tsum hs
    have hzero : ∀ n : ℤ, n ≠ j ->
        u n * (Pi.single (M:=fun _ : ℤ => ℂ) n (1:ℂ) j) = 0 := by
      intro n hn
      have hjn : j ≠ n := Ne.symm hn
      simp [Pi.single_eq_of_ne hjn]
    have ht : (∑' n : ℤ, u n *
        (Pi.single (M:=fun _ : ℤ => ℂ) n (1:ℂ) j)) = u j := by
      rw [tsum_eq_single j hzero]
      simp
    -- evaluation is continuous on `lp`; on a point mass it is just its coordinate
    have heval (n : ℤ) :
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 j) (wsDelta n) =
          (Pi.single (M:=fun _ : ℤ => ℂ) n (1:ℂ) j) := by
      change (wsDelta n : ℤ → ℂ) j = _
      rfl
    -- spell out the two evaluation maps, so the right hand side is `ht`
    change ((∑' n : ℤ, (u n) • wsDelta n) : WS) j = _ at hm
    simpa [lp.coeFn_smul, heval, ht, smul_eq_mul] using hm
  have hres := hs.hasSum
  rw [heq] at hres
  exact hres

/-- A character of the convolution algebra has the value `z^n` on `δ_n`.
    We prove the two signs separately; no spectral theory is used here. -/
private lemma ws_char_delta_zpow (φ : WeakDual.characterSpace ℂ WS) :
    ∀ n : ℤ, φ (wsDelta n) = (φ (wsDelta (1:ℤ))) ^ n := by
  let ψ : WS →ₐ[ℂ] ℂ := WeakDual.CharacterSpace.equivAlgHom φ
  have hmul (m n : ℤ) :
      φ (wsDelta (m+n)) = φ (wsDelta m) * φ (wsDelta n) := by
    have h := congrArg (fun q : WS => φ q) (wsDelta_add m n)
    -- `ψ` and `φ` have the same underlying function
    have hm' : φ (wsDelta m * wsDelta n) =
        φ (wsDelta m) * φ (wsDelta n) := by
      exact map_mul ψ _ _
    rw [hm'] at h
    exact h.symm
  have hone : φ (wsDelta 0) = 1 := by
    rw [wsDelta_zero]
    exact map_one ψ
  have hinv (n : ℤ) : φ (wsDelta n) * φ (wsDelta (-n)) = 1 := by
    rw [← hmul]
    simpa using hone
  have hne (n : ℤ) : φ (wsDelta n) ≠ 0 := by
    intro hn
    have h := hinv n
    rw [hn, zero_mul] at h
    exact zero_ne_one h
  have hnat : ∀ k : ℕ, φ (wsDelta (Int.ofNat k)) =
        (φ (wsDelta (1:ℤ))) ^ k := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih =>
      have hk : (Int.ofNat (Nat.succ k)) = (Int.ofNat k) + (1:ℤ) := by
        simp
      rw [hk, hmul, ih]
      -- the target power is a natural power on the right
      simp [pow_succ]
  intro n
  cases n with
  | ofNat k =>
      simpa using hnat k
  | negSucc k =>
      -- use `δ_m * δ_{-m}=1`
      let m : ℤ := Int.ofNat (k+1)
      have hmneg : -m = Int.negSucc k := by
        simp [m, Int.ofNat_eq_coe]
        omega
      have hmprod := hinv m
      have hmn := hne m
      have hpos := hnat (k+1)
      have hsolve : φ (wsDelta (Int.negSucc k)) =
          ((φ (wsDelta (1:ℤ))) ^ (k+1))⁻¹ := by
        rw [hmneg] at hmprod
        rw [hpos] at hmprod
        have hpne : (φ (wsDelta (1:ℤ))) ^ (k+1) ≠ 0 := by
          have hhpos : φ (wsDelta (Int.ofNat (k+1))) ≠ 0 := hne _
          intro hz
          exact hhpos (hpos.trans hz)
        have hh := (mul_eq_one_iff_inv_eq₀ hpne).1 hmprod
        exact hh.symm
      simpa [zpow_negSucc] using hsolve

/-- Evaluating a character commutes with the absolutely convergent expansion in
point masses. This is the only continuity step in the character computation. -/
private lemma ws_char_apply (φ : WeakDual.characterSpace ℂ WS) (u : WS) :
    φ u = ∑' n : ℤ, (u n) * (φ (wsDelta (1:ℤ))) ^ n := by
  let ψ : WS →ₐ[ℂ] ℂ := WeakDual.CharacterSpace.equivAlgHom φ
  have hm := ψ.toContinuousLinearMap.hasSum (ws_hasSum_delta u)
  change HasSum (fun n : ℤ => ψ.toContinuousLinearMap ((u n) • wsDelta n)) (φ u) at hm
  have hterm (n : ℤ) :
      ψ.toContinuousLinearMap ((u n) • wsDelta n) =
        (u n) * (φ (wsDelta (1:ℤ))) ^ n := by
    change φ ((u n) • wsDelta n) = _
    have h := map_smul ψ (u n) (wsDelta n)
    change φ ((u n) • wsDelta n) = (u n) • φ (wsDelta n) at h
    rw [h, ws_char_delta_zpow]
    rfl
  have hh : HasSum (fun n : ℤ => (u n) * (φ (wsDelta (1:ℤ))) ^ n) (φ u) := by
    -- rewrite each summand in the mapped series
    simpa only [hterm] using hm
  exact hh.tsum_eq.symm


/-- Evaluation of the uniformly absolutely convergent Fourier series. -/
private lemma wienerSeries_apply' {T : ℝ} [Fact (0 < T)] (a : ℤ → ℂ)
    (ha : Summable a) (x : AddCircle T) :
    (wienerSeries (T:=T) a) x =
      ∑' n : ℤ, a n * (fourier (T:=T) n) x := by
  unfold wienerSeries
  have hev := (ContinuousMap.evalCLM ℂ x).map_tsum
      (wiener_terms_summable (T:=T) ha)
  simpa [smul_eq_mul] using hev

/-ResultProofDefinitionsEnd-/


theorem wiener_inverse_closed (f : C(AddCircle T, ℂ))
    (hf : InWienerAlgebra f) (hzero : ∀ x, f x ≠ 0) :
    ∃ g : C(AddCircle T, ℂ),
      (∀ x, g x = (f x)⁻¹) ∧ InWienerAlgebra g := by
  let g : C(AddCircle T, ℂ) :=
    ⟨(fun x => (f x)⁻¹),
      (Continuous.inv₀ f.continuous hzero)⟩
  refine ⟨g, ?_, ?_⟩
  · intro x
    rfl
  change Summable (fourierCoeff g)
  -- It is enough to invert in the coefficient algebra: uniqueness of an
  -- algebraic inverse recovers the pointwise reciprocal above.
  have hf' : Summable (fourierCoeff f) := hf
  have hunit : ∃ k : C(AddCircle T, ℂ),
        Summable (fourierCoeff k) ∧ f * k = 1 := by
    -- At this point all the analytic/Fourier bookkeeping has reduced the
    -- remaining Wiener lemma to invertibility in the bilateral `ℓ¹`
    -- convolution algebra.
    let a : ℤ → ℂ := fourierCoeff f
    have ha : Summable a := hf'
    have hana : ∀ x, wienerSeries (T:=T) a x ≠ 0 := by
      intro x
      rw [wienerSeries_fourierCoeff f hf']
      exact hzero x
    have hconv : ∃ b : ℤ → ℂ, Summable b ∧
        (fun n : ℤ => ∑' j : ℤ, a j * b (n-j)) = Pi.single 0 (1:ℂ) := by
      -- Work in the complete convolution algebra `WS = ℓ¹(ℤ)`.
      let u : WS := wsOf a ha
      have hu : IsUnit u := by
        by_contra hn
        obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero (A:=WS) hn
        have char_bound (v:WS) : ‖φ v‖ ≤ ‖v‖ := by
          have h := spectrum.norm_le_norm_mul_of_mem (AlgHom.apply_mem_spectrum
            (WeakDual.CharacterSpace.equivAlgHom φ) v)
          have honeN : ‖(1:WS)‖ = 1 := by
            change ‖(show WS from lp.single (1:ENNReal) (0:ℤ) (1:ℂ))‖ = _
            simp [lp.norm_single (p:=(1:ENNReal)) (by norm_num)]
          simpa [honeN] using h
        have hd (n:ℤ) : φ (wsDelta n) * φ (wsDelta (-n)) = 1 := by
          rw [← map_mul, wsDelta_add]
          simp [wsDelta_zero]
        have hdle (n:ℤ) : ‖φ (wsDelta n)‖ ≤ 1 := by
          simpa [wsDelta_norm] using char_bound (wsDelta n)
        have hdabs (n:ℤ) : ‖φ (wsDelta n)‖ = 1 := by
          have hm := hd n
          have habs : ‖φ (wsDelta n)‖ * ‖φ (wsDelta (-n))‖ = 1 := by
            rw [← norm_mul, hm, norm_one]
          have h1 := hdle n
          have h2 := hdle (-n)
          have hnon := norm_nonneg (φ (wsDelta n))
          nlinarith [norm_nonneg (φ (wsDelta (-n)))]
        -- A norm-one complex number is a point of the circle.
        let z : Circle := ⟨φ (wsDelta (1:ℤ)),
          (mem_sphere_zero_iff_norm).2 (hdabs (1:ℤ))⟩
        have hT : T ≠ 0 := ne_of_gt (Fact.out : 0 < T)
        let x : AddCircle T := (AddCircle.homeomorphCircle hT).symm z
        have hx : AddCircle.toCircle x = z := by
          calc
            AddCircle.toCircle x = AddCircle.homeomorphCircle hT x :=
              (AddCircle.homeomorphCircle_apply hT x).symm
            _ = z := (AddCircle.homeomorphCircle hT).apply_symm_apply z
        have hfour (n : ℤ) : (fourier (T:=T) n) x =
            (φ (wsDelta (1:ℤ))) ^ n := by
          rw [fourier_apply, AddCircle.toCircle_zsmul, hx, Circle.coe_zpow]
        have hseries : φ u = wienerSeries (T:=T) a x := by
          rw [ws_char_apply φ u, wienerSeries_apply' a ha x]
          congr 1
          funext n
          rw [hfour n]
          rfl
        apply (hana x)
        rw [← hseries]
        exact hφ
      obtain ⟨v, hv⟩ := hu
      refine ⟨(fun n : ℤ => ((v⁻¹ : WSˣ) : WS) n), ws_summable ((v⁻¹ : WSˣ) : WS), ?_⟩
      funext n
      have heq : u * ((v⁻¹ : WSˣ) : WS) = 1 := by
        rw [← hv]
        change (v : WS) * (↑(v⁻¹) : WS) = 1
        exact Units.mul_inv v
      have hn := congrArg (fun q : WS => q n) heq
      simpa [ws_mul_apply, ws_one_apply, u, wsOf] using hn
    obtain ⟨b, hb, hab⟩ := hconv
    refine ⟨wienerSeries (T:=T) b, ?_, ?_⟩
    · have he : fourierCoeff (wienerSeries (T:=T) b) = b := by
        funext n
        exact wienerSeries_coeff hb n
      rw [he]
      exact hb
    · rw [← wienerSeries_fourierCoeff f hf']
      rw [wienerSeries_mul ha hb]
      rw [hab]
      exact wienerSeries_single_zero
  obtain ⟨k, hk, hk1⟩ := hunit
  have keq : k = g := by
    ext x
    change k x = (f x)⁻¹
    apply (mul_left_cancel₀ (hzero x))
    have hpoint : f x * k x = 1 := by
      have h := congrArg (fun u : C(AddCircle T, ℂ) => u x) hk1
      simpa using h
    simpa [mul_inv_cancel₀ (hzero x)] using hpoint
  simpa [keq] using hk


end Submission
