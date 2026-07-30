import Mathlib
namespace Submission

open scoped Matrix Topology BigOperators
open Filter NormedSpace
noncomputable section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
lemma exp_apply_nil {m:Type*} [Fintype m] [DecidableEq m]
 (N:Matrix m m ℂ) (w:m→ℂ) (k:ℕ) (hk:(N^k).mulVec w=0) (t:ℝ) :
 (exp ((t:ℝ) • N)).mulVec w =
   ∑ i ∈ Finset.range k, (((i.factorial:ℂ)⁻¹ * (t:ℂ)^i) • ((N^i).mulVec w)) := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] (m→ℂ) :=
    { toFun := fun M => M.mulVec w
      map_add' := fun X Y => Matrix.add_mulVec X Y w
      map_smul' := fun c X => Matrix.smul_mulVec c X w }
  let L : Matrix m m ℂ →L[ℂ] (m→ℂ) := LinearMap.toContinuousLinearMap L0
  have pow0 : ∀ j : ℕ, k ≤ j → (N^j).mulVec w = 0 := by
    intro j h
    obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm, pow_add]
    rw [← Matrix.mulVec_mulVec w]
    rw [hk, Matrix.mulVec_zero]
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂:=ℂ) ((t:ℝ) • N)
  have hs' := L.hasSum hs
  have eq1 := hs'.tsum_eq
  change (∑' i:ℕ, L (((i.factorial:ℂ)⁻¹) • (((t:ℝ) • N)^i))) = _ at eq1
  change L (exp _) = _
  trans ∑' i:ℕ, L (((i.factorial:ℂ)⁻¹) • (((t:ℝ) • N)^i))
  · exact eq1.symm
  -- finite terms
  rw [tsum_eq_sum (s := Finset.range k) (by
    intro j hnot
    have hj : k ≤ j := Nat.le_of_not_gt (fun hlt => hnot (Finset.mem_range.mpr hlt))
    dsimp [L, L0]
    rw [smul_pow, Matrix.smul_mulVec]
    rw [Matrix.smul_mulVec]
    simp [pow0 j hj])]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [L, L0]
  rw [smul_pow]
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec]
  -- scalars assoc
  ext r
  simp [smul_eq_mul]
  ring
lemma exp_apply_gen {m:Type*} [Fintype m] [DecidableEq m]
 (B:Matrix m m ℂ) (μ:ℂ) (w:m→ℂ) (k:ℕ)
 (hk:((B - μ • (1:Matrix m m ℂ))^k).mulVec w=0) (t:ℝ) :
 (exp ((t:ℝ) • B)).mulVec w =
   ∑ i ∈ Finset.range k, ((Complex.exp ((t:ℂ)*μ) * ((i.factorial:ℂ)⁻¹ * (t:ℂ)^i)) • (((B-μ • (1:Matrix m m ℂ))^i).mulVec w)) := by
 let D : Matrix m m ℂ := μ • (1:Matrix m m ℂ)
 let N : Matrix m m ℂ := B - D
 have BN : B = D + N := by dsimp [N,D]; abel
 have comm : Commute ((t:ℝ) • D) ((t:ℝ) • N) := by
   -- D central
   have hd : ∀ X : Matrix m m ℂ, Commute D X := by
     intro X
     exact (Commute.one_left X).smul_left μ
   exact ((hd N).smul_left t).smul_right t
 rw [BN, smul_add, Matrix.exp_add_of_commute _ _ comm]
 -- action splits
 rw [← Matrix.mulVec_mulVec w]
 rw [exp_apply_nil N w k (by simpa [N,D] using hk) t]
 rw [Matrix.mulVec_sum]
 apply Finset.sum_congr rfl
 intro i hi
 -- expD = diagonal
 have ed : exp ((t:ℝ) • D) = Matrix.diagonal (fun _ : m => Complex.exp ((t:ℂ)*μ)) := by
   have eqd : (t:ℝ) • D = Matrix.diagonal (fun _ : m => (t:ℂ)*μ) := by
     ext a b
     classical
     by_cases h : a=b
     · subst b; simp [D]
     · simp [D, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]
   rw [eqd, Matrix.exp_diagonal]
   ext a
   simp [Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
 rw [ed]
 ext r
 rw [Matrix.mulVec_diagonal]
 dsimp
 have hh : D + N - μ • (1:Matrix m m ℂ) = N := by
   change D + N - D = N
   abel
 simp [hh]
 -- scalar arithmetic
 ring
lemma complex_poly_exp {a:ℂ} (ha:a.re<0) (k:ℕ) :
 Filter.Tendsto (fun t:ℝ => (t:ℂ)^k * Complex.exp ((t:ℂ)*a)) Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) (-a.re) (neg_pos.mpr ha)
  have h' : Filter.Tendsto (fun t:ℝ => t^k * Real.exp (a.re*t)) Filter.atTop (nhds 0) := by
    simpa [Real.rpow_natCast] using h
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  simp [norm_mul, Complex.norm_exp, abs_of_nonneg ht, Complex.mul_re, mul_comm, ht]
lemma exp_gen_tendsto {m:Type*} [Fintype m] [DecidableEq m]
 (B:Matrix m m ℂ) (μ:ℂ) (hμ:μ.re<0) (w:m→ℂ) (k:ℕ)
 (hk:((B - μ • (1:Matrix m m ℂ))^k).mulVec w=0) :
 Filter.Tendsto (fun t:ℝ => (exp ((t:ℝ) • B)).mulVec w) Filter.atTop (nhds 0) := by
 let f : ℕ → ℝ → (m→ℂ) := fun i t =>
    ((Complex.exp ((t:ℂ)*μ) * ((i.factorial:ℂ)⁻¹ * (t:ℂ)^i)) •
       (((B-μ • (1:Matrix m m ℂ))^i).mulVec w))
 have hi (i:ℕ) : Filter.Tendsto (f i) Filter.atTop (nhds 0) := by
   have hp := complex_poly_exp hμ i
   have hp' : Filter.Tendsto
       (fun t:ℝ => Complex.exp ((t:ℂ)*μ) * ((i.factorial:ℂ)⁻¹ * (t:ℂ)^i))
       Filter.atTop (nhds 0) := by
     convert (hp.const_mul ((i.factorial:ℂ)⁻¹)) using 1
     · ext t;  ring
     · simp
   convert hp'.smul_const (((B-μ • (1:Matrix m m ℂ))^i).mulVec w) using 1 <;> simp [f]
 have hs : Filter.Tendsto (fun t:ℝ => ∑ i ∈ Finset.range k, f i t)
       Filter.atTop (nhds (∑ i ∈ Finset.range k, (0: (m→ℂ)))) := by
    exact tendsto_finset_sum (Finset.range k) (fun i _ => hi i)
 have hz : Filter.Tendsto (fun t:ℝ => ∑ i ∈ Finset.range k, f i t)
       Filter.atTop (nhds 0) := by simpa using hs
 refine hz.congr' ?_
 filter_upwards [] with t
 exact (exp_apply_gen B μ w k hk t).symm



/-- Over the complex numbers the whole finite-dimensional coordinate space is spanned
by generalized eigenspaces.  We keep the sum as a `Finsupp`; its finite support
is precisely what will be used to take limits later.  Notice that only the
non-zero summands assert an eigenvalue, so that the zero-dimensional case and
the zero summands cause no choice of eigenvalue. -/
lemma matrix_exists_generalized_sum {m : Type*} [Fintype m] [DecidableEq m]
 (B : Matrix m m ℂ) (w : m → ℂ) :
 ∃ (g : ℂ →₀ (m → ℂ)),
   (∀ μ : ℂ, ∃ k : ℕ, ((B - μ • (1 : Matrix m m ℂ)) ^ k).mulVec (g μ) = 0) ∧
   (∀ μ : ℂ, g μ ≠ 0 → Module.End.HasEigenvalue (Matrix.toLin' B) μ) ∧
   (g.sum (fun _ v => v) = w) := by
 classical
 let f : Module.End ℂ (m → ℂ) := Matrix.toLin' B
 -- The algebraically closed-field theorem gives spanning by maximal
 -- generalized eigenspaces.  Membership in an `iSup` can be recorded as a
 -- finitely supported sum.
 have hw : w ∈ ⨆ μ : ℂ, f.maxGenEigenspace μ := by
   rw [Module.End.iSup_maxGenEigenspace_eq_top]
   trivial
 obtain ⟨g, hmem, hsum⟩ :=
   (Submodule.mem_iSup_iff_exists_finsupp
       (fun μ : ℂ => f.maxGenEigenspace μ) w).1 hw
 refine ⟨g, ?_, ?_, hsum⟩
 · intro μ
   obtain ⟨k, hk⟩ :=
     (Module.End.mem_maxGenEigenspace f μ (g μ)).1 (hmem μ)
   refine ⟨k, ?_⟩
   -- Transfer the iterate of the endomorphism to a power of the matrix.
   have hh : Matrix.toLin' (B - μ • (1 : Matrix m m ℂ)) =
        f - μ • (1 : Module.End ℂ (m → ℂ)) := by
       dsimp [f]
       simp [Module.End.one_eq_id]
   have heq : (((f - μ • (1 : Module.End ℂ (m → ℂ))) ^ k) (g μ)) =
            ((B - μ • (1 : Matrix m m ℂ)) ^ k).mulVec (g μ) := by
       rw [← hh]
       rw [← Matrix.toLin'_pow]
       rfl
   rw [← heq]
   exact hk
 · intro μ hne
   -- A nonzero element of a generalized eigenspace is a generalized
   -- eigenvector.  Generalized eigenvalues are ordinary eigenvalues.
   obtain ⟨k, hk⟩ :=
     (Module.End.mem_maxGenEigenspace f μ (g μ)).1 (hmem μ)
   have hker : g μ ∈ LinearMap.ker
       ((f - μ • (1 : Module.End ℂ (m → ℂ))) ^ k) :=
     (LinearMap.mem_ker).2 hk
   have hgen : g μ ∈ f.genEigenspace μ (k : ℕ) :=
       (Module.End.mem_genEigenspace_nat).2 hker
   have hvec : f.HasGenEigenvector μ k (g μ) :=
       (Module.End.hasGenEigenvector_iff).2 ⟨hgen, hne⟩
   have heg : f.HasGenEigenvalue μ k := hvec.hasUnifEigenvalue
   exact Module.End.hasEigenvalue_of_hasGenEigenvalue heg


lemma matrix_exp_tendsto_of_spectrum {m : Type*} [Fintype m] [DecidableEq m]
 (B : Matrix m m ℂ)
 (hB : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' B) μ → μ.re < 0)
 (w : m → ℂ) :
 Filter.Tendsto (fun t : ℝ => (exp ((t : ℝ) • B)).mulVec w)
   Filter.atTop (nhds 0) := by
 classical
 obtain ⟨g, hnil, heig, hsum⟩ := matrix_exists_generalized_sum B w
 -- Each of the finitely many non-zero summands tends to zero.
 have hμ : ∀ μ ∈ g.support,
     Filter.Tendsto
       (fun t : ℝ => (exp ((t : ℝ) • B)).mulVec (g μ))
       Filter.atTop (nhds (0 : (m → ℂ))) := by
   intro μ hμs
   have hne : g μ ≠ 0 := Finsupp.mem_support_iff.mp hμs
   obtain ⟨k, hk⟩ := hnil μ
   exact exp_gen_tendsto B μ (hB μ (heig μ hne)) (g μ) k hk
 have hfin :
     Filter.Tendsto
       (fun t : ℝ => ∑ μ ∈ g.support,
          (exp ((t : ℝ) • B)).mulVec (g μ))
       Filter.atTop
       (nhds (∑ μ ∈ g.support, (0 : (m → ℂ)))) := by
   -- first sum over the support, then over its entries
   exact tendsto_finset_sum g.support (fun μ hμs => hμ μ hμs)
 have hzero :
     Filter.Tendsto
       (fun t : ℝ => ∑ μ ∈ g.support,
          (exp ((t : ℝ) • B)).mulVec (g μ))
       Filter.atTop (nhds (0 : (m → ℂ))) := by
   simpa using hfin
 refine hzero.congr' ?_
 filter_upwards [] with t
 -- Linearity of the matrix action brings the sum back to `w`.
 calc
  (∑ μ ∈ g.support,
          (exp ((t : ℝ) • B)).mulVec (g μ)) =
      (exp ((t : ℝ) • B)).mulVec
        (∑ μ ∈ g.support, g μ) := by
          rw [Matrix.mulVec_sum]
          -- inner bound sum notation, congruity
  _ = (exp ((t : ℝ) • B)).mulVec w := by
        have hs : (∑ μ ∈ g.support, g μ) = w := by
          simpa [Finsupp.sum] using hsum
        rw [hs]

lemma test_const (n:ℕ) (A:Matrix (Fin n) (Fin n) ℝ) (x:ℝ→(Fin n→ℝ))
 (hx:∀ t:ℝ, 0<t → HasDerivAt x (A.mulVec (x t)) t) :
 ∀ u t : ℝ, 0<u → 0<t →
 (exp ((-t:ℝ) • A)).mulVec (x t) = (exp ((-u:ℝ) • A)).mulVec (x u) := by
 classical
 -- continuous linear map from matrices to operators on vectors
 let T0 : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
   { toFun := fun M => LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
     map_add' := by
       intro M N
       ext v i
       change ((M+N).mulVec v) i = _
       rw [Matrix.add_mulVec]
       rfl
     map_smul' := by
       intro c M
       ext v i
       change ((c • M).mulVec v) i = _
       rw [Matrix.smul_mulVec]
       rfl }
 let T : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
    LinearMap.toContinuousLinearMap T0
 let F : ℝ → (Fin n → ℝ) := fun s => (exp ((-s:ℝ) • A)).mulVec (x s)
 have hder (s:ℝ) (hs:0<s) : HasDerivAt F 0 s := by
   -- use exp of a fixed matrix with scalar parameter
   have he0 := hasDerivAt_exp_smul_const (-A) s
   have he : HasDerivAt (fun u:ℝ => exp (u • (-A)))
       (exp (s • (-A)) * (-A)) s := he0
   have hc0 := (T.hasFDerivAt.comp_hasDerivAt s he)
   have hc := hc0
   have hu := hx s hs
   have hp := hc.clm_apply hu
   -- unfold the harmless continuous-linear wrappers to vectors
   dsimp [T, T0] at hp
   simp [smul_neg, neg_smul, mul_neg] at hp
   unfold LinearMap.toContinuousLinearMap at hp
   -- after reducing the finite-dimensional continuous wrappers all terms are mulVec
   change HasDerivAt (fun y : ℝ => (exp (-(y • A))).mulVec (x y))
      ( -((exp (-(s • A)) * A).mulVec (x s)) +
         (exp (-(s • A)) * A).mulVec (x s)) s at hp
   have hcalc : -((exp (-(s • A)) * A).mulVec (x s)) +
         (exp (-(s • A)) * A).mulVec (x s) = (0 : Fin n → ℝ) := by simp
   rw [hcalc] at hp
   simpa [F, neg_smul] using hp
 have hdiff : DifferentiableOn ℝ F (Set.Ioi (0:ℝ)) := by
   intro s hs
   exact (hder s hs).differentiableAt.differentiableWithinAt
 have hz : Set.EqOn (deriv F) (0 : ℝ → (Fin n → ℝ)) (Set.Ioi (0:ℝ)) := by
   intro s hs
   exact (hder s hs).deriv
 intro u t hu ht
 exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hz ht hu
lemma test_rep (n:ℕ) (A:Matrix (Fin n) (Fin n) ℝ) (x:ℝ→(Fin n→ℝ))
 (hx:∀ t:ℝ, 0<t → HasDerivAt x (A.mulVec (x t)) t) :
 ∀ t : ℝ, 0<t →
 x t = (exp ((t-1:ℝ) • A)).mulVec (x 1) := by
 classical
 have hc := test_const n A x hx
 intro t ht
 have eqc := hc 1 t (by norm_num) ht
 have inv (r:ℝ) : exp (r • A) * exp ((-r) • A) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
   rw [← Matrix.exp_add_of_commute]
   · rw [← add_smul]
     simp
   · exact ((Commute.refl A).smul_left r).smul_right (-r)
 have comb (r u:ℝ) : exp (r • A) * exp ((-u) • A) = exp ((r-u) • A) := by
   rw [← Matrix.exp_add_of_commute]
   · rw [← add_smul]
     congr 2
   · exact ((Commute.refl A).smul_left r).smul_right (-u)
 -- multiply by exp(tA)
 have hmul := congrArg (fun v : Fin n → ℝ => (exp (t • A)).mulVec v) eqc
 -- simplify via associativity
 rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, inv, comb] at hmul
 simpa using hmul
lemma test_cast (n:ℕ) (A:Matrix (Fin n) (Fin n) ℝ) (v:Fin n→ℝ) (s:ℝ) :
  (fun i => ((exp (s • A)).mulVec v i : ℂ)) =
   (exp (s • (A.map (algebraMap ℝ ℂ)))).mulVec (fun i => (v i : ℂ)) := by
 classical
 let f := RingHom.mapMatrix (m:= Fin n) (algebraMap ℝ ℂ)
 have hf : Continuous f := by
   -- finite matrix entrywise
   apply continuous_pi
   intro i
   apply continuous_pi
   intro j
   exact Complex.continuous_ofReal.comp (continuous_apply j |>.comp (continuous_apply i))
 -- map exponential
 have he := NormedSpace.map_exp f hf (s • A)
 have harg : f (s • A) = s • (A.map (algebraMap ℝ ℂ)) := by
   ext i j
   change ((s * A i j : ℝ) : ℂ) = (s:ℂ) * (A i j : ℂ)
   simp
 -- cast mulvec
 funext i
 have hentry (M:Matrix (Fin n) (Fin n) ℝ) :
    ((M.mulVec v i : ℝ) : ℂ) =
      (M.map (algebraMap ℝ ℂ)).mulVec (fun j => (v j : ℂ)) i := by
   simp [Matrix.mulVec, dotProduct]
 -- use
 calc
  ((exp (s • A)).mulVec v i : ℂ) =
      ((exp (s • A)).map (algebraMap ℝ ℂ)).mulVec (fun j => (v j : ℂ)) i := hentry _
  _ = (f (exp (s • A))).mulVec (fun j => (v j : ℂ)) i := by
        rw [RingHom.mapMatrix_apply]
  _ = (exp (f (s • A))).mulVec (fun j => (v j : ℂ)) i := by
        exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.mulVec (fun j => (v j : ℂ)) i) he
  _ = (exp (s • (A.map (algebraMap ℝ ℂ)))).mulVec (fun j => (v j : ℂ)) i := by
        exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (exp M).mulVec (fun j => (v j : ℂ)) i) harg

open scoped Matrix
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem linear_ode_asymptotic_stability (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℂ,
        Module.End.HasEigenvalue
          (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0)
    (x : ℝ → (Fin n → ℝ))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t) :
    Filter.Tendsto (fun t : ℝ => ‖x t‖) Filter.atTop (nhds 0) :=
/-ResultProofBegin-/ by
 classical
 let B : Matrix (Fin n) (Fin n) ℂ := A.map (algebraMap ℝ ℂ)
 let w : Fin n → ℂ := fun i => (x 1 i : ℂ)
 have hc : Filter.Tendsto (fun s : ℝ => (exp ((s:ℝ) • B)).mulVec w)
      Filter.atTop (nhds (0 : Fin n → ℂ)) :=
   matrix_exp_tendsto_of_spectrum B hA w
 have hsh : Filter.Tendsto (fun t : ℝ => t - 1) Filter.atTop Filter.atTop := by
   convert tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) tendsto_id using 1 <;>
     simp [sub_eq_add_neg]
 have hc' := hc.comp hsh
 have hv : Filter.Tendsto (fun t : ℝ => (fun i => (x t i : ℂ)))
      Filter.atTop (nhds (0 : Fin n → ℂ)) := by
   -- compare the tail by the real propagator and its complexification
   refine hc'.congr' ?_
   filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
   change (exp ((t - 1) • B)).mulVec w =
       (fun i => (x t i : ℂ))
   symm
   have hr := test_rep n A x hx t ht
   rw [hr]
   exact test_cast n A (x 1) (t - 1)
 have hvn := hv.norm
 -- the sup norm of a real vector is unchanged by the coordinatewise complex embedding
 have hn (v : Fin n → ℝ) : ‖(fun i => (v i : ℂ))‖ = ‖v‖ := by
   rw [Pi.norm_def, Pi.norm_def]
   congr 1
   apply Finset.sup_congr rfl
   intro i hi
   exact Complex.nnnorm_real _
 have hvn' : Filter.Tendsto (fun t : ℝ => ‖(fun i => (x t i : ℂ))‖)
       Filter.atTop (nhds 0) := by simpa using hvn
 convert hvn' using 1
 ext t
 exact (hn (x t)).symm
/-ResultProofEnd-/
/-ResultEnd-/

end
end Submission
