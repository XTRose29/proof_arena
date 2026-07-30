import Mathlib

namespace Submission

open scoped NNReal
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ)
    (hA : A.IsIrreducible) :
    ∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' A) (spectralRadius ℝ A).toReal v ∧
      (∀ i, 0 < v i) :=
/-ResultProofBegin-/by
  classical
  have hnon : ∀ i j, 0 ≤ A i j := hA.nonneg
  -- A useful elementary part of Perron--Frobenius: once a nonzero
  -- nonnegative eigenvector has been found, irreducibility makes every
  -- one of its coordinates positive.  We work with `mulVec`, in order
  -- that no choices of bases are involved.
  have positive_of_eigen
      {u : n → ℝ} {a : ℝ}
      (hu0 : ∀ i, 0 ≤ u i) (hu : u ≠ 0)
      (he : Matrix.mulVec A u = a • u) : ∀ i, 0 < u i := by
    have hj : ∃ j : n, 0 < u j := by
      by_contra! hn
      have uz : u = 0 := by
        funext j
        have hle : u j ≤ 0 := hn j
        exact le_antisymm hle (hu0 j)
      exact hu uz
    obtain ⟨j, hj⟩ := hj
    -- The equality for all powers is convenient here (and avoids
    -- following a path one edge at a time).
    have hpowe : ∀ k : ℕ, Matrix.mulVec (A ^ k) u = (a ^ k) • u := by
      intro k
      induction k with
      | zero =>
          ext t
          simp
      | succ k ih =>
          -- `(A^k A)u=A^k(Au)`
          calc
            Matrix.mulVec (A ^ (Nat.succ k)) u = Matrix.mulVec (A ^ k) (Matrix.mulVec A u) := by
              rw [pow_succ]
              exact (Matrix.mulVec_mulVec u (A ^ k) A).symm
            _ = Matrix.mulVec (A ^ k) (a • u) := by rw [he]
            _ = a • (Matrix.mulVec (A ^ k) u) := by
              simpa using (Matrix.mulVec_smul (A ^ k) a u)
            _ = a • ((a ^ k) • u) := by rw [ih]
            _ = (a ^ (Nat.succ k)) • u := by
              -- scalars commute in `ℝ`
              rw [smul_smul]
              rw [pow_succ]
              rw [mul_comm]
    intro i
    obtain ⟨k, hk, hik⟩ :=
      (Matrix.isIrreducible_iff_exists_pow_pos hnon).1 hA i j
    have hterm : 0 < (A ^ k) i j * u j := mul_pos hik hj
    have hsum : 0 < (Matrix.mulVec (A ^ k) u) i := by
      -- keep the single strictly positive summand, the others are
      -- nonnegative
      change 0 < ∑ t : n, (A ^ k) i t * u t
      have hle : (A ^ k) i j * u j ≤
          ∑ t : n, (A ^ k) i t * u t := by
        exact Finset.single_le_sum
          (fun t _ => mul_nonneg (Matrix.pow_apply_nonneg hnon k i t) (hu0 t))
          (Finset.mem_univ j)
      exact lt_of_lt_of_le hterm hle
    have hai : 0 < a ^ k * u i := by
      have h := congrFun (hpowe k) i
      -- `smul` on functions and on reals are both pointwise
      have h' : (Matrix.mulVec (A ^ k) u) i = a ^ k * u i := by
        simpa using h
      rwa [h'] at hsum
    by_contra hh
    have hui : u i = 0 := le_antisymm (le_of_not_gt hh) (hu0 i)
    have : a ^ k * u i = 0 := by rw [hui, mul_zero]
    rw [this] at hai
    exact (lt_irrefl 0) hai
  -- A positive eigenvector automatically belongs to the largest *real*
  -- modulus.  This elementary comparison (using a largest coordinate of a
  -- finite vector) is particularly handy since the `spectralRadius` in the
  -- statement is the real one.
  have radius_of_positive
      {u : n → ℝ} {a : ℝ}
      (hu : ∀ i, 0 < u i)
      (he : Matrix.mulVec A u = a • u) (ha : 0 ≤ a) :
      (spectralRadius ℝ A).toReal = a := by
    have bound : ∀ b : ℝ, b ∈ spectrum ℝ A → |b| ≤ a := by
      intro b hb
      have hb' : b ∈ spectrum ℝ (Matrix.toLin' A) := by
        simpa using (show b ∈ spectrum ℝ A from hb)
      have hev := (Module.End.HasEigenvalue.of_mem_spectrum hb')
      obtain ⟨w, hw⟩ := hev.exists_hasEigenvector
      have wne : w ≠ 0 := hw.2
      have hnonzero : ∃ t : n, 0 < |w t| := by
        by_contra! hh
        have wz : w = 0 := by
          funext t
          have hz : |w t| = 0 := le_antisymm (hh t) (abs_nonneg _)
          simpa using hz
        exact wne wz
      obtain ⟨k, hk_mem, hk⟩ :=
        Finset.exists_max_image (s := (Finset.univ : Finset n))
          (fun i : n => |w i| / u i) (Finset.univ_nonempty)
      have hratio (i : n) : |w i| / u i ≤ |w k| / u k :=
        hk i (Finset.mem_univ i)
      have hkpos : 0 < |w k| / u k := by
        obtain ⟨t, ht⟩ := hnonzero
        have : 0 < |w t| / u t := div_pos ht (hu t)
        exact lt_of_lt_of_le this (hratio t)
      let c : ℝ := |w k| / u k
      have hcpos : 0 < c := hkpos
      have hwle (i : n) : |w i| ≤ c * u i := by
        have hi : |w i| / u i ≤ c := by simpa [c] using hratio i
        exact (div_le_iff₀ (hu i)).1 hi
      have hwEq := hw.apply_eq_smul
      have hwcomp : (Matrix.mulVec A w) k = b * w k := by
        have := congrFun hwEq k
        simpa using this
      have habs : |b| * |w k| ≤
          ∑ j : n, A k j * |w j| := by
        calc
          |b| * |w k| = |(Matrix.mulVec A w) k| := by rw [hwcomp, abs_mul]
          _ = |∑ j : n, A k j * w j| := rfl
          _ ≤ ∑ j : n, |A k j * w j| :=
              Finset.abs_sum_le_sum_abs (fun j : n => A k j * w j)
                Finset.univ
          _ = ∑ j : n, A k j * |w j| := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [abs_mul, abs_of_nonneg (hnon k j)]
      have hcomp : (∑ j : n, A k j * |w j|)
             ≤ ∑ j : n, A k j * (c * u j) := by
        exact Finset.sum_le_sum (fun j hj =>
          mul_le_mul_of_nonneg_left (hwle j) (hnon k j))
      have huv : (∑ j : n, A k j * (c * u j)) =
            c * (a * u k) := by
        have hh := congrFun he k
        change (∑ j : n, A k j * (c * u j)) = c * (a * u k)
        -- pull the scalar out, then use the eigenvector equation for `u`
        have hku : (∑ j : n, A k j * u j) = a * u k := by
          change (∑ j : n, A k j * u j) = a * u k at hh
          exact hh
        calc
          (∑ j : n, A k j * (c * u j))
              = c * (∑ j : n, A k j * u j) := by
                  simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
          _ = c * (a * u k) := by rw [hku]
      have hwk : |w k| = c * u k := by
        -- the defining maximal ratio
        dsimp [c]
        exact (div_mul_cancel₀ _ (ne_of_gt (hu k))).symm
      have hlast : |b| * (c * u k) ≤ c * (a * u k) := by
        rw [← hwk]
        exact habs.trans (hcomp.trans_eq huv)
      have hp : 0 < c * u k := mul_pos hcpos (hu k)
      nlinarith
    have hua : Module.End.HasEigenvalue (Matrix.toLin' A) a := by
      rw [Module.End.hasEigenvalue_iff]
      intro hbot
      have hu_mem : u ∈ Module.End.eigenspace (Matrix.toLin' A) a :=
        (Module.End.mem_eigenspace_iff).2 (by
          simpa [Matrix.toLin'_apply] using he)
      rw [hbot] at hu_mem
      have uz : u = 0 := by simpa using hu_mem
      have : False := by
        have hi := hu (Classical.choice ‹Nonempty n›)
        have hz : u (Classical.choice ‹Nonempty n›) = 0 := by rw [uz]; rfl
        linarith
      contradiction
    have hamem : a ∈ spectrum ℝ A := by
      have := hua.mem_spectrum
      simpa using this
    have hle : spectralRadius ℝ A ≤ ENNReal.ofReal a := by
      unfold spectralRadius
      refine iSup_le (fun b => ?_)
      refine iSup_le (fun hb => ?_)
      change (↑‖b‖₊ : ENNReal) ≤ ENNReal.ofReal a
      rw [ENNReal.coe_nnreal_eq]
      apply ENNReal.ofReal_le_ofReal
      simpa only [Real.norm_eq_abs, coe_nnnorm] using bound b hb
    have hge : ENNReal.ofReal a ≤ spectralRadius ℝ A := by
      unfold spectralRadius
      have hself : ENNReal.ofReal a = (↑‖a‖₊ : ENNReal) := by
        rw [ENNReal.coe_nnreal_eq]
        congr 1
        simp [Real.norm_eq_abs, abs_of_nonneg ha]
      rw [hself]
      exact le_iSup_of_le a (le_iSup_of_le hamem (le_rfl))
    have heq : spectralRadius ℝ A = ENNReal.ofReal a := le_antisymm hle hge
    rw [heq]
    exact ENNReal.toReal_ofReal ha
  -- Thus only the cone-existence assertion is needed; the comparison
  -- above identifies its eigenvalue with the real spectral radius.
  obtain ⟨a, u, huEig, hu0, ha⟩ :
      ∃ (a : ℝ) (u : n → ℝ),
        Module.End.HasEigenvector (Matrix.toLin' A) a u ∧
          (∀ i, 0 ≤ u i) ∧ 0 ≤ a := by
    rcases subsingleton_or_nontrivial n with hs | hn
    · letI : Subsingleton n := hs
      let d : n := Classical.choice (inferInstance : Nonempty n)
      letI : Unique n :=
        { default := d
          uniq := fun x => Subsingleton.elim x d }
      let u : n → ℝ := fun _ => 1
      have hmul : Matrix.mulVec A u = (A (default : n) default) • u := by
        funext i
        change (∑ j : n, A i j * (1:ℝ)) = A default default * 1
        rw [Fintype.sum_unique]
        rw [mul_one, mul_one]
        have hi : i = default := Subsingleton.elim _ _
        rw [hi]
      have hvec : Module.End.HasEigenvector (Matrix.toLin' A)
                  (A default default) u := by
        refine ⟨?_, ?_⟩
        · rw [Module.End.genEigenspace_one]
          apply (LinearMap.mem_ker).2
          -- applying `f - a` to this vector
          change (Matrix.toLin' A - (A default default) • (1 : Module.End ℝ (n → ℝ))) u = 0
          rw [LinearMap.sub_apply]
          have hu' : (Matrix.toLin' A) u = (A default default) • u := by
            simpa using hmul
          rw [hu']
          simp
        · intro huz
          have h := congrFun huz (default : n)
          norm_num [u] at h
      refine ⟨A default default, u, hvec, ?_, hnon default default⟩
      intro i
      simp [u]
    · letI : Nontrivial n := hn
      -- maximize the sub-eigenvalue on the nonnegative simplex
      let R : ℝ := ∑ i : n, ∑ j : n, A i j
      have hR : 0 ≤ R := by
        dsimp [R]
        exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnon i j))
      let S : Set (ℝ × (n → ℝ)) := {p |
          0 ≤ p.1 ∧ p.1 ≤ R ∧
          (∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ 1) ∧
          (∑ i : n, p.2 i) = 1 ∧
          (∀ i, p.1 * p.2 i ≤ ∑ j : n, A i j * p.2 j) }
      have hSclosed : IsClosed S := by
        have h0 : IsClosed {p : ℝ × (n → ℝ) | (0:ℝ) ≤ p.1} :=
          isClosed_le continuous_const continuous_fst
        have hR' : IsClosed {p : ℝ × (n → ℝ) | p.1 ≤ R} :=
          isClosed_le continuous_fst continuous_const
        have hx (i : n) : IsClosed {p : ℝ × (n → ℝ) |
              0 ≤ p.2 i ∧ p.2 i ≤ (1:ℝ)} := by
          exact (isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)).inter
            (isClosed_le ((continuous_apply i).comp continuous_snd) continuous_const)
        have hx' : IsClosed {p : ℝ × (n → ℝ) |
              ∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ (1:ℝ)} := by
          simpa only [Set.setOf_forall] using (isClosed_iInter (fun i => hx i))
        have hcSum : Continuous (fun p : ℝ × (n → ℝ) => ∑ i : n, p.2 i) := by
          fun_prop
        have hs' : IsClosed {p : ℝ × (n → ℝ) | (∑ i : n, p.2 i) = (1:ℝ)} :=
          isClosed_eq hcSum continuous_const
        have hi (i : n) : IsClosed {p : ℝ × (n → ℝ) |
              p.1 * p.2 i ≤ ∑ j : n, A i j * p.2 j} := by
          apply isClosed_le
          · fun_prop
          · fun_prop
        have hi' : IsClosed {p : ℝ × (n → ℝ) |
              ∀ i, p.1 * p.2 i ≤ ∑ j : n, A i j * p.2 j} := by
          simpa only [Set.setOf_forall] using (isClosed_iInter (fun i => hi i))
        have hall := h0.inter (hR'.inter (hx'.inter (hs'.inter hi')))
        -- put the five closed conditions together
        simpa [S, Set.setOf_and] using hall
      have hScompact : IsCompact S := by
        let B : Set (ℝ × (n → ℝ)) :=
          Set.Icc (0:ℝ) R ×ˢ (Set.univ.pi (fun _ : n => Set.Icc (0:ℝ) 1))
        have hB : IsCompact B := by
          exact isCompact_Icc.prod (isCompact_univ_pi (fun _ : n => isCompact_Icc))
        apply hB.of_isClosed_subset hSclosed
        intro p hp
        change (p.1 ∈ Set.Icc (0:ℝ) R ∧
          p.2 ∈ Set.univ.pi (fun _ : n => Set.Icc (0:ℝ) 1))
        change 0 ≤ p.1 ∧ p.1 ≤ R ∧
          (∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ 1) ∧
          _ ∧ _ at hp
        refine ⟨⟨hp.1, hp.2.1⟩, ?_⟩
        intro i hi
        exact hp.2.2.1 i
      let d : n := Classical.choice (inferInstance : Nonempty n)
      let x0 : n → ℝ := fun i => if i = d then 1 else 0
      have hx0 (i : n) : 0 ≤ x0 i ∧ x0 i ≤ (1:ℝ) := by
        dsimp [x0]
        split_ifs <;> constructor <;> norm_num
      have hx0sum : (∑ i : n, x0 i) = (1:ℝ) := by
        classical
        simp [x0]
      have hSne : S.Nonempty := by
        refine ⟨(0, x0), ?_⟩
        change 0 ≤ (0:ℝ) ∧ (0:ℝ) ≤ R ∧
          (∀ i, 0 ≤ x0 i ∧ x0 i ≤ (1:ℝ)) ∧
          (∑ i : n, x0 i) = 1 ∧
          (∀ i, (0:ℝ) * x0 i ≤ ∑ j : n, A i j * x0 j)
        refine ⟨le_rfl, hR, hx0, hx0sum, ?_⟩
        intro i
        simp only [zero_mul]
        exact Finset.sum_nonneg (fun j _ => mul_nonneg (hnon i j) (hx0 j).1)
      obtain ⟨p, hp, hpmax⟩ :=
        hScompact.exists_isMaxOn hSne (continuous_fst.continuousOn)
      let T : ℝ := p.1
      let x : n → ℝ := p.2
      have hT : 0 ≤ T := hp.1
      have hx (i : n) : 0 ≤ x i := (hp.2.2.1 i).1
      have hxle (i : n) : x i ≤ (1:ℝ) := (hp.2.2.1 i).2
      have hxsum : (∑ i : n, x i) = (1:ℝ) := hp.2.2.2.1
      have hpineq (i : n) : T * x i ≤ ∑ j : n, A i j * x j := hp.2.2.2.2 i
      -- a general elementary bound used to put constructed pairs back in the compact set
      have boundR {t : ℝ} {v : n → ℝ}
          (hv0 : ∀ i, 0 ≤ v i) (hvle : ∀ i, v i ≤ (1:ℝ))
          (hvsum : (∑ i : n, v i) = (1:ℝ))
          (hv : ∀ i, t * v i ≤ ∑ j : n, A i j * v j) : t ≤ R := by
        have h1 : (∑ i : n, t * v i) ≤
            ∑ i : n, ∑ j : n, A i j * v j :=
          Finset.sum_le_sum (fun i _ => hv i)
        have h2 : (∑ i : n, ∑ j : n, A i j * v j) ≤ R := by
          dsimp [R]
          exact Finset.sum_le_sum (fun i _ =>
            Finset.sum_le_sum (fun j _ => by
              simpa using (mul_le_mul_of_nonneg_left (hvle j) (hnon i j))))
        have heq : (∑ i : n, t * v i) = t := by
          rw [← Finset.mul_sum, hvsum, mul_one]
        linarith
      let w : n → ℝ := fun i => (Matrix.mulVec A x) i - T * x i
      have hw0 (i : n) : 0 ≤ w i := by
        dsimp [w]
        exact sub_nonneg.mpr (hpineq i)
      by_cases hzero : w = 0
      · have hAx : Matrix.mulVec A x = T • x := by
          funext i
          have hi := congrFun hzero i
          dsimp [w] at hi
          simpa using (sub_eq_zero.mp hi)
        have hxne : x ≠ 0 := by
          intro hz
          have : (0:ℝ) = 1 := by simpa [hz] using hxsum
          norm_num at this
        have heig : Module.End.HasEigenvector (Matrix.toLin' A) T x := by
          rw [Module.End.hasEigenvector_iff]
          refine ⟨(Module.End.mem_eigenspace_iff).2 ?_, hxne⟩
          simpa [Matrix.toLin'_apply] using hAx
        exact ⟨T, x, heig, hx, hT⟩
      · have hwpos : ∃ j : n, 0 < w j := by
          by_contra! hh
          apply hzero
          funext i
          exact le_antisymm (hh i) (hw0 i)
        obtain ⟨j, hwj⟩ := hwpos
        have hk_spec (i : n) : ∃ k : ℕ, k > 0 ∧ 0 < (A ^ k) i j :=
          (Matrix.isIrreducible_iff_exists_pow_pos hnon).1 hA i j
        choose k hkpos hkpow using hk_spec
        let N : ℕ := ∑ i : n, k i
        have hkN (i : n) : k i ≤ N := by
          dsimp [N]
          exact Finset.single_le_sum (fun t _ => Nat.zero_le (k t)) (Finset.mem_univ i)
        let y : n → ℝ := ∑ q ∈ Finset.range (N+1), Matrix.mulVec (A^q) x
        let z : n → ℝ := ∑ q ∈ Finset.range (N+1), Matrix.mulVec (A^q) w
        have hxq0 (q : ℕ) (i : n) : 0 ≤ (Matrix.mulVec (A^q) x) i := by
          exact Finset.sum_nonneg (fun l _ =>
            mul_nonneg (Matrix.pow_apply_nonneg hnon q i l) (hx l))
        have hwq0 (q : ℕ) (i : n) : 0 ≤ (Matrix.mulVec (A^q) w) i := by
          exact Finset.sum_nonneg (fun l _ =>
            mul_nonneg (Matrix.pow_apply_nonneg hnon q i l) (hw0 l))
        have hy0 (i : n) : 0 ≤ y i := by
          dsimp [y]
          simp only [Finset.sum_apply]
          exact Finset.sum_nonneg (fun q _ => hxq0 q i)
        have hzpos (i : n) : 0 < z i := by
          have hinner : 0 < (Matrix.mulVec (A^(k i)) w) i := by
            have hterm : 0 < (A^(k i)) i j * w j := mul_pos (hkpow i) hwj
            have hle : (A^(k i)) i j * w j ≤
                ∑ l : n, (A^(k i)) i l * w l :=
              Finset.single_le_sum
                (fun l _ => mul_nonneg (Matrix.pow_apply_nonneg hnon (k i) i l) (hw0 l))
                (Finset.mem_univ j)
            exact lt_of_lt_of_le hterm hle
          dsimp [z]
          simp only [Finset.sum_apply]
          have hm : k i ∈ Finset.range (N+1) := Finset.mem_range.2 (Nat.lt_succ_of_le (hkN i))
          have hle : (Matrix.mulVec (A^(k i)) w) i ≤
              ∑ q ∈ Finset.range (N+1), (Matrix.mulVec (A^q) w) i :=
            Finset.single_le_sum (fun q _ => hwq0 q i) hm
          exact lt_of_lt_of_le hinner hle
        have hAxw : Matrix.mulVec A x = T • x + w := by
          funext i
          dsimp [w]
          simp
        have hterm (q : ℕ) :
            Matrix.mulVec A (Matrix.mulVec (A^q) x) =
              T • (Matrix.mulVec (A^q) x) + Matrix.mulVec (A^q) w := by
          calc
            Matrix.mulVec A (Matrix.mulVec (A^q) x) =
                Matrix.mulVec (A * (A^q)) x := Matrix.mulVec_mulVec x A (A^q)
            _ = Matrix.mulVec ((A^q) * A) x := by rw [(Commute.self_pow A q).eq]
            _ = Matrix.mulVec (A^q) (Matrix.mulVec A x) :=
                (Matrix.mulVec_mulVec x (A^q) A).symm
            _ = Matrix.mulVec (A^q) (T • x + w) := by rw [hAxw]
            _ = T • (Matrix.mulVec (A^q) x) + Matrix.mulVec (A^q) w := by
                rw [Matrix.mulVec_add, Matrix.mulVec_smul]
        have hAy : Matrix.mulVec A y = T • y + z := by
          dsimp [y, z]
          change A.mulVecLin (∑ q ∈ Finset.range (N+1), Matrix.mulVec (A^q) x) = _
          rw [map_sum]
          simp only [Matrix.mulVecLin_apply]
          simp_rw [hterm]
          rw [Finset.sum_add_distrib]
          congr 1
          rw [Finset.smul_sum]
        have hyx (i : n) : x i ≤ y i := by
          have hmem : 0 ∈ Finset.range (N+1) := Finset.mem_range.2 (Nat.zero_lt_succ _)
          have hle : (Matrix.mulVec (A^0) x) i ≤
              ∑ q ∈ Finset.range (N+1), (Matrix.mulVec (A^q) x) i :=
            Finset.single_le_sum (fun q _ => hxq0 q i) hmem
          have hzeroq : (Matrix.mulVec (A^0) x) i = x i := by simp
          dsimp [y]
          simp only [Finset.sum_apply]
          simpa [hzeroq] using hle
        let Y : ℝ := ∑ i : n, y i
        have hY1 : (1:ℝ) ≤ Y := by
          dsimp [Y]
          rw [← hxsum]
          exact Finset.sum_le_sum (fun i _ => hyx i)
        have hY : 0 < Y := lt_of_lt_of_le (by norm_num) hY1
        have hyY (i : n) : y i ≤ Y := by
          dsimp [Y]
          exact Finset.single_le_sum (fun q _ => hy0 q) (Finset.mem_univ i)
        obtain ⟨i₀, hi₀, hmin⟩ :=
          Finset.exists_min_image (s := (Finset.univ : Finset n))
             (fun i : n => z i) (Finset.univ_nonempty)
        let m : ℝ := z i₀
        have hm : 0 < m := hzpos i₀
        have hmi (i : n) : m ≤ z i := hmin i (Finset.mem_univ i)
        let e : ℝ := m / Y
        have hepos : 0 < e := div_pos hm hY
        have heY : e * Y = m := by
          dsimp [e]
          exact div_mul_cancel₀ _ (ne_of_gt hY)
        have hey (i : n) : e * y i ≤ z i := by
          calc
            e * y i ≤ e * Y := mul_le_mul_of_nonneg_left (hyY i) (le_of_lt hepos)
            _ = m := heY
            _ ≤ z i := hmi i
        have hyineq (i : n) : (T + e) * y i ≤ (Matrix.mulVec A y) i := by
          have hh := congrFun hAy i
          change (Matrix.mulVec A y) i = T * y i + z i at hh
          rw [hh]
          nlinarith [hey i]
        let v : n → ℝ := fun i => y i / Y
        have hv0 (i : n) : 0 ≤ v i := by
          dsimp [v]
          exact div_nonneg (hy0 i) (le_of_lt hY)
        have hvle (i : n) : v i ≤ (1:ℝ) := by
          dsimp [v]
          exact (div_le_one (hY)).2 (hyY i)
        have hvsum : (∑ i : n, v i) = (1:ℝ) := by
          dsimp [v]
          rw [← Finset.sum_div]
          change Y / Y = 1
          exact div_self (ne_of_gt hY)
        have hvineq (i : n) : (T+e) * v i ≤ ∑ j : n, A i j * v j := by
          calc
            (T+e) * v i = ((T+e) * y i) / Y := by dsimp [v]; ring
            _ ≤ (Matrix.mulVec A y i) / Y :=
              div_le_div_of_nonneg_right (hyineq i) (le_of_lt hY)
            _ = ∑ j : n, A i j * v j := by
              change (∑ j : n, A i j * y j) / Y = _
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro j hj
              dsimp [v]
              ring
        have hvR : T + e ≤ R :=
          boundR hv0 hvle hvsum hvineq
        have hvS : (T+e, v) ∈ S := by
          change 0 ≤ T+e ∧ T+e ≤ R ∧
            (∀ i, 0 ≤ v i ∧ v i ≤ (1:ℝ)) ∧
            (∑ i : n, v i) = 1 ∧
            (∀ i, (T+e) * v i ≤ ∑ j : n, A i j * v j)
          exact ⟨by linarith, hvR, fun i => ⟨hv0 i, hvle i⟩, hvsum, hvineq⟩
        have hpmax' : ∀ q ∈ S, q.1 ≤ p.1 := by
          simpa [IsMaxOn, IsMaxFilter] using hpmax
        have bad := hpmax' (T+e, v) hvS
        change T + e ≤ T at bad
        exfalso
        linarith
  have he : Matrix.mulVec A u = a • u := by
    simpa using huEig.apply_eq_smul
  have hup : ∀ i, 0 < u i := positive_of_eigen hu0 huEig.2 he
  have hra : (spectralRadius ℝ A).toReal = a := radius_of_positive hup he ha
  refine ⟨u, ?_, hup⟩
  simpa [hra] using huEig
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
