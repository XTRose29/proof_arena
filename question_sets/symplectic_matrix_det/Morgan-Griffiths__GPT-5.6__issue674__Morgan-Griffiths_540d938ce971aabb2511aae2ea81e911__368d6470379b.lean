import Mathlib

namespace Submission

open Matrix
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

-- A useful large open cell of the symplectic group.  This is the place where
-- the elementary Schur-complement proof works (no Pfaffians are necessary).
private lemma sympl_det_of_invertible₁₁
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    (a b c d : Matrix l l R) [Invertible a]
    (h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l R) :
    (Matrix.fromBlocks a b c d).det = 1 := by
  -- use the version of the equation in which the columns are a symplectic basis
  have h' : (Matrix.fromBlocks a b c d)ᵀ * Matrix.J l R *
        (Matrix.fromBlocks a b c d) = Matrix.J l R :=
    (SymplecticGroup.mem_iff').1 h
  -- Its two upper blocks are the familiar equations
  have eq11 : cᵀ * a - aᵀ * c = (0 : Matrix l l R) := by
    have t := congrArg Matrix.toBlocks₁₁ h'
    simpa [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, sub_eq_add_neg,
      Matrix.mul_add, Matrix.add_mul] using t
  have eq12 : cᵀ * b - aᵀ * d = -(1 : Matrix l l R) := by
    have t := congrArg Matrix.toBlocks₁₂ h'
    simpa [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, sub_eq_add_neg,
      Matrix.mul_add, Matrix.add_mul] using t
  -- transposing an invertible matrix is invertible
  letI : Invertible aᵀ := Matrix.invertibleTranspose a
  -- The Schur complement is the inverse-transpose of a.
  have hschur_mul :
      aᵀ * (d - c * (⅟ a) * b) = (1 : Matrix l l R) := by
    -- first the other form of the off diagonal equation
    have e12 : aᵀ * d - cᵀ * b = (1 : Matrix l l R) := by
      -- this is just the negative of eq12
      calc
        aᵀ * d - cᵀ * b = -(cᵀ * b - aᵀ * d) := by
          abel
        _ = -(-(1 : Matrix l l R)) := by rw [eq12]
        _ = 1 := neg_neg _
    calc
      aᵀ * (d - c * (⅟ a) * b) =
          aᵀ * d - (aᵀ * c) * (⅟ a) * b := by
            -- just reassociate
            simp only [Matrix.mul_sub, Matrix.mul_assoc]
      _ = aᵀ * d - (cᵀ * a) * (⅟ a) * b := by
            have e11 : cᵀ * a = aᵀ * c := sub_eq_zero.mp eq11
            rw [e11]
      _ = aᵀ * d - cᵀ * b := by
            simp [Matrix.mul_assoc]
      _ = 1 := e12
  -- Taking determinants of this left-inverse equation is enough; it avoids
  -- any choice of inverse for the transposed matrix.
  rw [Matrix.det_fromBlocks₁₁]
  have hh := congrArg (fun z : Matrix l l R => z.det) hschur_mul
  simpa [Matrix.det_mul, Matrix.det_transpose] using hh


-- The simple block shears have determinant one and let us compute the sign chosen for `J`
-- without invoking a square-root of its determinant.
private lemma det_J_eq_one' {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R] :
    (Matrix.J l R).det = 1 := by
  let S : Matrix (l ⊕ l) (l ⊕ l) R :=
    Matrix.fromBlocks (1 : Matrix l l R) (1 : Matrix l l R)
      (0 : Matrix l l R) (1 : Matrix l l R)
  have hS : S ∈ Matrix.symplecticGroup l R := by
    -- this is the elementary upper unipotent symplectic shear
    rw [SymplecticGroup.mem_iff]
    simp [S, Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one]
  have hSJ : S * Matrix.J l R ∈ Matrix.symplecticGroup l R :=
    (Matrix.symplecticGroup l R).mul_mem hS (SymplecticGroup.J_mem l R)
  have blocksSJ : S * Matrix.J l R =
      Matrix.fromBlocks (1 : Matrix l l R) (-1 : Matrix l l R)
        (1 : Matrix l l R) (0 : Matrix l l R) := by
    -- multiplication of the two displayed block matrices
    simp [S, Matrix.J, Matrix.fromBlocks_multiply]
  have hcell : (S * Matrix.J l R).det = (1 : R) := by
    have inv1 : Invertible (1 : Matrix l l R) := invertibleOne
    -- in these blocks the top-left entry is the identity
    have hm : Matrix.fromBlocks (1 : Matrix l l R) (-1 : Matrix l l R)
          (1 : Matrix l l R) (0 : Matrix l l R) ∈ Matrix.symplecticGroup l R := by
      rw [← blocksSJ]
      exact hSJ
    simpa [blocksSJ] using
      (sympl_det_of_invertible₁₁ (R:=R) (l:=l)
        (1 : Matrix l l R) (-1 : Matrix l l R)
        (1 : Matrix l l R) (0 : Matrix l l R) hm)
  have detS : S.det = (1 : R) := by
    simp [S, Matrix.det_fromBlocks_zero₂₁]
  simpa [Matrix.det_mul, detS] using hcell

private lemma sympl_det_of_invertible₁₂
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    (a b c d : Matrix l l R) [Invertible b]
    (h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l R) :
    (Matrix.fromBlocks a b c d).det = 1 := by
  let A : Matrix (l ⊕ l) (l ⊕ l) R := Matrix.fromBlocks a b c d
  have hAJ : A * Matrix.J l R ∈ Matrix.symplecticGroup l R :=
    (Matrix.symplecticGroup l R).mul_mem h (SymplecticGroup.J_mem l R)
  have blocks : A * Matrix.J l R =
      Matrix.fromBlocks b (-a) d (-c) := by
    simp [A, Matrix.J, Matrix.fromBlocks_multiply]
  have hv : (A * Matrix.J l R).det = (1 : R) := by
    rw [blocks]
    have hm : Matrix.fromBlocks b (-a) d (-c) ∈ Matrix.symplecticGroup l R := by
      rw [← blocks]
      exact hAJ
    exact sympl_det_of_invertible₁₁ b (-a) d (-c) hm
  simpa [Matrix.det_mul, det_J_eq_one' (l:=l) (R:=R), A] using hv

private lemma sympl_det_of_invertible₂₁
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    (a b c d : Matrix l l R)
    (hc : IsUnit c)
    (h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l R) :
    (Matrix.fromBlocks a b c d).det = 1 := by
  let A : Matrix (l ⊕ l) (l ⊕ l) R := Matrix.fromBlocks a b c d
  have hJA : Matrix.J l R * A ∈ Matrix.symplecticGroup l R :=
    (Matrix.symplecticGroup l R).mul_mem (SymplecticGroup.J_mem l R) h
  have blocks : Matrix.J l R * A =
      Matrix.fromBlocks (-c) (-d) a b := by
    simp [A, Matrix.J, Matrix.fromBlocks_multiply]
  have ic : IsUnit (-c) := hc.neg
  -- it is a little easier to package the unit as an `Invertible` instance
  letI : Invertible (-c) := ic.nonempty_invertible.some
  have hv : (Matrix.J l R * A).det = (1 : R) := by
    rw [blocks]
    have hm : Matrix.fromBlocks (-c) (-d) a b ∈ Matrix.symplecticGroup l R := by
      rw [← blocks]
      exact hJA
    exact sympl_det_of_invertible₁₁ (-c) (-d) a b hm
  simpa [Matrix.det_mul, det_J_eq_one' (l:=l) (R:=R), A] using hv


private lemma sympl_det_of_invertible₂₂
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    (a b c d : Matrix l l R)
    (hd : IsUnit d)
    (h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l R) :
    (Matrix.fromBlocks a b c d).det = 1 := by
  let A : Matrix (l ⊕ l) (l ⊕ l) R := Matrix.fromBlocks a b c d
  -- Multiplication by J on both sides puts `-d` in the north-west corner.
  have hJA : Matrix.J l R * A ∈ Matrix.symplecticGroup l R :=
    (Matrix.symplecticGroup l R).mul_mem (SymplecticGroup.J_mem l R) h
  have hJAJ : Matrix.J l R * A * Matrix.J l R ∈ Matrix.symplecticGroup l R :=
    (Matrix.symplecticGroup l R).mul_mem hJA (SymplecticGroup.J_mem l R)
  have blocks : Matrix.J l R * A * Matrix.J l R =
      Matrix.fromBlocks (-d) c b (-a) := by
    simp [A, Matrix.J, Matrix.fromBlocks_multiply]
  have iid : IsUnit (-d) := hd.neg
  letI : Invertible (-d) := iid.nonempty_invertible.some
  have hv : (Matrix.J l R * A * Matrix.J l R).det = (1 : R) := by
    rw [blocks]
    have hm : Matrix.fromBlocks (-d) c b (-a) ∈ Matrix.symplecticGroup l R := by
      rw [← blocks]
      exact hJAJ
    exact sympl_det_of_invertible₁₁ (-d) c b (-a) hm
  simpa [Matrix.det_mul, det_J_eq_one' (l:=l) (R:=R), A] using hv


-- The first n columns of a symplectic matrix are independent: the equation
-- `Aᵀ J A = J` supplies the explicit left inverse `dᵀ,-bᵀ`.  This
-- elementary fact is the input for the pencil/large-cell argument over a
-- field; phrasing it in terms of `mulVec` avoids any rank choices.
private lemma symplectic_left_inverse_first_columns
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    (a b c d : Matrix l l R)
    (h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l R) :
    dᵀ * a - bᵀ * c = (1 : Matrix l l R) := by
  have h' : (Matrix.fromBlocks a b c d)ᵀ * Matrix.J l R *
        (Matrix.fromBlocks a b c d) = Matrix.J l R :=
    (SymplecticGroup.mem_iff').1 h
  have t := congrArg Matrix.toBlocks₂₁ h'
  -- The lower-left block of `J` is the identity.
  simpa [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul] using t

/-- The same columns span an isotropic subspace.  We record the matrix form of
this second input of the regular-pencil argument separately. -/
private lemma symplectic_first_columns_isotropic
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    (a b c d : Matrix l l R)
    (h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l R) :
    cᵀ * a = aᵀ * c := by
  have h' : (Matrix.fromBlocks a b c d)ᵀ * Matrix.J l R *
        (Matrix.fromBlocks a b c d) = Matrix.J l R :=
    (SymplecticGroup.mem_iff').1 h
  have t0 := congrArg Matrix.toBlocks₁₁ h'
  have ez : cᵀ * a - aᵀ * c = (0 : Matrix l l R) := by
    simpa [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul] using t0
  exact sub_eq_zero.mp ez

private lemma symplectic_first_columns_ker
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    (a b c d : Matrix l l R)
    (h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l R)
    (x : l → R) (ha : a *ᵥ x = 0) (hc : c *ᵥ x = 0) :
    x = 0 := by
  have e21 : dᵀ * a - bᵀ * c = (1 : Matrix l l R) :=
    symplectic_left_inverse_first_columns a b c d h
  have ev := congrArg (fun z : Matrix l l R => z *ᵥ x) e21
  -- Applying the left inverse to a vector with both blocks zero kills it.
  -- This argument uses no division, hence will also be useful after extension
  -- of scalars to a field of rational functions.
  have ev' : (0 : l → R) = x := by
    simpa [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ha, hc] using ev
  exact ev'.symm

-- A symmetric shear is useful as well: it enlarges the north-west Schur cell from
-- `a` to any `a + t*c`.  This statement is still valid over rings.
private lemma sympl_det_of_invertible_add_mul
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    (a b c d t : Matrix l l R) (ht : tᵀ = t)
    (hu : IsUnit (a + t * c))
    (h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l R) :
    (Matrix.fromBlocks a b c d).det = 1 := by
  let S : Matrix (l ⊕ l) (l ⊕ l) R :=
    Matrix.fromBlocks (1 : Matrix l l R) t (0 : Matrix l l R) (1 : Matrix l l R)
  have hS : S ∈ Matrix.symplecticGroup l R := by
    rw [SymplecticGroup.mem_iff]
    simp [S, Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, ht]
  let A : Matrix (l ⊕ l) (l ⊕ l) R := Matrix.fromBlocks a b c d
  have hSA : S * A ∈ Matrix.symplecticGroup l R :=
    (Matrix.symplecticGroup l R).mul_mem hS h
  have blocks : S * A = Matrix.fromBlocks (a + t*c) (b + t*d) c d := by
    simp [S, A, Matrix.fromBlocks_multiply]
  letI : Invertible (a + t*c) := hu.nonempty_invertible.some
  have hv : (S*A).det = (1 : R) := by
    rw [blocks]
    have hm : Matrix.fromBlocks (a + t*c) (b+t*d) c d ∈
        Matrix.symplecticGroup l R := by
      rw [← blocks]
      exact hSA
    exact sympl_det_of_invertible₁₁ (a+t*c) (b+t*d) c d hm
  have hsdet : S.det = (1 : R) := by
    simp [S]
  simpa [Matrix.det_mul, hsdet, A] using hv

-- and the same operation on the right changes `a` into `a + b*t`.
private lemma sympl_det_of_invertible_add_mul_right
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    (a b c d t : Matrix l l R) (ht : tᵀ = t)
    (hu : IsUnit (a + b * t))
    (h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l R) :
    (Matrix.fromBlocks a b c d).det = 1 := by
  let S : Matrix (l ⊕ l) (l ⊕ l) R :=
    Matrix.fromBlocks (1 : Matrix l l R) (0 : Matrix l l R) t (1 : Matrix l l R)
  have hS : S ∈ Matrix.symplecticGroup l R := by
    rw [SymplecticGroup.mem_iff]
    simp [S, Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, ht]
  let A : Matrix (l ⊕ l) (l ⊕ l) R := Matrix.fromBlocks a b c d
  have hAS : A * S ∈ Matrix.symplecticGroup l R :=
    (Matrix.symplecticGroup l R).mul_mem h hS
  have blocks : A * S = Matrix.fromBlocks (a + b*t) b (c + d*t) d := by
    simp [A, S, Matrix.fromBlocks_multiply]
  letI : Invertible (a + b*t) := hu.nonempty_invertible.some
  have hv : (A*S).det = (1 : R) := by
    rw [blocks]
    have hm : Matrix.fromBlocks (a + b*t) b (c+d*t) d ∈
        Matrix.symplecticGroup l R := by
      rw [← blocks]
      exact hAS
    exact sympl_det_of_invertible₁₁ (a+b*t) b (c+d*t) d hm
  have hsdet : S.det = (1 : R) := by
    simp [S]
  simpa [Matrix.det_mul, hsdet, A] using hv


-- In one hyperbolic plane the assertion is just the off diagonal entry of
-- `Aᵀ J A = J`; this also covers nonfields where no corner need be a unit.
private lemma sympl_det_subsingleton
    {l R : Type*} [DecidableEq l] [Fintype l] [Subsingleton l] [CommRing R]
    {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (h : A ∈ Matrix.symplecticGroup l R) : A.det = 1 := by
  classical
  cases isEmpty_or_nonempty l with
  | inl hempty =>
      letI := hempty
      -- the zero-by-zero case
      haveI : IsEmpty (l ⊕ l) := by infer_instance
      exact Matrix.det_isEmpty
  | inr hne =>
    letI := hne
    let x : l := Classical.choice hne
    letI ux : Unique l := { default := x, uniq := fun y => Subsingleton.elim _ _ }
    let a : Matrix l l R := Matrix.toBlocks₁₁ A
    let b : Matrix l l R := Matrix.toBlocks₁₂ A
    let c : Matrix l l R := Matrix.toBlocks₂₁ A
    let d : Matrix l l R := Matrix.toBlocks₂₂ A
    have hblocks : Matrix.fromBlocks a b c d = A := by
      simpa [a,b,c,d] using (Matrix.fromBlocks_toBlocks A)
    have h' : (Matrix.fromBlocks a b c d)ᵀ * Matrix.J l R *
        (Matrix.fromBlocks a b c d) = Matrix.J l R := by
      rw [hblocks]
      exact (SymplecticGroup.mem_iff').1 h
    have e12 : aᵀ * d - cᵀ * b = (1 : Matrix l l R) := by
      have t0 := congrArg Matrix.toBlocks₁₂ h'
      have t1 : cᵀ * b - aᵀ * d = -(1 : Matrix l l R) := by
        simpa [Matrix.J, Matrix.fromBlocks_transpose,
          Matrix.fromBlocks_multiply, sub_eq_add_neg,
          Matrix.mul_add, Matrix.add_mul] using t0
      calc
        aᵀ * d - cᵀ * b = -(cᵀ * b - aᵀ * d) := by abel
        _ = -(-(1 : Matrix l l R)) := by rw [t1]
        _ = 1 := neg_neg _
    have esc : a x x * d x x - c x x * b x x = (1 : R) := by
      have := congrArg (fun z : Matrix l l R => z x x) e12
      classical
      have hx : (default : l) = x := Subsingleton.elim _ _
      simpa [Matrix.mul_apply, Finset.univ_unique, hx, x] using this
    -- reindex to the explicitly ordered two element set to use `det_fin_two`.
    let ex : Fin 1 ≃ l := (Fintype.equivOfCardEq (by simp [Fintype.card_unique] : Fintype.card (Fin 1) = Fintype.card l))
    -- Use the evident order: first the left point and then the right point.
    let e : Fin 2 ≃ (l ⊕ l) :=
      (finCongr (by decide : 1 + 1 = 2)).symm.trans (finSumFinEquiv.symm) |> fun z =>
        z.trans (Equiv.sumCongr ex ex)
    have e0 : e (0 : Fin 2) = Sum.inl x := by
      apply congrArg Sum.inl
      apply Subsingleton.elim
    have e1 : e (1 : Fin 2) = Sum.inr x := by
      apply congrArg Sum.inr
      apply Subsingleton.elim
    have hd := Matrix.det_submatrix_equiv_self e A
    -- the four blocks of this submatrix are the four scalar entries
    have hf := Matrix.det_fin_two (A.submatrix e e)
    rw [hd] at hf
    -- and the off-diagonal equation obtained above is exactly this determinant
    rw [hf]
    -- expose the four blocks
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply,
      Matrix.submatrix_apply, Matrix.submatrix_apply]
    rw [e0, e1]
    rw [← hblocks]
    change
      a x x * d x x - b x x * c x x = (1 : R)
    calc
      a x x * d x x - b x x * c x x =
          a x x * d x x - c x x * b x x := by
            rw [mul_comm (b x x) (c x x)]
      _ = 1 := esc



private lemma finrank_ker_mulVec_transpose {l K : Type*} [DecidableEq l] [Fintype l] [Field K]
 (c : Matrix l l K) :
 Module.finrank K ↥(Matrix.mulVecLin c).ker =
 Module.finrank K ↥(Matrix.mulVecLin cᵀ).ker := by
  have hr1 : c.rank = Module.finrank K ↥(Matrix.mulVecLin c).range := by
    rw [← Matrix.toLin'_apply']
    exact Matrix.rank_eq_finrank_range_toLin c (Pi.basisFun K l) (Pi.basisFun K l)
  have hr2 : cᵀ.rank = Module.finrank K ↥(Matrix.mulVecLin cᵀ).range := by
    rw [← Matrix.toLin'_apply']
    exact Matrix.rank_eq_finrank_range_toLin cᵀ (Pi.basisFun K l) (Pi.basisFun K l)
  have hr : Module.finrank K ↥(Matrix.mulVecLin c).range =
       Module.finrank K ↥(Matrix.mulVecLin cᵀ).range := by
    calc
      Module.finrank K ↥(Matrix.mulVecLin c).range = c.rank := hr1.symm
      _ = cᵀ.rank := (Matrix.rank_transpose c).symm
      _ = Module.finrank K ↥(Matrix.mulVecLin cᵀ).range := hr2
  have hk1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin c)
  have hk2 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin cᵀ)
  have hk1' : Module.finrank K ↥(Matrix.mulVecLin c).range +
      Module.finrank K ↥(Matrix.mulVecLin c).ker = Fintype.card l := by
    simpa [Module.finrank_pi] using hk1
  have hk2' : Module.finrank K ↥(Matrix.mulVecLin cᵀ).range +
      Module.finrank K ↥(Matrix.mulVecLin cᵀ).ker = Fintype.card l := by
    simpa [Module.finrank_pi] using hk2
  omega
-- test isotropic and induced equivalence
private lemma map_ker_mulVec_to_ker_transpose {l K : Type*} [DecidableEq l] [Fintype l] [Field K]
 (a b c d : Matrix l l K)
 (e : cᵀ * a = aᵀ * c)
 (kinj : ∀ x : l → K, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0) :
 ∃ f : (Matrix.mulVecLin c).ker →ₗ[K] (Matrix.mulVecLin cᵀ).ker,
     Function.Bijective f ∧
     ∀ u, (f u : l → K) = a *ᵥ (u : l → K) := by
  let A₀ : (l → K) →ₗ[K] (l → K) := Matrix.mulVecLin a
  let C₀ : (l → K) →ₗ[K] (l → K) := Matrix.mulVecLin c
  let D₀ : (l → K) →ₗ[K] (l → K) := Matrix.mulVecLin cᵀ
  have him : ∀ x : C₀.ker, (A₀ (x : l → K)) ∈ D₀.ker := by
    intro x
    change cᵀ *ᵥ (a *ᵥ (x : l → K)) = 0
    have hx : c *ᵥ (x : l → K) = 0 := by
      have hxm := x.property
      change c *ᵥ (x : l → K) = 0 at hxm
      exact hxm
    calc
      cᵀ *ᵥ (a *ᵥ (x : l → K)) = (cᵀ * a) *ᵥ (x : l → K) :=
          Matrix.mulVec_mulVec _ _ _
      _ = (aᵀ * c) *ᵥ (x : l → K) := by rw [e]
      _ = aᵀ *ᵥ (c *ᵥ (x : l → K)) :=
            (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hx]; exact Matrix.mulVec_zero _
  let f : C₀.ker →ₗ[K] D₀.ker :=
    LinearMap.codRestrict D₀.ker (A₀ ∘ₗ C₀.ker.subtype) (by
      intro x
      exact him x)
  have fi : Function.Injective f := by
    -- kernel criterion on underlying vector equations
    intro x y hxy
    -- subtract and use kinj directly: since c x=c y
    apply Subtype.ext
    have haxy : a *ᵥ (x : l → K) = a *ᵥ (y : l → K) := by
      exact congrArg Subtype.val hxy
    let z : l → K := (x : l → K) - (y : l → K)
    have haz : a *ᵥ z = 0 := by
      dsimp [z]
      rw [Matrix.mulVec_sub, haxy, sub_self]
    have hcz : c *ᵥ z = 0 := by
      dsimp [z]
      rw [Matrix.mulVec_sub]
      have hx : c *ᵥ (x : l → K) = 0 := by
        have hx0 := x.property
        change c *ᵥ (x : l → K) = 0 at hx0
        exact hx0
      have hy : c *ᵥ (y : l → K) = 0 := by
        have hx0 := y.property
        change c *ᵥ (y : l → K) = 0 at hx0
        exact hx0
      simp [hx, hy]
    have hz := kinj z haz hcz
    change (x : l → K) = (y : l → K)
    exact sub_eq_zero.mp hz
  have hk : Module.finrank K C₀.ker = Module.finrank K D₀.ker := by
    change Module.finrank K (Matrix.mulVecLin c).ker =
      Module.finrank K (Matrix.mulVecLin cᵀ).ker
    exact finrank_ker_mulVec_transpose c
  have fs : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hk).mp fi
  refine ⟨f, ⟨fi, fs⟩, ?_⟩
  intro u
  rfl
open Matrix
private lemma extend_symmetric_bilin_to_matrix {l K : Type*} [DecidableEq l] [Fintype l] [Field K]
 (W : Submodule K (l → K))
 (H : LinearMap.BilinForm K W)
 (hs : ∀ x y, H x y = H y x) :
 ∃ t : Matrix l l K, tᵀ = t ∧
   ∀ x y : W, (x : l → K) ⬝ᵥ (t *ᵥ (y : l → K)) = H x y := by
  -- choose a projection onto W
  have ki : (W.subtype).ker = (⊥ : Submodule K W) := Submodule.ker_subtype W
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (W.subtype) ki
  -- p : V -> W, hp : p ∘ subtype = id
  have hp' : ∀ x : W, p (x : l → K) = x := by
    intro x
    have hpx := LinearMap.congr_fun hp x
    simpa using hpx
  -- extend the bilinear form by the projection in each argument
  let B : LinearMap.BilinForm K (l → K) :=
    LinearMap.mk₂ K (fun x y : l → K => H (p x) (p y))
      (by intro x y z; simp)
      (by intro c x y; simp)
      (by intro x y z; simp)
      (by intro c x y; simp)
  have B_apply (x y : l → K) : B x y = H (p x) (p y) := rfl
  have Bsym : ∀ x y, B x y = B y x := by
    intro x y
    simpa [B_apply] using hs (p x) (p y)
  let t : Matrix l l K :=
    (LinearMap.BilinForm.toMatrix (Pi.basisFun K l)) B
  have tsym : tᵀ = t := by
    ext i j
    -- entries are evaluations on basis vectors
    change t j i = t i j
    dsimp [t]
    rw [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply]
    exact Bsym _ _
  refine ⟨t, tsym, ?_⟩
  intro x y
  have hb := LinearMap.BilinForm.dotProduct_toMatrix_mulVec (Pi.basisFun K l)
        B (x : l → K) (y : l → K)
  -- equivalence sends coordinates back to the same vector
  -- since the chosen basis is `basisFun`
  have hx : (Pi.basisFun K l).equivFun.symm (x : l → K) = (x : l → K) := by
    -- linear equiv equals refl
    have he := Pi.basisFun_equivFun K l
    -- he : ...equivFun = refl
    rw [he]
    rfl
  have hy : (Pi.basisFun K l).equivFun.symm (y : l → K) = (y : l → K) := by
    rw [Pi.basisFun_equivFun K l]
    rfl
  change (x : l → K) ⬝ᵥ (t *ᵥ (y : l → K)) = H x y
  rw [show (x : l → K) ⬝ᵥ (t *ᵥ (y : l → K)) =
      B ((x : l → K)) ((y : l → K)) by simpa [t, hx, hy] using hb]
  simp [B_apply, hp']
private lemma bigCell_field {l K : Type*} [DecidableEq l] [Fintype l] [Field K]
 (a b c d : Matrix l l K)
 (e : cᵀ * a = aᵀ * c)
 (kinj : ∀ x : l → K, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0) :
 ∃ t : Matrix l l K, tᵀ = t ∧ IsUnit (a + t * c) := by
  classical
  let A₀ : (l → K) →ₗ[K] (l → K) := Matrix.mulVecLin a
  let C₀ : (l → K) →ₗ[K] (l → K) := Matrix.mulVecLin c
  let W : Submodule K (l → K) := C₀.range
  -- choose a linear section of C onto its range
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective
      (C₀.rangeRestrict) (LinearMap.range_rangeRestrict C₀)
  have hs' : ∀ y : W, c *ᵥ (s y) = (y : l → K) := by
    intro y
    have hy := LinearMap.congr_fun hs y
    -- congr_fun returns rangeRestrict ... = y subtype; take val
    have hyv := congrArg Subtype.val hy
    simpa [C₀, Matrix.mulVecLin_apply] using hyv
  -- the symmetric form on the image given by A
  let F : LinearMap.BilinForm K W :=
    LinearMap.mk₂ K
      (fun z y : W => (z : l → K) ⬝ᵥ (a *ᵥ (s y)))
      (by intro x y z; simp [add_dotProduct])
      (by intro t x y; simp [smul_dotProduct])
      (by intro x y z; simp [Matrix.mulVec_add, dotProduct_add])
      (by intro t x y; simp [Matrix.mulVec_smul, dotProduct_smul])
  have F_apply (z y : W) : F z y = (z : l → K) ⬝ᵥ (a *ᵥ (s y)) := rfl
  have Fsym : ∀ z y, F z y = F y z := by
    intro z y
    -- replace z,y with c*s z, c*s y and use c^T a = a^T c
    change (z : l → K) ⬝ᵥ (a *ᵥ (s y)) =
      (y : l → K) ⬝ᵥ (a *ᵥ (s z))
    rw [← hs' z, ← hs' y]
    -- need isotropy identity
    -- via dotProduct_mulVec etc using e
    -- prove auxiliary below inline
    calc
      (c *ᵥ (s z)) ⬝ᵥ (a *ᵥ (s y)) =
          (s z) ⬝ᵥ (cᵀ *ᵥ (a *ᵥ (s y))) := by
            have hh := Matrix.dotProduct_mulVec (s z) cᵀ (a *ᵥ (s y))
            simpa [Matrix.vecMul_transpose] using hh.symm
      _ = (s z) ⬝ᵥ ((cᵀ * a) *ᵥ (s y)) := by
            rw [← Matrix.mulVec_mulVec]
      _ = (s z) ⬝ᵥ ((aᵀ * c) *ᵥ (s y)) := by rw [e]
      _ = (s z) ⬝ᵥ (aᵀ *ᵥ (c *ᵥ (s y))) := by
            rw [Matrix.mulVec_mulVec]
      _ = (c *ᵥ (s y)) ⬝ᵥ (a *ᵥ (s z)) := by
            exact Matrix.dotProduct_transpose_mulVec _ _ _
  -- a standard nondegenerate form on W via a basis
  let bas := Module.finBasis K W
  let G : LinearMap.BilinForm K W :=
    LinearMap.mk₂ K
      (fun z y : W => (bas.equivFun z) ⬝ᵥ (bas.equivFun y))
      (by intro x y z; simp [add_dotProduct])
      (by intro t x y; simp [smul_dotProduct])
      (by intro x y z; simp [dotProduct_add])
      (by intro t x y; simp [dotProduct_smul])
  have G_apply (z y : W) : G z y = (bas.equivFun z) ⬝ᵥ (bas.equivFun y) := rfl
  have Gsym : ∀ z y, G z y = G y z := by
    intro z y
    change bas.equivFun z ⬝ᵥ bas.equivFun y = _
    exact dotProduct_comm _ _
  have Gnon : ∀ y : W, (∀ z : W, G z y = 0) → y = 0 := by
    intro y hz
    -- coordinates vanish testing basis vectors
    apply bas.equivFun.injective
    apply funext
    intro i
    have hzi := hz (bas i)
    change (bas.equivFun y) i = (bas.equivFun (0 : W)) i
    simp only [map_zero, Pi.zero_apply]
    -- equivFun(bas i) is the i-th standard basis
    -- unfold G and dotProduct; use single_dotProduct or sums
    change (bas.equivFun (bas i)) ⬝ᵥ (bas.equivFun y) = 0 at hzi
    have hcoord : bas.equivFun (bas i) = Pi.single i (1 : K) := by
      ext j
      classical
      simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
    rw [hcoord, single_dotProduct] at hzi
    simpa using hzi
  let H : LinearMap.BilinForm K W := G - F
  have Hsym : ∀ z y, H z y = H y z := by
    intro z y
    change G z y - F z y = G y z - F y z
    rw [Gsym, Fsym]
  obtain ⟨t, ht, htform⟩ := extend_symmetric_bilin_to_matrix W H Hsym
  refine ⟨t, ht, ?_⟩
  -- over a field square matrix IsUnit iff trivial kernel
  have inj : Function.Injective (Matrix.mulVec (a + t*c)) := by
    -- actually criterion via mulVec_injective_iff_isUnit
    intro x y hxy
    -- use z=x-y to show zero
    have hz0 : (a + t*c) *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have heq : a *ᵥ (x-y) + t *ᵥ (c *ᵥ (x-y)) = 0 := by
      simpa [Matrix.add_mulVec, ← Matrix.mulVec_mulVec] using hz0
    let yy : l → K := c *ᵥ (x-y)
    have ymem : yy ∈ W := by
      refine ⟨x-y, ?_⟩
      rfl
    let yW : W := ⟨yy, ymem⟩
    have hGzero : ∀ z : W, G z yW = 0 := by
      intro z
      -- pair heq with z; apply H formula
      have pair0 : (z : l → K) ⬝ᵥ (a *ᵥ (x-y) + t *ᵥ (c *ᵥ (x-y))) = 0 := by
        rw [heq]
        simp
      have hform : (z : l → K) ⬝ᵥ (t *ᵥ (yy)) = H z yW := htform z yW
      rw [dotProduct_add] at pair0
      -- F z yW equals dot z (a * (x-y)): difference section lies ker
      have feq : F z yW = (z : l → K) ⬝ᵥ (a *ᵥ (x-y)) := by
        change (z : l → K) ⬝ᵥ (a *ᵥ (s yW)) = _
        -- use symmetry of F and isotropy avoids membership orth proof:
        -- z=c*s z
        rw [← hs' z]
        -- transform via e then section y
        calc
          (c *ᵥ (s z)) ⬝ᵥ (a *ᵥ (s yW)) =
              (c *ᵥ (s yW)) ⬝ᵥ (a *ᵥ (s z)) := by
                have q := Fsym z yW
                change (z : l → K) ⬝ᵥ (a *ᵥ (s yW)) =
                    (yW : l → K) ⬝ᵥ (a *ᵥ (s z)) at q
                simpa [hs' z, hs' yW] using q
          _ = (c *ᵥ (x-y)) ⬝ᵥ (a *ᵥ (s z)) := by
            rw [hs' yW]
          _ = (c *ᵥ (s z)) ⬝ᵥ (a *ᵥ (x-y)) := by
            -- isotropy for arbitrary
            calc
              (c *ᵥ (x-y)) ⬝ᵥ (a *ᵥ (s z)) =
                 (x-y) ⬝ᵥ (cᵀ *ᵥ (a *ᵥ (s z))) := by
                   have hh := Matrix.dotProduct_mulVec (x-y) cᵀ (a *ᵥ (s z))
                   simpa [Matrix.vecMul_transpose] using hh.symm
              _ = (x-y) ⬝ᵥ ((cᵀ * a) *ᵥ (s z)) := by rw [← Matrix.mulVec_mulVec]
              _ = (x-y) ⬝ᵥ ((aᵀ * c) *ᵥ (s z)) := by rw [e]
              _ = (x-y) ⬝ᵥ (aᵀ *ᵥ (c *ᵥ (s z))) := by rw [Matrix.mulVec_mulVec]
              _ = (c *ᵥ (s z)) ⬝ᵥ (a *ᵥ (x-y)) :=
                 Matrix.dotProduct_transpose_mulVec _ _ _
      -- H = G-F
      change G z yW = 0
      have hform' : (z : l → K) ⬝ᵥ (t *ᵥ yy) = G z yW - F z yW := by
        simpa [H, LinearMap.sub_apply] using hform
      have p' : (z : l → K) ⬝ᵥ (a *ᵥ (x-y)) +
          (z : l → K) ⬝ᵥ (t *ᵥ yy) = 0 := by
        simpa [yy] using pair0
      rw [feq] at hform'
      calc
        G z yW = (z : l → K) ⬝ᵥ (a *ᵥ (x-y)) +
            (z : l → K) ⬝ᵥ (t *ᵥ yy) := by
              linear_combination hform'.symm
        _ = 0 := p'
    have yw0 := Gnon yW hGzero
    have cy0 : c *ᵥ (x-y) = 0 := by
      have v := congrArg Subtype.val yw0
      exact v
    have ax0 : a *ᵥ (x-y) = 0 := by simpa [cy0] using heq
    have subzero := kinj (x-y) ax0 cy0
    exact sub_eq_zero.mp subzero
  exact (Matrix.mulVec_injective_iff_isUnit).mp inj


-- Over a field the open symmetric-shear charts already cover the whole
-- Lagrangian Grassmannian.  The preceding bilinear construction proves this
-- without any appeal to cardinality of the field (and works for finite fields
-- as well).  It is a convenient field-level reduction of the determinant
-- problem.
private lemma sympl_det_field
    {l K : Type*} [DecidableEq l] [Fintype l] [Field K]
    (a b c d : Matrix l l K)
    (h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l K) :
    (Matrix.fromBlocks a b c d).det = 1 := by
  classical
  have e : cᵀ * a = aᵀ * c := symplectic_first_columns_isotropic a b c d h
  have ki : ∀ x : l → K, a *ᵥ x = 0 → c *ᵥ x = 0 → x = 0 :=
    fun x ha hc => symplectic_first_columns_ker a b c d h x ha hc
  obtain ⟨t, ht, hu⟩ := bigCell_field a b c d e ki
  exact sympl_det_of_invertible_add_mul a b c d t ht hu h



private lemma sympl_det_domain
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R] [IsDomain R]
    (a b c d : Matrix l l R)
    (h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l R) :
    (Matrix.fromBlocks a b c d).det = 1 := by
  classical
  let f : R →+* FractionRing R := algebraMap R (FractionRing R)
  let a' := a.map f
  let b' := b.map f
  let c' := c.map f
  let d' := d.map f
  have h0 : Matrix.fromBlocks a b c d * Matrix.J l R *
      (Matrix.fromBlocks a b c d)ᵀ = Matrix.J l R :=
    (SymplecticGroup.mem_iff).1 h
  have hj : (Matrix.J l R).map f = Matrix.J l (FractionRing R) := by
    simp [Matrix.J, Matrix.fromBlocks_map, f, Matrix.map_neg]
  have hf : Matrix.fromBlocks a' b' c' d' ∈
      Matrix.symplecticGroup l (FractionRing R) := by
    rw [SymplecticGroup.mem_iff]
    have q := congrArg (fun z : Matrix (l ⊕ l) (l ⊕ l) R => z.map f) h0
    simpa [Matrix.map_mul, Matrix.transpose_map, Matrix.fromBlocks_map,
      a', b', c', d', hj] using q
  have hd := sympl_det_field a' b' c' d' hf
  have hd' : f ((Matrix.fromBlocks a b c d).det) = f (1:R) := by
    simpa [a', b', c', d', Matrix.fromBlocks_map,
      RingHom.map_det] using hd
  exact (IsFractionRing.injective R (FractionRing R)) hd'



-- Reduction over a local ring, by passing to the residue field and lifting
-- a symmetric shear.
private lemma sympl_det_local
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R] [IsLocalRing R]
    (a b c d : Matrix l l R)
    (h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l R) :
    (Matrix.fromBlocks a b c d).det = 1 := by
  classical
  let K := IsLocalRing.ResidueField R
  let f : R →+* K := IsLocalRing.residue R
  let a' : Matrix l l K := a.map f
  let b' : Matrix l l K := b.map f
  let c' : Matrix l l K := c.map f
  let d' : Matrix l l K := d.map f
  have h0 : Matrix.fromBlocks a b c d * Matrix.J l R *
        (Matrix.fromBlocks a b c d)ᵀ = Matrix.J l R :=
    (SymplecticGroup.mem_iff).1 h
  have hj : (Matrix.J l R).map f = Matrix.J l K := by
    simp [Matrix.J, Matrix.fromBlocks_map, f, Matrix.map_neg]
  have hf : Matrix.fromBlocks a' b' c' d' ∈
      Matrix.symplecticGroup l K := by
    rw [SymplecticGroup.mem_iff]
    have q := congrArg (fun z : Matrix (l ⊕ l) (l ⊕ l) R => z.map f) h0
    simpa [Matrix.map_mul, Matrix.transpose_map, Matrix.fromBlocks_map,
      a', b', c', d', hj] using q
  have ee : c'ᵀ * a' = a'ᵀ * c' :=
    symplectic_first_columns_isotropic a' b' c' d' hf
  have kk : ∀ x : l → K, a' *ᵥ x = 0 → c' *ᵥ x = 0 → x = 0 :=
    fun x hx hy => symplectic_first_columns_ker a' b' c' d' hf x hx hy
  obtain ⟨tb, htb, hub⟩ := bigCell_field a' b' c' d' ee kk
  -- choose scalar lifts; use a fixed enumeration to choose the same lift
  -- on the two sides of the diagonal.
  let efin : l ≃ Fin (Fintype.card l) := Fintype.equivFin l
  let lift : K → R := fun z => Classical.choose (IsLocalRing.residue_surjective z)
  have lift_spec (z : K) : f (lift z) = z :=
    Classical.choose_spec (IsLocalRing.residue_surjective z)
  let u : Matrix l l R := fun i j => lift (tb i j)
  let t : Matrix l l R := fun i j =>
    if efin i ≤ efin j then u i j else u j i
  have ht : tᵀ = t := by
    ext i j
    change t j i = t i j
    dsimp [t]
    by_cases hij : efin i ≤ efin j
    · by_cases hji : efin j ≤ efin i
      · have he : i = j := efin.injective (le_antisymm hij hji)
        subst j
        simp
      · simp [hij, hji]
    · have hji : efin j ≤ efin i := le_of_not_ge hij
      simp [hij, hji]
  have tm : t.map f = tb := by
    ext i j
    change f (t i j) = tb i j
    dsimp [t]
    by_cases hij : efin i ≤ efin j
    · simp [hij, u, lift_spec]
    · have hji : efin j ≤ efin i := le_of_not_ge hij
      have tbji : tb j i = tb i j := by
        have q := congrArg (fun X : Matrix l l K => X i j) htb
        -- htb says transpose = itself
        -- its (i,j) entry is tb j i
        simpa using q
      simp [hij, u, lift_spec, tbji]
  have humatK : IsUnit ((a + t * c).map f) := by
    have eqm : (a + t * c).map f = a' + tb * c' := by
      simp [Matrix.map_add, Matrix.map_mul, tm, a', c']
    rw [eqm]
    exact hub
  have hudetK : IsUnit (f ((a + t * c).det)) := by
    have hu' : IsUnit (((a + t * c).map f).det) :=
      (Matrix.isUnit_iff_isUnit_det ((a + t*c).map f)).1 humatK
    simpa [RingHom.map_det] using hu'
  have hudet0 : f ((a + t*c).det) ≠ 0 := hudetK.ne_zero
  have hudet : IsUnit ((a + t*c).det) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit ((a + t*c).det)).1 hudet0
  have hu : IsUnit (a + t*c) :=
    (Matrix.isUnit_iff_isUnit_det (a + t*c)).2 hudet
  exact sympl_det_of_invertible_add_mul a b c d t ht hu h

/- ann ideal test follows -/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem symplectic_matrix_det {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    {A : Matrix (l ⊕ l) (l ⊕ l) R} (_hA : A ∈ Matrix.symplecticGroup l R) :
    A.det = 1 :=
/-ResultProofBegin-/by
  classical
  let a : Matrix l l R := Matrix.toBlocks₁₁ A
  let b : Matrix l l R := Matrix.toBlocks₁₂ A
  let c : Matrix l l R := Matrix.toBlocks₂₁ A
  let d : Matrix l l R := Matrix.toBlocks₂₂ A
  have hblocks : Matrix.fromBlocks a b c d = A := by
    simpa [a,b,c,d] using (Matrix.fromBlocks_toBlocks A)
  have h : Matrix.fromBlocks a b c d ∈ Matrix.symplecticGroup l R := by
    rw [hblocks]
    exact _hA
  rw [← hblocks]
  -- equality can be checked in all local rings.  We spell out that elementary
  -- localization argument to retain nilpotents.
  let r : R := (Matrix.fromBlocks a b c d).det - 1
  suffices hr : r = 0 by
    exact sub_eq_zero.mp hr
  by_contra hn
  have hn' : r ≠ 0 := hn
  -- annihilator of r
  let I : Ideal R :=
    { carrier := {x : R | x * r = 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change x * r = 0 at hx
        change y * r = 0 at hy
        change (x + y) * r = 0
        simp [add_mul, hx, hy]
      smul_mem' := by
        intro s x hx
        change x * r = 0 at hx
        change (s * x) * r = 0
        rw [mul_assoc, hx, mul_zero] }
  have hI : I ≠ (⊤ : Ideal R) := by
    intro hi
    have h1 : (1 : R) ∈ I := by
      rw [hi]
      trivial
    change (1:R) * r = 0 at h1
    have : r = 0 := by simpa using h1
    exact hn' this
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal I hI
  letI hprime : P.IsPrime := hPmax.isPrime
  let S := Localization.AtPrime P
  letI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S P
  let g : R →+* S := algebraMap R S
  let aS : Matrix l l S := a.map g
  let bS : Matrix l l S := b.map g
  let cS : Matrix l l S := c.map g
  let dS : Matrix l l S := d.map g
  have hj : (Matrix.J l R).map g = Matrix.J l S := by
    simp [Matrix.J, Matrix.fromBlocks_map, g, Matrix.map_neg]
  have hs : Matrix.fromBlocks aS bS cS dS ∈ Matrix.symplecticGroup l S := by
    rw [SymplecticGroup.mem_iff]
    have h0 : Matrix.fromBlocks a b c d * Matrix.J l R *
          (Matrix.fromBlocks a b c d)ᵀ = Matrix.J l R :=
      (SymplecticGroup.mem_iff).1 h
    have q := congrArg (fun z : Matrix (l ⊕ l) (l ⊕ l) R => z.map g) h0
    simpa [Matrix.map_mul, Matrix.transpose_map, Matrix.fromBlocks_map,
      aS, bS, cS, dS, hj] using q
  have hdetS := sympl_det_local aS bS cS dS hs
  have hgr : g r = 0 := by
    have hv : g ((Matrix.fromBlocks a b c d).det) = (1:S) := by
      simpa [aS, bS, cS, dS, Matrix.fromBlocks_map, RingHom.map_det] using hdetS
    simp [r, hv]
  have hex : ∃ w : P.primeCompl, (w:R) * r = 0 :=
    (IsLocalization.map_eq_zero_iff P.primeCompl S r).1 hgr
  obtain ⟨w, hw⟩ := hex
  have wi : (w:R) ∈ I := by
    change (w:R) * r = 0
    exact hw
  have wp : (w:R) ∈ P := hIP wi
  exact w.property wp
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
