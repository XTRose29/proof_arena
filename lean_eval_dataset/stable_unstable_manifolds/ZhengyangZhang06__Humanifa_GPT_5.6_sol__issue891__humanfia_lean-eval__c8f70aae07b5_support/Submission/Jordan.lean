import Mathlib

open Function Module Set Submodule

namespace Submission.Jordan

set_option maxHeartbeats 800000

/-- A basis arranged in Jordan chains for a linear endomorphism. -/
structure JordanChainBasis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) where
  ι : Type
  [finite : Fintype ι]
  [decidableEq : DecidableEq ι]
  size : ι → ℕ
  positive_size : ∀ i, 0 < size i
  eigenvalue : ι → K
  basis : Module.Basis (Σ i : ι, Fin (size i)) K V
  chain :
    ∀ (i : ι) (j : Fin (size i)),
      f (basis ⟨i, j⟩) =
        eigenvalue i • basis ⟨i, j⟩ +
          if j.val = 0 then 0
          else basis ⟨i, ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩⟩

attribute [instance] JordanChainBasis.finite JordanChainBasis.decidableEq

/-- Coordinates of the image of a vector in a Jordan-chain basis. -/
theorem JordanChainBasis.repr_apply {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {f : Module.End K V} (c : JordanChainBasis f)
    (i : c.ι) (j : Fin (c.size i)) (x : V) :
    c.basis.repr (f x) ⟨i, j⟩ =
      c.eigenvalue i * c.basis.repr x ⟨i, j⟩ +
        if h : j.val + 1 < c.size i then
          c.basis.repr x ⟨i, ⟨j.val + 1, h⟩⟩
        else 0 := by
  classical
  let t : Σ i : c.ι, Fin (c.size i) := ⟨i, j⟩
  let nextCoord : V →ₗ[K] K :=
    if h : j.val + 1 < c.size i then
      c.basis.coord ⟨i, ⟨j.val + 1, h⟩⟩
    else 0
  have nextCoord_apply (y : V) :
      nextCoord y =
        if h : j.val + 1 < c.size i then
          c.basis.repr y ⟨i, ⟨j.val + 1, h⟩⟩
        else 0 := by
    by_cases h : j.val + 1 < c.size i
    · simp [nextCoord, h, Module.Basis.coord_apply]
    · simp [nextCoord, h]
  have nextCoord_basis_eq_zero
      (p : Σ i : c.ι, Fin (c.size i))
      (hne : ∀ h : j.val + 1 < c.size i,
        (⟨i, ⟨j.val + 1, h⟩⟩ :
          Σ i : c.ι, Fin (c.size i)) ≠ p) :
      nextCoord (c.basis p) = 0 := by
    rw [nextCoord_apply]
    split
    · rename_i h
      simp [Ne.symm (hne h)]
    · rfl
  have nextCoord_basis_eq_one (h : j.val + 1 < c.size i) :
      nextCoord (c.basis ⟨i, ⟨j.val + 1, h⟩⟩) = 1 := by
    rw [nextCoord_apply]
    simp [h]
  have hmaps :
      (c.basis.coord t).comp f =
        c.eigenvalue i • c.basis.coord t + nextCoord := by
    apply c.basis.ext
    rintro ⟨l, k⟩
    rw [LinearMap.comp_apply, c.chain]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    by_cases hli : l = i
    · subst l
      by_cases hkj : k = j
      · subst k
        have hnext :
            ∀ h : j.val + 1 < c.size i,
              (⟨i, ⟨j.val + 1, h⟩⟩ :
                  Σ i : c.ι, Fin (c.size i)) ≠ ⟨i, j⟩ := by
            intro hn h
            have hfin :
                (⟨j.val + 1, hn⟩ :
                  Fin (c.size i)) = j := by
              simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
            have hv := congrArg Fin.val hfin
            change j.val + 1 = j.val at hv
            omega
        have hnextZero :=
          nextCoord_basis_eq_zero (⟨i, j⟩ :
            Σ i : c.ι, Fin (c.size i)) hnext
        by_cases hj0 : j.val = 0
        · simp [t, hj0, hnextZero]
        · have hpred :
              (⟨i, ⟨j.val - 1,
                lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩⟩ :
                  Σ i : c.ι, Fin (c.size i)) ≠ t := by
              intro h
              have hv := congrArg (fun p : Σ i : c.ι, Fin (c.size i) => p.2.val) h
              dsimp [t] at hv
              omega
          simp [t, hj0, Ne.symm hpred, hnextZero]
      · by_cases hsucc : k.val = j.val + 1
        · have hnext : j.val + 1 < c.size i := hsucc ▸ k.isLt
          have hk0 : k.val ≠ 0 := by omega
          have hpred :
              (⟨i, ⟨k.val - 1,
                lt_of_le_of_lt (Nat.sub_le k.val 1) k.isLt⟩⟩ :
                  Σ i : c.ι, Fin (c.size i)) = t := by
              have hfin :
                  (⟨k.val - 1,
                    lt_of_le_of_lt (Nat.sub_le k.val 1) k.isLt⟩ :
                      Fin (c.size i)) = j := by
                apply Fin.ext
                change k.val - 1 = j.val
                omega
              exact congrArg
                (fun z : Fin (c.size i) =>
                  (⟨i, z⟩ : Σ i : c.ι, Fin (c.size i))) hfin
          have hnextEq :
              (⟨i, ⟨j.val + 1, hnext⟩⟩ :
                  Σ i : c.ι, Fin (c.size i)) = ⟨i, k⟩ := by
              exact congrArg
                (fun z : Fin (c.size i) =>
                  (⟨i, z⟩ : Σ i : c.ι, Fin (c.size i)))
                (Fin.ext hsucc.symm)
          have hpt :
              (⟨i, k⟩ : Σ i : c.ι, Fin (c.size i)) ≠ t := by
              intro h
              apply hkj
              exact Fin.ext (congrArg
                (fun p : Σ i : c.ι, Fin (c.size i) => p.2.val) h)
          have hnextOne : nextCoord (c.basis ⟨i, k⟩) = 1 := by
            rw [← hnextEq]
            exact nextCoord_basis_eq_one hnext
          simp [t, hk0, hpred, hnextOne,
            Ne.symm hpt]
        · have hpt :
              (⟨i, k⟩ : Σ i : c.ι, Fin (c.size i)) ≠ t := by
              intro h
              apply hkj
              exact Fin.ext (congrArg
                (fun p : Σ i : c.ι, Fin (c.size i) => p.2.val) h)
          have hpred :
              k.val ≠ 0 →
                (⟨i, ⟨k.val - 1,
                  lt_of_le_of_lt (Nat.sub_le k.val 1) k.isLt⟩⟩ :
                    Σ i : c.ι, Fin (c.size i)) ≠ t := by
              intro hk0 h
              apply hsucc
              have hv := congrArg
                (fun p : Σ i : c.ι, Fin (c.size i) => p.2.val) h
              dsimp [t] at hv
              omega
          have hnext :
              ∀ h : j.val + 1 < c.size i,
                (⟨i, ⟨j.val + 1, h⟩⟩ :
                    Σ i : c.ι, Fin (c.size i)) ≠ ⟨i, k⟩ := by
              intro _ h
              apply hsucc
              exact (congrArg
                (fun p : Σ i : c.ι, Fin (c.size i) => p.2.val) h).symm
          have hnextZero :=
            nextCoord_basis_eq_zero (⟨i, k⟩ :
              Σ i : c.ι, Fin (c.size i)) hnext
          by_cases hk0 : k.val = 0
          · simp [t, hk0, Ne.symm hpt, hnextZero]
          · simp [t, hk0, Ne.symm hpt, Ne.symm (hpred hk0),
              hnextZero]
    · have hpt :
          (⟨l, k⟩ : Σ i : c.ι, Fin (c.size i)) ≠ t := by
          intro h
          exact hli (congrArg Sigma.fst h)
      have hpred :
          ∀ hk0 : k.val ≠ 0,
            (⟨l, ⟨k.val - 1,
              lt_of_le_of_lt (Nat.sub_le k.val 1) k.isLt⟩⟩ :
                Σ i : c.ι, Fin (c.size i)) ≠ t := by
          intro _ h
          exact hli (congrArg Sigma.fst h)
      have hnext :
          ∀ h : j.val + 1 < c.size i,
            (⟨i, ⟨j.val + 1, h⟩⟩ :
                Σ i : c.ι, Fin (c.size i)) ≠ ⟨l, k⟩ := by
          intro _ h
          exact hli ((congrArg Sigma.fst h).symm)
      have hnextZero :=
        nextCoord_basis_eq_zero (⟨l, k⟩ :
          Σ i : c.ι, Fin (c.size i)) hnext
      by_cases hk0 : k.val = 0
      · simp [t, hk0, Ne.symm hpt, hnextZero]
      · simp [t, hk0, Ne.symm hpt, Ne.symm (hpred hk0),
          hnextZero]
  have hx := LinearMap.congr_fun hmaps x
  simp only [LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul] at hx
  rw [nextCoord_apply] at hx
  simpa [t, Module.Basis.coord_apply] using hx

/-- A basis arranged in chains for a nilpotent endomorphism. -/
structure NilpotentChainBasis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) where
  ι : Type
  [finite : Fintype ι]
  [decidableEq : DecidableEq ι]
  size : ι → ℕ
  positive_size : ∀ i, 0 < size i
  basis : Basis (Σ i : ι, Fin (size i)) K V
  chain :
    ∀ (i : ι) (j : Fin (size i)),
      f (basis ⟨i, j⟩) =
        if j.val = 0 then 0
        else basis ⟨i, ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩⟩

attribute [instance] NilpotentChainBasis.finite NilpotentChainBasis.decidableEq

private def sigmaFinOneEquiv (ι : Type*) : (Σ _ : ι, Fin 1) ≃ ι :=
  (Equiv.sigmaCongrRight fun _ => finOneEquiv).trans (Equiv.sigmaPUnit ι)

private def sigmaFinSuccEquiv {ι : Type*} (s : ι → ℕ) :
    (Σ i, Fin (s i + 1)) ≃ (Σ i, Fin (s i)) ⊕ ι :=
  ((Equiv.sigmaCongrRight fun i => (@finSumFinEquiv (s i) 1).symm).trans
      (Equiv.sigmaSumDistrib (fun i => Fin (s i)) (fun _ => Fin 1))).trans
    (Equiv.sumCongr (Equiv.refl _) (sigmaFinOneEquiv ι))

@[simp]
private theorem sigmaFinSuccEquiv_castSucc {ι : Type*} (s : ι → ℕ)
    (i : ι) (j : Fin (s i)) :
    sigmaFinSuccEquiv s ⟨i, Fin.castSucc j⟩ = Sum.inl ⟨i, j⟩ := by
  unfold sigmaFinSuccEquiv
  simp only [Equiv.trans_apply]
  have h :
      (Equiv.sigmaCongrRight fun i => (@finSumFinEquiv (s i) 1).symm)
          ⟨i, Fin.castSucc j⟩ =
        (⟨i, Sum.inl j⟩ : Σ i, Fin (s i) ⊕ Fin 1) := by
    change (⟨i, (@finSumFinEquiv (s i) 1).symm (Fin.castSucc j)⟩ :
        Σ i, Fin (s i) ⊕ Fin 1) = ⟨i, Sum.inl j⟩
    rw [finSumFinEquiv_symm_apply_castSucc]
  rw [h]
  rfl

@[simp]
private theorem sigmaFinSuccEquiv_last {ι : Type*} (s : ι → ℕ) (i : ι) :
    sigmaFinSuccEquiv s ⟨i, Fin.last (s i)⟩ = Sum.inr i := by
  unfold sigmaFinSuccEquiv
  simp only [Equiv.trans_apply]
  have h :
      (Equiv.sigmaCongrRight fun i => (@finSumFinEquiv (s i) 1).symm)
          ⟨i, Fin.last (s i)⟩ =
        (⟨i, Sum.inr 0⟩ : Σ i, Fin (s i) ⊕ Fin 1) := by
    change (⟨i, (@finSumFinEquiv (s i) 1).symm (Fin.last (s i))⟩ :
        Σ i, Fin (s i) ⊕ Fin 1) = ⟨i, Sum.inr 0⟩
    rw [finSumFinEquiv_symm_last]
  rw [h]
  rfl

private def extendChainIndexEquiv {ι q : Type*} (s : ι → ℕ) :
    (Σ x : ι ⊕ q, Fin (Sum.elim (fun i => s i + 1) (fun _ => 1) x)) ≃
      ((Σ i, Fin (s i)) ⊕ ι) ⊕ q :=
  (Equiv.sumSigmaDistrib _).trans
    (Equiv.sumCongr (sigmaFinSuccEquiv s) (sigmaFinOneEquiv q))

@[simp]
private theorem extendChainIndexEquiv_castSucc {ι q : Type*} (s : ι → ℕ)
    (i : ι) (j : Fin (s i)) :
    extendChainIndexEquiv (q := q) s ⟨Sum.inl i, Fin.castSucc j⟩ =
      Sum.inl (Sum.inl ⟨i, j⟩) := by
  simp [extendChainIndexEquiv, Equiv.sumSigmaDistrib]

@[simp]
private theorem extendChainIndexEquiv_last {ι q : Type*} (s : ι → ℕ) (i : ι) :
    extendChainIndexEquiv (q := q) s ⟨Sum.inl i, Fin.last (s i)⟩ =
      Sum.inl (Sum.inr i) := by
  simp [extendChainIndexEquiv, Equiv.sumSigmaDistrib]

@[simp]
private theorem extendChainIndexEquiv_singleton {ι q : Type*} (s : ι → ℕ)
    (a : q) (j : Fin 1) :
    extendChainIndexEquiv (q := q) s ⟨Sum.inr a, j⟩ = Sum.inr a := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simp [extendChainIndexEquiv, sigmaFinOneEquiv, Equiv.sumSigmaDistrib]

private def NilpotentChainBasis.lastIndex {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {f : Module.End K V} (c : NilpotentChainBasis f) (i : c.ι) :
    Fin (c.size i) :=
  ⟨c.size i - 1, by have := c.positive_size i; omega⟩

private theorem NilpotentChainBasis.topCoord_apply_eq_zero {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {f : Module.End K V} (c : NilpotentChainBasis f)
    (i : c.ι) (x : V) :
    c.basis.coord ⟨i, c.lastIndex i⟩ (f x) = 0 := by
  rw [← c.basis.sum_repr x, map_sum, map_sum]
  apply Finset.sum_eq_zero
  rintro ⟨l, j⟩ -
  rw [map_smul, map_smul]
  suffices c.basis.coord ⟨i, c.lastIndex i⟩ (f (c.basis ⟨l, j⟩)) = 0 by
    simp [this]
  rw [c.chain l j]
  split_ifs with hj
  · simp
  · have hne :
        (⟨l, ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩⟩ :
            Σ l, Fin (c.size l)) ≠ ⟨i, c.lastIndex i⟩ := by
      intro h
      have hli := congrArg Sigma.fst h
      change l = i at hli
      subst l
      have hv := congrArg (fun a : Σ l, Fin (c.size l) => a.2.val) h
      dsimp [NilpotentChainBasis.lastIndex] at hv
      omega
    simp [hne]

private theorem NilpotentChainBasis.top_quotient_linearIndependent
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {f : Module.End K V} (c : NilpotentChainBasis f) :
    LinearIndependent K
      ((LinearMap.range f).mkQ ∘ fun i => c.basis ⟨i, c.lastIndex i⟩) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hmem : (∑ l, a l • c.basis ⟨l, c.lastIndex l⟩) ∈ LinearMap.range f := by
    have hq : (LinearMap.range f).mkQ
        (∑ l, a l • (c.basis ⟨l, c.lastIndex l⟩ : V)) = 0 := by
      simpa [map_sum, map_smul, Function.comp_apply] using ha
    exact (Submodule.Quotient.mk_eq_zero _).mp hq
  obtain ⟨x, hx⟩ := hmem
  have hcoordSum :
      c.basis.coord ⟨i, c.lastIndex i⟩
          (∑ l, a l • c.basis ⟨l, c.lastIndex l⟩) = a i := by
    simp only [map_sum, map_smul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro l _hl hli
      have hne :
          (⟨l, c.lastIndex l⟩ : Σ l, Fin (c.size l)) ≠ ⟨i, c.lastIndex i⟩ := by
        intro h
        exact hli (congrArg Sigma.fst h)
      simp [hne]
    · simp
  calc
    a i = c.basis.coord ⟨i, c.lastIndex i⟩
        (∑ l, a l • c.basis ⟨l, c.lastIndex l⟩) := hcoordSum.symm
    _ = c.basis.coord ⟨i, c.lastIndex i⟩ (f x) := congrArg _ hx.symm
    _ = 0 := c.topCoord_apply_eq_zero i x

/-- A nilpotent endomorphism of a finite-dimensional vector space has a chain basis. -/
theorem nilpotentChainBasisOfPowEqZero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (k : ℕ) (hf : f ^ k = 0) :
    Nonempty (NilpotentChainBasis f) := by
  classical
  induction k generalizing V with
  | zero =>
      have hone : (1 : Module.End K V) = 0 := by simpa using hf
      have hzero (x : V) : x = 0 := by
        have hx := LinearMap.congr_fun hone x
        simpa using hx
      letI : Subsingleton V := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
      let emptySize : Fin 0 → ℕ := Fin.elim0
      exact ⟨{
        ι := Fin 0
        size := emptySize
        positive_size := fun i => Fin.elim0 i
        basis := Basis.empty _
        chain := fun i => Fin.elim0 i
      }⟩
  | succ k ih =>
      let Rng : Submodule K V := LinearMap.range f
      have hfR : MapsTo f Rng Rng := by
        rintro _ ⟨x, rfl⟩
        exact ⟨f x, rfl⟩
      let fR : Module.End K Rng := f.restrict hfR
      have hpowR : fR ^ k = 0 := by
        rw [Module.End.pow_restrict]
        ext x
        rcases x with ⟨_, ⟨y, rfl⟩⟩
        change (f ^ k) (f y) = 0
        simpa [pow_succ, Module.End.mul_apply] using LinearMap.congr_fun hf y
      obtain ⟨c⟩ := ih fR hpowR
      let top (i : c.ι) : Rng := c.basis ⟨i, c.lastIndex i⟩
      let lift (i : c.ι) : V := (top i).property.choose
      have hlift (i : c.ι) : f (lift i) = (top i : V) :=
        (top i).property.choose_spec
      have hliftQuot : LinearIndependent K (Rng.mkQ ∘ lift) := by
        rw [Fintype.linearIndependent_iff]
        intro a ha i
        have hsumMem : (∑ l, a l • lift l) ∈ Rng := by
          have hq : Rng.mkQ (∑ l, a l • lift l) = 0 := by
            simpa [map_sum, map_smul, Function.comp_apply] using ha
          exact (Submodule.Quotient.mk_eq_zero _).mp hq
        let y : Rng := ⟨∑ l, a l • lift l, hsumMem⟩
        have htopMem : (∑ l, a l • top l) ∈ LinearMap.range fR := by
          refine ⟨y, ?_⟩
          apply Subtype.ext
          simp [y, fR, map_sum, map_smul, hlift]
        have htopZero :
            ∑ l, a l • (LinearMap.range fR).mkQ (top l) = 0 := by
          have hq : (LinearMap.range fR).mkQ (∑ l, a l • top l) = 0 := by
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact htopMem
          rw [map_sum] at hq
          simpa only [map_smul] using hq
        exact Fintype.linearIndependent_iff.mp c.top_quotient_linearIndependent a
          (by simpa [Function.comp_apply] using htopZero) i
      let Old := Σ i : c.ι, Fin (c.size i)
      let Ext := Old ⊕ c.ι
      let extFamily : Ext → V := Sum.elim (fun a => (c.basis a : Rng)) lift
      have hext : LinearIndependent K extFamily := by
        exact LinearIndependent.sumElim_of_quotient c.basis.linearIndependent lift hliftQuot
      let P : Submodule K V := Submodule.span K (Set.range extFamily)
      have hbasisMem (a : Old) : (c.basis a : V) ∈ Submodule.map f P := by
        rcases a with ⟨i, j⟩
        by_cases hj : j.val + 1 < c.size i
        · let js : Fin (c.size i) := ⟨j.val + 1, hj⟩
          have hjsMem : (c.basis ⟨i, js⟩ : V) ∈ P := by
            have := Submodule.subset_span (R := K) (s := Set.range extFamily)
              (Set.mem_range_self (Sum.inl ⟨i, js⟩ : Ext))
            simpa [extFamily] using this
          refine ⟨(c.basis ⟨i, js⟩ : V), hjsMem, ?_⟩
          have hjs : js.val ≠ 0 := by simp [js]
          have hpred :
              (⟨js.val - 1, lt_of_le_of_lt (Nat.sub_le js.val 1) js.isLt⟩ :
                Fin (c.size i)) = j := by
            apply Fin.ext
            simp [js]
          have hc := congrArg Subtype.val (c.chain i js)
          rw [if_neg hjs, hpred] at hc
          exact hc
        · have hlast : j = c.lastIndex i := by
            apply Fin.ext
            dsimp [NilpotentChainBasis.lastIndex]
            omega
          subst j
          have hliftMem : lift i ∈ P := by
            have := Submodule.subset_span (R := K) (s := Set.range extFamily)
              (Set.mem_range_self (Sum.inr i : Ext))
            simpa [extFamily] using this
          exact ⟨lift i, hliftMem, hlift i⟩
      have hRngLe : Rng ≤ Submodule.map f P := by
        intro x hx
        let xr : Rng := ⟨x, hx⟩
        have hrepr :
            (∑ a, c.basis.repr xr a • (c.basis a : V)) = x :=
          calc
            (∑ a, c.basis.repr xr a • (c.basis a : V)) =
                ((∑ a, c.basis.repr xr a • c.basis a : Rng) : V) := by
                  simp only [Submodule.coe_sum, Submodule.coe_smul]
            _ = x := congrArg Subtype.val (c.basis.sum_repr xr)
        have hm :
            (∑ a, c.basis.repr xr a • (c.basis a : V)) ∈ Submodule.map f P :=
          Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hbasisMem a)
        rw [hrepr] at hm
        exact hm
      have hPker : P ⊔ LinearMap.ker f = ⊤ := by
        rw [eq_top_iff]
        intro x _hx
        have hfx : f x ∈ Rng := ⟨x, rfl⟩
        obtain ⟨p, hp, hfp⟩ := hRngLe hfx
        have hxmp : x - p ∈ LinearMap.ker f := by
          rw [LinearMap.mem_ker, map_sub, hfp, sub_self]
        rw [Submodule.mem_sup]
        exact ⟨p, hp, x - p, hxmp, by abel⟩
      let Q := Fin (finrank K (V ⧸ P))
      let qb : Basis Q K (V ⧸ P) := Module.finBasis K (V ⧸ P)
      have existsKerLift (x : V ⧸ P) :
          ∃ y : V, y ∈ LinearMap.ker f ∧ P.mkQ y = x := by
        obtain ⟨v, rfl⟩ := Quotient.mk_surjective x
        have hv : v ∈ P ⊔ LinearMap.ker f := by rw [hPker]; trivial
        obtain ⟨p, hp, y, hy, hpy⟩ := Submodule.mem_sup.mp hv
        refine ⟨y, hy, ?_⟩
        change P.mkQ y = P.mkQ v
        rw [← hpy, map_add]
        have hp0 : P.mkQ p = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact hp
        rw [hp0, zero_add]
      let z (a : Q) : V := (existsKerLift (qb a)).choose
      have hzKer (a : Q) : z a ∈ LinearMap.ker f :=
        (existsKerLift (qb a)).choose_spec.1
      have hzQuot (a : Q) : P.mkQ (z a) = qb a :=
        (existsKerLift (qb a)).choose_spec.2
      have hzLI : LinearIndependent K (P.mkQ ∘ z) := by
        convert qb.linearIndependent using 1
        funext a
        exact hzQuot a
      let pb : Basis Ext K P := Basis.span hext
      let rawFamily : Ext ⊕ Q → V := Sum.elim (fun a => (pb a : V)) z
      have hrawLI : LinearIndependent K rawFamily :=
        LinearIndependent.sumElim_of_quotient pb.linearIndependent z hzLI
      have hcard : Fintype.card (Ext ⊕ Q) = finrank K V := by
        rw [Fintype.card_sum]
        rw [show Fintype.card Q = finrank K (V ⧸ P) by simp [Q]]
        rw [← Module.finrank_eq_card_basis pb]
        rw [Nat.add_comm]
        exact P.finrank_quotient_add_finrank
      let rawBasis : Basis (Ext ⊕ Q) K V :=
        basisOfLinearIndependentOfCardEqFinrank' rawFamily hrawLI hcard
      let newSize : c.ι ⊕ Q → ℕ := Sum.elim (fun i => c.size i + 1) (fun _ => 1)
      let indexEquiv : (Σ a, Fin (newSize a)) ≃ Ext ⊕ Q :=
        extendChainIndexEquiv c.size
      let b : Basis (Σ a, Fin (newSize a)) K V := rawBasis.reindex indexEquiv.symm
      have b_castSucc (i : c.ι) (j : Fin (c.size i)) :
          b ⟨Sum.inl i, Fin.castSucc j⟩ = (c.basis ⟨i, j⟩ : Rng) := by
        simp [b, indexEquiv, rawBasis, rawFamily, pb, extFamily]
        rw [extendChainIndexEquiv_castSucc]
        exact (Basis.coe_span_apply hext (Sum.inl ⟨i, j⟩)).trans rfl
      have b_last (i : c.ι) :
          b ⟨Sum.inl i, Fin.last (c.size i)⟩ = lift i := by
        simp [b, indexEquiv, rawBasis, rawFamily, pb, extFamily]
        rw [extendChainIndexEquiv_last]
        exact (Basis.coe_span_apply hext (Sum.inr i)).trans rfl
      have b_singleton (a : Q) (j : Fin 1) : b ⟨Sum.inr a, j⟩ = z a := by
        simp [b, indexEquiv, rawBasis, rawFamily, pb, extFamily]
        rw [extendChainIndexEquiv_singleton]
        rfl
      refine ⟨{
        ι := c.ι ⊕ Q
        size := newSize
        positive_size := ?_
        basis := b
        chain := ?_
      }⟩
      · intro a
        rcases a with i | a
        · change 0 < c.size i + 1
          omega
        · simp [newSize]
      · intro a j
        rcases a with i | a
        · dsimp [newSize] at j ⊢
          refine Fin.lastCases ?_ (fun r => ?_) j
          · rw [b_last]
            have hj : (Fin.last (c.size i)).val ≠ 0 := by
              dsimp
              exact ne_of_gt (c.positive_size i)
            rw [if_neg hj, hlift]
            have hpred :
                (⟨(Fin.last (c.size i)).val - 1,
                    lt_of_le_of_lt (Nat.sub_le _ 1) (Fin.last (c.size i)).isLt⟩ :
                  Fin (c.size i + 1)) = Fin.castSucc (c.lastIndex i) := by
              apply Fin.ext
              dsimp [NilpotentChainBasis.lastIndex]
            rw [hpred, b_castSucc]
          · rw [b_castSucc]
            by_cases hr : r.val = 0
            · rw [if_pos (by simpa using hr)]
              have hc : f (c.basis ⟨i, r⟩ : Rng) = 0 := by
                simpa [fR, hr] using congrArg Subtype.val (c.chain i r)
              exact hc
            · rw [if_neg (by simpa using hr)]
              have hpred :
                  (⟨(Fin.castSucc r).val - 1,
                      lt_of_le_of_lt (Nat.sub_le _ 1) (Fin.castSucc r).isLt⟩ :
                    Fin (c.size i + 1)) =
                    Fin.castSucc
                      ⟨r.val - 1, lt_of_le_of_lt (Nat.sub_le r.val 1) r.isLt⟩ := by
                apply Fin.ext
                rfl
              rw [hpred, b_castSucc]
              have hc :
                  f (c.basis ⟨i, r⟩ : Rng) =
                    (c.basis
                      ⟨i, ⟨r.val - 1,
                        lt_of_le_of_lt (Nat.sub_le r.val 1) r.isLt⟩⟩ : Rng) := by
                simpa [fR, hr] using congrArg Subtype.val (c.chain i r)
              exact hc
        · simp only [newSize, Sum.elim_inr] at j ⊢
          have hj : j.val = 0 := by omega
          rw [b_singleton, if_pos hj]
          exact LinearMap.mem_ker.mp (hzKer a)

theorem nilpotentChainBasis
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (hf : IsNilpotent f) : Nonempty (NilpotentChainBasis f) := by
  obtain ⟨k, hk⟩ := hf
  exact nilpotentChainBasisOfPowEqZero f k hk

private def sigmaAssocEquiv {α : Type*} {β : α → Type*}
    {γ : (Σ a, β a) → Type*} :
    (Σ p, γ p) ≃ (Σ a, Σ b, γ ⟨a, b⟩) where
  toFun := fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  invFun := fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩
  left_inv := by rintro ⟨⟨a, b⟩, c⟩; rfl
  right_inv := by rintro ⟨a, b, c⟩; rfl

/-- Assemble nilpotent chain bases on the generalized eigenspaces. -/
theorem jordanChainBasis
    {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) :
    Nonempty (JordanChainBasis f) := by
  classical
  let E := {μ : K // f.maxGenEigenspace μ ≠ ⊥}
  have hEfinite : Set.Finite {μ : K | f.maxGenEigenspace μ ≠ ⊥} :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  letI : Fintype E := hEfinite.fintype
  let E₀ := Fin (Fintype.card E)
  let enum : E₀ ≃ E := (Fintype.equivFin E).symm
  let A : E₀ → Submodule K V := fun μ => f.maxGenEigenspace (enum μ : K)
  have hAll : DirectSum.IsInternal f.maxGenEigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      f.independent_maxGenEigenspace f.iSup_maxGenEigenspace_eq_top
  have hSub : DirectSum.IsInternal
      (fun μ : E => f.maxGenEigenspace (μ : K)) := by
    simpa [E] using (DirectSum.isInternal_ne_bot_iff.mpr hAll)
  have hAind : iSupIndep A := by
    simpa [A, Function.comp_def] using
      f.independent_maxGenEigenspace.comp
        (Subtype.coe_injective.comp enum.injective)
  have hAtop : iSup A = ⊤ := by
    apply le_antisymm le_top
    rw [← hSub.submodule_iSup_eq_top]
    refine iSup_le fun μ => ?_
    obtain ⟨a, rfl⟩ := enum.surjective μ
    exact le_iSup A a
  have hA : DirectSum.IsInternal A :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hAind hAtop
  let maps (μ : E₀) :
      MapsTo (f - algebraMap K (Module.End K V) (enum μ : K)) (A μ) (A μ) :=
    f.mapsTo_maxGenEigenspace_of_comm
      (Algebra.mul_sub_algebraMap_commutes f (enum μ : K)) (enum μ : K)
  let g (μ : E₀) : Module.End K (A μ) :=
    (f - algebraMap K (Module.End K V) (enum μ : K)).restrict (maps μ)
  have hgNil (μ : E₀) : IsNilpotent (g μ) := by
    exact f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap
      (enum μ : K) (maps μ)
  let c (μ : E₀) : NilpotentChainBasis (g μ) :=
    Classical.choice (nilpotentChainBasis (g μ) (hgNil μ))
  let I := Σ μ : E₀, (c μ).ι
  let size : I → ℕ := fun p => (c p.1).size p.2
  let componentBasis (μ : E₀) :
      Basis (Σ i : (c μ).ι, Fin ((c μ).size i)) K (A μ) :=
    (c μ).basis
  let collected :
      Basis (Σ μ : E₀, Σ i : (c μ).ι, Fin ((c μ).size i)) K V :=
    hA.collectedBasis componentBasis
  let indexEquiv :
      (Σ p : I, Fin (size p)) ≃
        (Σ μ : E₀, Σ i : (c μ).ι, Fin ((c μ).size i)) :=
    sigmaAssocEquiv
  let b : Basis (Σ p : I, Fin (size p)) K V :=
    collected.reindex indexEquiv.symm
  have b_apply (μ : E₀) (i : (c μ).ι) (j : Fin ((c μ).size i)) :
      b ⟨⟨μ, i⟩, j⟩ = ((c μ).basis ⟨i, j⟩ : A μ) := by
    simp [b, indexEquiv, sigmaAssocEquiv, collected, componentBasis]
  refine ⟨{
    ι := I
    size := size
    positive_size := fun p => (c p.1).positive_size p.2
    eigenvalue := fun p => (enum p.1 : K)
    basis := b
    chain := ?_
  }⟩
  rintro ⟨μ, i⟩ j
  have hc :
      f (((c μ).basis ⟨i, j⟩ : A μ) : V) -
          (enum μ : K) • (((c μ).basis ⟨i, j⟩ : A μ) : V) =
        ((if j.val = 0 then 0
          else (c μ).basis
            ⟨i, ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩⟩ : A μ) : V) := by
    simpa [g, LinearMap.sub_apply] using
      congrArg Subtype.val ((c μ).chain i j)
  rw [sub_eq_iff_eq_add] at hc
  rw [b_apply]
  by_cases hj : j.val = 0
  · rw [if_pos hj] at hc ⊢
    simpa only [Submodule.coe_zero, zero_add, add_zero] using hc
  · rw [if_neg hj] at hc ⊢
    rw [b_apply]
    exact hc.trans (add_comm _ _)

end Submission.Jordan
