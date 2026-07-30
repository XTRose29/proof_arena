import Submission.BFCCenter

namespace Submission.Helpers

open scoped BigOperators Filter Topology commutatorElement

noncomputable section

def subgroupTopEquiv (A : Type) [Group A] : (⊤ : Subgroup A) ≃ A where
  toFun x := x.1
  invFun x := ⟨x, Subgroup.mem_top x⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma unitCharacterAnnihilator_top_eq_bot
    (D : Type) [CommGroup D] [Finite D] :
    unitCharacterAnnihilator D (⊤ : Subgroup (D →* ℂˣ)) = ⊥ := by
  ext d
  constructor
  · intro hd
    have hbot : d ∈ (⊥ : Subgroup D) := by
      rw [← CommGroup.forall_monoidHom_apply_eq_one_iff ℂ (⊥ : Subgroup D) d]
      intro chi _
      exact hd ⟨chi, Subgroup.mem_top chi⟩
    simpa using hbot
  · intro hd
    have hd_one : d = 1 := by simpa using hd
    subst d
    exact Subgroup.one_mem _

lemma bfcCoreProfileKernelInGroup_top_eq_bot
    (G : Type) [Group G] [Finite G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C) :
    let C := bfcCore G
    letI := C.toGroup
    letI := commutatorCommGroupOfLeCenter C hcentral
    bfcCoreProfileKernelInGroup G hcentral
      (⊤ : Subgroup (commutator C →* ℂˣ)) = ⊥ := by
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  change (unitCharacterAnnihilator (commutator C) ⊤).map
    (bfcCoreDerivedEmbedding G) = ⊥
  rw [unitCharacterAnnihilator_top_eq_bot]
  exact Subgroup.map_bot (bfcCoreDerivedEmbedding G)

lemma commProb_eq_expect_bfcCoreCharacterValue
    (G : Type) [Group G] [Finite G]
    (hcentral : let C := bfcCore G;
      letI := C.toGroup
      commutator C ≤ Subgroup.center C) :
    let C := bfcCore G
    letI := C.toGroup
    letI := commutatorCommGroupOfLeCenter C hcentral
    letI := Fintype.ofFinite G
    ((commProb G : ℚ) : ℂ) =
      𝔼 chi : commutator C →* ℂˣ, 𝔼 x : G, 𝔼 y : G,
        bfcCoreCharacterValue G hcentral chi x y := by
  classical
  let C := bfcCore G
  letI := C.toGroup
  letI := commutatorCommGroupOfLeCenter C hcentral
  letI := Fintype.ofFinite G
  let X : Subgroup (commutator C →* ℂˣ) := ⊤
  letI := Fintype.ofFinite X
  have hK : bfcCoreProfileKernelInGroup G hcentral X = ⊥ := by
    simpa [X] using bfcCoreProfileKernelInGroup_top_eq_bot G hcentral
  calc
    ((commProb G : ℚ) : ℂ) =
        𝔼 x : G, 𝔼 y : G,
          if x * y = y * x then (1 : ℂ) else 0 :=
      (expect_commute_indicator_eq_commProb G).symm
    _ = 𝔼 x : G, 𝔼 y : G,
        complexPropIndicator (Commute x y) := by
      apply Finset.expect_congr rfl
      intro x _
      apply Finset.expect_congr rfl
      intro y _
      rfl
    _ = 𝔼 x : G, 𝔼 y : G, 𝔼 chi : X,
        bfcCoreCharacterValue G hcentral chi.1 x y := by
      apply Finset.expect_congr rfl
      intro x _
      apply Finset.expect_congr rfl
      intro y _
      rw [expect_bfcCoreCharacterValue_eq_indicator]
      rw [hK]
      congr 1
      apply propext
      change Commute x y ↔ ⁅x, y⁆ = 1
      constructor
      · exact fun h => h.commutator_eq
      · exact fun h => commutatorElement_eq_one_iff_mul_comm.mp h
    _ = 𝔼 chi : X, 𝔼 x : G, 𝔼 y : G,
        bfcCoreCharacterValue G hcentral chi.1 x y :=
      @expect_rotate_three G G X _ _ _
        (fun x y chi => bfcCoreCharacterValue G hcentral chi.1 x y)
    _ = 𝔼 chi : commutator C →* ℂˣ, 𝔼 x : G, 𝔼 y : G,
        bfcCoreCharacterValue G hcentral chi x y := by
      apply Fintype.expect_equiv (subgroupTopEquiv (commutator C →* ℂˣ))
      intro chi
      rfl

lemma FiniteCommProbWitness.centralCore_commutator_le_center
    (W : FiniteCommProbWitness) :
    let V := W.centralCoreWitness
    letI := V.group
    commutator V.carrier ≤ Subgroup.center V.carrier := by
  letI := W.group
  exact bfcCore_commutator_le_center W.carrier

def bfcCharacterAverage
    (W : ℕ → FiniteCommProbWitness)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (n : ℕ)
    (chi : let V0 := (W 0).centralCoreWitness;
      letI := V0.group; commutator V0.carrier →* ℂˣ) : ℂ := by
  let Wn := W n
  letI := Wn.group
  letI := Wn.finite
  letI := Fintype.ofFinite Wn.carrier
  let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
  letI := (V n).group
  let chin := transportedUnitCharacterHom V d hcard hcode n chi
  exact 𝔼 x : Wn.carrier, 𝔼 y : Wn.carrier,
    bfcCoreCharacterValue Wn.carrier
      (bfcCore_commutator_le_center Wn.carrier)
      chin x y

def bfcTransportedUnitCharacterMulEquiv
    (W : ℕ → FiniteCommProbWitness)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (n : ℕ) :
    let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
    letI := (V 0).group
    let Wn := W n
    letI := Wn.group
    let Cn := bfcCore Wn.carrier
    letI := Cn.toGroup
    (commutator (V 0).carrier →* ℂˣ) ≃* (commutator Cn →* ℂˣ) := by
  let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
  let Wn := W n
  letI := Wn.group
  let Cn := bfcCore Wn.carrier
  letI := Cn.toGroup
  letI := (V 0).group
  letI := (V n).group
  change (commutator (V 0).carrier →* ℂˣ) ≃*
    (commutator (V n).carrier →* ℂˣ)
  exact transportedUnitCharacterMulEquiv V d hcard hcode n

def bfcTransportedUnitCharacterHom
    (W : ℕ → FiniteCommProbWitness)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (n : ℕ) :
    let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
    letI := (V 0).group
    let Wn := W n
    letI := Wn.group
    let Cn := bfcCore Wn.carrier
    letI := Cn.toGroup
    (commutator (V 0).carrier →* ℂˣ) →* (commutator Cn →* ℂˣ) := by
  let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
  let Wn := W n
  letI := Wn.group
  let Cn := bfcCore Wn.carrier
  letI := Cn.toGroup
  letI := (V 0).group
  letI := (V n).group
  change (commutator (V 0).carrier →* ℂˣ) →*
    (commutator (V n).carrier →* ℂˣ)
  exact transportedUnitCharacterHom V d hcard hcode n

lemma bfcTransportedUnitCharacterHom_injective
    (W : ℕ → FiniteCommProbWitness)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (n : ℕ) :
    let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
    letI := (V 0).group
    let Wn := W n
    letI := Wn.group
    let Cn := bfcCore Wn.carrier
    letI := Cn.toGroup
    Function.Injective (bfcTransportedUnitCharacterHom W d hcard hcode n) := by
  let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
  let Wn := W n
  letI := Wn.group
  let Cn := bfcCore Wn.carrier
  letI := Cn.toGroup
  letI := (V 0).group
  letI := (V n).group
  change Function.Injective (transportedUnitCharacterHom V d hcard hcode n)
  exact transportedUnitCharacterHom_injective V d hcard hcode n

def bfcTransportedUnitCharacterSubgroup
    (W : ℕ → FiniteCommProbWitness)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (X : let V := (W 0).centralCoreWitness;
      letI := V.group; Subgroup (commutator V.carrier →* ℂˣ))
    (n : ℕ) :
    let Wn := W n
    letI := Wn.group
    let Cn := bfcCore Wn.carrier
    letI := Cn.toGroup
    Subgroup (commutator Cn →* ℂˣ) :=
  X.map (bfcTransportedUnitCharacterHom W d hcard hcode n)

def bfcProfileQuotientWitness
    (W : ℕ → FiniteCommProbWitness)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (X : let V := (W 0).centralCoreWitness;
      letI := V.group; Subgroup (commutator V.carrier →* ℂˣ))
    (n : ℕ) : FiniteCommProbWitness := by
  let Wn := W n
  letI := Wn.group
  letI := Wn.finite
  let Cn := bfcCore Wn.carrier
  letI := Cn.toGroup
  let Xn := bfcTransportedUnitCharacterSubgroup W d hcard hcode X n
  let K := bfcCoreProfileKernelInGroup Wn.carrier
    (bfcCore_commutator_le_center Wn.carrier) Xn
  letI := bfcCoreProfileKernelInGroupNormal Wn.carrier
    (bfcCore_commutator_le_center Wn.carrier) Xn
  exact ⟨Wn.carrier ⧸ K, inferInstance, inferInstance⟩

lemma probability_eq_expect_bfcCharacterAverage
    (W : ℕ → FiniteCommProbWitness)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (n : ℕ) :
    let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
    letI := (V 0).group
    letI := (V 0).finite
    letI := commutatorCommGroupOfLeCenter (V 0).carrier
      ((W 0).centralCore_commutator_le_center)
    ((W n).probability : ℂ) =
      𝔼 chi : commutator (V 0).carrier →* ℂˣ,
        bfcCharacterAverage W d hcard hcode n chi := by
  classical
  dsimp only
  let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
  let Wn := W n
  letI := Wn.group
  letI := Wn.finite
  letI := Fintype.ofFinite Wn.carrier
  letI := (V 0).group
  letI := (V 0).finite
  letI := commutatorCommGroupOfLeCenter (V 0).carrier
    ((W 0).centralCore_commutator_le_center)
  let Cn := bfcCore Wn.carrier
  letI := Cn.toGroup
  let hcentralN := bfcCore_commutator_le_center Wn.carrier
  letI := commutatorCommGroupOfLeCenter Cn hcentralN
  change ((W n).probability : ℂ) =
    𝔼 chi : commutator (V 0).carrier →* ℂˣ,
      bfcCharacterAverage W d hcard hcode n chi
  have hfourier := commProb_eq_expect_bfcCoreCharacterValue Wn.carrier
    hcentralN
  let eTransport : (commutator (V 0).carrier →* ℂˣ) ≃*
      (commutator Cn →* ℂˣ) := by
    letI := (V n).group
    change (commutator (V 0).carrier →* ℂˣ) ≃*
      (commutator (V n).carrier →* ℂˣ)
    exact transportedUnitCharacterMulEquiv V d hcard hcode n
  calc
    ((W n).probability : ℂ) =
        𝔼 chi : commutator Cn →* ℂˣ,
          𝔼 x : Wn.carrier, 𝔼 y : Wn.carrier,
            bfcCoreCharacterValue Wn.carrier
              hcentralN chi x y := by
      simpa [Wn, V, FiniteCommProbWitness.probability] using hfourier
    _ = 𝔼 chi : commutator (V 0).carrier →* ℂˣ,
        bfcCharacterAverage W d hcard hcode n chi := by
      symm
      apply Fintype.expect_equiv eTransport
      intro chi
      dsimp [eTransport]
      rfl

lemma bfcProfileQuotient_probability_eq_expect
    (W : ℕ → FiniteCommProbWitness)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (X : let V := (W 0).centralCoreWitness;
      letI := V.group; Subgroup (commutator V.carrier →* ℂˣ))
    (n : ℕ) :
    let V := (W 0).centralCoreWitness
    letI := V.group
    letI := V.finite
    letI := Fintype.ofFinite X
    ((bfcProfileQuotientWitness W d hcard hcode X n).probability : ℂ) =
      𝔼 chi : X, bfcCharacterAverage W d hcard hcode n chi.1 := by
  classical
  let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
  let Wn := W n
  letI := Wn.group
  letI := Wn.finite
  letI := Fintype.ofFinite Wn.carrier
  let Cn := bfcCore Wn.carrier
  letI := Cn.toGroup
  let hcentralN := bfcCore_commutator_le_center Wn.carrier
  letI := commutatorCommGroupOfLeCenter Cn hcentralN
  letI := (V 0).group
  letI := (V 0).finite
  letI := Fintype.ofFinite X
  let f : (commutator (V 0).carrier →* ℂˣ) →*
      (commutator Cn →* ℂˣ) :=
    bfcTransportedUnitCharacterHom W d hcard hcode n
  let Xn : Subgroup (commutator Cn →* ℂˣ) :=
    bfcTransportedUnitCharacterSubgroup W d hcard hcode X n
  letI := Fintype.ofFinite Xn
  let K := bfcCoreProfileKernelInGroup Wn.carrier hcentralN Xn
  letI := bfcCoreProfileKernelInGroupNormal Wn.carrier hcentralN Xn
  have hquot := commProb_bfcCoreProfileQuotient_eq_expect Wn.carrier hcentralN Xn
  calc
    ((bfcProfileQuotientWitness W d hcard hcode X n).probability : ℂ) =
        𝔼 chi : Xn, 𝔼 x : Wn.carrier, 𝔼 y : Wn.carrier,
          bfcCoreCharacterValue Wn.carrier hcentralN chi.1 x y := by
      change ((((commProb (Wn.carrier ⧸ K) : ℚ) : ℝ)) : ℂ) = _
      exact_mod_cast hquot
    _ = 𝔼 chi : X, bfcCharacterAverage W d hcard hcode n chi.1 := by
      let eX : X ≃* Xn := by
        exact Subgroup.equivMapOfInjective X f
          (bfcTransportedUnitCharacterHom_injective W d hcard hcode n)
      symm
      apply Fintype.expect_equiv eX.toEquiv
      intro chi
      dsimp [eX, f, Xn, bfcTransportedUnitCharacterSubgroup]
      rfl

lemma norm_bfcCharacterAverage_le_inv_index
    (W : ℕ → FiniteCommProbWitness)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (n : ℕ)
    (chi : let V := (W 0).centralCoreWitness;
      letI := V.group; commutator V.carrier →* ℂˣ) :
    let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
    let hcentral : ∀ k,
      letI := (V k).group
      commutator (V k).carrier ≤ Subgroup.center (V k).carrier := fun k =>
        (W k).centralCore_commutator_le_center
    ‖bfcCharacterAverage W d hcard hcode n chi‖ ≤
      1 / (classTwoCharacterIndex V hcentral d hcard hcode n chi : ℝ) := by
  classical
  let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
  let hcentral : ∀ k,
      letI := (V k).group
      commutator (V k).carrier ≤ Subgroup.center (V k).carrier := fun k =>
    (W k).centralCore_commutator_le_center
  let Wn := W n
  letI := Wn.group
  letI := Wn.finite
  letI := Fintype.ofFinite Wn.carrier
  letI := (V 0).group
  letI := (V n).group
  let chin := transportedUnitCharacterHom V d hcard hcode n chi
  have hbound := norm_expect_bfcCoreCharacterValue_le_inv_index Wn.carrier
    (bfcCore_commutator_le_center Wn.carrier) chin
  change ‖𝔼 x : Wn.carrier, 𝔼 y : Wn.carrier,
      bfcCoreCharacterValue Wn.carrier
        (bfcCore_commutator_le_center Wn.carrier) chin x y‖ ≤
    1 / ((commutatorCharMap (bfcCore Wn.carrier)
      (bfcCore_commutator_le_center Wn.carrier)
      (unitCharToComplex chin)).ker.index : ℝ)
  exact hbound

lemma bfcCharacterAverage_tendsto_zero_of_index_tendsto_top
    (W : ℕ → FiniteCommProbWitness)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (φ : ℕ → ℕ)
    (chi : let V := (W 0).centralCoreWitness;
      letI := V.group; commutator V.carrier →* ℂˣ)
    (hindex :
      let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
      let hcentral : ∀ k,
        letI := (V k).group
        commutator (V k).carrier ≤ Subgroup.center (V k).carrier := fun k =>
          (W k).centralCore_commutator_le_center
      Filter.Tendsto
        (fun n => (classTwoCharacterIndex V hcentral d hcard hcode (φ n) chi :
          WithTop ℕ)) Filter.atTop (𝓝 ⊤)) :
    Filter.Tendsto
      (fun n => bfcCharacterAverage W d hcard hcode (φ n) chi)
      Filter.atTop (𝓝 0) := by
  classical
  let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
  let hcentral : ∀ k,
      letI := (V k).group
      commutator (V k).carrier ≤ Subgroup.center (V k).carrier := fun k =>
    (W k).centralCore_commutator_le_center
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hcomplex := tendsto_inv_natCast_zero_of_tendsto_withTop_top hindex
  have hnorm := hcomplex.norm
  have hreal : Filter.Tendsto
      (fun n => 1 /
        (classTwoCharacterIndex V hcentral d hcard hcode (φ n) chi : ℝ))
      Filter.atTop (𝓝 0) := by
    simpa using hnorm
  exact squeeze_zero
    (fun n => norm_nonneg (bfcCharacterAverage W d hcard hcode (φ n) chi))
    (fun n => norm_bfcCharacterAverage_le_inv_index
      W d hcard hcode (φ n) chi)
    hreal

lemma bfcCharacterIndex_profile_infinite_yields_cluster
    (W : ℕ → FiniteCommProbWitness)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (φ : ℕ → ℕ) {p : ℝ}
    (hprob : Filter.Tendsto (fun n => (W (φ n)).probability)
      Filter.atTop (𝓝 p))
    (a :
      let V := (W 0).centralCoreWitness
      letI := V.group
      letI := commutatorCommGroupOfLeCenter V.carrier
        ((W 0).centralCore_commutator_le_center)
      (commutator V.carrier →* ℂˣ) → WithTop ℕ)
    (ha :
      let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
      let hcentral : ∀ k,
        letI := (V k).group
        commutator (V k).carrier ≤ Subgroup.center (V k).carrier := fun k =>
          (W k).centralCore_commutator_le_center
      letI := (V 0).group
      letI := commutatorCommGroupOfLeCenter (V 0).carrier (hcentral 0)
      ∀ chi, Filter.Tendsto
        (fun n => (classTwoCharacterIndex V hcentral d hcard hcode (φ n) chi :
          WithTop ℕ)) Filter.atTop (𝓝 (a chi)))
    (hinfinite : ¬ ∀ chi, a chi ≠ ⊤) :
    ∃ q : ℕ, 2 ≤ q ∧
      ClusterPt ((q : ℝ) * p) (Filter.principal CommProbRange) := by
  classical
  let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
  let hcentral : ∀ k,
      letI := (V k).group
      commutator (V k).carrier ≤ Subgroup.center (V k).carrier := fun k =>
    (W k).centralCore_commutator_le_center
  letI := (V 0).group
  letI := (V 0).finite
  letI := commutatorCommGroupOfLeCenter (V 0).carrier (hcentral 0)
  letI := Fintype.ofFinite (commutator (V 0).carrier)
  let A := commutator (V 0).carrier →* ℂˣ
  let X := finiteClassTwoCharacterProfileSubgroup
    V hcentral d hcard hcode φ a ha
  letI := Fintype.ofFinite X
  have hX_ne_top : X ≠ ⊤ := by
    intro htop
    apply hinfinite
    intro chi
    have hmem : chi ∈ X := by
      rw [htop]
      exact Subgroup.mem_top chi
    change a chi ≠ ⊤ at hmem
    exact hmem
  let q := X.index
  have hq : 2 ≤ q := by
    have := Subgroup.one_lt_index_of_ne_top hX_ne_top
    omega
  have hfull : Filter.Tendsto
      (fun n => 𝔼 chi : A, bfcCharacterAverage W d hcard hcode (φ n) chi)
      Filter.atTop (𝓝 (p : ℂ)) := by
    refine hprob.ofReal.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact probability_eq_expect_bfcCharacterAverage W d hcard hcode (φ n)
  have hcomplTerm : ∀ chi ∈ subgroupComplementFinset A X,
      Filter.Tendsto
        (fun n => bfcCharacterAverage W d hcard hcode (φ n) chi)
        Filter.atTop (𝓝 0) := by
    intro chi hchi
    have hnot : chi ∉ X := by
      simpa [subgroupComplementFinset] using hchi
    have hatop : a chi = ⊤ := by
      by_contra hne
      apply hnot
      change a chi ≠ ⊤
      exact hne
    have hindex := ha chi
    rw [hatop] at hindex
    exact bfcCharacterAverage_tendsto_zero_of_index_tendsto_top
      W d hcard hcode φ chi hindex
  have hcomplSum : Filter.Tendsto
      (fun n => ∑ chi ∈ subgroupComplementFinset A X,
        bfcCharacterAverage W d hcard hcode (φ n) chi)
      Filter.atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (subgroupComplementFinset A X) hcomplTerm
  have hcompl : Filter.Tendsto
      (fun n => (∑ chi ∈ subgroupComplementFinset A X,
        bfcCharacterAverage W d hcard hcode (φ n) chi) /
          (Fintype.card X : ℂ)) Filter.atTop (𝓝 0) := by
    simpa using hcomplSum.div_const (Fintype.card X : ℂ)
  have hscaledFull : Filter.Tendsto
      (fun n => (q : ℂ) *
        (𝔼 chi : A, bfcCharacterAverage W d hcard hcode (φ n) chi))
      Filter.atTop (𝓝 ((q : ℂ) * (p : ℂ))) :=
    hfull.const_mul (q : ℂ)
  have hdiff : Filter.Tendsto
      (fun n => (q : ℂ) *
          (𝔼 chi : A, bfcCharacterAverage W d hcard hcode (φ n) chi) -
        (∑ chi ∈ subgroupComplementFinset A X,
          bfcCharacterAverage W d hcard hcode (φ n) chi) /
            (Fintype.card X : ℂ))
      Filter.atTop (𝓝 ((q : ℂ) * (p : ℂ))) := by
    simpa using hscaledFull.sub hcompl
  have hXexpect : Filter.Tendsto
      (fun n => 𝔼 chi : X,
        bfcCharacterAverage W d hcard hcode (φ n) chi.1)
      Filter.atTop (𝓝 ((q : ℂ) * (p : ℂ))) := by
    refine hdiff.congr' (Filter.Eventually.of_forall fun n => ?_)
    have hid := subgroup_index_mul_expect_eq_expect_add_compl A X
      (fun chi => bfcCharacterAverage W d hcard hcode (φ n) chi)
    change _ - _ = _
    exact ((eq_sub_iff_add_eq).2 hid.symm).symm
  let U : ℕ → FiniteCommProbWitness := fun n =>
    bfcProfileQuotientWitness W d hcard hcode X (φ n)
  have hUcomplex : Filter.Tendsto (fun n => ((U n).probability : ℂ))
      Filter.atTop (𝓝 ((q : ℂ) * (p : ℂ))) := by
    refine hXexpect.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact (bfcProfileQuotient_probability_eq_expect
      W d hcard hcode X (φ n)).symm
  have hUreal : Filter.Tendsto (fun n => (U n).probability)
      Filter.atTop (𝓝 ((q : ℝ) * p)) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hUcomplex
    change Filter.Tendsto (fun n => Complex.re ((U n).probability : ℂ))
      Filter.atTop (𝓝 (Complex.re ((q : ℂ) * (p : ℂ)))) at hre
    simpa using hre
  have hcluster : ClusterPt ((q : ℝ) * p)
      (Filter.principal CommProbRange) := by
    rw [← mem_closure_iff_clusterPt]
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun n => (U n).probability, ?_, hUreal⟩
    intro n
    exact ⟨(U n).carrier, (U n).group, rfl⟩
  exact ⟨q, hq, hcluster⟩

lemma mem_CommProbRange_of_bfcCharacterIndex_profile_finite
    (W : ℕ → FiniteCommProbWitness)
    (B : ℕ) (hbound : ∀ n, (W n).commutatorCard ≤ B)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (φ : ℕ → ℕ) {p : ℝ}
    (hprob : Filter.Tendsto (fun n => (W (φ n)).probability)
      Filter.atTop (𝓝 p))
    (a :
      let V := (W 0).centralCoreWitness
      letI := V.group
      letI := commutatorCommGroupOfLeCenter V.carrier
        ((W 0).centralCore_commutator_le_center)
      (commutator V.carrier →* ℂˣ) → WithTop ℕ)
    (ha :
      let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
      let hcentral : ∀ k,
        letI := (V k).group
        commutator (V k).carrier ≤ Subgroup.center (V k).carrier := fun k =>
          (W k).centralCore_commutator_le_center
      letI := (V 0).group
      letI := commutatorCommGroupOfLeCenter (V 0).carrier (hcentral 0)
      ∀ chi, Filter.Tendsto
        (fun n => (classTwoCharacterIndex V hcentral d hcard hcode (φ n) chi :
          WithTop ℕ)) Filter.atTop (𝓝 (a chi)))
    (hfinite :
      let V := (W 0).centralCoreWitness
      letI := V.group
      letI := commutatorCommGroupOfLeCenter V.carrier
        ((W 0).centralCore_commutator_le_center)
      ∀ chi, a chi ≠ ⊤) :
    p ∈ CommProbRange := by
  classical
  let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
  let hcentral : ∀ k,
      letI := (V k).group
      commutator (V k).carrier ≤ Subgroup.center (V k).carrier := fun k =>
    (W k).centralCore_commutator_le_center
  letI := (V 0).group
  letI := (V 0).finite
  letI := commutatorCommGroupOfLeCenter (V 0).carrier (hcentral 0)
  let b : (commutator (V 0).carrier →* ℂˣ) → ℕ := fun chi =>
    (a chi).untop (hfinite chi)
  have heventIndex : ∀ chi : commutator (V 0).carrier →* ℂˣ,
      ∀ᶠ n in Filter.atTop,
        classTwoCharacterIndex V hcentral d hcard hcode (φ n) chi = b chi := by
    intro chi
    have h := ha chi
    rw [← WithTop.coe_untop (a chi) (hfinite chi)] at h
    have hevent := eventually_eq_of_tendsto_withTop_coe h
    filter_upwards [hevent] with n hn
    exact WithTop.coe_eq_coe.mp hn
  have heventAll : ∀ᶠ n in Filter.atTop, ∀ chi,
      classTwoCharacterIndex V hcentral d hcard hcode (φ n) chi = b chi :=
    Filter.eventually_all.mpr heventIndex
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventAll
  let P : ℕ := ∏ chi : commutator (V 0).carrier →* ℂˣ, b chi
  let K : ℕ := B ^ B
  let T : ℕ := (B ^ K) * P * K
  have hBpos : 0 < B := by
    have hpositive : 0 < (W 0).commutatorCard := by
      letI := (W 0).group
      letI := (W 0).finite
      change 0 < Nat.card (commutator (W 0).carrier)
      exact Nat.card_pos
    exact hpositive.trans_le (hbound 0)
  have hcenterTail : ∀ n, N ≤ n → (W (φ n)).centerIndex ≤ T := by
    intro n hn
    let Wn := W (φ n)
    letI := Wn.group
    letI := Wn.finite
    let C := bfcCore Wn.carrier
    letI := C.toGroup
    have hD : Nat.card (commutator Wn.carrier) ≤ B := by
      simpa [Wn, FiniteCommProbWitness.commutatorCard] using hbound (φ n)
    have hCindex : C.index ≤ K := by
      apply (bfcCore_index_le_commutatorCard_pow Wn.carrier).trans
      calc
        Nat.card (commutator Wn.carrier) ^ Nat.card (commutator Wn.carrier) ≤
            B ^ Nat.card (commutator Wn.carrier) :=
          Nat.pow_le_pow_left hD _
        _ ≤ B ^ B := Nat.pow_le_pow_right hBpos hD
    have haction : (bfcCoreCenterActionHom Wn.carrier).ker.index ≤ B ^ K := by
      apply (bfcCoreCenterActionKernel_index_le Wn.carrier).trans
      calc
        Nat.card (commutator Wn.carrier) ^ C.index ≤ B ^ C.index :=
          Nat.pow_le_pow_left hD _
        _ ≤ B ^ K := Nat.pow_le_pow_right hBpos hCindex
    have hcore : (Subgroup.center C).index ≤ P := by
      let Vn := V (φ n)
      letI := Vn.group
      letI := Vn.finite
      letI := commutatorCommGroupOfLeCenter Vn.carrier (hcentral (φ n))
      letI := Fintype.ofFinite (commutator Vn.carrier)
      letI fintypeDual : Fintype
          (AddChar (Additive (commutator Vn.carrier)) ℂ) :=
        Fintype.ofFinite _
      have hproduct := classTwo_center_index_le_addCharKernel_product
        Vn.carrier (hcentral (φ n))
      change (Subgroup.center Vn.carrier).index ≤ P
      calc
        (Subgroup.center Vn.carrier).index ≤
            ∏ psi : AddChar (Additive (commutator Vn.carrier)) ℂ,
              (commutatorCharMap Vn.carrier (hcentral (φ n)) psi).ker.index := by
          exact hproduct
        _ = ∏ chi : commutator (V 0).carrier →* ℂˣ,
              classTwoCharacterIndex V hcentral d hcard hcode (φ n) chi := by
          exact (Fintype.prod_equiv
            (transportedCommutatorCharacterEquiv
              V d hcard hcode hcentral (φ n))
            (fun chi => classTwoCharacterIndex
              V hcentral d hcard hcode (φ n) chi)
            (fun psi =>
              (commutatorCharMap Vn.carrier
                (hcentral (φ n)) psi).ker.index)
            (fun chi => rfl)).symm
        _ = P := by
          apply Finset.prod_congr rfl
          intro chi _
          exact hN n hn chi
    change (Subgroup.center Wn.carrier).index ≤ T
    rw [center_index_eq_bfcCore_factors Wn.carrier]
    exact Nat.mul_le_mul (Nat.mul_le_mul haction hcore) hCindex
  let Wtail : ℕ → FiniteCommProbWitness := fun n => W (φ (n + N))
  have hprobTail : Filter.Tendsto (fun n => (Wtail n).probability)
      Filter.atTop (𝓝 p) := by
    exact hprob.comp (Filter.tendsto_add_atTop_nat N)
  apply mem_CommProbRange_of_probability_tendsto_centerIndex_bounded
    Wtail hprobTail T
  intro n
  exact hcenterTail (n + N) (by omega)

lemma bfcCharacterIndex_profile_dichotomy
    (W : ℕ → FiniteCommProbWitness)
    (B : ℕ) (hbound : ∀ n, (W n).commutatorCard ≤ B)
    (d : ℕ) (hcard : ∀ n, ((W n).centralCoreWitness).commutatorCard = d)
    (hcode : ∀ n (hn : ((W n).centralCoreWitness).commutatorCard = d)
      (hzero : ((W 0).centralCoreWitness).commutatorCard = d),
      ((W n).centralCoreWitness).commutatorMulCode d hn =
        ((W 0).centralCoreWitness).commutatorMulCode d hzero)
    (φ : ℕ → ℕ) {p : ℝ}
    (hprob : Filter.Tendsto (fun n => (W (φ n)).probability)
      Filter.atTop (𝓝 p))
    (a :
      let V := (W 0).centralCoreWitness
      letI := V.group
      letI := commutatorCommGroupOfLeCenter V.carrier
        ((W 0).centralCore_commutator_le_center)
      (commutator V.carrier →* ℂˣ) → WithTop ℕ)
    (ha :
      let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
      let hcentral : ∀ k,
        letI := (V k).group
        commutator (V k).carrier ≤ Subgroup.center (V k).carrier := fun k =>
          (W k).centralCore_commutator_le_center
      letI := (V 0).group
      letI := commutatorCommGroupOfLeCenter (V 0).carrier (hcentral 0)
      ∀ chi, Filter.Tendsto
        (fun n => (classTwoCharacterIndex V hcentral d hcard hcode (φ n) chi :
          WithTop ℕ)) Filter.atTop (𝓝 (a chi))) :
    p ∈ CommProbRange ∨
      ∃ q : ℕ, 2 ≤ q ∧
        ClusterPt ((q : ℝ) * p) (Filter.principal CommProbRange) := by
  classical
  let V : ℕ → FiniteCommProbWitness := fun k => (W k).centralCoreWitness
  let hcentral : ∀ k,
      letI := (V k).group
      commutator (V k).carrier ≤ Subgroup.center (V k).carrier := fun k =>
    (W k).centralCore_commutator_le_center
  letI := (V 0).group
  letI := (V 0).finite
  letI := commutatorCommGroupOfLeCenter (V 0).carrier (hcentral 0)
  by_cases hfinite : ∀ chi, a chi ≠ ⊤
  · exact Or.inl (mem_CommProbRange_of_bfcCharacterIndex_profile_finite
      W B hbound d hcard hcode φ hprob a ha hfinite)
  · exact Or.inr (bfcCharacterIndex_profile_infinite_yields_cluster
      W d hcard hcode φ hprob a ha hfinite)

lemma bfc_probability_limit_dichotomy
    (W : ℕ → FiniteCommProbWitness)
    (B : ℕ) (hbound : ∀ n, (W n).commutatorCard ≤ B)
    {p : ℝ}
    (hprob : Filter.Tendsto (fun n => (W n).probability)
      Filter.atTop (𝓝 p)) :
    p ∈ CommProbRange ∨
      ∃ q : ℕ, 2 ≤ q ∧
        ClusterPt ((q : ℝ) * p) (Filter.principal CommProbRange) := by
  let V : ℕ → FiniteCommProbWitness := fun n => (W n).centralCoreWitness
  have hVbound : ∀ n, (V n).commutatorCard ≤ B := by
    intro n
    exact (bfcCore_commutatorCard_le (W n)).trans (hbound n)
  obtain ⟨d, φ₁, hφ₁, hcard, hcode⟩ :=
    exists_fixed_commutator_model_subsequence V B hVbound
  let W₁ : ℕ → FiniteCommProbWitness := fun n => W (φ₁ n)
  let V₁ : ℕ → FiniteCommProbWitness := fun n => (W₁ n).centralCoreWitness
  have hcentral₁ : ∀ n,
      letI := (V₁ n).group
      commutator (V₁ n).carrier ≤ Subgroup.center (V₁ n).carrier := by
    intro n
    exact (W₁ n).centralCore_commutator_le_center
  have hcard₁ : ∀ n, (V₁ n).commutatorCard = d := by
    intro n
    exact hcard n
  have hcode₁ : ∀ n (hn : (V₁ n).commutatorCard = d)
      (hzero : (V₁ 0).commutatorCard = d),
      (V₁ n).commutatorMulCode d hn =
        (V₁ 0).commutatorMulCode d hzero := by
    intro n hn hzero
    exact hcode n hn hzero
  have hbound₁ : ∀ n, (W₁ n).commutatorCard ≤ B := by
    intro n
    exact hbound (φ₁ n)
  have hprob₁ : Filter.Tendsto (fun n => (W₁ n).probability)
      Filter.atTop (𝓝 p) := hprob.comp hφ₁.tendsto_atTop
  obtain ⟨a, φ₂, hφ₂, ha⟩ :=
    exists_classTwoCharacterIndex_profile_subsequence
      V₁ hcentral₁ d hcard₁ hcode₁
  exact bfcCharacterIndex_profile_dichotomy
    W₁ B hbound₁ d hcard₁ hcode₁ φ₂
    (hprob₁.comp hφ₂.tendsto_atTop) a ha

end

end Submission.Helpers
