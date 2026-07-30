import Submission.SphereCommutationReduction
import Submission.StableSphere

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Submission.Helpers

open Set

noncomputable section

private abbrev SE (d : ℕ) := EuclideanSpace ℝ (Fin d)

private abbrev suspensionSplit (d : ℕ) :
    SE (d + d) ≃L[ℝ] SE d × SE d :=
  splitBlocks d

private abbrev suspensionFirst (d : ℕ) (w : SE (d + d)) : SE d :=
  firstBlock d w

private abbrev suspensionSecond (d : ℕ) (w : SE (d + d)) : SE d :=
  secondBlock d w

private abbrev suspensionJoin (d : ℕ) (u v : SE d) : SE (d + d) :=
  joinBlocks d u v

private theorem suspensionFirst_join (d : ℕ) (u v : SE d) :
    suspensionFirst d (suspensionJoin d u v) = u :=
  firstBlock_joinBlocks d u v

private theorem suspensionSecond_join (d : ℕ) (u v : SE d) :
    suspensionSecond d (suspensionJoin d u v) = v :=
  secondBlock_joinBlocks d u v

private theorem suspensionJoin_blocks (d : ℕ) (w : SE (d + d)) :
    suspensionJoin d (suspensionFirst d w) (suspensionSecond d w) = w :=
  joinBlocks_blocks d w

private theorem suspension_norm_sq_blocks (d : ℕ) (w : SE (d + d)) :
    ‖w‖ ^ 2 = ‖suspensionFirst d w‖ ^ 2 + ‖suspensionSecond d w‖ ^ 2 :=
  norm_sq_eq_blocks d w

private theorem suspension_norm_sq_join (d : ℕ) (u v : SE d) :
    ‖suspensionJoin d u v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 :=
  norm_sq_joinBlocks d u v

private theorem continuous_suspensionFirst (d : ℕ) :
    Continuous (suspensionFirst d) :=
  continuous_firstBlock d

private theorem continuous_suspensionSecond (d : ℕ) :
    Continuous (suspensionSecond d) :=
  continuous_secondBlock d

private theorem continuous_suspensionJoin (d : ℕ) :
    Continuous (Function.uncurry (suspensionJoin d)) :=
  continuous_joinBlocks d

private def suspendedPoint (d : ℕ) (x : SE d) : SE (d + d) :=
  suspensionJoin d x 0

private theorem suspendedPoint_not_mem_range (d : ℕ)
    (r : Metric.sphere (0 : SE d) 1 → SE d)
    (x : ((Set.range r)ᶜ : Set (SE d))) :
    suspendedPoint d x ∉ Set.range (suspendedEmbedding d r) := by
  rintro ⟨q, hq⟩
  have hsecond : suspensionSecond d (q : SE (d + d)) = 0 := by
    have h := congrArg (suspensionSecond d) hq
    simpa only [suspendedPoint, suspendedEmbedding, suspensionSecond_join] using h
  have hqnorm : ‖(q : SE (d + d))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp q.2
  have hfirstnorm : ‖suspensionFirst d (q : SE (d + d))‖ = 1 := by
    have hblocks := suspension_norm_sq_blocks d (q : SE (d + d))
    rw [hqnorm, one_pow, hsecond, norm_zero, zero_pow (by norm_num), add_zero] at hblocks
    nlinarith [norm_nonneg (suspensionFirst d (q : SE (d + d)))]
  have hfirstne : suspensionFirst d (q : SE (d + d)) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hfirstnorm]; norm_num)
  have hfirst := congrArg (suspensionFirst d) hq
  simp only [suspendedEmbedding, suspendedPoint, firstBlock_joinBlocks] at hfirst
  rw [radialEmbeddingExtension, dif_neg hfirstne, hfirstnorm, one_smul] at hfirst
  apply x.2
  refine ⟨⟨NormedSpace.normalize (suspensionFirst d (q : SE (d + d))), ?_⟩,
    hfirst⟩
  rw [mem_sphere_zero_iff_norm]
  exact NormedSpace.norm_normalize hfirstne

private def suspensionScale {d : ℕ} (v : SE d) : ℝ :=
  Real.sqrt (1 - ‖v‖ ^ 2)

private theorem suspensionScale_pos {d : ℕ} {v : SE d} (hv : ‖v‖ < 1) :
    0 < suspensionScale v := by
  apply Real.sqrt_pos.2
  nlinarith [norm_nonneg v]

private theorem suspensionScale_sq {d : ℕ} {v : SE d} (hv : ‖v‖ ≤ 1) :
    suspensionScale v ^ 2 = 1 - ‖v‖ ^ 2 := by
  exact Real.sq_sqrt (by nlinarith [norm_nonneg v])

private theorem suspensionScale_eq_zero {d : ℕ} {v : SE d} (hv : ‖v‖ = 1) :
    suspensionScale v = 0 := by
  simp [suspensionScale, hv]

private theorem continuous_suspensionScale (d : ℕ) :
    Continuous (suspensionScale : SE d → ℝ) := by
  exact Real.continuous_sqrt.comp
    (continuous_const.sub (continuous_norm.pow 2))

private def suspensionCone (d : ℕ) (p : SE d × SE d) : SE (d + d) :=
  suspensionJoin d (suspensionScale p.2 • p.1) p.2

private theorem continuous_suspensionCone (d : ℕ) :
    Continuous (suspensionCone d) := by
  have hscaled : Continuous (fun p : SE d × SE d ↦
      suspensionScale p.2 • p.1) :=
    ((continuous_suspensionScale d).comp continuous_snd).smul continuous_fst
  have hpair : Continuous (fun p : SE d × SE d ↦
      (suspensionScale p.2 • p.1, p.2)) :=
    hscaled.prodMk continuous_snd
  change Continuous (fun p : SE d × SE d ↦
    (splitBlocks d).symm (suspensionScale p.2 • p.1, p.2))
  exact (splitBlocks d).symm.continuous.comp hpair

private def openSuspensionRegion (d : ℕ) (U : Set (SE d)) : Set (SE (d + d)) :=
  {w | ‖suspensionSecond d w‖ < 1 ∧
    (suspensionScale (suspensionSecond d w))⁻¹ • suspensionFirst d w ∈ U}

private def closedSuspensionRegion (d : ℕ) (U : Set (SE d)) : Set (SE (d + d)) :=
  suspensionCone d '' (closure U ×ˢ Metric.closedBall (0 : SE d) 1)

private theorem openSuspensionRegion_mem (d : ℕ) (U : Set (SE d))
    {u v : SE d} (hu : u ∈ U) (hv : ‖v‖ < 1) :
    suspensionCone d (u, v) ∈ openSuspensionRegion d U := by
  constructor
  · simpa only [suspensionCone, suspensionSecond_join] using hv
  · simp only [suspensionCone, suspensionSecond_join, suspensionFirst_join]
    simpa only [smul_smul, inv_mul_cancel₀ (suspensionScale_pos hv).ne',
      one_smul] using hu

private theorem suspendedPoint_mem_openSuspensionRegion (d : ℕ)
    (U : Set (SE d)) {x : SE d} (hx : x ∈ U) :
    suspendedPoint d x ∈ openSuspensionRegion d U := by
  change ‖suspensionSecond d (suspensionJoin d x 0)‖ < 1 ∧
    (suspensionScale (suspensionSecond d (suspensionJoin d x 0)))⁻¹ •
      suspensionFirst d (suspensionJoin d x 0) ∈ U
  rw [suspensionSecond_join, suspensionFirst_join]
  simpa [suspensionScale] using hx

private theorem openSuspensionRegion_subset_closed (d : ℕ) (U : Set (SE d)) :
    openSuspensionRegion d U ⊆ closedSuspensionRegion d U := by
  intro w hw
  let v := suspensionSecond d w
  let u := (suspensionScale v)⁻¹ • suspensionFirst d w
  have hv : ‖v‖ < 1 := hw.1
  have hscale : suspensionScale v ≠ 0 := (suspensionScale_pos hv).ne'
  have hu : u ∈ U := hw.2
  refine ⟨(u, v), ⟨subset_closure hu, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact hv.le
  · dsimp only [suspensionCone, u, v]
    rw [smul_smul, mul_inv_cancel₀ hscale, one_smul,
      suspensionJoin_blocks]

private theorem isCompact_closedSuspensionRegion (d : ℕ) (U : Set (SE d))
    (hUb : Bornology.IsBounded U) :
    IsCompact (closedSuspensionRegion d U) := by
  exact (hUb.isCompact_closure.prod (isCompact_closedBall (0 : SE d) 1)).image
    (continuous_suspensionCone d)

private theorem isBounded_openSuspensionRegion (d : ℕ) (U : Set (SE d))
    (hUb : Bornology.IsBounded U) :
    Bornology.IsBounded (openSuspensionRegion d U) :=
  (isCompact_closedSuspensionRegion d U hUb).isBounded.subset
    (openSuspensionRegion_subset_closed d U)

private theorem suspensionCone_mem_range_of_mem_frontier (d : ℕ)
    (r : Metric.sphere (0 : SE d) 1 → SE d) (U : Set (SE d))
    (hfront : frontier U = Set.range r) {u v : SE d}
    (hu : u ∈ frontier U) (hv : ‖v‖ ≤ 1) :
    suspensionCone d (u, v) ∈ Set.range (suspendedEmbedding d r) := by
  rw [hfront] at hu
  obtain ⟨z, rfl⟩ := hu
  let s := suspensionScale v
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  let qvec : SE (d + d) := suspensionJoin d (s • (z : SE d)) v
  have hqnorm : ‖qvec‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)).mp
    rw [suspension_norm_sq_join, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs0, mem_sphere_zero_iff_norm.mp z.2, mul_one,
      suspensionScale_sq hv]
    ring
  let q : Metric.sphere (0 : SE (d + d)) 1 :=
    ⟨qvec, mem_sphere_zero_iff_norm.mpr hqnorm⟩
  refine ⟨q, ?_⟩
  apply (suspensionSplit d).injective
  apply Prod.ext
  · change suspensionFirst d (suspendedEmbedding d r q) =
      suspensionFirst d (suspensionCone d (r z, v))
    dsimp only [q, qvec]
    simp only [suspendedEmbedding, suspensionCone, suspensionFirst_join]
    change radialEmbeddingExtension d r (s • (z : SE d)) = s • r z
    by_cases hs : s = 0
    · simp [hs, radialEmbeddingExtension]
    · have hz0 : (z : SE d) ≠ 0 := by
        intro hz
        have hznorm := mem_sphere_zero_iff_norm.mp z.2
        rw [hz, norm_zero] at hznorm
        norm_num at hznorm
      have hsz : s • (z : SE d) ≠ 0 := smul_ne_zero hs hz0
      have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      rw [radialEmbeddingExtension, dif_neg hsz, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hs0,
        mem_sphere_zero_iff_norm.mp z.2, mul_one]
      congr 1
      apply congrArg r
      apply Subtype.ext
      calc
        NormedSpace.normalize (s • (z : SE d)) =
            NormedSpace.normalize (z : SE d) :=
          NormedSpace.normalize_smul_of_pos hspos (z : SE d)
        _ = (z : SE d) := NormedSpace.normalize_eq_self_of_norm_eq_one
          (mem_sphere_zero_iff_norm.mp z.2)
  · change suspensionSecond d (suspendedEmbedding d r q) =
      suspensionSecond d (suspensionCone d (r z, v))
    dsimp only [q, qvec]
    simp only [suspendedEmbedding, suspensionCone, suspensionSecond_join]

private theorem suspensionCone_mem_range_of_norm_eq_one (d : ℕ)
    (r : Metric.sphere (0 : SE d) 1 → SE d) {u v : SE d}
    (hv : ‖v‖ = 1) :
    suspensionCone d (u, v) ∈ Set.range (suspendedEmbedding d r) := by
  let qvec : SE (d + d) := suspensionJoin d 0 v
  have hqnorm : ‖qvec‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)).mp
    rw [suspension_norm_sq_join, norm_zero, zero_pow (by norm_num), zero_add, hv]
  let q : Metric.sphere (0 : SE (d + d)) 1 :=
    ⟨qvec, mem_sphere_zero_iff_norm.mpr hqnorm⟩
  refine ⟨q, ?_⟩
  apply (suspensionSplit d).injective
  apply Prod.ext
  · change suspensionFirst d (suspendedEmbedding d r q) =
      suspensionFirst d (suspensionCone d (u, v))
    dsimp only [q, qvec]
    simp only [suspendedEmbedding, suspensionCone, firstBlock_joinBlocks,
      secondBlock_joinBlocks, suspensionScale_eq_zero hv, zero_smul]
    rw [radialEmbeddingExtension, dif_pos rfl]
  · change suspensionSecond d (suspendedEmbedding d r q) =
      suspensionSecond d (suspensionCone d (u, v))
    dsimp only [q, qvec]
    simp only [suspendedEmbedding, suspensionCone, suspensionSecond_join]

private theorem closedSuspensionRegion_subset_open_union_range (d : ℕ)
    (r : Metric.sphere (0 : SE d) 1 → SE d) (U : Set (SE d))
    (hUOpen : IsOpen U) (hfront : frontier U = Set.range r) :
    closedSuspensionRegion d U ⊆
      openSuspensionRegion d U ∪ Set.range (suspendedEmbedding d r) := by
  rintro _ ⟨⟨u, v⟩, ⟨hucl, hvball⟩, rfl⟩
  have hv : ‖v‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hvball
  by_cases hvlt : ‖v‖ < 1
  · by_cases hu : u ∈ U
    · exact Or.inl (openSuspensionRegion_mem d U hu hvlt)
    · apply Or.inr
      apply suspensionCone_mem_range_of_mem_frontier d r U hfront
      · change u ∈ closure U \ interior U
        exact ⟨hucl, by simpa only [hUOpen.interior_eq] using hu⟩
      · exact hv
  · apply Or.inr
    apply suspensionCone_mem_range_of_norm_eq_one d r
    exact le_antisymm hv (le_of_not_gt hvlt)

private theorem openSuspensionRegion_eq_closed_inter_compl (d : ℕ)
    (r : Metric.sphere (0 : SE d) 1 → SE d) (U : Set (SE d))
    (hUOpen : IsOpen U) (hfront : frontier U = Set.range r) :
    openSuspensionRegion d U = closedSuspensionRegion d U ∩
      (Set.range (suspendedEmbedding d r))ᶜ := by
  apply Set.Subset.antisymm
  · intro w hw
    refine ⟨openSuspensionRegion_subset_closed d U hw, ?_⟩
    rintro ⟨q, hq⟩
    have hwSecond : suspensionSecond d w = suspensionSecond d q := by
      rw [← hq]
      simp only [suspendedEmbedding, suspensionSecond_join]
    have hqnorm : ‖(q : SE (d + d))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp q.2
    have hblocks := suspension_norm_sq_blocks d (q : SE (d + d))
    have hsecondlt : ‖suspensionSecond d (q : SE (d + d))‖ < 1 := by
      simpa only [← hwSecond] using hw.1
    have hfirstne : suspensionFirst d (q : SE (d + d)) ≠ 0 := by
      intro hzero
      rw [hqnorm, one_pow, hzero, norm_zero, zero_pow (by norm_num), zero_add]
        at hblocks
      nlinarith [norm_nonneg (suspensionSecond d (q : SE (d + d)))]
    have hfirst := congrArg (suspensionFirst d) hq
    simp only [suspendedEmbedding, suspensionFirst_join] at hfirst
    rw [radialEmbeddingExtension, dif_neg hfirstne] at hfirst
    have hscale : suspensionScale (suspensionSecond d w) =
        ‖suspensionFirst d (q : SE (d + d))‖ := by
      have hsnonneg : 0 ≤ suspensionScale (suspensionSecond d w) :=
        Real.sqrt_nonneg _
      have hfnnonneg : 0 ≤ ‖suspensionFirst d (q : SE (d + d))‖ := norm_nonneg _
      have hblocksOne := hblocks
      rw [hqnorm, one_pow] at hblocksOne
      apply (sq_eq_sq₀ hsnonneg hfnnonneg).mp
      rw [suspensionScale_sq hw.1.le, hwSecond]
      nlinarith [hblocksOne]
    have hscale0 : suspensionScale (suspensionSecond d w) ≠ 0 :=
      (suspensionScale_pos hw.1).ne'
    have hrU : r (normalizedSpherePoint d (suspensionFirst d q) hfirstne) ∈ U := by
      have hmem := hw.2
      rw [← hfirst, ← hscale] at hmem
      simpa only [smul_smul, inv_mul_cancel₀ hscale0, one_smul] using hmem
    have hrfront : r (normalizedSpherePoint d (suspensionFirst d q) hfirstne) ∈
        frontier U := by
      rw [hfront]
      exact ⟨_, rfl⟩
    change r (normalizedSpherePoint d (suspensionFirst d q) hfirstne) ∈
      closure U \ interior U at hrfront
    exact hrfront.2 (by simpa only [hUOpen.interior_eq] using hrU)
  · intro w hw
    rcases closedSuspensionRegion_subset_open_union_range d r U hUOpen hfront hw.1 with
      hwOpen | hwRange
    · exact hwOpen
    · exact (hw.2 hwRange).elim

private theorem isOpen_openSuspensionRegion (d : ℕ) (U : Set (SE d))
    (hUOpen : IsOpen U) : IsOpen (openSuspensionRegion d U) := by
  let V : Set (SE (d + d)) := {w | ‖suspensionSecond d w‖ < 1}
  have hVOpen : IsOpen V :=
    isOpen_lt ((continuous_suspensionSecond d).norm) continuous_const
  let quotient : C(V, SE d) :=
    { toFun := fun w ↦
        (suspensionScale (suspensionSecond d w))⁻¹ • suspensionFirst d w
      continuous_toFun := by
        have hscale : Continuous (fun w : V ↦
            suspensionScale (suspensionSecond d (w : SE (d + d)))) :=
          (continuous_suspensionScale d).comp
            ((continuous_suspensionSecond d).comp continuous_subtype_val)
        have hfirst : Continuous (fun w : V ↦
            suspensionFirst d (w : SE (d + d))) :=
          (continuous_suspensionFirst d).comp continuous_subtype_val
        exact (hscale.inv₀ fun w ↦
          (suspensionScale_pos w.2).ne').smul hfirst }
  let good : Set V := quotient ⁻¹' U
  have hgoodOpen : IsOpen good := hUOpen.preimage quotient.continuous
  have hgoodImage : ((↑) : V → SE (d + d)) '' good =
      openSuspensionRegion d U := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
    · intro hw
      exact ⟨⟨w, hw.1⟩, hw.2, rfl⟩
  rw [← hgoodImage]
  exact hVOpen.isOpenMap_subtype_val good hgoodOpen

private theorem isClopen_openSuspensionRegionInComplement (d : ℕ)
    (r : Metric.sphere (0 : SE d) 1 → SE d) (U : Set (SE d))
    (hUOpen : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfront : frontier U = Set.range r) :
    IsClopen (((↑) : ((Set.range (suspendedEmbedding d r))ᶜ :
      Set (SE (d + d))) → SE (d + d)) ⁻¹' openSuspensionRegion d U) := by
  constructor
  · have hclosed : IsClosed (closedSuspensionRegion d U) :=
      (isCompact_closedSuspensionRegion d U hUb).isClosed
    have heq : (((↑) : ((Set.range (suspendedEmbedding d r))ᶜ :
        Set (SE (d + d))) → SE (d + d)) ⁻¹' openSuspensionRegion d U) =
        ((↑) : ((Set.range (suspendedEmbedding d r))ᶜ :
          Set (SE (d + d))) → SE (d + d)) ⁻¹' closedSuspensionRegion d U := by
      ext w
      rw [openSuspensionRegion_eq_closed_inter_compl d r U hUOpen hfront]
      simp only [mem_preimage, mem_inter_iff, mem_compl_iff]
      exact and_iff_left w.2
    rw [heq]
    exact hclosed.preimage continuous_subtype_val
  · exact (isOpen_openSuspensionRegion d U hUOpen).preimage continuous_subtype_val

def suspendedComplementPoint (d : ℕ)
    (r : Metric.sphere (0 : SE d) 1 → SE d)
    (x : ((Set.range r)ᶜ : Set (SE d))) :
    ((Set.range (suspendedEmbedding d r))ᶜ : Set (SE (d + d))) :=
  ⟨suspendedPoint d x, suspendedPoint_not_mem_range d r x⟩

@[simp] theorem suspendedComplementPoint_coe (d : ℕ)
    (r : Metric.sphere (0 : SE d) 1 → SE d)
    (x : ((Set.range r)ᶜ : Set (SE d))) :
    (suspendedComplementPoint d r x : SE (d + d)) = joinBlocks d x 0 :=
  rfl

theorem suspendedComplementPoint_mem_region (d : ℕ)
    (r : Metric.sphere (0 : SE d) 1 → SE d) (U : Set (SE d))
    (x : ((Set.range r)ᶜ : Set (SE d))) (hx : (x : SE d) ∈ U) :
    (suspendedComplementPoint d r x : SE (d + d)) ∈
      openSuspensionRegion d U :=
  suspendedPoint_mem_openSuspensionRegion d U hx

theorem isBounded_suspendedComponent (d : ℕ)
    (r : Metric.sphere (0 : SE d) 1 → SE d) (U : Set (SE d))
    (hUOpen : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfront : frontier U = Set.range r)
    (x : ((Set.range r)ᶜ : Set (SE d))) (hx : (x : SE d) ∈ U) :
    Bornology.IsBounded
      (connectedComponentIn (Set.range (suspendedEmbedding d r))ᶜ
        (suspendedComplementPoint d r x : SE (d + d))) := by
  rw [connectedComponentIn_eq_image (suspendedComplementPoint d r x).2]
  apply (isBounded_openSuspensionRegion d U hUb).subset
  rintro _ ⟨z, hz, rfl⟩
  have hclopen :=
    isClopen_openSuspensionRegionInComplement d r U hUOpen hUb hfront
  exact hclopen.connectedComponent_subset
    (suspendedComplementPoint_mem_region d r U x hx) hz

theorem original_mem_region_of_suspendedComponent_mem (d : ℕ)
    (r : Metric.sphere (0 : SE d) 1 → SE d) (U : Set (SE d))
    (hUOpen : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfront : frontier U = Set.range r)
    (x y : ((Set.range r)ᶜ : Set (SE d))) (hx : (x : SE d) ∈ U)
    (hy : (suspendedComplementPoint d r y : SE (d + d)) ∈
      connectedComponentIn (Set.range (suspendedEmbedding d r))ᶜ
        (suspendedComplementPoint d r x : SE (d + d))) :
    (y : SE d) ∈ U := by
  rw [connectedComponentIn_eq_image (suspendedComplementPoint d r x).2] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hclopen :=
    isClopen_openSuspensionRegionInComplement d r U hUOpen hUb hfront
  have hzRegion := hclopen.connectedComponent_subset
    (suspendedComplementPoint_mem_region d r U x hx) hz
  have hyRegion : (suspendedComplementPoint d r y : SE (d + d)) ∈
      openSuspensionRegion d U := hzy ▸ hzRegion
  have hyU := hyRegion.2
  simp only [suspendedComplementPoint, suspendedPoint, secondBlock_joinBlocks,
    firstBlock_joinBlocks] at hyU
  simpa [suspensionScale] using hyU

end

end Submission.Helpers
