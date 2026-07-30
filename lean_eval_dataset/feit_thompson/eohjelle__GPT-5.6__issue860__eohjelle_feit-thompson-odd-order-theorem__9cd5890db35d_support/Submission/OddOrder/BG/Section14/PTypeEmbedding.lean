import Submission.OddOrder.BG.Section14.SigmaDecompositionAndTypes
import Submission.OddOrder.BG.Section14.PTypeStructure
import Submission.OddOrder.BG.Section14.SigmaSupport
import Submission.OddOrder.BG.Section12.ComplementExistence
import Submission.OddOrder.MathlibSupport.NormalizedTI
import Submission.OddOrder.PF.Section02.ClassSupportProperties
import Submission.OddOrder.PF.Section02.ClassSupportPartition
import Submission.OddOrder.PF.Section03.CyclicTIGroupFacts
import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
# Bender--Glauberman Section 14: the P-type embedding theorem

This file ports `BGsection14.v`, lines 1315--1946: Theorem 14.7 and the two
parts of Corollary 14.8.  The eight conclusions of the source theorem are
packaged as `PTypeEmbedding`; this avoids a brittle, deeply nested conjunction
while retaining one named field for every source clause (a)--(h).

MathComp's predicate `pi.-Hall(M) K` includes `K \subset M`.  In the Lean
interface this containment is stated separately from
`IsHall pi (K.subgroupOf M)`.
-/

namespace Submission.OddOrder.BG.Section14

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative BigOperators

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! ## The conclusion of Theorem 14.7 -/

/-- The subgroup denoted `K^* = C_{M_sigma}(K)` in Theorem 14.7. -/
def pTypePartner (M K : Subgroup G) : Subgroup G :=
  centralizerWithin (sigmaCore M) K

/-- The subgroup `Z = K K^*` occurring in Theorem 14.7. -/
def pTypeJoin (M K : Subgroup G) : Subgroup G :=
  K ⊔ pTypePartner M K

/-- The TI set `Z-hat = Z \ (K union K^*)` occurring in Theorem 14.7. -/
def pTypeTISet (M K : Subgroup G) : Set G :=
  (pTypeJoin M K : Set G) \
    ((K : Set G) ∪ (pTypePartner M K : Set G))

private theorem centralizerWithin_map_mulEquiv_pType
    (D S : Subgroup G) (e : G ≃* G) :
    (centralizerWithin D S).map e.toMonoidHom =
      centralizerWithin (D.map e.toMonoidHom)
        (S.map e.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mpr hy.1, ?_⟩
    intro z hz
    have hz' : e.symm z ∈ S := Subgroup.mem_map_equiv.mp hz
    simpa using congrArg e (hy.2 (e.symm z) hz')
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mp hy.1, ?_⟩
    intro z hz
    have hz' : e z ∈ S.map e.toMonoidHom :=
      (Subgroup.mem_map_iff_mem e.injective).mpr hz
    simpa using congrArg e.symm (hy.2 (e z) hz')

private theorem pTypePartner_map_conj
    (M K : Subgroup G) (g : G) :
    (pTypePartner M K).map (MulAut.conj g).toMonoidHom =
      pTypePartner
        (M.map (MulAut.conj g).toMonoidHom)
        (K.map (MulAut.conj g).toMonoidHom) := by
  simpa only [pTypePartner, sigmaCore_conj] using
    centralizerWithin_map_mulEquiv_pType (sigmaCore M) K (MulAut.conj g)

private theorem mem_pTypeTISet_map_conj_iff
    (M K : Subgroup G) (g x : G) :
    (MulAut.conj g) x ∈
        pTypeTISet
          (M.map (MulAut.conj g).toMonoidHom)
          (K.map (MulAut.conj g).toMonoidHom) ↔
      x ∈ pTypeTISet M K := by
  let e : G ≃* G := MulAut.conj g
  simp only [pTypeTISet, pTypeJoin, Set.mem_diff, Set.mem_union]
  rw [← pTypePartner_map_conj, ← Subgroup.map_sup]
  have hmem (H : Subgroup G) :
      e x ∈ H.map e.toMonoidHom ↔ x ∈ H := by
    rw [Subgroup.mem_map_equiv]
    simpa only [MulEquiv.symm_apply_apply]
  change
    (e x ∈ (K ⊔ pTypePartner M K).map e.toMonoidHom ∧
        ¬ (e x ∈ K.map e.toMonoidHom ∨
          e x ∈ (pTypePartner M K).map e.toMonoidHom)) ↔
      x ∈ K ⊔ pTypePartner M K ∧
        ¬ (x ∈ K ∨ x ∈ pTypePartner M K)
  simp only [hmem]

/-- Two ambient subgroups are conjugate in `G`.

The orientation agrees with the rest of the odd-order port: the right
conjugate from MathComp is represented by `MulAut.conj`. -/
def AreConjugateSubgroups (M H : Subgroup G) : Prop :=
  ∃ g : G, H = M.map (MulAut.conj g).toMonoidHom

private theorem areConjugateSubgroups_refl (M : Subgroup G) :
    AreConjugateSubgroups M M := by
  refine ⟨1, ?_⟩
  ext x
  rw [Subgroup.mem_map_equiv]
  simpa only [MulAut.conj_symm_apply, inv_one, one_mul, mul_one]

private theorem areConjugateSubgroups_of_map_conj_eq
    {A B : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom = B) :
    AreConjugateSubgroups B A := by
  refine ⟨g⁻¹, ?_⟩
  rw [← h, Subgroup.map_map]
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Two conjugacy-saturated supports meet exactly when a conjugate of one
raw support meets the other.  This is the set-theoretic reduction used in
the induction at the end of Theorem 14.7. -/
private theorem classSupport_overlap_witness
    {S T : Set G}
    (h : ¬ Disjoint
      (classSupportWithin (⊤ : Subgroup G) S)
      (classSupportWithin (⊤ : Subgroup G) T)) :
    ∃ x : G, x ∈ S ∧ ∃ g : G, g⁻¹ * x * g ∈ T := by
  rw [Set.not_disjoint_iff] at h
  obtain ⟨z, hzS, hzT⟩ := h
  rcases hzS with ⟨x, hxS, g, -, rfl⟩
  rcases hzT with ⟨y, hyT, a, -, hay⟩
  refine ⟨x, hxS, g * a⁻¹, ?_⟩
  change a⁻¹ * y * a = g⁻¹ * x * g at hay
  have hxy : (g * a⁻¹)⁻¹ * x * (g * a⁻¹) = y := by
    rw [mul_inv_rev, inv_inv]
    calc
      a * g⁻¹ * x * (g * a⁻¹) =
          a * (g⁻¹ * x * g) * a⁻¹ := by group
      _ = a * (a⁻¹ * y * a) * a⁻¹ := by rw [← hay]
      _ = y := by group
  rwa [hxy]

private theorem not_disjoint_of_two_half_supports
    {S T : Set G}
    (hS : (Nat.card G : ℚ) / 2 < (S.ncard : ℚ))
    (hT : (Nat.card G : ℚ) / 2 < (T.ncard : ℚ)) :
    ¬ Disjoint S T := by
  intro hdis
  have hunion := Set.ncard_union_eq hdis
  have hle : (S ∪ T).ncard ≤ Nat.card G := by
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  have hunionQ : ((S ∪ T).ncard : ℚ) =
      (S.ncard : ℚ) + (T.ncard : ℚ) := by
    exact_mod_cast hunion
  have hleQ : ((S ∪ T).ncard : ℚ) ≤ Nat.card G := by
    exact_mod_cast hle
  nlinarith

/-- The class supports of `T` and a sigma cover are disjoint once `T` is
disjoint from the sigma cover of every maximal subgroup.  Both supports are
conjugacy-saturated, so two meeting conjugates can be transported back to
`T` and the sigma cover of a conjugate maximal subgroup. -/
private theorem classSupport_disjoint_of_disjoint_sigmaCover
    {T : Set G}
    (hdis : ∀ {H : Subgroup G},
      H ∈ minSimple_max_groups (G := G) →
        Disjoint T (sigmaCover H))
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Disjoint
      (classSupportWithin (⊤ : Subgroup G) T)
      (classSupportWithin (⊤ : Subgroup G) (sigmaCover M)) := by
  apply Set.disjoint_left.2
  intro z hzT hzM
  rcases hzT with ⟨t, htT, g, -, rfl⟩
  rcases hzM with ⟨s, hsM, a, -, hconj⟩
  change a⁻¹ * s * a = g⁻¹ * t * g at hconj
  let c : G := g * a⁻¹
  have hst : (MulAut.conj c) s = t := by
    rw [MulAut.conj_apply]
    calc
      c * s * c⁻¹ = g * (a⁻¹ * s * a) * g⁻¹ := by
        simp [c]
        group
      _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [hconj]
      _ = t := by group
  have htSigma :
      t ∈ sigmaCover (M.map (MulAut.conj c).toMonoidHom) := by
    rw [sigma_supportJ]
    exact ⟨s, hsM, hst⟩
  have hMc :
      M.map (MulAut.conj c).toMonoidHom ∈
        minSimple_max_groups (G := G) :=
    (mmaxJ M (MulAut.conj c)).2 hM
  exact (Set.disjoint_left.mp (hdis hMc)) htT htSigma

/-- Conjugating a sigma-cover element cannot produce the identity. -/
private theorem classSupport_sigmaCover_subset_nonidentity_pType
    {M : Subgroup G} (hM : M ∈ minSimple_max_groups (G := G)) :
    classSupportWithin (⊤ : Subgroup G) (sigmaCover M) ⊆
      nonidentitySet G := by
  rintro y ⟨x, hxCover, g, -, rfl⟩
  change g⁻¹ * x * g ≠ 1
  intro hconjOne
  have hxOne : x = 1 := by
    calc
      x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [hconjOne]; simp
  rcases hxCover with ⟨a, haSigma, haOne, r, hr, rfl⟩
  have haDecomp : a ∈ sigmaDecomposition (a * r) :=
    mem_sigma_cover_decomposition
      (Msigma_ell1 hM haSigma haOne)
      ⟨a, Set.mem_singleton a, r, hr, rfl⟩
  have hlenNe : sigmaLength (a * r) ≠ 0 :=
    Set.ncard_ne_zero_of_mem haDecomp
  exact hlenNe ((ell_sigma0P (a * r)).mpr hxOne)

/-- Removing the identity from a finite subgroup removes exactly one
element, stated without truncated subtraction for use in cardinal sums. -/
private theorem subgroupNonidentity_ncard_add_one_pType
    (H : Subgroup G) :
    (subgroupNonidentity H).ncard + 1 = Nat.card H := by
  have hone : (1 : G) ∈ (H : Set G) := H.one_mem
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hcard :
      (subgroupNonidentity H).ncard = Nat.card H - 1 := by
    rw [show subgroupNonidentity H = (H : Set G) \ {1} by
      ext x
      simp [subgroupNonidentity, nonidentitySet]]
    rw [Set.ncard_sdiff_singleton_of_mem hone, ← Nat.card_coe_set_eq]
    congr 1
  rw [hcard]
  omega

/-- The ambient nonidentity set likewise has cardinality one below the
ambient group. -/
private theorem nonidentitySet_ncard_add_one_pType :
    (nonidentitySet G).ncard + 1 = Nat.card G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hcard : (nonidentitySet G).ncard = Nat.card G - 1 := by
    rw [show nonidentitySet G = (Set.univ : Set G) \ {1} by
      ext x
      simp [nonidentitySet]]
    rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ 1), Set.ncard_univ]
  rw [hcard]
  omega

private theorem ncard_classSupport_normalizedTI
    {S : Set G} {N : Subgroup G}
    (hTI : IsNormalizedTI S (⊤ : Subgroup G) N) :
    (classSupportWithin (⊤ : Subgroup G) S).ncard =
      S.ncard * N.index := by
  let action := subgroupConjugationActionOnAmbient (⊤ : Subgroup G)
  letI : SMul (⊤ : Subgroup G) G := action.toSMul
  letI : MulAction (⊤ : Subgroup G) G := action.toMulAction
  letI : MulAction (⊤ : Subgroup G) (Set G) := Set.mulActionSet
  have hpart := normalizedTI_classSupport_partition hTI
  change IsSetPartition (MulAction.orbit (⊤ : Subgroup G) S)
      (classSupportWithin (⊤ : Subgroup G) S) ∧
    (MulAction.orbit (⊤ : Subgroup G) S).ncard =
      N.relIndex (⊤ : Subgroup G) at hpart
  have horbitFinite :
      (MulAction.orbit (⊤ : Subgroup G) S).Finite := Set.toFinite _
  have hblock : ∀ B ∈ MulAction.orbit (⊤ : Subgroup G) S,
      B.ncard = S.ncard := by
    intro B hB
    rcases hB with ⟨g, rfl⟩
    exact Set.ncard_smul_set g S
  rw [← hpart.1.1]
  have hsUnion : ⋃₀ (MulAction.orbit (⊤ : Subgroup G) S) =
      ⋃ B ∈ MulAction.orbit (⊤ : Subgroup G) S, B := by
    ext x
    simp
  rw [hsUnion]
  calc
    (⋃ B ∈ MulAction.orbit (⊤ : Subgroup G) S, B).ncard =
        ∑ᶠ B ∈ MulAction.orbit (⊤ : Subgroup G) S, B.ncard :=
      horbitFinite.ncard_biUnion
        (fun B _ ↦ Set.toFinite B) hpart.1.2.1
    _ = ∑ᶠ _B ∈ MulAction.orbit (⊤ : Subgroup G) S, S.ncard :=
      finsum_mem_congr rfl hblock
    _ = (∑ᶠ _B ∈ MulAction.orbit (⊤ : Subgroup G) S, (1 : ℕ)) *
          S.ncard := by
      rw [finsum_mem_mul' (fun _B : Set G ↦ 1) S.ncard horbitFinite]
      simp
    _ = (MulAction.orbit (⊤ : Subgroup G) S).ncard * S.ncard := by
      rw [finsum_one]
    _ = N.relIndex (⊤ : Subgroup G) * S.ncard := by rw [hpart.2]
    _ = S.ncard * N.index := by
      rw [N.relIndex_top_right, Nat.mul_comm]

private theorem internalDirectProduct_eq_sup
    {A B W : Subgroup G} (h : IsInternalDirectProductIn A B W) :
    W = A ⊔ B := by
  apply le_antisymm
  · intro x hx
    have hx' : (⟨x, hx⟩ : W) ∈
        (A.subgroupOf W) ⊔ (B.subgroupOf W) := by
      rw [h.complement.sup_eq_top]
      exact Subgroup.mem_top _
    have hxmap : x ∈
        ((A.subgroupOf W) ⊔ (B.subgroupOf W)).map W.subtype :=
      ⟨⟨x, hx⟩, hx', rfl⟩
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le h.left_le,
      Subgroup.map_subgroupOf_eq_of_le h.right_le] at hxmap
    exact hxmap
  · exact sup_le h.left_le h.right_le

private theorem internalSemidirectProduct_eq_sup
    {A B W : Subgroup G} (h : IsInternalSemidirectProductIn A B W) :
    W = A ⊔ B := by
  apply le_antisymm
  · intro x hx
    have hx' : (⟨x, hx⟩ : W) ∈
        (A.subgroupOf W) ⊔ (B.subgroupOf W) := by
      rw [h.2.2.2.sup_eq_top]
      exact Subgroup.mem_top _
    have hxmap : x ∈
        ((A.subgroupOf W) ⊔ (B.subgroupOf W)).map W.subtype :=
      ⟨⟨x, hx⟩, hx', rfl⟩
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le h.1,
      Subgroup.map_subgroupOf_eq_of_le h.2.1] at hxmap
    exact hxmap
  · exact sup_le h.1 h.2.1

private theorem internalDirectProduct_disjoint_ambient
    {A B W : Subgroup G} (h : IsInternalDirectProductIn A B W) :
    Disjoint A B := by
  rw [disjoint_iff]
  apply eq_bot_iff.mpr
  intro y hy
  let yW : W := ⟨y, h.left_le hy.1⟩
  let yA : A.subgroupOf W := ⟨yW, hy.1⟩
  let yB : B.subgroupOf W := ⟨yW, hy.2⟩
  have hpairs : (yA, (1 : B.subgroupOf W)) =
      ((1 : A.subgroupOf W), yB) := by
    apply h.complement.1
    apply Subtype.ext
    simp [yA, yB, yW]
  have hyAOne : yA = 1 := congrArg Prod.fst hpairs
  apply Subgroup.mem_bot.mpr
  have hyOne := congrArg (fun z : A.subgroupOf W ↦ (z : G)) hyAOne
  simpa [yA, yW] using hyOne

private theorem subgroupOf_disjoint_of_ambient_pType
    {A B W : Subgroup G} (hAW : A ≤ W) (hBW : B ≤ W)
    (hdis : Disjoint A B) :
    Disjoint (A.subgroupOf W) (B.subgroupOf W) := by
  rw [disjoint_iff]
  apply eq_bot_iff.mpr
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Subgroup.mem_bot.mp
  rw [← disjoint_iff.mp hdis]
  exact hx

/-- Both factors of an internal direct product are normal in the product.
They are the kernels of the opposite canonical projections. -/
private theorem internalDirectProduct_normal_factors
    {A B W : Subgroup G} (h : IsInternalDirectProductIn A B W) :
    (A.subgroupOf W).Normal ∧ (B.subgroupOf W).Normal := by
  have hAker : A.subgroupOf W = h.rightProjection.ker := by
    ext w
    constructor
    · intro hw
      let a : A := ⟨w, hw⟩
      have hwa : h.leftEmbedding a = w := by
        apply Subtype.ext
        rfl
      change h.rightProjection w = 1
      rw [← hwa, h.rightProjection_leftEmbedding]
    · intro hw
      have hproj : h.rightProjection w = 1 := hw
      have hwa : w = h.leftEmbedding (h.leftProjection w) := by
        calc
          w = h.mulEquiv (h.leftProjection w, h.rightProjection w) :=
            (h.mulEquiv_projections w).symm
          _ = h.mulEquiv (h.leftProjection w, 1) := by rw [hproj]
          _ = h.leftEmbedding (h.leftProjection w) :=
            h.mulEquiv_apply_left (h.leftProjection w)
      change (w : G) ∈ A
      rw [hwa]
      exact (h.leftProjection w).property
  have hBker : B.subgroupOf W = h.leftProjection.ker := by
    ext w
    constructor
    · intro hw
      let b : B := ⟨w, hw⟩
      have hwb : h.rightEmbedding b = w := by
        apply Subtype.ext
        rfl
      change h.leftProjection w = 1
      rw [← hwb, h.leftProjection_rightEmbedding]
    · intro hw
      have hproj : h.leftProjection w = 1 := hw
      have hwb : w = h.rightEmbedding (h.rightProjection w) := by
        calc
          w = h.mulEquiv (h.leftProjection w, h.rightProjection w) :=
            (h.mulEquiv_projections w).symm
          _ = h.mulEquiv (1, h.rightProjection w) := by rw [hproj]
          _ = h.rightEmbedding (h.rightProjection w) :=
            h.mulEquiv_apply_right (h.rightProjection w)
      change (w : G) ∈ B
      rw [hwb]
      exact (h.rightProjection w).property
  constructor
  · rw [hAker]
    infer_instance
  · rw [hBker]
    infer_instance

/-- Nilpotence transports from the two factors across the canonical direct
product equivalence. -/
private theorem isNilpotent_of_internalDirectProduct
    {A B W : Subgroup G} (h : IsInternalDirectProductIn A B W)
    (hA : Group.IsNilpotent A) (hB : Group.IsNilpotent B) :
    Group.IsNilpotent W := by
  letI : Group.IsNilpotent A := hA
  letI : Group.IsNilpotent B := hB
  exact Group.nilpotent_of_mulEquiv h.mulEquiv

/-- A subgroup of a nilpotent ambient subgroup is nilpotent, with both
subgroups represented in the common ambient group. -/
private theorem isNilpotent_of_le
    {A B : Subgroup G} (hB : Group.IsNilpotent B) (hAB : A ≤ B) :
    Group.IsNilpotent A := by
  letI : Group.IsNilpotent B := hB
  have hsub : Group.IsNilpotent (A.subgroupOf B) := by infer_instance
  letI : Group.IsNilpotent (A.subgroupOf B) := hsub
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hAB)

/-- A Sylow subgroup and its ambient image are isomorphic, hence cyclic
simultaneously. -/
private theorem isCyclic_ambientSylow_iff_pType
    {p : ℕ} (M : Subgroup G) (S : Sylow p M) :
    IsCyclic (ambientSylow M S) ↔ IsCyclic S := by
  let e : S ≃* ambientSylow M S :=
    (S : Subgroup M).equivMapOfInjective M.subtype M.subtype_injective
  exact e.isCyclic.symm

/-- A nontrivial semiregular actor has trivial full centralizer in the
acted-on subgroup. -/
private theorem centralizerWithin_eq_bot_of_semiregular_actor_ne_bot_pType
    {H R : Subgroup G} (hreg : IsSemiregularConjugation H R)
    (hR : R ≠ ⊥) :
    centralizerWithin H R = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
  have hrR : (r : G) ∈ R := r.property
  let rR : R := r
  let xH : H := ⟨x, hx.1⟩
  have hrR1 : rR ≠ 1 := by
    intro hr
    apply hr1
    simpa [rR] using congrArg Subtype.val hr
  have hcomm : (r : G) * x = x * (r : G) := hx.2 r hrR
  have hfix : (rR : G) * (xH : G) * (rR : G)⁻¹ = (xH : G) := by
    change (r : G) * x * (r : G)⁻¹ = x
    rw [hcomm]
    simp
  have hxOne : xH = 1 := hreg rR hrR1 xH hfix
  simpa [xH] using congrArg Subtype.val hxOne

private theorem isHall_map_mulEquiv_pType
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {pi : Set ℕ} {L : Subgroup A} (e : A ≃* B)
    (hL : IsHall pi L) :
    IsHall pi (L.map e.toMonoidHom) := by
  constructor
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hL.isPiNumber_card
  · change IsPiNumber piᶜ ((L.map (e : A →* B)).index)
    rw [Subgroup.index_map_equiv]
    exact hL.isPiNumber_index

private theorem isHall_subgroupOf_map_conj
    {H L : Subgroup G} (hLH : L ≤ H)
    {pi : Set ℕ} (hL : IsHall pi (L.subgroupOf H))
    (e : G ≃* G) :
    IsHall pi
      ((L.map e.toMonoidHom).subgroupOf
        (H.map e.toMonoidHom)) := by
  let eH : H ≃* H.map e.toMonoidHom :=
    H.equivMapOfInjective e.toMonoidHom e.injective
  have hmap :
      (L.subgroupOf H).map eH.toMonoidHom =
        (L.map e.toMonoidHom).subgroupOf
          (H.map e.toMonoidHom) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (y : G) ∈ L.map e.toMonoidHom
      exact (Subgroup.mem_map_iff_mem e.injective).mpr hy
    · intro hx
      change (x : G) ∈ L.map e.toMonoidHom at hx
      have hx' := Subgroup.mem_map_equiv.mp hx
      let y : H := ⟨e.symm x, hLH hx'⟩
      refine ⟨y, hx', ?_⟩
      apply Subtype.ext
      change e (e.symm (x : G)) = (x : G)
      exact e.apply_symm_apply _
  rw [← hmap]
  exact isHall_map_mulEquiv_pType eH hL

private theorem complementary_isHall_of_internalDirectProduct
    {A B W : Subgroup G} {pi : Set ℕ}
    (h : IsInternalDirectProductIn A B W)
    (hA : IsPiNumber piᶜ (Nat.card A))
    (hB : IsPiNumber pi (Nat.card B)) :
    IsHall piᶜ (A.subgroupOf W) ∧
      IsHall pi (B.subgroupOf W) := by
  constructor
  · constructor
    · simpa [MathlibSupport.natCard_subgroupOf_eq h.left_le] using hA
    · rw [h.complement.symm.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq h.right_le]
      simpa only [compl_compl] using hB
  · constructor
    · simpa [MathlibSupport.natCard_subgroupOf_eq h.right_le] using hB
    · rw [h.complement.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq h.left_le]
      exact hA

/-- Relative normal Hall containment, with all subgroups represented in the
same ambient group. -/
private theorem isPiNumber_le_normal_isHall_pType
    {pi : Set ℕ} {L H X : Subgroup G}
    (hHL : H ≤ L) (hHnormal : (H.subgroupOf L).Normal)
    (hHHall : IsHall pi (H.subgroupOf L))
    (hXL : X ≤ L) (hXpi : IsPiNumber pi (Nat.card X)) :
    X ≤ H := by
  let HL : Subgroup L := H.subgroupOf L
  let XL : Subgroup L := X.subgroupOf L
  have hXpiL : IsPiNumber pi (Nat.card XL) := by
    rw [MathlibSupport.natCard_subgroupOf_eq hXL]
    exact hXpi
  have hsupPi : IsPiNumber pi (Nat.card (HL ⊔ XL : Subgroup L)) :=
    isPiNumber_card_sup_of_normal_left hHnormal
      hHHall.isPiNumber_card hXpiL
  have hHLsup : HL ≤ HL ⊔ XL := le_sup_left
  have hrelPi : IsPiNumber pi (HL.relIndex (HL ⊔ XL)) :=
    hsupPi.of_dvd (Subgroup.relIndex_dvd_card HL (HL ⊔ XL))
  have hrelCompl : IsPiNumber piᶜ (HL.relIndex (HL ⊔ XL)) :=
    hHHall.isPiNumber_index.of_dvd
      (Subgroup.relIndex_dvd_index_of_le hHLsup)
  have hrelOne : HL.relIndex (HL ⊔ XL) = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (hrelPi.coprime_compl hrelCompl) dvd_rfl dvd_rfl
  have hsub : XL ≤ HL :=
    le_sup_right.trans (Subgroup.relIndex_eq_one.mp hrelOne)
  have hmapped := Subgroup.map_mono hsub (f := L.subtype)
  rw [Subgroup.map_subgroupOf_eq_of_le hXL,
    Subgroup.map_subgroupOf_eq_of_le hHL] at hmapped
  exact hmapped

/-- If a subgroup is disjoint from a normal `pi`-Hall subgroup, its order
has complementary prime support. -/
private theorem isPiNumber_compl_of_disjoint_normal_isHall
    {pi : Set ℕ} {L H X : Subgroup G}
    (hHL : H ≤ L) (hHnormal : (H.subgroupOf L).Normal)
    (hHHall : IsHall pi (H.subgroupOf L))
    (hXL : X ≤ L) (hdis : X ⊓ H = ⊥) :
    IsPiNumber piᶜ (Nat.card X) := by
  intro p hp hpX
  change p ∉ pi
  intro hpPi
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := X) p hpX
  let P : Subgroup G := Subgroup.zpowers (x : G)
  have hPX : P ≤ X := Subgroup.zpowers_le.mpr x.property
  have hcardP : Nat.card P = p := by
    change Nat.card (Subgroup.zpowers (x : G)) = p
    rw [Nat.card_zpowers]
    simpa using hxOrder
  have hPpi : IsPiNumber pi (Nat.card P) := by
    rw [hcardP]
    intro q hq hqp
    have hqp' : q = p :=
      (Nat.dvd_prime hp).mp hqp |>.resolve_left hq.ne_one
    simpa [hqp'] using hpPi
  have hPH : P ≤ H :=
    isPiNumber_le_normal_isHall_pType hHL hHnormal hHHall
      (hPX.trans hXL) hPpi
  have hxInf : (x : G) ∈ X ⊓ H :=
    ⟨x.property, hPH (Subgroup.mem_zpowers (x : G))⟩
  have hxOne : (x : G) = 1 := by
    have : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdis]
      exact hxInf
    simpa using this
  have horderOne : orderOf x = 1 := by
    simpa using congrArg orderOf hxOne
  exact hp.ne_one (hxOrder.symm.trans horderOne)

/-- Membership in a normal Hall subgroup can be tested from the prime
support of an element's order. -/
private theorem mem_normalHall_of_isPiNumber_order_pType
    {pi : Set ℕ} {C K : Subgroup G}
    (hKC : K ≤ C) (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall pi (K.subgroupOf C))
    {x : G} (hxC : x ∈ C)
    (hxPi : IsPiNumber pi (orderOf x)) :
    x ∈ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa [KC] using hKnormal
  let xC : C := ⟨x, hxC⟩
  let qC : C →* C ⧸ KC := QuotientGroup.mk' KC
  have hxPiC : IsPiNumber pi (orderOf xC) := by
    simpa [xC] using hxPi
  have horderPi : IsPiNumber pi (orderOf (qC xC)) :=
    hxPiC.of_dvd (orderOf_map_dvd qC xC)
  have horderCompl : IsPiNumber piᶜ (orderOf (qC xC)) := by
    apply hKHall.isPiNumber_index.of_dvd
    have hdvd : orderOf (qC xC) ∣ KC.index := by
      rw [KC.index_eq_card]
      exact orderOf_dvd_natCard (qC xC)
    simpa only [KC] using hdvd
  have horderOne : orderOf (qC xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (horderPi.coprime_compl horderCompl) dvd_rfl dvd_rfl
  have hqOne : qC xC = 1 := orderOf_eq_one_iff.mp horderOne
  have hxKC : xC ∈ KC :=
    (QuotientGroup.eq_one_iff xC).mp (by simpa [qC] using hqOne)
  exact hxKC

/-- The sigma component of an element of `Z` belongs to a normal sigma-Hall
factor of `Z`. -/
private theorem mem_normalHall_sigmaComponent
    {M K Z : Subgroup G} {x : G}
    (hKZ : K ≤ Z) (hKnormal : (K.subgroupOf Z).Normal)
    (hKHall : IsHall (sigmaPrimes M) (K.subgroupOf Z))
    (hxZ : x ∈ Z) :
    sigmaComponent M x ∈ K := by
  have hcomponentZ : sigmaComponent M x ∈ Z :=
    (Subgroup.zpowers_le.mpr hxZ)
      (primeSetComponent_spec (sigmaPrimes M) x).1
  exact mem_normalHall_of_isPiNumber_order_pType
    hKZ hKnormal hKHall hcomponentZ
      (sigmaComponent_isPiNumber M x)

/-- The complementary sigma component of an element of `Z` belongs to a
normal complementary Hall factor. -/
private theorem mem_normalHall_sigmaComplementComponent
    {M K Z : Subgroup G} {x : G}
    (hKZ : K ≤ Z) (hKnormal : (K.subgroupOf Z).Normal)
    (hKHall : IsHall (sigmaPrimes M)ᶜ (K.subgroupOf Z))
    (hxZ : x ∈ Z) :
    sigmaComplementComponent M x ∈ K := by
  have hcomponentZ : sigmaComplementComponent M x ∈ Z :=
    (Subgroup.zpowers_le.mpr hxZ) (by
      rw [sigmaComplementComponent, primeSetComplementComponent]
      exact (Subgroup.zpowers x).mul_mem
        ((Subgroup.zpowers x).inv_mem
          (primeSetComponent_spec (sigmaPrimes M) x).1)
        (Subgroup.mem_zpowers x))
  exact mem_normalHall_of_isPiNumber_order_pType
    hKZ hKnormal hKHall hcomponentZ
      (sigmaComplementComponent_isPiNumber M x)

/-- If the sigma component is trivial, an element of `Z` belongs to a
normal complementary Hall factor. -/
private theorem mem_complementary_normalHall_of_sigmaComponent_eq_one
    {M K Z : Subgroup G} {x : G}
    (hKZ : K ≤ Z) (hKnormal : (K.subgroupOf Z).Normal)
    (hKHall : IsHall (sigmaPrimes M)ᶜ (K.subgroupOf Z))
    (hxZ : x ∈ Z) (hcomponent : sigmaComponent M x = 1) :
    x ∈ K := by
  have hcomplement : sigmaComplementComponent M x = x := by
    have hfactor := sigmaComponent_mul_complement M x
    rw [hcomponent, one_mul] at hfactor
    exact hfactor
  apply mem_normalHall_of_isPiNumber_order_pType
    hKZ hKnormal hKHall hxZ
  rw [← hcomplement]
  exact sigmaComplementComponent_isPiNumber M x

/-- In the mixed part of a P-type direct product, the sigma component lies
in the centralizer partner. -/
private theorem sigmaComponent_mem_partner_of_mem_pTypeTISet
    {M K : Subgroup G}
    (hdir : IsInternalDirectProductIn K (pTypePartner M K)
      (normalizerWithin M K))
    (hKcompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K))
    (hPartnerSigma :
      IsPiNumber (sigmaPrimes M) (Nat.card (pTypePartner M K)))
    {t : G} (ht : t ∈ pTypeTISet M K) :
    sigmaComponent M t ∈ pTypePartner M K := by
  have hnorm := internalDirectProduct_normal_factors hdir
  have hHall := complementary_isHall_of_internalDirectProduct
    hdir hKcompl hPartnerSigma
  have hjoin : normalizerWithin M K = pTypeJoin M K := by
    simpa [pTypeJoin] using internalDirectProduct_eq_sup hdir
  have htNorm : t ∈ normalizerWithin M K := by
    rw [hjoin]
    exact ht.1
  exact mem_normalHall_sigmaComponent
    hdir.right_le hnorm.2 hHall.2 htNorm

/-- Membership in the mixed P-type set also makes its sigma component
nontrivial: a trivial sigma component would put the whole element in the
complementary factor `K`. -/
private theorem sigmaComponent_ne_one_of_mem_pTypeTISet
    {M K : Subgroup G}
    (hdir : IsInternalDirectProductIn K (pTypePartner M K)
      (normalizerWithin M K))
    (hKcompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K))
    (hPartnerSigma :
      IsPiNumber (sigmaPrimes M) (Nat.card (pTypePartner M K)))
    {t : G} (ht : t ∈ pTypeTISet M K) :
    sigmaComponent M t ≠ 1 := by
  intro hcomponent
  have hnorm := internalDirectProduct_normal_factors hdir
  have hHall := complementary_isHall_of_internalDirectProduct
    hdir hKcompl hPartnerSigma
  have hjoin : normalizerWithin M K = pTypeJoin M K := by
    simpa [pTypeJoin] using internalDirectProduct_eq_sup hdir
  have htNorm : t ∈ normalizerWithin M K := by
    rw [hjoin]
    exact ht.1
  have htK : t ∈ K :=
    mem_complementary_normalHall_of_sigmaComponent_eq_one
      hdir.left_le hnorm.1 hHall.1 htNorm hcomponent
  exact ht.2 (Or.inl htK)

/-- A sigma-Hall partner inside `Mstar` is exactly the intersection of
`Mstar` with the original sigma core.  The reverse containment follows by
comparing the relative index with both complementary prime supports. -/
private theorem inf_sigmaCore_partner_eq
    {M Mstar K : Subgroup G}
    (hPartnerLe : pTypePartner M K ≤ Mstar)
    (hHall : IsHall (sigmaPrimes M)
      ((pTypePartner M K).subgroupOf Mstar)) :
    sigmaCore M ⊓ Mstar = pTypePartner M K := by
  let A : Subgroup G := sigmaCore M ⊓ Mstar
  let P : Subgroup G := pTypePartner M K
  have hPA : P ≤ A :=
    le_inf (centralizerWithin_le_left _ _) hPartnerLe
  have hAMstar : A ≤ Mstar := inf_le_right
  have hApi : IsPiNumber (sigmaPrimes M) (Nat.card A) :=
    (sigmaCore_isPiNumber M).of_dvd
      (Subgroup.card_dvd_of_le inf_le_left)
  have hrelPi : IsPiNumber (sigmaPrimes M) (P.relIndex A) :=
    hApi.of_dvd (Subgroup.relIndex_dvd_card P A)
  have hrelDvd : P.relIndex A ∣ P.relIndex Mstar := by
    exact ⟨A.relIndex Mstar,
      (Subgroup.relIndex_mul_relIndex P A Mstar hPA hAMstar).symm⟩
  have hrelCompl : IsPiNumber (sigmaPrimes M)ᶜ (P.relIndex A) := by
    apply hHall.isPiNumber_index.of_dvd
    exact hrelDvd
  have hrelOne : P.relIndex A = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (hrelPi.coprime_compl hrelCompl) dvd_rfl dvd_rfl
  apply le_antisymm
  · exact Subgroup.relIndex_eq_one.mp hrelOne
  · exact hPA

/-- The five assertions grouped as clause (d) of `Ptype_embedding`. -/
structure PTypeCyclicStructure
    (M Mstar K : Subgroup G) : Prop where
  /-- `Z` is cyclic. -/
  cyclic_join : IsCyclic (pTypeJoin M K)
  /-- `M \cap M^* = Z`. -/
  inf_eq_join : M ⊓ Mstar = pTypeJoin M K
  /-- Nonidentity elements of `K` have centralizer `Z` in `M`. -/
  centralizer_left : ∀ {x : G}, x ∈ K → x ≠ 1 →
    centralizerWithin M (Subgroup.zpowers x) = pTypeJoin M K
  /-- Nonidentity elements of `K^*` have centralizer `Z` in `M^*`. -/
  centralizer_right : ∀ {y : G}, y ∈ pTypePartner M K → y ≠ 1 →
    centralizerWithin Mstar (Subgroup.zpowers y) = pTypeJoin M K
  /-- Mixed nonidentity products have full centralizer `Z`. -/
  centralizer_product : ∀ {x y : G},
    x ∈ K → x ≠ 1 →
    y ∈ pTypePartner M K → y ≠ 1 →
    Subgroup.centralizer ({x * y} : Set G) = pTypeJoin M K

/-- Bender--Glauberman Theorem 14.7, clauses (a)--(h), with a fixed witness
`Mstar`.

The source's unindexed family `'E^1(K)` is rendered by explicitly quantifying
the prime and a rank-one elementary-abelian subgroup. -/
structure PTypeEmbedding
    (M K Mstar : Subgroup G) : Prop where
  /-- The witness is itself of P type. -/
  Mstar_typeP : Mstar ∈ typePMaximalSubgroups (G := G)
  /-- The witness is not conjugate to `M`. -/
  Mstar_not_conjugate : ¬ AreConjugateSubgroups M Mstar
  /-- Clause (a): every rank-one subgroup of `K` has `Mstar` as the unique
  maximal overgroup of its centralizer. -/
  rankOne_unique : ∀ {p : ℕ}, p.Prime → ∀ {X : Subgroup G},
    RankOneLineIn p K X →
    minSimple_max_groups_of (G := G)
        (Subgroup.centralizer (X : Set G) : Set G) = {Mstar}
  /-- Ambient containment needed by both Hall statements in clause (b). -/
  Kstar_le_Mstar : pTypePartner M K ≤ Mstar
  /-- First half of clause (b). -/
  Kstar_hall_kappa :
    IsHall (kappaPrimes Mstar)
      ((pTypePartner M K).subgroupOf Mstar)
  /-- Second half of clause (b). -/
  Kstar_hall_sigma :
    IsHall (sigmaPrimes M)
      ((pTypePartner M K).subgroupOf Mstar)
  /-- First half of clause (c). -/
  doubleCentralizer :
    centralizerWithin (sigmaCore Mstar) (pTypePartner M K) = K
  /-- Second half of clause (c). -/
  kappa_eq_tau1 : kappaPrimes M = tau1Primes M
  /-- Clause (d). -/
  cyclicStructure : PTypeCyclicStructure M Mstar K
  /-- First assertion in clause (e). -/
  normalizedTI :
    IsNormalizedTI (pTypeTISet M K) (⊤ : Subgroup G) (pTypeJoin M K)
  /-- Second assertion in clause (e). -/
  outside_disjoint : ∀ {g : G}, g ∉ M →
    Disjoint (pTypeTISet M K)
      (M.map (MulAut.conj g).toMonoidHom : Set G)
  /-- The retained counting assertion in clause (e). -/
  half_lt_classSupport :
    (Nat.card G : ℚ) / 2 <
      ((classSupportWithin (⊤ : Subgroup G) (pTypeTISet M K)).ncard : ℚ)
  /-- Clause (f). -/
  typeP2_prime :
    (M ∈ typeP2MaximalSubgroups (G := G) ∧ (Nat.card K).Prime) ∨
    (Mstar ∈ typeP2MaximalSubgroups (G := G) ∧
      (Nat.card (pTypePartner M K)).Prime)
  /-- Clause (g). -/
  typeP_transitive : ∀ {H : Subgroup G},
    H ∈ typePMaximalSubgroups (G := G) →
      AreConjugateSubgroups M H ∨ AreConjugateSubgroups Mstar H
  /-- Clause (h): `M = M' : K`. -/
  derived_sdprod :
    IsInternalSemidirectProductIn
      ((_root_.commutator M).map M.subtype) K M

/-! ## Private proof machinery

The MathComp proof first constructs clauses (a)--(f) and (h), together with
the support estimate, and only then proves (g) by strong induction on the
support cardinality.  The following private record exposes exactly that
seam; unlike the public result it does not mention arbitrary P-type maximal
subgroups. -/

private structure PTypeLocalEmbedding
    (M K Mstar : Subgroup G) : Prop where
  Mstar_typeP : Mstar ∈ typePMaximalSubgroups (G := G)
  Mstar_not_conjugate : ¬ AreConjugateSubgroups M Mstar
  rankOne_unique : ∀ {p : ℕ}, p.Prime → ∀ {X : Subgroup G},
    RankOneLineIn p K X →
    minSimple_max_groups_of (G := G)
        (Subgroup.centralizer (X : Set G) : Set G) = {Mstar}
  Kstar_le_Mstar : pTypePartner M K ≤ Mstar
  Kstar_hall_kappa :
    IsHall (kappaPrimes Mstar)
      ((pTypePartner M K).subgroupOf Mstar)
  Kstar_hall_sigma :
    IsHall (sigmaPrimes M)
      ((pTypePartner M K).subgroupOf Mstar)
  doubleCentralizer :
    centralizerWithin (sigmaCore Mstar) (pTypePartner M K) = K
  kappa_eq_tau1 : kappaPrimes M = tau1Primes M
  cyclicStructure : PTypeCyclicStructure M Mstar K
  normalizedTI :
    IsNormalizedTI (pTypeTISet M K) (⊤ : Subgroup G) (pTypeJoin M K)
  outside_disjoint : ∀ {g : G}, g ∉ M →
    Disjoint (pTypeTISet M K)
      (M.map (MulAut.conj g).toMonoidHom : Set G)
  half_lt_classSupport :
    (Nat.card G : ℚ) / 2 <
      ((classSupportWithin (⊤ : Subgroup G) (pTypeTISet M K)).ncard : ℚ)
  typeP2_prime :
    (M ∈ typeP2MaximalSubgroups (G := G) ∧ (Nat.card K).Prime) ∨
    (Mstar ∈ typeP2MaximalSubgroups (G := G) ∧
      (Nat.card (pTypePartner M K)).Prime)
  /-- Local form of the final capture argument: if the two conjugacy
  supports meet, the new P-type maximal subgroup is in one of the two
  conjugacy classes already found. -/
  support_capture : ∀ {H L : Subgroup G},
    H ∈ typePMaximalSubgroups (G := G) →
    L ≤ H → IsHall (kappaPrimes H) (L.subgroupOf H) →
    ¬ Disjoint
      (classSupportWithin (⊤ : Subgroup G) (pTypeTISet M K))
      (classSupportWithin (⊤ : Subgroup G) (pTypeTISet H L)) →
    AreConjugateSubgroups M H ∨ AreConjugateSubgroups Mstar H
  derived_sdprod :
    IsInternalSemidirectProductIn
      ((_root_.commutator M).map M.subtype) K M

private def PTypeLocalEmbedding.withTransitivity
    {M K Mstar : Subgroup G}
    (h : PTypeLocalEmbedding M K Mstar)
    (htrans : ∀ {H : Subgroup G},
      H ∈ typePMaximalSubgroups (G := G) →
        AreConjugateSubgroups M H ∨ AreConjugateSubgroups Mstar H) :
    PTypeEmbedding M K Mstar where
  Mstar_typeP := h.Mstar_typeP
  Mstar_not_conjugate := h.Mstar_not_conjugate
  rankOne_unique := h.rankOne_unique
  Kstar_le_Mstar := h.Kstar_le_Mstar
  Kstar_hall_kappa := h.Kstar_hall_kappa
  Kstar_hall_sigma := h.Kstar_hall_sigma
  doubleCentralizer := h.doubleCentralizer
  kappa_eq_tau1 := h.kappa_eq_tau1
  cyclicStructure := h.cyclicStructure
  normalizedTI := h.normalizedTI
  outside_disjoint := h.outside_disjoint
  half_lt_classSupport := h.half_lt_classSupport
  typeP2_prime := h.typeP2_prime
  typeP_transitive := htrans
  derived_sdprod := h.derived_sdprod

/-- The rank-one family denoted `'E^1(K)` in the source. -/
private def rankOneSubgroups (K : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ p : ℕ, p.Prime ∧ RankOneLineIn p K X}

private theorem exists_rankOneLineIn_zpowers_of_mem
    {K : Subgroup G} {x : G} (hxK : x ∈ K) (hx1 : x ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ ∃ X : Subgroup G,
      RankOneLineIn p K X ∧ X ≤ Subgroup.zpowers x := by
  let C : Subgroup G := Subgroup.zpowers x
  have hCne : C ≠ ⊥ := by
    intro hbot
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_zpowers x
    exact hx1 (by simpa using hxbot)
  obtain ⟨p, hp, hpC⟩ := Nat.exists_prime_and_dvd
    (C.one_lt_card_iff_ne_bot.mpr hCne).ne'
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hyOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := C) p hpC
  let X : Subgroup G := Subgroup.zpowers (y : G)
  have hXC : X ≤ C := Subgroup.zpowers_le.mpr y.property
  have hXK : X ≤ K :=
    hXC.trans (Subgroup.zpowers_le.mpr hxK)
  have hcardX : Nat.card X = p := by
    change Nat.card (Subgroup.zpowers (y : G)) = p
    rw [Nat.card_zpowers]
    simpa using hyOrder
  exact ⟨p, hp, X,
    ⟨hXK, isElementaryAbelianOfRank_one_of_card_eq_prime hcardX⟩,
    hXC⟩

private theorem exists_rankOneLineIn_inf_of_ne_bot
    {A B : Subgroup G} (hAB : A ⊓ B ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ ∃ X : Subgroup G,
      RankOneLineIn p (A ⊓ B) X := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAB
  obtain ⟨p, hp, X, hX, -⟩ :=
    exists_rankOneLineIn_zpowers_of_mem x.property (by
      intro hx
      exact hx1 (Subtype.ext hx))
  exact ⟨p, hp, X, hX⟩

private theorem exists_maximal_normalizer_for_line
    {p : ℕ} {K X : Subgroup G} (hp : p.Prime)
    (hX : RankOneLineIn p K X) :
    ∃ M : Subgroup G,
      M ∈ minSimple_max_groups_of (G := G)
        (Subgroup.normalizer (X : Set G) : Set G) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hXproper : X < ⊤ :=
    mFT_pgroup_proper X hX.2.isPGroup
  obtain ⟨M, hM, hNM⟩ :=
    mmax_exists (Subgroup.normalizer (X : Set G))
      (mFT_norm_proper X hX.2.ne_bot hXproper)
  exact ⟨M, hM, hNM⟩

/-- The source family `MNX`: maximal overgroups of normalizers of lines in
`K`. -/
private def lineNormalizerMaximals (K : Subgroup G) : Set (Subgroup G) :=
  ⋃ X ∈ rankOneSubgroups K,
    minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (X : Set G) : Set G)

private theorem lineNormalizerMaximals_nonempty
    {K : Subgroup G} (hK : K ≠ ⊥) :
    (lineNormalizerMaximals K).Nonempty := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK
  obtain ⟨p, hp, X, hX, -⟩ :=
    exists_rankOneLineIn_zpowers_of_mem x.property (by
      intro hx
      exact hx1 (Subtype.ext hx))
  obtain ⟨M, hmaxNX⟩ := exists_maximal_normalizer_for_line hp hX
  refine ⟨M, ?_⟩
  simp only [lineNormalizerMaximals, Set.mem_iUnion]
  exact ⟨X, ⟨p, hp, hX⟩, hmaxNX⟩

/-- Data supplied by the symmetric normalizer argument at the start of the
proof of Theorem 14.7. -/
private structure PTypeSymmetricNormalizer
    (M K X Mi : Subgroup G) : Type u where
  join_le : pTypeJoin M K ≤ Mi
  not_conjugate : ¬ AreConjugateSubgroups M Mi
  Ki : Subgroup G
  Mi_typeP : Mi ∈ typePMaximalSubgroups (G := G)
  Ki_le_Mi : Ki ≤ Mi
  Ki_hall : IsHall (kappaPrimes Mi) (Ki.subgroupOf Mi)
  partner_le_Ki : pTypePartner M K ≤ Ki
  partner_lines_normalized : ∀ {p : ℕ}, p.Prime →
    ∀ {Xs : Subgroup G}, RankOneLineIn p (pTypePartner M K) Xs →
      pTypeJoin M K ≤ normalizerWithin Mi Xs

/-- The preliminary symmetry argument on p. 112, lines 1--7.  This is the
Lean analogue of the local assertion `Pmax_sym` in the MathComp proof. -/
private noncomputable def pType_symmetric_normalizer
    {M K X Mi : Subgroup G}
    (hM : M ∈ typePMaximalSubgroups (G := G))
    (hKM : K ≤ M)
    (hK : IsHall (kappaPrimes M) (K.subgroupOf M))
    {p : ℕ} (hp : p.Prime) (hX : RankOneLineIn p K X)
    (hMi : Mi ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (X : Set G) : Set G)) :
    PTypeSymmetricNormalizer M K X Mi := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let Ks : Subgroup G := pTypePartner M K
  let Z : Subgroup G := pTypeJoin M K
  have hmaxM : M ∈ minSimple_max_groups (G := G) := hM.1
  have hmaxMi : Mi ∈ minSimple_max_groups (G := G) := hMi.1
  have hs := Ptype_structure hM hKM hK
  have hline := hs.rankOne_normalizer hX
  have hZX : Z = normalizerWithin M X := by
    calc
      Z = K ⊔ Ks := by rfl
      _ = normalizerWithin M K :=
        (internalDirectProduct_eq_sup hs.normalizer_direct).symm
      _ = normalizerWithin M X := hline.1.symm
  have hZMi : Z ≤ Mi := by
    rw [hZX]
    exact inf_le_right.trans hMi.2
  have hXsigmaMi : X ≤ sigmaCore Mi := hline.2 hMi
  have hnotconj : ¬ AreConjugateSubgroups M Mi := by
    rintro ⟨g, rfl⟩
    have hsig : sigmaPrimes
          (M.map (MulAut.conj g).toMonoidHom) = sigmaPrimes M :=
      sigmaPrimes_conj M g
    have hkappa : kappaPrimes
          (M.map (MulAut.conj g).toMonoidHom) = kappaPrimes M :=
      Set.Subset.antisymm (fun q hq ↦ (kappaJ M g).mp hq)
        (fun q hq ↦ (kappaJ M g).mpr hq)
    have hXsigma : IsPiNumber (sigmaPrimes M) (Nat.card X) := by
      have htmp :=
        (sigmaCore_isPiNumber
          (M.map (MulAut.conj g).toMonoidHom)).of_dvd
          (Subgroup.card_dvd_of_le hXsigmaMi)
      rw [hsig] at htmp
      exact htmp
    have hXkappa : IsPiNumber (kappaPrimes M) (Nat.card X) := by
      have hKcard : IsPiNumber (kappaPrimes M) (Nat.card K) := by
        simpa only [MathlibSupport.natCard_subgroupOf_eq hKM] using
          hK.isPiNumber_card
      exact hKcard.of_dvd (Subgroup.card_dvd_of_le hX.1)
    have hcop := hXsigma.coprime_compl (hXkappa.mono (kappa_sigma' M))
    have hcardX : Nat.card X = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
    have hcardPrime : Nat.card X = p := by simpa using hX.2.card_eq
    exact hp.ne_one (hcardPrime ▸ hcardX)
  have hKsMi : Ks ≤ Mi := by
    exact (show Ks ≤ Z from le_sup_right).trans hZMi
  have hKsKappa : IsPiNumber (kappaPrimes Mi) (Nat.card Ks) := by
    intro q hq hqKs
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨xs, hoxs⟩ :=
      exists_prime_orderOf_dvd_card' (G := Ks) q hqKs
    have hxsKs : (xs : G) ∈ Ks := xs.property
    let Xs : Subgroup G := Subgroup.zpowers (xs : G)
    have hXsKs : Xs ≤ Ks := Subgroup.zpowers_le.mpr hxsKs
    have hcardXs : Nat.card Xs = q := by
      rw [Nat.card_zpowers]
      simpa using hoxs
    have hXs : RankOneLineIn q Ks Xs :=
      ⟨hXsKs, isElementaryAbelianOfRank_one_of_card_eq_prime hcardXs⟩
    have hqNotSigmaMi : q ∉ sigmaPrimes Mi := by
      intro hqSigmaMi
      have hqSigmaM : q ∈ sigmaPrimes M :=
        (sigmaCore_isPiNumber M) hq
          (hqKs.trans (Subgroup.card_dvd_of_le
            (show Ks ≤ sigmaCore M from centralizerWithin_le_left _ _)))
      exact (Set.disjoint_left.mp
        (sigma_partition hmaxM hmaxMi (fun g heq ↦
          hnotconj ⟨g, heq⟩))) hqSigmaM hqSigmaMi
    have huniqM := hs.Kstar_line_unique hXs
    obtain ⟨x, hxne⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hX.2.ne_bot
    have hxX : (x : G) ∈ X := x.property
    have hxSigmaMi : (x : G) ∈ sigmaCore Mi := hXsigmaMi hxX
    have hxsCentralizes :
        (xs : G) ∈ centralizerWithin Mi (Subgroup.zpowers (x : G)) := by
      refine ⟨hKsMi hxsKs, ?_⟩
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hs.normalizer_direct.commute
        ⟨(x : G), hX.1 hxX⟩ ⟨xs, hxsKs⟩).zpow_left n |>.eq
    have hxsNe : (xs : G) ≠ 1 := by
      intro hxs
      have : orderOf xs = 1 := by simpa using congrArg orderOf hxs
      exact hq.ne_one (hoxs.symm.trans this)
    have hxsSigmaCompl :
        IsPiNumber (sigmaPrimes Mi)ᶜ (orderOf (xs : G)) := by
      intro r hr hrOrder
      have hrq : r = q := by
        have hoxsG : orderOf (xs : G) = q := by simpa using hoxs
        rw [hoxsG] at hrOrder
        exact (Nat.dvd_prime hq).mp hrOrder |>.resolve_left hr.ne_one
      simpa [hrq] using hqNotSigmaMi
    have hxneG : (x : G) ≠ 1 := by
      intro hx
      exact hxne (Subtype.ext hx)
    rcases pi_of_cent_sigma hmaxMi hxSigmaMi hxneG
        hxsCentralizes hxsNe hxsSigmaCompl with hqKappa | hregular
    · have hoxsG : orderOf (xs : G) = q := by simpa using hoxs
      exact hqKappa.1 hq (by rw [hoxsG])
    · have hMiUnique := hregular.2.2
      have hMiEqM : Mi = M := by
        apply Set.singleton_injective
        exact hMiUnique.symm.trans (by simpa [Xs] using huniqM)
      exfalso
      apply hnotconj
      rw [hMiEqM]
      exact areConjugateSubgroups_refl M
  have hKiExists :=
    MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
      hKsMi (mmax_sol hmaxMi)
      (kappaPrimes Mi) hKsKappa
  let Ki : Subgroup G := Classical.choose hKiExists
  have hKiSpec := Classical.choose_spec hKiExists
  have hKsKi : Ks ≤ Ki := hKiSpec.1
  have hKiMi : Ki ≤ Mi := hKiSpec.2.1
  have hKiHall : IsHall (kappaPrimes Mi) (Ki.subgroupOf Mi) :=
    hKiSpec.2.2
  have hMiP : Mi ∈ typePMaximalSubgroups (G := G) := by
    apply (PtypeP hmaxMi).2
    have hKsCard : 1 < Nat.card Ks :=
      Ks.one_lt_card_iff_ne_bot.mpr hs.Kstar_ne_bot
    obtain ⟨q, hq, hqKs⟩ := Nat.exists_prime_and_dvd hKsCard.ne'
    exact ⟨q, hKsKappa hq hqKs⟩
  have hKiStruct := Ptype_structure hMiP hKiMi hKiHall
  refine
    { join_le := hZMi
      not_conjugate := hnotconj
      Ki := Ki
      Mi_typeP := hMiP
      Ki_le_Mi := hKiMi
      Ki_hall := hKiHall
      partner_le_Ki := hKsKi
      partner_lines_normalized := ?_ }
  intro r hr Xs hXs
  letI : Fact r.Prime := ⟨hr⟩
  have hlineXs := hKiStruct.rankOne_normalizer
    (p := r) (X := Xs) ⟨hXs.1.trans hKsKi, hXs.2⟩
  refine sup_le ?_ ?_
  · refine le_inf (le_sup_left.trans hZMi) ?_
    exact (show K ≤ Subgroup.centralizer (Xs : Set G) from by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro xs hxs
      exact (hs.normalizer_direct.commute
        ⟨k, hk⟩ ⟨xs, hXs.1 hxs⟩).eq.symm).trans
      (Subgroup.centralizer_le_normalizer (Xs : Set G))
  · rw [hlineXs.1]
    exact le_inf (le_sup_right.trans hZMi)
      (hKsKi.trans Subgroup.le_normalizer)

set_option maxHeartbeats 4000000 in
/-- Clauses (a)--(f) and (h), including the support estimate.  This is the
part of the source proof preceding the final induction which establishes
clause (g). -/
private theorem pType_local_embedding
    {M K : Subgroup G}
    (hM : M ∈ typePMaximalSubgroups (G := G))
    (hKM : K ≤ M)
    (hK : IsHall (kappaPrimes M) (K.subgroupOf M)) :
    ∃ Mstar : Subgroup G, PTypeLocalEmbedding M K Mstar := by
  classical
  let Ks : Subgroup G := pTypePartner M K
  let Z : Subgroup G := pTypeJoin M K
  let MNX : Set (Subgroup G) := lineNormalizerMaximals K
  let MX : Set (Subgroup G) := {M} ∪ MNX
  have hmaxM : M ∈ minSimple_max_groups (G := G) := hM.1
  have hs := Ptype_structure hM hKM hK
  have hKne : K ≠ ⊥ := by
    intro hbot
    exact hM.2 ((trivg_kappa hmaxM hKM hK).mp hbot)
  have hKsne : Ks ≠ ⊥ := by
    simpa [Ks, pTypePartner] using hs.Kstar_ne_bot

  /- `isKi`, `K_`, and `Ks_` from the source.  Outside `MNX`, the selected
  subgroup defaults to the original `K`; this makes `KAt M = K`
  definitionally recoverable after ruling out a second Hall subgroup which
  contains `Ks`. -/
  let IsKi (Mi Ki : Subgroup G) : Prop :=
    Mi ∈ typePMaximalSubgroups (G := G) ∧
      Ki ≤ Mi ∧ IsHall (kappaPrimes Mi) (Ki.subgroupOf Mi) ∧
      Ks ≤ Ki
  let KAt (Mi : Subgroup G) : Subgroup G :=
    if h : ∃ Ki : Subgroup G, IsKi Mi Ki then Classical.choose h else K
  let KsAt (Mi : Subgroup G) : Subgroup G :=
    centralizerWithin (sigmaCore Mi) (KAt Mi)

  have hMnotMNX : M ∉ MNX := by
    intro hMMNX
    change M ∈ lineNormalizerMaximals K at hMMNX
    simp only [lineNormalizerMaximals, Set.mem_iUnion] at hMMNX
    rcases hMMNX with ⟨X, hXline, hMX⟩
    change ∃ p : ℕ, p.Prime ∧ RankOneLineIn p K X at hXline
    obtain ⟨p, hp, hX⟩ := hXline
    have hsym := pType_symmetric_normalizer hM hKM hK hp hX hMX
    exact hsym.not_conjugate (areConjugateSubgroups_refl M)
  have hKAtM : KAt M = K := by
    simp only [KAt]
    split_ifs with hex
    · obtain ⟨Ki, hKi⟩ := hex
      have hKsKi : Ks ≤ Ki := hKi.2.2.2
      have hKiKappa : IsPiNumber (kappaPrimes M) (Nat.card Ki) := by
        simpa only [MathlibSupport.natCard_subgroupOf_eq hKi.2.1] using
          hKi.2.2.1.isPiNumber_card
      have hKsSigma : IsPiNumber (sigmaPrimes M) (Nat.card Ks) :=
        (sigmaCore_isPiNumber M).of_dvd
          (Subgroup.card_dvd_of_le
            (show Ks ≤ sigmaCore M from centralizerWithin_le_left _ _))
      have hKsKappa : IsPiNumber (kappaPrimes M) (Nat.card Ks) :=
        hKiKappa.of_dvd (Subgroup.card_dvd_of_le hKsKi)
      have hcop :=
        hKsSigma.coprime_compl (hKsKappa.mono (kappa_sigma' M))
      have hKsCard : Nat.card Ks = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
      exact (hKsne (Subgroup.card_eq_one.mp hKsCard)).elim
    · rfl
  have hKsAtM : KsAt M = Ks := by
    simp [KsAt, Ks, pTypePartner, hKAtM]
  have hNormM : normalizerWithin M K = Z := by
    simpa [Z, Ks, pTypeJoin, pTypePartner] using
      internalDirectProduct_eq_sup hs.normalizer_direct

  have hMNXspec : ∀ {Mi : Subgroup G}, Mi ∈ MNX → IsKi Mi (KAt Mi) := by
    intro Mi hMi
    change Mi ∈ lineNormalizerMaximals K at hMi
    simp only [lineNormalizerMaximals, Set.mem_iUnion] at hMi
    rcases hMi with ⟨X, ⟨p, hp, hX⟩, hMi⟩
    have hsym := pType_symmetric_normalizer hM hKM hK hp hX hMi
    have hex : ∃ Ki : Subgroup G, IsKi Mi Ki :=
      ⟨hsym.Ki, hsym.Mi_typeP, hsym.Ki_le_Mi,
        hsym.Ki_hall, hsym.partner_le_Ki⟩
    simp only [KAt, dif_pos hex]
    exact Classical.choose_spec hex
  have hMXspec : ∀ {Mi : Subgroup G}, Mi ∈ MX →
      Mi ∈ typePMaximalSubgroups (G := G) ∧
      KAt Mi ≤ Mi ∧
      IsHall (kappaPrimes Mi) ((KAt Mi).subgroupOf Mi) := by
    intro Mi hMi
    rcases hMi with (rfl | hMi)
    · simpa [hKAtM] using ⟨hM, hKM, hK⟩
    · have hspec := hMNXspec hMi
      exact ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩
  have hKsAtNe : ∀ {Mi : Subgroup G}, Mi ∈ MX → KsAt Mi ≠ ⊥ := by
    intro Mi hMi
    have hMiStruct := Ptype_structure
      (hMXspec hMi).1 (hMXspec hMi).2.1 (hMXspec hMi).2.2
    simpa [KsAt, pTypeCentralizer] using hMiStruct.Kstar_ne_bot

  /- Every member of `MX` supplies a direct decomposition of the same
  subgroup `Z`; these are `defZX`, `hallK_Z`, and `nsK_Z` in the source. -/
  have hcommonZ : ∀ {Mi : Subgroup G}, Mi ∈ MX →
      KAt Mi ⊔ KsAt Mi = Z := by
    intro Mi hMi
    change Mi ∈ ({M} ∪ MNX : Set (Subgroup G)) at hMi
    rcases hMi with hMiM | hMi
    · have hMiEq : Mi = M := by simpa using hMiM
      subst Mi
      rw [hKAtM, hKsAtM]
      change K ⊔ pTypePartner M K = pTypeJoin M K
      rfl
    · change Mi ∈ lineNormalizerMaximals K at hMi
      simp only [lineNormalizerMaximals, Set.mem_iUnion] at hMi
      rcases hMi with ⟨X, ⟨p, hp, hX⟩, hmaxNX⟩
      letI : Fact p.Prime := ⟨hp⟩
      have hsym := pType_symmetric_normalizer hM hKM hK hp hX hmaxNX
      have hMiMNX : Mi ∈ MNX := by
        change Mi ∈ lineNormalizerMaximals K
        simp only [lineNormalizerMaximals, Set.mem_iUnion]
        exact ⟨X, ⟨p, hp, hX⟩, hmaxNX⟩
      have hMiData := hMNXspec hMiMNX
      have hMiStruct := Ptype_structure hMiData.1 hMiData.2.1 hMiData.2.2.1
      have hKiCompl :
          IsPiNumber (sigmaPrimes Mi)ᶜ (Nat.card (KAt Mi)) := by
        have hcard : IsPiNumber (kappaPrimes Mi) (Nat.card (KAt Mi)) := by
          simpa only [MathlibSupport.natCard_subgroupOf_eq hMiData.2.1] using
            hMiData.2.2.1.isPiNumber_card
        exact hcard.mono (kappa_sigma' Mi)
      have hKsiSigma :
          IsPiNumber (sigmaPrimes Mi) (Nat.card (KsAt Mi)) :=
        (sigmaCore_isPiNumber Mi).of_dvd
          (Subgroup.card_dvd_of_le (centralizerWithin_le_left _ _))
      have hHallNi := complementary_isHall_of_internalDirectProduct
        hMiStruct.normalizer_direct hKiCompl hKsiSigma
      have hnormalNi :=
        internalDirectProduct_normal_factors hMiStruct.normalizer_direct
      have hlineInKs : ∃ q : ℕ, q.Prime ∧
          ∃ Xs : Subgroup G, RankOneLineIn q Ks Xs := by
        obtain ⟨q, hq, hqKs⟩ := Nat.exists_prime_and_dvd
          (Ks.one_lt_card_iff_ne_bot.mpr hKsne).ne'
        letI : Fact q.Prime := ⟨hq⟩
        obtain ⟨xs, hoxs⟩ :=
          exists_prime_orderOf_dvd_card' (G := Ks) q hqKs
        let Xs : Subgroup G := Subgroup.zpowers (xs : G)
        refine ⟨q, hq, Xs, Subgroup.zpowers_le.mpr xs.property, ?_⟩
        apply isElementaryAbelianOfRank_one_of_card_eq_prime
        simpa [Xs, Nat.card_zpowers] using hoxs
      obtain ⟨q, hq, Xs, hXs⟩ := hlineInKs
      letI : Fact q.Prime := ⟨hq⟩
      have hXsKi : RankOneLineIn q (KAt Mi) Xs :=
        ⟨hXs.1.trans hMiData.2.2.2, hXs.2⟩
      apply le_antisymm
      ·
        have hlineXs := hMiStruct.rankOne_normalizer hXsKi
        have hZNormXs := hsym.partner_lines_normalized hq hXs
        have hXNormKi : X ≤ normalizerWithin Mi (KAt Mi) := by
          rw [← hlineXs.1]
          exact (hX.1.trans (show K ≤ Z from le_sup_left)).trans hZNormXs
        have hXsigma : IsPiNumber (sigmaPrimes Mi) (Nat.card X) :=
          (sigmaCore_isPiNumber Mi).of_dvd
            (Subgroup.card_dvd_of_le ((hs.rankOne_normalizer hX).2 hmaxNX))
        have hXKsAt : X ≤ KsAt Mi :=
          isPiNumber_le_normal_isHall_pType
            hMiStruct.normalizer_direct.right_le hnormalNi.2 hHallNi.2
            hXNormKi hXsigma
        have huniqXs := hs.Kstar_line_unique hXs
        have hnormXsProper : Subgroup.normalizer (Xs : Set G) < ⊤ :=
          mFT_norm_proper Xs hXs.2.ne_bot
            (mFT_pgroup_proper Xs hXs.2.isPGroup)
        have hnormXsM : Subgroup.normalizer (Xs : Set G) ≤ M :=
          sub_uniq_mmax huniqXs
            (Subgroup.centralizer_le_normalizer (Xs : Set G)) hnormXsProper
        have hMmaxNXs : M ∈ minSimple_max_groups_of (G := G)
            (Subgroup.normalizer (Xs : Set G) : Set G) :=
          ⟨hmaxM, hnormXsM⟩
        have hsymRev := pType_symmetric_normalizer
          (M := Mi) (K := KAt Mi) (X := Xs) (Mi := M)
          hMiData.1 hMiData.2.1 hMiData.2.2.1 hq hXsKi hMmaxNXs
        have hXpartnerRev :
            RankOneLineIn p (pTypePartner Mi (KAt Mi)) X := by
          simpa only [KsAt, pTypePartner] using
            (show RankOneLineIn p (KsAt Mi) X from ⟨hXKsAt, hX.2⟩)
        have hjoinLeZ :=
          (hsymRev.partner_lines_normalized hp hXpartnerRev).trans_eq
            ((hs.rankOne_normalizer hX).1.trans hNormM)
        simpa only [pTypeJoin, KsAt, pTypePartner] using hjoinLeZ
      ·
        exact (hsym.partner_lines_normalized hq hXs).trans_eq
          ((hMiStruct.rankOne_normalizer hXsKi).1.trans
            (internalDirectProduct_eq_sup hMiStruct.normalizer_direct))
  have hdirectZ : ∀ {Mi : Subgroup G}, Mi ∈ MX →
      IsInternalDirectProductIn (KAt Mi) (KsAt Mi) Z := by
    intro Mi hMi
    have hMiStruct := Ptype_structure
      (hMXspec hMi).1 (hMXspec hMi).2.1 (hMXspec hMi).2.2
    have hnormEq : normalizerWithin Mi (KAt Mi) = Z := by
      calc
        normalizerWithin Mi (KAt Mi) = KAt Mi ⊔ KsAt Mi := by
          simpa only [KsAt] using
            internalDirectProduct_eq_sup hMiStruct.normalizer_direct
        _ = Z := hcommonZ hMi
    simpa only [KsAt, hnormEq] using hMiStruct.normalizer_direct
  have hHallZ : ∀ {Mi : Subgroup G}, Mi ∈ MX →
      IsHall (sigmaPrimes Mi)ᶜ ((KAt Mi).subgroupOf Z) ∧
      IsHall (sigmaPrimes Mi) ((KsAt Mi).subgroupOf Z) := by
    intro Mi hMi
    have hdirect := hdirectZ hMi
    have hKiCompl : IsPiNumber (sigmaPrimes Mi)ᶜ (Nat.card (KAt Mi)) := by
      have hcard : IsPiNumber (kappaPrimes Mi) (Nat.card (KAt Mi)) := by
        simpa only [MathlibSupport.natCard_subgroupOf_eq
          (hMXspec hMi).2.1] using
          (hMXspec hMi).2.2.isPiNumber_card
      exact hcard.mono (kappa_sigma' Mi)
    have hKsiSigma : IsPiNumber (sigmaPrimes Mi) (Nat.card (KsAt Mi)) :=
      (sigmaCore_isPiNumber Mi).of_dvd
        (Subgroup.card_dvd_of_le (centralizerWithin_le_left _ _))
    exact complementary_isHall_of_internalDirectProduct
      hdirect hKiCompl hKsiSigma
  have hnormalZ : ∀ {Mi : Subgroup G}, Mi ∈ MX →
      ((KAt Mi).subgroupOf Z).Normal ∧
      ((KsAt Mi).subgroupOf Z).Normal := by
    intro Mi hMi
    exact internalDirectProduct_normal_factors (hdirectZ hMi)

  /- Distinct centralizer factors are disjoint, and each lies in the
  opposite Hall factor. -/
  have hKsDisjoint : ∀ {Mi Mj : Subgroup G}, Mi ∈ MX → Mj ∈ MX →
      Mi ≠ Mj → KsAt Mi ⊓ KsAt Mj = ⊥ := by
    intro Mi Mj hMi hMj hne
    by_contra hmeet
    obtain ⟨q, hq, X, hX⟩ :=
      exists_rankOneLineIn_inf_of_ne_bot hmeet
    letI : Fact q.Prime := ⟨hq⟩
    have hXMi : RankOneLineIn q (KsAt Mi) X :=
      ⟨hX.1.trans inf_le_left, hX.2⟩
    have hXMj : RankOneLineIn q (KsAt Mj) X :=
      ⟨hX.1.trans inf_le_right, hX.2⟩
    have hMiStruct := Ptype_structure
      (hMXspec hMi).1 (hMXspec hMi).2.1 (hMXspec hMi).2.2
    have hMjStruct := Ptype_structure
      (hMXspec hMj).1 (hMXspec hMj).2.1 (hMXspec hMj).2.2
    have hi := hMiStruct.Kstar_line_unique hXMi
    have hj := hMjStruct.Kstar_line_unique hXMj
    exact hne (Set.singleton_injective (hi.symm.trans hj))
  have hcross : ∀ {Mi Mj : Subgroup G}, Mi ∈ MX → Mj ∈ MX →
      Mj ≠ Mi → KsAt Mj ≤ KAt Mi := by
    intro Mi Mj hMi hMj hne
    have hKsJCompl :
        IsPiNumber (sigmaPrimes Mi)ᶜ (Nat.card (KsAt Mj)) :=
      isPiNumber_compl_of_disjoint_normal_isHall
        (hdirectZ hMi).right_le (hnormalZ hMi).2 (hHallZ hMi).2
        (hdirectZ hMj).right_le (hKsDisjoint hMj hMi hne)
    exact isPiNumber_le_normal_isHall_pType
      (hdirectZ hMi).left_le (hnormalZ hMi).1 (hHallZ hMi).1
      (hdirectZ hMj).right_le hKsJCompl

  /- `T` is first defined as `Z^#` minus the cover by the nonidentity
  centralizer factors, exactly as in the source.  The following equality is
  `defT`: it is also the union of the mixed nonidentity products. -/
  let T : Set G :=
    subgroupNonidentity Z \
      ⋃ Mi ∈ MX, subgroupNonidentity (KsAt Mi)
  have hT_mixed :
      (⋃ Mi ∈ MX,
          subgroupNonidentity (KsAt Mi) *
            subgroupNonidentity (KAt Mi)) = T := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iUnion] at hx
      rcases hx with ⟨Mi, hMi, hprod⟩
      rw [Set.mem_mul] at hprod
      rcases hprod with ⟨y, hy, y', hy', rfl⟩
      rcases mem_subgroupNonidentity.mp hy with ⟨hyKs, hy1⟩
      rcases mem_subgroupNonidentity.mp hy' with ⟨hyK, hy'1⟩
      have hdir := hdirectZ hMi
      refine ⟨mem_subgroupNonidentity.mpr
          ⟨Z.mul_mem (hdir.right_le hyKs) (hdir.left_le hyK), ?_⟩, ?_⟩
      · intro hprod
        have hyInK : y ∈ KAt Mi := by
          have hyEq : y = y'⁻¹ := mul_eq_one_iff_eq_inv.mp hprod
          rw [hyEq]
          exact (KAt Mi).inv_mem hyK
        have hyInf : y ∈ KAt Mi ⊓ KsAt Mi := ⟨hyInK, hyKs⟩
        rw [disjoint_iff.mp (internalDirectProduct_disjoint_ambient hdir)] at hyInf
        exact hy1 (by simpa using hyInf)
      · intro hcover
        simp only [Set.mem_iUnion] at hcover
        rcases hcover with ⟨Mj, hMj, hprodJ⟩
        rcases mem_subgroupNonidentity.mp hprodJ with ⟨hprodJ, -⟩
        by_cases hji : Mj = Mi
        · subst Mj
          have hy'Ks : y' ∈ KsAt Mi := by
            simpa [mul_assoc] using
              (KsAt Mi).mul_mem ((KsAt Mi).inv_mem hyKs) hprodJ
          have hy'Inf : y' ∈ KAt Mi ⊓ KsAt Mi := ⟨hyK, hy'Ks⟩
          rw [disjoint_iff.mp (internalDirectProduct_disjoint_ambient hdir)] at hy'Inf
          exact hy'1 (by simpa using hy'Inf)
        · have hprodK : y * y' ∈ KAt Mi :=
            hcross hMi hMj hji hprodJ
          have hyK' : y ∈ KAt Mi := by
            simpa [mul_assoc] using
              (KAt Mi).mul_mem hprodK ((KAt Mi).inv_mem hyK)
          have hyInf : y ∈ KAt Mi ⊓ KsAt Mi := ⟨hyK', hyKs⟩
          rw [disjoint_iff.mp (internalDirectProduct_disjoint_ambient hdir)] at hyInf
          exact hy1 (by simpa using hyInf)
    · rintro ⟨hxZsharp, hxnone⟩
      rcases mem_subgroupNonidentity.mp hxZsharp with ⟨hxZ, hx1⟩
      have hfind : ∃ Mi : Subgroup G, Mi ∈ MX ∧ x ∉ KAt Mi := by
        by_cases hxK : x ∈ K
        · obtain ⟨p, hp, X, hX, hXcycle⟩ :=
            exists_rankOneLineIn_zpowers_of_mem hxK hx1
          letI : Fact p.Prime := ⟨hp⟩
          obtain ⟨Mi, hmaxNX⟩ :=
            exists_maximal_normalizer_for_line hp hX
          have hMiMNX : Mi ∈ MNX := by
            change Mi ∈ lineNormalizerMaximals K
            simp only [lineNormalizerMaximals, Set.mem_iUnion]
            exact ⟨X, ⟨p, hp, hX⟩, hmaxNX⟩
          have hMiMX : Mi ∈ MX := Or.inr hMiMNX
          refine ⟨Mi, hMiMX, ?_⟩
          intro hxKi
          have hXKi : X ≤ KAt Mi :=
            hXcycle.trans (Subgroup.zpowers_le.mpr hxKi)
          have hXsigma : X ≤ sigmaCore Mi :=
            (hs.rankOne_normalizer hX).2 hmaxNX
          have hpDiv : p ∣ Nat.card X := by
            have hcardXp : Nat.card X = p := by simpa using hX.2.card_eq
            rw [hcardXp]
          have hpKappa : p ∈ kappaPrimes Mi :=
            (by
              have hcard : IsPiNumber (kappaPrimes Mi)
                  (Nat.card (KAt Mi)) := by
                simpa only [MathlibSupport.natCard_subgroupOf_eq
                  (hMXspec hMiMX).2.1] using
                  (hMXspec hMiMX).2.2.isPiNumber_card
              exact hcard hp
                (hpDiv.trans (Subgroup.card_dvd_of_le hXKi)))
          have hpSigma : p ∈ sigmaPrimes Mi :=
            (sigmaCore_isPiNumber Mi) hp
              (hpDiv.trans (Subgroup.card_dvd_of_le hXsigma))
          exact ((kappa_sigma' Mi) hpKappa) hpSigma
        · exact ⟨M, by simp [MX], by simpa [hKAtM] using hxK⟩
      obtain ⟨Mi, hMi, hxKi⟩ := hfind
      let hdir := hdirectZ hMi
      let w : Z := ⟨x, hxZ⟩
      let ki : KAt Mi := hdir.leftProjection w
      let ksi : KsAt Mi := hdir.rightProjection w
      have hdecomp : (ki : G) * (ksi : G) = x := by
        exact congrArg Subtype.val (hdir.mulEquiv_projections w)
      have hki1 : (ki : G) ≠ 1 := by
        intro hki
        have hxKsi : x ∈ KsAt Mi := by
          rw [← hdecomp, hki, one_mul]
          exact ksi.property
        apply hxnone
        simp only [Set.mem_iUnion]
        exact ⟨Mi, hMi, mem_subgroupNonidentity.mpr ⟨hxKsi, hx1⟩⟩
      have hksi1 : (ksi : G) ≠ 1 := by
        intro hksi
        apply hxKi
        rw [← hdecomp, hksi, mul_one]
        exact ki.property
      simp only [Set.mem_iUnion]
      refine ⟨Mi, hMi, ?_⟩
      rw [Set.mem_mul]
      refine ⟨(ksi : G),
        mem_subgroupNonidentity.mpr ⟨ksi.property, hksi1⟩,
        (ki : G), mem_subgroupNonidentity.mpr ⟨ki.property, hki1⟩, ?_⟩
      exact (hdir.commute ki ksi).eq.symm.trans hdecomp
  have hTfactor : ∀ {t : G}, t ∈ T →
      ∃ Mi : Subgroup G, Mi ∈ MX ∧
        ∃ y : G, y ∈ subgroupNonidentity (KsAt Mi) ∧
          ∃ y' : G, y' ∈ subgroupNonidentity (KAt Mi) ∧
            t = y * y' := by
    intro t ht
    rw [← hT_mixed] at ht
    simp only [Set.mem_iUnion] at ht
    rcases ht with ⟨Mi, hMi, hprod⟩
    rw [Set.mem_mul] at hprod
    rcases hprod with ⟨y, hy, y', hy', hyy'⟩
    exact ⟨Mi, hMi, y, hy, y', hy', hyy'.symm⟩
  have hTnonempty : T.Nonempty := by
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKsne
    have hxK : (x : G) ∈ K := x.property
    have hyKs : (y : G) ∈ Ks := y.property
    have hx1G : (x : G) ≠ 1 := by
      intro hx
      exact hx1 (Subtype.ext hx)
    have hy1G : (y : G) ≠ 1 := by
      intro hy
      exact hy1 (Subtype.ext hy)
    refine ⟨(x : G) * (y : G), ?_⟩
    rw [← hT_mixed]
    simp only [Set.mem_iUnion]
    refine ⟨M, by simp [MX], ?_⟩
    rw [Set.mem_mul]
    refine ⟨(y : G),
      mem_subgroupNonidentity.mpr ⟨hKsAtM.symm ▸ hyKs, hy1G⟩,
      (x : G), mem_subgroupNonidentity.mpr ⟨hKAtM.symm ▸ hxK, hx1G⟩, ?_⟩
    exact (hs.normalizer_direct.commute ⟨x, hxK⟩ ⟨y, hyKs⟩).eq.symm

  have hT_disjoint_sigmaCover : ∀ {H : Subgroup G},
      H ∈ minSimple_max_groups (G := G) →
      Disjoint T (sigmaCover H) := by
    intro H hH
    apply Set.disjoint_left.2
    intro t htT htH
    rcases htH with ⟨x, hxSigma, hx1, r, hr, htCover⟩
    have ht1 : t ≠ 1 := (mem_subgroupNonidentity.mp htT.1).2
    have hcovered : ∃ x : G,
        sigmaLength x = 1 ∧ x⁻¹ * t ∈ ftSignalizer x := by
      refine ⟨x, Msigma_ell1 hH hxSigma hx1, ?_⟩
      rw [htCover]
      simpa using hr
    rcases hTfactor htT with
      ⟨Mi, hMi, y, hy, y', hy', htFactor⟩
    rcases mem_subgroupNonidentity.mp hy with ⟨hyKs, hy1⟩
    rcases mem_subgroupNonidentity.mp hy' with ⟨hyK, hy'1⟩
    have hMiMax := (hMXspec hMi).1.1
    have hresidual : ∃ y : G,
        sigmaLength y = 1 ∧
        ∃ N : Subgroup G,
          N ∈ sigmaMaximalOvergroups (Subgroup.zpowers y : Set G) ∧
          y⁻¹ * t ≠ 1 ∧
          y⁻¹ * t ∈ elementCentralizerWithin N y ∧
          IsPiNumber (kappaPrimes N) (orderOf (y⁻¹ * t)) := by
      refine ⟨y, Msigma_ell1 hMiMax
        (centralizerWithin_le_left _ _ hyKs) hy1, Mi, ?_, ?_, ?_, ?_⟩
      · exact ⟨hMiMax,
          Subgroup.zpowers_le.mpr (centralizerWithin_le_left _ _ hyKs)⟩
      · simpa [htFactor] using hy'1
      · have hcomm := (hdirectZ hMi).commute
          ⟨y', hyK⟩ ⟨y, hyKs⟩
        have hresEq : y⁻¹ * t = y' := by
          rw [htFactor]
          group
        refine ⟨(hMXspec hMi).2.1 (hresEq.symm ▸ hyK), ?_⟩
        intro z hz
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        rw [hresEq]
        simpa using hcomm.symm.zpow_left n |>.eq
      · have horder : orderOf y' ∣ Nat.card (KAt Mi) := by
          simpa using orderOf_dvd_natCard (⟨y', hyK⟩ : KAt Mi)
        have hcard : IsPiNumber (kappaPrimes Mi) (Nat.card (KAt Mi)) := by
          simpa only [MathlibSupport.natCard_subgroupOf_eq
            (hMXspec hMi).2.1] using
            (hMXspec hMi).2.2.isPiNumber_card
        have hresEq : y⁻¹ * t = y' := by
          rw [htFactor]
          group
        rw [hresEq]
        exact hcard.of_dvd horder
    exact
      (sigma_decomposition_dichotomy ht1).exclusive
        ⟨hcovered, hresidual⟩

  have hnormalizedT : IsNormalizedTI T (⊤ : Subgroup G) Z := by
    refine (isNormalizedTI_iff_mem_conj).2 ⟨hTnonempty, le_top, ?_⟩
    intro t ht g _
    constructor
    · intro htConj
      rcases hTfactor ht with
        ⟨Mi, hMi, y, hy, y', hy', rfl⟩
      rcases mem_subgroupNonidentity.mp hy with ⟨hyKs, hy1⟩
      rcases mem_subgroupNonidentity.mp hy' with ⟨hyK, hy'1⟩
      have hMiStruct := Ptype_structure
        (hMXspec hMi).1 (hMXspec hMi).2.1 (hMXspec hMi).2.2
      have hySigma :
          IsPiNumber (sigmaPrimes Mi) (orderOf y) := by
        have hpi := (hHallZ hMi).2.isPiNumber_card
        rw [MathlibSupport.natCard_subgroupOf_eq
          (hdirectZ hMi).right_le] at hpi
        apply hpi.of_dvd
        simpa using orderOf_dvd_natCard (⟨y, hyKs⟩ : KsAt Mi)
      have hyCompl :
          IsPiNumber (sigmaPrimes Mi)ᶜ (orderOf y') := by
        have hpi := (hHallZ hMi).1.isPiNumber_card
        rw [MathlibSupport.natCard_subgroupOf_eq
          (hdirectZ hMi).left_le] at hpi
        apply hpi.of_dvd
        simpa using orderOf_dvd_natCard (⟨y', hyK⟩ : KAt Mi)
      have hcomm : Commute y' y :=
        (hdirectZ hMi).commute ⟨y', hyK⟩ ⟨y, hyKs⟩
      have hcommConj :
          Commute (g⁻¹ * y' * g) (g⁻¹ * y * g) := by
        simpa [MulAut.conj_apply] using
          hcomm.map (MulAut.conj g⁻¹).toMonoidHom
      have hyConjSigma :
          IsPiNumber (sigmaPrimes Mi) (orderOf (g⁻¹ * y * g)) := by
        rw [show g⁻¹ * y * g = (MulAut.conj g⁻¹) y by
          simp [MulAut.conj_apply]]
        rw [(MulAut.conj g⁻¹).orderOf_eq]
        exact hySigma
      have hyConjCompl :
          IsPiNumber (sigmaPrimes Mi)ᶜ (orderOf (g⁻¹ * y' * g)) := by
        rw [show g⁻¹ * y' * g = (MulAut.conj g⁻¹) y' by
          simp [MulAut.conj_apply]]
        rw [(MulAut.conj g⁻¹).orderOf_eq]
        exact hyCompl
      have hconjFactor :
          g⁻¹ * (y * y') * g =
            (g⁻¹ * y' * g) * (g⁻¹ * y * g) := by
        calc
          g⁻¹ * (y * y') * g =
              (g⁻¹ * y * g) * (g⁻¹ * y' * g) := by group
          _ = (g⁻¹ * y' * g) * (g⁻¹ * y * g) := hcommConj.eq.symm
      have hcomponent :
          sigmaComponent Mi (g⁻¹ * (y * y') * g) =
            g⁻¹ * y * g := by
        rw [hconjFactor]
        exact sigmaComponent_mul_eq_right_of_compl_left_of_sigma_right
          Mi hcommConj hyConjCompl hyConjSigma
      have hcomplement :
          sigmaComplementComponent Mi (g⁻¹ * (y * y') * g) =
            g⁻¹ * y' * g := by
        rw [hconjFactor]
        exact sigmaComplementComponent_mul_eq_left_of_compl_left_of_sigma_right
          Mi hcommConj hyConjCompl hyConjSigma
      have htConjZ : g⁻¹ * (y * y') * g ∈ Z :=
        (mem_subgroupNonidentity.mp htConj.1).1
      have hyConjKs : g⁻¹ * y * g ∈ KsAt Mi := by
        rw [← hcomponent]
        exact mem_normalHall_sigmaComponent
          (hdirectZ hMi).right_le (hnormalZ hMi).2
          (hHallZ hMi).2 htConjZ
      have hgMi : g ∈ Mi := by
        by_contra hgMi
        have hyMap :
            y ∈ Mi.map (MulAut.conj g).toMonoidHom := by
          rw [Subgroup.mem_map_equiv]
          simpa [MulAut.conj_apply] using
            (hMiStruct.normalizer_direct.right_le hyConjKs).1
        have hyInf : y ∈
            pTypeCentralizer Mi (KAt Mi) ⊓
              Mi.map (MulAut.conj g).toMonoidHom :=
          ⟨hyKs, hyMap⟩
        rw [hMiStruct.Kstar_TI_outside g hgMi] at hyInf
        exact hy1 (by simpa using hyInf)
      have hyConjK : g⁻¹ * y' * g ∈ KAt Mi := by
        rw [← hcomplement]
        exact mem_normalHall_sigmaComplementComponent
          (hdirectZ hMi).left_le (hnormalZ hMi).1
          (hHallZ hMi).1 htConjZ
      have hgNorm : g ∈ Subgroup.normalizer (KAt Mi : Set G) := by
        by_contra hgNorm
        have hyMap :
            y' ∈ (KAt Mi).map (MulAut.conj g).toMonoidHom := by
          rw [Subgroup.mem_map_equiv]
          simpa [MulAut.conj_apply] using hyConjK
        have hyInf : y' ∈
            KAt Mi ⊓ (KAt Mi).map (MulAut.conj g).toMonoidHom :=
          ⟨hyK, hyMap⟩
        rw [hMiStruct.K_TI_off_normalizer g hgMi hgNorm] at hyInf
        exact hy'1 (by simpa using hyInf)
      have hgRel : g ∈ normalizerWithin Mi (KAt Mi) := ⟨hgMi, hgNorm⟩
      have hNormEq : normalizerWithin Mi (KAt Mi) = Z := by
        calc
          normalizerWithin Mi (KAt Mi) = KAt Mi ⊔ KsAt Mi :=
            internalDirectProduct_eq_sup hMiStruct.normalizer_direct
          _ = Z := hcommonZ hMi
      simpa [hNormEq] using hgRel
    · intro hgZ
      rcases ht with ⟨htZsharp, htNone⟩
      rcases mem_subgroupNonidentity.mp htZsharp with ⟨htZ, ht1⟩
      have htConjZ : g⁻¹ * t * g ∈ Z :=
        Z.mul_mem (Z.mul_mem (Z.inv_mem hgZ) htZ) hgZ
      have htConj1 : g⁻¹ * t * g ≠ 1 := by
        intro hconj
        apply ht1
        calc
          t = g * (g⁻¹ * t * g) * g⁻¹ := by group
          _ = 1 := by rw [hconj]; simp
      refine ⟨mem_subgroupNonidentity.mpr ⟨htConjZ, htConj1⟩, ?_⟩
      intro hcover
      simp only [Set.mem_iUnion] at hcover
      rcases hcover with ⟨Mj, hMj, htConjKsSharp⟩
      rcases mem_subgroupNonidentity.mp htConjKsSharp with
        ⟨htConjKs, -⟩
      let KsjZ : Subgroup Z := (KsAt Mj).subgroupOf Z
      let tcZ : Z := ⟨g⁻¹ * t * g, htConjZ⟩
      let gZ : Z := ⟨g, hgZ⟩
      have htcKsjZ : tcZ ∈ KsjZ := htConjKs
      have htBack : gZ * tcZ * gZ⁻¹ ∈ KsjZ :=
        (hnormalZ hMj).2.conj_mem tcZ htcKsjZ gZ
      have hbackEq : gZ * tcZ * gZ⁻¹ = (⟨t, htZ⟩ : Z) := by
        apply Subtype.ext
        dsimp [gZ, tcZ]
        group
      have htKsjZ : (⟨t, htZ⟩ : Z) ∈ KsjZ := by
        rw [← hbackEq]
        exact htBack
      apply htNone
      simp only [Set.mem_iUnion]
      refine ⟨Mj, hMj, mem_subgroupNonidentity.mpr ⟨?_, ht1⟩⟩
      exact htKsjZ

  /- The source cardinality calculation and the disjoint sigma-support
  estimate force a P2 member of `MX`. -/
  have hP2member : ∃ Mi : Subgroup G,
      Mi ∈ MX ∧ Mi ∈ typeP2MaximalSubgroups (G := G) := by
    by_contra hnone
    have hnone' : ∀ Mi : Subgroup G, Mi ∈ MX →
        Mi ∉ typeP2MaximalSubgroups (G := G) := by
      intro Mi hMi hMiP2
      exact hnone ⟨Mi, hMi, hMiP2⟩
    let TG := classSupportWithin (⊤ : Subgroup G) T
    let SS (Mi : Subgroup G) : Set G :=
      classSupportWithin (⊤ : Subgroup G) (sigmaCover Mi)
    let KU : Set G :=
      ⋃ Mi ∈ MX, subgroupNonidentity (KsAt Mi)
    let SU : Set G := ⋃ Mi ∈ MX, SS Mi
    let MXfin : MX.Finite := Set.toFinite MX
    let I : Finset (Subgroup G) := MXfin.toFinset
    have hIcard : I.card = MX.ncard := by
      simpa [I, MXfin] using
        (Set.ncard_eq_toFinset_card MX (Set.toFinite MX)).symm

    have hMXnotConj : ∀ {Mi Mj : Subgroup G},
        Mi ∈ MX → Mj ∈ MX → Mi ≠ Mj →
          ¬ AreConjugateSubgroups Mi Mj := by
      intro Mi Mj hMi hMj hne hconj
      rcases hconj with ⟨g, hg⟩
      have hSigmaEq : sigmaPrimes Mj = sigmaPrimes Mi := by
        rw [hg]
        exact sigmaPrimes_conj Mi g
      have hKsSigma :
          IsPiNumber (sigmaPrimes Mj) (Nat.card (KsAt Mi)) := by
        rw [hSigmaEq]
        exact (sigmaCore_isPiNumber Mi).of_dvd
          (Subgroup.card_dvd_of_le (centralizerWithin_le_left _ _))
      have hKsKappa :
          IsPiNumber (kappaPrimes Mj) (Nat.card (KsAt Mi)) := by
        have hcard : IsPiNumber (kappaPrimes Mj) (Nat.card (KAt Mj)) := by
          simpa only [MathlibSupport.natCard_subgroupOf_eq
            (hMXspec hMj).2.1] using
            (hMXspec hMj).2.2.isPiNumber_card
        exact hcard.of_dvd
          (Subgroup.card_dvd_of_le (hcross hMj hMi hne))
      have hcop :=
        hKsSigma.coprime_compl (hKsKappa.mono (kappa_sigma' Mj))
      have hcardOne : Nat.card (KsAt Mi) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
      exact hKsAtNe hMi (Subgroup.card_eq_one.mp hcardOne)

    have hKpairwise : MX.PairwiseDisjoint
        (fun Mi : Subgroup G ↦ subgroupNonidentity (KsAt Mi)) := by
      intro Mi hMi Mj hMj hne
      apply Set.disjoint_left.2
      intro x hxi hxj
      rcases mem_subgroupNonidentity.mp hxi with ⟨hxiKs, hxi1⟩
      rcases mem_subgroupNonidentity.mp hxj with ⟨hxjKs, -⟩
      have hxinf : x ∈ KsAt Mi ⊓ KsAt Mj := ⟨hxiKs, hxjKs⟩
      rw [hKsDisjoint hMi hMj hne] at hxinf
      exact hxi1 (by simpa using hxinf)
    have hKUcardRaw := MXfin.ncard_biUnion
      (fun _ _ ↦ Set.toFinite _) hKpairwise
    rw [finsum_mem_eq_finite_toFinset_sum _ MXfin] at hKUcardRaw
    have hKUcard : KU.ncard =
        ∑ Mi ∈ I, (subgroupNonidentity (KsAt Mi)).ncard := by
      simpa [KU, I] using hKUcardRaw
    have hKUsub : KU ⊆ subgroupNonidentity Z := by
      intro x hxiU
      change x ∈ ⋃ Mi ∈ MX, subgroupNonidentity (KsAt Mi) at hxiU
      simp only [Set.mem_iUnion] at hxiU
      rcases hxiU with ⟨Mi, hMi, hxi⟩
      rcases mem_subgroupNonidentity.mp hxi with ⟨hxiKs, hxi1⟩
      exact mem_subgroupNonidentity.mpr
        ⟨(hdirectZ hMi).right_le hxiKs, hxi1⟩
    have hTdef : T = subgroupNonidentity Z \ KU := by rfl
    have hTdisKU : Disjoint T KU := by
      rw [hTdef]
      exact Set.disjoint_sdiff_left
    have hTunionKU : T ∪ KU = subgroupNonidentity Z := by
      rw [hTdef]
      exact Set.sdiff_union_of_subset hKUsub
    have hTplusKU : T.ncard + KU.ncard =
        (subgroupNonidentity Z).ncard := by
      rw [← Set.ncard_union_eq hTdisKU, hTunionKU]
    have hTpartitionNat :
        T.ncard +
            (∑ Mi ∈ I, (subgroupNonidentity (KsAt Mi)).ncard) + 1 =
          Nat.card Z := by
      rw [hKUcard] at hTplusKU
      have hZsharp := subgroupNonidentity_ncard_add_one_pType Z
      omega

    have hSpairwise : MX.PairwiseDisjoint SS := by
      intro Mi hMi Mj hMj hne
      apply Set.disjoint_left.2
      intro z hzMi hzMj
      rcases hzMi with ⟨a, haMi, g, -, rfl⟩
      rcases hzMj with ⟨b, hbMj, h, -, hab⟩
      change h⁻¹ * b * h = g⁻¹ * a * g at hab
      let c : G := g * h⁻¹
      have hMjcMax :
          Mj.map (MulAut.conj c).toMonoidHom ∈
            minSimple_max_groups (G := G) :=
        (mmaxJ Mj (MulAut.conj c)).2 (hMXspec hMj).1.1
      have hnotConjC : ∀ r : G,
          Mj.map (MulAut.conj c).toMonoidHom ≠
            Mi.map (MulAut.conj r).toMonoidHom := by
        intro r heq
        apply hMXnotConj hMi hMj hne
        refine ⟨c⁻¹ * r, ?_⟩
        have hback := congrArg
          (fun L : Subgroup G ↦
            L.map (MulAut.conj c⁻¹).toMonoidHom) heq
        have hleft :
            (Mj.map (MulAut.conj c).toMonoidHom).map
                (MulAut.conj c⁻¹).toMonoidHom = Mj := by
          rw [Subgroup.map_map]
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        have hright :
            (Mi.map (MulAut.conj r).toMonoidHom).map
                (MulAut.conj c⁻¹).toMonoidHom =
              Mi.map (MulAut.conj (c⁻¹ * r)).toMonoidHom := by
          rw [Subgroup.map_map]
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        exact hleft.symm.trans (hback.trans hright)
      have hrawDis : Disjoint (sigmaCover Mi)
          (sigmaCover (Mj.map (MulAut.conj c).toMonoidHom)) :=
        sigma_support_disjoint (hMXspec hMi).1.1 hMjcMax hnotConjC
      have haMjc : a ∈
          sigmaCover (Mj.map (MulAut.conj c).toMonoidHom) := by
        rw [sigma_supportJ]
        refine ⟨b, hbMj, ?_⟩
        rw [MulAut.conj_apply]
        dsimp [c]
        calc
          (g * h⁻¹) * b * (g * h⁻¹)⁻¹ =
              g * (h⁻¹ * b * h) * g⁻¹ := by group
          _ = g * (g⁻¹ * a * g) * g⁻¹ := by rw [hab]
          _ = a := by group
      exact (Set.disjoint_left.mp hrawDis) haMi haMjc
    have hSUcardRaw := MXfin.ncard_biUnion
      (fun _ _ ↦ Set.toFinite _) hSpairwise
    rw [finsum_mem_eq_finite_toFinset_sum _ MXfin] at hSUcardRaw
    have hSUcard : SU.ncard = ∑ Mi ∈ I, (SS Mi).ncard := by
      simpa [SU, I] using hSUcardRaw
    have hTsupportDisjoint : ∀ Mi ∈ MX, Disjoint TG (SS Mi) := by
      intro Mi hMi
      exact classSupport_disjoint_of_disjoint_sigmaCover
        hT_disjoint_sigmaCover (hMXspec hMi).1.1
    have hTGdisSU : Disjoint TG SU := by
      apply Set.disjoint_left.2
      intro x hxTG hxSU
      change x ∈ ⋃ Mi ∈ MX, SS Mi at hxSU
      simp only [Set.mem_iUnion] at hxSU
      rcases hxSU with ⟨Mi, hMi, hxi⟩
      exact (Set.disjoint_left.mp (hTsupportDisjoint Mi hMi)) hxTG hxi
    have hCombinedCardNat :
        (TG ∪ SU).ncard = TG.ncard + ∑ Mi ∈ I, (SS Mi).ncard := by
      rw [Set.ncard_union_eq hTGdisSU, hSUcard]

    have hTGnonid : TG ⊆ nonidentitySet G := by
      rintro x ⟨t, htT, g, -, rfl⟩
      change g⁻¹ * t * g ≠ 1
      intro hconjOne
      have htOne : t = 1 := by
        calc
          t = g * (g⁻¹ * t * g) * g⁻¹ := by group
          _ = 1 := by rw [hconjOne]; simp
      have htSharp : t ∈ subgroupNonidentity Z := htT.1
      exact (mem_subgroupNonidentity.mp htSharp).2 htOne
    have hCombinedNonid : TG ∪ SU ⊆ nonidentitySet G := by
      rintro x (hxTG | hxSU)
      · exact hTGnonid hxTG
      · change x ∈ ⋃ Mi ∈ MX, SS Mi at hxSU
        simp only [Set.mem_iUnion] at hxSU
        rcases hxSU with ⟨Mi, hMi, hxi⟩
        exact classSupport_sigmaCover_subset_nonidentity_pType
          (hMXspec hMi).1.1 hxi
    have hCombinedUpperNat : (TG ∪ SU).ncard + 1 ≤ Nat.card G := by
      calc
        (TG ∪ SU).ncard + 1 ≤ (nonidentitySet G).ncard + 1 :=
          Nat.add_le_add_right (Set.ncard_le_ncard hCombinedNonid) 1
        _ = Nat.card G := nonidentitySet_ncard_add_one_pType

    have hMNXnonemptyEarly : MNX.Nonempty :=
      lineNormalizerMaximals_nonempty hKne
    have hMXcard : MX.ncard = MNX.ncard + 1 := by
      change ({M} ∪ MNX).ncard = MNX.ncard + 1
      rw [Set.singleton_union, Set.ncard_insert_of_notMem hMnotMNX]
    have hMNXcardPos : 1 ≤ MNX.ncard := by
      obtain ⟨N, hN⟩ := hMNXnonemptyEarly
      exact Nat.one_le_iff_ne_zero.mpr (Set.ncard_ne_zero_of_mem hN)
    have hIcardTwo : 2 ≤ I.card := by omega

    have hZleMX : ∀ Mi ∈ MX, Z ≤ Mi := by
      intro Mi hMi
      rw [← hcommonZ hMi]
      refine sup_le (hMXspec hMi).2.1 ?_
      simpa [KsAt] using
        ((centralizerWithin_le_left _ _).trans (sigmaCore_le Mi))
    have hZneM : Z ≠ M := by
      intro hZM
      obtain ⟨N, hNMNX⟩ := hMNXnonemptyEarly
      have hNMX : N ∈ MX := Or.inr hNMNX
      have hMN : M ≤ N := by
        rw [← hZM]
        exact hZleMX N hNMX
      have hMN_eq : M = N :=
        eq_mmax hmaxM (hMXspec hNMX).1.1 hMN
      apply hMnotMNX
      rw [hMN_eq]
      exact hNMNX

    have hsupportLower : ∀ Mi ∈ MX,
        ((classSupportWithin (⊤ : Subgroup G)
          (sigmaCover Mi)).ncard : ℚ) ≥
        (((Nat.card (KAt Mi) : ℚ)⁻¹ -
          ((2 * Nat.card Z : ℚ)⁻¹)) * Nat.card G) := by
      intro Mi hMi
      have hMiP1 : Mi ∈ typeP1MaximalSubgroups (G := G) := by
        by_contra hMiNotP1
        exact hnone' Mi hMi ⟨(hMXspec hMi).1, hMiNotP1⟩
      have hMiStruct := Ptype_structure
        (hMXspec hMi).1 (hMXspec hMi).2.1 (hMXspec hMi).2.2
      have hUbot : hMiStruct.U = ⊥ :=
        (trivg_kappa_compl (hMXspec hMi).1.1
          hMiStruct.complement).2 hMiP1
      have hZMi : Z ≤ Mi := hZleMX Mi hMi
      have hZneMi : Z ≠ Mi := by
        intro hZMiEq
        have hMiM : Mi = M :=
          eq_mmax (hMXspec hMi).1.1 hmaxM (by
            rw [← hZMiEq]
            exact hZleMX M (by simp [MX]))
        exact hZneM (hZMiEq.trans hMiM)
      have hZsubNeTop : Z.subgroupOf Mi ≠ ⊤ := by
        intro htop
        exact hZneMi
          (le_antisymm hZMi (Subgroup.subgroupOf_eq_top.mp htop))
      have hrelTwo : 2 ≤ Z.relIndex Mi :=
        Subgroup.one_lt_index_of_ne_top hZsubNeTop
      have hcardMiRel :
          Nat.card Z * Z.relIndex Mi = Nat.card Mi := by
        change Nat.card Z * (Z.subgroupOf Mi).index = Nat.card Mi
        rw [← MathlibSupport.natCard_subgroupOf_eq hZMi]
        exact (Z.subgroupOf Mi).card_mul_index
      have htwoZ : 2 * Nat.card Z ≤ Nat.card Mi := by
        calc
          2 * Nat.card Z = Nat.card Z * 2 := Nat.mul_comm _ _
          _ ≤ Nat.card Z * Z.relIndex Mi :=
            Nat.mul_le_mul_left _ hrelTwo
          _ = Nat.card Mi := hcardMiRel
      have hcardMiFactor :
          Nat.card Mi =
            Nat.card (sigmaCore Mi) * Nat.card (KAt Mi) := by
        let SM : Subgroup Mi := (sigmaCore Mi).subgroupOf Mi
        let CK : Subgroup Mi :=
          (hMiStruct.U ⊔ KAt Mi).subgroupOf Mi
        calc
          Nat.card Mi = Nat.card SM * SM.index :=
            SM.card_mul_index.symm
          _ = Nat.card SM * Nat.card CK := by
            rw [hMiStruct.sigma_UK_sdprod.2.2.2.symm.index_eq_card]
          _ = Nat.card (sigmaCore Mi) * Nat.card (KAt Mi) := by
            rw [MathlibSupport.natCard_subgroupOf_eq
                hMiStruct.sigma_UK_sdprod.1,
              MathlibSupport.natCard_subgroupOf_eq
                hMiStruct.sigma_UK_sdprod.2.1,
              hUbot, bot_sup_eq]
      have hcardGMi : Nat.card Mi * Mi.index = Nat.card G :=
        Mi.card_mul_index
      have hSigmaSharp :=
        subgroupNonidentity_ncard_add_one_pType (sigmaCore Mi)
      have hSigmaSub : Nat.card (sigmaCore Mi) - 1 =
          (subgroupNonidentity (sigmaCore Mi)).ncard := by
        omega
      have hSupportNat := card_class_support_sigma (hMXspec hMi).1.1
      rw [hSigmaSub] at hSupportNat
      have hSupportQ :
          ((SS Mi).ncard : ℚ) =
            ((subgroupNonidentity (sigmaCore Mi)).ncard : ℚ) *
              Mi.index := by
        simpa [SS] using congrArg (fun n : ℕ ↦ (n : ℚ)) hSupportNat
      have hSigmaSharpQ :
          ((subgroupNonidentity (sigmaCore Mi)).ncard : ℚ) + 1 =
            Nat.card (sigmaCore Mi) := by
        exact_mod_cast hSigmaSharp
      have hcardMiFactorQ :
          (Nat.card Mi : ℚ) =
            Nat.card (sigmaCore Mi) * Nat.card (KAt Mi) := by
        exact_mod_cast hcardMiFactor
      have hcardGMiQ :
          (Nat.card Mi : ℚ) * Mi.index = Nat.card G := by
        exact_mod_cast hcardGMi
      have hkNe : (Nat.card (KAt Mi) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos.ne' : Nat.card (KAt Mi) ≠ 0)
      have hzNe : (Nat.card Z : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos.ne' : Nat.card Z ≠ 0)
      have hRhsEq :
          (((Nat.card (KAt Mi) : ℚ)⁻¹ -
              ((2 * Nat.card Z : ℚ)⁻¹)) * Nat.card G) =
            ((Nat.card (sigmaCore Mi) : ℚ) -
                (Nat.card Mi : ℚ) / (2 * Nat.card Z)) * Mi.index := by
        rw [← hcardGMiQ, hcardMiFactorQ]
        field_simp [hkNe, hzNe]
        <;> ring
      have hRatio : (1 : ℚ) ≤
          (Nat.card Mi : ℚ) / (2 * Nat.card Z) := by
        rw [le_div_iff₀ (by positivity : (0 : ℚ) < 2 * Nat.card Z)]
        have htwoZQ : (2 * Nat.card Z : ℚ) ≤ Nat.card Mi := by
          exact_mod_cast htwoZ
        simpa only [one_mul] using htwoZQ
      rw [hRhsEq]
      rw [hSupportQ, ← hSigmaSharpQ]
      have hindexNonneg : (0 : ℚ) ≤ Mi.index := by positivity
      apply mul_le_mul_of_nonneg_right _ hindexNonneg
      nlinarith

    have hKsSharpQ : ∀ Mi ∈ MX,
        ((subgroupNonidentity (KsAt Mi)).ncard : ℚ) + 1 =
          Nat.card (KsAt Mi) := by
      intro Mi hMi
      exact_mod_cast (subgroupNonidentity_ncard_add_one_pType (KsAt Mi))
    have hsupportLowerSharp : ∀ Mi ∈ MX,
        (((subgroupNonidentity (KsAt Mi)).ncard : ℚ) + (1 / 2 : ℚ)) *
            Z.index ≤ (SS Mi).ncard := by
      intro Mi hMi
      have hraw := hsupportLower Mi hMi
      have hzcard :
          Nat.card Z = Nat.card (KAt Mi) * Nat.card (KsAt Mi) :=
        (hdirectZ hMi).card_eq_mul_card
      have hzindex : Nat.card Z * Z.index = Nat.card G :=
        Z.card_mul_index
      have hzcardQ : (Nat.card Z : ℚ) =
          Nat.card (KAt Mi) * Nat.card (KsAt Mi) := by
        exact_mod_cast hzcard
      have hzindexQ : (Nat.card Z : ℚ) * Z.index = Nat.card G := by
        exact_mod_cast hzindex
      have hkNe : (Nat.card (KAt Mi) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos.ne' : Nat.card (KAt Mi) ≠ 0)
      have hksNe : (Nat.card (KsAt Mi) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos.ne' : Nat.card (KsAt Mi) ≠ 0)
      have heq :
          (((Nat.card (KAt Mi) : ℚ)⁻¹ -
              ((2 * Nat.card Z : ℚ)⁻¹)) * Nat.card G) =
            ((Nat.card (KsAt Mi) : ℚ) - (1 / 2 : ℚ)) *
              Z.index := by
        rw [← hzindexQ, hzcardQ]
        field_simp [hkNe, hksNe]
        <;> ring
      rw [heq] at hraw
      have hsharp := hKsSharpQ Mi hMi
      rw [← hsharp] at hraw
      convert hraw using 1 <;> ring
    have hsumLower :
        (∑ Mi ∈ I,
            (((subgroupNonidentity (KsAt Mi)).ncard : ℚ) +
              (1 / 2 : ℚ)) * Z.index) ≤
          ∑ Mi ∈ I, ((SS Mi).ncard : ℚ) := by
      apply Finset.sum_le_sum
      intro Mi hMi
      exact hsupportLowerSharp Mi (by simpa [I] using hMi)
    have hsumRewrite :
        (∑ Mi ∈ I,
            (((subgroupNonidentity (KsAt Mi)).ncard : ℚ) +
              (1 / 2 : ℚ)) * Z.index) =
          ((∑ Mi ∈ I,
              ((subgroupNonidentity (KsAt Mi)).ncard : ℚ)) +
            (I.card : ℚ) / 2) * Z.index := by
      rw [← Finset.sum_mul]
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul]
      ring
    have hTpartitionQ :
        (T.ncard : ℚ) +
            (∑ Mi ∈ I,
              ((subgroupNonidentity (KsAt Mi)).ncard : ℚ)) + 1 =
          Nat.card Z := by
      exact_mod_cast hTpartitionNat
    have hTGcardQ : (TG.ncard : ℚ) =
        (T.ncard : ℚ) * Z.index := by
      exact_mod_cast (ncard_classSupport_normalizedTI hnormalizedT)
    have hCombinedCardQ : ((TG ∪ SU).ncard : ℚ) =
        (TG.ncard : ℚ) + ∑ Mi ∈ I, ((SS Mi).ncard : ℚ) := by
      exact_mod_cast hCombinedCardNat
    have hCombinedUpperQ : ((TG ∪ SU).ncard : ℚ) + 1 ≤
        Nat.card G := by
      exact_mod_cast hCombinedUpperNat
    have hIcardTwoQ : (2 : ℚ) ≤ I.card := by
      exact_mod_cast hIcardTwo
    have hZindexQ : (Nat.card Z : ℚ) * Z.index = Nat.card G := by
      exact_mod_cast (Z.card_mul_index)
    have hIndexNonneg : (0 : ℚ) ≤ Z.index := by positivity
    have hCoeff : (Nat.card Z : ℚ) ≤
        (T.ncard : ℚ) +
          (∑ Mi ∈ I,
            ((subgroupNonidentity (KsAt Mi)).ncard : ℚ)) +
          (I.card : ℚ) / 2 := by
      nlinarith [hTpartitionQ, hIcardTwoQ]
    have hWeighted : (Nat.card Z : ℚ) * Z.index ≤
        ((T.ncard : ℚ) +
          (∑ Mi ∈ I,
            ((subgroupNonidentity (KsAt Mi)).ncard : ℚ)) +
          (I.card : ℚ) / 2) * Z.index :=
      mul_le_mul_of_nonneg_right hCoeff hIndexNonneg
    have hCombinedLower : (Nat.card G : ℚ) ≤ (TG ∪ SU).ncard := by
      calc
        (Nat.card G : ℚ) = (Nat.card Z : ℚ) * Z.index :=
          hZindexQ.symm
        _ ≤ ((T.ncard : ℚ) +
              (∑ Mi ∈ I,
                ((subgroupNonidentity (KsAt Mi)).ncard : ℚ)) +
              (I.card : ℚ) / 2) * Z.index := hWeighted
        _ = (T.ncard : ℚ) * Z.index +
              ∑ Mi ∈ I,
                (((subgroupNonidentity (KsAt Mi)).ncard : ℚ) +
                  (1 / 2 : ℚ)) * Z.index := by
            rw [hsumRewrite]
            ring
        _ = (TG.ncard : ℚ) +
              ∑ Mi ∈ I,
                (((subgroupNonidentity (KsAt Mi)).ncard : ℚ) +
                  (1 / 2 : ℚ)) * Z.index := by
            rw [hTGcardQ]
        _ ≤ (TG.ncard : ℚ) +
              ∑ Mi ∈ I, ((SS Mi).ncard : ℚ) :=
            by
              exact add_le_add_right hsumLower _
        _ = ((TG ∪ SU).ncard : ℚ) := hCombinedCardQ.symm
    nlinarith [hCombinedLower, hCombinedUpperQ]
  obtain ⟨Mi, hMiMX, hMiP2⟩ := hP2member
  have hMiStruct := Ptype_structure
    (hMXspec hMiMX).1 (hMXspec hMiMX).2.1 (hMXspec hMiMX).2.2
  have hMiTwo := hMiStruct.typeP2 hMiP2

  /- The P2 prime-order conclusion collapses `MX` to two elements. -/
  obtain ⟨Mj, hMjMX, hMjNe⟩ :
      ∃ Mj : Subgroup G, Mj ∈ MX ∧ Mj ≠ Mi := by
    by_contra hnone
    push_neg at hnone
    have hMXsingle : MX = {Mi} := by
      ext L
      constructor
      · intro hL
        exact Set.mem_singleton_iff.mpr (hnone L hL)
      · intro hL
        simpa using hL ▸ hMiMX
    obtain ⟨N, hNMNX⟩ := lineNormalizerMaximals_nonempty hKne
    have hNMX : N ∈ MX := Or.inr hNMNX
    have hMMX : M ∈ MX := by simp [MX]
    rw [hMXsingle] at hNMX hMMX
    have hNMi := Set.mem_singleton_iff.mp hNMX
    have hMMi := Set.mem_singleton_iff.mp hMMX
    exact hMnotMNX (by simpa [hNMi, hMMi] using hNMNX)
  have hKsMj_eq_KMi : KsAt Mj = KAt Mi := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact hcross hMiMX hMjMX hMjNe
    · have hprime := hMiTwo.card_K_prime
      have hdvd :=
        Subgroup.card_dvd_of_le (hcross hMiMX hMjMX hMjNe)
      have hneOne : Nat.card (KsAt Mj) ≠ 1 := by
        intro hone
        exact hKsAtNe hMjMX (Subgroup.card_eq_one.mp hone)
      exact ((Nat.dvd_prime hprime).mp hdvd).resolve_left hneOne |>.ge
  have hMXpair : MX = {Mi, Mj} := by
    ext Mk
    constructor
    · intro hMk
      by_cases hki : Mk = Mi
      · simp [hki]
      by_cases hkj : Mk = Mj
      · simp [hkj]
      have hle : KsAt Mk ≤ KsAt Mj := by
        rw [hKsMj_eq_KMi]
        exact hcross hMiMX hMk hki
      have hbot : KsAt Mk = ⊥ := by
        rw [← inf_eq_left.mpr hle, hKsDisjoint hMk hMjMX hkj]
      exact (hKsAtNe hMk hbot).elim
    · intro hMk
      rcases hMk with (rfl | rfl)
      · exact hMiMX
      · exact hMjMX
  have hKsMi_eq_KMj : KsAt Mi = KAt Mj := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact hcross hMjMX hMiMX hMjNe.symm
    · have hi := (hdirectZ hMiMX).card_eq_mul_card
      have hj := (hdirectZ hMjMX).card_eq_mul_card
      rw [hKsMj_eq_KMi] at hj
      have hmul : Nat.card (KAt Mi) * Nat.card (KsAt Mi) =
          Nat.card (KAt Mi) * Nat.card (KAt Mj) := by
        calc
          Nat.card (KAt Mi) * Nat.card (KsAt Mi) = Nat.card Z := hi.symm
          _ = Nat.card (KAt Mj) * Nat.card (KAt Mi) := hj
          _ = Nat.card (KAt Mi) * Nat.card (KAt Mj) := Nat.mul_comm _ _
      exact (Nat.mul_left_cancel (Nat.card_pos (α := KAt Mi)) hmul).ge

  have hZnil : Group.IsNilpotent Z :=
    isNilpotent_of_internalDirectProduct
      (hdirectZ hMiMX)
      (isNilpotent_of_le (by
          letI : Fact (Nat.card (KAt Mi)).Prime := ⟨hMiTwo.card_K_prime⟩
          letI : IsCyclic (KAt Mi) :=
            isCyclic_of_prime_card (α := KAt Mi) rfl
          letI : CommGroup (KAt Mi) := IsCyclic.commGroup
          infer_instance)
        (show KAt Mi ≤ KAt Mi from le_rfl))
      (isNilpotent_of_le hMiTwo.sigmaCore_nilpotent
        (centralizerWithin_le_left _ _))
  have hZZgroup : IsZGroup Z := by
    refine ⟨?_⟩
    intro q hq S
    letI : Fact q.Prime := ⟨hq⟩
    let SG : Subgroup G := ambientSylow Z S
    have hSGZ : SG ≤ Z := by
      exact Subgroup.map_subtype_le (S : Subgroup Z)
    have hSGq : IsPGroup q SG := by
      exact S.isPGroup'.map Z.subtype
    rcases hSGq.card_eq_or_dvd with hSGone | hqSG
    · have hSGbot : SG = ⊥ := Subgroup.card_eq_one.mp hSGone
      have hSGcyclic : IsCyclic SG := by
        rw [hSGbot]
        infer_instance
      exact (isCyclic_ambientSylow_iff_pType Z S).mp hSGcyclic
    · have hSGcyclic : IsCyclic SG := by
        by_cases hqSigma : q ∈ sigmaPrimes Mi
        · have hSGKj : SG ≤ KAt Mj := by
            rw [← hKsMi_eq_KMj]
            exact isPiNumber_le_normal_isHall_pType
              (hdirectZ hMiMX).right_le (hnormalZ hMiMX).2
              (hHallZ hMiMX).2 hSGZ
              (hSGq.isPiNumber_natCard hqSigma)
          have hqKappa : q ∈ kappaPrimes Mj :=
            (hMXspec hMjMX).2.2.isPiNumber_card hq (by
              rw [MathlibSupport.natCard_subgroupOf_eq
                (hMXspec hMjMX).2.1]
              exact hqSG.trans (Subgroup.card_dvd_of_le hSGKj))
          apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
            hSGq (mFT_odd SG)).2
          rintro ⟨E, hE⟩
          let EG : Subgroup G := E.map SG.subtype
          have hEGMj : EG ≤ Mj :=
            (Subgroup.map_subtype_le E).trans
              (hSGKj.trans (hMXspec hMjMX).2.1)
          have hEGrank : IsElementaryAbelianOfRank q 2 EG :=
            hE.map_of_injective SG.subtype SG.subtype_injective
          exact (rank_kappa hqKappa).2 ⟨EG, hEGMj, hEGrank⟩
        · have hSGKi : SG ≤ KAt Mi :=
            isPiNumber_le_normal_isHall_pType
              (hdirectZ hMiMX).left_le (hnormalZ hMiMX).1
              (hHallZ hMiMX).1 hSGZ
              (hSGq.isPiNumber_natCard (by
                change q ∉ sigmaPrimes Mi
                exact hqSigma))
          letI : Fact (Nat.card (KAt Mi)).Prime := ⟨hMiTwo.card_K_prime⟩
          letI : IsCyclic (KAt Mi) :=
            isCyclic_of_prime_card (α := KAt Mi) rfl
          exact Subgroup.isCyclic_of_le hSGKi
      exact (isCyclic_ambientSylow_iff_pType Z S).mp hSGcyclic
  have hZcyclic : IsCyclic Z := by
    letI : Group.IsNilpotent Z := hZnil
    letI : IsZGroup Z := hZZgroup
    infer_instance

  have hDerived :
      IsInternalSemidirectProductIn
        ((_root_.commutator M).map M.subtype) K M := by
    obtain ⟨U, hU⟩ := ex_kappa_compl hmaxM hKM hK
    have hctx := kappa_compl_context hmaxM hU
    let D : Subgroup G := (_root_.commutator M).map M.subtype
    let A : Subgroup G := sigmaCore M ⊔ U
    have hUM : U ≤ M := hU.U_le_M
    have hAM : A ≤ M := sup_le (sigmaCore_le M) hUM
    have hKnormU : K ≤ Subgroup.normalizer (U : Set G) := by
      exact le_sup_right.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer
          hctx.U_K_sdprod.1).mp hctx.U_K_sdprod.2.2.1)
    have hcopUK : Nat.Coprime (Nat.card U) (Nat.card K) := by
      have hUpi : IsPiNumber (sigmaKappaPrimes M)ᶜ (Nat.card U) := by
        simpa only [MathlibSupport.natCard_subgroupOf_eq hUM] using
          hU.hall_U.isPiNumber_card
      have hKpi : IsPiNumber (sigmaKappaPrimes M) (Nat.card K) := by
        have hKappa : IsPiNumber (kappaPrimes M) (Nat.card K) := by
          simpa only [MathlibSupport.natCard_subgroupOf_eq hKM] using
            hU.hall_K.isPiNumber_card
        exact hKappa.mono (fun _ hp ↦ Or.inr hp)
      exact (hKpi.coprime_compl hUpi).symm
    have hUsol : IsSolvable U := by
      letI : IsSolvable M := mmax_sol hmaxM
      exact isSolvable_of_injective
        (Subgroup.inclusion hUM)
        (Subgroup.inclusion_injective hUM)
    have hcentUK : centralizerWithin U K = ⊥ :=
      centralizerWithin_eq_bot_of_semiregular_actor_ne_bot_pType
        hctx.U_K_semiregular hKne
    have hUcomm : U ≤ ⁅K, U⁆ := by
      letI : IsSolvable U := hUsol
      have hdecomp :=
        le_commutator_sup_centralizerWithin_of_coprime hKnormU hcopUK
      simpa [hcentUK, sup_bot_eq] using hdecomp
    have hUder : U ≤ D := by
      exact hUcomm.trans
        ((Subgroup.commutator_mono hKM hUM).trans
          M.map_subtype_commutator.ge)
    have hAleD : A ≤ D :=
      sup_le (by simpa [D] using Msigma_der1 hmaxM) hUder

    have hM_eq_AK : M = A ⊔ K := by
      calc
        M = sigmaCore M ⊔ (U ⊔ K) :=
          internalSemidirectProduct_eq_sup hctx.sigma_UK_sdprod
        _ = A ⊔ K := by simp [A, sup_assoc]
    have hMnormSigma :
        M ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (sigmaCore_le M)).mp (sigmaCore_normal M)
    have hKnormA : K ≤ Subgroup.normalizer (A : Set G) := by
      exact (le_inf (hKM.trans hMnormSigma) hKnormU).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup
          (sigmaCore M) U)
    have hMnormA : M ≤ Subgroup.normalizer (A : Set G) := by
      rw [hM_eq_AK]
      exact sup_le Subgroup.le_normalizer hKnormA
    have hAnormal : (A.subgroupOf M).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hMnormA
    let AM : Subgroup M := A.subgroupOf M
    let KM : Subgroup M := K.subgroupOf M
    have hsupAMKM : AM ⊔ KM = ⊤ := by
      change A.subgroupOf M ⊔ K.subgroupOf M = ⊤
      rw [← Subgroup.subgroupOf_sup hAM hKM, ← hM_eq_AK]
      exact Subgroup.subgroupOf_self M
    have hKcyclic : IsCyclic K := by
      letI : IsCyclic Z := hZcyclic
      exact Subgroup.isCyclic_of_le
        (show K ≤ Z from le_sup_left)
    have hKMcyclic : IsCyclic KM := by
      exact (Subgroup.subgroupOfEquivOfLe hKM).isCyclic.mpr hKcyclic
    have hcommMleA : _root_.commutator M ≤ AM := by
      letI : AM.Normal := by simpa [AM] using hAnormal
      exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
        hsupAMKM hKMcyclic.isMulCommutative
    have hDleA : D ≤ A := by
      have hmapped := Subgroup.map_mono hcommMleA (f := M.subtype)
      rw [Subgroup.map_subgroupOf_eq_of_le hAM] at hmapped
      simpa [D, AM] using hmapped
    have hderEq : D = A := le_antisymm hDleA hAleD

    have hSigmaKappaCompl :
        IsPiNumber (kappaPrimes M)ᶜ (Nat.card (sigmaCore M)) := by
      apply (sigmaCore_isPiNumber M).mono
      intro p hpSigma
      change p ∉ kappaPrimes M
      intro hpKappa
      exact (kappa_sigma' M hpKappa) hpSigma
    have hUKappaCompl :
        IsPiNumber (kappaPrimes M)ᶜ (Nat.card U) := by
      have hUCompl :
          IsPiNumber (sigmaKappaPrimes M)ᶜ (Nat.card U) := by
        simpa only [MathlibSupport.natCard_subgroupOf_eq hUM] using
          hU.hall_U.isPiNumber_card
      apply hUCompl.mono
      intro p hpCompl
      change p ∉ kappaPrimes M
      intro hpKappa
      exact hpCompl (Or.inr hpKappa)
    have hAKappaCompl :
        IsPiNumber (kappaPrimes M)ᶜ (Nat.card A) := by
      let SM : Subgroup M := (sigmaCore M).subgroupOf M
      let UM : Subgroup M := U.subgroupOf M
      have hSMnormal : SM.Normal := by
        simpa [SM] using sigmaCore_normal M
      have hSMpi : IsPiNumber (kappaPrimes M)ᶜ (Nat.card SM) := by
        rw [MathlibSupport.natCard_subgroupOf_eq (sigmaCore_le M)]
        exact hSigmaKappaCompl
      have hUMpi : IsPiNumber (kappaPrimes M)ᶜ (Nat.card UM) := by
        rw [MathlibSupport.natCard_subgroupOf_eq hUM]
        exact hUKappaCompl
      rw [← MathlibSupport.natCard_subgroupOf_eq hAM]
      change IsPiNumber (kappaPrimes M)ᶜ
        (Nat.card ((sigmaCore M ⊔ U).subgroupOf M))
      rw [Subgroup.subgroupOf_sup (sigmaCore_le M) hUM]
      exact isPiNumber_card_sup_of_normal_left hSMnormal hSMpi hUMpi
    have hcopAK : Nat.Coprime (Nat.card A) (Nat.card K) := by
      apply hAKappaCompl.coprime_compl
      have hKpi : IsPiNumber (kappaPrimes M) (Nat.card K) := by
        simpa only [MathlibSupport.natCard_subgroupOf_eq hKM] using
          hK.isPiNumber_card
      simpa only [compl_compl] using hKpi
    have hdisDK : Disjoint D K := by
      rw [hderEq]
      exact Subgroup.disjoint_of_coprime_natCard hcopAK
    have hDM : D ≤ M := by
      dsimp [D]
      exact Subgroup.map_subtype_le _
    have hDnormal : (D.subgroupOf M).Normal := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).mpr
      dsimp only [D]
      rw [Subgroup.map_subtype_commutator]
      exact Subgroup.normalizer_commutator_ge_left M M
    refine ⟨hDM, hKM, hDnormal, ?_⟩
    letI : (D.subgroupOf M).Normal := hDnormal
    have hdisSub :
        Disjoint (D.subgroupOf M) (K.subgroupOf M) :=
      subgroupOf_disjoint_of_ambient_pType hDM hKM hdisDK
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisSub
    rw [← Subgroup.normal_mul]
    have hsup : D ⊔ K = M := by
      rw [hderEq]
      exact hM_eq_AK.symm
    rw [← Subgroup.subgroupOf_sup hDM hKM, hsup]
    ext x
    simp

  /- `MNX` has one element, denoted `Mstar`; this is the partner different
  from `M`. -/
  have hMNXnonempty : MNX.Nonempty := lineNormalizerMaximals_nonempty hKne
  obtain ⟨Mstar, hMstarMNX⟩ := hMNXnonempty
  have hMNXsingle : MNX = {Mstar} := by
    have hMstarMX : Mstar ∈ MX := Or.inr hMstarMNX
    have hpair := hMXpair
    ext L
    constructor
    · intro hL
      have hLMX : L ∈ MX := Or.inr hL
      have hMMX : M ∈ MX := by simp [MX]
      rw [hpair] at hLMX hMstarMX hMMX
      apply Set.mem_singleton_iff.mpr
      by_contra hne
      have hML : M ≠ L := by
        intro heq
        exact hMnotMNX (heq.symm ▸ hL)
      have hMMstar : M ≠ Mstar := by
        intro heq
        exact hMnotMNX (heq.symm ▸ hMstarMNX)
      rcases hMMX with hMMi | hMMj <;>
        rcases hLMX with hLMi | hLMj <;>
        rcases hMstarMX with hSMi | hSMj <;>
        simp_all
    · intro hL
      simpa using hL ▸ hMstarMNX
  have hMstarMX : Mstar ∈ MX := Or.inr hMstarMNX
  have hMstarP := (hMXspec hMstarMX).1
  have hMstarHall := (hMXspec hMstarMX).2.2
  have hMstarNotConj : ¬ AreConjugateSubgroups M Mstar := by
    have hMstarLine := hMstarMNX
    change Mstar ∈ lineNormalizerMaximals K at hMstarLine
    simp only [lineNormalizerMaximals, Set.mem_iUnion] at hMstarLine
    rcases hMstarLine with ⟨X, ⟨p, hp, hX⟩, hmaxNX⟩
    exact (pType_symmetric_normalizer hM hKM hK hp hX hmaxNX).not_conjugate
  have hMstarNeM : Mstar ≠ M := by
    intro heq
    apply hMstarNotConj
    rw [heq]
    exact areConjugateSubgroups_refl M
  have hKs_eq_Kstar : Ks = KAt Mstar := by
    have hpair := hMXpair
    have hMmem : M ∈ MX := by simp [MX]
    rw [hpair] at hMmem hMstarMX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hMmem hMstarMX
    rcases hMmem with (hMMi | hMMj) <;>
      rcases hMstarMX with (hSMi | hSMj)
    · exact (hMstarNeM (hSMi.trans hMMi.symm)).elim
    · rw [← hMMi, ← hSMj] at hKsMi_eq_KMj
      simpa only [hKsAtM] using hKsMi_eq_KMj
    · rw [← hMMj, ← hSMi] at hKsMj_eq_KMi
      simpa only [hKsAtM] using hKsMj_eq_KMi
    · exact (hMstarNeM (hSMj.trans hMMj.symm)).elim
  have hKsMstar_eq_K : KsAt Mstar = K := by
    have hpair := hMXpair
    have hMmem : M ∈ MX := by simp [MX]
    rw [hpair] at hMmem hMstarMX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hMmem hMstarMX
    rcases hMmem with (hMMi | hMMj) <;>
      rcases hMstarMX with (hSMi | hSMj)
    · exact (hMstarNeM (hSMi.trans hMMi.symm)).elim
    · rw [← hMMi, ← hSMj] at hKsMj_eq_KMi
      simpa only [hKAtM] using hKsMj_eq_KMi
    · rw [← hMMj, ← hSMi] at hKsMi_eq_KMj
      simpa only [hKAtM] using hKsMi_eq_KMj
    · exact (hMstarNeM (hSMj.trans hMMj.symm)).elim
  have hKstarLe : Ks ≤ Mstar := by
    rw [hKs_eq_Kstar]
    exact (hMXspec hMstarMX).2.1
  have hHallKstarKappa :
      IsHall (kappaPrimes Mstar) (Ks.subgroupOf Mstar) := by
    simpa [hKs_eq_Kstar] using hMstarHall
  have hHallKstarSigma :
      IsHall (sigmaPrimes M) (Ks.subgroupOf Mstar) := by
    have hKsSigma : IsPiNumber (sigmaPrimes M) (Nat.card Ks) :=
      (sigmaCore_isPiNumber M).of_dvd
        (Subgroup.card_dvd_of_le (centralizerWithin_le_left _ _))
    obtain ⟨Y, hKsY, hYMstar, hYHall⟩ :=
      MathlibSupport.exists_ambient_isHall_ge_of_isSolvable hKstarLe
        (mmax_sol hMstarP.1) (sigmaPrimes M) hKsSigma
    have hYMs : Y ≤ sigmaCore M := by
      have hYsigma : IsPiNumber (sigmaPrimes M) (Nat.card Y) := by
        simpa only [MathlibSupport.natCard_subgroupOf_eq hYMstar] using
          hYHall.isPiNumber_card
      apply hs.sigma_inter_Kstar_le hYsigma
      change Y ⊓ Ks ≠ ⊥
      simpa only [inf_eq_right.mpr hKsY] using hKsne
    have hKMsSigma : K ≤ sigmaCore Mstar := by
      rw [← hKsMstar_eq_K]
      exact centralizerWithin_le_left _ _
    have hMnormSigma :
        M ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (sigmaCore_le M)).mp (sigmaCore_normal M)
    have hMstarNormSigma :
        Mstar ≤ Subgroup.normalizer (sigmaCore Mstar : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (sigmaCore_le Mstar)).mp (sigmaCore_normal Mstar)
    have hcommM : ⁅Y, K⁆ ≤ sigmaCore M :=
      (Subgroup.commutator_mono hYMs hKM).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hMnormSigma)
    have hcommMstar : ⁅Y, K⁆ ≤ sigmaCore Mstar :=
      (Subgroup.commutator_mono hYMstar hKMsSigma).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.mp
          hMstarNormSigma)
    have hSigmaDisjoint :
        Disjoint (sigmaPrimes M) (sigmaPrimes Mstar) :=
      sigma_partition hmaxM hMstarP.1 (by
        intro g heq
        exact hMstarNotConj ⟨g, heq⟩)
    have hCoreDisjoint : Disjoint (sigmaCore M) (sigmaCore Mstar) :=
      Subgroup.disjoint_of_coprime_natCard
        ((sigmaCore_isPiNumber M).coprime_compl
          ((sigmaCore_isPiNumber Mstar).mono (fun q hqMstar hqM ↦
            (Set.disjoint_left.mp hSigmaDisjoint) hqM hqMstar)))
    have hcommBot : ⁅Y, K⁆ = ⊥ := by
      apply le_antisymm ?_ bot_le
      exact (le_inf hcommM hcommMstar).trans
        (disjoint_iff.mp hCoreDisjoint).le
    have hYcentK : Y ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
    have hYKs : Y ≤ Ks := by
      intro y hy
      exact ⟨hYMs hy, hYcentK hy⟩
    have hYeq : Y = Ks := le_antisymm hYKs hKsY
    rw [hYeq] at hYHall
    exact hYHall
  have hDouble : centralizerWithin (sigmaCore Mstar) Ks = K := by
    simpa [KsAt, hKs_eq_Kstar] using hKsMstar_eq_K

  /- After `MNX = {Mstar}`, the cover in the definition of `T` consists
  of precisely `Ks^#` and `K^#`.  This is `defZhat` in the source. -/
  have hMXstar : MX = {M, Mstar} := by
    simp [MX, hMNXsingle]
  have hT_eq : T = pTypeTISet M K := by
    ext x
    change
      (x ∈ subgroupNonidentity Z ∧
          x ∉ ⋃ Mi ∈ MX, subgroupNonidentity (KsAt Mi)) ↔
        (x ∈ Z ∧ x ∉ (K : Set G) ∪ (Ks : Set G))
    constructor
    · rintro ⟨hxZsharp, hxnone⟩
      rcases mem_subgroupNonidentity.mp hxZsharp with ⟨hxZ, hx1⟩
      refine ⟨hxZ, ?_⟩
      rintro (hxK | hxKs)
      · apply hxnone
        simp only [Set.mem_iUnion]
        exact ⟨Mstar, hMstarMX, mem_subgroupNonidentity.mpr
          ⟨hKsMstar_eq_K.symm ▸ hxK, hx1⟩⟩
      · apply hxnone
        simp only [Set.mem_iUnion]
        exact ⟨M, (show M ∈ MX by simp [MX]),
          mem_subgroupNonidentity.mpr ⟨hKsAtM.symm ▸ hxKs, hx1⟩⟩
    · rintro ⟨hxZ, hxnot⟩
      have hxK : x ∉ K := fun hx ↦ hxnot (Or.inl hx)
      have hxKs : x ∉ Ks := fun hx ↦ hxnot (Or.inr hx)
      have hx1 : x ≠ 1 := by
        intro hx
        exact hxK (hx ▸ K.one_mem)
      refine ⟨mem_subgroupNonidentity.mpr ⟨hxZ, hx1⟩, ?_⟩
      intro hcover
      simp only [Set.mem_iUnion] at hcover
      rcases hcover with ⟨Mi, hMi, hxi⟩
      have hcases : Mi = M ∨ Mi = Mstar := by
        rw [hMXstar] at hMi
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hMi
      rcases hcases with rfl | rfl
      · exact hxKs (hKsAtM ▸ (mem_subgroupNonidentity.mp hxi).1)
      · exact hxK (hKsMstar_eq_K ▸ (mem_subgroupNonidentity.mp hxi).1)

  have hOutside : ∀ {g : G}, g ∉ M →
      Disjoint T (M.map (MulAut.conj g).toMonoidHom : Set G) := by
    intro g hg
    apply Set.disjoint_left.2
    intro t htT htg
    have htMixed : t ∈ pTypeTISet M K := by
      rw [← hT_eq]
      exact htT
    have hKcompl :
        IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K) := by
      have hKpi : IsPiNumber (kappaPrimes M) (Nat.card K) := by
        simpa only [MathlibSupport.natCard_subgroupOf_eq hKM] using
          hK.isPiNumber_card
      exact hKpi.mono (kappa_sigma' M)
    have hKsSigma :
        IsPiNumber (sigmaPrimes M) (Nat.card Ks) :=
      (sigmaCore_isPiNumber M).of_dvd
        (Subgroup.card_dvd_of_le (centralizerWithin_le_left _ _))
    let y : G := sigmaComponent M t
    have hyKs : y ∈ Ks := by
      simpa [y, Ks, pTypePartner] using
        sigmaComponent_mem_partner_of_mem_pTypeTISet
          hs.normalizer_direct hKcompl hKsSigma htMixed
    have hy1 : y ≠ 1 := by
      simpa [y, Ks, pTypePartner] using
        sigmaComponent_ne_one_of_mem_pTypeTISet
          hs.normalizer_direct hKcompl hKsSigma htMixed
    have hyMap : y ∈ M.map (MulAut.conj g).toMonoidHom := by
      exact (Subgroup.zpowers_le.mpr htg)
        (primeSetComponent_spec (sigmaPrimes M) t).1
    have hyInf : y ∈
        pTypeCentralizer M K ⊓
          M.map (MulAut.conj g).toMonoidHom := by
      exact ⟨by simpa [Ks, pTypePartner] using hyKs, hyMap⟩
    rw [hs.Kstar_TI_outside g hg] at hyInf
    exact hy1 (by simpa using hyInf)

  have hKappaTau : kappaPrimes M = tau1Primes M := by
    have hDerHall :
        IsHall (kappaPrimes M)ᶜ
          (((_root_.commutator M).map M.subtype).subgroupOf M) := by
      constructor
      · rw [← hDerived.2.2.2.index_eq_card]
        exact hK.isPiNumber_index
      · rw [hDerived.2.2.2.symm.index_eq_card]
        simpa only [compl_compl] using hK.isPiNumber_card
    have hCardM :
        Nat.card M =
          Nat.card (_root_.commutator M) * Nat.card K := by
      calc
        Nat.card M =
            Nat.card
                (((_root_.commutator M).map M.subtype).subgroupOf M) *
              (((_root_.commutator M).map M.subtype).subgroupOf M).index :=
          (((_root_.commutator M).map M.subtype).subgroupOf M).card_mul_index.symm
        _ = Nat.card (_root_.commutator M) * Nat.card K := by
          rw [hDerived.2.2.2.symm.index_eq_card,
            MathlibSupport.natCard_subgroupOf_eq hDerived.1,
            Subgroup.card_map_of_injective M.subtype_injective,
            MathlibSupport.natCard_subgroupOf_eq hKM]
    ext q
    constructor
    · intro hq
      rcases kappa_tau13 hq with hqTau1 | hqTau3
      · exact hqTau1
      · have hqDer : q ∣ Nat.card
            (((_root_.commutator M).map M.subtype).subgroupOf M) := by
          rw [MathlibSupport.natCard_subgroupOf_eq hDerived.1,
            Subgroup.card_map_of_injective M.subtype_injective]
          exact hqTau3.2.2.2.2
        exact (hDerHall.isPiNumber_card hqTau3.1 hqDer hq).elim
    · intro hqTau
      rcases hqTau.2.2.1 with ⟨A, hAM, hA⟩
      have hqA : q ∣ Nat.card A := by
        rw [hA.card_eq, pow_one]
      have hqMcard : q ∣ Nat.card M :=
        hqA.trans (Subgroup.card_dvd_of_le hAM)
      rw [hCardM] at hqMcard
      rcases hqTau.1.dvd_mul.mp hqMcard with hqDer | hqKcard
      · exact (hqTau.2.2.2.2 hqDer).elim
      · apply hK.isPiNumber_card hqTau.1
        rw [MathlibSupport.natCard_subgroupOf_eq hKM]
        exact hqKcard

  have hInf : M ⊓ Mstar = Z := by
    apply le_antisymm
    · have hnormKs : M ⊓ Mstar ≤ Subgroup.normalizer (Ks : Set G) := by
        dsimp only [Ks]
        rw [← inf_sigmaCore_partner_eq hKstarLe hHallKstarSigma]
        have hnormSigma :
            M ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer
            (sigmaCore_le M)).mp (sigmaCore_normal M)
        exact (inf_le_inf hnormSigma Subgroup.le_normalizer).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have hstarStruct := Ptype_structure
        hMstarP hKstarLe hHallKstarKappa
      have hNormStar : normalizerWithin Mstar Ks = Z := by
        have hEq := internalDirectProduct_eq_sup
          hstarStruct.normalizer_direct
        rw [show pTypeCentralizer Mstar Ks = K by exact hDouble] at hEq
        change normalizerWithin Mstar Ks = K ⊔ Ks
        simpa only [sup_comm] using hEq
      exact (le_inf inf_le_right hnormKs).trans_eq hNormStar
    · have hKMstar : K ≤ Mstar := by
        rw [← hDouble]
        exact (centralizerWithin_le_left _ _).trans (sigmaCore_le Mstar)
      exact sup_le
        (le_inf hKM hKMstar)
        (le_inf ((centralizerWithin_le_left _ _).trans (sigmaCore_le M))
          hKstarLe)
  have hCentLeft : ∀ {x : G}, x ∈ K → x ≠ 1 →
      centralizerWithin M (Subgroup.zpowers x) = Z := by
    intro x hxK hx1
    obtain ⟨p, hp, X, hX, hXcycle⟩ :=
      exists_rankOneLineIn_zpowers_of_mem hxK hx1
    letI : Fact p.Prime := ⟨hp⟩
    apply le_antisymm
    · calc
        centralizerWithin M (Subgroup.zpowers x) ≤
            centralizerWithin M X :=
          centralizerWithin_antitone_right hXcycle
        _ ≤ normalizerWithin M X := by
          rintro z ⟨hzM, hzC⟩
          exact ⟨hzM,
            Subgroup.centralizer_le_normalizer (X : Set G) hzC⟩
        _ = normalizerWithin M K :=
          (hs.rankOne_normalizer (p := p) hX).1
        _ = Z := hNormM
    · intro z hzZ
      refine ⟨?_, ?_⟩
      · exact (show M ⊓ Mstar ≤ M from inf_le_left)
          (hInf.symm ▸ hzZ)
      · intro a ha
        have haZ : a ∈ Z :=
          (show K ≤ Z from le_sup_left)
            ((Subgroup.zpowers_le.mpr hxK) ha)
        letI : IsCyclic Z := hZcyclic
        exact congrArg Subtype.val
          (mul_comm (⟨a, haZ⟩ : Z) (⟨z, hzZ⟩ : Z))
  have hCentRight : ∀ {y : G}, y ∈ Ks → y ≠ 1 →
      centralizerWithin Mstar (Subgroup.zpowers y) = Z := by
    intro y hyKs hy1
    obtain ⟨q, hq, Y, hY, hYcycle⟩ :=
      exists_rankOneLineIn_zpowers_of_mem hyKs hy1
    letI : Fact q.Prime := ⟨hq⟩
    have hstarStruct := Ptype_structure hMstarP hKstarLe hHallKstarKappa
    have hNormStar : normalizerWithin Mstar Ks = Z := by
      have hEq := internalDirectProduct_eq_sup hstarStruct.normalizer_direct
      rw [show pTypeCentralizer Mstar Ks = K by exact hDouble] at hEq
      change normalizerWithin Mstar Ks = K ⊔ Ks
      simpa only [sup_comm] using hEq
    apply le_antisymm
    · calc
        centralizerWithin Mstar (Subgroup.zpowers y) ≤
            centralizerWithin Mstar Y :=
          centralizerWithin_antitone_right hYcycle
        _ ≤ normalizerWithin Mstar Y := by
          rintro z ⟨hzMstar, hzC⟩
          exact ⟨hzMstar,
            Subgroup.centralizer_le_normalizer (Y : Set G) hzC⟩
        _ = normalizerWithin Mstar Ks :=
          (hstarStruct.rankOne_normalizer (p := q) hY).1
        _ = Z := hNormStar
    · intro z hzZ
      refine ⟨?_, ?_⟩
      · exact (show M ⊓ Mstar ≤ Mstar from inf_le_right)
          (hInf.symm ▸ hzZ)
      · intro a ha
        have haZ : a ∈ Z :=
          (show Ks ≤ Z from le_sup_right)
            ((Subgroup.zpowers_le.mpr hyKs) ha)
        letI : IsCyclic Z := hZcyclic
        exact congrArg Subtype.val
          (mul_comm (⟨a, haZ⟩ : Z) (⟨z, hzZ⟩ : Z))
  have hCentProduct : ∀ {x y : G}, x ∈ K → x ≠ 1 →
      y ∈ Ks → y ≠ 1 →
      Subgroup.centralizer ({x * y} : Set G) = Z := by
    intro x y hxK hx1 hyKs hy1
    have hxyT : x * y ∈ T := by
      rw [← hT_mixed]
      simp only [Set.mem_iUnion]
      refine ⟨M, Or.inl rfl, ?_⟩
      rw [Set.mem_mul]
      refine ⟨y,
        mem_subgroupNonidentity.mpr ⟨hKsAtM.symm ▸ hyKs, hy1⟩,
        x, mem_subgroupNonidentity.mpr ⟨hKAtM.symm ▸ hxK, hx1⟩, ?_⟩
      exact (hs.normalizer_direct.commute ⟨x, hxK⟩ ⟨y, hyKs⟩).eq.symm
    apply le_antisymm
    · intro z hz
      apply hnormalizedT.centralizerWithin_zpowers_le hxyT
      refine ⟨Subgroup.mem_top z, ?_⟩
      intro a ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hcomm : Commute (x * y) z := by
        rw [Commute]
        exact Subgroup.mem_centralizer_iff.mp hz (x * y)
          (Set.mem_singleton (x * y))
      exact hcomm.zpow_left n |>.eq
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have ha : a = x * y := Set.mem_singleton_iff.mp ha
      subst a
      have hxyZ : x * y ∈ Z :=
        Z.mul_mem ((show K ≤ Z from le_sup_left) hxK)
          ((show Ks ≤ Z from le_sup_right) hyKs)
      letI : IsCyclic Z := hZcyclic
      exact congrArg Subtype.val
        (mul_comm (⟨x * y, hxyZ⟩ : Z) (⟨z, hz⟩ : Z))

  have hRankOneUnique : ∀ {p : ℕ}, p.Prime →
      ∀ {X : Subgroup G}, RankOneLineIn p K X →
      minSimple_max_groups_of (G := G)
        (Subgroup.centralizer (X : Set G) : Set G) = {Mstar} := by
    intro p hp X hX
    letI : Fact p.Prime := ⟨hp⟩
    have hstarStruct := Ptype_structure
      hMstarP hKstarLe hHallKstarKappa
    apply hstarStruct.Kstar_line_unique (p := p)
    exact ⟨by simpa only [hDouble] using hX.1, hX.2⟩

  have hHalf :
      (Nat.card G : ℚ) / 2 <
        ((classSupportWithin (⊤ : Subgroup G) T).ncard : ℚ) := by
    have hdirM := hdirectZ (show M ∈ MX by simp [MX])
    have hTcard : T.ncard =
        (Nat.card K - 1) * (Nat.card Ks - 1) := by
      rw [hT_eq]
      change (cyclicTISet Z K Ks).ncard =
        (Nat.card K - 1) * (Nat.card Ks - 1)
      simpa only [hKAtM, hKsAtM] using
        hdirM.ncard_cyclicTISet
    have hclassCard :
        (classSupportWithin (⊤ : Subgroup G) T).ncard =
          T.ncard * Z.index :=
      ncard_classSupport_normalizedTI hnormalizedT
    have hZcard : Nat.card Z = Nat.card K * Nat.card Ks := by
      simpa [hKAtM, hKsAtM] using hdirM.card_eq_mul_card
    have hZindex : Nat.card Z * Z.index = Nat.card G :=
      Z.card_mul_index
    have hoddK := odd_natCard_subgroup K IsMinSimpleOddGroup.odd_card
    have hoddKs := odd_natCard_subgroup Ks IsMinSimpleOddGroup.odd_card
    obtain ⟨kK, hkK⟩ := hoddK
    obtain ⟨kKs, hkKs⟩ := hoddKs
    have hKgt : 2 < Nat.card K := by
      have hKone := K.one_lt_card_iff_ne_bot.mpr hKne
      omega
    have hKsgt : 2 < Nat.card Ks := by
      have hKsone := Ks.one_lt_card_iff_ne_bot.mpr hKsne
      omega
    have hcop : Nat.Coprime (Nat.card K) (Nat.card Ks) := by
      have hhall := hHallZ (show M ∈ MX by simp [MX])
      have hKcompl :
          IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K) := by
        have htmp := hhall.1.isPiNumber_card
        rw [MathlibSupport.natCard_subgroupOf_eq (hdirectZ
          (show M ∈ MX by simp [MX])).left_le] at htmp
        simpa only [hKAtM] using htmp
      have hKsSigma :
          IsPiNumber (sigmaPrimes M) (Nat.card Ks) := by
        have htmp := hhall.2.isPiNumber_card
        rw [MathlibSupport.natCard_subgroupOf_eq (hdirectZ
          (show M ∈ MX by simp [MX])).right_le] at htmp
        simpa only [hKsAtM] using htmp
      have hKsDoubleCompl :
          IsPiNumber ((sigmaPrimes M)ᶜ)ᶜ (Nat.card Ks) := by
        simpa only [compl_compl] using hKsSigma
      exact hKcompl.coprime_compl hKsDoubleCompl
    have hlarge : 5 ≤ Nat.card K ∨ 5 ≤ Nat.card Ks := by
      by_contra hsmall
      push_neg at hsmall
      have hK3 : Nat.card K = 3 := by omega
      have hKs3 : Nat.card Ks = 3 := by omega
      rw [hK3, hKs3] at hcop
      norm_num at hcop
    have hTcardQ : (T.ncard : ℚ) =
        ((Nat.card K : ℚ) - 1) * ((Nat.card Ks : ℚ) - 1) := by
      rw [hTcard, Nat.cast_mul, Nat.cast_sub (by omega),
        Nat.cast_sub (by omega), Nat.cast_one]
    have hclassCardQ :
        ((classSupportWithin (⊤ : Subgroup G) T).ncard : ℚ) =
          (T.ncard : ℚ) * Z.index := by
      exact_mod_cast hclassCard
    have hZcardQ : (Nat.card Z : ℚ) =
        (Nat.card K : ℚ) * Nat.card Ks := by
      exact_mod_cast hZcard
    have hZindexQ : (Nat.card Z : ℚ) * Z.index = Nat.card G := by
      exact_mod_cast hZindex
    have hindexPos : (0 : ℚ) < Z.index := by
      exact_mod_cast (Nat.pos_of_ne_zero Z.index_ne_zero_of_finite)
    have hcoeff :
        (Nat.card K : ℚ) * Nat.card Ks / 2 <
          ((Nat.card K : ℚ) - 1) * ((Nat.card Ks : ℚ) - 1) := by
      rcases hlarge with hKlarge | hKslarge
      · have hKlargeQ : (5 : ℚ) ≤ Nat.card K := by exact_mod_cast hKlarge
        have hKsThreeQ : (3 : ℚ) ≤ Nat.card Ks := by
          exact_mod_cast (show 3 ≤ Nat.card Ks by omega)
        have hprod : (0 : ℚ) ≤
            ((Nat.card K : ℚ) - 5) * ((Nat.card Ks : ℚ) - 3) :=
          mul_nonneg (sub_nonneg.mpr hKlargeQ) (sub_nonneg.mpr hKsThreeQ)
        nlinarith
      · have hKThreeQ : (3 : ℚ) ≤ Nat.card K := by
          exact_mod_cast (show 3 ≤ Nat.card K by omega)
        have hKslargeQ : (5 : ℚ) ≤ Nat.card Ks := by
          exact_mod_cast hKslarge
        have hprod : (0 : ℚ) ≤
            ((Nat.card K : ℚ) - 3) * ((Nat.card Ks : ℚ) - 5) :=
          mul_nonneg (sub_nonneg.mpr hKThreeQ) (sub_nonneg.mpr hKslargeQ)
        nlinarith
    have hmul := mul_lt_mul_of_pos_right hcoeff hindexPos
    calc
      (Nat.card G : ℚ) / 2 =
          (((Nat.card K : ℚ) * Nat.card Ks) * Z.index) / 2 := by
        rw [← hZindexQ, hZcardQ]
      _ = ((Nat.card K : ℚ) * Nat.card Ks / 2) * Z.index := by
        ring
      _ < ((Nat.card K : ℚ) - 1) *
          ((Nat.card Ks : ℚ) - 1) * Z.index := hmul
      _ = ((classSupportWithin (⊤ : Subgroup G) T).ncard : ℚ) := by
        rw [hclassCardQ, hTcardQ]

  have hP2prime :
      (M ∈ typeP2MaximalSubgroups (G := G) ∧ (Nat.card K).Prime) ∨
      (Mstar ∈ typeP2MaximalSubgroups (G := G) ∧
        (Nat.card Ks).Prime) := by
    rw [hMXstar] at hMiMX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hMiMX
    rcases hMiMX with hMiM | hMiStar
    · subst Mi
      exact Or.inl ⟨hMiP2, by simpa only [hKAtM] using
        hMiTwo.card_K_prime⟩
    · subst Mi
      refine Or.inr ⟨hMiP2, ?_⟩
      simpa only [hKs_eq_Kstar] using hMiTwo.card_K_prime

  /- This is the last paragraph of the source proof, isolated from the
  cardinal induction.  A meeting of the two class supports gives an element
  of `T` lying in a conjugate of the analogous set for `H`.  After conjugating
  `H` and its Hall subgroup, a nontrivial intersection of partner factors
  identifies `H` with one of the two members of `MX = {M,Mstar}`. -/
  have hCapture : ∀ {H L : Subgroup G},
      H ∈ typePMaximalSubgroups (G := G) →
      L ≤ H → IsHall (kappaPrimes H) (L.subgroupOf H) →
      ¬ Disjoint
        (classSupportWithin (⊤ : Subgroup G) (pTypeTISet M K))
        (classSupportWithin (⊤ : Subgroup G) (pTypeTISet H L)) →
      AreConjugateSubgroups M H ∨ AreConjugateSubgroups Mstar H := by
    intro H L hHP hLH hHallL hoverlap
    obtain ⟨t, htT, a, htaS⟩ := classSupport_overlap_witness hoverlap
    let Hc : Subgroup G := H.map (MulAut.conj a).toMonoidHom
    let Lc : Subgroup G := L.map (MulAut.conj a).toMonoidHom
    have hHcP : Hc ∈ typePMaximalSubgroups (G := G) := by
      simpa [Hc] using (PtypeJ H a).mpr hHP
    have hLcHc : Lc ≤ Hc := Subgroup.map_mono hLH
    have hHallLc :
        IsHall (kappaPrimes Hc) (Lc.subgroupOf Hc) := by
      have hkappa : kappaPrimes Hc = kappaPrimes H := by
        ext p
        simpa [Hc] using (kappaJ H a :
          p ∈ kappaPrimes
              (H.map (MulAut.conj a).toMonoidHom) ↔
            p ∈ kappaPrimes H)
      rw [hkappa]
      simpa [Hc, Lc] using
        isHall_subgroupOf_map_conj hLH hHallL (MulAut.conj a)
    have htTc : t ∈ pTypeTISet Hc Lc := by
      have := (mem_pTypeTISet_map_conj_iff H L a
        (a⁻¹ * t * a)).2 htaS
      simpa [Hc, Lc, MulAut.conj_apply, mul_assoc] using this
    let Ls : Subgroup G := pTypePartner Hc Lc
    have hHcStruct := Ptype_structure hHcP hLcHc hHallLc
    have htTlocal : t ∈ T := by
      rw [hT_eq]
      exact htT
    have htZ : t ∈ Z := by
      exact (mem_subgroupNonidentity.mp htTlocal.1).1
    have hLcSigmaCompl :
        IsPiNumber (sigmaPrimes Hc)ᶜ (Nat.card Lc) :=
      (by
        have hLcKappa : IsPiNumber (kappaPrimes Hc) (Nat.card Lc) := by
          simpa only [MathlibSupport.natCard_subgroupOf_eq hLcHc] using
            hHallLc.isPiNumber_card
        exact hLcKappa.mono (kappa_sigma' Hc))
    have hLsSigma :
        IsPiNumber (sigmaPrimes Hc) (Nat.card Ls) :=
      (sigmaCore_isPiNumber Hc).of_dvd
        (Subgroup.card_dvd_of_le (centralizerWithin_le_left _ _))

    /- The source takes the sigma-component of `t` relative to `Hc`, and
    then its sigma-component relative to the P2 member `Mi`.  According as
    the latter is trivial or not, it lies in the `Mj` or `Mi` factor. -/
    let y : G := sigmaComponent Hc t
    have hyLs : y ∈ Ls := by
      exact sigmaComponent_mem_partner_of_mem_pTypeTISet
        hHcStruct.normalizer_direct hLcSigmaCompl hLsSigma htTc
    have hy1 : y ≠ 1 := by
      exact sigmaComponent_ne_one_of_mem_pTypeTISet
        hHcStruct.normalizer_direct hLcSigmaCompl hLsSigma htTc
    have hyZ : y ∈ Z := by
      exact (Subgroup.zpowers_le.mpr htZ)
        (primeSetComponent_spec (sigmaPrimes Hc) t).1
    let ys : G := sigmaComponent Mi y
    have hMeetFactor : ∃ Mk : Subgroup G,
        Mk ∈ MX ∧ Ls ⊓ KsAt Mk ≠ ⊥ := by
      by_cases hys1 : ys = 1
      · refine ⟨Mj, hMjMX, ?_⟩
        have hyKMi : y ∈ KAt Mi :=
          mem_complementary_normalHall_of_sigmaComponent_eq_one
            (hdirectZ hMiMX).left_le (hnormalZ hMiMX).1
            (hHallZ hMiMX).1 hyZ hys1
        have hyKsMj : y ∈ KsAt Mj := by
          simpa [hKsMj_eq_KMi] using hyKMi
        intro hbot
        have : y = 1 := by
          simpa [hbot] using (show y ∈ Ls ⊓ KsAt Mj from ⟨hyLs, hyKsMj⟩)
        exact hy1 this
      · refine ⟨Mi, hMiMX, ?_⟩
        have hysLs : ys ∈ Ls := by
          exact (Subgroup.zpowers_le.mpr hyLs)
            (primeSetComponent_spec (sigmaPrimes Mi) y).1
        have hysKsMi : ys ∈ KsAt Mi :=
          mem_normalHall_sigmaComponent
            (hdirectZ hMiMX).right_le (hnormalZ hMiMX).2
            (hHallZ hMiMX).2 hyZ
        intro hbot
        have : ys = 1 := by
          simpa [hbot] using
            (show ys ∈ Ls ⊓ KsAt Mi from ⟨hysLs, hysKsMi⟩)
        exact hys1 this
    obtain ⟨Mk, hMkMX, hmeet⟩ := hMeetFactor
    obtain ⟨q, hq, Y, hY⟩ :=
      exists_rankOneLineIn_inf_of_ne_bot hmeet
    letI : Fact q.Prime := ⟨hq⟩
    have hYLs : RankOneLineIn q Ls Y :=
      ⟨hY.1.trans inf_le_left, hY.2⟩
    have hYKs : RankOneLineIn q (KsAt Mk) Y :=
      ⟨hY.1.trans inf_le_right, hY.2⟩
    have hMkStruct := Ptype_structure
      (hMXspec hMkMX).1 (hMXspec hMkMX).2.1 (hMXspec hMkMX).2.2
    have huniqH := hHcStruct.Kstar_line_unique hYLs
    have huniqMk := hMkStruct.Kstar_line_unique hYKs
    have hHcEq : Hc = Mk :=
      Set.singleton_injective (huniqH.symm.trans huniqMk)
    have hMkCases : Mk = M ∨ Mk = Mstar := by
      rw [hMXstar] at hMkMX
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hMkMX
    rcases hMkCases with hMkM | hMkStar
    · left
      exact areConjugateSubgroups_of_map_conj_eq
        (by simpa [Hc, hMkM] using hHcEq)
    · right
      exact areConjugateSubgroups_of_map_conj_eq
        (by simpa [Hc, hMkStar] using hHcEq)

  refine ⟨Mstar, ?_⟩
  exact
    { Mstar_typeP := hMstarP
      Mstar_not_conjugate := hMstarNotConj
      rankOne_unique := hRankOneUnique
      Kstar_le_Mstar := by simpa [Ks, pTypePartner] using hKstarLe
      Kstar_hall_kappa := by
        simpa [Ks, pTypePartner] using hHallKstarKappa
      Kstar_hall_sigma := by
        simpa [Ks, pTypePartner] using hHallKstarSigma
      doubleCentralizer := by
        simpa [Ks, pTypePartner] using hDouble
      kappa_eq_tau1 := hKappaTau
      cyclicStructure :=
        { cyclic_join := by simpa [Z] using hZcyclic
          inf_eq_join := by simpa [Z] using hInf
          centralizer_left := by
            intro x hx hx1
            simpa [Z] using hCentLeft (x := x) hx hx1
          centralizer_right := by
            intro y hy hy1
            simpa [Ks, Z, pTypePartner] using
              hCentRight (y := y) hy hy1
          centralizer_product := by
            intro x y hx hx1 hy hy1
            simpa [Ks, Z, pTypePartner] using
              hCentProduct (x := x) (y := y) hx hx1 hy hy1 }
      normalizedTI := by
        simpa [hT_eq, Z] using hnormalizedT
      outside_disjoint := by
        intro g hg
        simpa [hT_eq] using hOutside hg
      half_lt_classSupport := by simpa [hT_eq] using hHalf
      typeP2_prime := by simpa [Ks, pTypePartner] using hP2prime
      support_capture := hCapture
      derived_sdprod := hDerived }

/-! ## Theorem 14.7 and Corollary 14.8 -/

/- The induction parameter is an upper bound for the current exceptional
class support.  If the support attached to `H` is smaller, strong induction
supplies its own embedding and hence its half-cardinality estimate.  If it
is not smaller, the estimate for the current local embedding transfers to
it directly. -/
private theorem pType_embedding_bounded (n : ℕ) :
    ∀ (M K : Subgroup G),
      M ∈ typePMaximalSubgroups (G := G) →
      K ≤ M →
      IsHall (kappaPrimes M) (K.subgroupOf M) →
      (classSupportWithin (⊤ : Subgroup G)
        (pTypeTISet M K)).ncard ≤ n →
      ∃ Mstar : Subgroup G, PTypeEmbedding M K Mstar := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro M K hM hKM hHallK hsize
      obtain ⟨Mstar, hlocal⟩ := pType_local_embedding hM hKM hHallK
      have htrans : ∀ {H : Subgroup G},
          H ∈ typePMaximalSubgroups (G := G) →
            AreConjugateSubgroups M H ∨
              AreConjugateSubgroups Mstar H := by
        intro H hH
        obtain ⟨L, hLH, hHallL⟩ :=
          MathlibSupport.exists_ambient_isHall_of_isSolvable
            (mmax_sol hH.1) (kappaPrimes H)
        let s : ℕ :=
          (classSupportWithin (⊤ : Subgroup G)
            (pTypeTISet H L)).ncard
        have hSHalf :
            (Nat.card G : ℚ) / 2 <
              ((classSupportWithin (⊤ : Subgroup G)
                (pTypeTISet H L)).ncard : ℚ) := by
          by_cases hs : s < n
          · obtain ⟨Hstar, hHembed⟩ :=
              ih s hs H L hH hLH hHallL (by simp [s])
            exact hHembed.half_lt_classSupport
          · have hns : n ≤ s := Nat.le_of_not_gt hs
            have hle :
                (classSupportWithin (⊤ : Subgroup G)
                    (pTypeTISet M K)).ncard ≤ s :=
              hsize.trans hns
            have hleQ :
                ((classSupportWithin (⊤ : Subgroup G)
                    (pTypeTISet M K)).ncard : ℚ) ≤ s := by
              exact_mod_cast hle
            exact hlocal.half_lt_classSupport.trans_le
              (by simpa [s] using hleQ)
        have hoverlap : ¬ Disjoint
            (classSupportWithin (⊤ : Subgroup G) (pTypeTISet M K))
            (classSupportWithin (⊤ : Subgroup G) (pTypeTISet H L)) :=
          not_disjoint_of_two_half_supports
            hlocal.half_lt_classSupport hSHalf
        exact hlocal.support_capture hH hLH hHallL hoverlap
      exact ⟨Mstar, hlocal.withTransitivity htrans⟩

/-- `BGsection14.v: Ptype_embedding`, Bender--Glauberman Theorem 14.7.

The explicit containment `hKM` is the part of MathComp's Hall predicate
which is not carried by Lean's subgroup-internal `IsHall`. -/
theorem Ptype_embedding
    {M K : Subgroup G}
    (hM : M ∈ typePMaximalSubgroups (G := G))
    (hKM : K ≤ M)
    (hK : IsHall (kappaPrimes M) (K.subgroupOf M)) :
    ∃ Mstar : Subgroup G, PTypeEmbedding M K Mstar := by
  let n :=
    (classSupportWithin (⊤ : Subgroup G) (pTypeTISet M K)).ncard
  exact pType_embedding_bounded n M K hM hKM hK (by simp [n])

/-- Camel-case alias for downstream Lean code. -/
theorem pTypeEmbedding
    {M K : Subgroup G}
    (hM : M ∈ typePMaximalSubgroups (G := G))
    (hKM : K ≤ M)
    (hK : IsHall (kappaPrimes M) (K.subgroupOf M)) :
    ∃ Mstar : Subgroup G, PTypeEmbedding M K Mstar :=
  Ptype_embedding hM hKM hK

/-- `BGsection14.v: P1type_trans`, the first half of Corollary 14.8. -/
theorem P1type_trans
    {M H : Subgroup G}
    (hM : M ∈ typeP1MaximalSubgroups (G := G))
    (hH : H ∈ typeP1MaximalSubgroups (G := G)) :
    AreConjugateSubgroups M H := by
  obtain ⟨K, hKM, hHallK⟩ :=
    MathlibSupport.exists_ambient_isHall_of_isSolvable
      (mmax_sol hM.1.1) (kappaPrimes M)
  obtain ⟨Mstar, hEmbed⟩ := Ptype_embedding hM.1 hKM hHallK
  rcases hEmbed.typeP2_prime with hMP2 | hMstarP2
  · exact (hMP2.1.2 hM).elim
  · rcases hEmbed.typeP_transitive hH.1 with hMH | hMstarH
    · exact hMH
    · rcases hMstarH with ⟨g, hHg⟩
      have hMstarP1 : Mstar ∈ typeP1MaximalSubgroups (G := G) :=
        (P1typeJ Mstar g).mp (hHg ▸ hH)
      exact (hMstarP2.1.2 hMstarP1).elim

/-- Camel-case alias for the P1-transitivity corollary. -/
theorem p1TypeTrans
    {M H : Subgroup G}
    (hM : M ∈ typeP1MaximalSubgroups (G := G))
    (hH : H ∈ typeP1MaximalSubgroups (G := G)) :
    AreConjugateSubgroups M H :=
  P1type_trans hM hH

/-- `BGsection14.v: Ptype_trans`, the second half of Corollary 14.8. -/
theorem Ptype_trans
    {M : Subgroup G}
    (hM : M ∈ typePMaximalSubgroups (G := G)) :
    ∃ Mstar : Subgroup G,
      Mstar ∈ typePMaximalSubgroups (G := G) ∧
      ¬ AreConjugateSubgroups M Mstar ∧
      ∀ {H : Subgroup G},
        H ∈ typePMaximalSubgroups (G := G) →
          AreConjugateSubgroups M H ∨
            AreConjugateSubgroups Mstar H := by
  obtain ⟨K, hKM, hHallK⟩ :=
    MathlibSupport.exists_ambient_isHall_of_isSolvable
      (mmax_sol hM.1) (kappaPrimes M)
  obtain ⟨Mstar, hEmbed⟩ := Ptype_embedding hM hKM hHallK
  exact ⟨Mstar, hEmbed.Mstar_typeP, hEmbed.Mstar_not_conjugate,
    hEmbed.typeP_transitive⟩

/-- Camel-case alias for the P-type two-class transitivity corollary. -/
theorem pTypeTrans
    {M : Subgroup G}
    (hM : M ∈ typePMaximalSubgroups (G := G)) :
    ∃ Mstar : Subgroup G,
      Mstar ∈ typePMaximalSubgroups (G := G) ∧
      ¬ AreConjugateSubgroups M Mstar ∧
      ∀ {H : Subgroup G},
        H ∈ typePMaximalSubgroups (G := G) →
          AreConjugateSubgroups M H ∨
            AreConjugateSubgroups Mstar H :=
  Ptype_trans hM

end

end Submission.OddOrder.BG.Section14
