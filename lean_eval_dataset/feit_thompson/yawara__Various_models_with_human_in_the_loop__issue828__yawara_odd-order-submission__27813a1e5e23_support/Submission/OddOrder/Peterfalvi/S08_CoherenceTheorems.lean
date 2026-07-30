/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Submission.OddOrder.Peterfalvi.S08_CoherenceCore
import Submission.OddOrder.Peterfalvi.S08_Theorem65c2
import Submission.OddOrder.Peterfalvi.S08_CaseAWeightedEndgame
import Submission.OddOrder.Peterfalvi.S08_PGroupReduction

/-!
# Peterfalvi §8: Some Coherence Theorems

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§8, pp. 30-37.

Active leaf of §8 (the frozen lemma infrastructure lives upstream in
`S08_CoherenceCore.lean`): the (6.8) coherence capstone `sibleySetup_is_coherent`
(now **complete** — `X`-empty / Frobenius / (6.8)(c2) case-A / case-B dispatch, the latter
splitting `W₂ ⊊ H′` (6.8.3 bootstrap) vs `W₂ = H′` (6.8.2 seed)) and the
(7.10)-facing consumer interfaces (`IndChainDecomposition` and the Frobenius-case
constructor).

Reference note: `notes/peterfalvi/s08_coherence_theorems.md`.
-/

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory
open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]


/-- **Peterfalvi (6.8) Theorem.**  Under the faithful Sibley hypotheses
`SibleyDadeHypothesis` (a)/(b)/(c), the set `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` is
coherent: there is an integral isometric extension of the §4 Dade map `τ` from `Z[S, H^#]` to
`Z[S]` (`hyp.CoherenceTarget = IsCoherent hyp.tau S H^#`).

The proof dispatches on `hyp.cases`: the `X`-empty (abelian) branch is the `Y`-coherence
`coherenceTarget_of_Xset_empty`; the `X`-nonempty branch splits Frobenius
(`nonempty_coherent_S_of_frobenius`) vs (6.8)(c2) certain-type, where the (6.5) reduction makes
`H` a `p`-group and the (6.8.A/B) split on `Z(H) ∩ W₂` routes to the case-A producer
(`nonempty_coherent_S_caseA_of_c2`) or the case-B dispatch: `W₂ ⊊ H′` uses the (6.8.3) FPF
bootstrap (`nonempty_coherent_S_caseB_of_c2`), `W₂ = H′` uses the (6.8.2) seed directly
(`nonempty_coherent_S_caseB_edge`, since then `S = X(W₂) ∪ Y`).  Completed 2026-06-20; this was
one of the two sorries blocking §9 (7.10) `card_G0_lower_bound`
(`issues/0046-peterfalvi-s08-6-8-coherence.md`).

`noncomputable def` (not `theorem`) because `CoherenceTarget` (an `IsCoherent`) carries the
extension map `ν` as data, living in `Type`, not `Prop`. -/
noncomputable def sibleySetup_is_coherent {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (hyp : SibleyDadeHypothesis G L H) : hyp.CoherenceTarget := by
  haveI := hyp.H_normal
  by_cases hXe : hyp.Xset ⁅H, H⁆ = ∅
  · -- `X`-empty (abelian) branch: `S = Y`, discharged by the `Y`-coherence `coherentYset`.
    exact hyp.coherenceTarget_of_Xset_empty hXe
  · -- `X`-nonempty branch: dispatch on `hyp.cases` (Frobenius / (6.8)(c2) certain-type).
    have hXne : (hyp.Xset ⁅H, H⁆).Nonempty := Set.nonempty_iff_ne_empty.mpr hXe
    refine Nonempty.some ?_
    rcases hyp.cases with hF | ⟨h46, _hdade, hHK, hW1, hprime, hW2comm, hcop⟩
    · -- (c1) Frobenius
      exact nonempty_coherent_S_of_frobenius hyp hF hXne
    · -- (c2) certain-type: reduce to `H` a `p`-group ((6.5)), case-split (6.8.A/B) on `Z(H) ∩ W₂`.
      haveI : Finite ↥h46.W1 := inferInstance
      haveI : NeZero (Nat.card h46.W1) := ⟨Nat.card_pos.ne'⟩
      haveI : Invertible (Nat.card ↥h46.K : ℂ) := by
        have h : (Nat.card ↥h46.K : ℂ) = (Nat.card ↥H : ℂ) := by rw [hHK]
        rw [h]; infer_instance
      haveI : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
      haveI : Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ) :=
        invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
      haveI : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
      haveI : Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ) :=
        invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
      have hW2H : h46.W2 ≤ H := hW2comm.trans (by
        rw [Subgroup.commutator_le]; intro a ha b _hb; rw [commutatorElement_def]
        exact H.mul_mem (H.mul_mem (H.mul_mem ha _hb) (H.inv_mem ha)) (H.inv_mem _hb))
      by_contra hncoh
      have hbound := abelianization_card_le_of_not_coherent_c2 hyp h46 hHK hW1 hncoh
      have hsplit := caseAB_split_of_c2 h46 hW2H hprime
      refine hncoh (nonempty_coherent_S_of_c2_of_branches hyp h46 hHK hW1 hW2comm hcop hbound hsplit
        ?caseA ?caseB)
      case caseA =>
        intro p hp hHp hA
        refine nonempty_coherent_S_caseA_of_c2 hyp h46 hHK hW1
          (commutator_ne_bot_of_Xset_commutator_nonempty hyp hXne) ?_ hp
          (three_le_of_isPGroup_H hyp hp hHp) hHp
        rw [inf_comm]; exact disjoint_iff.mp hA
      case caseB =>
        intro p hp hHp hB
        haveI : Fintype ↥H := Fintype.ofFinite _
        haveI : Invertible (Nat.card ↥h46.W2 : ℂ) :=
          invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
        haveI : Fintype ↥(h46.W2.subgroupOf H) := Fintype.ofFinite _
        haveI : Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ) :=
          invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
        have hW2cenL : h46.W2 ≤ Subgroup.center ↥L := caseB_W2_le_center_L hyp h46 hW1 hW2H hB
        haveI : h46.W2.Normal := ⟨fun w hw g => by
          have hc : g * w = w * g := Subgroup.mem_center_iff.mp (hW2cenL hw) g
          have hgw : g * w * g⁻¹ = w := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
          rw [hgw]; exact hw⟩
        have hderiv : h46.W2.subgroupOf H ≤ commutator ↥H := by
          rw [← commutator_subgroupOf_self]
          exact fun x hx => Subgroup.mem_subgroupOf.mpr (hW2comm (Subgroup.mem_subgroupOf.mp hx))
        have hW2Hne : h46.W2.subgroupOf H ≠ ⊥ := by
          rw [← (h46.W2.subgroupOf H).one_lt_card_iff_ne_bot,
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2H).toEquiv]
          exact hprime.one_lt
        have hXne' : (hyp.Xset h46.W2).Nonempty :=
          Xset_nonempty_of_subgroupOf_ne_bot_weighted hyp hW2Hne
        by_cases hWMgt : 1 < (h46.W2.subgroupOf H).relIndex (commutator ↥H)
        · exact nonempty_coherent_S_caseB_of_c2 hyp h46 hHK hW1 hW2H hcop hp hHp hprime hW2comm hB
            hWMgt hXne'
        · -- edge `W₂ = H′ = ⁅H,H⁆`: `relIndex = 1`, so `W₂.subgroupOf H = commutator H`.
          have hHHle : (⁅H, H⁆ : Subgroup ↥L) ≤ H := by
            rw [Subgroup.commutator_le]; intro a ha b _hb; rw [commutatorElement_def]
            exact H.mul_mem (H.mul_mem (H.mul_mem ha _hb) (H.inv_mem ha)) (H.inv_mem _hb)
          have hr1 : (h46.W2.subgroupOf H).relIndex (commutator ↥H) = 1 := by
            have hne0 : (h46.W2.subgroupOf H).relIndex (commutator ↥H) ≠ 0 := by
              haveI : Finite ↥(commutator ↥H) := inferInstance
              exact Subgroup.index_ne_zero_of_finite
            have hle1 : (h46.W2.subgroupOf H).relIndex (commutator ↥H) ≤ 1 := Nat.not_lt.mp hWMgt
            omega
          have hge : commutator ↥H ≤ h46.W2.subgroupOf H := Subgroup.relIndex_eq_one.mp hr1
          have hsubeq : h46.W2.subgroupOf H = commutator ↥H := le_antisymm hderiv hge
          have hcardeq : Nat.card ↥h46.W2 = Nat.card ↥(⁅H, H⁆ : Subgroup ↥L) := by
            rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2H).toEquiv,
              ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHHle).toEquiv,
              hsubeq, commutator_subgroupOf_self]
          have hWeq : h46.W2 = ⁅H, H⁆ := Subgroup.eq_of_le_of_card_ge hW2comm hcardeq.ge
          exact nonempty_coherent_S_caseB_edge hyp h46 hHK hW1 hW2H hB hderiv hcop hp hHp hprime
            hW2comm hW2cenL hWeq hXne'

/-- **Peterfalvi (6.8) → (7.10) consumer interface.**
A degree-scaled `Z`-chain decomposition: given a coherence input `τ` on `(S, A)`
and an orthonormal family `ζ : Fin n → ClassFunction L ℂ` in `S` with explicit
integer degree ratios `d : Fin n → ℤ` (`d 0 = 1`), the family of images
`χ t = ν (ζ t)` under the coherence extension `ν` is orthonormal, and
`τ (ζ t - d t • ζ 0) = χ t - d t • χ 0`.

This packages the orthonormal-subsets-with-Ind-equation language used in the
(7.10) proof (see `references/peterfalvi/04.9_*.mmd` L133-135). -/
structure IndChainDecomposition
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G)
    {n : ℕ} [NeZero n]
    (ζ : Fin n → ClassFunction L ℂ) (d : Fin n → ℤ)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- The orthonormal output family `χ_t = ν(ζ_t)` in `ClassFunction G ℂ`. -/
  χ : Fin n → ClassFunction G ℂ
  /-- Each `χ_t` has norm `1`. -/
  norm_one : ∀ t, ClassFunction.inner (χ t) (χ t) = 1
  /-- Distinct indices give orthogonal `χ`. -/
  pairwise_inner_zero :
    ∀ ⦃t u : Fin n⦄, t ≠ u → ClassFunction.inner (χ t) (χ u) = 0
  /-- The reference index has trivial scaling: `d 0 = 1`. -/
  d_zero : d 0 = 1
  /-- The Ind equation: `τ(ζ_t - d_t · ζ_0) = χ_t - d_t · χ_0`. -/
  image_eq :
    ∀ t, τ (ζ t - (d t) • ζ 0) = χ t - (d t) • χ 0

namespace IndChainDecomposition

variable {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
variable [Fintype L] [Fintype G]
variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
variable {n : ℕ} [NeZero n]

/-- The Ind-chain decomposition vanishes at the reference index: for `t = 0`,
`τ(ζ 0 - d 0 · ζ 0) = 0`. -/
@[simp] theorem image_eq_zero
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) :
    τ (ζ 0 - (d 0) • ζ 0) = 0 := by
  rw [data.d_zero, one_smul, sub_self, map_zero]

                                                                                 
                       
                        
                                                            
                                                                            
                                                                              
                      
            
                                  
                                                  

/-- The weighted output sum `∑ d_t χ_t` used in Peterfalvi (7.10). -/
noncomputable def weightedOutput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (data : IndChainDecomposition (L := L) (G := G) τ ζ d) : ClassFunction G ℂ :=
  ∑ t : Fin n, (d t : ℂ) • data.χ t

/-- The integral weighted source difference `∑ d_t (ζ_t - d_t ζ_0)` used in Peterfalvi (7.10). -/
noncomputable def weightedDifferenceInput
    {ζ : Fin n → ClassFunction L ℂ} {d : Fin n → ℤ}
    (_data : IndChainDecomposition (L := L) (G := G) τ ζ d) : ClassFunction L ℂ :=
  ∑ t : Fin n, (d t) • (ζ t - (d t) • ζ 0)

                                                        
                                
                                                            
                                                                          
                                                                           
           
                                      
             
                                                                                    
                                                               
                                             
                                                                                                
                        
              
                                          
                                                      
                                                                
      

                                                                           
                                           
                                                            
                                                              
                                                                 
                                          
           
                                     
                                           
                                    
                                                
                               
             
      

                                                                           
                   
                                              
                                                            
                                                              
                                                                      
                                          
           
                                                               
                                           
                                                                 
             
                            

                                                                                   
             
                                           
                                                            
                                                              
                                                                                
           
                                                  
                                                                                  
                                                                      
                                                              
                                        
                    
            
                        

                                                                                     
                                     
                                                            
                                                              
                                     
                                                                      
           
                                       
                                           
                                 

                                                                                        
                                   
                                                                                
                                                            
                                                              
                                     
                                                                                
           
                                         
       
                             
                                                   
                                                                       
           
                                                                               
                                                        
                                                                                 
        
                                                                        
                                   
      
                                                              
                                                                                          
                                                       
                                                    
                                                            
                                     
                                                    
                                                              
                                 
                                                        
                                                              
             
                                                      
                                                              
                                             

                                                                     
                                                    
                                                            
                                                              
                                                                       
                                              
           
                                                          
                                          
                                                    
                                                     
                      
                                             
                               
                                                                                    
                                                                   
                                                                                      
                
          

                                                                           
                                                                    
                                                            
                                                              
                                                                       
                                                                           
                                                        
                                             

                                                                                 
                                                                         
                                                            
                                                              
                                                                            
                                              
                                                                        
                                                                                

                                                                                     
                                                              
                                                            
                                                              
                                                                                      
                                                                             
                                                       
                                                          
          

                                                             
                                                                              
                                                            
                                                              
                                     
                           
                                                                                       
                                                                                    
                                             

/-- Construct an `IndChainDecomposition` from a coherence input `hτ : IsCoherent τ S A`
together with the membership `ζ_t ∈ S`, the orthonormality of the input family `ζ`,
and the support of each scaled difference `ζ_t - d_t · ζ_0` in `Z[S, A]`.

The orthonormality of the images `χ_t = ν(ζ_t)` uses the **lattice-relative**
isometry `hτ.extension_inner_eq` on the generators `ζ_t ∈ S ⊆ Z[S] = zSpan S`
(`Submodule.subset_span`); this is all the weakened `IsCoherent` interface
supplies, and all it needs to. -/
noncomputable def ofIsCoherent
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    (hτ : OddOrder.Peterfalvi.S07.IsCoherent (L := L) (G := G) τ S A)
    {ζ : Fin n → ClassFunction L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ S)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u → ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A) :
    IndChainDecomposition (L := L) (G := G) τ ζ d where
  χ t := hτ.extension (ζ t)
  norm_one t := by
    rw [hτ.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem t)), hζ_norm]
  pairwise_inner_zero t u htu := by
    rw [hτ.extension_inner_eq _ _ (Submodule.subset_span (hζ_mem t))
      (Submodule.subset_span (hζ_mem u)), hζ_pairwise htu]
  d_zero := hd_zero
  image_eq t := by
    rw [← hτ.extends_on_supported _ (hsupp t), LinearMap.map_sub, map_zsmul]


end IndChainDecomposition

namespace SibleyDadeHypothesis

/-- **(6.8.1) → (7.10), Frobenius case:** an `IndChainDecomposition` from the
base-anchor common-index p-power X-chain data and generator-level `τ₃` glue.

This is the S09-facing consumer form of the Frobenius/c1 capstone: it first builds the full
`hyp.CoherenceTarget` using the base-anchor X-chain constructor and final generator-level glue, then
turns that coherence witness into the `IndChainDecomposition` package used by the §9 weighted-sum
argument. -/
noncomputable def
    indChainDecomposition_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty)
    (hstepData : ∀
      (pair : ℕ → ClassFunction ↥L ℂ × ClassFunction ↥L ℂ) (N : ℕ)
      (χs : ℕ → IrreducibleCharacter ↥L),
      (∀ i, i < N → (pair i).1 = (χs i : ClassFunction ↥L ℂ)) →
      (∀ i, i < N → (pair i).2 = (χs i : ClassFunction ↥L ℂ).conj) →
      (∀ j, j < N → OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j ⊆
        hyp.Xset ⁅H, H⁆) →
      (∀ j, j < N → Disjoint (OddOrder.Peterfalvi.S07.pairSet (L := ↥L) pair j)
        (OddOrder.Peterfalvi.S07.pairUnion (L := ↥L) (hyp.xBaseBlock ⁅H, H⁆) pair j)) →
      (∀ j, j + 1 < N →
        (OddOrder.Peterfalvi.S03.characterDegree (pair j).1).re ≤
          (OddOrder.Peterfalvi.S03.characterDegree (pair (j + 1)).1).re) →
      ∀ i, i < N →
        PairUnionBaseAnchorCommonIndexPrimePowerStepData hyp
          (Z := ⁅H, H⁆) (pair := pair) (i := i) (χs := χs))
    (ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hagreeX : ∀ x ∈ hyp.Xset ⁅H, H⁆,
      ν x =
        (hyp.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius
          hF hXne hstepData).extension x)
    (hagreeY : ∀ y ∈ hyp.Yset, ν y = hyp.coherentYset.extension y)
    (hmixed : ∀ x ∈ hyp.Xset ⁅H, H⁆, ∀ y ∈ hyp.Yset,
      ClassFunction.inner (ν x) (ν y) = ClassFunction.inner x y)
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (hyp.Xset ⁅H, H⁆ ∪ hyp.Yset)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ⊆
        Submodule.span ℤ
          (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (hyp.Xset ⁅H, H⁆)
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∪
          OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.Yset
            (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    {n : ℕ} [NeZero n] {ζ : Fin n → ClassFunction ↥L ℂ}
    (hζ_mem : ∀ t, ζ t ∈ hyp.S)
    (hζ_norm : ∀ t, ClassFunction.inner (ζ t) (ζ t) = 1)
    (hζ_pairwise : ∀ ⦃t u : Fin n⦄, t ≠ u → ClassFunction.inner (ζ t) (ζ u) = 0)
    {d : Fin n → ℤ} (hd_zero : d 0 = 1)
    (hsupp : ∀ t, ζ t - (d t) • ζ 0 ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) hyp.S
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) :
    IndChainDecomposition (L := ↥L) (G := G) hyp.tau ζ d := by
  exact IndChainDecomposition.ofIsCoherent
    (hyp.coherentS_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner
      hF hXne hstepData ν hagreeX hagreeY hmixed hgen)
    hζ_mem hζ_norm hζ_pairwise hd_zero hsupp

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08
