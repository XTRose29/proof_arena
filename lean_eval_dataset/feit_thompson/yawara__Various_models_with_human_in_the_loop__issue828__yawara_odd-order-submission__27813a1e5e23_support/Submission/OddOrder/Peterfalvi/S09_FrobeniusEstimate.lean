/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.OddOrder.Peterfalvi.S09_FrobeniusHypothesis78
import Submission.OddOrder.Isaacs.Ch06_FrobeniusActions.OddComplement

/-!
# Peterfalvi (7.8.b) for a Frobenius family — the `ζ`-norm estimate

Downstream of `S09_FrobeniusHypothesis78` (the (7.8) structure `Hypothesis78 G H_i^# L_i`): the
(7.8.b) norm bound `1 - e_i/h_i ≤ zetaNuRhoNormSq` for each Frobenius family member, en route to the
`card_G0_lower_bound` (7.10) character estimate (issue 0044).

Uses the shared representation-theory helper
`inner_induce_conj_eq_zero_of_frobenius_of_odd` for the `⟨ζ_0, ζ̄_0⟩ = 0` input to the
(7.8.a) `⊥ 1_G` fact `coherence_extension_orthogonal_constOne`.
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory
open OddOrder.Peterfalvi.S09.Cert

/-- **The `ρ`-map is restriction, for a TI Dade datum** (trivial local subgroups `H(a) = ⊥`, the
`of_isTISubset` case).  For `a ∈ A`, the `(7.2)` coset average
`χ^ρ(a) = (1/|H(a)|) ∑_{x ∈ H(a)} χ(a·x)` collapses (each `x = 1`, so every summand is `χ(a)`) to
`χ(a)`.  This is what makes two `Hypothesis71`'s built from the *same* TI subset — even via different
`of_isTISubset` expressions — agree on `chiRho` (hence `chiRhoCF`/`chiRhoNormSq`). -/
theorem chiRho_apply_of_trivial_local {G : Type*} [Group G] {A : Set G} {L : Subgroup G}
    [Fintype G] [Invertible (Nat.card G : ℂ)] (H71 : Hypothesis71 G A L)
    (hbot : ∀ (a : G) (ha : a ∈ A), H71.hyp.H ⟨a, ha⟩ = ⊥)
    (χ : ClassFunction G ℂ) {a : L} (ha : (a : G) ∈ A) :
    H71.chiRho χ a = χ (a : G) := by
  classical
  rw [H71.chiRho_of_mem χ ha]
  have hval : ∀ x : ↥(H71.hyp.H ⟨(a : G), ha⟩), χ ((a : G) * (x : G)) = χ (a : G) := by
    intro x
    have hx2 : (x : G) ∈ (⊥ : Subgroup G) := by rw [← hbot (a : G) ha]; exact x.2
    rw [Subgroup.mem_bot.mp hx2, mul_one]
  have hne : (Nat.card (H71.hyp.H ⟨(a : G), ha⟩) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos).ne'
  rw [Finset.sum_congr rfl (fun x _ => hval x), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- **The good-index norm lower bound** (Peterfalvi (7.10), the `hgood` core).  For `χ ∈ Irr G`
orthogonal to `S^ν` with `(β, χ) ≠ 0` (`χ` is a constituent of the (7.8.a) `β`), the (7.8.c.ii)
formula `‖χ^ρ‖² = (|A|/|L|)·(β,χ)·(β,χ)‾` together with integrality `(β,χ) ∈ ℤ` (`β ∈ ℤ[Irr]`,
`χ ∈ Irr`) gives `|(β,χ)|² ≥ 1`, hence `|A|/|L| ≤ ‖χ^ρ‖²`.  This is the per-good-member estimate
`hgood` of the (7.10) `characterEstimateData` assembly. -/
theorem chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero {G : Type*} [Group G] [Fintype G]
    {A : Set G} {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    [Invertible (Nat.card G : ℂ)] (H78 : Hypothesis78 G A L)
    (χ : ClassFunction G ℂ) (hχ_irr : IsIrreducibleCharacter χ)
    (hχ_orth : ∀ i : Fin (H78.hyp76.n + 1), i ≠ H78.ind1H →
      ClassFunction.inner χ (H78.nu (H78.hyp76.zeta i)) = 0)
    (hdiffZ : H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L)
    (hbeta_ne : ClassFunction.inner H78.beta χ ≠ 0) :
    (Nat.card A : ℝ) / (Nat.card ↥L : ℝ)
      ≤ (ClassFunction.inner (H78.hyp76.hyp71.chiRhoCF χ) (H78.hyp76.hyp71.chiRhoCF χ)).re := by
  have heq := H78.chiRho_norm_sq_eq_card_ratio_mul χ hχ_irr hχ_orth
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int
    (H78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr hdiffZ) hχ_irr.mem_ZIrr
  have hβχ : ClassFunction.inner H78.beta χ = (m : ℂ) := hm
  have hm_ne : m ≠ 0 := by
    intro h0
    apply hbeta_ne
    rw [hβχ, h0, Int.cast_zero]
  -- `‖χ^ρ‖² = (|A|/|L|)·m²`, a real number.
  have hstar : star ((m : ℤ) : ℂ) = ((m : ℤ) : ℂ) := by simp
  have hRHS : ((Nat.card A : ℂ) / (Nat.card ↥L : ℂ)) *
        (ClassFunction.inner H78.beta χ * star (ClassFunction.inner H78.beta χ))
      = (((Nat.card A : ℝ) / (Nat.card ↥L : ℝ) * (m : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [hβχ, hstar]
    push_cast
    ring
  rw [heq, hRHS, Complex.ofReal_re]
  -- `|A|/|L| ≤ |A|/|L| · m²`, since `|A|/|L| ≥ 0` and `m² ≥ 1`.
  have hratio_nonneg : (0 : ℝ) ≤ (Nat.card A : ℝ) / (Nat.card ↥L : ℝ) := by positivity
  have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
    have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm_ne
    have h2 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast h1
    nlinarith [sq_abs (m : ℝ), abs_nonneg (m : ℝ)]
  nlinarith [hratio_nonneg, hm2]

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **Peterfalvi (7.8.a) for the `i`-th Frobenius member: `⟨ζ_0^ν, 1_G⟩ = 0`** (`hzeta0nu`, the last
`zetaNuRhoNormSqGeOfDade` input).  The abstract `IsCoherent` does not carry orthogonality to `1_G`,
but it is recovered from the **complex conjugate** `ζ̄_0 = Ind θ̄_0 ∈ S` — a second member of the
*same degree*, distinct from `ζ_0` because `L_i` has odd order (no nontrivial real irreducible), so
`⟨ζ_0, ζ̄_0⟩ = 0` (`inner_induce_conj_eq_zero_of_frobenius_of_odd`).
`coherence_extension_orthogonal_constOne` then forces `⟨ν ζ_0, 1_G⟩ = 0`.  Mirrors
`S14.witness_L_hzeta0nu`; holds for **any** nontrivial `θ_0`. -/
theorem hzeta0nu [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)
    (θ0 : IrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)))
    (hθ0 : θ0 ≠ trivialIrreducibleCharacter ↥((F.H i).subgroupOf (F.L i))) :
    ClassFunction.inner
        ((F.coherence i hodd hnilp C hFrob).extension
          (ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0 : ClassFunction _ ℂ)))
        (Hypothesis71.constOne G) = 0 := by
  classical
  have hoddL : Odd (Nat.card ↥(F.L i)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
  haveI hKnorm : ((F.H i).subgroupOf (F.L i)).Normal := hFrob.isNormal
  -- Introduce `θ̄_0` **opaquely** (via `obtain`, not `let`) carrying only `↑θ̄_0 = (↑θ_0)‾`, so its
  -- coercion is not re-unfolded inside every `induce` coset sum (whnf-budget protection).
  obtain ⟨θ0', hθ0'coe⟩ :
      ∃ t : IrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)),
        (t : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ)
          = (θ0 : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ).conj :=
    ⟨⟨(θ0 : ClassFunction _ ℂ).conj, θ0.isIrreducible.conj⟩, rfl⟩
  have hθ0' : θ0' ≠ trivialIrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)) := by
    intro h
    apply hθ0
    have hcoe : (θ0 : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ).conj
        = trivialClassFunction ↥((F.H i).subgroupOf (F.L i)) := by
      rw [← hθ0'coe]
      have h2 := congrArg
        (fun c : IrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)) =>
          (c : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ)) h
      simpa using h2
    apply Subtype.ext
    show (θ0 : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ)
      = trivialClassFunction ↥((F.H i).subgroupOf (F.L i))
    rw [← ClassFunction.conj_conj (θ0 : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ), hcoe]
    exact trivialClassFunction_isReal
  -- The two members `ζ_0 = Ind θ_0`, `ζ̄_0 = Ind θ̄_0 ∈ S`.
  have hmem0 : ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0 : ClassFunction _ ℂ)
      ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := ⟨θ0, hθ0, rfl⟩
  have hmem0' : ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0' : ClassFunction _ ℂ)
      ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := ⟨θ0', hθ0', rfl⟩
  -- Norms `= 1` (Frobenius), orthogonality to `1_L`.
  have hnorm0 := inner_self_induce_eq_one_of_frobeniusGroup hFrob θ0 hθ0
  have hnorm0' := inner_self_induce_eq_one_of_frobeniusGroup hFrob θ0' hθ0'
  have h1_0 := inner_induce_constOne_eq_zero ((F.H i).subgroupOf (F.L i)) θ0 hθ0
  have h1_0' := inner_induce_constOne_eq_zero ((F.H i).subgroupOf (F.L i)) θ0' hθ0'
  -- `⟨ζ_0, ζ̄_0⟩ = 0` (odd-order Frobenius: `ζ_0` non-real), via the general helper.
  have horth : ClassFunction.inner
      (ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0 : ClassFunction _ ℂ))
      (ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0' : ClassFunction _ ℂ)) = 0 := by
    rw [hθ0'coe]
    exact inner_induce_conj_eq_zero_of_frobenius_of_odd hoddL hFrob θ0 hθ0
  -- The type-I support `A(L_i) = H_i^#`.
  have hAH : OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))
      = (F.H i : Set G) \ {1} := F.sharpImage_subgroupOf_eq i
  -- The equal-degree difference `ζ̄_0 − ζ_0` is `H_i^#`-supported.
  have hdeg' : ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0' : ClassFunction _ ℂ)
        (1 : ↥(F.L i))
      = 1 * ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0 : ClassFunction _ ℂ)
        (1 : ↥(F.L i)) := by
    rw [one_mul, ClassFunction.induce_apply_one, ClassFunction.induce_apply_one]
    congr 1
    rw [hθ0'coe, ClassFunction.conj_apply]
    obtain ⟨m, -, hm⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ0
    rw [hm, star_natCast]
  have hsupp : (ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0' : ClassFunction _ ℂ)
      - ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (θ0 : ClassFunction _ ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) := by
    have hds := induce_diff_support (K := (F.H i).subgroupOf (F.L i)) θ0' θ0 1 hdeg'
    rw [one_smul] at hds
    intro x hx
    have hxd := hds hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hxd
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff (F.H i) hAH x).mpr ⟨hxd.1, hxd.2⟩
  -- The Dade `⊥ 1_G` transport and `ℂ`-linearity of `τ = sib.tau`.
  have htau1 : ∀ φ : ClassFunction ↥(F.L i) ℂ,
      φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) →
      ClassFunction.inner
          ((F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).tau φ)
          (Hypothesis71.constOne G)
        = ClassFunction.inner φ (Hypothesis71.constOne ↥(F.L i)) := by
    intro φ hφ
    rw [show (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).tau φ
        = (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade.dadeMap
          ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ from
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
        (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
        ((F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade.fullDadeIsometryData
          (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).hconj) hφ]
    exact inner_tau_supported_constOne (F.sibleyToHypothesis71 i hodd hnilp C hFrob)
      ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
  have hτ_smul : ∀ (c : ℂ) (x : ClassFunction ↥(F.L i) ℂ),
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).tau (c • x)
        = c • (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).tau x :=
    dadeIntegralCharacterMap_smul_complex
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
      ((F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade.fullDadeIsometryData
        (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).hconj)
  exact coherence_extension_orthogonal_constOne (F.coherence i hodd hnilp C hFrob) hτ_smul htau1
    hmem0 hmem0' hnorm0 hnorm0' horth hsupp h1_0 h1_0'

/-- **The Sibley (7.1) `ρ`-map equals the family (7.1) `ρ`-map** (the (7.8.b)→(7.5) bridge).  Both
`sibleyToHypothesis71 i` (the Dade datum coherence is coherent for) and `hypothesis71 i` (the family
`FamilyHypothesis71` uses) are `of_isTISubset` on the *same* TI subset `H_i^#` (their supports agree
by `sharpImage_subgroupOf_eq`), with trivial local subgroups, so `chiRho` (hence `chiRhoCF`) is
restriction to `H_i^#` for both — they coincide (`chiRho_apply_of_trivial_local`).  This identifies
`H78.zetaNuRhoNormSq` (built on `sibleyToHypothesis71`) with `P.chiRhoNormSq` (built on
`hypothesis71`), the last link from the (7.8.b) bound to the (7.5) family estimate. -/
theorem sibleyToHypothesis71_chiRhoCF_eq [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)
    (χ : ClassFunction G ℂ) :
    (F.sibleyToHypothesis71 i hodd hnilp C hFrob).chiRhoCF χ = (F.hypothesis71 i).chiRhoCF χ := by
  ext a
  rw [Hypothesis71.chiRhoCF_apply, Hypothesis71.chiRhoCF_apply]
  by_cases ha : (a : G) ∈ OddOrder.Peterfalvi.S04.sharp (F.H i : Set G)
  · have haS : (a : G) ∈ OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i)) := by
      rw [F.sharpImage_subgroupOf_eq i]; exact ha
    rw [chiRho_apply_of_trivial_local _ (fun _ _ => rfl) χ haS,
      chiRho_apply_of_trivial_local _ (fun _ _ => rfl) χ ha]
  · have haS : (a : G) ∉ OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i)) := by
      rw [F.sharpImage_subgroupOf_eq i]; exact ha
    rw [(F.sibleyToHypothesis71 i hodd hnilp C hFrob).chiRho_of_not_mem χ haS,
      (F.hypothesis71 i).chiRho_of_not_mem χ ha]

                        
                                                                                                             
                                                                                                   
                                                                                                        
                                                                                                         
                                                                                            
                                                                                                           
                                                                      
                                                                   
                                                                 
                                                                 
                                                               
                             
                                                                                               
                                                                   
                                                   
                                                             
                                                    
           
                                                                      
                                                       
                                             
                                                             
                                             
                                                                
                                                                            
                                                             
                                                                                          
                                            
                                                               
                                                                                         
                                                                                         
                                                                                             
                                                                                               
                                     
                                                                                    
                                                                              
              
                                                       
                                                                                         
                                                                                            
                       
                                                                                         
                                                                                           
           
                                
                                                                                         
                                                                                            
                 
                                
                                                                       
                                           
                                                                                   
                                                           
                                                                      
                                                     
                                                               
                                                           
           
                                                                   
                                                  
        
                                                                     
                                                     
                                                         
                                                               
                     
                                                     
                                                           
                                                                                 
                                                                 
                                                                              
                                    
                                                                 
                                               
                                                   
                                                                                         
           
                                                                      
              
                                                                    
                                                                                         
                                                                            
                                        
                                                                                           
                        
                                                                                           
                             
                                                                                          
                                                                                             
                                                                                         
                                                                
                                                      
                                                                                           
                                                                     
                                                          
                                                                                                        
                                 
                                                                                                  
                       
                                                                                            
                                                                                                  
                                                                          
                                                                                       
                                                                      
                                 
                                                                             
                                                            
                                                             
                                                                   
                                                                                          
                                                  
                                              
                                               
                        
                                                                    
                                                                 
                                                                                 
                                                                             
                                           
                                                             
                                                                
                                                        
                                                                                          
                                                                                                 
                                    
                                                                                 
                                                             
                                    
                                                                                  
                         
                                                        
                                                                               
                                                                         
                       
                                                        
                                                                    
                                                                         
                              
                                                                                                    
                                                                              
                                                            
                      
                                                                                      
                                                            
                                                             
                                                                   
                                                                                          
                                         
                                                                     
               
                                                                                               
                                                                                                     
                                                                                                     
                                                                            
                                            
                                                                              
                                 
                                                                         
                                                 
                                            
                                  
                                                                          
                                                                                              
                                                     
                                                                                                        
                                                                   
                                                                           
                                                                                                 
                                                                                  
                                                                                               
                                               
              
                              
                

                                                                                                      
                                                                                                        
                                                                                           
                                                                                      
                                                                                                 
                                                                                                         
                                      
                                                                          
                                                                   
                                                                 
                                                               
                             
                                                                                               
                                                                   
                                                                                                  
                                                                
                                                                                       
                                                 

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
