import Submission.OddOrder.Peterfalvi.S15_SAndT_Setup.CountingLayer

/-!
# Canonicalization

Prefix-split from `OddOrder.Peterfalvi.S15_SAndT_Setup.NormEstimates` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# Peterfalvi (13.5)-(13.10) — norm estimate tail

Split from the former monolithic `OddOrder.Peterfalvi.S15_SAndT_Setup` (directory split, issue 0103).
-/
namespace OddOrder.Peterfalvi.S15
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ### Reusable (13.5)–(13.10) atoms

The former `CharacterDegreeData`-parameterized estimate cascade has been retired.  This leaf
keeps only the carrier-independent structural, sharp-set transport, and integrality lemmas used
by the honest `CharacterDegreeCore` relayers in `S15_CaseBEndgameSupply`. -/

/-- The (13.4) case-(b) parameters, unpacked: `d = 1`, `v ≥ 2`, and (for the type-V exclusion
of the counting layer) `vd ≠ 1`. -/
theorem Hypothesis.caseB_vd_facts (hyp : Hypothesis (G := G))
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    hyp.d = 1 ∧ 2 ≤ hyp.v ∧ hyp.v * hyp.d ≠ 1 := by
  have hd1 : hyp.d = 1 := by rw [hyp.d_eq_card_D, hD, Subgroup.card_bot]
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hqp_ge : hyp.q * hyp.q ≤ hyp.q ^ hyp.p := by
    calc hyp.q * hyp.q = hyp.q ^ 2 := (sq hyp.q).symm
      _ ≤ hyp.q ^ hyp.p := Nat.pow_le_pow_right (by omega)
        (by have := hyp.three_le_p; omega)
  have hv2 : 2 ≤ hyp.v := by
    rw [hv, Nat.le_div_iff_mul_le (by omega : 0 < hyp.q - 1)]
    have h3q : 3 * hyp.q ≤ hyp.q * hyp.q := Nat.mul_le_mul_right _ hq3
    omega
  exact ⟨hd1, hv2, by rw [hd1, mul_one]; omega⟩

/- `Hypothesis.eta10_mem_ZIrr` moved up next to the `eta10` definition (issue 2033:
the (1.10) congruence helper cites it). -/

open scoped FiniteInduce in
/-- **`‖η₁₀‖² = 1`** — real content of the 3002-threaded grid: `τ₃` is an isometry
(`tau3_isometry`) and the `ω`-grid is orthonormal (`omega_orthonormal`). -/
theorem Hypothesis.eta10_inner_self_one [Finite G] (hyp : Hypothesis (G := G)) :
    ClassFunction.inner hyp.eta10 hyp.eta10 = 1 := by
  rw [Hypothesis.eta10, hyp.eta_eq_tau_omega, hyp.tau3_isometry.inner_eq,
    hyp.omega_orthonormal]
  simp

open scoped Classical in
/-- **Sharp-set sum transport** (subgroup-of form ↔ ambient form): for `K ≤ L`, a sum over the
nonidentity `K`-members *inside `↥L`* equals the sum over the ambient sharp `K^# ⊂ G`.  The
bridge between the (13.5)/(13.6) engines (stated inside the abstract ambient `↥S` with
`H.subgroupOf S`) and the (13.10) counting layer (stated over `sharpSubgroup K ⊂ G`). -/
theorem sum_apply_erase_one_filter_subgroupOf [Finite G] {M : Type*} [AddCommMonoid M]
    {K L : Subgroup G} [Fintype ↥L] (hKL : K ≤ L) (f : G → M) :
    ∑ x ∈ (Finset.univ.filter (· ∈ K.subgroupOf L)).erase 1, f ↑x
      = ∑ x ∈ (Set.toFinite (sharpSubgroup K)).toFinset, f x := by
  classical
  refine Finset.sum_bij' (fun x _ => (↑x : G))
    (fun y hy => (⟨y, hKL ((Set.Finite.mem_toFinset _).mp hy).1⟩ : ↥L)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx1, hxK⟩ := Finset.mem_erase.mp hx
    rw [Set.Finite.mem_toFinset]
    refine ⟨Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxK).2, ?_⟩
    intro h1
    rw [Set.mem_singleton_iff] at h1
    exact hx1 (Subtype.ext h1)
  · intro y hy
    obtain ⟨hyK, hy1⟩ := (Set.Finite.mem_toFinset _).mp hy
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Subgroup.mem_subgroupOf.mpr hyK⟩⟩
    intro h1
    exact hy1 (by simpa using congrArg (Subtype.val) h1)
  · intro x hx
    rfl
  · intro y hy
    rfl
  · intro x hx
    rfl

/-- **`2u ≤ |P| − 1`** (Peterfalvi (13.2.c) consequence): from the (13.2.e) bound
`u ≤ (p^q − 1)/(p − 1)` (`basic_structure`) and `p ≥ 3`, so `u ≤ (p^q−1)/2`. -/
theorem Hypothesis.two_mul_u_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : 2 * hyp.u ≤ hyp.p ^ hyp.q - 1 := by
  obtain ⟨-, -, -, -, hub, -⟩ := basic_structure hG hyp
  have hp3 := hyp.three_le_p
  have h1 : (hyp.p ^ hyp.q - 1) / (hyp.p - 1) ≤ (hyp.p ^ hyp.q - 1) / 2 :=
    Nat.div_le_div_left (by omega) (by omega)
  have h2 : (hyp.p ^ hyp.q - 1) / 2 * 2 ≤ hyp.p ^ hyp.q - 1 := Nat.div_mul_le_self _ _
  omega

open scoped FiniteInduce in
/-- **Peterfalvi (3.2.d)** (hypothesis-level): a class function of `G` orthogonal to the whole
`η`-grid vanishes on the regular set `Ŵ = W ∖ (W₁ ∪ W₂)` — every irreducible of `G` off the
`σ`-image vanishes on `Ŵ`, and the `η_{ij} = ω_{ij}^{τ₃}` enumerate the image.  Faithful
producer; the honest supply is `S05.eq_zero_of_mem_V_of_inner_chiFam_eq_zero` (proven) through
the spine's `ω`-grid ↔ character-pair identification (`gridEquivE`/`omegaProdChar` — the
issue-2033 threading pattern; the grid here is `Fin q × Fin p`-indexed while the S05 family is
hom-pair-indexed, and the enumerations correspond along `w1CharEquiv`/`chi2enum`). -/
theorem Hypothesis.vanish_of_inner_eta_eq_zero [Finite G] (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ)
    (horth : ∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner (hyp.eta i j) χ = 0)
    {w : G} (hwW : w ∈ hyp.W) (hnot : w ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G)) :
    χ w = 0 := by
  refine hyp.eta_complete_vanish χ (fun i j => ?_) w hwW hnot
  rw [← hyp.eta_eq_tau_omega]
  exact horth i j

                                                             
                                                                                         
                                                                                                   
                                                                                              
                                                                        
                                  
                                                                                 
                                                                       
                                                      
                                                      
                                                                              
           
         
                                                                                          
                                                          
                                                                                        
                                  
                                    
                                                                                           
                                                   
                                  
                       
                                                                                  
                                                    
                                            
                                      
                                          
                                                               
                                          
                           
                                              
                                                                          
                                                                     
                                                                    
           
                                                                        
                                                      
                                                                                               
            
                                                                                         
                                          
                                                            
                                                        
                                                               
                                      
                   
                
                                           
                                                                  
                                                                  
           
                                                                        
            
                                                                                       
                                                                                    
                             
                                                                        
                                                   
                                                                                  
                                                     
                                                             
                                                                     
                                                     
                                                                
              
                                                               
                                                                
                                            
                                                  
                                                  


open scoped Classical in
/-- `F`-parameterized form of `sum_filter_erase_one_normSq_eq` (instance-free interface): any
`Finset` with the sharp-membership characterization works. -/
theorem sum_finset_sharp_normSq_eq {L : Type*} [Group L] [Fintype L]
    {K : Subgroup L} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (F : Finset L) (hF : ∀ x : L, x ∈ F ↔ (x ∈ K ∧ x ≠ 1))
    (f : L → ℂ) (ψ : ClassFunction ↥K ℂ) (hagree : ∀ k : ↥K, f ↑k = ψ k)
    {n : ℕ} (hn : ClassFunction.inner ψ ψ = (n : ℂ)) :
    ∑ x ∈ F, ‖f x‖ ^ 2 = (Nat.card ↥K : ℝ) * (n : ℝ) - ‖f 1‖ ^ 2 := by
  classical
  have hFeq : F = (Finset.univ.filter (· ∈ K)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [hFeq]
  exact sum_filter_erase_one_normSq_eq f ψ hagree hn

open scoped Classical in
/-- `F`-parameterized form of `sum_apply_erase_one_filter_subgroupOf` (instance-free
interface). -/
theorem sum_finset_sharp_transport [Finite G] {M : Type*} [AddCommMonoid M]
    {K L : Subgroup G} [Fintype ↥L] (hKL : K ≤ L)
    (F : Finset ↥L) (hF : ∀ x : ↥L, x ∈ F ↔ ((x : G) ∈ K ∧ x ≠ 1))
    (f : G → M) :
    ∑ x ∈ F, f ↑x = ∑ x ∈ (Set.toFinite (sharpSubgroup K)).toFinset, f x := by
  classical
  have hFeq : F = (Finset.univ.filter (· ∈ K.subgroupOf L)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter, Subgroup.mem_subgroupOf]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [hFeq]
  exact sum_apply_erase_one_filter_subgroupOf hKL f

                                                             
                                                                                        
                                                                                     
                                                                       
                              
                                                                                                
                                                                              
                                                                   
           
                                                                                    
         
                                                                         
                                                                                                        
           
                                            

                                                             
                                                                                                  
                                                                                                       
                                                                                                  
                                                                                        
                                                               
                                                                               
                                                                         
                                                      
                                                                                  
                                              

end OddOrder.Peterfalvi.S15
