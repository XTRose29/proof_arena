/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Submission.OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7C_ThompsonPComplementFinal

/-!
# Isaacs FGT Ch.7 (Thompson subgroup) — S7D part 1: Burnside p^a q^b setup (Thm 7.8 stmt, scaffolding, Steps 2-9 decomp, faithful-action bridge) (pp. 219-222)
-/

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement
open scoped Pointwise
open scoped IsMulCommutative -- rc2: IsMulCommutative→CommGroup (for IsNilpotent) now scoped

variable {G : Type*} [Group G]

/-! ## §7D: Burnside `p^a q^b` (pp. 219-222) -/


/-! ### Thm 7.8 — Burnside `p^a q^b` ⇒ solvable (conditional on 9-step argument)

**Isaacs Thm 7.8** (mmd L3955):

> `|G| = p^a q^b` ⇒ G solvable.

**character 不使用** (Goldschmidt + Bender + Matsuyama, 9 Step proof).

**先行 dep**: Thm 7.6 normal-J + Ch.2 Thm **2.13 Baer** ✅ + Ch.4 Thm **4.33** (p-local).

BG/Peterfalvi 直接被引用無いので最後着手. Phase 1 完成度のため必須 (BG L2633 で
"we can obtain Burnside's `p^a q^b` very easily now" として言及). -/

/-! ### §7D scaffolding — `IsPCentral`, `IsPType`, helper lemmas

We formalize the supporting machinery of Isaacs' §7D proof.  These definitions
are local to §7D (Burnside `p^a q^b`); the term "p-central element" appears
informally in the textbook on p.220 and does not have a mathlib analog. -/

/-- **Isaacs p.220** (definition of *p-central element*).

`x` is `p`-central if it is a nonidentity element of the center of some Sylow
`p`-subgroup of `G`.  Used in §7D Steps 4-9.

The condition is phrased via `(Subgroup.center P).map P.subtype` so that the
membership predicate lives in the ambient group `G`. -/
def IsPCentral (p : ℕ) {G : Type*} [Group G] (x : G) : Prop :=
  x ≠ 1 ∧ ∃ P : Sylow p G,
    x ∈ (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype

/-- **Isaacs p.219** (definition of *p-type maximal subgroup*).

A maximal subgroup `M` of `G` is `p`-type if `O_p(M) ≠ ⊥` (where `O_p(M)`
denotes the largest normal `p`-subgroup of `M` as a group in its own right).
In Isaacs §7D this notion partitions the maximal subgroups of a simple group
of order `p^a q^b` into two flavors. -/
def IsPType (p : ℕ) {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  IsCoatom M ∧ OddOrder.Isaacs.Ch01.opCore p ↥M ≠ ⊥

/-- Dual of `IsPType` with roles of `p` and `q` swapped (just a convenience
re-export of `IsPType q`). -/
abbrev IsQType (q : ℕ) {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  IsPType q M

/-- A group whose order is a `{p, q}`-number: `|G| = p^a * q^b`. -/
def IsPaQbOrder (p q : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ a b : ℕ, Nat.card G = p ^ a * q ^ b

                                            
                                                                 
                                           

                                                                           
                                                                     
                           
                      
                                                                              
      

                                                                              
                                                                    
                           
                                                   
                                
                    
                                            
          

                                                                                    
                                                                                 
                                                                          
                                                
                                                                                 
                                                                               
                                  
                              
            
               
                                                        
                       
                                                                                       
                                                             
                                                     
                                              
                
                                                                   
                                                                
                                                                                   
                                  
                                  
                                                          
                                                                                   
                                                 
                      
                                                                                   
                                      
                                           
                                                 
                                                                               
                                         
                                                                
                           
                     
                                                                                            
                                 
                                              
                                              
                                                
                                                           

                                                                        
                          

                                                                              
                                                                               
                                                                            
                                                          
                                          
                                        
                               
                                                                               
                                                                                         
                         
                                  
                         
                           
                                                  
                           
                                                              
                             
                                                              
                                                     
                                  
                                                          
                                                                        
                              
                            
                      

                                                                     
                                                                         
                                  

                                                                           
          

                                                                              
                                                 
                                                                            
                                                          
                         
                
                                                     
                             

                                                                           
                            

                                                                                
                                                                        
                                 
                                           
                                                             
                                                                
                                               
                                                 
                                         
                                                       
            
            
                                                                        
                                                                          
                                              
                                                                    
                                                             
                                                           
                                                                
                                                                
                                                       

                                                                        
                                        

                                                                       
                                                                       
                                                   
                                            
                                    
                                                                
                                                                        
                                                       
           
                     
                       
                                                                        
                                                        
                            
                                                                             
                                        
                                  
                                                                         
              
                                                                                      
                 
                                                                     
                                                                          
                                                                         
                                                     
                                                                      
                                        
                                                        
                                                     

                                                                          
                                                                           
               
                                              
                                                
                                                  
                                                             
                                                         
                                               
                                                                                   
                                                          
                                     
                                     
                                                                          
                                                                                  
                             
                                                              
                                                                            
           
                                                             
                                           
            
                                                             
                                           
                                                                             
                                                              
                                                                 
                                                    
                                                             
                                                                 
                                                             
                                                    

                                                                           
                                       

                                                                                
                                                                                      
                                                
                                                
                                              
                                                  
                                                           
                                         
                                                                 
                                                               
           
                   
                              
                                                                              
                  
            

                                                                             
                                                                            
          

                                                                             
                                                                               
                                  
                                                   
                                           
                                              
                                                                 
                 
                                                          
                                                      
                                                                                
                                                                                            
              
                                                               
                                       
                                          
                                                                                        
                              
                                               
                           
                 
                                 
                      
                          
                           
                   
                        
                 
           
                     
            
                          

/-- A Sylow `p`-subgroup is nontrivial whenever `p ∣ |G|`. -/
theorem Sylow.ne_bot_of_dvd_card
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp_dvd : p ∣ Nat.card G) (P : Sylow p G) :
    (P : Subgroup G) ≠ ⊥ := by
  intro hP_bot
  have hp_prime : p.Prime := Fact.out
  have h_card : Nat.card (P : Subgroup G) = 1 := by rw [hP_bot]; exact Subgroup.card_bot
  have h_eq := P.card_eq_multiplicity
  rw [h_card] at h_eq
  have h_pos : 0 < (Nat.card G).factorization p :=
    hp_prime.factorization_pos_of_dvd Nat.card_pos.ne' hp_dvd
  have h1 : (1 : ℕ) = p ^ 0 := by simp
  rw [h1] at h_eq
  have h_mult_zero : (Nat.card G).factorization p = 0 :=
    (Nat.pow_right_injective hp_prime.two_le h_eq).symm
  omega

                                                                               
                                                                             
                                                                       
                          
                                                                    
                                                
                                   
           
                            
                                              
                                                         
                                         
                                               
                                                    
                                                                                
                                                                   
                                                                                            
                                                     
                                                           
                                                                        
                          
                                      
                                                                
                                                       
                                                               
                           
                                                                                
             
                   
                     
                     
             
                                               
                                                  

                                                                                
                                                                
                                               
                                                
                                                 
                                                             
                                                       
                                                 
                          
                                                                             

/-- **§7D auxiliary observation** (Isaacs L3965) — if `M` is a maximal subgroup
of a simple group `G` and `K ≤ M` is a nontrivial subgroup normalized by every
element of `M`, then `M = N_G(K)`.

Proof: `M ⊆ N_G(K)` by hypothesis.  `N_G(K) ≠ ⊤` since otherwise `K ⊴ G`
which (by simplicity) forces `K = ⊥` (contradicting nontriviality) or `K = ⊤`
(contradicting `K ≤ M < G`).  By maximality, `N_G(K) = M`. -/
theorem maximal_eq_normalizer_of_M_normalizes
    {G : Type*} [Group G] [IsSimpleGroup G]
    {M K : Subgroup G} (hM_max : IsCoatom M)
    (hK_ne_bot : K ≠ ⊥) (hKM_le : K ≤ M)
    (hM_normalizes : M ≤ Subgroup.normalizer K) :
    Subgroup.normalizer K = M := by
  rcases hM_max.le_iff.mp hM_normalizes with h | h
  · -- N_G(K) = ⊤ ⇒ K is normal in G ⇒ K ∈ {⊥, ⊤} by simplicity.
    exfalso
    have hK_norm_G : K.Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hg_in_N : g ∈ Subgroup.normalizer K := h ▸ Subgroup.mem_top g
      rw [Subgroup.mem_normalizer_iff] at hg_in_N
      exact (hg_in_N x).mp hx
    rcases hK_norm_G.eq_bot_or_eq_top with hK_bot | hK_top
    · exact hK_ne_bot hK_bot
    · -- K = ⊤ contradicts K ≤ M and M < ⊤ (since M is a coatom).
      have : K ≤ M := hKM_le
      rw [hK_top] at this
      exact hM_max.ne_top (le_antisymm le_top this)
  · -- h : N_G(K) = M is exactly the goal.
    exact h

                                                                            
                                        

                                                                                
                                                                          
         

                                                                       
                                                  
                                      
                                                             
                               
                                                 
                                                                  
           
                                                                        
                                                           
                                                                                
                                              
                                           
                                                        
                                                     
                                                           
                                                                        
                          
                                                                
                                                       
                    
                                         
                                                          
             
                   
                     
                     
             
                                                                               
                                                   
                                                  
                                           
                                                 
              
                                                
                                             
                                             
                                       
                                     

                                                                                  
                                                                                 
                                                                         

                                                                                
                                                                        
                                                                        
                  
                                             
                                    
                                                             
                                                       
                                                                                            
                                                   
                                                                    
                                                         
                                                         
                                                             
                                  
                   
                                                     

/-! ### §7D Steps 2-9 — per-step decomposition of the 9-step argument

The original monolithic axiom `noNonsolvableSimplePaQb` (the entire
Goldschmidt-Bender-Matsuyama argument) is here decomposed into the individual
textbook steps.  Steps that are provable from the landed infrastructure appear
as theorems; the heavier steps (4, 8, 9) remain as fine-grained local axioms,
each tracked in issue 0032.  The steps are wired together into
`noNonsolvableSimplePaQb` (now a *theorem*) at the end. -/

                                                                          
                                                      

                                                                                
                                                                                  
                                                
                                                                
                                              
                                                           
                                       
                                                                 
                           
                                                               
                                                                 
                                                                                          
                                                                                           
                            
                                     
                                                                       
         
                                                                              
                                                                                  
                                                                      
                                                                       
                                                            
                                                             
                                                 
                      
              
                                                                              
                         
                
                                                                           
                                                                           
                                                                                                   
                                                             
                                 
                                                                      
                                                                          
                                                                

                                                                   

                                                                              
                                                                          
                                                                            
                                                                  
                                  
                                                
                                                 
                                                      
                                     
                                                                  
                                     
                                     
                                     
                                                                
                                     
                                                                          
                                                     
                                                          
                                                              
                                                            
                                            
                                                  
                                                                                          
                                                          
                                                              
                                                            
                                            
                                                  
                                                                                          
                              
                                                        
                                                 
                                                        
                                                 
                                                
                                                
                                   
                          
                                                                            

                                                                              

                                                                           
                                                                               

                                                                   
                                                                                       
                                                                          
                                 
                                                                  
                                                 
                                                      
                                   
                                            
                                                            
                                      
                                                                                    
                                                                           
                                                     
                                                       
                                                                                           
                
                                          
                                                                  
                    
             
                                                               
                                                                                      
             
                                                 
                                                            
                                             
                                                      
                                                                                                      
                                                                            
                                                                                                  
                                          
                                                          
                                                
                                                                        

                                                                        
                                                               

                                                                       
                                                                              
                                                                            
                                          
                                                        
                                                                  
                                                 
                                                      
                               
                                                            
                              
                                                            
               
                                     
                                                           
                           
                                              
                                                               
                                                  
                                                                                      
                           
                                     
                                     
                                     
                                                                
                                     
                                                                          
                                                                                  
                                                        
                                        
           
                                                              
                                                            
                                            
                                                  
                                                                                          
                                               
                                                       
                                                                  
                          
                              
                                                    

                                                                                 
                                                                     

                                                                                
                                                                                
                                                                                   
                                       
                                  
                                                
                                                 
                                                      
                                                                  
                                  
                                     
           
                                     
                                     
                                                                                   
                                                               
                                                                                        
                  
                                                               
                                                                   
                                                
                                                                     
                                 
                                                          
                                                    
                                                                              
              
                                                                  
                                                                      
                                                                 
                                                                                                
                                                                                                 
                                          
                     
                       
                                          
                                                                             
                                                               
                                                 
                                                               
                                                 
                                                                                       
                 
                 
                              
                                     
                                              
                                              


/-! ### §7D faithful-action generation bridge (Isaacs Thm 6.20/6.21, L3990-3993)

For the Step 3 contradiction we need the "generated-centralizer" conclusion in
the form Isaacs uses: if an abelian `A ≤ G` normalizes an abelian (more
generally arbitrary) subgroup `N ≤ G` of coprime order, and `A` is **not
cyclic**, then `N = ⟨C_N(a) ∣ 1 ≠ a ∈ A⟩`.  This is Isaacs Thm 6.21
(`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic`) applied to the
conjugation action of `A` on `N` (`Subgroup.normalizerMonoidHom` restricted to
`A`).  Conversely, the *faithfulness* of that conjugation action is `C_N(A)`
trivial, which Isaacs uses for the cyclic-arithmetic final branch. -/

/-- The conjugation action of a subgroup `A ≤ N_G(N)` on the subgroup `N`,
obtained by composing mathlib's conjugation `MulDistribMulAction` of `N_G(N)`
on `N` with the inclusion `A ↪ N_G(N)`.  Under this action
`a • n = ⟨↑a * ↑n * (↑a)⁻¹⟩`. -/
noncomputable def conjActionOfNormalizes {G : Type*} [Group G] (A N : Subgroup G)
    (hAN : A ≤ Subgroup.normalizer N) : MulDistribMulAction ↥A ↥N :=
  MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer N)) ↥N
    (Subgroup.inclusion hAN)

                                                                               
                                                                              
                                                                               

                                                             
                                                           
                                                    
                                                       
                           
                                       
                                                        
                                        
                                       
                                                                                       
           
                                                                        
                                                                            
                                                                                                          
                  
                                             
                                                                 
                                                       
                                                                              
                        
            
                                                                            
                                      
                                                         
                                                      
                                       
                                                                           
                                                                                          
                                                                  
                                        
                                   
                                                             
                                                                                  
                            
                                                                 
                                   
                                 
                                          
                                                  
                   
                                       
                                                               
                                                           
                                                                               
                                               
                                                                  
                             
                                   
                        
                                                         
                 
                                                      

/-- **§7D Step 1 helper** — a characteristic subgroup `W` of `K` (as a subgroup
of `↥K`) has its `H`-image `W.map K.subtype` normalized by `N_H(K)`.

For `g ∈ N_H(K)`, conjugation by `g` restricts to an automorphism of `↥K`; since
`W` is characteristic, that automorphism preserves `W`, so `g` preserves
`W.map K.subtype`.  Used to deduce `M = N_H(K_p)` from `M = N_H(K)` (`K_p`
characteristic in `K`). -/
theorem normalizer_le_normalizer_map_of_characteristic
    {H : Type*} [Group H] {K : Subgroup H} {W : Subgroup ↥K} [W.Characteristic] :
    Subgroup.normalizer (K : Set H) ≤
      Subgroup.normalizer ((W.map K.subtype) : Set H) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  -- The automorphism of ↥K induced by conjugation by `g ∈ N_H(K)`.
  set cg : ↥K ≃* ↥K := K.normalizerMonoidHom (⟨g, hg⟩ : ↥(Subgroup.normalizer K))
    with hcg_def
  -- W characteristic ⇒ `cg` fixes `W`.
  have hWfix : W.map (cg : ↥K →* ↥K) = W :=
    (Subgroup.characteristic_iff_map_eq.mp ‹W.Characteristic›) cg
  -- `↑(cg w) = g * ↑w * g⁻¹` for `w : ↥K`.
  have hcg_apply : ∀ w : ↥K, ((cg w : ↥K) : H) = g * (w : H) * g⁻¹ := fun w => rfl
  have hcg_symm_apply : ∀ w : ↥K, ((cg.symm w : ↥K) : H) = g⁻¹ * (w : H) * g := by
    intro w
    have h := hcg_apply (cg.symm w)
    rw [cg.apply_symm_apply] at h
    -- h : ↑w = g * ↑(cg.symm w) * g⁻¹  ⇒  ↑(cg.symm w) = g⁻¹ * ↑w * g.
    rw [h]; group
  intro y
  simp only [Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨w, hwW, rfl⟩
    -- y = ↑w, conjugate by g lands in W.map subtype via cg.
    refine ⟨cg w, ?_, ?_⟩
    · -- cg w ∈ W since cg fixes W.
      rw [← hWfix]; exact ⟨w, hwW, rfl⟩
    · rw [hcg_apply]
  · rintro ⟨w, hwW, hyeq⟩
    -- y conjugated back: g⁻¹ y g ∈ W.map subtype.
    refine ⟨cg.symm w, ?_, ?_⟩
    · rw [← hWfix] at hwW
      obtain ⟨w', hw'W, hw'eq⟩ := hwW
      -- cg.symm w = w' ∈ W.
      have : cg.symm w = w' := by rw [← hw'eq]; exact cg.symm_apply_apply w'
      rw [this]; exact hw'W
    · rw [hcg_symm_apply, hyeq]; group

                                                                                  
                                                                                
                    

                                                                         
                                                                                  
                           
                                                  
                                                                      
                                                 
                                                         
                                                                                   
           
                                     
                                     
                    
                                                                              
                                                                                
                    
                                    
                                                                     
                                               
                                                                           
              
                                                                  
                                                                 
                                                                 
                                                                                                
                                                                                                 
                                                      
                                                                
                                     
                                                        
                                                         

                                                                                   
                                                                               
                                                                                 

                                                                                 
                                                                                       
                                                                            
                                                             
                                               
                                                                   
                                                 
                                                        
                                                                   
                                           
                                                    
                                                                                             
                                                
           
                                     
                                     
                                                                                
                                                                
                                  
                                                                     
                                                                                     
                                 
                                                           
                                                                                 
                                        
                  
                                 
                                                                                     
                                          
                                               
                                  
                                                                                          
                                                                   
              
                                                                    
                              
                                                       
                         
                                                                                                
                                                                                   
                                                                      
                                                                     
                          
                                                                
                                                                
                                                            
                                                                              
                                  
                                                                         
                                               
                                                                               
                                         
                                                                   
                  
                                                 
                                                                                        
                                                                                               
                                                            
                                                                 
                                                
                                  
                                                                
                
                                                                      
                                  
                          
                                                                       
                                                                                  
                                                                     
                                                                   
                                                                        
                                              
                                          
                                                                                           
                                                                  
                                                           
                                

                                                                                  
                                   

                                                                            
                                                                            
                                                 

                                                                       
                                                                                
                                                                                     
                                                                                    
                                                                                
                                                                                      
                                                                
                             
                                                 
                                                                  
                                                 
                                                      
                                                                         
                                                       
                                                                 
                                                                      
                                                            
                                                            
           
                                     
                                     
                                                                               
                                                                    
                                                                                
                                                       
                                                                  
                                         
                                                        
                                                             
                                                                 
         
                                                
             
                                                           
                
                                                                     
                                 
                                                    
                                          
                         
                                                            
                                                      
                                                              
                                                                                          
                                                                                          
                                                        
                                                                                                      
                                                                
                                         
                                                                                       
                        
                              
                                                          
                                                           
                                             
                                      
                                                                 
                                      
                                                                 
                                                                                                
                                                                       
                                                           
                                                     
                                                              
                                                                                              
                                                                                   
                                                                
                
                                       
                              
                                                                       
                                                           
                                                     
                                                              
                                                                                              
                                                                                   
                                                                
                
                                       
                              
                                                             
                                      
                              
                                                                             
                            
                                      
                              
                                                                             
                            
                                                                                       
                                                                            
                                                       
                                                                                
                  
                                                          
                                                         
                                                                           
                                                                                
                                
                                                                            
                                                       
                                                                                
                                                                        
                                                         
                                                                           
                                                                                
                      
                                                     
                                                     
                                                    
                                                                    
                                                            
                                                      
                                                                                    
                                                                                  
                                                                                      
                                                                          
                                                          
                                                          
                                      
                                                   
                                                                       
                                                          
                                                          
                                                                                    
                                                                                    
                                      
                                                                 
                                                                   
                                                   
                                                                  
                                                                            
                                                               
                                 
                                                                                                    
                                                                           
                                                         
                                                    
                                                                 
                                                                                                 
                                                                   
                                              
                                                                                
                                              
                                                   
                                                               
                                                                                      
                                                          
                                                          
                                      
                                                   
                                                                       
                                                          
                                                          
                                                                                    
                                      
                                                                 
                                                                   
                                                   
                                                                            
                                                               
                                 
                                                                                                    
                                                                           
                                                         
                                                    
                                                                                                
                                                                 
                                                                                               
                 
                                              
                                                                                
                                              
                                                   
                                                                          
                                                                               
                                                                               
                                                         
                                                         
                                               
                                                 
                                
                                 
                                              
                                 
                                  
                                                       
                                  
                                                       
                                                      
                                                     
                                    
                
                                                                                    
                                                                                        
                                                    
                                                                                    
                                                    
                                                                                    
                                                                      
                                                                      
                                                   
                                                                      
                                                          
                                                         
                                                
                    
                                                                                             
                            
                                                                  
                                                                                              
                  
                                                        
                                                                                        
                                                                                              
                  
                                                        
                                                                                        
                                               
                      
                                                                                              
                                       
                                     
                                                         
                                               
                      
                                                                                              
                                       
                                     
                                                         
                                          
                                                                                  
                                          
                                                                                   
                                                                          
                                                         
                                             
              
                           
                                                                                    
                                                                                    
                                                                              
                    
                                           
                                                                                    
                                                                         
                                                                             
                                                                                             
                                                                       
                                                      
                                   
                                                      
                                                                               
                                              
                                                         
                                                                        
                                                  
                                        
                                                     
                                                                       
                
                                       
                
                                    
                                                                       
                
                                       
                
                                           
                                                             
                               
                                      
                                                                          
                                                                    
                               
                                      
                                                                          
                                                                    
                                                      
                                                     
                                                      
                                         
                                                           
                                                                            
                                 
                                                                                       
                                                         
                                                           
                                                                                      
                                                                        
                          
                                                         
                                                             
                                                            
             
                                                                                  
                                   
                                                                           
                                                                                       
                          
                                     


end OddOrder.Isaacs.Ch07
