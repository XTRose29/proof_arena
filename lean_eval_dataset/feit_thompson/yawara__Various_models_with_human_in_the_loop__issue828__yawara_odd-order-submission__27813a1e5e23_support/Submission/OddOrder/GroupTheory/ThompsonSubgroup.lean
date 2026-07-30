/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Submission.OddOrder.GroupTheory.ElementaryAbelian

/-!
# Thompson Subgroup `J(P)`

`OddOrder.GroupTheory` shared module: Thompson subgroup `J(P)` の定義と基本性質.

Isaacs, *Finite Group Theory* (2008), Chapter 7 (pp. 201-202) の中核 def.
mathlib v4.29.1 に未収載 (`Thompson` 名はゼロ件). Ch.7, BG App.A, BG App.B (Puig 代替),
BG §6, §8, §9 (Uniqueness Theorem) で繰り返し使われる shared concept として独立 module 化.

## Main definitions

* `Subgroup.maxElemAbelianIn P p`: 部分群 `P` 内の `p`-elementary abelian 部分群のうち
  最大位数のものの集合 (Isaacs L3727 の `E(P)`).
* `Subgroup.thompsonJ P p`: Thompson subgroup `J(P) = ⟨E(P)⟩`
  (Isaacs L3727, Aschbacher §32, BG L5586 の記法).

## Design notes

* Isaacs の `J(P)` は **largest order** の elementary abelian (Aschbacher 系). Thompson
  原版は **largest rank** (元の Thompson 1968) で、両者は P が abelian non-elementary
  のとき異なりうる. 本 module は Isaacs/Aschbacher 版を採用.
* `p` は引数で取る (`P ∈ Syl_p(G)` 文脈で外側固定が自然).
* `[Finite G]` は def 段階では不要だが, 主要結果 (Thm 7.2 等) では必須.

## Forward references

* `Subgroup.thompsonJ_le`: `J(P) ≤ P`.
* **Isaacs Thm 7.2** (`thompsonJ_eq_of_le_of_le`): `J(P) ≤ Q ≤ P ⇒ J(Q) = J(P)`.
  特に `J(P)` は `Q` 内 characteristic.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- `[Finite G]` のとき, `Subgroup G` 自体も有限. `Subgroup G ↪ Set G` 経由. -/
instance instFiniteSubgroupOfFinite [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

                                                                        
                                           
                                                  
                     
              
                               
            
                                            
                    

/-- **Maximum-order elementary abelian subgroups of `P`** (Isaacs Ch.7 L3727 の `E(P)`).

`E(P) = {E ≤ P | E は p-elementary abelian で, 任意の elem-ab subgroup F ≤ P について
|F| ≤ |E|}`. -/
def maxElemAbelianIn (P : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {E | E ≤ P ∧ E.IsElementaryAbelian p ∧
       ∀ F : Subgroup G, F ≤ P → F.IsElementaryAbelian p → Nat.card F ≤ Nat.card E}

/-- **Thompson subgroup** `J(P) = ⟨E(P)⟩` (Isaacs Ch.7 def, p.201).

`P` 内の最大位数 elementary abelian 部分群すべての (Subgroup G 内での) 上限. -/
def thompsonJ (P : Subgroup G) (p : ℕ) : Subgroup G :=
  ⨆ E ∈ maxElemAbelianIn P p, E

                                                            
                                                                           
                                              
            

                                                                           
                                                                         
                                                              
                                           

                                                                                       
                                                                                                                  
                                                                                                               
                                                                 
                                                       
                                          
                              

                                                                                       
                                                                         
                                         
                                                              
                                                                      
                                                                                
                                            
                                                                                 
                                                
                                    
                                 
                        
                                                            
                                        
                                    
                    
                                  

                                                             

                                                                                              
                                                                      

                                                                
                                                                                                  
                                             
                                                                                                       
                                                                                                        
                                            
                                                                        
                                                 
                                       
                   
                     
                                                  
                                                         
                                                                                    
                                               
                                                                             
                                                     
                                                                                         
                                           
                                                                                    
                                                                                             
                                              
                                   
                      
                   
                                                   
                                     
                     
                                                  
                                         
                                               
                                            
                                              
                                   
                      
                                           

                                                             

                                                                              
                                                                            
                                                                          
                  
                                                                             
                                                           
                               
           
                                                                   
                                                                       
                                                                                    
                                         
                                                  
                             
                                             
                
                               
                                                    
                
                                            
                                                                   
                                                                       
                                                            
                                                                            
                              
               
                                       
                                                                               
                                            
                                           
                                                                                        
                       
                                                           
                                                           
                                                          
                                                          
                                                                          
                                                                      
                                       
                                                            
                                
                                                   
                                                         
                                                                          
                                  
              
                        
                                            
                                                         
                                       
                                                                   
              
                                    
                         

                                                                         
                                                             

                                                                        
                                                                             
                                                                             

                                                                             
                                                 
                                                                   
                                                                           
                                                       
                                                                                      
                                         
                                                                             
                                                                        
              
                                           
                                                               
                                                                               
                                              
                                            
                                             
                            
                                                           
                                     
                                                                              
                                                                    
                                    
                             
                                                                                       
                        
                                                                   
                                                        
                                                 
                                                                                         
                                                            
                                       
                                               
                                                                                          
                                                
                                                                                       
                                                                   
                                                    
              
                                           
                                                                                       
                                                                                  
                                                                                 
                       
                                                                               
                                                                                      
                                           
                                                                                            
                                                             
                                                                    
                                     
                             
                                                          
                                      
                                             
                                                                                       
                                                     
                                                                  
                                            
                                     
                   
                                     
                                                
                                                         
                      
                                                                              
                                                                                
                                     
                                                
                                         
                                                             

                                                                                
                                                                                 

                                                                                     
                                               
                                                                                     
                                                
                                                                         
                                                                                            
                                                            
         
                         
               
                              
                            
               
                                         
                                                              
                                                                  
                            
                                                
                                                 
             
                                                                                         
                                                       

end Subgroup
