/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Submission.OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7A1_JpGL2p

/-!
# Isaacs FGT Ch.7 (Thompson subgroup) — S7A part 2: Lem 7.3 (formal) + Thm 7.5 normal-P + action infra (pp. 201-208)
-/

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement
open scoped Pointwise
open scoped IsMulCommutative -- rc2: IsMulCommutative→CommMonoid (for Additive V) now scoped

variable {G : Type*} [Group G]

/-! ### Thm 7.5 — normal-P theorem (statement 保留)

**Isaacs Thm 7.5** (mmd L3783):

> (i) G p-solvable, (ii) `p ≠ 2`, (iii) Sylow-2 abelian, (iv) G が p-group V に
> 忠実作用, (v) `|V:C_V(P)| ≤ p` ⇒ `P ⊴ G`.

**先行 def 依存**: `Aut(E) ≅ GL(n,p)` (Lem 7.3 と共用).

**proof 戦略** (8 Step): Sylow conjugacy + GL(2,p) embedding + Hall-Higman 3.21
+ Lem 7.3 + Ch.6 6.11 (p-group ≤1 subgroup p ⇒ cyclic/quaternion).

Ch.6 6.11 は `isCyclic_or_two_quaternion_of_subgroups_card_prime_unique` として利用可能.
残る作業は, 下の action / fixed subgroup bridge 群を使って Thm 7.5 の本体 statement と
book proof の contradiction assembly を Lean に載せること. -/

/-! #### Thm 7.5 action infrastructure

Theorem 7.5 repeatedly uses the faithful action of `G` on the `p`-group `V` as an
embedding `G ↪ Aut(V)`, and writes `C_V(P)` for the fixed subgroup of `P` acting on
`V`.  The following helpers keep those two translations explicit. -/

/-- Reinterpret automorphisms of an abelian group of exponent dividing `p` as `ZMod p`-linear
automorphisms of its additive type.

The `ZMod p`-module structure is supplied explicitly because in Thm 7.5 it is built from the
elementary-abelian hypothesis on a quotient. -/
noncomputable def mulAutZModGeneralLinearEquiv
    (V : Type*) [Group V] [IsMulCommutative V] (p : ℕ)
    [Module (ZMod p) (Additive V)] :
    MulAut V ≃* LinearMap.GeneralLinearGroup (ZMod p) (Additive V) where
  toFun φ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive V)).symm
      ((MulEquiv.toAdditive φ).toLinearEquiv
        (fun c x => ZMod.map_smul (MulEquiv.toAdditive φ).toAddMonoidHom c x))
  invFun φ :=
    (MulEquiv.toAdditive (G := V) (H := V)).symm φ.toLinearEquiv.toAddEquiv
  left_inv φ := by
    ext x
    rfl
  right_inv φ := by
    ext x
    rfl
  map_mul' φ ψ := by
    ext x
    rfl

/-- A chosen `ZMod p`-basis of size `2` identifies `Aut(V)` with `GL(2,p)`.

This is the explicit bridge needed to feed the action on an elementary-abelian quotient into
Isaacs Lemma 7.3 (`gl2_pSubgroup_centralizes_of_normalizes`). -/
noncomputable def mulAutGLTwoEquivOfBasis
    (V : Type*) [Group V] [IsMulCommutative V] (p : ℕ)
    [Module (ZMod p) (Additive V)]
    (b : Module.Basis (Fin 2) (ZMod p) (Additive V)) :
    MulAut V ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
  (mulAutZModGeneralLinearEquiv V p).trans (Matrix.GeneralLinearGroup.toLin' b).symm

/-- The `ZMod p` scalar-torsion condition supplied by an elementary-abelian multiplicative group.
-/
private lemma additive_nsmul_eq_zero_of_isElementaryAbelian
    {V : Type*} [Group V] {p : ℕ}
    (hV : OddOrder.GroupTheory.IsElementaryAbelian p V) :
    ∀ x : Additive V, (p : ℕ) • x = 0 := by
  intro x
  apply Additive.toMul.injective
  show (p • x).toMul = (0 : Additive V).toMul
  rw [toMul_nsmul, toMul_zero]
  exact hV.pow_eq_one x.toMul

/-- An elementary-abelian group of order `p^2` has automorphism group identified with `GL(2,p)`.

The basis is chosen noncomputably from the finite `ZMod p`-vector-space structure on the
additive type. -/
noncomputable def mulAutGLTwoEquivOfIsElementaryAbelianCard
    (V : Type*) [Group V] [Finite V] {p : ℕ} [Fact p.Prime]
    (hV : OddOrder.GroupTheory.IsElementaryAbelian p V) (hcard : Nat.card V = p ^ 2) :
    MulAut V ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod p) := by
  classical
  haveI : IsMulCommutative V := ⟨⟨hV.comm⟩⟩
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (Additive V) := Fintype.ofEquiv V Additive.ofMul
  haveI : Module (ZMod p) (Additive V) :=
    AddCommGroup.zmodModule (additive_nsmul_eq_zero_of_isElementaryAbelian hV)
  have hfinrank : Module.finrank (ZMod p) (Additive V) = 2 := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    calc
      p ^ Module.finrank (ZMod p) (Additive V)
          = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) (Additive V) := by
              rw [ZMod.card]
      _ = Fintype.card (Additive V) := (Module.card_eq_pow_finrank
              (K := ZMod p) (V := Additive V)).symm
      _ = Nat.card (Additive V) := by rw [Nat.card_eq_fintype_card]
      _ = Nat.card V := (Nat.card_congr Additive.ofMul).symm
      _ = p ^ 2 := hcard
  let b0 := Module.Free.chooseBasis (ZMod p) (Additive V)
  have hidx_card : Fintype.card (Module.Free.ChooseBasisIndex (ZMod p) (Additive V)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact hfinrank
  let eidx : Module.Free.ChooseBasisIndex (ZMod p) (Additive V) ≃ Fin 2 :=
    Fintype.equivOfCardEq (by rw [hidx_card, Fintype.card_fin])
  exact mulAutGLTwoEquivOfBasis V p (b0.reindex eidx)

                                                                             

                                                                                     
                                                                                           
                                                  
                                                  
                                                                                  
                               
                                            
                                     
                                                          
                                                     
                 
                                                                    
                                                                                       
                                                
                                                                                            
                                                                           
             
                                   
             
                                            
                                             
                                            
                                             
                                         
                                                           
                   
                               

                                                                         

                                                                                       
                                                                                         
                                                         
                                                                                   
                      
                                                                     
                                                
             
                                   
             
                                                                  
                                                                  
                                           
                                                               
           
                             

                                                                  

                                                                                        
                                                                        
                                                           
                                                              
                                                        
                                                                                  
                      
                                                     
                                              
                                                                   
                                                              
                 
                                                                    
                                                                                                
                                             
                                                       
                                                                                  

/-- The image of any subgroup normalizes the image of a normal subgroup.

This is the normalizer adapter used in the reduced `GL(2,p)` branch of Isaacs Thm 7.5:
`P` normalizes `O_{p'}(G)`, so its faithful image normalizes the image of `O_{p'}(G)`. -/
theorem map_le_normalizer_map_of_normal
    {A B : Type*} [Group A] [Group B] {φ : A →* B} {P L : Subgroup A} [L.Normal] :
    P.map φ ≤ Subgroup.normalizer ((L.map φ) : Set B) := by
  rintro _ ⟨p, _hpP, rfl⟩
  have hLnorm : L.Normal := inferInstance
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨l, hlL, rfl⟩
    refine ⟨p * l * p⁻¹, hLnorm.conj_mem l hlL p, ?_⟩
    simp [map_mul]
  · rintro ⟨l, hlL, hyl⟩
    have hconj : p⁻¹ * l * p ∈ L := by
      simpa using hLnorm.conj_mem l hlL p⁻¹
    refine ⟨p⁻¹ * l * p, hconj, ?_⟩
    calc
      φ (p⁻¹ * l * p) = (φ p)⁻¹ * φ l * φ p := by simp [map_mul]
      _ = y := by rw [hyl]; group

                                                                         
                                                        
                                                                         
                                                                  
           
                                                                              
                                      
              
                                                  
                                                                       
                                                      
                                                                                             
                                

                                                                                         
      

                                                                                        
                                                                                       
                                                  
                                                   
                                                                                   
                                                                                    
                                     
                                                   
                                       
                                  
                        
                                     
                            
                                  
                                            
                 
                     
             
                                  
                                                        
                                
           
                                              
                                              
                                                        
                                                        
                             
                                                           
                   
                                              
                                                  

                                                        

                                                                                  
                                                                                
                                                                
                                                                   
                                                           
                            
                                                          
                   
                                                                                    
                                                        
                                                           
                                                   
                                 
                         
                                                                             
                                                               
                 
                               
                                                                        
                                          
                         
                                                                     
                                     
                        
                                                                       
                  
                                                                         
                       
                                                              
                                             
                  
                                                                           
                                 
                                                         
                                                             
                                                     
                                                                                 
                                                                                              
                                 
             
                  
               
                                                     
                                                                          
                
                                                        
                                                                          
                                     
                                                                      
                                        
             
                                                                                 
                           
                                             
                                             
              
                                                            
                
                                                            
                                                      
                                                         
                                        
                   
                                                                    
                                                                                                   
                     
                                                               
                                          
                                                                                    
                                                                           
                                                       
                                                      
                                                                   
                           
                                                                           
                                                                        
                                         
                                                                           
                     
             
                

                                                                                           
                                                            

                                                                                             
                                                                                           
                                     
                                                       
                                                  
                                                                           
                  
                                    
                                                                               
                                                   
                

/-- A faithful action by automorphisms embeds the acting group into `MulAut V`. -/
theorem toMulAut_injective_of_faithful {A V : Type*} [Group A] [Group V]
    [MulDistribMulAction A V] [FaithfulSMul A V] :
    Function.Injective (MulDistribMulAction.toMulAut A V) := by
  intro a b hab
  apply MulAction.toPerm_injective (α := A) (β := V)
  ext v
  have h := congrArg (fun ψ : MulAut V => ψ v) hab
  simpa using h

                                                       
                                                                         
                                                  
                                                   
                                                                 

                                                                         
                                         
                                                             
                                                               
                  
                                        
                                  
                     
                                                              
                     
                                                   
                                                 
                                   
                   
                                           
                                  
                               
                                      
                              
                                                     
                                             
                                                             
                                                                        
                                     
                                             
                                                                                      
                                              
                                     
                                
                                                            
                               

/-- A faithful action by automorphisms realizes the acting group as a subgroup of `Aut(V)`. -/
noncomputable def subgroupOfMulAutAction (A V : Type*) [Group A] [Group V]
    [MulDistribMulAction A V] [FaithfulSMul A V] :
    A ≃* (MulDistribMulAction.toMulAut A V).range :=
  MulEquiv.ofLeftInverse' _
    (Classical.choose_spec (toMulAut_injective_of_faithful (A := A) (V := V)).hasLeftInverse)

/-- Action-centralizer notation for `C_V(P)`: the elements of `V` fixed by every element of `P`
under `φ : A →* MulAut V`. -/
def actionCentralizer {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P : Subgroup A) : Subgroup V :=
  Subgroup.fixedPointsOfMulAut (φ.comp P.subtype)

@[simp]
theorem mem_actionCentralizer {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {P : Subgroup A} {v : V} :
    v ∈ actionCentralizer φ P ↔ ∀ p : P, (φ p) v = v :=
  Iff.rfl

@[simp]
theorem mem_actionCentralizer_top {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {v : V} :
    v ∈ actionCentralizer φ (⊤ : Subgroup A) ↔ ∀ a : A, (φ a) v = v := by
  constructor
  · intro hv a
    exact hv ⟨a, trivial⟩
  · intro hv a
    exact hv a

                                              
                                                                    
                                                               
                                                           
              
                                  

                                                               

                                                                       
                                                                    
                                                     
                                                              
                                                        
       
             
             
                                                                    
           
                                         
                                                                       
                                                       
                                                         
                                          
                                                          
                           
                              
                                          
                                
                                                    
                                           
                                             
                                           
            
                           

                                                                      
                                                                          
                                                     
                                                                      
                                          
                                 
                                                                     
                                                           
                                                                  
                                    
                                                                                  
                      

                                                                                          

                                                                                             
                             
                                                               
                                               
                                                                                            
       
             
             
                                                                                 
                                                                             
                          
                                                                              
                                                      
                                     
                                                           
                 
                            
                             
                             
           
                          
                            
                   
          
                                                        
                                                
                                                 

                                                                                      
                                     
                                                                        
                                               
                                              
                                                                           
                            
                             

                                                                                   
                                                                              
                                                         
                                               
                                                 
                                                       
                                                                      

                                                                                        
                                                           
                                                                           
                                                       
                                               
                                                 
                                                          
      
                                                       
                                                       
                        

                                                                                    
                  
                                                                           
                                                       
                                               
                                                 
                                                                             
                                
                                                      

                                                                                       
                                          

                                                                                  
                                                      
                                                
                                                
                                             
                                               
                                                 
                                                                    
                                               
                                           
                                               
                                           
                                               
                                               
                

                                                                
                                                          
                                       
                                                          
                                                                               
                                                                          
                                               
                                                 
                                                                                        
                                                                                     

                                                                                       
                                                                   

                                                                                     
                                            
                                                                                        
                                                
                                                                      
                                                                
                       
                                               
                                               
                                                                                            
                                              
                                                                       
                                                                                     
                                                                                
                                                                        
                                                                     
              

                                                                                            
                                                                                  
                                           
                                                          
                                                
                                                     
              
                                               
          

                                                                                          

                                                                                          
                                                        
                                                            
                                              
                                        
                                                               
                                                
                                     

                                                                           

                                                                                      
                                                           
                                                   
                                                    
                                                              
                              
              

                                                                                     
                                                                      
                                                       
                                                            
                                                
                                         
                                                                
                                       
                                  

/-- The induced action on `V/U` for an invariant normal subgroup `U`. -/
noncomputable def quotientActionHom {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) : A →* MulAut (V ⧸ U) :=
  OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hU

@[simp]
theorem quotientActionHom_apply_mk' {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) (a : A) (v : V) :
    (quotientActionHom φ hU a) (QuotientGroup.mk' U v) =
      QuotientGroup.mk' U ((φ a) v) :=
  OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk'
    hU a v

                                                                                      
                                                                               
                                                            
                               
                                                                    
                                                          
                                                         
                             
                                                                    
                         
                                  
                                             

/-- Kernel of the induced action on `V/U`. In Isaacs Thm 7.5 this is the subgroup `K`
acting trivially on `V/U`. -/
noncomputable def quotientActionKernel {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) : Subgroup A :=
  (quotientActionHom φ hU).ker

/-- The kernel of the induced quotient action is normal in the acting group. -/
instance quotientActionKernel_normal {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) :
    (quotientActionKernel φ hU).Normal := by
  change (quotientActionHom φ hU).ker.Normal
  infer_instance

/-- The faithful action of `A/K` on `V/U`, where `K` is the kernel of the induced action.

This is the formal version of the Thm 7.5 step "the quotient group `G/K` acts faithfully on
`V/U`". -/
noncomputable def quotientActionFaithfulHom {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) :
    A ⧸ quotientActionKernel φ hU →* MulAut (V ⧸ U) :=
  QuotientGroup.kerLift (quotientActionHom φ hU)

@[simp]
theorem quotientActionFaithfulHom_mk' {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) (a : A) :
    quotientActionFaithfulHom φ hU
        (QuotientGroup.mk' (quotientActionKernel φ hU) a) =
      quotientActionHom φ hU a :=
  rfl

                                                                                        
                    
                                                                                    
                                                            
                               
                                                                    
                                                          
                                                         
                                                                      
                                
                                               
             
                                                           
                                   
                                    
                                                          
                                                          
                                                                    
                                                                                    
                                                     
                                           
            

                                                                                             
                                                         
                                                                       
                               
                                                                            
                                          
                                                 
                                                        
                                                                                   
                                                                                          
        
      
                                                        
                                                                       
                                                                         
                                     
                                         
                                                                    
                 

                                                                
                                                                             
                                                      
                                                   
                                                              
                                                         
                                                                 

                                                                                  

                                                                                   
                
                                                      
                                                            
                               
                                                 
                                                              
                                                                         
                                                        
           
                                                     
                                                    
                       
           
                                                               
                                                            
           
                                        
                                    
                                                               
                             
                                        

                                                                                   
                                                
                                                            
                               
                                                   
                                         
                                                             
                                                          

                                                                                        
                                   

                                                                         
                                                                  
                                                            
                               
                                                 
                                                            
                                                              
                                                                 
                                                            
              
                                                                               
                                                           

                                                                                        
                                                      
                                                            
                                                            
                               
                                                 
                                                              
                                         
                                                          
                                                                                    
                                                                             

                                                                      
                                                                                       
                                         
                                                                            
                                                            
                                                          
                                        
                                       
                                                          
                                                                        
                                               
                                             
                                             
                                                           
                                         
                                          
                                                             
                                          
                                                                 
                          
                 

                                                                                          
                                          

                                                                                     
                  
                                                             
                                                           
                                                   
                               
                                                 
                                                     
                                                              
                                                 
                                                              
                                               
                                        
                 
                     
                 
                                                            
                                           
                               
                                                                    
               
                                         
                                                            
                                                                       
                                                                                  
                                                                      
                              
              
                                                               
                                          
                                                                    
                                       
                                                                           
                                                              
                                                                        
                             
                                                          
                                                             
                                                                     
                            
                                                                               
                     
                                                  
                                                        
                                              
                                                             

                                                 
                                                        

                                                                                               
                                        
                                                                         
                                                           
                                                   
                      
                                                                            
                                                                             
                                       
                                                                              
                                                             
              
             
                                        

                                                                                   
          

                                                                                         
                                                                 
                                             
                                                       
                   
                                                    
                  
               
                                                                                  
                                    
                              
                 
                                         

                                                                      
                                        
                                                                       
                                                                     
                             
                                                         
                                      

                                                                                     
                                                                       
                                                                
                                                                       
                                                                   
                                                                     
               
                                                                             

                                                                                      
                                   

                                                                                     
                                                             
                                      
                                                         
                                                     
                                                                     
            
           
                
                                                                                  
                                    
                              
                
                                                                                  
                                    
                              
                                     

                                                                                   
                                                         
                                                             
                                     
                                                     
                                                        
                                                            
            
                                                       
                
                                                    
                                                     
                                  
                                     
                                     
                                        
               
                          
                                                                
                     

                                                                                           
                                                                        
                                                             
                                                                   
                                                  
                                                            
                                                                
             
                                                       
                     
                                                             
                                                             

                                                                             

                                                                                          
                                                                                        
                                                             
                                     
                                                                
                                                                                    
                                                   
                                       
                                               
                                          
                     
                                             
                    
           
                
                    
                 
           
                  
                                       
           
                                                                      
                                
                       
                              
          
                           
                              
                                            
                                                  
                                                                     
                                              
                                                   
                                                              
                               
                                                                   
             
                     
                     
                                                   
                                                         
                                                   
                                                         
                                                                               
                     
                 
           
                                               
                  
           
                                               
                  
           
                                               
                                       
                                       
                              
                              
                                  
                                                       
      
                                                   
                                      
                                   
                                      
                                 

                                                                                      
                         

                                                              
                                                                                  
                                                                       
                               
                                                                                
                                                           
                            
                                                          
                   
                                                                                    
                                                      
                                                 
                                                                   
                                                           
                                                                                    
                                                                
                                                           
                  
                                                        
                                             
                                               
                                                    
                                                                   
                                                                   
                                                 
                                           
                                                          
                                                                                 

                                                                                   

                                                                                           
                                                                                        
                                                                                  
                                                                             
                                                           
                            
                                                          
                   
                                                                                    
                                                      
                                                 
                                                  
                                                                   
                                                         
                                                           
               
                                                             
                                                              
                                                                               
                                          

                                                                                    
               

                                                                                      
                                                                  
                                                         
                                                
                            
                                                                           
                                                                   
                                                                                    
                                                                
                                                        
                                                 
                                                          
                                           
                                            
                                                                                   
                                                            
                                           

                                                                          
                                                      
                                                
                            
                                                                           
                                                 
                                                                  
                                                           
               
                                                             
                                                              
                                                               

                                                                               

                                                                                      
                                                                                   
                                                                                                
                                                      
                                                                           
                                                           
                            
                          
                          
                                                                               
                                      
                                                                              
                                                      
                                                             
                             
                                                
             
                                                              
                                                                   
         
                                     
               
                 
                                              
                                  
                                             
                                                     
                
                 
                                                                       
                                                    
                                          
           
                                                                         
               
                                               
                                                                
                                    
                                                                      

                                          

                                                                                     
                                                                                           
                                                    

                                                                                       
                                                                                              
                                                                                              
                                                                                              
                                                                                          
                                   
                                                   
                                                           
                            
                                                          
                   
                                                                                    
                                                        
                       
                          
                                                                               
                                                   
           
                                                       
                                       
                                                                                                
                                                                                      
                                                           
                             
                                                                                 
                                                                 
                                         
                                                            
                                                
                                                                 
                         
                                                           
                                                  
              
                                                        
                  
                                                                              
                                    
                                                         
                                                                         
                           
                                     
                                                                         
                                                                       
                           
                                                                       
                           
                     
                                                  
                                                            
                                                                   
                                                                    
                                    
                       
                                            
                                                    
                                                     
                                                              
                                               
               
                                                               
                                                                               
                                                                  
                      
                      
                                 
                         
                                                                  
                                                 
                        
                         
           
                                                      
                                                      
                                                         
                                        
                                                                                        
                                                                        
           
                                                                             
                                                                                      
                                                                
                                  
                                            
                                                   
                                                                                
                                                     
          
                                                       
                                                                                
                              
                            
                                                                                   
                                                                                    
                              
                                           
                                                  
                                                                   
                                                                                    
                                                    
                     
                                                                                
                 
                                                                   
                                                      
               
                       
                       
                                      
                                                           
                                      
                                                           
                                                                                  
                   
                                                              
                                                            
                   
                       
                   
                              
                               
                                                                   
                                          
              
                                                                   
                                            
                                                                         
                     
                                                 
                                                                    
                                   
                                
                                           
                                                 
                                                                    
                                   
                                                                            
                               
                                                   
                                   
                                                                   
                                                                       
                                                
                  
                                                                                
                                                                        
                                      
                  
                                                                                
                                                                        
                                      
                                                                
                                     
                                             



end OddOrder.Isaacs.Ch07
