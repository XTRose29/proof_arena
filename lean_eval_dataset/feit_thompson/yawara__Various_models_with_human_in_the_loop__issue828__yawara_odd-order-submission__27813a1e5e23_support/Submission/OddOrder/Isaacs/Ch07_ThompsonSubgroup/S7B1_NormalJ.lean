/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Submission.OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7A2_NormalPThm75

/-!
# Isaacs FGT Ch.7 (Thompson subgroup) — S7B part 1: normal-J (Thm 7.6) Steps 1-6 (pp. 209-214)
-/

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## §7B: normal-J theorem (pp. 209-214) -/


/-! ### Thm 7.6 — normal-J theorem ⭐⭐ (conditional on 8-step argument)

**Isaacs Thm 7.6** (mmd L3832):

> (i) G p-solvable, (ii) `p ≠ 2`, (iii) Sylow-2 abelian, (iv) `O_{p'}(G) = 1`,
> (v) `P = C_G(Z(P))` ⇒ `J(P) ⊴ G`.

**= BG Theorem 6.2 の odd-order 等価版**. **FT クリティカル度 HIGHEST**: BG §6, §8,
§9, App.A で 7 ヶ所超で直接引用.

**proof 戦略** (8 Step, mmd L3832-3896): Thm 7.5 + Ch.6 **6.20** (abelian coprime
⟨C_N(a)⟩=N) + Ch.4 **4.35** (Ω₁ fixed) + Hall-Higman 3.21.

The full Goldschmidt-style 8-step proof requires Thm 7.5 (✅ landed) + Ch.6 6.20 +
Ch.4 4.35 (still pending).  Below we land the **conditional version** that takes
the minimum-counterexample contradiction as a forward-dependency hypothesis. -/

/-! ### Step 1 corollaries of Hall-Higman 3.21 (mmd L3837)

The first step of Isaacs Thm 7.6 proof observes that under hyp (iv)
`O_{p'}(G) = 1`, Hall-Higman 3.21 (with `π = {p}`) yields
`C_G(O_p(G)) ≤ O_p(G)`, and consequently `Z(P) ≤ O_p(G)` for any
Sylow `p`-subgroup `P`. -/

                                                    

                                                                               
                                                                             
                                                            
                                                  
                                                     
                                                                       
                                                                          
                                             
                                   
            
                                                                           
                                                             
                                       
                                                      
                                

                                                                            

                                                                            
                                 
                                                           
                                                             
                                                          
                                                                 
                                                                      
                                           
                                                                                    
                                                                       
                  
              
             
                                                                        
                                                                         
           

                                                                                     

                                                                    
                                                                         
                                                                        
                                                     
                                                             
                                                          
                                                                                 
                                                                       
                                        
                                              
                                                              

                                                             
                                                                                   

                                                                            
                                                                             
                                                                      
                                                       
                                                     
                                                             
                                                            
                        
                                                   
                                                                    
                                                                         
                                                
                                                                    
                                                                      
                                                            
                                                                             
                                                                                  
                                                                      
                                                                  
                                                           
                                                                                          
                                                                                    
                 
                        
                
                                                                                    
                
                                  
                                                                 
                                                                            
                                                                                                 
                 
               
                                                                           
                                                                   
                                                                                

/-! ### §7B Step 4 setup: the subgroup `L = O_{p',p}(G)`.

Following Isaacs L3835 the book sets `L̅ = O_{p'}(G̅)` (where `G̅ = G/U`,
`U = O_p(G)`) and defines `L` to be the unique preimage of `L̅` in `G`
containing `U`.  We work with the comap-along-`mk'` form. -/

/-- `L = O_{p',p}(G)` defined as the preimage of `L̅ = O_{p'}(G̅)` along
the quotient map `G →* G/(O_p(G))`.  This is the second term of the lower
`p`-radical series of `G` (with `O_p` first, `O_{p'}` second). -/
noncomputable def opPpPrimeCore (G : Type*) [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] : Subgroup G :=
  (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)).comap
    (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))

/-- `L = O_{p',p}(G)` is `G`-normal (comap of normal subgroup is normal). -/
instance opPpPrimeCore_normal {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] : (opPpPrimeCore G p).Normal := by
  unfold opPpPrimeCore
  infer_instance

                                                                                
                                            
                                  
                                                               
                                                                              
                      
            
                         
                                                                   
                                                   
                                                                   

                                                                        
                                                                                   
                                 
                                                               
                           
                                                                              
                                                
                                                                    
                      
                                                
                                      

                                                                               
                                                                                   

                                                                                  
                                                                   
                           
                           
                                                             
                                             
                                                                                  
                                                
                                                                          
                                           
                            
                                                                                     
               
                                                                         
                                                                                        
              
                                                               
                                
                                                                                       
                                    
                                                       
                     
                           
                                                       
                                        
                  
                                                                                      
                                                          
                                                   
                                                 
                                                                     
                                                           
                                                                                           
                                                                                    
                 
                              
                                                                                     
                       
                                            
                                                                        
                                                        

                                                                        
                                                                        
                                                                
                                                                            
                                                                                  
                        
                                               
                                               
                                             
         
                                                          
                                           
                                                                      
                
                                                    
                                         
                                 
                                             
                                                               
                                                      
                                                       
                                                                                             
           
                                                  
                                              
                                             
                                                                    
                                   
                    

                                                                                          
                        
                                                     
                                            
                                                                  
                           

                                                                                
                                                                                 
                        
                                                        
                                    
                                                            
                           
                      

                                                                           
                                                                      
                                                                       
                                                                               
                                                          
                                                      
                                           
                                                             
                 
                   
                                              

                                                                    
                                                                   
                                                      
                                                              
                                                     
                                         
                     
                                                               
                     
                                          
                                     
                                                                                                       
                                              
                                                   
                               
                     
                      
                                     
                                                             
                                                  

                                                                     
                                                                       

                                                    
                             
                                                             
                    
                                                                           
                                                                                            
            
                 
            
             
                                                                                
                                                                                     
                    
                                     
                                            

                                                                            
                                                                                 
                                  

                                                                       
                                       
                                                             
                                                          
                                             
                                                                                  
                          
                                                   
                                                                    
                                                                                 
                 
      
                                                                                  
                            
                                                     
                                                                      
                                                                       
                                                                                          
                                                      
                                                                       
                                                                     
                                        

/-! ### Step 2-3: structural bridges for `A ∈ E(P)`, `A ⊄ L` (mmd L3845-3858)

We pick `A ∈ maxElemAbelianIn P p` with `A ⊄ L = O_p(G)`.  These bridges express
the basic structural relations between `A`, `D := A ⊓ L`, and the global subgroups
of `G` needed in subsequent steps.

The book takes `A ∈ E(P)` failing to lie in `L` for the contradiction in Step 7.
We package the elementary observations: `A` is an elementary abelian `p`-subgroup
of `P`, hence contained in `P`; and `D = A ⊓ L` is a proper subgroup of `A` (with
nontrivial quotient `A/D`). -/

                                                           
                                                                          

                                                        
                                                                            
                                                                                   
                                                                          
                                
                                                
                              
        

                                                                
                                
                                                
              
      

                                                                                           

                                                                                
                                                                               
                                                                       

                                                                                     
                                                                         
                                                                              
                                                                           
                                                                                 
                  

                                                                             
                                            
                                                        
                                                                     
                                       
                                     
                                                                               
                                             
                           

                                                                            

                                                                                 
                
                                               
                                                    
                                       
                   
                

/-! ### Step 4: action of `A` on `V := Z(L) = Z(O_p(G))` (mmd L3858-3864)

Set `V := Z(L)`.  Since `L = O_p(G)` is `G`-normal, the conjugation action of `G`
on `L` restricts to an action on `Z(L)`, and in particular `A ≤ P ≤ G` acts on `V`.
Furthermore `D = A ⊓ L ≤ L` commutes with all of `V = Z(L)` by definition of
center, so `D` is contained in the kernel of the action of `A` on `V`. -/

/-- **Isaacs Thm 7.6 Step 4** (mmd L3858): `Z(O_p(G))` is `G`-normal (and `G`-characteristic).

The `Subgroup.center` of a characteristic subgroup is itself characteristic in the
ambient group.  In particular `Subgroup.center` of `O_p(G)`, viewed as the image
of `Subgroup.center (opCore p G)` in `G`, is `G`-normal. -/
private theorem center_opCore_map_normal {G : Type*} [Group G] {p : ℕ} :
    ((Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)).map
      (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G).subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨⟨z, hz_L⟩, hz_center, rfl⟩ g
  -- g * z * g⁻¹ ∈ opCore p G  (since opCore is normal)
  have hLnorm : (OddOrder.Isaacs.Ch01.opCore p G).Normal := inferInstance
  have hgz : g * z * g⁻¹ ∈ OddOrder.Isaacs.Ch01.opCore p G :=
    hLnorm.conj_mem z hz_L g
  refine ⟨⟨g * z * g⁻¹, hgz⟩, ?_, rfl⟩
  -- Show ⟨g*z*g⁻¹, _⟩ ∈ Subgroup.center (opCore p G).
  change (⟨g * z * g⁻¹, hgz⟩ : OddOrder.Isaacs.Ch01.opCore p G) ∈
    Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G)
  rw [Subgroup.mem_center_iff]
  rintro ⟨h, hh_L⟩
  -- ⟨h, hh_L⟩ * ⟨g*z*g⁻¹, hgz⟩ = ⟨g*z*g⁻¹, hgz⟩ * ⟨h, hh_L⟩,
  -- i.e., h * (g*z*g⁻¹) = (g*z*g⁻¹) * h.
  have hgh : g⁻¹ * h * g ∈ OddOrder.Isaacs.Ch01.opCore p G := by
    have := hLnorm.conj_mem h hh_L g⁻¹
    simpa [mul_assoc] using this
  have hcomm : (⟨g⁻¹ * h * g, hgh⟩ : OddOrder.Isaacs.Ch01.opCore p G) * ⟨z, hz_L⟩
      = ⟨z, hz_L⟩ * ⟨g⁻¹ * h * g, hgh⟩ :=
    Subgroup.mem_center_iff.mp hz_center _
  have hcomm_G : (g⁻¹ * h * g) * z = z * (g⁻¹ * h * g) := congr_arg Subtype.val hcomm
  apply Subtype.ext
  calc h * (g * z * g⁻¹)
      = g * ((g⁻¹ * h * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [hcomm_G]
    _ = (g * z * g⁻¹) * h := by group

                                               
                                       

                                                                                   
                                                                                    
                                                                                    
                                                           
                                                      
                                             
                          
                                                                              
                                                                                
            
                                   
                                              
                                                                         
                                                           
                                                                       
                                                                                                     
                                                                                
                                        
                                          
                                          

/-! ### Step 5-6: action triviality on `V := Z(O_p(G))` (mmd L3864-3884)

The book applies Ch.6 Thm 6.20 + Ch.4 Cor 4.35 to deduce that the action of
`A/D ≅ ℤ/p` on `V = Z(L)` is trivial.  At the bridge layer we record:

* `V` is a finite abelian `p`-group (Ch.4 Cor 4.35 hypothesis).
* `Z(L)` is the centralizer of `L` inside `L`, which contains the image of
  `Z(P)` (by Step 1's `center_sylow_le_opCore_of_oPiCorePrime_eq_bot` and the
  fact that `Z(P)` ≤ centralizer (Z(P)) ≤ centralizer L ⊓ L = Z(L)`...).

The combined deduction "A trivial on `Ω₁ Z(L)` ⇒ A trivial on `Z(L)`" requires
both Thm 6.20 (factoring through cyclic quotients) and Cor 4.35 (Ω₁ argument).
We supply pieces; the full Step 5-6 deduction is deferred to a later session. -/

                                                                      

                                                                               
                                                     
                                                                                       
                                                                                  
                                                          

                                                                                    
          

                                                                                   
                                          
                                                    
              
                                                                           
                                                                  
                                  

                                                                                 

                                                                               
                                                                           
                                                                           
                               
                                  
                                     
                                                                             
                         
           
                                                                        
                                                     
                                                                           
                                                                                   
                                                                                
                   
                  

/-! ### Step 7 preparation: `V := Ω₁(Z(O_p(G)))` as a subgroup of `G` (sub-session A)

For the Step 5-6 application of Cor 4.35 we need
`V := Ω₁(Z(O_p(G)))`, i.e., `{z ∈ Z(O_p(G)) | z^p = 1}`.  Since `Z(O_p(G))`
is abelian (it is a center), this set forms a subgroup of `G` directly,
without taking a closure.  We package it as `omega1ZCenterOpCore` together
with its key properties: normal in `G`, contained in `O_p(G)`, abelian as
a group, and a `p`-group.

These are the structural ingredients for **Isaacs Thm 7.6 Step 7 sub-session
(A)**.  The downstream application combines `V` with Cor 4.35
(`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`) to derive
`[A, V] = ⊥` from the fixed-point hypothesis. -/

/-- Local notation shorthand inside §7B: the underlying subgroup of `Z(O_p(G))`
viewed inside `G` (i.e., the image of `Subgroup.center (opCore p G)` under
the inclusion `opCore p G ↪ G`). -/
def zCenterOpCoreSubgroup (G : Type*) [Group G] (p : ℕ) : Subgroup G :=
  (Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)).map
    (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G).subtype

                                               
                                     
                                                                       
                                      
            

private theorem zCenterOpCoreSubgroup_comm
    {G : Type*} [Group G] {p : ℕ} :
    ∀ x ∈ zCenterOpCoreSubgroup G p,
      ∀ y ∈ zCenterOpCoreSubgroup G p, x * y = y * x := by
  rintro _ ⟨⟨x, hx_L⟩, hx_center, rfl⟩ _ ⟨⟨y, hy_L⟩, hy_center, rfl⟩
  -- ⟨x, _⟩ ∈ Z(L) so commutes with ⟨y, _⟩ in L; project to G.
  -- mem_center_iff: x ∈ center ↔ ∀ g, g * x = x * g.
  have hcomm :
      (⟨y, hy_L⟩ : OddOrder.Isaacs.Ch01.opCore p G) * ⟨x, hx_L⟩ =
        ⟨x, hx_L⟩ * ⟨y, hy_L⟩ :=
    Subgroup.mem_center_iff.mp hx_center _
  exact (congr_arg Subtype.val hcomm).symm

/-- **V := Ω₁(Z(O_p(G)))** as a subgroup of `G`.

The set `{g ∈ Z(O_p(G)) | g^p = 1}`, viewed inside `G`.  Since `Z(O_p(G))`
is abelian, this is a subgroup of `G` directly (no closure required).

This is the `V` of **Isaacs Thm 7.6 Step 7 sub-session (A)**: the bottom
layer `Ω₁` of the center of the `p`-core, on which the action of
`A ∈ E(P)` will be analyzed via Cor 4.35. -/
def omega1ZCenterOpCore (G : Type*) [Group G] (p : ℕ) : Subgroup G :=
  OddOrder.GroupTheory.omega1OfAbelian G (zCenterOpCoreSubgroup G p) p
    zCenterOpCoreSubgroup_comm

/-- Membership characterization for `V := Ω₁(Z(O_p(G)))`. -/
theorem mem_omega1ZCenterOpCore {G : Type*} [Group G] {p : ℕ} {g : G} :
    g ∈ omega1ZCenterOpCore G p ↔
      g ∈ zCenterOpCoreSubgroup G p ∧ g ^ p = 1 := by
  unfold omega1ZCenterOpCore
  exact OddOrder.GroupTheory.mem_omega1OfAbelian

/-- `V ≤ Z(O_p(G))` (the bottom layer is contained in the center it sits in). -/
theorem omega1ZCenterOpCore_le_zCenterOpCore
    {G : Type*} [Group G] {p : ℕ} :
    omega1ZCenterOpCore G p ≤ zCenterOpCoreSubgroup G p :=
  OddOrder.GroupTheory.omega1OfAbelian_le

                                                                            
                                     
                                     
                                                                  
                                                                            

/-- **Isaacs Thm 7.6 Step 7 sub-session (A)**: `V := Ω₁(Z(O_p(G)))` is normal in `G`.

Proof: `Z(O_p(G))` (as `zCenterOpCoreSubgroup`) is normal in `G` (already in
`center_opCore_map_normal`).  Conjugation by `g ∈ G` preserves the power map
`x ↦ x^p`, so it sends `{z ∈ Z(O_p(G)) | z^p = 1}` to itself. -/
instance omega1ZCenterOpCore_normal {G : Type*} [Group G] {p : ℕ} :
    (omega1ZCenterOpCore G p).Normal := by
  refine ⟨?_⟩
  intro n hn g
  rw [mem_omega1ZCenterOpCore] at hn ⊢
  refine ⟨?_, ?_⟩
  · -- Z(O_p(G)) is normal (center_opCore_map_normal).
    have h_norm : (zCenterOpCoreSubgroup G p).Normal := center_opCore_map_normal
    exact h_norm.conj_mem _ hn.1 g
  · -- (g * n * g⁻¹) ^ p = g * n^p * g⁻¹ = g * 1 * g⁻¹ = 1.
    calc (g * n * g⁻¹) ^ p
        = g * n ^ p * g⁻¹ := by rw [conj_pow]
      _ = g * 1 * g⁻¹ := by rw [hn.2]
      _ = 1 := by group

                                           

                                                                       
                                    
                                                    
                                           
                                                         
                                                      
                                    

/-- The elements of `V := Ω₁(Z(O_p(G)))` commute pairwise (V is abelian).

Inherited from the fact that they sit in `Z(O_p(G))`. -/
theorem omega1ZCenterOpCore_comm {G : Type*} [Group G] {p : ℕ} :
    ∀ x y : ↥(omega1ZCenterOpCore G p), x * y = y * x := by
  intro x y
  apply Subtype.ext
  have hx : (x : G) ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore x.2
  have hy : (y : G) ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore y.2
  exact zCenterOpCoreSubgroup_comm _ hx _ hy

/-- `V := Ω₁(Z(O_p(G)))` as a `CommGroup`.

The pairwise-commutativity from `omega1ZCenterOpCore_comm` upgrades the
ambient `Group ↥V` structure to `CommGroup`. -/
@[reducible] def omega1ZCenterOpCore_commGroup (G : Type*) [Group G] (p : ℕ) :
    CommGroup ↥(omega1ZCenterOpCore G p) :=
  { (inferInstance : Group ↥(omega1ZCenterOpCore G p)) with
    mul_comm := omega1ZCenterOpCore_comm }

                                                                    

                                                 
                                               
                                           
                                                       
                                     

/-! ### Step 7 sub-session (A): Cor 4.35 wrapper for `V := Ω₁(Z(O_p(G)))`

We specialize **Isaacs Cor 4.35**
(`OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`)
to `V := Ω₁(Z(O_p(G)))`: any `p'`-group `A` acting on `V` that fixes every
element of order `p` (= every element of `V`!) has `actionCommutator φ = ⊥`.

The wrapper packages the `CommGroup`, `IsPGroup p`, `Finite` instances on `V`
so callers only need to supply the action `φ : A →* MulAut ↥V` and the
hypotheses `¬ p ∣ |A|` and the fixed-point property. -/

                                                                      
                        

                                                                                      
                                                                       
                                                                                

                   
                                                                                   
                                                              
                                        
                                                             
                                    
                                                     
                                 
                                                                
                                
                                                     
                                                   
                                     
                                                                                 
                                                            

/-- `Z(U) = Z(O_p(G))` is `G`-normal: it is the image of the center
of the (`G`-normal) `O_p(G)`, transported up via `center_opCore_map_normal`. -/
instance zCenterOpCoreSubgroup_normal
    {G : Type*} [Group G] {p : ℕ} :
    (zCenterOpCoreSubgroup G p).Normal := center_opCore_map_normal

/-- The conjugation action of an arbitrary subgroup `Q ≤ G` on `Z(U) = Z(O_p(G))`:
`Q →* MulAut Z(U)` via `MulAut.conjNormal ∘ Q.subtype`.

Used in Step 6: `Q` (a Sylow `q`-subgroup of `K = C_G(V)`, `q ≠ p`) acts on
`Z(U)` by conjugation; combined with `Q` fixing `V = Ω₁ Z(U)` (from `Q ⊆ K`),
Cor 4.35 yields `Q` acts trivially on `Z(U)`. -/
noncomputable def conjActionOnZCenterOpCoreSubgroup
    {G : Type*} [Group G] {p : ℕ} (Q : Subgroup G) :
    Q →* MulAut ↥(zCenterOpCoreSubgroup G p) :=
  MulAut.conjNormal.comp Q.subtype


                                                                        
                        
                                      
                                                               
                                             
                                                                                  

/-- Pairwise commutativity on the subtype ↥(Z(U)). -/
theorem zCenterOpCoreSubgroup_comm_subtype
    {G : Type*} [Group G] {p : ℕ} :
    ∀ x y : ↥(zCenterOpCoreSubgroup G p), x * y = y * x := by
  intro x y
  apply Subtype.ext
  exact zCenterOpCoreSubgroup_comm _ x.2 _ y.2

/-- `Z(U)` as a `CommGroup`. -/
@[reducible] def zCenterOpCoreSubgroup_commGroup
    (G : Type*) [Group G] (p : ℕ) :
    CommGroup ↥(zCenterOpCoreSubgroup G p) :=
  { (inferInstance : Group ↥(zCenterOpCoreSubgroup G p)) with
    mul_comm := zCenterOpCoreSubgroup_comm_subtype }

                                                                                 
                                 
                                       
                                     
                                                                        
                            
                                                                       
                                                       
                     

                                                         

                                                                         
                                                                     
                                          
                                                             
                                    
                                                       
                                 
                                                                  
                                
                                                     
                                                     
                                       
                                                                                 
                                                              

/-- Generic: a subgroup-level `IsElementaryAbelian p H` upgrades the ambient
`Group ↥H` to a `CommGroup ↥H` using the commutativity component.  Local
construction used when applying CommGroup-requiring lemmas (e.g., index
calculations) on elementary abelian subgroups. -/
@[reducible] def isElementaryAbelian_commGroup
    {G : Type*} [Group G] {p : ℕ} {H : Subgroup G} (hH : H.IsElementaryAbelian p) :
    CommGroup ↥H :=
  { (inferInstance : Group ↥H) with mul_comm := hH.1 }

                                                                           
                                                                                
                                      
                                                               
                                       
                                                              
                                             
                                                       
                                                                      
                                                                                  
               
                    
                                                                

                                                                             
                                        
                                                        
                                                             
                    
                                                                            
                                                             
                                     
                                                  

/-- `V ⊆ centralizer U` in `G`: since `V ⊆ Z(U)`, every element of `V`
commutes with every element of `U`.  Used in Step 7 to argue `V * D`
is abelian (`V ⊆ centralizer U ⊇ D`). -/
theorem omega1ZCenterOpCore_centralizes_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    omega1ZCenterOpCore G p ≤
      Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) := by
  intro x hx
  have hx_ZU : x ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore hx
  rcases hx_ZU with ⟨⟨z, hz_U⟩, hz_center, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hcomm : (⟨u, hu⟩ : ↥(OddOrder.Isaacs.Ch01.opCore p G)) * ⟨z, hz_U⟩ =
      ⟨z, hz_U⟩ * ⟨u, hu⟩ :=
    Subgroup.mem_center_iff.mp hz_center _
  exact congr_arg Subtype.val hcomm

                                                                                  
                                    
                                                               
                                         
                                                                                        
                                                     
                                            
                                                           
                                                                         

                                                                             
                                                                           
                                                       
                                                      
                                                                                   
                      
                                         
                     
                                                 
                     
                               
                                                                                                 
                                                                                         
                              
                     
                         
                                                         
                                                                                    

                                                                      
                                                                     
                                                              
                                               
                                                               
                                                         
                                           
         
                   
                        
                                                   

                                                                             
                                                                    

                                                                            
                                                            
                                                                    
                                                             
                                                          
                                                                                 
                                                                       
                                     
                                                 
                           
                                                                
                                                        
                                            
                                                                            
                                               
                                                                           
                                                       
                              
         
                   
                                                  
                                                                                  
                                                                         
                                                
                                           
                                   

                                                                                
                                               
                                                               
                               
                                                                  
            
                                   
            
                                                                           
                                                               
                                   

/-- **Isaacs Thm 7.6 Step 6 setup** (mmd L3879): `K := C_G(V)` (where
`V = Ω₁(Z(O_p(G)))`) is `G`-normal.  Trivial: centralizers of normal subgroups
are normal. -/
instance centralizer_omega1ZCenterOpCore_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)).Normal :=
  Subgroup.normal_centralizer

                                                                          
                                                                
                                                             
                                                             
                                                                                   
                                                              
                                        
                                                    

/-! ### Step 6 main: `K := C_G(V)` is a `p`-group (mmd L3879-3884)

This is the heart of Step 6: for every prime `q ≠ p`, the action of any
Sylow `q`-subgroup `Q` of `K` on `Z(U) = Z(O_p(G))` (by conjugation) is
forced to be trivial via Cor 4.35 (`Q` fixes every element of order `p`
in `Z(U)`, namely all of `V`), so `Q ⊆ C_G(Z(U)) ⊆ C_G(Z(P)) = P`.  Then
`Q ⊆ P ∩ K`, but `Q` is a `q`-group and `P` is a `p`-group with `q ≠ p`,
forcing `Q = ⊥`.  Since all primes `q ≠ p` give trivial Sylow `q`-subgroups
of `K`, `K` is a `p`-group. -/

                                                                                
                                                                         
                                                                              
                     
                                                                    
                                                             
                    
                                                                            
                                                                        
                                                       
                                                              
                                                       
                                
                        
                                                      
                                                                                      
                                                                     
                 
                                                                 
                                                            
                                                                   
                   
                                                                            
                                          
                                                                                 
             

                                                                        
                                 

                                                                                 
                                                                               
                                                                                  
                                                                       
                                                      
                                                             
                                                  
                                          
                                                                              
                                                                        
                                        
                                                                  
                                       
                                                   
           
               
                                       
                                                            
                                        
                                                                              
                       
                                                                                        
                 
                                                                                 
                
                                                                                 
                                                                                             
                                                                    
                                                                  
                  
                                                         
                                                         
                                                                                   
                                              
                
                                   
             
                                                                                             
                                                                               
                                                        
                                                                                              
                                                                                          
                                                                                             
                                                            
                 
                                                          
                                                                                                 
                                                                       
                                                               
                          

                                                                        
                                                                

                                                                                   
                                                                                          
                                                                     
                                        
                                                             
                                                          
                                                                               
                           
                           
                                                                                    
                            
                                                  
                                          
                                                                              
                                
                     
                                                                                 
                                                                    
                                                   
                  
                                                                                        
                                    
                                                                       
                      
                                                                  
                            
                                                                                        
                                     
                                            
                                  

                                                                    
                                                                            

                                                                                   
                                                                                   
                                      
                                                             
                                                          
                                                                               
                           
                           
                                                                                    
                            
                                                  
                                          
                                                                              
                 
                                        
                                          
                                                                                  
                                                                        
                                                        
                                                
                                                  
                                                  
                                     
                                     
                                                   
                  
                               
                          
                                                        
               
                  
                          
                                   
                                                                                     
                          
                                                                
                                                                              
                  
                                            

                                                                     
                                                                             

                                                                                  
                                                                                   
                                                                      
                                                                    

                                                                                  
                                                
                                                             
                                                          
                                                                               
                           
                           
                                                                                    
                              
                                                                             
                                                                                       
                           
                      
                                                                                          
                                                           
                                      
                                                                                  
               
                                                          
                  
                    
                                      
                                     
                                   
                                                                      
                   
                     
                                                   
                                   
                                                  
                                                                       
                                               
                                
                       
              
                                                                                
                 
                                     
                                                       
                                      
                                               
                                              
                                       
                                                                                 
                                               
                                     
              
                                    
                                                       
                                            
                                                            
                                                                                        
                                                     
         
                   
                                        
                                                                                
                                                               
                                                        
                 
                                               
                                                        
                                          
                          
                      
                                          
                                                      
                                        
                                                 
                                                
                                                                                
                                                                
                                                                     
                                       
                      

                                                                                  
                                                                                
                                                     
                                                               
                                                             
                                                                         
                                          
                                                                
                                                                                        
                                                     
                              
            
                                                                 
                                             
                                                           
                                                                                 

/-! ### Step 7 counting argument: `|V : V ∩ A| ≤ p` (mmd L3886-3892)

The book's Step 7 derives a counting bound on `V := Ω₁ Z(O_p(G))`:

> Write `D = U ∩ A` and `E = V ∩ A`.  Then `|V:E| = |V:V∩D| = |VD:D|`.  Now
> `D` is elementary abelian in `U`, and `V` is a central elementary abelian
> subgroup of `U`, so `VD` is elementary abelian.  By `A ∈ E(P)`, `|VD| ≤ |A|`,
> hence `|VD:D| ≤ |A:D| = |Ā| = p`.

We package this combinatorial step as `omega1ZCenterOpCore_relIndex_inter_A_le`,
isolating from the broader Goldschmidt argument the part that only needs
elementary-abelian structure, `V ≤ centralizer U`, and the maximality of
`A ∈ maxElemAbelianIn P p`.

The hypothesis `|A : A ⊓ U| ≤ p` is supplied externally (it is the Step 5
conclusion `|Ā| = p`). -/

                                                                       
                                                            

                                                                                 
                                                       
                                            
                                             
                                             
                                                    
                                                                                          
                                                                                      
                                                                               
                                                        
                                                      
                                                                 
                                                                           
              
                                                      
              
                                                                        
                                                                             
                                       
            
                                                                   
                                                           
                 
                                                        
                                
                                   
                                                      
                                          
                                                         
                                   
                                                       
                               
                                   
                                                         
                                   
                                                       
                                      
                                                      
                                          
                                  
                          
                                                
                                     
                                   
                                     
                                   
                   
                                      
                                                             
                                                      
                                  
                                                                                   
                                                            
            
                                                                  
                                                                           
                                     
                                                         

                                                                              
                                                                               
                   

                                                                                 
                                                                                
                           
                                                       
                                                                 
                                                                 
                                                    
                                                      
                                             
                                                              
                                                         
                                                                                 
                                                                                                   
              
                                                                          
                                                    
                        
                                            
                                 
                     
                                 
             
                     
                                  
                                                 
                                                
                   
                                                             
           
                     
                              
                                           
                                                               
                   
                                                                           
                                        
                              
                                                  
                                 
                                        
                                                                
             
                               
                                
                                      
                               
                                
                                      
                            

                                                                             
                                                                      

                                                  
                                                       
                                                           

                    
                                                                                    
                                          
                                                                          
                                                                                     
                                                          
                                                                         
                                                                                 
                                                                            
                                               
                                                             
                                    
                                                             
                                                                          
                                                    
           
                                                           
                                                                   
                                           
                 
                                                         
                                            
                                                                        
                                                
                                         
                                                          
                                                                                 
                                                            
                                          
                                        
                                       
                                                            
                                                     
                                   
                                                
                                                               
                                                                 
                   
                                                                   
                   
                                                      
                                        
                                                                        
                                    
                                                                                  
                                                                                         
                                          
                                                      
                                                  
                                                 
                                                                  
                                                                                
                                                                                           
                                                                                           
                                             
                                                      
                           
             
                                                                                       
                                                              
                                                    
              
                                    
           
                                                                         
                                                                                                
               
               
                                                                              
                                         
                                                             
                           
              
              
                
                                                                                    
                                                              
                                                                       
                                          
                                                                
                                        
                     
               
                                             
                                                      
                                                                         
                                                  
                                                         
                                                    
                                                             
                                                        
                                          
                  
                                                                                  
                                                     
                                           
                       
                
                                                                    
                                                   
                                                                
                                                     
                                                   
                               
                                                                   
                                                                                          
                                                 
                                                
                                                                      
                                                                  
                           
                                                              
                                         
                                                             
                                                    
                                                 
                               
                                                                        
                                                                
                                                                                             
                                           
                                               
                                                                   
                                                                 
                                                 
                                                            
                                               
                                                             
                                                                   
                                                                               
                                  
                        
                                                                            

/-! ### Step 7-8: closing reductions (mmd L3884-3896)

Once Step 5-6 produce the triviality of the `A`-action on `V = Z(L)`, the book:

* (Step 7) Combines `[A, V] = 1` with hypothesis (v) `P = C_G(Z(P))` and the
  maximality of `A ∈ E(P)` to force `A ⊆ L`, contradicting `A ⊄ L`.
* (Step 8) From Step 2's conclusion `J(P) ≤ L`, applies Thm 7.2
  (`thompsonJ_eq_of_le_of_le`) to get `J(L) = J(P)`, then uses that `J(L)` is
  characteristic in `L` and `L` is characteristic in `G` to conclude
  `J(P) ⊴ G`.

The Step 7 contradiction itself is a delicate counting argument over `E(P)`
combined with the action analysis; we defer it.  Step 8 only needs the Thm 7.2
bridge, which we record here. -/

                                                                             
                                                                        
                                                                          
                                                              
                                                                                        
                                                                         
                                              
                                                                           

                                                                               

                                                                                  
                                                                                
                                                                           
             
                                         
                                                                      
                                                        
                                                                             
                         
                            
                               
                                    
                               
                              
                                            
                       
                                                                     
                       
                                                                                      
                                        
                                                         
                                     
                                              
                                            
                                                   
                                                           
                                         
                       
                                     
                                 
                                                 
                                     
                               
                                    
                         
                                          
                         
                                                
                      
                                                                                        
                     
                                                           
                                                                                   
                     
                                                           
                     
                                                                    
                                 
                                      
                                           
                                     
                                                                                         
                         
                                                                       
                         
                                                                        
                                                                 
                                          
                                                          
                                       
                                                                    
                                                        
                                                               
                                                                                 
                                           
                         
                                                 
                                   
                                                  
                                       
                                           
                                                              
                                                      
                           
                                                                            
                             
              

                                                                                 
                                                                                      

                                                                                    
                                                                                            
                                      
                                     
                                                              
                                                                                        
                                                        
                                        
                                                                                   
                                              
                                                                     
               
                                                                    
                 
              
                                           
                                                               
                 
                                                                               
                                       
                                                                               
                                                                                
                                               
                                                                         
                          
                              
                          
                                   
                                                                           
                      
                                                                               
                                                                  
                                               
                                                           
                                         
                          
                                          
       
                     

/-! ### Step 7: contradiction giving `J(P) ≤ L` (mmd L3884-3892)

The book's Step 7 combines:

* The Step 5-6 conclusion: `A` acts trivially on `V := Z(O_p(G))`, i.e.,
  `[A, V] = 1` (`A` and `V` commute pointwise).
* The Step 1 conclusion: `Z(P) ≤ Z(L)` (Z(P) sits inside Z(L) since
  Z(P) commutes with all of L).
* The hypothesis (v): `P = C_G(Z(P))`.
* The maximality of `A ∈ E(P)`.

The combined counting argument forces `A ⊆ L`, contradicting the choice of
`A ⊄ L`.  This is the most delicate part of the Goldschmidt-style proof; we
**axiomatize the Step 7 conclusion** as the existence of a contradiction from
the working hypotheses, and use it together with Step 8's wrap-up.

Tracking issue: [`issues/0036-stuck-7-6-step-7.md`](../../../issues/0036-stuck-7-6-step-7.md). -/


end OddOrder.Isaacs.Ch07
