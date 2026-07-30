/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Submission.OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeAction

/-!
# BG §14 Proposition 14.2 support lemmas (`κ`-free)

**Scope**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter III, support for §14 Proposition 14.2 (mmd L3778).

Generic, `κ`-free utilities that BG Proposition 14.2 (`typeP_structure`, in
`S14_TypePCounting`, lane H) cites to transport the prime action and the
`M_σ`-centralizer witness across `M`-conjugacy:

* `smul_centralizer_singleton` / `smul_centralizer_subgroup`: conjugation transport for
  element- and subgroup-centralizers (`C_G(a)^m = C_G(a^m)`, `C_G(X)^m = C_G(X^m)`).
* `actsPrimeOn_conj`: `ActsPrimeOn N X → ActsPrimeOn N (X^m)` when `m ∈ N_G(N)`.
  Used in Proposition 14.2's `κ ⊆ τ₁` case (WLOG `K = E₁`: transport `E₁`'s prime
  action on `M_σ` to the `M`-conjugate Hall `κ`-subgroup `K`, since `M_σ ◁ M` and `m ∈ M`).

Stated entirely without reference to `κ(M)` (defined downstream in `S14_TypePCounting`)
so this leaf sits **below** that file in the import DAG; lane H imports it with one line.
See `issues/7000-s14-prop142-support.md`.
-/

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Conjugation transport for an element centralizer**: `C_G(a)^m = C_G(m a m⁻¹)`. -/
theorem smul_centralizer_singleton (m a : G) :
    MulAut.conj m • Subgroup.centralizer ({a} : Set G)
      = Subgroup.centralizer ({m * a * m⁻¹} : Set G) := by
  have himg : ({m * a * m⁻¹} : Set G) = (MulAut.conj m).toMonoidHom '' ({a} : Set G) := by
    simp [MulAut.conj_apply]
  rw [himg]
  exact Subgroup.map_centralizer_eq_of_bijective ({a} : Set G)
    (MulAut.conj m).toMonoidHom (MulAut.conj m).bijective

/-- **Conjugation transport for a subgroup centralizer**: `C_G(X)^m = C_G(X^m)`. -/
theorem smul_centralizer_subgroup (m : G) (X : Subgroup G) :
    MulAut.conj m • Subgroup.centralizer (X : Set G)
      = Subgroup.centralizer ((MulAut.conj m • X : Subgroup G) : Set G) :=
  Subgroup.map_centralizer_eq_of_bijective (X : Set G) (MulAut.conj m).toMonoidHom
    (MulAut.conj m).bijective

                                                                                       
                                                                                           
                                                                     

                                                                                                
                                                                                         
                                                                            

                                                                                             
                                                                                      
                                                   
                                                              
                                             
                                                                                
                
                                                         
                                                   
                                                                                 
                                       
                                                               
                            
                                                   
                                                                                          
                     
                                                  
                                                                                    
                                       
             

end OddOrder.BG.Ch3.S13
