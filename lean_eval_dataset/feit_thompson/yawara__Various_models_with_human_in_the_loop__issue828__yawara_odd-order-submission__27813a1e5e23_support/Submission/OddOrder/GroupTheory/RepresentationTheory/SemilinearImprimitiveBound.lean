/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finite.Prod
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.GroupTheory.Coset.Card

/-!
# The imprimitive order bound: `|U| ≤ (p − 1)^(q−1)`

The σ-theory foundation of Peterfalvi (9.7)(a) (the *non-Galois* branch of `typeP_Galois`, issue
9000): when the abelian complement `U` acts on the Frobenius kernel quotient `Hbar ≅ 𝔽_p^q` (`q`
prime) **reducibly**, `Hbar` decomposes into `q` one-dimensional blocks `H1^w` (`|H1| = p`) permuted
cyclically by `W₁`.  Writing `a := |U : C_U(H1)|` for the order of the scalar action on a block
(`a ∣ p − 1`, since `U/C_U(H1) ↪ 𝔽_p^×`), the map `x ↦ (block-scalar_i(x)/block-scalar_1(x))_i`
embeds `Ū` injectively into `ℤ_a^{q−1}` (the `−1` normalizing by block `1`), whence

  `u = |Ū| ≤ a^{q−1} ≤ (p − 1)^{q−1}`.

This file supplies the **generic arithmetic engine** — an injective map into a `(q−1)`-fold product
of an `a`-element type bounds the source by `a^{q−1}`, and `a ≤ p − 1` lifts it to `(p−1)^{q−1}`.
The structural inputs (the block decomposition and the injectivity of the ratio embedding) are the
imprimitive `𝔽_p`-module content, supplied by the caller (the Pf (9.7)(a) assembly); combined with
`(p−1)^{q−1} ≤ (p^q−1)/(p−1)` this yields the non-Galois half of `basic_structure.u_bound`.
-/

namespace OddOrder.RepresentationTheory

                                                                                                     
                                                                                          
                                                             
                                                                         
                                                           
                                       
                                                                                       
                                                         
                      
                

                                                                                                 
                                                                                                        

                                                                                                      
                                                                                                            
                                                                                   
                                                                                
                                                    
                                          
                                                
                                                                 
                                          
                                            
                                             
                        
                                           

/-- **The block-scalar ratio homomorphism** in Peterfalvi (9.7.a):
`x ↦ (φ_{i+1}(x) / φ_0(x))_i`.

Normalizing all scalar coordinates by the zeroth one removes the common-scalar diagonal and leaves
`n` coordinates from an `n + 1` block system.  The target is a group because scalar values lie
in the commutative group `A`. -/
def blockScalarRatioHom {Ubar A : Type*} [Group Ubar] [CommGroup A] {n : ℕ}
    (φ : Fin (n + 1) → (Ubar →* A)) : Ubar →* (Fin n → A) where
  toFun x i := φ i.succ x / φ 0 x
  map_one' := by
    ext i
    simp
  map_mul' x y := by
    ext i
    simp only [Pi.mul_apply, map_mul, div_eq_mul_inv, mul_inv_rev]
    ac_rfl

/-- **Injectivity of the block-scalar ratio homomorphism.**  If an element whose scalar values are
constant on all `n + 1` blocks is necessarily trivial, then the normalized ratio homomorphism is
injective.  This is the qualitative form of the (9.7.a) product embedding; unlike its cardinality
corollaries below, it can be restricted to Sylow subgroups by downstream consumers. -/
theorem blockScalarRatioHom_injective {Ubar A : Type*} [Group Ubar] [CommGroup A] {n : ℕ}
    (φ : Fin (n + 1) → (Ubar →* A))
    (hconst : ∀ x : Ubar, (∀ i : Fin (n + 1), φ i x = φ 0 x) → x = 1) :
    Function.Injective (blockScalarRatioHom φ) := by
  intro x y hxy
  have hxy' : ∀ i : Fin n, φ i.succ x / φ 0 x = φ i.succ y / φ 0 y :=
    fun i => congrFun hxy i
  have hz : x * y⁻¹ = 1 := by
    apply hconst
    refine Fin.cases rfl (fun j => ?_)
    have h : φ j.succ x * φ 0 y = φ j.succ y * φ 0 x :=
      (div_eq_div_iff_mul_eq_mul).mp (hxy' j)
    change φ j.succ (x * y⁻¹) = φ 0 (x * y⁻¹)
    rw [map_mul, map_mul, map_inv, map_inv, ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_eq_div_iff_mul_eq_mul, mul_comm (φ 0 x)]
    exact h
  exact mul_inv_eq_one.mp hz

                                                                                
                                                                    

                                     
                                                                                              
                                                                                                  
                                                                                                 
                                                                     
                                                                                     
                            
                                                  
                                                                               
                                          
                           
                                                           
                                               

                                                                                                
                                                                                           
                                                                                                              
                                                                                            
                                                                                                           

                   

                                                                                                            
                                                                                                           
                                                                                                      
                                
                                                                                    
                            
                                                  
                                                                               
                                          
                    
                                                                   
                                                 
                                               

/-- **Non-Galois → cyclotomic-quotient bridge**: `(p − 1)^{q−1} ≤ (p^q − 1)/(p − 1)`.

`(p−1)^{q−1}·(p−1) = (p−1)^q < p^q`, so `(p−1)^q ≤ p^q − 1`; division by `p − 1`
gives the claim.
Pure `ℕ` arithmetic, `sorry`-free.  Lifts the non-Galois bound `u ≤ (p−1)^{q−1}` to the uniform
`u ≤ (p^q − 1)/(p − 1)` matching the Galois branch (`SingerLineBound`). -/
theorem pow_sub_one_le_cyclotomicQuotient {p q : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q) :
    (p - 1) ^ (q - 1) ≤ (p ^ q - 1) / (p - 1) := by
  have hp1 : 0 < p - 1 := by omega
  rw [Nat.le_div_iff_mul_le hp1]
  have hpow : (p - 1) ^ (q - 1) * (p - 1) = (p - 1) ^ q := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow]
  have hlt : (p - 1) ^ q < p ^ q := Nat.pow_lt_pow_left (by omega) (by omega)
  have hpq1 : 1 ≤ p ^ q := Nat.one_le_pow _ _ (by omega)
  omega

                                                                                                
                                                                                                

                                  

                                                                                                  
                                                                                      
                                       
                                                           
                                                                        
                                                
                                                                 
                                           
                                                                   
                                             

end OddOrder.RepresentationTheory
