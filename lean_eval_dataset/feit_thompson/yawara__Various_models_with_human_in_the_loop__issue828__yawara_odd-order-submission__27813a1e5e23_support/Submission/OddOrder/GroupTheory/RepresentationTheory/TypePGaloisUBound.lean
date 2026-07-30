/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Submission.OddOrder.GroupTheory.RepresentationTheory.SingerLineBound
import Submission.OddOrder.GroupTheory.RepresentationTheory.SemilinearImprimitiveBound
import Submission.OddOrder.GroupTheory.RepresentationTheory.LineScalarCharacter
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The `typeP_Galois` `u`-bound dichotomy: `|U| ≤ (p^q − 1)/(p − 1)`

The σ-theory foundation entry point (issue 9000, step 3) for Peterfalvi (13.2.c)
`basic_structure.u_bound`.  A faithful fixed-point-free abelian action of `U` on `Hbar ≅ 𝔽_p^q`
(`q` prime) satisfies `|U| ≤ (p^q − 1)/(p − 1)` regardless of `typeP_Galois`:

* **Galois** (`IsSimpleModule` — `U` irreducible): the Singer line bound
  `card_le_cyclotomicQuotient_of_faithful_irreducible_fpf` (`SingerLineBound`) gives it directly.
* **non-Galois** (reducible): the imprimitive block structure gives
  `|U| ≤ (p−1)^{q−1} ≤ (p^q−1)/(p−1)`
  (`card_le_cyclotomicQuotient_of_injective_imprimitive`, `SemilinearImprimitiveBound`).

This file packages the case split so a consumer (lane a's Pf (9.7) assembly / `basic_structure`)
cites one lemma.  The **non-Galois branch is exposed as a hypothesis** `hReducible` — the
imprimitive decomposition (`Hbar = ⊕ H1^w`, the ratio embedding `Ū ↪ ℤ_a^{q−1}`) is the
`𝔽_p`-module + `W₁`-permutation content, discharged by the caller via
`card_le_cyclotomicQuotient_of_injective_imprimitive`; the Galois branch is fully proven here.
-/

namespace OddOrder.RepresentationTheory

universe u

/-- **The qualitative block-scalar product embedding.**  Under the imprimitive block hypotheses,
the normalized scalar-ratio homomorphism embeds `U` into `n` copies of `(ZMod p)ˣ`.

This is the group-structural form of the block engine.  The cardinality and divisibility theorems
below forget this map; Peterfalvi (14.6) instead restricts it to a Sylow subgroup. -/
theorem exists_blockScalarRatioEmbedding_of_blocks {p : ℕ} [Fact p.Prime]
    {U M : Type u} [CommGroup U] [Finite U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    {n : ℕ} (ρ : Representation (ZMod p) U M) (B : Fin (n + 1) → Subrepresentation ρ)
    (hBcard : ∀ i, Nat.card (B i).toSubmodule = p)
    (hconst : ∀ u : U,
        (∀ i : Fin (n + 1),
          lineScalarChar (B i).toRepresentation
              (finrank_eq_one_of_card_eq_prime (hBcard i)) u
            = lineScalarChar (B 0).toRepresentation
                (finrank_eq_one_of_card_eq_prime (hBcard 0)) u)
        → u = 1) :
    ∃ ψ : U →* (Fin n → (ZMod p)ˣ), Function.Injective ψ :=
  ⟨blockScalarRatioHom (fun i => lineScalarChar (B i).toRepresentation
      (finrank_eq_one_of_card_eq_prime (hBcard i))),
    blockScalarRatioHom_injective _ hconst⟩

/-- The scalar-character identity on an order-`p` subrepresentation, viewed in the ambient
representation.  This avoids exposing the subtype module's implementation instances to callers
that assemble the block identities into an equality on the whole representation. -/
theorem lineScalarChar_smul_coe_of_card_eq_prime {p : ℕ} [Fact p.Prime]
    {U M : Type u} [Group U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    (ρ : Representation (ZMod p) U M) (B : Subrepresentation ρ)
    (hBcard : Nat.card B.toSubmodule = p) (u : U) (x : B) :
    ρ u x.1 =
      (lineScalarChar B.toRepresentation
        (finrank_eq_one_of_card_eq_prime hBcard) u : ZMod p) • x.1 := by
  change (↑(B.toRepresentation u x) : M) = _
  simpa using congrArg Subtype.val
    (lineScalarChar_smul B.toRepresentation
      (finrank_eq_one_of_card_eq_prime hBcard) u x)

                                                                                              
                                                                           

                                                                                                  
                                                       
                                                                                                   
                                                                 
                                                  
                                             
                                                        
                                         
                                                
                                                                                        
                   
                                                                           
                                                                                  
                                                                    
                                               
                                              
                                                                
                     
                                                                                         
                             

                                                                                               
                                                                                           

                                                                                            
                                                                                                
                                                            
                                                                                           
                                                                                           
                                                    
                        
                             
                                                                                              
                                                   
                                                               
                    
                                    
                                                       
                                 
                                                     
                                                     
            
                                                 
                                                                                         
                      
                                                                                          
                                                                                            
                                                                                              
                                                                                                  
                                               

                                                                                                    
                                                                                 
                                                                                
                                                                                                    
                                                                                                      
                                                                               
                                                                     
                                                                                           
                                                                                           
                                                    
                        
                             
                                                                                              
                                                                                                   
                    
                                                    
                                                     
                                
                                                                                                   
            
                                                 
                                                                                         
                   
                                       
                                           
                                                                         
                                                
                     

end OddOrder.RepresentationTheory
