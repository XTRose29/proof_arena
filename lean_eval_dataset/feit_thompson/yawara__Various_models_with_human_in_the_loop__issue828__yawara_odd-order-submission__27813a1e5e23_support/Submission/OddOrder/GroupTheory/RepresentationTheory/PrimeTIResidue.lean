/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Submission.OddOrder.GroupTheory.RepresentationTheory.IsometryDifferencePair
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedTransport
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier
import Submission.OddOrder.Peterfalvi.S05_SigmaIsometry
import Submission.OddOrder.Peterfalvi.S06_CertainTypeClifford
import Submission.OddOrder.Peterfalvi.S06_CertainTypeSupport
import Submission.OddOrder.Peterfalvi.S07_Coherence
import Submission.OddOrder.Peterfalvi.S08_CoherenceCorePart1

/-!
# Prime-TI residue characters (Peterfalvi (4.5), Feit–Thompson (13.2–13.3))

This module ports the **core of the prime-TI residue theory** from mathcomp's
`character` library (`coq/theories/PFsection4.v`, definitions `primeTIred`,
`prTIres_irr_cases`, `cfInd_prTIres`), which Peterfalvi's `S1cases`
(`coq/theories/PFsection13.v:401-428`) depends on.

## Mathematical setup

Let `S = PU ⋊ W1` be a group with `W = W1 × W2` an abelian TI-subgroup of prime-order
cyclic factors (Peterfalvi Hypothesis (4.2) = Feit–Thompson (13.2)).  The **prime-TI
irreducibles** `mu2_ i j ∈ Irr(S)` (`i : Iirr W1`, `j : Iirr W2`) are the constituents of
the images `σ(w_ i j)` of the linear characters of `W` under the cyclic-TI isometry
`σ = cyclicTIiso`.  Their **column sums**

  `primeTIred j := μ_j := ∑_i mu2_ i j ∈ ℂ CF(S)`   (Coq `primeTIred`)

are *reducible* characters, and each `μ_j` is induced from an irreducible **residue**
`chi_ j ∈ Irr(PU)` of `PU = S'`:

  `Ind_{PU}^S (chi_ j) = μ_j`   (Coq `cfInd_prTIres`).

The constituent classification `prTIres_irr_cases` says: for every `θ ∈ Irr(PU)`, either
`θ = chi_ j` for some `j` (equivalently `Ind θ = μ_j`), or `Ind θ` is irreducible.

## What this file builds, and the port's shape

The construction of `mu2_ i j` itself sits on top of the **entire mathcomp cyclic-TI
isometry stack** (`cyclicTIiso`, `dirr_dIirr`, `PFsection3.v`), which is not yet in this
repo.  Following the established repo idiom for such deep character data
(`OddOrder.Peterfalvi.S06.Hypothesis46`, `SignedIrreducibleDifferenceFamily`,
`FullDadeIsometryData`), we **posit the (4.3.b)/(4.5.a) residue grid as fields** of a
structure `PrimeTIResidueData`, packaging the prime-TI irreducibles, their residues, and
their *defining relations* (each of which mathcomp's `primeTIirr_spec` / `prTIres_spec`
*proves*).  On top of these fields we then build, **sorry-free**, the derived residue API
that `S1cases` consumes:

* `primeTIred`, `prTIred_char`, `prTIred_neq0`, `prTIred_not_irr`;
* the inner products `cfdot_prTIirr_red`, `cfdot_prTIred`, `cfnorm_prTIred`, `prTIred_inj`;
* the induction formula `cfInd_prTIres` and restriction `cfRes_prTIred`;
* `prTIres0` (`chi_ 0 = 1`), `prTIred0`.

The single genuinely-deep sub-fact, `prTIres_irr_cases` (Peterfalvi (4.5.b), the inertia-group /
`p`-group fixed-point counting argument, Coq `PFsection4.v:620-665`), is **posited as the field
`PrimeTIResidueData.prTIres_irr_cases`** rather than derived: its mathcomp proof computes the
inertia group `'I_S[θ] = PU` from the cyclic-TI structure (`W1`, the decomposition
`S = PU ⋊ W1`, the `W1`-action on `Irr(PU)`, and `coprime |PU| |W1|`), which is exactly the data
that is abstracted away here and supplied by the constructor together with `mu2`/`chi`.  It is
therefore on the same honest footing as the other `cyclicTIiso`-provenance fields
(`mu2_orthonormal`, `chi_res`, `ind_chi`, `cfker_prTIres`), all of which are genuine mathcomp
theorems the constructor discharges.  With this the leaf is **sorry-free**.

The eventual **constructor** of `PrimeTIResidueData` (from a genuine
`primeTI_hypothesis`, via a Lean port of `cyclicTIiso` + `primeTIirr_spec`, which discharges
`prTIres_irr_cases` via `card_afix_irr_classes` + `IsPGroup.card_modEq_card_fixedPoints` and the
repo capstone `isIrreducibleCharacter_induce_of_inertia_eq`) is the multi-session continuation
tracked in `issues/9014-primeti-residue-api.md`.

## References

* Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §4,
  Theorems (4.3), (4.5).
* Coq: `coq/theories/PFsection4.v` (`primeTIred`, `cfInd_prTIres`, `prTIres_irr_cases`);
  `coq/theories/PFsection13.v:401-428` (`S1cases`, the consumer).
* `issues/9014-primeti-residue-api.md`.
-/

namespace OddOrder.RepresentationTheory

open scoped BigOperators
open OddOrder.Peterfalvi.S07 (zSpan)

/-! ### The prime-TI residue datum

`PrimeTIResidueData S PU q p` posits, over a group `S` with commutator-type subgroup
`PU ≤ S` (Coq `PU = S^(1)`), the prime-TI residue grid: `q = #|W1|` column-index bound
(indices `i : Fin q`), `p = #|W2|` residue-index bound (indices `j : Fin p`).  The fields
mirror the *conclusions* of `primeTIirr_spec` and `prTIres_spec`. -/

/-- **Prime-TI residue datum** (Peterfalvi (4.3.b)+(4.5.a), Coq `PFsection4.v`).

Bundles, over the pair `PU ≤ S`, the data that mathcomp derives from a
`primeTI_hypothesis` via `cyclicTIiso`:

* `mu2 i j ∈ Irr(S)` — the prime-TI irreducibles (`mu2_ i j`), `i : Fin q`, `j : Fin p`;
* `chi j ∈ Irr(PU)` — the residue characters (`chi_ j`), `j : Fin p`;

together with their defining relations (each a mathcomp theorem):

* `mu2_orthonormal`  : `⟨mu2 i j, mu2 i' j'⟩ = [i=i' ∧ j=j']`   (Coq `cfdot_prTIirr`);
* `chi_res`          : `chi j = Res_{PU} (mu2 0 j)`               (Coq `cfRes_prTIirr`);
* `ind_chi`          : `Ind_{PU}^S (chi j) = ∑_i mu2 i j`         (Coq `cfInd_prTIres`);
* `chi_zero`         : `chi 0 = 1_{PU}`                           (Coq `prTIres0`).

The grid columns `i ↦ mu2 i j` correspond to `SignedIrreducibleDifferenceFamily` columns
(cf. `OddOrder.Peterfalvi.S06.Hypothesis.columnFamily`). -/
structure PrimeTIResidueData (S : Type*) [Group S] [Fintype S]
    [Invertible (Nat.card S : ℂ)] (PU : Subgroup S) [Fintype ↥PU]
    [Invertible (Nat.card ↥PU : ℂ)] (q p : ℕ) [NeZero q] [NeZero p] where
  /-- The prime-TI irreducibles `mu2_ i j ∈ Irr(S)` (Coq `primeTIirr`). -/
  mu2 : Fin q → Fin p → IrreducibleCharacter S
  /-- The residue characters `chi_ j ∈ Irr(PU)` (Coq `primeTIres`). -/
  chi : Fin p → IrreducibleCharacter ↥PU
  /-- **(4.3.b)** Orthonormality `⟨mu2 i j, mu2 i' j'⟩ = [(i,j) = (i',j')]` (Coq
  `cfdot_prTIirr`): the `mu2 i j` are pairwise-distinct irreducibles. -/
  mu2_orthonormal : ∀ (i i' : Fin q) (j j' : Fin p),
    ClassFunction.inner (mu2 i j : ClassFunction S ℂ) (mu2 i' j' : ClassFunction S ℂ)
      = (if i = i' ∧ j = j' then 1 else 0)
  /-- **(4.5.a)** Restriction to `PU`: `chi j = Res_{PU} (mu2 0 j)` (Coq `cfRes_prTIirr` at
  `i = 0`; the restriction of `mu2 i j` to `PU` is independent of `i`). -/
  chi_res : ∀ j : Fin p,
    (chi j : ClassFunction ↥PU ℂ) = ClassFunction.restrict PU (mu2 0 j : ClassFunction S ℂ)
  /-- **(4.5.a)** Induction formula: `Ind_{PU}^S (chi j) = ∑_i mu2 i j` (Coq
  `cfInd_prTIres`). -/
  ind_chi : ∀ j : Fin p,
    ClassFunction.induce PU (chi j : ClassFunction ↥PU ℂ)
      = ∑ i : Fin q, (mu2 i j : ClassFunction S ℂ)
  /-- **(4.5.a)** The `0`-residue is the trivial character (Coq `prTIres0`). -/
  chi_zero : (chi 0 : ClassFunction ↥PU ℂ) = trivialClassFunction ↥PU
  /-- The Sylow `p`-subgroup `P ≤ PU` (`= S_F` realised inside `PU`), carrying the kernel
  condition of the `(P)`-nonlinear induced family `seqIndD PU S P 1`.  In the Feit–Thompson
  application `P = S_F` is the Fitting subgroup of `S` (elementary abelian of order `p^q`),
  and the residues `chi_ j` (`j ≠ 0`) are exactly the `Irr(PU)`-characters non-trivial on `P`. -/
  P : Subgroup ↥PU
  /-- **(4.5.b), kernel condition** (Coq `cfker_prTIres`, `PFsection4.v:801`): for `j ≠ 0` the
  residue `chi_ j` does **not** have `P` in its kernel (it is `P`-nonlinear).  Equivalently
  `P ⊄ ker (chi_ j)`, so `μ_j = Ind_{PU}^S (chi_ j) ∈ seqIndD PU S P 1`.  A genuine mathcomp
  theorem (the `j = 0` residue is trivial with full kernel by `chi_zero`; every other residue
  is a non-principal constituent of `Res_P (mu2 0 j)`, hence non-trivial on `P`). -/
  cfker_prTIres : ∀ j : Fin p, j ≠ 0 →
    ¬ ((P : Set ↥PU) ⊆ OddOrder.Peterfalvi.S03.characterKernel (chi j : ClassFunction ↥PU ℂ))
  /-- **Peterfalvi (4.5.b), `prTIres_irr_cases`** (Coq `PFsection4.v:620`, a genuine mathcomp
  `Theorem`).  The constituent classification of a prime-TI residue: for every irreducible
  `θ ∈ Irr(PU)`, exactly one of

  * **(residue case)** `θ = chi_ j` for some `j`  (equivalently `Ind_{PU}^S θ = μ_j`); or
  * **(induced-irreducible case)** `Ind_{PU}^S θ ∈ Irr(S)` and `Ind θ ≠ mu2 i j` for all
    `i, j` (a fresh irreducible, not a prime-TI constituent).

  This is the dichotomy `S1cases` uses to split the induced constituents of a member of
  `calS1` into the reducible `μ_j` family and the `𝒮 ∩ Irr(S)` part.

  **Why a posited field, not a derived theorem.**  The mathcomp proof establishes the
  *inertia group* `'I_S[θ] = PU` for `θ ∉ {chi_ j}` (whence `Ind θ` is irreducible by
  `inertia_Ind_irr`, whose repo analogue `isIrreducibleCharacter_induce_of_inertia_eq` is
  available) via a **`p`-group fixed-point count**: on the `W1`-conjugation action on
  `Irr(PU)`, the `z`-fixed irreducibles (`z ∈ W1` a `p`-element) equal the `z`-fixed classes
  (`card_afix_irr_classes`, repo `card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm`),
  and `sylow.pgroup_fix_mod` (mathlib `IsPGroup.card_modEq_card_fixedPoints`) with the
  coprimality `p ∤ |PU|` pins the fixed set to the residue image `{chi_ j}` of size `p`.  This
  computation consumes the **cyclic-TI structure** — the group `W1`, the decomposition
  `S = PU ⋊ W1`, the `W1`-action on `Irr(PU)`, and `coprime |PU| |W1|` — none of which is data
  of this structure (it is deliberately abstracted away, being supplied by the eventual
  `cyclicTIiso`-based constructor together with `mu2`/`chi`).  So the classification is not
  determined by the other fields; like `mu2_orthonormal`, `chi_res`, `ind_chi`, `cfker_prTIres`
  (all mathcomp theorems of the same `cyclicTIiso` provenance), it is posited here and
  discharged by the constructor.  See the module docstring / `issues/9014-primeti-residue-api.md`
  continuation #1–#2. -/
  prTIres_irr_cases : ∀ θ : IrreducibleCharacter ↥PU,
    (∃ j : Fin p, (θ : ClassFunction ↥PU ℂ) = (chi j : ClassFunction ↥PU ℂ))
      ∨ (IsIrreducibleCharacter (ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ))
          ∧ ∀ (i : Fin q) (j : Fin p),
              ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ)
                ≠ (mu2 i j : ClassFunction S ℂ))

namespace PrimeTIResidueData

variable {S : Type*} [Group S] [Fintype S] [Invertible (Nat.card S : ℂ)]
variable {PU : Subgroup S} [Fintype ↥PU] [Invertible (Nat.card ↥PU : ℂ)]
variable {q p : ℕ} [NeZero q] [NeZero p]
variable (D : PrimeTIResidueData S PU q p)

/-! ### `primeTIred`: the reducible column-sum characters `μ_j`

`primeTIred D j := ∑_i mu2 i j` (Coq `primeTIred`).  Below: it is a genuine character
(`prTIred_char`), reducible with `⟨μ_j⟩ = q > 1` (`cfnorm_prTIred`, `prTIred_not_irr`),
nonzero (`prTIred_neq0`), and injective in `j` (`prTIred_inj`). -/

/-- **Peterfalvi (4.5.a), `primeTIred`.** The reducible residue character
`μ_j := ∑_i mu2_ i j ∈ ℂ CF(S)` (Coq `primeTIred ptiW j`). -/
noncomputable def primeTIred (j : Fin p) : ClassFunction S ℂ :=
  ∑ i : Fin q, (D.mu2 i j : ClassFunction S ℂ)

                                    
                                                                            

/-- **`cfInd_prTIres`** (Coq `PFsection4.v:594`): `Ind_{PU}^S (chi_ j) = μ_j`.  Immediate
from the `ind_chi` field and the definition of `primeTIred`. -/
theorem cfInd_prTIres (j : Fin p) :
    ClassFunction.induce PU (D.chi j : ClassFunction ↥PU ℂ) = D.primeTIred j :=
  D.ind_chi j

/-- Each `μ_j` is a **genuine character** (Coq `prTIred_char`): a finite sum of
irreducible characters. -/
theorem prTIred_char (j : Fin p) : IsCharacter (D.primeTIred j) := by
  refine IsCharacter.sum fun i _ => ?_
  exact (D.mu2 i j).isIrreducible.isCharacter

/-- **`cfdot_prTIirr_red`** (Coq `PFsection4.v:452`): `⟨mu2 i j, μ_k⟩ = [j = k]`.

Expanding `μ_k = ∑_{i'} mu2 i' k` and using orthonormality of the `mu2`, the sum over `i'`
collapses to the single term `i' = i` (present iff `j = k`). -/
theorem cfdot_prTIirr_red (i : Fin q) (j k : Fin p) :
    ClassFunction.inner (D.mu2 i j : ClassFunction S ℂ) (D.primeTIred k)
      = (if j = k then 1 else 0) := by
  classical
  rw [primeTIred, inner_sum_right]
  -- each summand is the orthonormality value `[i = i' ∧ j = k]`
  have hval : ∀ i' : Fin q,
      ClassFunction.inner (D.mu2 i j : ClassFunction S ℂ) (D.mu2 i' k : ClassFunction S ℂ)
        = (if i = i' ∧ j = k then 1 else 0) := fun i' => D.mu2_orthonormal i i' j k
  rw [Finset.sum_congr rfl fun i' _ => hval i']
  by_cases hjk : j = k
  · -- only the `i' = i` term survives
    rw [if_pos hjk]
    have hcond : ∀ i' : Fin q, (i = i' ∧ j = k) ↔ i = i' := fun i' => by
      simp [hjk]
    simp only [hcond]
    rw [Finset.sum_ite_eq Finset.univ i (fun _ => (1 : ℂ)), if_pos (Finset.mem_univ i)]
  · -- every term vanishes
    rw [if_neg hjk]
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [if_neg fun h => hjk h.2]

/-- **`cfdot_prTIred`** (Coq `PFsection4.v:459`): `⟨μ_{j₁}, μ_{j₂}⟩ = [j₁ = j₂] · q`. -/
theorem cfdot_prTIred (j₁ j₂ : Fin p) :
    ClassFunction.inner (D.primeTIred j₁) (D.primeTIred j₂)
      = (if j₁ = j₂ then (q : ℂ) else 0) := by
  classical
  -- expand the left column-sum, then use `cfdot_prTIirr_red` termwise
  rw [primeTIred, inner_sum_left]
  rw [Finset.sum_congr rfl fun i _ => D.cfdot_prTIirr_red i j₁ j₂]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  by_cases hjk : j₁ = j₂
  · rw [if_pos hjk, if_pos hjk, nsmul_eq_mul, mul_one]
  · rw [if_neg hjk, if_neg hjk, nsmul_eq_mul, mul_zero]

/-- **`cfnorm_prTIred`** (Coq `PFsection4.v:465`): `⟨μ_j⟩ = q = #|W1|`. -/
theorem cfnorm_prTIred (j : Fin p) :
    ClassFunction.inner (D.primeTIred j) (D.primeTIred j) = (q : ℂ) := by
  rw [cfdot_prTIred, if_pos rfl]

                                                                                           
                                                             
         
                                                                                   
                      
                 
                                                    
                                        

                                                                                  

                                                                                       
                                                                                          
                                                                                      
                                                  
                                                                     
                     
         
                                                     
                                            
       

                                                                          

                                                                                                           
                                                                       
                                                                          
                    
               
                                                                                 
                                  
                                      
                                 

                                                                                                 
                                                                                                   

                                                                                                
                                                                                                  
                                                                                              
                                          
                                                                           
                                                                                   
           
                                        
                     
                                                                      
                      

/-! ### The residue `chi_ 0` and `μ_0` -/

/-- **`prTIres0`** (Coq `PFsection4.v:608`): the `0`-residue is the trivial character. -/
theorem prTIres0 : (D.chi 0 : ClassFunction ↥PU ℂ) = trivialClassFunction ↥PU :=
  D.chi_zero

/-! ### The constituent classification `prTIres_irr_cases`

This is Peterfalvi (4.5.b) (Coq `PFsection4.v:620-665`), the single genuinely-deep sub-fact of
this port.  Its mathcomp proof is the inertia-group computation `'I_S[θ] = PU` (via `p`-group
fixed-point counting, `pgroup_fix_mod`, on the `W1`-action on `Irr(PU)`), which consumes the
cyclic-TI structure (`W1`, `S = PU ⋊ W1`, `coprime |PU| |W1|`) that is *not* data of
`PrimeTIResidueData` — it is supplied by the eventual `cyclicTIiso`-based constructor together
with `mu2`/`chi`.  Accordingly the classification is **posited as the field
`PrimeTIResidueData.prTIres_irr_cases`** (see its docstring for the full inertia/`pgroup_fix_mod`
provenance and why it is a field rather than a derivation), on the same honest footing as the
other `cyclicTIiso`-provenance fields `mu2_orthonormal`, `chi_res`, `ind_chi`, `cfker_prTIres`.
The constructor discharges all of them; this leaf is sorry-free.  `S1cases` below consumes the
field directly via `D.prTIres_irr_cases`. -/

/-! ### Membership of `μ_j` in `ℤ[Irr S]`

The `μ_j` are genuine characters (`prTIred_char`), hence virtual characters. -/

/-- Each `μ_j` is a **virtual character** (`μ_j ∈ ℤ[Irr S]`): it is a genuine character
(`prTIred_char`), and every genuine character lies in `ZIrr`. -/
theorem prTIred_mem_ZIrr (j : Fin p) : D.primeTIred j ∈ ZIrr S :=
  (D.prTIred_char j).mem_ZIrr

/-! ### The `(P)`-nonlinear induced family `calS = seqIndD PU S P 1`

`calS D := { Ind_{PU}^S ξ | ξ ∈ Irr(PU), P ⊄ ker ξ }` (Coq `seqIndD PU S P 1`, the reduced
family Peterfalvi's §13 coherence runs on).  This is the `PU`-level analogue of the S11 §9
family `sSet = Ind_{HU}^M 𝒳`; here the kernel condition is on the field `D.P ≤ PU`.  The
`μ_j` (`j ≠ 0`) are members (`FTseqInd_TIred`); more generally every `P`-nonlinear induction
`Ind_{PU}^S θ` lands in `calS D` and hence in `zSpan (calS D)` (`induce_mem_calS`,
`induce_mem_zSpan_calS`). -/

/-- **Peterfalvi §13 family `calS = seqIndD PU S P 1`** (Coq `PFsection13.v:157`): the set of
characters `Ind_{PU}^S ξ` induced from an irreducible `ξ ∈ Irr(PU)` whose kernel does **not**
contain `P` (the `(P)`-nonlinear residue family).  Mirrors the S11 `sSet` idiom. -/
noncomputable def calS : Set (ClassFunction S ℂ) :=
  { φ | ∃ ξ : IrreducibleCharacter ↥PU,
      ¬ ((D.P : Set ↥PU) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ξ : ClassFunction ↥PU ℂ))
        ∧ φ = ClassFunction.induce PU (ξ : ClassFunction ↥PU ℂ) }

                                             
                                                          
                                                                                                       
                                                                          
         

                                                                                                  
                                                                       
                                                         
                                    
                                                                                
                                                                        
                    

                                                                                                
                                                              

                                                                                      
                                                                                   
                                                                                   
                                                
                                

/-! ### The dichotomy `S1cases` and the membership `Ind θ ∈ zSpan calS`

`S1cases` (Coq `PFsection13.v:401-428`) classifies the induced character `Ind_{PU}^S θ` of an
irreducible `θ ∈ Irr(PU)` with `P ⊄ ker θ`, via `prTIres_irr_cases`, into two mutually
exclusive shapes — either `Ind θ = μ_j` for some `j ≠ 0`, or `Ind θ ∈ calS D ∩ Irr(S)` — both
of which lie in `calS D`.  This is the `PU`-level residue dichotomy on which Coq's
`sS1S : calS1 ⊆ ℤ[calS]` (and the S15 consumer `induce_H_mem_zSpan_S`) is built. -/

                                                                                                 
                                                                              

                                                                                         
                                                                                              
                                  

                                                                                                
                                                                                                   
                                                                                                 
                                                 
                                     
                                                                                
                               
                                                                                
                                                                                          
                                                                                      
                                                                
                                                                       
                                 
                                                                                                         
                
                    
                                                                                         
                                
                                        
                                      
                                                                                            
                                                      

                                                                                                 
                                                                                                

                                                                                         
                                                                                  
                                                                                             
                                              
                                                               
                                     
                                                                                
                                                                                 
                                 
                                                                
                                        
               

/-! ### The `H`-level lift `induce_H_mem_zSpan_calS`

Coq's `S1cases` is stated for a *smaller* group `H ≤ PU` than the induction target `PU`: it
classifies `Ind_H^S θ` (for irreducible `θ ∈ Irr(H)` with `P ⊄ ker θ`) into `zSpan (calS)`.  The
`PU`-level engine `induce_mem_zSpan_calS` above is the case `H = PU`; the general `H ≤ PU` case is
obtained by *induction in stages* and *constituent expansion* (Coq's `cfun_sum_constt` → `rpred_sum`
flow):

* `Ind_H^S θ = Ind_{PU}^S (Ind_H^{PU} θ)` — the two-stage induction (definitionally, via the
  `↥PU`-ambient `ClassFunction.induce`);
* `Ind_H^{PU} θ = ∑_{s ∈ Irr(PU)} ⟨θ, Res_H s⟩ • s` — the constituent (Fourier + Frobenius)
  decomposition `induce_eq_sum_inner_restrict_smul`, with non-negative integer coefficients;
* each constituent `s` with `⟨θ, Res_H s⟩ ≠ 0` has `P ⊄ ker s` (`constituent_P_not_subset_ker`,
  the kernel step: `θ` is a constituent of `Res_H s`, so `P ⊆ ker s ⟹ P ⊆ ker θ`, contradiction),
  hence `Ind_{PU}^S s ∈ zSpan (calS)` by the engine;
* `zSpan (calS)` is `ℤ`-closed, so the coefficient-weighted sum lands in it.

Here `H : Subgroup ↥PU` is an intermediate subgroup with `P ≤ H`, and `Ind_H^S θ` is written as the
honest two-stage induction `Ind_{PU}^S (Ind_H^{PU} θ)`.  Bridging this to the single-stage
`Ind_{(H.map PU.subtype)}^S` (as the S15 consumer `induce_H_mem_zSpan_S` phrases it) is
`induce_induce_subgroupOf` (`InducedTransport.lean`), applied on the S15 side. -/

                                                                                                  
                                                                                                        
                                                                                                             
                                                                                                   
                                       

                                                                                    
                                                                                               
                                                                    
                                                                                                  
                                                                                                  
                                                    
                                    
                                                                          
                                                                      
                                                 
                                                  
                                    
                                
                                                                         
                             
                                                                                  
                                             
            
                                                                                                       
                                                                                         
                                                                              
                                    
                                                                             
                        
                                                                                     
                                                                
                                                  
                                             
                                                                   
                                                                      
                                                                                                      
                        
                                                                                  
                                          

                                              
                                                                                                     
                                                                                                         
                                                                                                   
                                                                   

                                                                   

                                                                                             
                                                                               
                                                                                
                                                                                    
                                                                                           
                                                                      
                                                                                                 
                                                                                               
                     

                                                                              
                                                                                       
                                                 
                               
                                                                          
                                                                      
                                                 
                                                    
                                                                              
           
                                             
                                                                    
                                                                                                          
                                                                     
                                          
                                
                                                                               
                                                                                         
                                                                              
                                                                        
                                                                                           
                       
                                                                    
                                                                                               
                                                                                                             
                                            
               
                          
                                       
                                                                                                

end PrimeTIResidueData

end OddOrder.RepresentationTheory

/-! ## The `prTIres_irr_cases` dichotomy, assembled over the S06 certain-type `Hypothesis`

The genuinely-deep constituent classification `prTIres_irr_cases` (Peterfalvi (4.5.b)) — the crux the
`PrimeTIResidueData` structure posits — is **already proven** as the inertia computation in
`S06_CertainTypeClifford`: a `χ ∈ Irr(K)` not among the residues `χ_j` has full inertia `I_L(χ) = K`
(`inertia_eq_K_of_forall_chiRestrict_ne`, the `p`-group fixed-point count via
`card_fixedPoints_conjByPermIrr…` + `IsPGroup.card_modEq_card_fixedPoints`), whence `Ind χ` is a fresh
irreducible (`induce_isIrreducible_of_forall_chiRestrict_ne`) distinct from every `μ_{ij}`
(`induce_ne_certainType_of_forall_chiRestrict_ne`).  Assembling the residue case (by definition) with
that induced-irreducible case gives exactly the dichotomy `PrimeTIResidueData.prTIres_irr_cases`
posits.  So the constructor of `PrimeTIResidueData` is a **bridge from an `S06.Hypothesis`**, not a
from-scratch `cyclicTIiso` port (issue 9014): the single genuinely-deep field is discharged by
`prTIres_irr_dichotomy` below. -/

namespace OddOrder.Peterfalvi.S06.Hypothesis

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L] (h : Hypothesis L)
  [Invertible (Nat.card L : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)]
  [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] [Invertible (Nat.card ↥h.K : ℂ)]
  [NeZero (Nat.card h.W1)] [NeZero (Nat.card h.W2)]

/-- **Peterfalvi (4.5.b) `prTIres_irr_cases`, assembled.**  Every `χ ∈ Irr(K)` is either a residue
`χ_j` (`= chiRestrict χ₂` for some `W₂`-column `χ₂`) or induces to a *fresh* irreducible of `L`
distinct from every certain-type character `μ_{ij}`.  The residue case is by definition; the
induced-irreducible case is the S06 inertia computation (`induce_isIrreducible_of_forall_chiRestrict_ne`
+ `induce_ne_certainType_of_forall_chiRestrict_ne`).  This is the deep field of a `PrimeTIResidueData`
constructor built from an `S06.Hypothesis` (issue 9014). -/
theorem prTIres_irr_dichotomy (χ : IrreducibleCharacter ↥h.K) :
    (∃ χ₂, h.chiRestrict χ₂ = χ) ∨
      (IsIrreducibleCharacter (ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ)) ∧
        ∀ (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)),
          ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ)
            ≠ ((h.columnFamily χ₂).mu i : ClassFunction L ℂ)) := by
  by_cases hcase : ∃ χ₂, h.chiRestrict χ₂ = χ
  · exact Or.inl hcase
  · push Not at hcase
    exact Or.inr ⟨h.induce_isIrreducible_of_forall_chiRestrict_ne hcase,
      fun χ₂ i => h.induce_ne_certainType_of_forall_chiRestrict_ne hcase χ₂ i⟩

/-! ### The `PrimeTIResidueData` constructor from an `S06.Hypothesis`

The residue grid `S = L`, `PU = K`, `q = |W₁|`, `p = |W₂|`.  The S06 grid is indexed by
`W₂`-columns `χ₂ ∈ Ŵ₂` (`h.columnFamily`/`h.chiRestrict`), of which there are exactly `|W₂| = p`
(`card_charGroup_W2`).  The bridge to the `Fin p` residue index is the equiv
`charGroupW2Equiv` below, normalized so the trivial column `1 : Ŵ₂` maps to index `0`
(so that `chi 0 = chiRestrict 1 = 1_K`, matching the `chi_zero` field). -/

/-- **Index bridge `Fin p ≃ Ŵ₂`** for the `PrimeTIResidueData` constructor.  From
`card_charGroup_W2 : |Ŵ₂| = |W₂| = p` we get an equiv `Fin p ≃ Ŵ₂`, then compose with a
transposition so that the trivial column `1 : Ŵ₂` sits at index `0` (`charGroupW2Equiv_zero`). -/
noncomputable def charGroupW2Equiv :
    Fin (Nat.card h.W2) ≃ ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
  haveI : Fintype ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Fintype.ofFinite _
  letI e0 : Fin (Nat.card h.W2) ≃ ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
    (Fintype.equivFinOfCardEq
      (by rw [← Nat.card_eq_fintype_card, h.card_charGroup_W2])).symm
  (Equiv.swap 0 (e0.symm 1)).trans e0

@[simp] theorem charGroupW2Equiv_zero :
    h.charGroupW2Equiv 0 = 1 := by
  classical
  simp only [charGroupW2Equiv, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

/-- **`PrimeTIResidueData` from the certain-type `S06.Hypothesis`** (the bridge of issue 9014,
discharging the deep field `prTIres_irr_cases` via `prTIres_irr_dichotomy`).  Given a subgroup
`H : Subgroup ↥h.K` with `W₂ ≤ H` (the (4.6.c) covering condition on the kernel family `P := H`),
assembles the residue grid `S = L`, `PU = K`, `q = |W₁|`, `p = |W₂|` from the S06 column machinery:
`mu2 i j := (columnFamily (e j)).mu i`, `chi j := chiRestrict (e j)` (`e = charGroupW2Equiv`).
Every field is a genuine S06 theorem — orthonormality (`columnFamily_mu_ne` + `injective`),
restriction (`coe_chiRestrict`), induction (`induce_restrict_certainType_eq`), the trivial residue
(`chiRestrict_one_eq_trivial` via `charGroupW2Equiv_zero`), the `(4.7)` kernel non-containment
(`not_subset_characterKernel_chiRestrict_of_ne_one`), and the `(4.5.b)` dichotomy
(`prTIres_irr_dichotomy`). -/
noncomputable def _root_.OddOrder.RepresentationTheory.PrimeTIResidueData.ofS06Hypothesis
    [Fintype ↥h.K] (H : Subgroup ↥h.K) (hW2H : h.W2.subgroupOf h.K ≤ H) :
    PrimeTIResidueData L h.K (Nat.card h.W1) (Nat.card h.W2) :=
  { mu2 := fun i j => (h.columnFamily (h.charGroupW2Equiv j)).mu i
    chi := fun j => h.chiRestrict (h.charGroupW2Equiv j)
    mu2_orthonormal := fun i i' j j' => by
      classical
      rw [irreducibleCharacter_inner_eq_ite]
      by_cases hjj' : j = j'
      · subst hjj'
        by_cases hii' : i = i'
        · subst hii'; simp
        · rw [if_neg (fun hc => hii' ((h.columnFamily (h.charGroupW2Equiv j)).injective hc)),
            if_neg (by simp [hii'])]
      · rw [if_neg (h.columnFamily_mu_ne (fun hc => hjj' (h.charGroupW2Equiv.injective hc)) i i'),
          if_neg (by simp [hjj'])]
    chi_res := fun j => h.coe_chiRestrict (h.charGroupW2Equiv j)
    ind_chi := fun j => by
      rw [h.coe_chiRestrict (h.charGroupW2Equiv j),
        h.induce_restrict_certainType_eq (h.charGroupW2Equiv j)]
    chi_zero := by
      rw [charGroupW2Equiv_zero, h.chiRestrict_one_eq_trivial,
        IrreducibleCharacter.coe_trivialIrreducibleCharacter]
    P := H
    cfker_prTIres := fun j hj => by
      have hne1 : h.charGroupW2Equiv j ≠ 1 := by
        rw [← charGroupW2Equiv_zero (h := h)]
        exact fun hc => hj (h.charGroupW2Equiv.injective hc)
      intro hHker
      exact h.not_subset_characterKernel_chiRestrict_of_ne_one hne1
        (Set.Subset.trans (SetLike.coe_subset_coe.mpr hW2H) hHker)
    prTIres_irr_cases := fun θ => by
      rcases h.prTIres_irr_dichotomy θ with ⟨χ₂, hχ₂⟩ | ⟨hirr, hne⟩
      · refine Or.inl ⟨h.charGroupW2Equiv.symm χ₂, ?_⟩
        rw [Equiv.apply_symm_apply, hχ₂]
      · exact Or.inr ⟨hirr, fun i j => hne (h.charGroupW2Equiv j) i⟩ }

                                                                                        
                                                                                      
                                                                                              
                                                                     
                                                                
                                                                                       
                                                                          
                                           

                                                                                  
                                                                                                        
                                  
                                                                                                  
                                                                             
                                                       
                                                      
                                                                                   
                                                            
                                                 
                                                          
                                                             
                                                             

end OddOrder.Peterfalvi.S06.Hypothesis

/-! ## Relocated from `S05_SigmaIsometry` (hub ruling 9014/fcfc0644): the `μ` extraction grid

The signed-irreducible extraction `ω^σ = ±μ` (`mu2Grid`) is the σ-grounding down-payment on the
prime-TI constructor (`cyclicTIiso` port), so it belongs with the prime-TI residue foundation
here rather than in lane-a's `S05_SigmaIsometry`.  Namespace and API are unchanged
(`TICyclicHypothesis.mu2Grid` etc.); only the file location moved. -/

namespace OddOrder.Peterfalvi.S05.TICyclicHypothesis

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

/-! ### The signed-irreducible extraction of (3.2): `ω^σ = ±μ` (the `dirr` step)

Peterfalvi §4 / Feit–Thompson §13 (Coq `primeTIirr_spec`, `PFsection4.v:288-387`, via
`dirr_dIirr`) refine the isometry (3.2) by showing that each basis image `ω^σ` is not merely a
virtual character but a **single signed irreducible** `δ · μ` (`δ = ±1`, `μ ∈ Irr(G)`), so that the
`μ` form an orthonormal system indexed by `Irr(W)` — the prime-TI irreducibles `mu2_ i j`.

This is exactly the norm-`1` classifier applied to `ω^σ`: `ω^σ ∈ ZIrr G` (`sigma_mem_ZIrr`) and
`‖ω^σ‖² = ‖ω‖² = 1` (isometry, `sigma_inner_irreducibleCharacter`), so by
`exists_zsmul_irreducibleCharacter_of_inner_self_one` (Peterfalvi (5.9.a)) it is `δ · μ`.  The
grid `mu2Grid`/`mu2GridSign` packages the extracted `μ`/`δ`, and `mu2Grid_orthonormal`
(= Coq `cfdot_prTIirr`) reads the orthonormality of the `μ` straight off the isometry.

These are reusable `σ`-side building blocks for the Peterfalvi §4 `dirr` extraction (the signed
irreducibles `μ` of the prime-TI grid, read off the (3.2) isometry).  Standalone, `sorry`-free;
currently unconsumed (the §4 prime-TI residue grid itself is carried by `S06`'s `certainType`/
`columnFamily` machinery, so these are kept only as a self-contained `σ`→signed-irreducible API). -/

/-- **Peterfalvi §4 `dirr` step** (existence form).  Each basis image `ω^σ` of the (3.2) isometry
is a single signed irreducible: there are a sign `δ = ±1` and an irreducible `μ ∈ Irr(G)` with
`ω^σ = δ • μ`.  (Coq `primeTIirr_spec` via `dirr_dIirr`: a norm-`1` element of `ℤ[Irr G]` lies in
`± Irr(G)`.) -/
theorem exists_sign_smul_irr_of_sigma_omega (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) :
    ∃ (δ : ℤ) (μ : IrreducibleCharacter G), (δ = 1 ∨ δ = -1) ∧
      hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) = δ • (μ : ClassFunction G ℂ) := by
  have hσZ : hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ) ∈ ZIrr G :=
    hyp.sigma_mem_ZIrr hVeq app (IsIrreducibleCharacter.mem_ZIrr ω.2)
  have hσ1 : ClassFunction.inner (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ))
      (hyp.sigma hVeq app (ω : ClassFunction hyp.W ℂ)) = 1 := by
    rw [hyp.sigma_inner_irreducibleCharacter hVeq app, irreducibleCharacter_inner_eq_ite,
      if_pos rfl]
  exact exists_zsmul_irreducibleCharacter_of_inner_self_one hσZ hσ1

/-- **Peterfalvi §4 `dirr` step, grid form**: the extracted prime-TI irreducible `μ = mu2Grid ω`
(Coq `primeTIirr`), a choice of the single irreducible `μ` with `ω^σ = ±μ`
(`exists_sign_smul_irr_of_sigma_omega`). -/
noncomputable def mu2Grid (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) : IrreducibleCharacter G :=
  (hyp.exists_sign_smul_irr_of_sigma_omega hVeq app ω).choose_spec.choose

/-- The extracted sign `δ = mu2GridSign ω ∈ {±1}` of the `dirr` step. -/
noncomputable def mu2GridSign (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)
    (ω : IrreducibleCharacter hyp.W) : ℤ :=
  (hyp.exists_sign_smul_irr_of_sigma_omega hVeq app ω).choose

                                                                   
                                                                       
                                                                       
                                       
                                                                           
                                                                                 

                                                                                                      
                                                                                            
                                                                       
                                                                       
                                       
                                                     
                                                                                          
                                                                                 

                                                                                                               
                                                                                     
                                                                       
                                                                       
                                       
                                                   
                                                                                               
                                                                         
                                                                      

                        
                                                                                             
                                                            
                                                                                                   
                                                                                                    
                                                        
                                                                        
                                                                       
                                                                       
                                           
                                                                       
                                                        
                                       
                            
                 
                                                                  
                                                          
                                                                               
                  
             
                                                                                                      
                                                                                         
                                                                      
                                                                                           
                      
                                                                
                                                                    
                                                                     
                                                                                    
                                                                                     
                                                                                 
                                                            
                                                                 
                                                     

                                                                                              
                                                                
                                                                      
                                                                       
                                                                         
                                                   
                  
               
                                                   
                                                                          
                     

end OddOrder.Peterfalvi.S05.TICyclicHypothesis
