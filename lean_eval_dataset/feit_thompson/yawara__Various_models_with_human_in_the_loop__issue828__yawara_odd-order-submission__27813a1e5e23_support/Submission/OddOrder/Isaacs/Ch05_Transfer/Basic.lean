/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Focal
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Main
import Submission.OddOrder.Isaacs.Ch04_Commutators.Main

/-!
# Basic

Prefix-split from `OddOrder.Isaacs.Ch05_Transfer.Main` (2000-line limit, issue 0103 第 2 パス).
-/

open scoped commutatorElement
open scoped IsMulCommutative -- rc2: IsMulCommutative→CommGroup/Monoid now scoped

/-!
# OddOrder.Isaacs.Ch05 — Transfer

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 5
"Transfer" (pp. 147-180) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 5A | Transfer 定義・welldefinedness・準同型性 | 5.1 – 5.4 | mathlib + ✅ Thm 5.3 + Cor 5.4 |
| 5B | 中心への transfer = n 乗, Schur, Dietzmann | 5.5 – 5.10 | ✅ 5.8 + 5.9, mathlib + 5.10 保留 |
| 5C | Hall transfer, Burnside, cyclic / abelian Sylow | 5.11 – 5.19 | ✅ Lem 5.11 + Lem 5.12 + Thm 5.17 + Thm 5.18 (強形+弱形) + Cor 5.19 (cyclic Sylow_2 版) |
| 5D | Focal subgroup theorem + p-transfer control | 5.20 – 5.24 | ✅ 5.20-5.23; 5.24 保留 |
| 5E | Frobenius normal p-complement + 系 | 5.25 – 5.30 | ✅ 5.25-5.30 |

## 方針

mathlib カバレッジは Ch.5 中で最も厚い (`Mathlib/GroupTheory/Transfer.lean` 350 行 +
`Focal.lean` 218 行 + `Schreier.lean` + `SpecificGroups/ZGroup.lean`).
**no-wrapper policy** に従い, mathlib 直接対応の Isaacs 番号は section docstring の
対応表に記録するのみ. Isaacs 流のステートメント (引数特殊化や Isaacs 流の `H/H'` 標的)
が必要な場合のみ別途定理化する.

## Mathlib direct correspondence (no wrapper)

mathlib 既収載で本ファイルでは wrapper を書かないもの:

* `MonoidHom.transfer` (`Transfer.lean:148`) = **Thm 5.1, 5.2** (transfer welldef + 準同型).
* `MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot` (`Transfer.lean:161`) = **Thm 5.5**
  (transfer-evaluation lemma; orbital 分解).
* `MonoidHom.transfer_center_eq_pow`, `transferCenterPow` (`Transfer.lean:222, 229`)
  = **Thm 5.6** (中心 transfer = `g ↦ g^|G:Z|`).
* `Subgroup.card_commutator_le_of_finite_commutatorSet` (`Schreier.lean:208`) =
  **Thm 5.7** (Schur, bound 付き強化版).
* `MonoidHom.ker_transferSylow_isComplement'` (`Transfer.lean:275`) = **Thm 5.13 Burnside**.
* `IsCyclic.isComplement'` (`Transfer.lean:339`) = **Cor 5.14** (cyclic Sylow + smallest prime).
* `IsZGroup.isCyclic_commutator` (`ZGroup.lean:144`) = **Thm 5.16 part 1** (G' cyclic).
* `IsZGroup.isCyclic_abelianization` (`ZGroup.lean:134`) = **Thm 5.16 part 2** (G/G' cyclic).
* `IsZGroup.coprime_commutator_index` (`ZGroup.lean:280`) = **Thm 5.16 part 3** (|G'|, |G:G'| coprime).
* `isZGroup_iff_exists_mulEquiv` (`ZGroup.lean:315`) = **Thm 5.16 part 4** (semidirect product 形).
* `IsZGroup → IsSolvable` instance (`ZGroup.lean:102`) = **Cor 5.15** (Z-group solvable).
* `Subgroup.focalSubgroup`, `focalSubgroupOf`, `transferFocal` (`Focal.lean:58, 67, 151`) =
  Focal subgroup の定義 (Isaacs §5D 冒頭).
* `Subgroup.ker_restrict_transferFocal_eq_focalSubgroupOf` (`Focal.lean:191`) = **Thm 5.20**
  に相当 (ker(v) restrict 表示).
* `Subgroup.commutator_inf_eq_focalSubgroup` (`Focal.lean:208`) = **Thm 5.21 Focal Subgroup
  Theorem (D. G. Higman)** ⭐ **FT クリティカル**. BG が独自 Thm 1.17 として再述.
* `Subgroup.transferFocal_surjective` (`Focal.lean:180`) = transfer 全射性 (5.21 系).

## 下流被引用 (FT 経路)

**最重要**: **Focal Subgroup Theorem (5.21)** — BG が独自 Thm 1.17 として再述, 本文 3 箇所
(L2723, L5042, L5068) で使用. **Burnside (5.13)** = BG Thm 1.18 として再述.

Peterfalvi 本体 §4-§16 では transfer / focal を使わず. Suzuki 定理付録 (05.4) のみで
transfer-evaluation を直接利用 (1 件).

ノート: [`notes/isaacs/ch05_transfer.md`](../../notes/isaacs/ch05_transfer.md)
-/

namespace OddOrder.Isaacs.Ch05

open Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 5A: Transfer definition + homomorphism (pp. 147-153) -/

/-! ### Isaacs §5A (Transfer 定義)

- **Thm 5.1** (transfer welldef): mathlib `MonoidHom.transfer` 構成時点で transversal
  非依存性が組み込み済. wrapper 不要.
- **Thm 5.2** (transfer 準同型性): 同上, 構造の `map_mul'` フィールドで内包.
- **Thm 5.3** (`p ∣ |G' ∩ Z(G)|` ⇒ Sylow_p(G) は非可換): ✅
  `not_isMulCommutative_sylow_of_dvd_card_commutator_inf_center`.
- **Thm 5.4** (Schur multiplier corollary): ✅ 弱形
  `not_isMulCommutative_sylow_of_le_commutator_inf_center` — `Z ≤ Γ' ∩ Z(Γ)`, `p ∣ |Z|`
  ⇒ Sylow_p(Γ) 非可換. Schur multiplier 概念 (M(G), 中心 extension の universal) 自体は
  mathlib 未収載で full 形 (Sylow_p(Γ/Z) noncyclic) は別途. -/

                                                                                         

                                                                                      
                                                                                               
                                                                                                   
                                                                                 
                                                                         
                                                                                    
                                     
                                                                    
                                                                       
                                                                              
                                              
            
                                             
                             
                                                                                     
                                                             
                                                                  
                                          
                                          
                              
                                                  
                                 
                                                         
                      
                                                         
                                   
                                                       
                                             
                     
                                                                               
                                    
                                                                
                                              
                                                            
                                                         
                                                           
                                                        
                                                                         
                                    
                                                          
                                                        
                                                   
                                                                 
                                                                                
                                          
                                            
                                                                                       
                                                                                           
                                    
                                                             
                                                                        
                                         
                                                      
                                                                                                 
                                                          
                  
                                                         
                                  
                                                             
                                                     
                                        
                                                       
                                                            
                                  
                                                                            
                                                                    
                                                                          
                                                              
                                                                        
                                                                            
                                                             
       
                                                             
                                      
                                            
                                                        
                   
                                                   
                                                
                        
                                             
                                                                       
                                                              
                                                                    
                   
                       
            
                                                   
                                                 
                     
                               

                                                                                             
                                         

                                                                                         

                                                                                                                  
                                                                                            
                                                                                                       
                                                                                                                
                                                              
                                                        
                                                   
                                                                  
                                           
                                                                
                                                

end -- 5A

section /- 5B: Central transfer, Schur, Dietzmann (pp. 153-159) -/

/-! ### Isaacs §5B (中心 transfer, Schur, Dietzmann)

- **Thm 5.6** (中心 transfer = `g ↦ g^n`): mathlib `MonoidHom.transferCenterPow` 直接.
- **Lemma 5.8, Cor 5.9** (`Z(G)` transversal commutator 構造 + `|G:Z|`-乗 = 1):
  ✅ quotient `out` 代表元版 + transfer-kernel 版.
- **Thm 5.7 Schur** (`|G:Z(G)| < ∞ ⇒ G' 有限`): mathlib
  `Subgroup.card_commutator_le_of_finite_commutatorSet` 直接 (bound 付き強化版).
- **Thm 5.10 Dietzmann** (`X ⊆ G` 有限・共役閉・∃n, x^n=1 ⇒ `⟨X⟩` 有限):
  mathlib 未収載. Schur 5.7 の証明では mathlib `closureCommutatorRepresentatives` 経路
  で代替されているため独立 Dietzmann の必要なし. 形式化保留. -/

                                                                                                 
                                                                                    
                                     
                                                                      
                                              

                                                                                                  
                                                                                     
                                     
                                                                                     
                                              

                                                                                     
                                                         

                                                                                                
                                                                                    
                                                           
                
                                                       
                                                              
                                                                             
                                                                             
            
                                                    
                                                     
             
            
                                                    
                                                     
             
                                                                                   
                                                                                   
      
                                                   
                                                                
                                               
                                                                      
                                                         
                                                                 

                                                                                       
                      
                                                  
                                                                               
           
                                                          
                                                                                  
                          
                                                      
              
                                                             
                                                      
                                                 
                                                           
                                                        

                                                                                   
                                               
                                                                            
                                                                                         
                

                                                                                         
                                       
                                                 
                                                                                  
                                           
                                                                                   
                                                                                    
                                

                                                                        
                                      
                                                 
                                                          
                                                    
                                                 
                            
                                                                                    

end -- 5B

/-- "G has a normal p-complement" — there exists a normal subgroup `N : Subgroup G` such
that for every Sylow `p`-subgroup `P`, `(N, P)` form a complement pair (`IsComplement'`).

For finite `G`, this is equivalent to existence of normal `N` with `|N|` coprime to `p`
and `|G:N|` a `p`-power. mathlib 未収載のため新規定義. -/
def HasNormalPComplement (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ N : Subgroup G, N.Normal ∧
    ∀ P : Sylow p G, Subgroup.IsComplement' N (P : Subgroup G)

section /- 5C: Hall transfer, Burnside, cyclic / abelian Sylow (pp. 159-167) -/

/-! ### Isaacs §5C (Hall transfer + Burnside)

- **Lemma 5.11** (Hall index transfer): `ker_transfer_sup_eq_top_of_hall` ✅.
- **Lemma 5.12** (`N_G(P)` controls `C_G(P)` fusion): `normalizer_controls_centralizer_fusion` ✅.
- **Thm 5.13 Burnside**: `hasNormalPComplement_of_sylow_normalizer_le_centralizer` ✅.
- **Cor 5.14**: `IsCyclic.isComplement'` 直接.
- **Cor 5.15** (Z-group solvable): mathlib `IsZGroup` instance 直接.
- **Thm 5.16** (Z-group 構造): mathlib `IsZGroup` API 直接.
- **Thm 5.17** (cyclic Sylow_p ⇒ p∤|G'| or p∤|G:G'|): ✅ `isaacs_thm_5_17`
  (Ch.4 §4D Thm 4.28 + 4.34 Fitting + cyclic-chain helper).
- **Cor 5.19** (Sylow_2 cyclic direct factor ⇒ 非単純): 形式化保留. -/

/-! ### Ch.4 §4D adapter

Thm 5.17 は Ch.4 §4D **Thm 4.28 + 4.34 Fitting** に依存する. Ch.4 の
`fixedPointsOfMulAut` / `actionCommutator` 形式を、Ch.5 の subgroup conjugation 形式へ
ここで変換する. -/

/-- **Isaacs Thm 4.34 (Fitting)** — Ch.5 subgroup-conjugation adapter.

`A` (= subgroup `K` of `G` with `K ≤ N_G(P)`) が abelian subgroup `P` に conjugation 経由で
作用. `(|P|, |K|) = 1` (coprime) ⇒ `P = C_P(K) × ⁅P, K⁆` (internal direct product, element form).

**証明戦略** (Isaacs p.142, θ trick):
* θ : ↥P → ↥P, θ(p) = ∏_{k ∈ K} k • p. P abelian なので well-def + homomorphism.
* θ(p) ∈ C_P(K) (θ は K 作用と可換).
* `p ∈ C_P(K)` で θ(p) = p^|K|; (|P|, |K|) = 1 ⇒ θ(p) = 1 ⇒ p = 1.
* ⁅P, K⁆ ⊆ ker θ (各 [p, k] が ker に入る).
* ⇒ C_P(K) ⊓ ⁅P, K⁆ = ⊥.
* p^|K| = θ(p) · h with h ∈ ⁅P, K⁆ (元素計算). Bezout で p ∈ C_P(K) · ⁅P, K⁆.

This is the form needed by Isaacs Thm 5.17: a subgroup `K ≤ N_G(P)` acts on the
abelian subgroup `P` by conjugation. Ch.4 gives the same result for an abstract
automorphism action on the group `↥P`; this theorem translates fixed points to
`C_G(K) ∩ P` and action-commutators to `⁅P, K⁆`. -/
theorem fitting_coprime_abelian_decomp
    {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} [IsMulCommutative ↥P]
    {K : Subgroup G} (hK_norm : K ≤ Subgroup.normalizer P)
    (h_coprime : Nat.Coprime (Nat.card ↥P) (Nat.card ↥K)) :
    (Subgroup.centralizer (K : Set G) ⊓ P) ⊓ (⁅P, K⁆ : Subgroup G) = ⊥ ∧
      (Subgroup.centralizer (K : Set G) ⊓ P) ⊔ (⁅P, K⁆ : Subgroup G) = P := by
  classical
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  let KN : Subgroup N := K.subgroupOf N
  let φ : KN →* MulAut P := MulDistribMulAction.toMulAut KN P
  have hKN_card : Nat.card KN = Nat.card K :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := K) (K := N)
        (by simpa [N] using hK_norm)).toEquiv
  have hCop : Nat.Coprime (Nat.card KN) (Nat.card P) := by
    rw [hKN_card]
    exact h_coprime.symm
  have hSolv : IsSolvable KN ∨ IsSolvable P := by
    right
    infer_instance
  have h_inf_P :
      Subgroup.fixedPointsOfMulAut φ ⊓
        _root_.OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
    _root_.OddOrder.Isaacs.Ch04.fixedPoints_inf_actionCommutator_eq_bot_of_abelian
      φ hCop
  have h_sup_P :
      Subgroup.fixedPointsOfMulAut φ ⊔
        _root_.OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤ :=
    _root_.OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
      (φ := φ) hCop hSolv
  have h_fixed_map_le : (Subgroup.fixedPointsOfMulAut φ).map P.subtype ≤
      Subgroup.centralizer (K : Set G) ⊓ P := by
    intro x hx
    rw [Subgroup.mem_inf]
    rcases hx with ⟨xp, hxp_fixed, rfl⟩
    constructor
    · rw [Subgroup.mem_centralizer_iff]
      intro y hyK
      let yN : N := ⟨y, by simpa [N] using hK_norm hyK⟩
      let yKN : KN := ⟨yN, by rw [Subgroup.mem_subgroupOf]; exact hyK⟩
      have hfix : (φ yKN) xp = xp := hxp_fixed yKN
      have hconj : y * (xp : G) * y⁻¹ = (xp : G) := by
        exact congrArg Subtype.val hfix
      calc y * (xp : G) = (y * (xp : G) * y⁻¹) * y := by group
        _ = (xp : G) * y := by rw [hconj]
    · exact xp.property
  have h_ac_map_le :
      (_root_.OddOrder.Isaacs.Ch04.actionCommutator φ).map P.subtype ≤
        (⁅P, K⁆ : Subgroup G) := by
    rw [Subgroup.map_le_iff_le_comap,
      _root_.OddOrder.Isaacs.Ch04.actionCommutator_le_iff]
    intro a x
    rw [Subgroup.mem_comap]
    change ((a : N).val * (x : G) * (a : N).val⁻¹) * (x : G)⁻¹ ∈
      (⁅P, K⁆ : Subgroup G)
    have haK : ((a : N).val : G) ∈ K := by
      have ha := a.property
      rwa [Subgroup.mem_subgroupOf] at ha
    have hxP : (x : G) ∈ P := x.property
    have hcomm : (⁅(x : G), ((a : N).val : G)⁆ : G) ∈ (⁅P, K⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator hxP haK
    convert (Subgroup.inv_mem _ hcomm) using 1
    group
  have h_comm_le_ac_map :
      (⁅P, K⁆ : Subgroup G) ≤
        (_root_.OddOrder.Isaacs.Ch04.actionCommutator φ).map P.subtype := by
    rw [Subgroup.commutator_le]
    intro x hxP y hyK
    let yN : N := ⟨y, by simpa [N] using hK_norm hyK⟩
    let yKN : KN := ⟨yN, by rw [Subgroup.mem_subgroupOf]; exact hyK⟩
    let xP : P := ⟨x, hxP⟩
    have hgen : xP * (φ yKN) xP⁻¹ ∈
        _root_.OddOrder.Isaacs.Ch04.actionCommutator φ :=
      Subgroup.subset_closure ⟨xP, yKN, rfl⟩
    refine ⟨xP * (φ yKN) xP⁻¹, hgen, ?_⟩
    dsimp [φ, xP, yKN, yN]
    change x * (y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹
    group
  have h_inf_bot :
      (Subgroup.centralizer (K : Set G) ⊓ P) ⊓ (⁅P, K⁆ : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases Subgroup.mem_inf.mp hx with ⟨hx_centP, hx_comm⟩
    rcases Subgroup.mem_inf.mp hx_centP with ⟨hx_cent, hxP⟩
    let xP : P := ⟨x, hxP⟩
    have hx_fixed : xP ∈ Subgroup.fixedPointsOfMulAut φ := by
      intro a
      apply Subtype.ext
      rcases a with ⟨⟨y, _hyN⟩, hyK⟩
      have hcomm : y * x = x * y := by
        rw [Subgroup.mem_centralizer_iff] at hx_cent
        exact hx_cent y hyK
      change y * x * y⁻¹ = x
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hx_ac : xP ∈ _root_.OddOrder.Isaacs.Ch04.actionCommutator φ := by
      have hx_map :
          x ∈ (_root_.OddOrder.Isaacs.Ch04.actionCommutator φ).map P.subtype :=
        h_comm_le_ac_map hx_comm
      rcases hx_map with ⟨z, hz_ac, hz_val⟩
      have hz_eq : z = xP := Subtype.ext hz_val
      rwa [hz_eq] at hz_ac
    have hxP_bot : xP ∈ (⊥ : Subgroup P) := by
      rw [← h_inf_P]
      exact ⟨hx_fixed, hx_ac⟩
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxP_bot)
  have h_sup_eq :
      (Subgroup.centralizer (K : Set G) ⊓ P) ⊔ (⁅P, K⁆ : Subgroup G) = P := by
    apply le_antisymm
    · exact sup_le inf_le_right (by
        rw [Subgroup.commutator_le]
        intro x hxP y hyK
        have hyN : y ∈ N := by simpa [N] using hK_norm hyK
        have hyxiy : y * x⁻¹ * y⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp (P.inv_mem hxP)
        have h_eq : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        rw [show (⁅x, y⁆ : G) = x * y * x⁻¹ * y⁻¹ from rfl, h_eq]
        exact P.mul_mem hxP hyxiy)
    · intro x hxP
      have hx_map_top : x ∈ ((⊤ : Subgroup P).map P.subtype) := by
        exact ⟨⟨x, hxP⟩, Subgroup.mem_top _, rfl⟩
      rw [← h_sup_P, Subgroup.map_sup] at hx_map_top
      exact (sup_le_sup h_fixed_map_le h_ac_map_le) hx_map_top
  exact ⟨h_inf_bot, h_sup_eq⟩

                                                                                  

                                                                                          
                                                                            

                 
                                                                                                 
                                                                                   
                                                                                     
                                                                                    
                                                                                                  
                                                                     
                                                                                                
                                                                          
                                    
                                                             
                                                                          
                                                                
                                               
                                            
                                                                            
                 
                   
                                    
                                                
                                                             
                                                        
                               
               
                 
                     
                        
                                                  
                                         
                                                              
                                         
                                                          
                                         
                                                                        
                                                
                                                             
                                                        
                               
               
                 
                     
                        
                                                  
                                         
                                                              
                                         
                                                          
                                         
                                                                        
                                                                                             
                                   
                                   
                                       
                                             
                                            
                                       
                                             
                                            
                                                               
                                                           
                             
                                                                                   
                              
                                                                       
                                                  
                                                                  
                                                
                                                                             
                                     
                                                           
                                              
                                                                 
                                                           
                                              
                                                                 
                                                              
                                                                              
                                                                        
                                            
                                                                              
                                                                        
                                            
                                                                       
                                 
                                                                    
                                                           
                                                       
                                                                   
                                      
                                                              
                                                                                  
                                  
                                  
                         
            
                                  
                              
                                           
                                                                        
                                                       
                                         
                                       
                                                 

                                                                                            
                                                                     

                                                                                                 
                                                                                                           
                                                                      

                                                                               
                                                                 
                                                                                       
                                                        
                                       
                                                 
                                                        
                                                              
                                                                            
                                                             
                                                 
                                                                    
                                    
            
                                           
                                                                    
                          
                                                             
                                                                

                                                              
                                                                                                   

                                                                                                     
                                                                                                               
                                                                                                     
                                                                                           
                                              
                                                       
               
                                                 
                                                 
                                 
                                                                                 
                                                                      
                                      
                                             
                   
                                              
                                                        
                                                                             
                                                                  
                                
              
                                          
                                                                                      
                                                             
                                                 
                                                                
                                                 
                                   
                                     
              
                                              
                                                                           
                                                                                                                  
                          
                                            
                                          
                                                 
                                                         
                         
                                          
                                                    
                                                            
                                   
                                                                  
                                                                                                          
                                                                                          
                                                                       
                                                                                   
            
                                                                             
                                           
                                                                          
                                  
                          
                                             
                   
                                                                                                
                                              
                                            
                                                                       
                                               
                                                               
                                                    
                                                       
                       

/-- **Isaacs Thm 5.13 (Burnside normal p-complement)**:
if a Sylow `p`-subgroup centralizes its normalizer, then `G` has a normal
`p`-complement.

This adapts mathlib's `MonoidHom.ker_transferSylow_isComplement'`, which gives a
complement for the chosen Sylow subgroup, to this file's `HasNormalPComplement`
predicate requiring the same normal complement for every Sylow subgroup. -/
theorem hasNormalPComplement_of_sylow_normalizer_le_centralizer
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP : Subgroup.normalizer (P : Set G) ≤
      Subgroup.centralizer ((P : Subgroup G) : Set G)) :
    HasNormalPComplement p G := by
  classical
  let N : Subgroup G := (MonoidHom.transferSylow P hP).ker
  have hNP : Subgroup.IsComplement' N (P : Subgroup G) := by
    simpa [N] using MonoidHom.ker_transferSylow_isComplement' P hP
  refine ⟨N, inferInstance, ?_⟩
  intro Q
  have hdisj : Disjoint N (Q : Subgroup G) := by
    simpa [N] using MonoidHom.ker_transferSylow_disjoint P hP
      (Q : Subgroup G) Q.isPGroup'
  have hcardQ : Nat.card (Q : Subgroup G) = Nat.card (P : Subgroup G) := by
    exact Nat.card_congr (Sylow.equiv Q P).toEquiv
  have hcard : Nat.card N * Nat.card (Q : Subgroup G) = Nat.card G := by
    rw [hcardQ]
    exact hNP.card_mul
  exact Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdisj

                                                                                         
                                                                   
                                                                          
                                             
                                                                         
                                                                 
                                            

                                                                                          

                                                               

                                                                              
                                                              
                                                                                   
                                                                                                       
                                                                                                   
                                                                                      
                                                                                        
                                                  
                                                                   
                                                                       
                                              
                                                                          
                                                                               
               
                                               
                                    
                                                             
                                                                        
                                         
                                      
                                                                                
               
                                     
               
                                                                                                 
                  
                                
                            
                                                                                          
                                            
                            
                                                                           
                                                                                        
                                                                                         
                             
                                
                                                                                             
                                   
                                                                           
                                     
                                                        
                                                      
                                                              
                             
                                                
                              
                                                  
                        
                       
                                                              
                                                                    
                                                                          
                                                       
                                                                        
                                                                            
                                                      
       
                                          
                               
                                            
                                                        
                   
                                                   
                                                
                        
                                             
                
                                                       
                                                                           
                       
            
                                           
                                                  
                                                                            
                                       
             
                                                 
                                  
                                                               
                                                                       
           
                                
                                                                    
                                                                
                                                          
                                       
                                      
                                                          
                                          

                                                                                             
                                                            

                                                               

                                                                                       
                                                                      
                         
                                                                               

                                                                              
                                  

                                                                                               
                                                                                          
                                                                                         
                              

                                                                                                   
                                                                                      

                                                                                             
                                                        
                       
                                                                       
                                            
                                                                            
                       
                                                                    
                                                     
                                                      
                                                                        
                                                                 
                                      
                                                                                 
                                                                 
                                                                    
                                                                      
                                                                   
                                                            
                                               
                                                               
                           
                                                                                                  
                                                                    
                                                                  
                                                                         
                                
                                                      
                                                
                                                                                          
                                 
                                        
            
                              
              
                                 
                     
                                                                                          
                                                                                      
                 
                                                     
                                                                                                     
                                    
                                                     
                                  
                                       
                  
                                                                      
                                                                   
                                           
                       
                            
                                      
                                                       
                                                                                         
                                                                                        
                               
                   
                                    
                                                            
                                                                                  
                                                                               
                                                                       
                                           
                                                                                                  
                
                                                                             
                                                  
                                                                        
                                                                                             
         
                         
                                                             
                                                
                                
                                                  
                                                                                      
                                                                                       
                   
                                                                       
                                         
                                                     
                                                                                               
        
                                                                               
                                                                      
                                                                           
                                                       
                                                                      
                                                   
                                                                                     
                 
                                       
                 
                                                                          
                                  
                                                                                     
                                                 
                                                                  
                                 
                                         
                                                         
                                                         
                                                                       
                                                                       
                                                                           
                          
                                                                       
                    
                                      
                                                                            
                                 
                                                                                   
                                                           
                                                                                            
                                                                                        
                                                        
                   
                                                   
                                                
                                                     
                                                                        
                        
                           
                      
                                                                             

                                                                                     
                                                                                     
                                            
                                                           
                                                                   
                                         
           
                                                  
                                           
                                                               
                                                                                       
                                                  
                                                     
                            
                                                                                    

                                                                                            
                                  

                                                                                                     
                                                                                                        

                                                                                                 
                                                                                             
                                                                                     
                                                                  
                                                                   
                                                                                   
                                                                                                
                                               
                                                 
                                   
                                          
                                                
                            
             
                                                   
                       
                                                             
                             
               
                 
                    
                            
                                                              
                                                   
                                                                 
                
                                                           
                                         
                                                                       
                                                                        
                                
                                                                        
                                                                              
                   
                                                                    
              
                                                          
                                                     
                                                      
                                                       
                                                
                                                              
                                                       
                                                                             
                                              
                     
                                                                                
                                              
                                                                                             
                                                        
                                                                   
                                               
                                 
                                          
                                                                    
                                                 
                
                   
                                                                    
                                 
                                                                                                       
                                                             
                                                                            
                                                                           
                  
                                    
                                                       
                                
                                                                                        
                                              
                                                             
                                                                
                         
                                        

end -- 5C

section /- 5D: Focal Subgroup theorem (pp. 167-173) -/

/-! ### Isaacs §5D (Focal Subgroup Theorem)

mathlib `Focal.lean` で Focal Subgroup Theorem が完全実装済 (Boyang Hu, 2026):

- `Subgroup.focalSubgroup`, `focalSubgroupOf`: focal subgroup の定義 (Isaacs §5D 冒頭).
- `Subgroup.transferFocal`: `G →* H/H*` の transfer.
- **`Subgroup.commutator_inf_eq_focalSubgroup`** = **Focal Subgroup Theorem (Thm 5.21)** ⭐.

**Thm 5.20** (ker(v) = A^p(G)) = `ker_restrict_transferFocal_eq_focalSubgroupOf` で同等内容
(Isaacs 流は `A^p(G) = O^p(G) · G'` の表示だが, mathlib では `focalSubgroupOf` 表示で同値).

**Cor 5.22, 5.23** (`H controls fusion ⇒ controls p-transfer`): ✅ `A^p` equality
form implemented (`A^p(H)=H∩A^p(G)`), without adding a separate transfer-control predicate.

**Thm 5.24** (G simple, H maximal nilpotent ⇒ H は p-group; Wielandt): BG/Peterfalvi
直接被引用無し. 保留. -/

/-- "`K` controls `G`-fusion in `H`": any two elements of `H` conjugate in the
ambient group `G` are already conjugate by an element of `K`.

Isaacs §5C-§5D で使う fusion-control 条件. -/
def _root_.Subgroup.ControlsFusionIn {G : Type*} [Group G] (K H : Subgroup G) : Prop :=
  ∀ ⦃x y : G⦄, x ∈ H → y ∈ H →
    (∃ g : G, g * x * g⁻¹ = y) →
    (∃ u : G, u ∈ K ∧ u * x * u⁻¹ = y)

/-- **Isaacs Cor 5.22 (focal-subgroup core)**:
if `H` controls `G`-fusion in `P`, then the focal subgroup of `P` computed inside
`H` maps to the focal subgroup of `P` computed inside `G`.

This is the substantive focal-subgroup step in the proof that `H` controls
`p`-transfer in `G`; the remaining book argument is an index/kernel comparison
via the focal subgroup theorem. -/
theorem _root_.Subgroup.focalSubgroup_subgroupOf_map_eq_of_controlsFusionIn
    {G : Type*} [Group G] {P H : Subgroup G} (hP_le_H : P ≤ H)
    (hFusion : H.ControlsFusionIn P) :
    (P.subgroupOf H).focalSubgroup.map H.subtype = P.focalSubgroup := by
  apply le_antisymm
  · rw [Subgroup.focalSubgroup_def, MonoidHom.map_closure, Subgroup.focalSubgroup_def]
    apply Subgroup.closure_mono
    rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨hzPH, x, hxPH, u, rfl⟩
    exact ⟨hzPH, (x : G), hxPH, (u : G), rfl⟩
  · rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
    rintro g ⟨hgP, x, hxP, u, rfl⟩
    have hyP : u * x * u⁻¹ ∈ P := by
      have hy_eq : u * x * u⁻¹ = (⁅x, u⁆)⁻¹ * x := by
        rw [commutatorElement_def]
        group
      rw [hy_eq]
      exact P.mul_mem (P.inv_mem hgP) hxP
    obtain ⟨v, hvH, hv⟩ := hFusion hxP hyP ⟨u, rfl⟩
    have hcomm_eq : ⁅x, u⁆ = ⁅x, v⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc
        x * u * x⁻¹ * u⁻¹ = x * (u * x * u⁻¹)⁻¹ := by group
        _ = x * (v * x * v⁻¹)⁻¹ := by rw [hv]
        _ = x * v * x⁻¹ * v⁻¹ := by group
    let xH : H := ⟨x, hP_le_H hxP⟩
    let vH : H := ⟨v, hvH⟩
    let gH : H := ⟨⁅x, u⁆, hP_le_H hgP⟩
    have hgH_focal : gH ∈ (P.subgroupOf H).focalSubgroup := by
      rw [Subgroup.focalSubgroup_def]
      apply Subgroup.subset_closure
      refine ⟨hgP, xH, hxP, vH, ?_⟩
      apply Subtype.ext
      exact hcomm_eq
    exact Subgroup.mem_map_of_mem H.subtype hgH_focal

/-- `OPrime p G` — the smallest normal subgroup of `G` with `p`-power index.
For finite `G`, this is the intersection of all such normal subgroups (Isaacs §5D 冒頭, 'O^p(G)').

mathlib 未収載のため新規定義. 5.25 (⇐), 5.20 等で使用. -/
def OPrime (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨅ N : {N : Subgroup G // N.Normal ∧ ∃ k : ℕ, N.index = p ^ k}, N.val

                                                                 
                                                                
                                                                 
                       
                                                    

/-- `OPrime p G` is normal. -/
instance OPrime_normal (p : ℕ) (G : Type*) [Group G] : (OPrime p G).Normal := by
  unfold OPrime
  exact Subgroup.normal_iInf_normal (fun N => N.property.1)

/-- Per-element Normal instance for the `OPrime` indexing subtype. Needed so that
`G ⧸ N.val` (over `N` in the subtype) has a group structure during type elaboration. -/
instance OPrime_index_subtype_normal {p : ℕ} {G : Type*} [Group G]
    (N : {N : Subgroup G // N.Normal ∧ ∃ k : ℕ, N.index = p ^ k}) :
    (N.val : Subgroup G).Normal := N.property.1

                                                     

                                                                                              
                                                                                  
                                                                                          
                                                                        
                                                                             
                                                                                          
                                                                    
                                                                                       
                                                 
           
                                                                                  
                                     
                                           
                                                                                                      
                                                             
                                                      
                        
                                        
         
                                         
                                     
             
                                                                 
                                                       
                                                             
                                            
                             
           
                                                                               
                                 
                                         
               
                                              
                                                                      
                                                                                                
                                     
                                          
                                                                          
                  
                                                                         
                                         
                                                                                                    
                    
                                              
                               
                                    
                                                                  
                                                                                                    
                                                                               
                                       
                                                   
                                      
                                                                         
                                            
                          
                                                                             
                                              
                                                 
                                                                    
                   

/-- `APrime p G` — the smallest normal subgroup `K ⊴ G` with `G/K` abelian and p-power index.
Equivalently, the smallest member of the family `{K ⊴ G : commutator G ≤ K ∧ [G:K] is p-power}`.

For finite `G`, this corresponds to Isaacs' `A^p(G)`. mathlib 未収載のため新規定義. -/
def APrime (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨅ K : {K : Subgroup G // K.Normal ∧ commutator G ≤ K ∧ ∃ k : ℕ, K.index = p ^ k}, K.val

/-- Per-element Normal instance for the `APrime` indexing subtype. -/
instance APrime_index_subtype_normal {p : ℕ} {G : Type*} [Group G]
    (K : {K : Subgroup G // K.Normal ∧ commutator G ≤ K ∧ ∃ k : ℕ, K.index = p ^ k}) :
    (K.val : Subgroup G).Normal := K.property.1

                                                                                         
                                                                
                                                                                
                       
                                             

/-- `APrime p G` is normal. -/
instance APrime_normal (p : ℕ) (G : Type*) [Group G] : (APrime p G).Normal := by
  unfold APrime
  exact Subgroup.normal_iInf_normal (fun K => K.property.1)

                                                                                          
                                                                                              
            
               
                        
         
                         

                                                                                            
                                                                               
                                                                                       
                                                 
           
                    
                                                                                        
                                     
                                           
                                                             
                                                      
                                        
         
                                         
                                     
             
                                                                 
                                                       
                                                             
                                            
                             
           
                                                                               
                                 
                                         
               
                                                                      
                                                                                                
                                     
                                                                          
                  
                                                                         
                                                                                                    
                    
                                              
                               
                                                                    
                                                        
                                                 
                                                                               
                                       
                                                   
                                                                         
                                            
                          
                                                                             
                                              
                                                 
                                                                    
                   

                                                  

                                                                                           
                                                               
                                                                                       
                                     
           
                                           
          
                                                         
                                            
                                         
              
                           
                                                              
                                               
                                                                           
                                   
                                                                
                                  
                                                        
                                                 
                                       
                                                            
                                              
                                                     

                                                

                                                                                  
                                                                                  
                                                                     
                                                              
           
                                                        
                                                
                                                                               
                                            
                                                           
                               
            
                                                          
                                                                     

                                                                  
                                            

                                                                                        
                                                                                  
                                                                           
                     
                                                                          
                   
         
                                                                                     
                                                         
                                           
                                                         
                                                        
                                                      

                                                 
                                                                              
                                                                                    

                                                                                    
                                              
                                                                           
                   
                                                                                  
                                                                                 
                                                                          
                                                                                     
                                                      
                                        
                                                        

                                                               

                                                                                    
                                                                                   
                                                                                     
                                                                       
                     
                                          
           
                                  
                                           
                        
             
                  
                        
             
                  
                              
                                                                      
                                                                               
                                                                         
                                                                               
                                                                     
                                                        
                                             
                                                        
                                                          
                                                  
                                                                                 
                                              
                      
                                            
                               
            
                                                   
                                      
                                                                
             
                                                                              
                                                               
                                                   
                                      
                                                                
             
                                                                              
                                                               
                                           
        
                                                 
                                                                             
                                               
                                                                  
                                        
                                                                  
                               
                                           
                                        
                       
                                                                             
                                               
                                           
                                                          
                                                                   
                                    
                                                                
                                                                     

                                                  
                                                            
                          

                                                                                 
                                                                
                                                                                 
                                                                         
                                                  
           
                                  
                                             
                                                        
                                             
                                                   
                                      
                                                                
             
                                                                              
                                                               
                                    
                                
                                   
                                                                         
                                      
                      
                               
                                                                   
                                      
                                                                          
                                                        
              
                        
                                                            
                                          
                                                                      
                                                                 
                                                  
                                                  
                                      
                                                                    

                                               
                                                           
                        

                                                                         
                                 
                                                                  
                                                             
                                      
                                                     
                                                
           
                                  
                                  
                                                          
                                            
                                                                                          
                                        
                                                                    
                                                
              
                                                                                  
                                                      
                                             
                                      
                                                            
                                                                    
                             
                                                                          
                                                
                                                           
                                      
                                               
                                                                                   
                                                                
                                                                        
                                           
                                                           
                                               
                                                      
             
                                                                                 
                                                               
                                                                        
                                                           
                                               
                                                     
                                                                  
               
                                                                                
                                                                 
                                      
                                  
                                     
                      
                               
                                                                   
                                      
                                                         
                                       
                                                                     
             
                                                                                 
                                                               
                                                          
        
                                       
                                                                             
                                                 
                                              
                                        
                                                           
                                  
                                                
                                        
                                      
                                                                                
                                                            
                                                          
                                                                      
                                        
                                                                    
                                    
                                                                
                                                                      

                                               
                                                                              
                                               

                                                                             
                       
                                                                        
                                                       
                                            
                                                
                                                                     
           
                                                       
                                                                 
                                                          
                         
                               
                                                                          
                                       
                
                                 
                                                                                                 
                                                                          
                                       
                
                                 
                                                                                                 
                                                               
                 
                                                                                       

end -- 5D

section /- 5E: Frobenius normal p-complement (pp. 173-180) -/

end
end OddOrder.Isaacs.Ch05
